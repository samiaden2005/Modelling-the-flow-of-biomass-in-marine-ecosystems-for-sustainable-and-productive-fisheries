library(mizer)
library(dplyr)
library(ggplot2)

# Day 40 (mortality follow-up): Days 39/40's own
# anchovy_params()/make_anchovy_fishing_params_theta() was silently discarding
# the paper's own mortality curve.
#
# setAnchovyMort() set the custom senescence/background mortality by writing
# straight to @mu_b. Every theta/interaction_resource variant then called
# species_params(params) <- sp to set interaction_resource -- which runs
# setParams() and hence setExtMort() internally, and SILENTLY RECOMPUTES
# @mu_b from mizer's own z0 defaults, discarding whatever setAnchovyMort()
# had just written. Confirmed directly in Section 0b below: every model built
# through that code path (Days 39-40's baseline AND every theta variant) had
# a FLAT mu_b=0.148 at every size, not the paper's own two-part
# larval/senescence curve. The fix (this file, ported from the CURRENT
# 39_experiments.R, which already carries it): set mortality LAST, through
# ext_mort<-() rather than a direct @mu_b write -- the setter marks the array
# as manually set, so later species_params<-() calls leave it alone.
#
# Self-contained convention since Day 20: helpers redefined here. Uses the
# modern accessor-function API (w(), ext_mort<-(), gear_params<-(), etc.),
# matching the CURRENT 39_experiments.R rather than Day 40's own @-slot
# style, since that's the style the fix itself is written in.

plot_dir <- "interesting_plots"
dir.create(plot_dir, showWarnings = FALSE)

save_plot <- function(plot, filename, width = 9, height = 6, dpi = 150) {
  max_name <- 40
  if (nchar(filename) > max_name) {
    ext      <- tools::file_ext(filename)
    base     <- tools::file_path_sans_ext(filename)
    filename <- paste0(substr(base, 1, max_name - nchar(ext) - 1), ".", ext)
    warning(sprintf("save_plot(): filename too long, truncated to '%s'", filename))
  }
  print(plot)
  ggsave(file.path(plot_dir, filename), plot = plot, width = width, height = height, dpi = dpi)
}

################################################################################
# Section 0: the fixed model builder, ported verbatim from the CURRENT
# 39_experiments.R (not the version this project's earlier days -- including
# all of Day 40 -- were actually built against).
################################################################################

p2 <- list(
  dt = 0.001, dx = 0.1, w_min = 0.0003, w_inf = 66.5,
  ppmr_min = 100, ppmr_max = 30000, gamma = 750, alpha = 0.85, K = 0.1,
  mu_l = 0, w_l = 0.03, rho_l = 5,
  mu_0 = 1, rho_b = -0.25,
  w_s = 0.5, rho_s = 1,
  w_mat = 10, rho_m = 15, rho_inf = 0.2, epsilon_R = 0.1,
  w_pp_cutoff = 0.1, r0 = 10, a0 = 100, i0 = 100, rho = 0.85, lambda = 2
)

setAnchovyMort <- function(params, p) {
  w <- w(params)
  mu_b <- rep(0, length(w))
  mu_b[w <= p$w_s] <- (p$mu_0 * (w / p$w_min)^p$rho_b)[w < p$w_s]
  mu_s <- if (p$mu_0 > 0) min(mu_b[w <= p$w_s]) else p$mu_s
  mu_b[w >= p$w_s] <- (mu_s * (w / p$w_s)^p$rho_s)[w >= p$w_s]
  mu_b <- mu_b + p$mu_l / (1 + (w / p$w_l)^p$rho_l)

  # ext_mort<-() rather than a direct write to @mu_b: the setter marks the array
  # as manually set, so the later species_params<-() call below (interaction_resource)
  # leaves it alone instead of silently recomputing mu_b from the z0 defaults.
  mort <- ext_mort(params)
  mort[] <- mu_b
  ext_mort(params) <- mort
  params
}

plankton_state <- new.env(parent = emptyenv())
plankton_state$time   <- 0
plankton_state$factor <- 1

# Exact step for
#   dn/dt = immigration + (rate - mortality) * n - rate / capacity * n^2.
# This is the logistic resource equation with constant immigration. As in
# mizer::resource_logistic(), rates are held fixed during each time step.
# Replaces the old explicit-Euler step (n_pp + dt*f) -- pulled in from
# upstream/GitHub, not written for this project. Unlike the Euler version,
# this is exact for any dt, so it no longer forces dt to stay small for the
# RESOURCE side specifically; whether the CONSUMER side (still the default
# first-order upwind scheme, no second_order_w/tr_bdf2 anywhere in this
# project) can also tolerate a larger dt is untested -- see the Overnight
# section's own note before assuming dt can just be raised project-wide.
exact_logistic_immigration_step <- function(n, rate, capacity, immigration,
                                            mortality, dt) {
  result <- n
  active <- is.finite(n) & is.finite(rate) & is.finite(capacity) &
    is.finite(immigration) & is.finite(mortality) &
    rate > 0 & capacity > 0 & immigration >= 0
  if (dt == 0 || !any(active)) return(result)

  n0 <- n[active]
  r  <- rate[active]
  k  <- capacity[active]
  i  <- immigration[active]
  mu <- mortality[active]
  a  <- r - mu
  b  <- r / k
  next_n <- numeric(length(n0))

  # With immigration the quadratic has one positive and one negative root.
  # The alternative root formulae avoid cancellation when abs(a) is large.
  has_immigration <- i > 0
  if (any(has_immigration)) {
    idx <- which(has_immigration)
    ai  <- a[idx]
    bi  <- b[idx]
    ii  <- i[idx]
    d   <- sqrt(ai^2 + 4 * bi * ii)
    n_plus <- ifelse(ai >= 0, (ai + d) / (2 * bi), 2 * ii / (d - ai))
    n_minus <- ifelse(ai <= 0, (ai - d) / (2 * bi), -2 * ii / (ai + d))
    ratio <- ((n0[idx] - n_plus) / (n0[idx] - n_minus)) * exp(-d * dt)
    next_n[idx] <- (n_plus - ratio * n_minus) / (1 - ratio)
  }

  # The zero-immigration limit is handled separately, including rate == mortality.
  no_immigration <- !has_immigration
  if (any(no_immigration)) {
    idx <- which(no_immigration)
    az  <- a[idx]
    bz  <- b[idx]
    nz  <- n0[idx]
    value <- numeric(length(idx))
    zero_rate <- az == 0
    value[zero_rate] <- nz[zero_rate] /
      (1 + bz[zero_rate] * nz[zero_rate] * dt)

    positive <- az > 0 & nz > 0
    phi <- -expm1(-az[positive] * dt) / az[positive]
    value[positive] <- nz[positive] /
      (exp(-az[positive] * dt) +
         bz[positive] * nz[positive] * phi)

    negative <- az < 0
    exp_adt <- exp(az[negative] * dt)
    phi <- expm1(az[negative] * dt) / az[negative]
    value[negative] <- nz[negative] * exp_adt /
      (1 + bz[negative] * nz[negative] * phi)
    next_n[idx] <- value
  }

  # Round-off can only create tiny negative values; the analytic solution is
  # non-negative for non-negative initial abundance and immigration.
  result[active] <- pmax(next_n, 0)
  result
}

plankton_logistic <- function(params, n, n_pp, n_other, rates, dt = 0.1, ...) {
  plankton_state$time <- plankton_state$time + dt
  exact_logistic_immigration_step(
    n = n_pp,
    rate = params@rr_pp,
    capacity = params@cc_pp * plankton_state$factor,
    immigration = anchovy_immigration,
    mortality = rates$resource_mort,
    dt = dt
  )
}

norm_box_pred_kernel <- function(ppmr, ppmr_min, ppmr_max) {
  phi <- rep(1, length(ppmr))
  phi[ppmr > ppmr_max] <- 0
  phi[ppmr < ppmr_min] <- 0
  phi[1] <- 0
  logppmr <- log(ppmr)
  dl <- logppmr[2] - logppmr[1]
  N <- sum(phi) * dl
  phi / N
}

anchovy_params <- function(interaction_val = 1, interaction_resource_val = 1,
                           knife_edge_size = p2$w_mat, p = p2) {
  kappa <- p$a0 * exp(-6.9 * (p$lambda - 1))

  species_params_df <- data.frame(
    species = "Anchovy", w_min = p$w_min, w_mat = p$w_mat, m = p$rho_inf + 2/3,
    w_inf = p$w_inf, erepro = p$epsilon_R, alpha = p$K, ks = 0, gamma = p$gamma,
    q = p$alpha, ppmr_min = p$ppmr_min, ppmr_max = p$ppmr_max,
    pred_kernel_type = "norm_box", h = Inf, R_max = Inf, linecolour = "brown",
    stringsAsFactors = FALSE
  )

  params <- newMultispeciesParams(
    species_params_df, no_w = round(log(p$w_inf / p$w_min) / p$dx),
    lambda = p$lambda, kappa = kappa, w_pp_cutoff = p$w_pp_cutoff,
    resource_dynamics = "plankton_logistic"
  )
  resource_rate(params) <- p$r0 * w_full(params)^(p$rho - 1)

  interaction_matrix(params) <- interaction_val
  species_params(params)$interaction_resource <- interaction_resource_val

  gp                 <- gear_params(params)
  gp$sel_func        <- "knife_edge"
  gp$knife_edge_size <- knife_edge_size
  gp$catchability    <- 1
  gear_params(params) <- gp

  # Mortality last -- protected via ext_mort<-() from the species_params<-()
  # call above, which is the actual source of the Day 39-40 bug.
  setAnchovyMort(params, p)
}

p_scan <- anchovy_params()
anchovy_immigration <- p2$i0 * w_full(p_scan)^(-p2$lambda) * exp(-6.9 * (p2$lambda - 1))

################################################################################
# Section 0b: confirm the bug directly -- compare mu_b from the OLD
# (buggy-ordering, direct @mu_b write) construction against the NEW
# (ext_mort<-(), mortality-last) construction, at identical parameters.
################################################################################

theta_low <- 0.3

# The OLD, buggy-ordering builder, reproduced exactly as it appeared in
# 40_experiments.R -- kept ONLY for this one comparison, not used elsewhere
# in this file.
make_anchovy_fishing_params_theta_BUGGY <- function(interaction_val, interaction_resource_val,
                                                     knife_edge_size = p2$w_mat, p = p2) {
  params <- anchovy_params_base_only(p)
  params <- setAnchovyMort_BUGGY(params, p)          # mortality set FIRST, direct @mu_b write
  params@interaction[] <- interaction_val
  sp <- species_params(params)
  sp$interaction_resource <- interaction_resource_val
  species_params(params) <- sp                        # <-- silently resets @mu_b here
  gp                 <- params@gear_params
  gp$sel_func        <- "knife_edge"
  gp$knife_edge_size <- knife_edge_size
  gp$catchability    <- 1
  gear_params(params) <- gp
  params
}
setAnchovyMort_BUGGY <- function(params, p) {
  mu_b <- rep(0, length(params@w))
  mu_b[params@w <= p$w_s] <- (p$mu_0 * (params@w / p$w_min)^p$rho_b)[params@w < p$w_s]
  mu_s <- if (p$mu_0 > 0) min(mu_b[params@w <= p$w_s]) else p$mu_s
  mu_b[params@w >= p$w_s] <- (mu_s * (params@w / p$w_s)^p$rho_s)[params@w >= p$w_s]
  mu_b <- mu_b + p$mu_l / (1 + (params@w / p$w_l)^p$rho_l)
  params@mu_b[] <- mu_b
  params
}
anchovy_params_base_only <- function(p) {
  kappa <- p$a0 * exp(-6.9 * (p$lambda - 1))
  species_params_df <- data.frame(
    species = "Anchovy", w_min = p$w_min, w_mat = p$w_mat, m = p$rho_inf + 2/3,
    w_inf = p$w_inf, erepro = p$epsilon_R, alpha = p$K, ks = 0, gamma = p$gamma,
    q = p$alpha, ppmr_min = p$ppmr_min, ppmr_max = p$ppmr_max,
    pred_kernel_type = "norm_box", h = Inf, R_max = Inf, linecolour = "brown",
    stringsAsFactors = FALSE
  )
  newMultispeciesParams(species_params_df, no_w = round(log(p$w_inf / p$w_min) / p$dx),
                        lambda = p$lambda, kappa = kappa, w_pp_cutoff = p$w_pp_cutoff,
                        resource_dynamics = "plankton_logistic")
}

p_theta_low_BUGGY <- make_anchovy_fishing_params_theta_BUGGY(theta_low, 1, knife_edge_size = 10)
p_theta_low_FIXED <- anchovy_params(theta_low, 1, knife_edge_size = 10)

w_check <- c(0.0003, 0.001, 0.01, 0.1, 0.5, 1, 5, 10, 30, 66)
idx_check <- vapply(w_check, function(x) which.min(abs(w(p_theta_low_FIXED) - x)), integer(1))

mu_b_compare_df <- data.frame(
  w              = round(w(p_theta_low_FIXED)[idx_check], 4),
  mu_b_OLD_buggy = p_theta_low_BUGGY@mu_b[idx_check],
  mu_b_NEW_fixed = ext_mort(p_theta_low_FIXED)[1, idx_check]
)
write.csv(mu_b_compare_df, file.path(plot_dir, "day40_changed_mort_mu_b_compare.csv"), row.names = FALSE)
cat("Section 0b: OLD (buggy) mu_b is FLAT (mizer's own z0 default) at every size; NEW (fixed) mu_b is the paper's own U-shaped curve. See day40_changed_mort_mu_b_compare.csv:\n")
print(mu_b_compare_df)

################################################################################
# Section 0c: does the fix change the model's cycle period? Day 40's own
# t_fork=20/scan_summary_window=12 convention assumed a ~5-6yr period --
# worth actually checking under the corrected mortality rather than assuming
# it still holds. (An earlier, undersampled look at this trajectory wrongly
# suggested a ~16yr period -- an aliasing artefact of sampling only every 4th
# year; the properly-resolved check below supersedes that.)
################################################################################

set_state <- function(params, n, n_pp) {
  n0 <- initialN(params); n0[] <- n; initialN(params) <- n0
  npp0 <- initialNResource(params); npp0[] <- n_pp; initialNResource(params) <- npp0
  params
}
seed_from <- function(params, sim) set_state(params, finalN(sim), finalNResource(sim))

make_anchovy_fork_sim <- function(params, t_fork) {
  params <- set_state(params, 0.001 * w(params)^(-1.8), resource_capacity(params))
  settled <- project(params, t_max = 10, dt = p2$dt, progress_bar = FALSE)
  params <- set_state(params, finalN(settled) / 1e7, finalNResource(settled))
  project(params, t_max = t_fork - 10, t_start = 10, dt = p2$dt, t_save = 0.2,
         progress_bar = FALSE, effort = 0)
}

after_cut <- function(x, sim, t_cut) unname(x[getTimes(sim) > t_cut, 1])
gear_knife_edge <- function(params) gear_params(params)$knife_edge_size[[1]]
selected_biomass <- function(sim, t_cut = -Inf) {
  after_cut(getBiomass(sim, min_w = gear_knife_edge(sim@params)), sim, t_cut)
}

t_fork               <- 20
scan_post_fork_years <- 24
scan_summary_window  <- 12
scan_t_cut           <- t_fork + scan_post_fork_years - scan_summary_window

sim_fork_theta_low <- make_anchovy_fork_sim(p_theta_low_FIXED, t_fork)

# Extend well past t_fork to check the true, long-run period rather than
# assuming Day 37-40's ~5-6yr figure still applies.
sim_long <- project(sim_fork_theta_low, t_max = 60, t_start = t_fork, dt = p2$dt, t_save = 0.5,
                    progress_bar = FALSE, effort = 0)
bp_long <- selected_biomass(sim_long, t_cut = -Inf)
tv_long <- getTimes(sim_long)
df_long <- data.frame(t = tv_long, b = bp_long) %>% filter(t > t_fork)

n_long   <- nrow(df_long)
is_peak  <- c(FALSE, df_long$b[2:(n_long-1)] > df_long$b[1:(n_long-2)] & df_long$b[2:(n_long-1)] > df_long$b[3:n_long], FALSE)
peak_times <- df_long$t[is_peak]

cycle_period_df <- data.frame(peak_t = peak_times, peak_b = df_long$b[is_peak],
                              period_since_last = c(NA, diff(peak_times)))
write.csv(cycle_period_df, file.path(plot_dir, "day40_changed_mort_cycle_period.csv"), row.names = FALSE)
cat(sprintf(
  "Section 0c: fixed-mortality theta=0.3, unfished, peak spacing over t=[%.0f,%.0f]: mean period=%.2fyr (range %.1f-%.1f) -- close to Day 37-40's own ~5-6yr assumption, so t_fork=20/scan_summary_window=12 are kept unchanged rather than re-derived from scratch.\n",
  t_fork, max(tv_long), mean(diff(peak_times), na.rm = TRUE), min(diff(peak_times), na.rm = TRUE), max(diff(peak_times), na.rm = TRUE)
))
print(cycle_period_df)

################################################################################
# Section 1: redo Day 40 Section 1's headline comparison (Baseline theta=1 vs.
# theta=0.3, Constant fishing, knife_edge=10) under the corrected mortality.
#
# Moderate 8-point grid (not Day 40's ultra-fine 14-point one) -- this is a
# first-pass redo to establish whether the fix changes the STORY, not a
# final, fully-resolved replacement for Day 40's own sweep.
################################################################################

sim_metrics <- function(sim, t_cut) {
  total  <- after_cut(getBiomass(sim), sim, t_cut)
  mature <- after_cut(getBiomass(sim, min_w = p2$w_mat), sim, t_cut)
  yield  <- after_cut(getYield(sim), sim, t_cut)
  data.frame(mean_total = mean(total), min_total = min(total),
            mean_selected = mean(mature), mean_juvenile = mean(total - mature),
            mean_yield = mean(yield),
            rel_amplitude = (max(total) - min(total)) / ((max(total) + min(total)) / 2))
}

cannibalism_fishing_probe <- function(params, fork_sim, fish_level_seq, years = scan_summary_window) {
  params <- seed_from(params, fork_sim)
  bind_rows(lapply(fish_level_seq, function(fl) {
    sim <- project(params, t_max = years, dt = p2$dt, t_save = 0.2,
                   t_start = t_fork, progress_bar = FALSE, effort = fl)
    cbind(fish_level = fl, sim_metrics(sim, t_fork + years / 2))
  }))
}

p_baseline_fixed <- anchovy_params(1, 1, knife_edge_size = 10)
sim_fork_baseline <- make_anchovy_fork_sim(p_baseline_fixed, t_fork)

fish_level_seq_redo <- c(1, 2, 3, 5, 9, 20, 50, 100)

redo_probe_df <- bind_rows(
  cannibalism_fishing_probe(p_baseline_fixed, sim_fork_baseline, fish_level_seq_redo) %>%
    mutate(model = "Baseline (theta=1), FIXED mortality"),
  cannibalism_fishing_probe(p_theta_low_FIXED, sim_fork_theta_low, fish_level_seq_redo) %>%
    mutate(model = "theta=0.3, FIXED mortality")
)
write.csv(redo_probe_df, file.path(plot_dir, "day40_changed_mort_probe.csv"), row.names = FALSE)
cat("Section 1 (Baseline vs. theta=0.3, FIXED mortality, knife_edge=10): see day40_changed_mort_probe.csv.\n")
print(redo_probe_df %>% select(model, fish_level, mean_total, mean_yield, rel_amplitude))

redo_yield_plot <- ggplot(redo_probe_df, aes(x = fish_level, y = mean_yield, color = model)) +
  geom_line() +
  geom_point(size = 2) +
  scale_x_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
       title = "Corrected mortality: theta=0.3's yield curve is no longer cleanly single-peaked",
       subtitle = "knife_edge=10 -- local peak near fish_level=9, dip at 20, then rises again by 50-100 (contrast with Day 40's clean peak-then-decline under the buggy mortality)") +
  theme_minimal()
save_plot(redo_yield_plot, "day40_changed_mort_yield.png", width = 9, height = 6)

cat(paste(
  "Section 1 headline finding: the mortality fix barely moves the theta=1 BASELINE",
  "(cannibalism-driven predation mortality dominates there -- fixed-mortality numbers",
  "land almost exactly on Day 39's own buggy-mortality baseline, e.g. mean_yield=0.0985",
  "vs. 0.09846 at fish_level=100). theta=0.3 is a different story: mean_total drops from",
  "the buggy version's own ~0.56-0.65 range to ~0.36-0.43, and -- critically -- the clean",
  "single-peaked yield curve Day 40 built its whole headline result on (peak at",
  "fish_level=2, smooth decline to 100) does NOT survive. The fixed-mortality yield curve",
  "rises to a local peak near fish_level=9, dips at 20, then rises AGAIN by fish_level=50-100,",
  "ending higher than the local peak -- not a clean sustainable-yield shape at all.",
  "This is a first-pass, 8-point-grid finding, not a finished replacement for Day 40's own",
  "fine sweep -- see What's Next.\n"
))

################################################################################
# Overnight: theta x interaction_resource grid under the FIXED mortality --
# mirrors Day 39 Section 3's own grid (same theta_grid_seq/resource_grid_seq),
# to check whether theta=0.3/interaction_resource=1 (Day 40's own choice,
# built under the BUGGY mortality) is still the most fishing-sensitive point,
# or whether the buggy mortality was itself steering that choice toward a
# combination that only looked good by accident.
#
# NOT run interactively. A first attempt at this exact grid ran for over an
# hour in the live session without finishing -- each of the 25 cells does
# three full projections (10yr settle, 10yr kick-regrowth, 12yr fished) at
# dt=0.001 -- and was cancelled rather than left blocking further work.
# Queued here as a batch/overnight job instead (e.g. via Rscript from a
# terminal, not the interactive r-mizer session). Uses the exact resource
# stepper above as-is; whether dt itself can be safely raised to actually
# speed this up hasn't been tested yet -- see the note there.
################################################################################

w_grid_check   <- c(0.01, 1, 10, 30)
idx_grid_check <- vapply(w_grid_check, function(x) which.min(abs(w(p_baseline_fixed) - x)), integer(1))

fork_rate            <- function(getter, params, sim, idx) getter(seed_from(params, sim))[1, idx]
growth_baseline_grid <- fork_rate(getEGrowth, p_baseline_fixed, sim_fork_baseline, idx_grid_check)

grid_probe_effort <- 10

run_interaction_grid_case <- function(theta_val, ir_val) {
  params        <- anchovy_params(theta_val, ir_val, knife_edge_size = p2$w_mat)
  sim_fork_grid <- make_anchovy_fork_sim(params, t_fork)

  bp_grid        <- selected_biomass(sim_fork_grid, t_cut = t_fork - scan_summary_window)
  unfished_ratio <- max(bp_grid) / max(min(bp_grid), 1e-12)

  growth_grid     <- fork_rate(getEGrowth, params, sim_fork_grid, idx_grid_check)
  growth_recovery <- growth_grid / growth_baseline_grid

  total_unfished <- mean(after_cut(getBiomass(sim_fork_grid), sim_fork_grid, t_fork - scan_summary_window))

  sim_fished <- project(seed_from(params, sim_fork_grid), t_max = scan_summary_window, dt = p2$dt,
                        t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = grid_probe_effort)
  total_at_effort     <- mean(after_cut(getBiomass(sim_fished), sim_fished, t_fork + scan_summary_window / 2))
  yield_at_effort     <- mean(after_cut(getYield(sim_fished), sim_fished, t_fork + scan_summary_window / 2))
  fishing_sensitivity <- 1 - total_at_effort / total_unfished

  data.frame(theta = theta_val, interaction_resource = ir_val, unfished_cycle_ratio = unfished_ratio,
            growth_recovery_w0.01 = growth_recovery[1], growth_recovery_w1 = growth_recovery[2],
            growth_recovery_w10 = growth_recovery[3], growth_recovery_w30 = growth_recovery[4],
            total_unfished = total_unfished, total_at_effort10 = total_at_effort,
            mean_yield_at_effort10 = yield_at_effort, fishing_sensitivity = fishing_sensitivity)
}

theta_grid_seq    <- c(1, 0.7, 0.5, 0.3, 0.1)
resource_grid_seq <- c(1, 1.3, 2, 3, 5)

interaction_grid_df <- bind_rows(lapply(theta_grid_seq, function(th) {
  bind_rows(lapply(resource_grid_seq, function(ir) run_interaction_grid_case(th, ir)))
}))
write.csv(interaction_grid_df, file.path(plot_dir, "day40_changed_mort_interaction_grid.csv"), row.names = FALSE)
cat("Overnight grid (theta x interaction_resource, FIXED mortality): see day40_changed_mort_interaction_grid.csv.\n")
print(interaction_grid_df)

grid_growth_heatmap <- ggplot(interaction_grid_df,
                              aes(x = factor(theta), y = factor(interaction_resource), fill = growth_recovery_w10)) +
  geom_tile() +
  geom_text(aes(label = sprintf("%.2f", growth_recovery_w10)), size = 3, color = "white") +
  scale_fill_viridis_c(limits = c(0, NA)) +
  labs(x = "theta (cannibalism)", y = "interaction_resource", fill = "recovery",
       title = "FIXED mortality: growth recovery at w=10.1g",
       subtitle = "1.0 = fully back to the (theta=1, interaction_resource=1) baseline's own growth there") +
  theme_minimal()
save_plot(grid_growth_heatmap, "day40_changed_mort_grid_growth.png", width = 8, height = 6)

grid_sensitivity_heatmap <- ggplot(interaction_grid_df,
                                   aes(x = factor(theta), y = factor(interaction_resource), fill = fishing_sensitivity)) +
  geom_tile() +
  geom_text(aes(label = sprintf("%.2f", fishing_sensitivity)), size = 3, color = "white") +
  scale_fill_viridis_c(option = "magma", limits = c(0, NA)) +
  labs(x = "theta (cannibalism)", y = "interaction_resource", fill = "sensitivity",
       title = "FIXED mortality: fraction of unfished biomass lost at effort=10",
       subtitle = "Higher = more responsive to fishing") +
  theme_minimal()
save_plot(grid_sensitivity_heatmap, "day40_changed_mort_grid_sensitiv.png", width = 8, height = 6)

grid_tradeoff_plot <- ggplot(interaction_grid_df,
                             aes(x = fishing_sensitivity, y = growth_recovery_w10,
                                 color = factor(theta), shape = factor(interaction_resource))) +
  geom_point(size = 3) +
  labs(x = "Fishing sensitivity (fraction of unfished biomass lost at effort=10)",
       y = "Growth recovery at w=10.1g (1.0 = theta=1/ir=1 baseline)",
       color = "theta", shape = "interaction_resource",
       title = "FIXED mortality: the same trade-off Day 39 Section 3 navigated, redone",
       subtitle = "Is theta=0.3/interaction_resource=1 -- Day 40's own choice -- actually the best point here?") +
  theme_minimal()
save_plot(grid_tradeoff_plot, "day40_changed_mort_grid_tradeoff.png", width = 9, height = 6)

baseline_grid_row <- interaction_grid_df %>% filter(theta == 1, interaction_resource == 1)
theta_03_row       <- interaction_grid_df %>% filter(theta == 0.3, interaction_resource == 1)
cat(sprintf(
  "Baseline cell (theta=1, ir=1): fishing_sensitivity=%.3f at effort=10. Day 40's own choice (theta=0.3, ir=1) under FIXED mortality: fishing_sensitivity=%.3f, growth_recovery_w10=%.3f -- compare against the full grid to see whether a different cell would have served the project's aim better.\n",
  baseline_grid_row$fishing_sensitivity, theta_03_row$fishing_sensitivity, theta_03_row$growth_recovery_w10
))

################################################################################
# Section 2: What's-Next item 5 -- now that the resource step is exact, can dt
# be raised above 0.001? The CONSUMER side is still the default first-order
# upwind scheme (no second_order_w/tr_bdf2), so this is testing that scheme's
# own tolerance, not the resource stepper's.
#
# Reuses the already-computed dt=0.001 reference (sim_long/df_long/peak_times,
# Section 0c above: mean_total=0.0170, rel_amplitude=1.41, period=5.55yr over
# the same t=[68,80] window) rather than re-deriving it.
################################################################################

ref_window_dt <- df_long %>% filter(t > (t_fork + 48), t <= (t_fork + 60))
dt_ref_summary <- data.frame(
  dt = p2$dt,
  mean_total = mean(ref_window_dt$b),
  rel_amplitude = (max(ref_window_dt$b) - min(ref_window_dt$b)) / ((max(ref_window_dt$b) + min(ref_window_dt$b)) / 2),
  mean_period = mean(diff(peak_times[peak_times > t_fork & peak_times <= (t_fork + 60)]))
)

run_dt_case <- function(dt_val) {
  params <- set_state(p_theta_low_FIXED, 0.001 * w(p_theta_low_FIXED)^(-1.8), resource_capacity(p_theta_low_FIXED))
  settled <- project(params, t_max = 10, dt = dt_val, progress_bar = FALSE)
  params <- set_state(params, finalN(settled) / 1e7, finalNResource(settled))
  forked <- project(params, t_max = t_fork - 10, t_start = 10, dt = dt_val, t_save = 0.2,
                    progress_bar = FALSE, effort = 0)
  sim <- project(forked, t_max = 60, t_start = t_fork, dt = dt_val, t_save = 0.5,
                 progress_bar = FALSE, effort = 0)
  bp <- selected_biomass(sim, t_cut = -Inf)
  tv <- getTimes(sim)
  win <- data.frame(t = tv, b = bp) %>% filter(t > (t_fork + 48), t <= (t_fork + 60))
  n <- length(bp)
  is_pk <- c(FALSE, bp[2:(n - 1)] > bp[1:(n - 2)] & bp[2:(n - 1)] > bp[3:n], FALSE)
  pkt <- tv[is_pk & tv > t_fork]
  data.frame(dt = dt_val, mean_total = mean(win$b),
            rel_amplitude = (max(win$b) - min(win$b)) / ((max(win$b) + min(win$b)) / 2),
            mean_period = mean(diff(pkt)))
}

dt_sweep_df <- bind_rows(
  dt_ref_summary,
  run_dt_case(0.002),
  run_dt_case(0.005),
  run_dt_case(0.01)
) %>%
  mutate(pct_diff_mean_total = 100 * (mean_total / dt_ref_summary$mean_total - 1),
        pct_diff_rel_amplitude = 100 * (rel_amplitude / dt_ref_summary$rel_amplitude - 1))
write.csv(dt_sweep_df, file.path(plot_dir, "day40_mort_dt_sweep.csv"), row.names = FALSE)
cat("Section 2 (dt sweep, theta=0.3 unfished cycle, FIXED mortality): see day40_mort_dt_sweep.csv.\n")
print(dt_sweep_df)

cat(paste(
  "Section 2 verdict: dt CANNOT be raised as a free speedup while the consumer side stays",
  "first-order upwind. dt=0.002 tracks the dt=0.001 reference closely (mean_total within ~0.1%,",
  "rel_amplitude within ~2%), but dt=0.005 and dt=0.01 drift further with every doubling",
  "(mean_total +7% and +13%, rel_amplitude -4% and -8%) -- exactly the numerical-diffusion",
  "signature MIZER-AGENTS.md warns about for the default upwind scheme: it smears the cycle's",
  "troughs, raising the mean and damping the amplitude. A quick check of the documented fix",
  "(second_order_w=TRUE + method='tr_bdf2') at dt=0.01 did NOT recover accuracy here -- it drove",
  "the population to numerical extinction (mean_total ~1e-33) even at dt=0.001, most likely",
  "because this project's own fork/settle heuristic (an arbitrary 0.001*w^-1.8 spectrum settled",
  "for only 10yr) was never built or validated for that discretisation, which changes the",
  "discrete steady state per project()'s own documentation. Adopting second_order_w/tr_bdf2 here",
  "is not a drop-in swap; it would need its own steady-state-finding workflow, not the ad-hoc",
  "settle-and-kick convention this file inherited from Day 20. dt therefore stays at 0.001.\n"
))

################################################################################
# Section 3: What's-Next item 1 -- a finer fish_level grid between 9 and 100
# (theta=0.3, FIXED mortality, knife_edge=10) to check whether Section 1's own
# dip-then-rise shape is real or a coarse-grid artefact.
################################################################################

fish_level_seq_fine <- c(9, 12, 15, 18, 20, 25, 30, 40, 50, 70, 100)
fine_grid_df <- cannibalism_fishing_probe(p_theta_low_FIXED, sim_fork_theta_low, fish_level_seq_fine)

full_fine_df <- bind_rows(
  redo_probe_df %>% filter(model == "theta=0.3, FIXED mortality", fish_level < 9),
  fine_grid_df
) %>% arrange(fish_level)
write.csv(full_fine_df, file.path(plot_dir, "day40_mort_finer_grid.csv"), row.names = FALSE)
cat("Section 3 (finer effort grid, theta=0.3, FIXED mortality, knife_edge=10): see day40_mort_finer_grid.csv.\n")
print(full_fine_df %>% select(fish_level, mean_total, mean_yield, rel_amplitude))

fine_yield_plot <- ggplot(full_fine_df, aes(x = fish_level, y = mean_yield)) +
  geom_line(color = "#c0392b") +
  geom_point(size = 2, color = "#c0392b") +
  scale_x_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
       title = "Finer grid confirms the dip-then-rise is real, not a coarse-grid artefact",
       subtitle = "theta=0.3, FIXED mortality, knife_edge=10 -- local peak ~fish_level=9-12, genuine dip through 15-20, second rise from 25 to 100 that overtakes the local peak") +
  theme_minimal()
save_plot(fine_yield_plot, "day40_mort_finer_yield.png", width = 9, height = 6)

cat(paste(
  "Section 3 verdict: the dip-then-rise is real, not sampling noise. Local yield peak sits at",
  "fish_level=9-12 (~0.050-0.051), a genuine dip follows through 15-20 (down to ~0.044), then a",
  "second, larger rise from 25 to 100 (0.056 -> 0.078) that ends well above the local peak.",
  "Section 0c's own aliasing lesson does NOT apply here -- the shape survives an 11-point grid",
  "spanning the whole dip-and-rise region, not just 4 widely-spaced points.\n"
))

################################################################################
# Section 4: What's-Next item 2 -- is fish_level=100 a genuinely different
# dynamical regime, or just a noisier version of the same cycle? Full
# selected/total biomass time series at fish_level=9 (local peak), 20 (dip),
# and 100 (second rise), Day 36+ sanity-check convention.
################################################################################

series_at_effort <- function(params, fork_sim, fish_level, years = scan_summary_window) {
  p <- seed_from(params, fork_sim)
  sim <- project(p, t_max = years, dt = p2$dt, t_save = 0.2,
                 t_start = t_fork, progress_bar = FALSE, effort = fish_level)
  tv <- getTimes(sim)
  data.frame(t = tv, fish_level = fish_level,
            selected = unname(getBiomass(sim, min_w = p2$w_mat)[, 1]),
            total = unname(getBiomass(sim)[, 1]))
}

regime_series_df <- bind_rows(
  series_at_effort(p_theta_low_FIXED, sim_fork_theta_low, 9),
  series_at_effort(p_theta_low_FIXED, sim_fork_theta_low, 20),
  series_at_effort(p_theta_low_FIXED, sim_fork_theta_low, 100)
) %>% filter(t > t_fork)
write.csv(regime_series_df, file.path(plot_dir, "day40_mort_regime_series.csv"), row.names = FALSE)

regime_total_plot <- ggplot(regime_series_df, aes(x = t, y = total, color = factor(fish_level))) +
  geom_line() +
  labs(x = "Time (yr)", y = "Total biomass", color = "fish_level",
       title = "Total biomass: shorter period, deeper troughs at fish_level=100",
       subtitle = "theta=0.3, FIXED mortality, knife_edge=10") +
  theme_minimal()
save_plot(regime_total_plot, "day40_mort_regime_total.png", width = 9, height = 6)

regime_sel_plot <- ggplot(regime_series_df, aes(x = t, y = selected, color = factor(fish_level))) +
  geom_line() +
  labs(x = "Time (yr)", y = "Selected (harvestable) biomass", color = "fish_level",
       title = "Selected biomass: already heavily suppressed by fish_level=9, further crushed by 100",
       subtitle = "theta=0.3, FIXED mortality, knife_edge=10") +
  theme_minimal()
save_plot(regime_sel_plot, "day40_mort_regime_selected.png", width = 9, height = 6)

cat(paste(
  "Section 4 verdict: fish_level=100 IS a genuinely different regime, not just a noisier version",
  "of the fish_level=9 cycle. Total biomass at fish_level=100 cycles visibly faster and deeper",
  "(trough ~0.09 vs. ~0.16-0.20 at fish_level=9/20, and the peak-to-trough timing compresses).",
  "Selected (harvestable) biomass is already heavily suppressed at fish_level=9 (peak ~0.023) and",
  "is crushed further by fish_level=100 (peak ~0.005) -- the same compositional-shift mechanism",
  "the Day 40 blog post's own Section 3 found for the threshold schedules (sustained pressure on",
  "the harvestable compartment relieves cannibalism on juveniles, which boom into the space that",
  "opens up), now confirmed as the mechanism behind the Section 3 dip-then-rise yield curve too:",
  "yield keeps climbing past fish_level=25 not because the fishery is healthy, but because a",
  "faster-cycling, juvenile-dominated population still throws off catchable biomass even with its",
  "harvestable compartment almost entirely suppressed.\n"
))

################################################################################
# Section 5: What's-Next item 3 -- redo Day 40 Section 5's knife_edge sweep
# under the FIXED mortality. Gear only matters once effort>0 (Day 40's own
# finding), so the existing unfished fork (sim_fork_theta_low) is reused
# across every knife_edge_size -- no re-forking needed, same shortcut Day 40
# used.
################################################################################

total_unfished_ref <- {
  sim_uf <- project(seed_from(p_theta_low_FIXED, sim_fork_theta_low), t_max = scan_summary_window,
                    dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = 0)
  mean(after_cut(getBiomass(sim_uf), sim_uf, t_fork + scan_summary_window / 2))
}

knife_edge_seq_sweep <- c(3, 5, 7, 10, 15, 20)   # spans well below/above w_mat=10
fish_level_seq_ke    <- c(1, 2, 3, 5, 9, 20, 50, 100)

knife_edge_sweep_fixed_df <- bind_rows(lapply(knife_edge_seq_sweep, function(ke) {
  p_ke <- anchovy_params(theta_low, 1, knife_edge_size = ke)
  cannibalism_fishing_probe(p_ke, sim_fork_theta_low, fish_level_seq_ke) %>%
    mutate(knife_edge_size = ke)
}))
write.csv(knife_edge_sweep_fixed_df, file.path(plot_dir, "day40_mort_knife_edge_sweep.csv"), row.names = FALSE)
cat(sprintf(
  "Section 5 (knife_edge sweep, theta=0.3, FIXED mortality, unfished total biomass reference=%.4f): see day40_mort_knife_edge_sweep.csv.\n",
  total_unfished_ref
))

ke_biomass_plot_fixed <- ggplot(knife_edge_sweep_fixed_df, aes(x = fish_level, y = pmax(mean_total, 1e-20),
                                                                color = factor(knife_edge_size))) +
  geom_line() +
  geom_point(size = 2) +
  scale_x_log10() +
  scale_y_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean total biomass (log scale)",
       color = "knife_edge_size",
       title = "FIXED mortality: small knife-edge collapse survives the fix",
       subtitle = "theta=0.3, interaction_resource=1 -- knife_edge=3/5 still crash toward extinction; knife_edge=10 (aim model) still never does") +
  theme_minimal()
save_plot(ke_biomass_plot_fixed, "day40_mort_ke_sweep_biomass.png", width = 9, height = 6)

ke_yield_plot_fixed <- ggplot(knife_edge_sweep_fixed_df, aes(x = fish_level, y = mean_yield, color = factor(knife_edge_size))) +
  geom_line() +
  geom_point(size = 2) +
  scale_x_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
       color = "knife_edge_size",
       title = "FIXED mortality: knife_edge sweep, yield vs. effort",
       subtitle = "theta=0.3, interaction_resource=1 -- ke=3's late uptick still coincides with near-collapse, not a real yield gain") +
  theme_minimal()
save_plot(ke_yield_plot_fixed, "day40_mort_ke_sweep_yield.png", width = 9, height = 6)

ke_collapse_summary_fixed <- knife_edge_sweep_fixed_df %>%
  group_by(knife_edge_size) %>%
  summarise(fraction_of_unfished_at_100 = mean_total[fish_level == 100] / total_unfished_ref,
           collapses_by_fish_level_100 = fraction_of_unfished_at_100 < 0.01, .groups = "drop")
write.csv(ke_collapse_summary_fixed, file.path(plot_dir, "day40_mort_ke_collapse_summary.csv"), row.names = FALSE)
cat("Fraction of unfished total biomass remaining at fish_level=100, by knife_edge_size (FIXED mortality):\n")
print(ke_collapse_summary_fixed)

cat(paste(
  "Section 5 verdict: the collapse-at-small-knife-edge finding SURVIVES the mortality fix,",
  "essentially unchanged in shape. knife_edge=3 and 5 still crash to near-extinction by",
  "fish_level=100 (1.5e-19 and 4.5e-06 of the unfished reference respectively). knife_edge=7 is",
  "still intermediate (27% of unfished -- declining hard but not extinct). knife_edge=10, the aim",
  "model, is if anything LESS responsive here than under the buggy mortality (99.4% of unfished",
  "remaining at fish_level=100, vs. Day 40's own ~higher-effort erosion) -- consistent with",
  "Section 3/4 above, where the same juvenile-boom mechanism keeps total biomass high even as the",
  "harvestable compartment is crushed. knife_edge=15/20 remain essentially fishing-inert (100-101%",
  "of unfished). Cutting cannibalism does not remove this failure mode at either mortality version",
  "of the model; it just relocates it to gear settings below where this project's own aim model",
  "(knife_edge=10) sits, and the fix does not move that boundary in any qualitatively new way.\n"
))

################################################################################
# Section 6: Synthesis -- should 40_experiments.R's own results be superseded?
################################################################################

cat(paste(
  "Section 6 verdict: BOTH, not either/or, and for different reasons per finding.",
  "SUPERSEDED: Section 1's own headline claim (theta=0.3 gives a clean single-peaked",
  "sustainable-yield curve, peak at fish_level=2) does not survive -- the corrected-mortality",
  "curve is peak-dip-rise, not peak-then-decline (Section 1/3 above), and the mechanism behind",
  "the second rise (Section 4 above) means fish_level=100 was never actually a safe high-yield",
  "operating point to begin with. STILL HOLDS, reported alongside rather than discarded: the",
  "structural findings that were never about the buggy mortality's exact numbers -- the",
  "threshold-schedule comparisons (Day 40 Sections 2-3, both schedules beat Constant), the",
  "compositional-shift mechanism itself (Day 40 Section 3, now independently confirmed under",
  "fixed mortality by Section 4 above), and the knife_edge collapse boundary (Day 40 Section 5,",
  "now confirmed unchanged by Section 5 above). The buggy mortality mattered for theta=0.3's own",
  "absolute numbers and its Section-1 headline shape; it did not matter for the qualitative",
  "dynamical mechanisms this project has been building up since Day 36. Both files should stay in",
  "the repo -- 40_experiments.R as the record of what the buggy-mortality analysis found and why",
  "its Section-1 claim no longer holds, this file as the corrected replacement -- rather than",
  "deleting or silently overwriting either.\n"
))

################################################################################
# Section 7: theta=0.3, interaction_resource=1.3, FIXED mortality -- redo the
# Constant-effort grid at the OTHER Overnight-grid cell this project's own aim
# model choice was weighed against (Section 0's own interaction_grid_df: at
# effort=10, ir=1.3 has fishing_sensitivity=+0.32 vs. ir=1's -0.18 -- a real
# fishing response instead of the juvenile-boom artefact Sections 3-5 found at
# ir=1). Same fork/gear-reuse convention as Sections 1 and 5.
################################################################################

ir_val <- 1.3
p_theta_ir13 <- anchovy_params(theta_low, ir_val, knife_edge_size = 10)
sim_fork_theta_ir13 <- make_anchovy_fork_sim(p_theta_ir13, t_fork)

fish_level_seq_ir13 <- c(1, 2, 3, 5, 9, 12, 15, 18, 20, 25, 30, 40, 50, 70, 100)
ir13_grid_df <- cannibalism_fishing_probe(p_theta_ir13, sim_fork_theta_ir13, fish_level_seq_ir13)
write.csv(ir13_grid_df, file.path(plot_dir, "day40_ir13_effort_grid.csv"), row.names = FALSE)
cat("Section 7 (Constant-effort grid, theta=0.3, interaction_resource=1.3, FIXED mortality, knife_edge=10): see day40_ir13_effort_grid.csv.\n")
print(ir13_grid_df %>% select(fish_level, mean_total, mean_yield, rel_amplitude))

ir13_yield_plot <- ggplot(ir13_grid_df, aes(x = fish_level, y = mean_yield)) +
  geom_line(color = "#2980b9") +
  geom_point(size = 2, color = "#2980b9") +
  scale_x_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
       title = "theta=0.3, interaction_resource=1.3: yield climbs monotonically, no peak in [1,100]",
       subtitle = "FIXED mortality, knife_edge=10 -- contrast with ir=1's peak-dip-rise; here total biomass declines gently and steadily instead") +
  theme_minimal()
save_plot(ir13_yield_plot, "day40_ir13_effort_yield.png", width = 9, height = 6)

cat(paste(
  "Section 7 verdict (confirmed live, 2026-08-16): ir=1.3 gives a genuinely different failure mode",
  "from ir=1's peak-dip-rise -- yield climbs SMOOTHLY and MONOTONICALLY across the whole [1,100]",
  "range (0.0091 at fish_level=1 to 0.0676 at fish_level=100), never turning over. Total biomass",
  "declines gently and steadily instead of the near-flat/rebounding pattern at ir=1 (0.351 unfished",
  "-> 0.307 at fish_level=100, ~87% remaining, vs. ir=1's compositional-shift rebound). rel_amplitude",
  "grows gradually (0.13 -> 0.71) rather than jumping past 1 by fish_level=9 the way ir=1 does. This",
  "is the more 'textbook' fishing response of the two -- population genuinely declines under",
  "pressure -- but it still doesn't hand this project a clean single-peaked sustainable-yield curve",
  "within the tested range; it just fails in the OPPOSITE direction from ir=1 (never turns over,",
  "rather than turning over and then recovering). Whether it turns over above fish_level=100 is",
  "untested.\n"
))

################################################################################
# Section 8: knife_edge sweep at theta=0.3, interaction_resource=1.3, FIXED
# mortality -- same gear range/fish_level grid and unfished-fork-reuse
# shortcut as Section 5.
#
# Took ~1hr in the live session to complete (vs. ~20min for the equivalent
# ir=1 sweep in Section 5) -- confirmed run, not just queued code.
################################################################################

total_unfished_ref_ir13 <- {
  sim_uf <- project(seed_from(p_theta_ir13, sim_fork_theta_ir13), t_max = scan_summary_window,
                    dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = 0)
  mean(after_cut(getBiomass(sim_uf), sim_uf, t_fork + scan_summary_window / 2))
}

knife_edge_sweep_ir13_df <- bind_rows(lapply(knife_edge_seq_sweep, function(ke) {
  p_ke <- anchovy_params(theta_low, ir_val, knife_edge_size = ke)
  cannibalism_fishing_probe(p_ke, sim_fork_theta_ir13, fish_level_seq_ke) %>%
    mutate(knife_edge_size = ke)
}))
write.csv(knife_edge_sweep_ir13_df, file.path(plot_dir, "day40_ir13_knife_edge_sweep.csv"), row.names = FALSE)
cat(sprintf(
  "Section 8 (knife_edge sweep, theta=0.3, interaction_resource=1.3, FIXED mortality, unfished total biomass reference=%.4f): see day40_ir13_knife_edge_sweep.csv.\n",
  total_unfished_ref_ir13
))
print(knife_edge_sweep_ir13_df %>% select(knife_edge_size, fish_level, mean_total, mean_yield, rel_amplitude))

ke_biomass_plot_ir13 <- ggplot(knife_edge_sweep_ir13_df, aes(x = fish_level, y = pmax(mean_total, 1e-20),
                                                              color = factor(knife_edge_size))) +
  geom_line() +
  geom_point(size = 2) +
  scale_x_log10() +
  scale_y_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean total biomass (log scale)",
       color = "knife_edge_size",
       title = "theta=0.3, interaction_resource=1.3: knife_edge sweep",
       subtitle = "FIXED mortality -- does the ir=1 collapse boundary (ke=3/5 crash, ke>=10 barely respond) hold at ir=1.3 too?") +
  theme_minimal()
save_plot(ke_biomass_plot_ir13, "day40_ir13_ke_sweep_biomass.png", width = 9, height = 6)

ke_yield_plot_ir13 <- ggplot(knife_edge_sweep_ir13_df, aes(x = fish_level, y = mean_yield, color = factor(knife_edge_size))) +
  geom_line() +
  geom_point(size = 2) +
  scale_x_log10() +
  labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
       color = "knife_edge_size",
       title = "theta=0.3, interaction_resource=1.3: knife_edge sweep, yield vs. effort",
       subtitle = "FIXED mortality") +
  theme_minimal()
save_plot(ke_yield_plot_ir13, "day40_ir13_ke_sweep_yield.png", width = 9, height = 6)

ke_collapse_summary_ir13 <- knife_edge_sweep_ir13_df %>%
  group_by(knife_edge_size) %>%
  summarise(fraction_of_unfished_at_100 = mean_total[fish_level == 100] / total_unfished_ref_ir13,
           collapses_by_fish_level_100 = fraction_of_unfished_at_100 < 0.01, .groups = "drop")
write.csv(ke_collapse_summary_ir13, file.path(plot_dir, "day40_ir13_ke_collapse_summary.csv"), row.names = FALSE)
cat("Fraction of unfished total biomass remaining at fish_level=100, by knife_edge_size (ir=1.3, FIXED mortality):\n")
print(ke_collapse_summary_ir13)

cat(paste(
  "Section 8 verdict (confirmed live): the ke=3/5 collapse and ke>=15 fishing-inert boundaries",
  "survive at ir=1.3 (ke=3: 1.1e-13 of unfished, ke=5: 0.0011, both collapsed; ke=15: 0.980, ke=20:",
  "0.999, both essentially inert), same shape as ir=1's own Section 5. What DOES move: ke=10 (this",
  "project's own aim gear) is noticeably MORE fishing-responsive at ir=1.3 (0.838 of unfished",
  "remaining at fish_level=100) than at ir=1 (0.994, Section 5) -- consistent with ir=1.3's own",
  "positive fishing_sensitivity in the Overnight grid. ke=7 sits at 0.340, intermediate as at ir=1.\n"
))

################################################################################
# Section 9: Constant/peaks/troughs threshold-schedule comparison at theta=0.3,
# interaction_resource=1.3, FIXED mortality -- Day 40 Sections 2-3's own
# machinery (thresholdFMort()), never run under the fix or at this ir value.
#
# ir=1.3 has NO interior yield peak in [1,100] (Section 7 above), so there is
# no "MSY effort" to set as the floor the way Section 1's fish_level=2 did for
# ir=1. baseline_effort is set to 2 instead -- the same nominal value Day 40
# Section 3 used for ir=1's own MSY floor -- purely to keep the two ir values
# comparable at a matched floor, not because it is this model's own optimum.
#
# Confirmed run. Machinery ported verbatim from 40_experiments.R's
# thresholdFMort()/attach_threshold_rule()/etc. (Day 36/38/39/40's own
# convention) onto this file's anchovy_params()/seed_from() builder rather
# than the buggy make_anchovy_fishing_params_theta().
################################################################################

thresholdFMort <- function(params, n, n_pp, n_other, t, effort, e_growth, pred_mort, ...) {
  p <- other_params(params)
  f_ref            <- mizerFMortGear(params, effort = 1)
  biomass_density  <- sweep(n, 2, params@w * params@dw, "*")
  selected_biomass <- sum(colSums(f_ref) * biomass_density)

  direction <- if (p$mode == "above") 1 else -1
  on_frac   <- if (isTRUE(p$hard_step)) {
    as.numeric(direction * (selected_biomass - p$threshold) > 0)
  } else {
    plogis(direction * (selected_biomass - p$threshold) / max(p$sharpness, 1e-12))
  }

  fmort_on  <- colSums(mizerFMortGear(params, effort = p$fish_level))
  fmort_off <- colSums(mizerFMortGear(params, effort = p$background_level))
  result <- on_frac * fmort_on + (1 - on_frac) * fmort_off
  dim(result)      <- dim(n)
  dimnames(result) <- dimnames(n)
  result
}

attach_threshold_rule <- function(params, threshold, fish_level, background_level = 0,
                                  mode = c("above", "below"), sharpness, hard_step = FALSE) {
  mode <- match.arg(mode)
  other_params(params) <- list(threshold = threshold, fish_level = fish_level,
                               background_level = background_level, mode = mode,
                               sharpness = sharpness, hard_step = hard_step)
  setRateFunction(params, "FMort", "thresholdFMort")
}

compute_selected_biomass_series <- function(sim, params, t_cut) {
  tv    <- getTimes(sim)
  keep  <- which(tv > t_cut)
  f_ref <- mizerFMortGear(params, effort = 1)
  vapply(keep, function(i) {
    n_i <- array(sim@n[i, , , drop = FALSE], dim = dim(sim@n)[-1])
    biomass_density <- sweep(n_i, 2, params@w * params@dw, "*")
    sum(colSums(f_ref) * biomass_density)
  }, numeric(1))
}

compute_total_biomass_series <- function(sim, t_cut) {
  tv   <- getTimes(sim)
  keep <- which(tv > t_cut)
  unname(getBiomass(sim)[, 1])[keep]
}

compute_on_frac_series <- function(sim, params, threshold, mode, sharpness, t_cut, hard_step = FALSE) {
  tv    <- getTimes(sim)
  keep  <- which(tv > t_cut)
  f_ref <- mizerFMortGear(params, effort = 1)
  direction <- if (mode == "above") 1 else -1
  vapply(keep, function(i) {
    n_i <- array(sim@n[i, , , drop = FALSE], dim = dim(sim@n)[-1])
    biomass_density  <- sweep(n_i, 2, params@w * params@dw, "*")
    selected_biomass <- sum(colSums(f_ref) * biomass_density)
    if (isTRUE(hard_step)) {
      as.numeric(direction * (selected_biomass - threshold) > 0)
    } else {
      plogis(direction * (selected_biomass - threshold) / max(sharpness, 1e-12))
    }
  }, numeric(1))
}

threshold_diagnostics <- function(sim, threshold, fish_level, background_level, mode, sharpness, t_cut, hard_step = FALSE) {
  tv      <- getTimes(sim)
  on_frac <- compute_on_frac_series(sim, sim@params, threshold, mode, sharpness, t_cut, hard_step)
  is_on   <- on_frac > 0.5
  runs   <- rle(is_on)
  n_runs <- length(runs$values)
  interior <- rep(TRUE, n_runs)
  if (n_runs > 0) { interior[1] <- FALSE; interior[n_runs] <- FALSE }
  on_lengths <- runs$lengths[runs$values & interior]
  dt_save    <- mean(diff(tv[tv > t_cut]))
  list(
    mean_effort      = mean(on_frac * fish_level + (1 - on_frac) * background_level),
    effective_window = if (length(on_lengths) > 0) mean(on_lengths) * dt_save else NA_real_,
    n_bursts         = length(on_lengths)
  )
}

scan_metrics_layered <- function(sim) {
  tv   <- getTimes(sim)
  keep <- tv > scan_t_cut
  total_bm    <- unname(getBiomass(sim)[, 1])[keep]
  selected_bm <- unname(getBiomass(sim, min_w = p2$w_mat)[, 1])[keep]
  yield_bm    <- unname(getYield(sim)[, 1])[keep]
  data.frame(min_total = min(total_bm), mean_total = mean(total_bm),
            mean_selected = mean(selected_bm), mean_juvenile = mean(total_bm - selected_bm),
            mean_yield = mean(yield_bm),
            rel_amplitude = (max(total_bm) - min(total_bm)) / ((max(total_bm) + min(total_bm)) / 2))
}

# FIXED-mortality analogue of 40_experiments.R's run_layered_ke_case_with_series(),
# built on anchovy_params()/seed_from() rather than the buggy builder.
run_layered_ke_case_fixed <- function(theta_val, ir_val, knife_edge_size, fork_sim,
                                      baseline_effort, boost_seq) {
  params <- anchovy_params(theta_val, ir_val, knife_edge_size = knife_edge_size)

  sim_const <- project(seed_from(params, fork_sim), t_max = scan_post_fork_years, dt = p2$dt, t_save = 0.2,
                       t_start = t_fork, progress_bar = FALSE, effort = baseline_effort)
  bp_const     <- compute_selected_biomass_series(sim_const, params, scan_t_cut)
  sharpness_ke <- 0.02 * (max(bp_const) - min(bp_const))
  threshold_ke <- unname(quantile(bp_const, probs = 0.5))

  const_row <- cbind(scan_metrics_layered(sim_const),
                     schedule = "Constant", boost_level = NA_real_, mean_effort = baseline_effort,
                     effective_window = NA_real_, n_bursts = NA_integer_)
  tv_const <- getTimes(sim_const)
  const_series <- data.frame(
    t = tv_const[tv_const > t_fork],
    selected_biomass = compute_selected_biomass_series(sim_const, params, t_fork),
    total_biomass = compute_total_biomass_series(sim_const, t_fork),
    on_frac = NA_real_, schedule = "Constant", boost_level = NA_real_)

  boosted <- lapply(boost_seq, function(boost) {
    lapply(c("above", "below"), function(mode) {
      schedule_name <- if (mode == "above") "Threshold (peaks)" else "Threshold (troughs)"
      p_rule <- attach_threshold_rule(params, threshold = threshold_ke, fish_level = boost,
                                      background_level = baseline_effort, mode = mode,
                                      sharpness = sharpness_ke)
      p_rule <- seed_from(p_rule, fork_sim)
      sim <- project(p_rule, t_max = scan_post_fork_years, dt = p2$dt, t_save = 0.2,
                     t_start = t_fork, progress_bar = FALSE, effort = 1)
      diag <- threshold_diagnostics(sim, threshold_ke, boost, baseline_effort, mode,
                                    sharpness_ke, scan_t_cut)
      row <- cbind(scan_metrics_layered(sim),
                  schedule = schedule_name, boost_level = boost, mean_effort = diag$mean_effort,
                  effective_window = diag$effective_window, n_bursts = diag$n_bursts)
      tv   <- getTimes(sim)
      series <- data.frame(
        t = tv[tv > t_fork],
        selected_biomass = compute_selected_biomass_series(sim, params, t_fork),
        total_biomass = compute_total_biomass_series(sim, t_fork),
        on_frac = compute_on_frac_series(sim, params, threshold_ke, mode, sharpness_ke, t_fork),
        schedule = schedule_name, boost_level = boost)
      list(row = row, series = series)
    })
  })
  boosted <- unlist(boosted, recursive = FALSE)

  list(summary = bind_rows(const_row, lapply(boosted, `[[`, "row")),
       series  = bind_rows(const_series, lapply(boosted, `[[`, "series")),
       threshold = threshold_ke, sharpness = sharpness_ke)
}

baseline_effort_ir13 <- 2                        # matched to ir=1's own MSY floor, not ir=1.3's own optimum (see comment above)
boost_seq_ir13        <- c(3, 5, 7, 9, 15, 20, 30) # same boost sequence Day 40 Section 3 used at floor=2

ir13_schedule_result <- run_layered_ke_case_fixed(theta_low, ir_val, knife_edge_size = 10,
                                                  fork_sim = sim_fork_theta_ir13,
                                                  baseline_effort = baseline_effort_ir13,
                                                  boost_seq = boost_seq_ir13)
ir13_schedule_df <- ir13_schedule_result$summary
write.csv(ir13_schedule_df, file.path(plot_dir, "day40_ir13_schedule_summary.csv"), row.names = FALSE)
write.csv(ir13_schedule_result$series, file.path(plot_dir, "day40_ir13_schedule_series.csv"), row.names = FALSE)
cat(sprintf(
  "Section 9 (Constant/peaks/troughs, theta=0.3, interaction_resource=1.3, FIXED mortality, knife_edge=10, floor=%.2g): see day40_ir13_schedule_summary.csv.\n",
  baseline_effort_ir13
))
print(ir13_schedule_df %>% select(schedule, boost_level, mean_effort, mean_total, mean_yield, rel_amplitude))

ir13_schedule_yield_plot <- ggplot(ir13_schedule_df, aes(x = mean_effort, y = mean_yield, color = schedule)) +
  geom_line(aes(group = schedule)) +
  geom_point(size = 2) +
  labs(x = "Mean realised fishing effort", y = "Mean yield", color = NULL,
       title = "theta=0.3, interaction_resource=1.3: does a threshold schedule beat Constant here too?",
       subtitle = sprintf("FIXED mortality, knife_edge=10, floor=%.2g", baseline_effort_ir13)) +
  theme_minimal()
save_plot(ir13_schedule_yield_plot, "day40_ir13_schedule_yield.png", width = 9, height = 6)

ir13_schedule_amplitude_plot <- ggplot(ir13_schedule_df, aes(x = mean_effort, y = rel_amplitude, color = schedule)) +
  geom_line(aes(group = schedule)) +
  geom_point(size = 2) +
  labs(x = "Mean realised fishing effort", y = "Relative amplitude", color = NULL,
       title = "theta=0.3, interaction_resource=1.3: schedule amplitude vs. effort",
       subtitle = sprintf("FIXED mortality, knife_edge=10, floor=%.2g", baseline_effort_ir13)) +
  theme_minimal()
save_plot(ir13_schedule_amplitude_plot, "day40_ir13_schedule_amplitude.png", width = 9, height = 6)

cat(paste(
  "Section 9 verdict (confirmed live): both schedules beat Constant on yield at every boost, same",
  "qualitative finding as ir=1 (Day 40 Section 3). Constant's own mean_yield=0.0161; 'peaks' barely",
  "moves (0.0168-0.0171 across boost=3-30 -- it almost never fires, n_bursts=0 at every boost,",
  "because ir=1.3's own low-amplitude cycle rarely crosses back above the median threshold once",
  "fishing starts). 'Troughs' is where the real gain is: mean_yield climbs from 0.0193 (boost=3) to",
  "0.0681 (boost=30) -- more than 4x Constant -- while rel_amplitude grows from 0.13 to 0.48, still",
  "well short of the near-2.0 collapse ceiling Day 39 found in the original model. Unlike ir=1",
  "(Section 3, Day 40), there is no late amplitude jump here -- rel_amplitude climbs smoothly with",
  "boost rather than staying flat then jumping.\n"
))

################################################################################
# Section 10: full sweep suite (effort grid + knife_edge sweep + threshold
# schedule) at the two extremes of the Overnight interaction_grid_df's own
# fishing_sensitivity column (at effort=10), restricted to theta<1 -- theta=1
# is already this project's extensively-studied baseline, so the comparison
# that matters is within the cannibalism-cut range the project is actually
# exploring:
#   - theta=0.5, interaction_resource=2   (sensitivity=+0.372, most positive
#     among theta<1 -- essentially tied with theta=1/ir=3's own +0.377)
#   - theta=0.7, interaction_resource=5   (sensitivity=-0.885, most negative
#     in the whole 5x5 grid)
# Both use knife_edge=10 for continuity with every other section in this file.
#
# Confirmed run (both this section and Section 11 completed live).
#
# run_full_sweep_suite() generalises Sections 7-9's own three-part pattern
# (effort grid -> knife_edge sweep -> threshold schedule at that model's own
# MSY floor, or a default floor of 2 if the effort grid has no interior peak,
# matching Section 9's own reasoning for ir=1.3) into one function so it can
# be called once per parameter point instead of duplicating ~150 lines twice.
################################################################################

run_full_sweep_suite <- function(theta_val, ir_val, label, knife_edge_size = 10,
                                 fish_level_seq_grid = c(1, 2, 3, 5, 9, 12, 15, 18, 20, 25, 30, 40, 50, 70, 100),
                                 knife_edge_seq = c(3, 5, 7, 10, 15, 20),
                                 fish_level_seq_ke_local = c(1, 2, 3, 5, 9, 20, 50, 100),
                                 boost_seq = c(3, 5, 7, 9, 15, 20, 30),
                                 default_floor = 2) {
  params   <- anchovy_params(theta_val, ir_val, knife_edge_size = knife_edge_size)
  fork_sim <- make_anchovy_fork_sim(params, t_fork)

  # -- Constant-effort grid --
  grid_df <- cannibalism_fishing_probe(params, fork_sim, fish_level_seq_grid)
  write.csv(grid_df, file.path(plot_dir, sprintf("day40_%s_effort_grid.csv", label)), row.names = FALSE)
  peak_row          <- grid_df[which.max(grid_df$mean_yield), ]
  has_interior_peak <- peak_row$fish_level < max(grid_df$fish_level)
  baseline_effort   <- if (has_interior_peak) peak_row$fish_level else default_floor

  yield_plot <- ggplot(grid_df, aes(x = fish_level, y = mean_yield)) +
    geom_line(color = "#8e44ad") +
    geom_point(size = 2, color = "#8e44ad") +
    scale_x_log10() +
    labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
         title = sprintf("theta=%.1f, interaction_resource=%.1f: Constant-effort yield curve", theta_val, ir_val),
         subtitle = sprintf("FIXED mortality, knife_edge=%d -- %s", knife_edge_size,
                            if (has_interior_peak) sprintf("interior peak at fish_level=%.2g", peak_row$fish_level)
                            else "no interior peak in tested range")) +
    theme_minimal()
  save_plot(yield_plot, sprintf("day40_%s_effort_yield.png", label), width = 9, height = 6)

  # -- knife_edge sweep (reuses the unfished fork -- gear only matters once effort>0) --
  total_unfished_ref <- {
    sim_uf <- project(seed_from(params, fork_sim), t_max = scan_summary_window,
                      dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = 0)
    mean(after_cut(getBiomass(sim_uf), sim_uf, t_fork + scan_summary_window / 2))
  }
  ke_df <- bind_rows(lapply(knife_edge_seq, function(ke) {
    p_ke <- anchovy_params(theta_val, ir_val, knife_edge_size = ke)
    cannibalism_fishing_probe(p_ke, fork_sim, fish_level_seq_ke_local) %>%
      mutate(knife_edge_size = ke)
  }))
  write.csv(ke_df, file.path(plot_dir, sprintf("day40_%s_knife_edge_sweep.csv", label)), row.names = FALSE)

  ke_biomass_plot <- ggplot(ke_df, aes(x = fish_level, y = pmax(mean_total, 1e-20), color = factor(knife_edge_size))) +
    geom_line() + geom_point(size = 2) + scale_x_log10() + scale_y_log10() +
    labs(x = "Fishing effort (Constant, log scale)", y = "Mean total biomass (log scale)",
         color = "knife_edge_size",
         title = sprintf("theta=%.1f, interaction_resource=%.1f: knife_edge sweep", theta_val, ir_val),
         subtitle = "FIXED mortality") +
    theme_minimal()
  save_plot(ke_biomass_plot, sprintf("day40_%s_ke_sweep_biomass.png", label), width = 9, height = 6)

  ke_yield_plot <- ggplot(ke_df, aes(x = fish_level, y = mean_yield, color = factor(knife_edge_size))) +
    geom_line() + geom_point(size = 2) + scale_x_log10() +
    labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield", color = "knife_edge_size",
         title = sprintf("theta=%.1f, interaction_resource=%.1f: knife_edge sweep, yield vs. effort", theta_val, ir_val),
         subtitle = "FIXED mortality") +
    theme_minimal()
  save_plot(ke_yield_plot, sprintf("day40_%s_ke_sweep_yield.png", label), width = 9, height = 6)

  ke_collapse_summary <- ke_df %>%
    group_by(knife_edge_size) %>%
    summarise(fraction_of_unfished_at_100 = mean_total[fish_level == 100] / total_unfished_ref,
             collapses_by_fish_level_100 = fraction_of_unfished_at_100 < 0.01, .groups = "drop")
  write.csv(ke_collapse_summary, file.path(plot_dir, sprintf("day40_%s_ke_collapse_summary.csv", label)), row.names = FALSE)

  # -- threshold schedule: Constant/peaks/troughs, floor = this model's own MSY
  # if the effort grid found one, else default_floor (mirrors Section 9's own
  # reasoning for ir=1.3, which has no interior peak) --
  schedule_result <- run_layered_ke_case_fixed(theta_val, ir_val, knife_edge_size = knife_edge_size,
                                               fork_sim = fork_sim, baseline_effort = baseline_effort,
                                               boost_seq = boost_seq[boost_seq > baseline_effort])
  write.csv(schedule_result$summary, file.path(plot_dir, sprintf("day40_%s_schedule_summary.csv", label)), row.names = FALSE)
  write.csv(schedule_result$series, file.path(plot_dir, sprintf("day40_%s_schedule_series.csv", label)), row.names = FALSE)

  schedule_yield_plot <- ggplot(schedule_result$summary, aes(x = mean_effort, y = mean_yield, color = schedule)) +
    geom_line(aes(group = schedule)) + geom_point(size = 2) +
    labs(x = "Mean realised fishing effort", y = "Mean yield", color = NULL,
         title = sprintf("theta=%.1f, interaction_resource=%.1f: Constant/peaks/troughs", theta_val, ir_val),
         subtitle = sprintf("FIXED mortality, knife_edge=%d, floor=%.2g", knife_edge_size, baseline_effort)) +
    theme_minimal()
  save_plot(schedule_yield_plot, sprintf("day40_%s_schedule_yield.png", label), width = 9, height = 6)

  schedule_amplitude_plot <- ggplot(schedule_result$summary, aes(x = mean_effort, y = rel_amplitude, color = schedule)) +
    geom_line(aes(group = schedule)) + geom_point(size = 2) +
    labs(x = "Mean realised fishing effort", y = "Relative amplitude", color = NULL,
         title = sprintf("theta=%.1f, interaction_resource=%.1f: schedule amplitude vs. effort", theta_val, ir_val),
         subtitle = sprintf("FIXED mortality, knife_edge=%d, floor=%.2g", knife_edge_size, baseline_effort)) +
    theme_minimal()
  save_plot(schedule_amplitude_plot, sprintf("day40_%s_schedule_amplitude.png", label), width = 9, height = 6)

  list(params = params, fork_sim = fork_sim, grid = grid_df, has_interior_peak = has_interior_peak,
       baseline_effort = baseline_effort, total_unfished_ref = total_unfished_ref,
       ke_sweep = ke_df, ke_collapse_summary = ke_collapse_summary, schedule = schedule_result)
}

suite_theta05_ir2 <- run_full_sweep_suite(0.5, 2, "theta05_ir2")
cat(sprintf(
  "Section 10 (theta=0.5, interaction_resource=2, most positive fishing_sensitivity among theta<1): %s, threshold-schedule floor used=%.2g. See day40_theta05_ir2_*.csv/png.\n",
  if (suite_theta05_ir2$has_interior_peak) sprintf("interior yield peak at fish_level=%.2g", suite_theta05_ir2$grid$fish_level[which.max(suite_theta05_ir2$grid$mean_yield)]) else "no interior yield peak in [1,100]",
  suite_theta05_ir2$baseline_effort
))
print(suite_theta05_ir2$grid %>% select(fish_level, mean_total, mean_yield, rel_amplitude))
print(suite_theta05_ir2$ke_collapse_summary)
print(suite_theta05_ir2$schedule$summary %>% select(schedule, boost_level, mean_effort, mean_total, mean_yield, rel_amplitude))

cat(paste(
  "Section 10 verdict (confirmed live): the MOST fishing-responsive point tested in this whole",
  "project so far. No interior yield peak (mean_total falls smoothly and steadily from 0.367",
  "unfished to 0.229 at fish_level=100, a genuine ~38% decline -- the biggest of any point tested).",
  "knife_edge=10 (this project's own aim gear) loses 42% of unfished biomass by fish_level=100",
  "(fraction remaining=0.584) -- more responsive than ir=1 (0.994), ir=1.3 (0.838), or ir=1's own",
  "theta=1 baseline. ke=3 still collapses outright (8.9e-11); ke=5 is now borderline (0.083, just",
  "above the collapse cutoff) rather than clearly intermediate. The threshold schedule barely",
  "matters here: 'peaks' never fires (n_bursts=0 at every boost, mean_effort stays ~2.0 = the",
  "floor) because the Constant cycle's own amplitude is too small to cross back above its median;",
  "'troughs' produces a smooth, well-behaved yield/biomass trade-off (yield 0.0139->0.0503,",
  "rel_amplitude staying under 0.03 throughout) -- no oscillation blow-up anywhere. This is the",
  "closest thing to a textbook, monotonically-responsive fishery this project has found.\n"
))

################################################################################
# Section 11: the other extreme -- theta=0.7, interaction_resource=5, the most
# negative fishing_sensitivity (-0.885) in the whole Overnight grid. Same
# run_full_sweep_suite() as Section 10, confirmed run.
################################################################################

suite_theta07_ir5 <- run_full_sweep_suite(0.7, 5, "theta07_ir5")
cat(sprintf(
  "Section 11 (theta=0.7, interaction_resource=5, most negative fishing_sensitivity in the whole grid): %s, threshold-schedule floor used=%.2g. See day40_theta07_ir5_*.csv/png.\n",
  if (suite_theta07_ir5$has_interior_peak) sprintf("interior yield peak at fish_level=%.2g", suite_theta07_ir5$grid$fish_level[which.max(suite_theta07_ir5$grid$mean_yield)]) else "no interior yield peak in [1,100]",
  suite_theta07_ir5$baseline_effort
))
print(suite_theta07_ir5$grid %>% select(fish_level, mean_total, mean_yield, rel_amplitude))
print(suite_theta07_ir5$ke_collapse_summary)
print(suite_theta07_ir5$schedule$summary %>% select(schedule, boost_level, mean_effort, mean_total, mean_yield, rel_amplitude))

cat(paste(
  "Section 11 verdict (confirmed live): the most extreme cultivation-effect regime found in this",
  "project. Total biomass RISES under fishing at low-to-moderate effort (0.662 unfished ->",
  "0.732 peak at fish_level=9), then declines only slowly, still exceeding the unfished level at",
  "fish_level=30 (0.663) and only reaching 0.574 (87% of unfished) by fish_level=100. No knife_edge",
  "tested collapses -- not even ke=3, which crashed to near-extinction at EVERY other theta/ir",
  "combination in this file (0.453 of unfished remaining here, vs. ~1e-13 to 1e-19 everywhere",
  "else). ke=15 and ke=20 end up ABOVE their own unfished reference at fish_level=100 (1.207 and",
  "1.131 respectively) -- fishing with that gear leaves MORE fish in the sea than not fishing at",
  "all. The threshold schedule is correspondingly unremarkable: 'peaks' is flat (n_bursts=0",
  "throughout, mean_effort ~2.0), 'troughs' pushes mean_total up further at low boost (0.779 ->",
  "0.808 at boost=5) before it eventually declines at boost=30 (0.676) -- rel_amplitude never",
  "exceeds 0.12 anywhere, barely above Constant's own 0.109. Nothing in this parameter regime is",
  "fragile; the open question is whether it is fragile at ANY effort level tested vs. untested",
  "higher efforts, not which schedule protects it.\n"
))

################################################################################
# Section 12: Overnight fine theta x interaction_resource x knife_edge x
# effort sweep -- CSV only, no heatmap/plot (a grid this fine on three
# categorical axes would be unreadable as a plot; the CSV is the deliverable,
# to be filtered/sorted after the fact). Goal: find a regime that genuinely
# goes extinct by fish_level=100, something none of Sections 1-11 found at
# knife_edge=10 -- but Section 5/8/10's own knife_edge sweeps already showed
# small knife_edge (3/5) collapses most theta/ir combinations tested so far
# (the one exception being theta=0.7/ir=5, Section 11, which didn't collapse
# even at knife_edge=3). Varying knife_edge alongside theta and
# interaction_resource searches all three axes that have moved this model's
# fishing response so far, rather than holding gear fixed at this project's
# own aim value of 10.
#
# Grid:
#   theta_seq_fine       <- c(1, 0.7, 0.5, 0.3, 0.1)            (5, matches the
#                            Overnight grid's own theta_grid_seq for continuity)
#   ir_seq_fine           <- c(0.3, 0.7, 1, 1.3, 2, 3, 5, 10)    (8, extends
#                            BELOW 1 -- untested by every section above, on the
#                            hypothesis that restricting resource access starves
#                            the compositional-shift juvenile boom that has
#                            buffered every theta=0.3 variant tested so far)
#   knife_edge_seq_fine   <- c(3, 5, 7, 10, 15)                  (5, matches
#                            knife_edge_seq_sweep exactly)
#   fish_level_seq_fine   <- c(1, 5, 9, 20, 50, 70, 85, 100)     (8, concentrated
#                            toward the top of [1,100] where collapse would show)
#
# run_fine_sweep_theta_ir() builds ONE fork simulation and ONE unfished
# reference per (theta, ir) pair -- both are gear-independent (effort=0 means
# no fishing regardless of knife_edge_size, the same shortcut Sections 5/8/10/
# 11 all use) -- and reuses them across every knife_edge_size, rather than
# re-forking per (theta, ir, knife_edge) triple. That keeps the total fished-
# projection count at n_theta*n_ir*n_ke*n_effort = 5*8*5*8 = 1600, plus only
# 40 forks and 40 unfished references (not 200 of each).
#
# NOT sized for the interactive session -- this file's own single knife_edge
# sweeps (48 projections) have taken 20min to over an hour each live; this is
# ~35x that scale. Run as a batch job, e.g.
#   Rscript -e 'source("finding_jams/40_changed_mort_experiments.R")'
# from a terminal, not the interactive r-mizer session. Results are appended
# to the CSV after every (theta, ir) pair's full knife_edge x effort block
# finishes (40 checkpoints), so a partial or interrupted run still leaves
# usable data -- check day40_fine_extinction_sweep.csv directly rather than
# waiting for the whole grid. Delete that file before re-running from scratch;
# the incremental-append logic otherwise mixes old and new rows. If this looks
# too slow after the first few (theta, ir) pairs, thin theta_seq_fine /
# ir_seq_fine / knife_edge_seq_fine / fish_level_seq_fine and restart.
################################################################################

theta_seq_fine       <- c(1, 0.7, 0.5, 0.3, 0.1)
ir_seq_fine          <- c(0.3, 0.7, 1, 1.3, 2, 3, 5, 10)
knife_edge_seq_fine  <- c(3, 5, 7, 10, 15)
fish_level_seq_fine  <- c(1, 5, 9, 20, 50, 70, 85, 100)

fine_sweep_path <- file.path(plot_dir, "day40_fine_extinction_sweep.csv")

run_fine_sweep_theta_ir <- function(theta_val, ir_val, knife_edge_seq, fish_level_seq) {
  # Fork and unfished reference are gear-independent -- built ONCE per
  # (theta, ir) and reused across every knife_edge_size.
  params_ref <- anchovy_params(theta_val, ir_val, knife_edge_size = knife_edge_seq[1])
  fork_sim   <- make_anchovy_fork_sim(params_ref, t_fork)

  total_unfished_ref <- {
    sim_uf <- project(seed_from(params_ref, fork_sim), t_max = scan_summary_window,
                      dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = 0)
    mean(after_cut(getBiomass(sim_uf), sim_uf, t_fork + scan_summary_window / 2))
  }

  bind_rows(lapply(knife_edge_seq, function(ke) {
    p_ke    <- anchovy_params(theta_val, ir_val, knife_edge_size = ke)
    grid_df <- cannibalism_fishing_probe(p_ke, fork_sim, fish_level_seq)
    grid_df$knife_edge_size      <- ke
    grid_df$theta                <- theta_val
    grid_df$interaction_resource <- ir_val
    grid_df$total_unfished_ref   <- total_unfished_ref
    grid_df$fraction_of_unfished <- grid_df$mean_total / total_unfished_ref
    grid_df
  }))
}

# Incremental: append each (theta, ir) pair's rows to CSV as soon as its whole
# knife_edge x effort block is done, rather than holding everything in memory
# and writing once at the very end -- a partial/interrupted run still leaves
# readable results.
for (theta_val in theta_seq_fine) {
  for (ir_val in ir_seq_fine) {
    cell_df <- run_fine_sweep_theta_ir(theta_val, ir_val, knife_edge_seq_fine, fish_level_seq_fine)
    write.table(cell_df, fine_sweep_path, sep = ",", row.names = FALSE,
               col.names = !file.exists(fine_sweep_path), append = file.exists(fine_sweep_path))
    best_row <- cell_df[cell_df$fish_level == 100, ][which.min(cell_df$fraction_of_unfished[cell_df$fish_level == 100]), ]
    cat(sprintf(
      "theta=%.2f, ir=%.2f done -- best (lowest fraction_of_unfished) at fish_level=100: knife_edge=%d, fraction=%.4g\n",
      theta_val, ir_val, best_row$knife_edge_size, best_row$fraction_of_unfished
    ))
  }
}

fine_sweep_df <- read.csv(fine_sweep_path)
cat(sprintf(
  "Section 12: fine theta x interaction_resource x knife_edge x effort sweep complete -- %d rows across %d (theta, ir) x %d knife_edge combinations. See day40_fine_extinction_sweep.csv.\n",
  nrow(fine_sweep_df), length(theta_seq_fine) * length(ir_seq_fine), length(knife_edge_seq_fine)
))

extinction_candidates <- fine_sweep_df %>%
  filter(fish_level == 100, fraction_of_unfished < 0.01) %>%
  arrange(fraction_of_unfished)
cat(sprintf("%d candidate regime(s) with <1%% of unfished biomass remaining at fish_level=100:\n", nrow(extinction_candidates)))
print(extinction_candidates %>% select(theta, interaction_resource, knife_edge_size, mean_total, fraction_of_unfished))

survivors_ke3 <- fine_sweep_df %>%
  filter(fish_level == 100, knife_edge_size == 3, fraction_of_unfished >= 0.01) %>%
  arrange(desc(fraction_of_unfished))
cat(sprintf("%d combination(s) that do NOT collapse even at knife_edge=3 (the smallest gear tested):\n", nrow(survivors_ke3)))
print(survivors_ke3 %>% select(theta, interaction_resource, fraction_of_unfished))

cat(paste(
  "Section 12 verdict (confirmed, 40 (theta,ir) pairs x 5 knife_edge values = 200 cells run",
  "overnight): the fine sweep found the extinction regime this project was looking for -- 42 of 200",
  "(theta, interaction_resource, knife_edge) cells collapse to <1% of unfished biomass by",
  "fish_level=100 (21/40 at knife_edge=3,",
  "16/40 at knife_edge=5, 5/40 at knife_edge=7, 0/40 at knife_edge=10 or 15 in this grid). knife_edge",
  "is overwhelmingly the dominant lever, not theta or interaction_resource -- collapse at fish_level=",
  "100 happens across a WIDE range of theta/ir combinations once the gear is small enough, echoing",
  "Section 5's own original knife_edge=3/5 finding for theta=0.3/ir=1 rather than overturning it.",
  "The single cleanest example, and the one requiring no new parameters this project hasn't already",
  "adopted: theta=0.3 (this project's own aim theta), interaction_resource=1 (default), knife_edge=3.",
  "Its full trajectory is a genuine cliff-edge, not a gradual decline: biomass sits ABOVE the",
  "unfished reference at low-to-moderate effort (fraction=1.05-1.40 across fish_level=1-9, a",
  "cultivation-effect boost), crashes hard between fish_level=9 and 20 (fraction 1.05 -> 0.20), and",
  "is functionally extinct by fish_level=50 (fraction=4.3e-9) -- well before reaching 100, not",
  "marginally at it. The flip side is equally informative: interaction_resource=10 is protective",
  "against gear-driven collapse specifically, not just effort-driven collapse -- every theta paired",
  "with ir=10 survives even knife_edge=3 with 66-88% of unfished biomass intact, the most robust",
  "corner of the whole grid. theta=0.7/interaction_resource=5 (Section 11's own pick, the most",
  "negative fishing_sensitivity in the Overnight grid) sits mid-pack among survivors at ke=3 (45%",
  "remaining) rather than being uniquely special -- its Section 11 resilience was specific to",
  "knife_edge=10, not a general immunity to fishing pressure at every gear setting.\n"
))

################################################################################
# Section 13: does the Section 12 extinction regime (theta=0.3,
# interaction_resource=1, knife_edge=3) actually oscillate as effort rises
# toward its own collapse cliff, and does it have a genuine interior MSY peak
# before that cliff -- or does yield just climb monotonically into the crash
# the way Day 40's own caveat about "late yield upticks" warned about?
#
# Written to be run in the user's own session, not executed here. Gear is
# irrelevant to the unfished fork (established repeatedly above), so
# sim_fork_theta_low (already built for theta=0.3, ir=1 at the top of this
# file) is reused directly rather than re-forking at knife_edge=3.
################################################################################

p_extinct <- anchovy_params(theta_low, 1, knife_edge_size = 3)

## -- 13a: oscillation check -------------------------------------------------
# Full selected/total biomass time series at a run of effort levels spanning
# unfished through Section 12's own known collapse zone (fraction_of_unfished
# was 1.05 at fish_level=9, 0.20 at fish_level=20 -- the cliff sits somewhere
# in between), plus one point past it, to see whether cycling persists, damps,
# or breaks down before the population actually crashes.

osc_effort_seq <- c(0, 5, 9, 15, 18, 20, 25)

osc_series_df <- bind_rows(lapply(osc_effort_seq, function(fl) {
  sim <- project(seed_from(p_extinct, sim_fork_theta_low), t_max = scan_post_fork_years,
                 dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = fl)
  tv <- getTimes(sim)
  data.frame(t = tv[tv > t_fork], fish_level = fl,
            selected = unname(getBiomass(sim, min_w = p2$w_mat)[, 1])[tv > t_fork],
            total    = unname(getBiomass(sim)[, 1])[tv > t_fork])
}))
write.csv(osc_series_df, file.path(plot_dir, "day40_extinct_osc_series.csv"), row.names = FALSE)

# Peak-to-peak period and amplitude per effort level, same convention as
# Section 0c's own cycle-period check, applied here across the whole
# osc_effort_seq rather than just the unfished case.
osc_period_summary <- bind_rows(lapply(osc_effort_seq, function(fl) {
  d  <- osc_series_df %>% filter(fish_level == fl) %>% arrange(t)
  bp <- d$total
  n  <- length(bp)
  if (n < 3 || all(bp < 1e-30)) {
    return(data.frame(fish_level = fl, mean_period = NA_real_, n_peaks = 0,
                      mean_total = mean(bp), rel_amplitude = NA_real_))
  }
  is_pk <- c(FALSE, bp[2:(n-1)] > bp[1:(n-2)] & bp[2:(n-1)] > bp[3:n], FALSE)
  pkt   <- d$t[is_pk]
  data.frame(fish_level = fl, mean_period = if (length(pkt) > 1) mean(diff(pkt)) else NA_real_,
            n_peaks = length(pkt), mean_total = mean(bp),
            rel_amplitude = (max(bp) - min(bp)) / ((max(bp) + min(bp)) / 2))
}))
write.csv(osc_period_summary, file.path(plot_dir, "day40_extinct_osc_period_summary.csv"), row.names = FALSE)
cat("Section 13a (oscillation check, theta=0.3, ir=1, knife_edge=3): see day40_extinct_osc_period_summary.csv.\n")
print(osc_period_summary)

osc_plot <- ggplot(osc_series_df, aes(x = t, y = total)) +
  geom_line(color = "#16a085") +
  facet_wrap(~ sprintf("fish_level=%g", fish_level), scales = "free_y", ncol = 2) +
  labs(x = "Time (yr)", y = "Total biomass",
       title = "theta=0.3, interaction_resource=1, knife_edge=3: does the cycle survive on the way to collapse?",
       subtitle = "FIXED mortality -- unfished (0) through Section 12's own known collapse zone (9->20) and past it (25)") +
  theme_minimal()
save_plot(osc_plot, "day40_extinct_osc_series.png", width = 9, height = 10)

## -- 13b: MSY-peak check -----------------------------------------------------
# Fine effort grid spanning the same collapse zone, to check whether yield
# has a genuine interior peak before the cliff or just climbs monotonically
# into it -- Day 40's own caveat (Section 5, this file) warned that a late
# yield "uptick" right before collapse is a transient fished-down-population
# artefact, not a real sustainable peak; this resolves whether that applies
# here too.

msy_check_seq <- c(1, 2, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 25, 28, 30)
extinct_msy_df <- cannibalism_fishing_probe(p_extinct, sim_fork_theta_low, msy_check_seq)
write.csv(extinct_msy_df, file.path(plot_dir, "day40_extinct_msy_check.csv"), row.names = FALSE)
cat("Section 13b (fine MSY check, theta=0.3, ir=1, knife_edge=3): see day40_extinct_msy_check.csv.\n")
print(extinct_msy_df %>% select(fish_level, mean_total, mean_yield, rel_amplitude))

extinct_msy_plot <- ggplot(extinct_msy_df, aes(x = fish_level, y = mean_yield)) +
  geom_line(color = "#c0392b") +
  geom_point(size = 2, color = "#c0392b") +
  labs(x = "Fishing effort (Constant)", y = "Mean yield",
       title = "theta=0.3, interaction_resource=1, knife_edge=3: is there a real MSY peak before the cliff?",
       subtitle = "FIXED mortality -- fine grid across the fish_level=1-30 collapse zone") +
  theme_minimal()
save_plot(extinct_msy_plot, "day40_extinct_msy_check.png", width = 9, height = 6)

peak_row_extinct <- extinct_msy_df[which.max(extinct_msy_df$mean_yield), ]
collapse_row     <- extinct_msy_df %>% filter(mean_total < 0.01 * max(extinct_msy_df$mean_total)) %>% slice(1)
cat(sprintf(
  "Section 13b: peak mean_yield=%.4f at fish_level=%.2g; population collapses (mean_total < 1%% of its own peak) starting at fish_level=%s. Compare peak_row_extinct's own fish_level against collapse_row's to see whether the peak sits BEFORE the collapse threshold (a real MSY) or AT/immediately before it (Day 40's own 'late uptick' artefact).\n",
  peak_row_extinct$mean_yield, peak_row_extinct$fish_level,
  if (nrow(collapse_row) > 0) as.character(collapse_row$fish_level) else "none in this range"
))

cat(paste(
  "Section 13 verdict (confirmed live, 2026-08-17): BOTH questions answered, and the two results",
  "explain each other.",
  "",
  "13a -- YES it oscillates, and not in the way a simple 'cycling stops before collapse' story would",
  "predict. Period COMPRESSES as effort rises rather than the cycle damping out: mean_period=5.7yr",
  "unfished (4 peaks over 24yr) -> 5.5yr at fish_level=9 (still within Section 12's own 'above",
  "unfished' zone) -> 2.24yr at fish_level=15 (10 peaks) -> 1.71yr at fish_level=18 (14 peaks) ->",
  "1.59yr at fish_level=20 (15 peaks) -> 1.18yr at fish_level=25 (20 peaks) -- nearly annual cycling",
  "by the time the population is deep in collapse. rel_amplitude stays large throughout (1.7-1.9",
  "across fish_level=9-18, dipping to 0.60 at fish_level=20 before climbing back to 0.97 at",
  "fish_level=25) -- this is a population flickering faster and faster at ever-lower absolute",
  "biomass, not a smooth monotonic decay and not a damped return to a stable equilibrium.",
  "",
  "13b -- there IS a numerical peak in mean_yield (0.3661 at fish_level=18), but it is NOT a genuine",
  "sustainable MSY -- it is exactly the 'late uptick' artefact Day 40's own Section 5 caveat warned",
  "about. mean_total is monotonically declining across the ENTIRE fine grid with no sign of",
  "restabilising (0.522 at fish_level=7, already down to 0.107 by the yield peak at fish_level=18,",
  "0.0106 by fish_level=30, and Section 12's own coarser grid shows <1e-9 by fish_level=50) -- the",
  "yield peak is measured while the population is actively mid-collapse, not at a settled",
  "equilibrium, and 13a confirms the dynamics underneath it are still rapidly cycling rather than",
  "having stabilised. collapse_row above reports 'none in this range' only because this fine grid",
  "stops at fish_level=30, well before the population actually crosses 1% of its own unfished",
  "reference (that happens by fish_level=50, per Section 12) -- not because the population has",
  "recovered or stabilised.",
  "",
  "One data anomaly worth flagging rather than reading into: fish_level=7 shows a yield DIP",
  "(mean_yield=0.0675, versus 0.108 at fish_level=5 and 0.127 at fish_level=9) despite having the",
  "HIGHEST mean_total in the whole grid (0.522) and an anomalously low rel_amplitude (0.41 vs. 1.05-",
  "1.9 everywhere else nearby) -- almost certainly the 12-year averaging window landing on an",
  "unusually trough-heavy phase of the still-large-amplitude cycle at that specific effort level, the",
  "same sampling-window-phase sensitivity flagged elsewhere in this project (Day 40 Section 3's own",
  "caveat), not a real feature of the fish_level=7 dynamics.\n"
))

################################################################################
# Section 14: fine Constant-effort scan across the "promising" (theta,
# interaction_resource, knife_edge) combinations from Section 12's own fine
# sweep, screening for a genuine MSY under constant fishing -- CSV only, no
# plot (56 combinations x 10 effort points would be as unreadable as a plot as
# Section 12's own full grid was).
#
# "Promising" = Section 12's own day40_fine_extinction_sweep.csv rows where
# fishing meaningfully reduces biomass by fish_level=100 WITHOUT the
# population already being extinct there: 0.03 < fraction_of_unfished < 0.6 at
# fish_level=100. That excludes both the barely-responsive combinations
# (fraction near 1, no real fishing pressure to speak of) and the flagship
# extinction regime itself (theta=0.3, ir=1, knife_edge=3, fraction=1.5e-19 --
# Section 13 already found its own yield "peak" is a late-uptick artefact on
# the way to total collapse, not a real MSY). This section checks whether any
# of the 56 combinations in between -- declining meaningfully but not yet
# extinct by fish_level=100 -- have a genuine interior yield peak instead.
#
# msy_scan_effort_seq spans 1 to 100 with 10 points, denser below 30 (where
# Section 13's own extinction-regime peak/collapse zone sat) and sparse above
# it (just 50 and 100) -- kept deliberately coarse past effort=30 to keep this
# runnable in a single sitting rather than another overnight job. This is a
# screen for WHETHER an interior peak exists per combination, not a precise
# fix on where it sits; any combination that looks promising here is worth a
# second, finer pass (like Section 13b's own 21-point grid) on its own.
#
# Each combination gets its OWN fork (unlike Section 12, which reused one fork
# per (theta, ir) pair across knife_edge values) because every row here
# already specifies one exact (theta, ir, knife_edge) triple, not a knife_edge
# sweep -- no reuse opportunity the way Section 12 had.
#
# Sized for a single sitting, not an overnight run: 56 combinations x 10
# effort points = 560 fished projections plus 56 forks. Still substantial --
# the 56 forks alone are roughly equivalent to another ~90 fished projections
# worth of compute -- so this can still take a while in the interactive
# session; consider Rscript from a terminal if it runs longer than expected.
# Results are appended to the CSV after every combination finishes, so a
# partial/interrupted run still leaves usable data. Delete
# day40_msy_scan.csv before re-running from scratch.
################################################################################

promising_msy_candidates <- fine_sweep_df %>%
  filter(fish_level == 100, fraction_of_unfished > 0.03, fraction_of_unfished < 0.6) %>%
  select(theta, interaction_resource, knife_edge_size)

msy_scan_effort_seq <- c(1, 3, 5, 9, 15, 20, 25, 30, 50, 100)
msy_scan_path        <- file.path(plot_dir, "day40_msy_scan.csv")

run_msy_scan_cell <- function(theta_val, ir_val, ke_val) {
  params   <- anchovy_params(theta_val, ir_val, knife_edge_size = ke_val)
  fork_sim <- make_anchovy_fork_sim(params, t_fork)
  grid_df  <- cannibalism_fishing_probe(params, fork_sim, msy_scan_effort_seq)
  grid_df$theta                <- theta_val
  grid_df$interaction_resource <- ir_val
  grid_df$knife_edge_size      <- ke_val
  grid_df
}

for (i in seq_len(nrow(promising_msy_candidates))) {
  row     <- promising_msy_candidates[i, ]
  cell_df <- run_msy_scan_cell(row$theta, row$interaction_resource, row$knife_edge_size)
  write.table(cell_df, msy_scan_path, sep = ",", row.names = FALSE,
             col.names = !file.exists(msy_scan_path), append = file.exists(msy_scan_path))
  peak_row <- cell_df[which.max(cell_df$mean_yield), ]
  cat(sprintf(
    "theta=%.2f, ir=%.2f, ke=%d done -- peak yield=%.4f at fish_level=%.2g (%s)\n",
    row$theta, row$interaction_resource, row$knife_edge_size,
    peak_row$mean_yield, peak_row$fish_level,
    if (peak_row$fish_level < max(msy_scan_effort_seq)) "interior peak" else "still rising at boundary"
  ))
}

msy_scan_df <- read.csv(msy_scan_path)
cat(sprintf(
  "Section 14: fine MSY scan complete -- %d rows across %d candidate combinations. See day40_msy_scan.csv.\n",
  nrow(msy_scan_df), nrow(promising_msy_candidates)
))

# Screening logic: a genuine MSY needs (a) an interior yield peak -- not still
# rising at fish_level=100 -- with (b) total biomass actually stabilising
# after the peak rather than continuing to crash (Section 13's own "late
# uptick" artefact), AND (c) rel_amplitude staying well clear of the ~2.0
# collapse-flicker ceiling Section 13 found for the flagship extinction
# regime -- a stabilising MEAN can still hide a population flickering to
# near-zero at every trough, which rel_amplitude alone catches and
# frac_drop_last3 alone would miss.
msy_screen <- msy_scan_df %>%
  group_by(theta, interaction_resource, knife_edge_size) %>%
  arrange(fish_level, .by_group = TRUE) %>%
  summarise(
    peak_fish_level = fish_level[which.max(mean_yield)],
    peak_yield      = max(mean_yield),
    is_interior     = peak_fish_level < max(fish_level),
    declines_after  = tail(mean_yield, 1) < peak_yield * 0.95,
    frac_drop_last3 = (nth(mean_total, -3) - dplyr::last(mean_total)) / nth(mean_total, -3),
    max_amplitude   = max(rel_amplitude),
    .groups = "drop"
  ) %>%
  filter(is_interior, declines_after)

msy_clean_candidates <- msy_screen %>%
  filter(frac_drop_last3 < 0.2, max_amplitude < 1.0) %>%
  arrange(max_amplitude)
write.csv(msy_screen, file.path(plot_dir, "day40_msy_screen_summary.csv"), row.names = FALSE)
cat(sprintf(
  "Section 14 screen: %d of %d candidates have a genuine interior peak; %d pass the full screen (biomass stabilising AND amplitude < 1.0, clear of the collapse-flicker ceiling). See day40_msy_screen_summary.csv.\n",
  nrow(msy_screen), nrow(promising_msy_candidates), nrow(msy_clean_candidates)
))
print(msy_clean_candidates)

cat(paste(
  "Section 14 verdict (confirmed live, 2026-08-18): FOUND IT -- theta=0.3, interaction_resource=3",
  "at knife_edge=3 or knife_edge=5 is a genuine sustainable-yield regime, the first one this project",
  "has found. 17 of the 56 screened combinations show a numerical interior yield peak, but 15 of",
  "those are the same late-uptick-into-flickering-collapse artefact Section 13 found for the",
  "flagship extinction regime -- rel_amplitude climbs to 1.68-2.00 (the same near-2.0 ceiling Day 39",
  "flagged as a near-extinction signature) even where the MEAN biomass looks like it has stabilised,",
  "which frac_drop_last3 alone would have missed. Only theta=0.3/ir=3/knife_edge=3 (peak yield=0.0820",
  "at fish_level=9, max rel_amplitude=0.529) and theta=0.3/ir=3/knife_edge=5 (peak yield=0.0804 at",
  "fish_level=15, max rel_amplitude=0.461) pass both tests: a real interior peak, mean_total settling",
  "into a reduced-but-stable range afterward (0.786->0.410 and 0.792->0.435 respectively, both",
  "essentially flat by fish_level=50-100), and amplitude staying well clear of the collapse-flicker",
  "ceiling across the entire tested range. interaction_resource=3 was in the ORIGINAL Overnight grid",
  "(theta_grid_seq x resource_grid_seq) from the very start of this file but was never itself pulled",
  "out for a full effort/knife_edge sweep -- every other section in this project focused on ir=1,",
  "1.3, 2, or 5 instead. This is a coarse 10-point effort grid, not a fine one -- worth a proper",
  "21-point pass (Section 13b's own convention) plus a genuine oscillation check (Section 13a's own",
  "convention: full time series across several effort levels, not just summary rel_amplitude) before",
  "treating this as fully confirmed, but it is the first candidate in this whole project that looks",
  "right on both counts at once.\n"
))

################################################################################
# Section 15: size spectrum and biomass-flux plots, knife_edge=10 (this
# project's own default gear) throughout, for four (theta, interaction_resource)
# combinations -- the default, each single-parameter change on its own, and
# both together (Section 14's own newly-found MSY regime):
#   - default:        theta=1,   ir=1
#   - reduced theta:   theta=0.3, ir=1
#   - increased ir:    theta=1,   ir=3
#   - both:            theta=0.3, ir=3
#
# Each is snapshotted at the end of the standard unfished fork (t_fork=20) --
# the same state every other section in this file treats as its own starting
# point -- rather than at an arbitrary or fished time. Since this model
# oscillates rather than sitting at a true fixed point, this snapshot is a
# point on the cycle, not an equilibrium; it is the consistent reference point
# used throughout this project, not a claim that the spectrum/flux shown here
# is unchanging.
#
# plotSpectra() and getFlux() are both built-in, exported mizer functions
# (checked against the currently installed mizer, not recalled from memory --
# see MIZER-AGENTS.md's own warning about stale API recollection). Preferred
# over any hand-rolled ggplot per this project's own convention, and over the
# older mizerExperimental::getFlux()+plotHover() pattern used in this
# project's early finding_jams files, which predates the version of mizer
# installed here and produces an interactive plotly widget rather than a
# static plot -- not suitable for a batch Rscript run producing PNG files.
# getFlux()'s own `power` argument is confirmed verbatim from the installed
# mizer's own help page (not recalled from memory): "The default power = 0
# gives the flux of individuals (numbers/year), whereas power = 1 gives the
# flux of biomass (grams/year)." power=1 is therefore what this project cares
# about -- matching its own "flow of biomass" framing -- and is NOT the same
# as the power=2 used for a display-only weighting in this project's early,
# now-superseded finding_jams files (those called mizerExperimental's own
# plotHover(getFlux(sim, power=2)), a different function on a different
# argument convention, not a biomass-flux precedent to follow here). The
# y-axis is relabelled explicitly below rather than trusting mizer's own
# generic default label to say so.
#
# Its return value is an ArraySpeciesBySize object, the same wrapper class
# getTrophicLevel() returns; plot() on it gives a curve-per-species plot
# directly, with no custom plotting code needed.
#
# Preamble below redefines every prerequisite this section needs -- library
# calls, p2, setAnchovyMort(), the resource stepper, anchovy_params(),
# set_state()/seed_from(), make_anchovy_fork_sim(), t_fork -- verbatim from
# earlier in this file, so Section 15 can be run standalone in a fresh R
# session (e.g. after restarting R) without sourcing everything above it
# first. This matches this file's own stated convention ("Self-contained
# convention since Day 20: helpers redefined here") rather than introducing
# a new one. Safe to run even after the full file has already been sourced --
# these are pure redefinitions, not appends.
################################################################################

library(mizer)
library(dplyr)
library(ggplot2)

plot_dir <- "interesting_plots"
dir.create(plot_dir, showWarnings = FALSE)

save_plot <- function(plot, filename, width = 9, height = 6, dpi = 150) {
  max_name <- 40
  if (nchar(filename) > max_name) {
    ext      <- tools::file_ext(filename)
    base     <- tools::file_path_sans_ext(filename)
    filename <- paste0(substr(base, 1, max_name - nchar(ext) - 1), ".", ext)
    warning(sprintf("save_plot(): filename too long, truncated to '%s'", filename))
  }
  print(plot)
  ggplot2::ggsave(file.path(plot_dir, filename), plot = plot, width = width, height = height, dpi = dpi)
}

p2 <- list(
  dt = 0.001, dx = 0.1, w_min = 0.0003, w_inf = 66.5,
  ppmr_min = 100, ppmr_max = 30000, gamma = 750, alpha = 0.85, K = 0.1,
  mu_l = 0, w_l = 0.03, rho_l = 5,
  mu_0 = 1, rho_b = -0.25,
  w_s = 0.5, rho_s = 1,
  w_mat = 10, rho_m = 15, rho_inf = 0.2, epsilon_R = 0.1,
  w_pp_cutoff = 0.1, r0 = 10, a0 = 100, i0 = 100, rho = 0.85, lambda = 2
)

setAnchovyMort <- function(params, p) {
  w <- w(params)
  mu_b <- rep(0, length(w))
  mu_b[w <= p$w_s] <- (p$mu_0 * (w / p$w_min)^p$rho_b)[w < p$w_s]
  mu_s <- if (p$mu_0 > 0) min(mu_b[w <= p$w_s]) else p$mu_s
  mu_b[w >= p$w_s] <- (mu_s * (w / p$w_s)^p$rho_s)[w >= p$w_s]
  mu_b <- mu_b + p$mu_l / (1 + (w / p$w_l)^p$rho_l)

  mort <- ext_mort(params)
  mort[] <- mu_b
  ext_mort(params) <- mort
  params
}

plankton_state <- new.env(parent = emptyenv())
plankton_state$time   <- 0
plankton_state$factor <- 1

exact_logistic_immigration_step <- function(n, rate, capacity, immigration,
                                            mortality, dt) {
  result <- n
  active <- is.finite(n) & is.finite(rate) & is.finite(capacity) &
    is.finite(immigration) & is.finite(mortality) &
    rate > 0 & capacity > 0 & immigration >= 0
  if (dt == 0 || !any(active)) return(result)

  n0 <- n[active]
  r  <- rate[active]
  k  <- capacity[active]
  i  <- immigration[active]
  mu <- mortality[active]
  a  <- r - mu
  b  <- r / k
  next_n <- numeric(length(n0))

  has_immigration <- i > 0
  if (any(has_immigration)) {
    idx <- which(has_immigration)
    ai  <- a[idx]
    bi  <- b[idx]
    ii  <- i[idx]
    d   <- sqrt(ai^2 + 4 * bi * ii)
    n_plus <- ifelse(ai >= 0, (ai + d) / (2 * bi), 2 * ii / (d - ai))
    n_minus <- ifelse(ai <= 0, (ai - d) / (2 * bi), -2 * ii / (ai + d))
    ratio <- ((n0[idx] - n_plus) / (n0[idx] - n_minus)) * exp(-d * dt)
    next_n[idx] <- (n_plus - ratio * n_minus) / (1 - ratio)
  }

  no_immigration <- !has_immigration
  if (any(no_immigration)) {
    idx <- which(no_immigration)
    az  <- a[idx]
    bz  <- b[idx]
    nz  <- n0[idx]
    value <- numeric(length(idx))
    zero_rate <- az == 0
    value[zero_rate] <- nz[zero_rate] /
      (1 + bz[zero_rate] * nz[zero_rate] * dt)

    positive <- az > 0 & nz > 0
    phi <- -expm1(-az[positive] * dt) / az[positive]
    value[positive] <- nz[positive] /
      (exp(-az[positive] * dt) +
         bz[positive] * nz[positive] * phi)

    negative <- az < 0
    exp_adt <- exp(az[negative] * dt)
    phi <- expm1(az[negative] * dt) / az[negative]
    value[negative] <- nz[negative] * exp_adt /
      (1 + bz[negative] * nz[negative] * phi)
    next_n[idx] <- value
  }

  result[active] <- pmax(next_n, 0)
  result
}

plankton_logistic <- function(params, n, n_pp, n_other, rates, dt = 0.1, ...) {
  plankton_state$time <- plankton_state$time + dt
  exact_logistic_immigration_step(
    n = n_pp,
    rate = params@rr_pp,
    capacity = params@cc_pp * plankton_state$factor,
    immigration = anchovy_immigration,
    mortality = rates$resource_mort,
    dt = dt
  )
}

norm_box_pred_kernel <- function(ppmr, ppmr_min, ppmr_max) {
  phi <- rep(1, length(ppmr))
  phi[ppmr > ppmr_max] <- 0
  phi[ppmr < ppmr_min] <- 0
  phi[1] <- 0
  logppmr <- log(ppmr)
  dl <- logppmr[2] - logppmr[1]
  N <- sum(phi) * dl
  phi / N
}

anchovy_params <- function(interaction_val = 1, interaction_resource_val = 1,
                           knife_edge_size = p2$w_mat, p = p2) {
  kappa <- p$a0 * exp(-6.9 * (p$lambda - 1))

  species_params_df <- data.frame(
    species = "Anchovy", w_min = p$w_min, w_mat = p$w_mat, m = p$rho_inf + 2/3,
    w_inf = p$w_inf, erepro = p$epsilon_R, alpha = p$K, ks = 0, gamma = p$gamma,
    q = p$alpha, ppmr_min = p$ppmr_min, ppmr_max = p$ppmr_max,
    pred_kernel_type = "norm_box", h = Inf, R_max = Inf, linecolour = "brown",
    stringsAsFactors = FALSE
  )

  params <- newMultispeciesParams(
    species_params_df, no_w = round(log(p$w_inf / p$w_min) / p$dx),
    lambda = p$lambda, kappa = kappa, w_pp_cutoff = p$w_pp_cutoff,
    resource_dynamics = "plankton_logistic"
  )
  resource_rate(params) <- p$r0 * w_full(params)^(p$rho - 1)

  interaction_matrix(params) <- interaction_val
  species_params(params)$interaction_resource <- interaction_resource_val

  gp                 <- gear_params(params)
  gp$sel_func        <- "knife_edge"
  gp$knife_edge_size <- knife_edge_size
  gp$catchability    <- 1
  gear_params(params) <- gp

  setAnchovyMort(params, p)
}

p_scan <- anchovy_params()
anchovy_immigration <- p2$i0 * w_full(p_scan)^(-p2$lambda) * exp(-6.9 * (p2$lambda - 1))

set_state <- function(params, n, n_pp) {
  n0 <- initialN(params); n0[] <- n; initialN(params) <- n0
  npp0 <- initialNResource(params); npp0[] <- n_pp; initialNResource(params) <- npp0
  params
}
seed_from <- function(params, sim) set_state(params, finalN(sim), finalNResource(sim))

make_anchovy_fork_sim <- function(params, t_fork) {
  params <- set_state(params, 0.001 * w(params)^(-1.8), resource_capacity(params))
  settled <- project(params, t_max = 10, dt = p2$dt, progress_bar = FALSE)
  params <- set_state(params, finalN(settled) / 1e7, finalNResource(settled))
  project(params, t_max = t_fork - 10, t_start = 10, dt = p2$dt, t_save = 0.2,
         progress_bar = FALSE, effort = 0)
}

t_fork <- 20

spectrum_flux_scenarios <- list(
  list(label = "default (theta=1, interaction_resource=1)",          slug = "default",           theta = 1,   ir = 1),
  list(label = "reduced theta (theta=0.3, interaction_resource=1)",  slug = "theta_low",         theta = 0.3, ir = 1),
  list(label = "increased ir (theta=1, interaction_resource=3)",     slug = "ir_high",           theta = 1,   ir = 3),
  list(label = "both (theta=0.3, interaction_resource=3)",           slug = "theta_low_ir_high", theta = 0.3, ir = 3)
)

for (sc in spectrum_flux_scenarios) {
  params_sc <- anchovy_params(sc$theta, sc$ir, knife_edge_size = 10)
  fork_sc   <- make_anchovy_fork_sim(params_sc, t_fork)
  snapshot  <- seed_from(params_sc, fork_sc)

  spectrum_plot <- plotSpectra(snapshot) +
    ggplot2::labs(title = sprintf("Size spectrum: %s", sc$label),
                 subtitle = "knife_edge=10, FIXED mortality, unfished fork state (t_fork=20)")
  save_plot(spectrum_plot, sprintf("day41_spectrum_%s.png", sc$slug), width = 8, height = 6)

  # power=1: biomass flux (g/year), confirmed against getFlux()'s own help
  # page above -- power=0 (the default) would be the numbers flux instead.
  # ggplot2:: qualified throughout this section since it's sometimes run on
  # its own without the library(ggplot2) call at the top of this file.
  flux_plot <- plot(getFlux(snapshot, power = 1)) +
    ggplot2::labs(title = sprintf("Biomass flux: %s", sc$label),
                 subtitle = "knife_edge=10, FIXED mortality, unfished fork state (t_fork=20)",
                 y = "Biomass flux (g/year)")
  save_plot(flux_plot, sprintf("day41_flux_%s.png", sc$slug), width = 8, height = 6)

  cat(sprintf(
    "Section 15: %s -- spectrum saved to day41_spectrum_%s.png, biomass flux saved to day41_flux_%s.png.\n",
    sc$label, sc$slug, sc$slug
  ))
}

################################################################################
# Section 16: does the second-order scheme change Section 15's own finding?
# Quick check at theta=0.3, interaction_resource=3, knife_edge=10 (Section
# 14's own newly-found MSY regime, and Section 15's own headline "jam
# resolved" case) -- MIZER-AGENTS.md's documented fix for the default
# scheme's numerical diffusion is `second_order_w(params) <- TRUE` paired
# with `method="tr_bdf2"` in project(); this section checks whether switching
# to it changes the size spectrum / biomass flux shape Section 15 found.
#
# steady()/steadyNewton() does NOT work for this model -- ruled out rather
# than attempted here. The analyse-stability skill's own scope note is exact:
# "Assumes the standard semichemostat resource dynamics." This file's own
# resource dynamics is the custom plankton_logistic()/exact_logistic_
# immigration_step() pair (Section 0 above, adopted Day 40), not mizer's own
# semichemostat -- steadyNewton()'s internal machinery does not know how to
# solve for this custom resource equation's own equilibrium, so it is not a
# usable reference point here regardless of numerical scheme.
#
# Also deliberately NOT using this file's own ad-hoc settle-and-rescale fork
# (make_anchovy_fork_sim(), Section 15's own convention) FROM SCRATCH for the
# second-order side: this file's own earlier dt-raising test (top of file)
# already found that exact fork procedure -- a 10yr settle from an arbitrary
# 0.001*w^-1.8 spectrum, then /1e7 rescale -- collapses to numerical
# extinction (~1e-33) under second_order_w+tr_bdf2, most likely because those
# two constants were empirically tuned for the default first-order scheme
# specifically and the arbitrary starting spectrum is a large, artificial
# perturbation the stiffer scheme handles badly.
#
# Instead: run the FIRST-ORDER fork as usual (known-good, Section 15's own
# convention) to reach a physically sensible point on the real cycle at
# t_fork=20, then seed a SECOND-ORDER copy of the same params from that same
# state and continue for a short additional projection under tr_bdf2 --
# not restarting from an arbitrary spectrum, just switching which scheme
# takes over from an already-sensible starting point. Far less likely to hit
# the same pathology, and quick: a few more years, not another 10yr settle.
#
# NOT run here, per this session's own instruction -- written for the user's
# own session. If this ALSO collapses or behaves degenerately, that is a
# real finding in its own right (the scheme itself may be incompatible with
# this custom resource dynamics, not just this file's own fork constants) --
# report it rather than continuing to patch the seeding procedure further.
################################################################################

theta_check <- 0.3
ir_check    <- 3
ke_check    <- 10

params_first_order <- anchovy_params(theta_check, ir_check, knife_edge_size = ke_check)
fork_check          <- make_anchovy_fork_sim(params_first_order, t_fork)
snapshot_first_order <- seed_from(params_first_order, fork_check)

params_second_order <- params_first_order
second_order_w(params_second_order) <- TRUE
params_second_order <- seed_from(params_second_order, fork_check)

spectrum_first_order <- plotSpectra(snapshot_first_order) +
  ggplot2::labs(title = "First-order upwind (default)",
               subtitle = "theta=0.3, interaction_resource=3, knife_edge=10 -- unfished fork state (t_fork=20)")
save_plot(spectrum_first_order, "day41_scheme_spectrum_1st.png", width = 8, height = 6)

# power=1: biomass flux (g/year), same convention as Section 15's own flux
# plots -- confirmed against getFlux()'s own help page there.
flux_first_order <- plot(getFlux(snapshot_first_order, power = 1)) +
  ggplot2::labs(title = "First-order upwind (default): biomass flux",
               subtitle = "theta=0.3, interaction_resource=3, knife_edge=10 -- unfished fork state (t_fork=20)",
               y = "Biomass flux (g/year)")
save_plot(flux_first_order, "day41_scheme_flux_1st.png", width = 8, height = 6)

################################################################################
# The first pass (+4yr under tr_bdf2) found the bimodal flux collapsing back
# into a single sharp peak, and the resource losing its grazed kink -- but
# 4yr is LESS than one full cycle (~5-6yr), so that could equally be a
# genuine scheme-driven difference or just an incomplete transient as the
# system readjusts to the new scheme's own rate calculations. Extending to
# ~3.6 cycles (checkpoints at +4, +12, +20yr, each CONTINUING the previous
# MizerSim rather than restarting -- project() on a MizerSim object inherits
# its own dt/method automatically) distinguishes the two: if the bimodal
# structure re-emerges once the transient has genuinely settled, that
# supports Section 6's own mechanism; if it stays single-peaked across
# multiple full cycles, Section 6's mechanism needs rethinking rather than
# defending.
################################################################################

checkpoint_years <- c(4, 12, 20)   # cumulative years past t_fork=20, under tr_bdf2
sim_checkpoint    <- NULL
years_so_far      <- 0

for (yr in checkpoint_years) {
  step_years <- yr - years_so_far
  if (is.null(sim_checkpoint)) {
    sim_checkpoint <- project(params_second_order, t_max = step_years, dt = p2$dt, t_save = 0.2,
                              progress_bar = FALSE, effort = 0, method = "tr_bdf2")
  } else {
    sim_checkpoint <- project(sim_checkpoint, t_max = step_years, progress_bar = FALSE)
  }
  years_so_far <- yr

  snapshot_checkpoint <- seed_from(params_second_order, sim_checkpoint)

  spectrum_checkpoint <- plotSpectra(snapshot_checkpoint) +
    ggplot2::labs(title = sprintf("Second-order (tr_bdf2): +%dyr past fork", yr),
                 subtitle = "theta=0.3, interaction_resource=3, knife_edge=10")
  save_plot(spectrum_checkpoint, sprintf("day41_scheme_spectrum_2nd_%dyr.png", yr), width = 8, height = 6)

  flux_checkpoint <- plot(getFlux(snapshot_checkpoint, power = 1)) +
    ggplot2::labs(title = sprintf("Second-order (tr_bdf2): biomass flux, +%dyr past fork", yr),
                 subtitle = "theta=0.3, interaction_resource=3, knife_edge=10",
                 y = "Biomass flux (g/year)")
  save_plot(flux_checkpoint, sprintf("day41_scheme_flux_2nd_%dyr.png", yr), width = 8, height = 6)

  cat(sprintf(
    "Section 16: second-order checkpoint +%dyr saved (day41_scheme_{spectrum,flux}_2nd_%dyr.png).\n",
    yr, yr
  ))
}

cat(
  "Section 16: first-order snapshot (t_fork=20) vs second-order checkpoints at +4/+12/+20yr, all seeded from the same first-order fork state -- see day41_scheme_{spectrum,flux}_1st.png and day41_scheme_{spectrum,flux}_2nd_{4,12,20}yr.png. If the bimodal flux shape re-emerges by +12 or +20yr, Section 6's own mechanism survives the scheme check; if it stays single-peaked throughout, that finding needs to be revisited.\n"
)

################################################################################
# Section 17: theta=0 -- no cannibalism at all, not just cut to 30% -- paired
# with interaction_resource=1, knife_edge=10 (this project's own original
# default ir, not the theta=0.3/ir=3 regime this whole file has otherwise
# been focused on since Section 14). Cannibalism (self-interaction, set via
# interaction_matrix()) is this project's own documented source of the
# destabilising feedback that produces the oscillation in the first place --
# report-background-mizer.qmd's own note, after Datta, Delius and Law (2011):
# narrow diet breadth/self-predation is destabilising for this class of
# equation. theta=0 removes that feedback outright rather than reducing it.
#
# Two questions: (17a) does this actually stop the population from
# oscillating at all, and (17b) if so, does increasing Constant fishing
# effort still drive a now-non-oscillating population to extinction, or does
# the collapse behaviour found throughout Sections 3/5/12-14 specifically
# need the cycling dynamics in the mix?
################################################################################

theta_zero    <- 0
ir_zero_check <- 1
ke_zero_check <- 10

params_no_cannibalism <- anchovy_params(theta_zero, ir_zero_check, knife_edge_size = ke_zero_check)
fork_no_cannibalism   <- make_anchovy_fork_sim(params_no_cannibalism, t_fork)

## -- 17a: does it actually stop oscillating? Same peak-detection convention
## as Section 0c's own cycle-period check, extended well past t_fork to catch
## any residual cycling rather than trusting a short window.
sim_long_no_cannibalism <- project(fork_no_cannibalism, t_max = 60, t_start = t_fork, dt = p2$dt,
                                   t_save = 0.5, progress_bar = FALSE, effort = 0)
bp_no_cannibalism <- selected_biomass(sim_long_no_cannibalism, t_cut = -Inf)
tv_no_cannibalism <- getTimes(sim_long_no_cannibalism)
n_nc       <- length(bp_no_cannibalism)
is_peak_nc <- c(FALSE, bp_no_cannibalism[2:(n_nc - 1)] > bp_no_cannibalism[1:(n_nc - 2)] &
                       bp_no_cannibalism[2:(n_nc - 1)] > bp_no_cannibalism[3:n_nc], FALSE)
peak_times_nc <- tv_no_cannibalism[is_peak_nc & tv_no_cannibalism > t_fork]

cat(sprintf(
  "Section 17a: theta=0, interaction_resource=1, knife_edge=10, unfished, t=[%.0f,%.0f]: %d local peaks detected (%s). %s\n",
  t_fork, max(tv_no_cannibalism), length(peak_times_nc),
  if (length(peak_times_nc) > 1) sprintf("mean spacing=%.2fyr", mean(diff(peak_times_nc))) else "too few to call a cycle",
  if (length(peak_times_nc) <= 1) "Consistent with theta=0 removing the oscillation entirely."
  else "Still oscillating even with theta=0 -- worth checking why before trusting 17b as a clean no-oscillation test."
))

cat(paste(
  "Section 17a verdict (confirmed live, 2026-08-18): ZERO peaks detected across the full",
  "t=[20,80] window -- not just small-amplitude cycling, genuinely none. The trajectory is",
  "monotonically increasing the whole way (selected biomass 0.0144 at t=20.5 -> 0.0185 at t=80,",
  "+28%, minimum at the start and maximum at the end), which is exactly why no local peak exists",
  "to detect: the population never turns over even once. This means it had not actually finished",
  "settling within 80 years total -- it is on a slow, smooth climb toward wherever its true",
  "equilibrium sits, just with no cyclic component at all, rather than having already reached a",
  "flat steady state within the same t_fork=20 window every theta=0.3 variant in this project",
  "settles inside. Removing cannibalism does not just remove the oscillation, it changes the",
  "relaxation timescale itself, and this needs a longer fork (or steady()/projectToSteady(), which",
  "does apply here since a genuine fixed point -- not a limit cycle -- is plausible for theta=0)",
  "before 17b's own Constant-effort sweep is seeded from a truly converged state rather than a",
  "still-drifting one. The qualitative finding stands regardless: 17b's own rel_amplitude stays at",
  "0.005-0.05 across every fishing effort tested, two orders of magnitude below the 0.6-2.0 typical",
  "of every theta=0.3 variant elsewhere in this file, and fraction_of_unfished never drops below",
  "~0.73 even at fish_level=100 -- dramatically more fishing-resistant than any oscillating variant",
  "tested, consistent with the cycling dynamics themselves being what the compositional-shift",
  "collapse-and-boom mechanism (Sections 3/5/12-14) actually depends on.\n"
))

## -- 17b: Constant-effort sweep -- does increasing fishing effort drive this
## (now non-oscillating, if 17a confirms it) population to extinction?
fish_level_seq_no_cannibalism <- c(1, 2, 3, 5, 9, 15, 20, 30, 50, 70, 100)
no_cannibalism_grid_df <- cannibalism_fishing_probe(params_no_cannibalism, fork_no_cannibalism,
                                                    fish_level_seq_no_cannibalism)

total_unfished_ref_nc <- {
  sim_uf <- project(seed_from(params_no_cannibalism, fork_no_cannibalism), t_max = scan_summary_window,
                    dt = p2$dt, t_save = 0.2, t_start = t_fork, progress_bar = FALSE, effort = 0)
  mean(after_cut(getBiomass(sim_uf), sim_uf, t_fork + scan_summary_window / 2))
}
no_cannibalism_grid_df$fraction_of_unfished <- no_cannibalism_grid_df$mean_total / total_unfished_ref_nc

write.csv(no_cannibalism_grid_df, file.path(plot_dir, "day41_no_cannibalism_effort_grid.csv"), row.names = FALSE)
cat(sprintf(
  "Section 17b: theta=0, interaction_resource=1, knife_edge=10, unfished total biomass reference=%.4f. See day41_no_cannibalism_effort_grid.csv.\n",
  total_unfished_ref_nc
))
print(no_cannibalism_grid_df %>% select(fish_level, mean_total, mean_yield, rel_amplitude, fraction_of_unfished))

# ggplot2:: qualified in case this section is run on its own after an R
# restart, without library(ggplot2) having been (re-)run first -- same
# defensive convention Section 15 adopted.
no_cannibalism_yield_plot <- ggplot2::ggplot(no_cannibalism_grid_df, ggplot2::aes(x = fish_level, y = mean_yield)) +
  ggplot2::geom_line(color = "#c0392b") +
  ggplot2::geom_point(size = 2, color = "#c0392b") +
  ggplot2::scale_x_log10() +
  ggplot2::labs(x = "Fishing effort (Constant, log scale)", y = "Mean yield",
               title = "theta=0 (no cannibalism), interaction_resource=1, knife_edge=10",
               subtitle = "Does removing cannibalism -- and any oscillation with it -- change whether fishing drives this population toward extinction?") +
  ggplot2::theme_minimal()
save_plot(no_cannibalism_yield_plot, "day41_no_cannibalism_yield.png", width = 9, height = 6)

no_cannibalism_biomass_plot <- ggplot2::ggplot(no_cannibalism_grid_df,
                                               ggplot2::aes(x = fish_level, y = pmax(fraction_of_unfished, 1e-20))) +
  ggplot2::geom_line(color = "#16a085") +
  ggplot2::geom_point(size = 2, color = "#16a085") +
  ggplot2::scale_x_log10() +
  ggplot2::scale_y_log10() +
  ggplot2::geom_hline(yintercept = 0.01, linetype = "dotted") +
  ggplot2::labs(x = "Fishing effort (Constant, log scale)", y = "Fraction of unfished biomass (log scale)",
               title = "theta=0 (no cannibalism): does fishing drive this population extinct?",
               subtitle = "Dotted line = 1% of unfished, this project's own collapse threshold (Section 12)") +
  ggplot2::theme_minimal()
save_plot(no_cannibalism_biomass_plot, "day41_no_cannibalism_biomass.png", width = 9, height = 6)

cat(sprintf(
  "Section 17b: fraction of unfished biomass remaining at fish_level=100: %.4g (%s this project's own <1%% collapse threshold).\n",
  no_cannibalism_grid_df$fraction_of_unfished[no_cannibalism_grid_df$fish_level == 100],
  if (no_cannibalism_grid_df$fraction_of_unfished[no_cannibalism_grid_df$fish_level == 100] < 0.01) "BELOW" else "above"
))

################################################################################
# Section 17c: 17a found the theta=0 unfished trajectory still slowly rising
# after 60yr past t_fork=20, not yet converged -- so 17b's own sweep was
# seeded from a still-drifting state, not a genuine equilibrium. This section
# redoes it properly: projectToSteady() (not steady(), which does not work
# here for the same reason it fails for the oscillating models -- it assumes
# standard semichemostat resource dynamics, and this project's own custom
# plankton_logistic() is not that) applied directly to a FRESH
# anchovy_params(0, 1, knife_edge_size=10) build, bypassing this project's
# own fork procedure entirely -- that procedure (10yr settle from an
# arbitrary tiny spectrum, /1e7 rescale) was tuned for the theta=0.3 models'
# own fast oscillatory attractor and turns out to be a genuinely bad starting
# point here: projectToSteady() from mizer's own default initial spectrum
# converges to a real fixed point (type="steady", not "cycle") in just 28.8
# years, far faster than the fork-seeded run had managed in 80.
#
# Each fishing effort gets its own projectToSteady() call, chained from the
# same converged unfished params (not from each other) -- getBiomass()/
# getYield() then read the exact steady-state values directly off the
# returned MizerParams, no time-window averaging needed at all.
################################################################################

params_nc_converged <- projectToSteady(params_no_cannibalism, t_per = 0.2, t_max = 150,
                                       dt = p2$dt, progress_bar = FALSE)
cat("Section 17c: theta=0 unfished convergence via projectToSteady() (bypassing this file's own fork procedure):\n")
print(attr(params_nc_converged, "convergence"))

fish_level_seq_nc <- c(1, 2, 3, 5, 9, 15, 20, 30, 50, 70, 100)
total_unfished_nc_converged <- unname(getBiomass(params_nc_converged))

nc_converged_results <- lapply(fish_level_seq_nc, function(fl) {
  p_run <- projectToSteady(params_nc_converged, t_per = 0.2, t_max = 150, dt = p2$dt,
                           effort = fl, progress_bar = FALSE)
  conv <- attr(p_run, "convergence")
  data.frame(fish_level = fl, mean_total = unname(getBiomass(p_run)),
            mean_yield = unname(getYield(p_run)), conv_type = conv$type,
            conv_years = conv$years)
})
nc_converged_df <- dplyr::bind_rows(nc_converged_results)
nc_converged_df$fraction_of_unfished <- nc_converged_df$mean_total / total_unfished_nc_converged
write.csv(nc_converged_df, file.path(plot_dir, "day41_no_cannibalism_converged_grid.csv"), row.names = FALSE)
cat("Section 17c: properly-converged theta=0 effort sweep -- see day41_no_cannibalism_converged_grid.csv.\n")
print(nc_converged_df)

cat(paste(
  "Section 17c verdict (confirmed live, 2026-08-18): every one of the 11 effort levels tested",
  "converges cleanly to type='steady' (a genuine fixed point) -- fishing does not induce any",
  "oscillation in this theta=0 regime at any effort tested, confirming 17a/17b's own qualitative",
  "finding under the corrected, fully-converged procedure. The QUANTITATIVE picture changes a",
  "great deal, though: fraction_of_unfished at fish_level=100 is 0.368, not 17b's own uncorrected",
  "0.730 -- roughly half. The curve is also NOT monotonic: it declines from 0.986 (fish_level=1)",
  "to a local minimum of 0.866 (fish_level=9), genuinely RISES back to 0.898-0.905 (fish_level=",
  "15-20), then crashes sharply to 0.515 between fish_level=20 and 30, continuing down to 0.368 by",
  "100. conv_years spikes exactly at that crash (22.2yr at fish_level=20 -> 47.8yr at 30) -- the",
  "textbook critical-slowing-down signature of approaching a genuine bifurcation in the underlying",
  "equilibrium, not a numerical artefact. mean_yield tells the same story: a real interior peak of",
  "0.0514 at fish_level=9, a dip to a minimum of 0.0223 at fish_level=30 (exactly the crash point),",
  "then a slight rise back to 0.0272 by fish_level=100 -- a genuine peak-dip-rise yield curve, the",
  "same qualitative shape this project has treated throughout as a signature of the oscillating,",
  "compositional-shift dynamics (Sections 1/3 of this file, Day 40's own headline finding) --",
  "except here with ZERO oscillation anywhere in the range. That shape is not unique to the",
  "cycling regime; it can also come from a pure equilibrium fold/bifurcation between two stable",
  "branches. The qualitative extinction-resistance finding still holds even after correction --",
  "0.368 remains far short of this project's own 1% collapse threshold -- but the specific numbers",
  "in 17b above should be read as illustrative rather than precise, and the bifurcation itself is a",
  "new, previously undocumented finding worth its own follow-up (bracketing fish_level=20-30 more",
  "finely to locate it precisely, and checking whether it is a genuine fold or something else via",
  "getStability()/steadyNewton() on either side of it).\n"
))

################################################################################
# Section 17d: is the fish_level=27->28 jump actually a bifurcation, or just a
# steep-but-continuous decline? "Convergence took longer nearby" (17c) is
# suggestive but not proof by itself -- a genuine fold requires showing that
# the SAME effort value has two different stable states depending on which
# direction it is approached from (hysteresis), not just that one path
# happens to be steep. Two tests: (a) a fine bracket of the transition zone
# from the SAME (unfished) branch 17c already used, to see whether the jump
# is a real discontinuity or the fine grid just smooths it out; (b) starting
# from the OTHER side (converged at effort=30, past the jump) and stepping
# DOWN through the same effort values, to check whether that path lands on a
# different branch than the upward path did at the same effort.
################################################################################

## -- 17d(a): fine bracket, same (unfished) branch as 17c --
fish_level_fine <- c(21, 22, 23, 24, 25, 26, 27, 28, 29)

fine_up_results <- lapply(fish_level_fine, function(fl) {
  p_run <- projectToSteady(params_nc_converged, t_per = 0.2, t_max = 150, dt = p2$dt,
                           effort = fl, progress_bar = FALSE)
  conv <- attr(p_run, "convergence")
  data.frame(fish_level = fl, mean_total = unname(getBiomass(p_run)),
            mean_yield = unname(getYield(p_run)), conv_type = conv$type,
            conv_years = conv$years)
})
fine_up_df <- dplyr::bind_rows(fine_up_results)
fine_up_df$fraction_of_unfished <- fine_up_df$mean_total / total_unfished_nc_converged
write.csv(fine_up_df, file.path(plot_dir, "day41_no_cannibalism_fine_bracket.csv"), row.names = FALSE)
cat("Section 17d(a): fine bracket of the fish_level=20-30 transition (same unfished branch as 17c) -- see day41_no_cannibalism_fine_bracket.csv.\n")
print(fine_up_df)

## -- 17d(b): hysteresis check -- converge at effort=30 (past the jump),
## then step DOWN through the same effort values the upward path already
## covered, to see whether the SAME effort lands on a different branch.
p_high         <- projectToSteady(params_nc_converged, t_per = 0.2, t_max = 150, dt = p2$dt,
                                  effort = 30, progress_bar = FALSE)
p_down_to_25   <- projectToSteady(p_high, t_per = 0.2, t_max = 150, dt = p2$dt,
                                  effort = 25, progress_bar = FALSE)
p_down_to_20   <- projectToSteady(p_down_to_25, t_per = 0.2, t_max = 150, dt = p2$dt,
                                  effort = 20, progress_bar = FALSE)

hysteresis_df <- data.frame(
  fish_level = c(30, 25, 20),
  fraction_from_above = c(
    unname(getBiomass(p_high))       / total_unfished_nc_converged,
    unname(getBiomass(p_down_to_25)) / total_unfished_nc_converged,
    unname(getBiomass(p_down_to_20)) / total_unfished_nc_converged
  ),
  years_from_above = c(attr(p_high, "convergence")$years,
                      attr(p_down_to_25, "convergence")$years,
                      attr(p_down_to_20, "convergence")$years),
  fraction_from_below = c(
    nc_converged_df$fraction_of_unfished[nc_converged_df$fish_level == 30],
    fine_up_df$fraction_of_unfished[fine_up_df$fish_level == 25],
    nc_converged_df$fraction_of_unfished[nc_converged_df$fish_level == 20]
  ),
  years_from_below = c(nc_converged_df$conv_years[nc_converged_df$fish_level == 30],
                      fine_up_df$conv_years[fine_up_df$fish_level == 25],
                      nc_converged_df$conv_years[nc_converged_df$fish_level == 20])
)
write.csv(hysteresis_df, file.path(plot_dir, "day41_no_cannibalism_hysteresis.csv"), row.names = FALSE)
cat("Section 17d(b): same effort, approached from above (past the jump) vs. from below (unfished branch) -- see day41_no_cannibalism_hysteresis.csv.\n")
print(hysteresis_df)

cat(paste(
  "Section 17d verdict (confirmed live, 2026-08-18): this IS a genuine bifurcation, not just a",
  "steep decline -- confirmed by hysteresis, the direct test, not inferred from convergence time",
  "alone. The fine bracket (17d(a)) shows a real discontinuity: fraction_of_unfished declines",
  "smoothly from 0.894 (fish_level=21) to 0.820 (fish_level=27), then jumps to 0.578 between",
  "fish_level=27 and 28 -- a 0.24 drop in one unit of effort, not a continuation of the preceding",
  "~0.012-per-unit trend. conv_years jumps at the identical point (29.6yr at 27 -> 45.4yr at 28).",
  "17d(b) then tested the decisive question directly: at fish_level=25, approaching from the",
  "unfished branch gives fraction=0.862 (converging in 26.6yr); approaching the SAME effort from",
  "above (converged at effort=30, stepped down) gives fraction=0.507, converging in just 0.8yr --",
  "two different stable equilibria coexisting at the identical effort value. The same holds at",
  "fish_level=20: 0.898 from below vs. 0.502 from above, the latter converging in 1yr. This is",
  "textbook bistability -- two coexisting stable branches with a fold between them, not a single",
  "steep-but-continuous curve -- and the fast convergence on whichever branch is NOT being crossed",
  "into (0.8-1yr) versus the slow convergence on the branch closer to its own fold (22-48yr) is the",
  "expected signature on both sides. The lower edge of the bistable region (how far below",
  "fish_level=20 the 'low' branch remains reachable from above) is not yet mapped -- confirmed",
  "bistable across [20,27] at least, not yet known outside that window.\n"
))

################################################################################
# Section 18: Overnight sweep -- is Section 17d's own bistability (theta=0,
# interaction_resource=1, knife_edge=10) a global feature of this model, or a
# theta=0 curiosity? Every collapse/MSY finding in this project so far
# (Sections 1-14) has only ever swept Constant effort in ONE direction
# (upward, from the unfished branch) -- this tests both directions across a
# grid of (theta, interaction_resource, knife_edge), flagging any point where
# they disagree as a candidate bistable point, generalising the exact test
# Section 17d applied once by hand to theta=0/ir=1/ke=10 alone.
#
# Grid (a screen, not an exhaustive characterisation): theta in
# {0, 0.3, 0.7, 1} (0 as the known reference, 0.3 as this project's own aim
# value, 0.7/1 bracketing); interaction_resource in {1, 2, 3, 5}; knife_edge
# in {5, 10, 15} (excluding 3, which this project's own earlier sweeps found
# collapses almost everywhere regardless of theta/ir -- a knife_edge that
# extinguishes the population outright is not informative for a BISTABILITY
# screen specifically, which needs two surviving branches to compare). 4 x 4
# x 3 = 48 combinations x 5 effort levels x 2 directions, plus 2 extra
# projectToSteady() calls per combination (the shared unfished reference and
# the downward chain's own high-effort starting point) = 480 projectToSteady()
# calls total.
#
# Each direction is a CHAINED sweep -- every effort seeded from the PREVIOUS
# one in the same direction, not re-seeded from a fixed base each time --
# exactly Section 17d's own convention (both cheaper, since each step is a
# smaller perturbation than jumping straight from unfished, and more
# physically realistic: a fishery ramping effort up or down gradually, not
# teleporting to each new effort from scratch).
#
# NOT run here -- written for the user's own session/Rscript batch run, the
# same convention as Section 12's own overnight grid. Individual points can
# take anywhere from under a year to projectToSteady()'s own t_max=150 cap to
# converge -- Section 17d found convergence times spiking from ~20yr to ~48yr
# right at its own fold -- so total runtime is genuinely unpredictable in
# advance. Results are appended to the CSV after every combination finishes
# (48 checkpoints), so a partial/interrupted run still leaves usable data;
# delete day41_bistability_sweep.csv before re-running from scratch. Thin the
# grid below and restart if this is still running after a full night.
################################################################################

theta_seq_bistab   <- c(0, 0.3, 0.7, 1)
ir_seq_bistab      <- c(1, 2, 3, 5)
ke_seq_bistab      <- c(5, 10, 15)
effort_seq_bistab  <- c(10, 20, 30, 50, 100)

bistab_path <- file.path(plot_dir, "day41_bistability_sweep.csv")

# Runs a CHAINED projectToSteady() sweep across effort_seq, in whatever order
# it is given -- each effort seeded from the PREVIOUS one's own converged
# state. `direction` is a label only ("up"/"down"), recorded in the output,
# not used to change any computation. If a species goes extinct partway
# through a chain, mean_total is recorded as NA for that and all subsequent
# points in the same chain rather than erroring -- once extinct in a chain,
# every higher (or, going down, lower) effort in the same direction stays
# extinct too, which is itself informative, not a failure to work around.
run_chained_sweep <- function(params, effort_seq, direction) {
  current <- params
  bind_rows(lapply(effort_seq, function(fl) {
    current <<- projectToSteady(current, t_per = 0.2, t_max = 150, dt = p2$dt,
                                effort = fl, progress_bar = FALSE)
    conv <- attr(current, "convergence")
    data.frame(fish_level = fl, direction = direction,
              mean_total = if (conv$type %in% c("steady", "cycle")) unname(getBiomass(current)) else NA_real_,
              conv_type = conv$type, conv_years = conv$years)
  }))
}

for (theta_val in theta_seq_bistab) {
  for (ir_val in ir_seq_bistab) {
    for (ke_val in ke_seq_bistab) {
      params_bistab <- anchovy_params(theta_val, ir_val, knife_edge_size = ke_val)

      # Unfished reference, converged once, shared by both directions.
      params_unfished_bistab <- projectToSteady(params_bistab, t_per = 0.2, t_max = 150,
                                                dt = p2$dt, effort = 0, progress_bar = FALSE)
      total_unfished_bistab <- unname(getBiomass(params_unfished_bistab))

      up_df <- run_chained_sweep(params_unfished_bistab, effort_seq_bistab, "up")

      # Downward chain starts fresh at the highest effort (a single large
      # jump directly from the unfished state, matching Section 17d's own
      # convention for p_high), then steps down through the rest of
      # effort_seq_bistab in reverse, each seeded from the previous.
      params_high_bistab <- projectToSteady(params_unfished_bistab, t_per = 0.2, t_max = 150,
                                            dt = p2$dt, effort = max(effort_seq_bistab),
                                            progress_bar = FALSE)
      down_df <- run_chained_sweep(params_high_bistab, rev(effort_seq_bistab), "down")

      cell_df <- bind_rows(up_df, down_df) %>%
        mutate(theta = theta_val, interaction_resource = ir_val, knife_edge_size = ke_val,
              fraction_of_unfished = mean_total / total_unfished_bistab)

      write.table(cell_df, bistab_path, sep = ",", row.names = FALSE,
                 col.names = !file.exists(bistab_path), append = file.exists(bistab_path))
      cat(sprintf("theta=%.2f, ir=%.2f, ke=%d done.\n", theta_val, ir_val, ke_val))
    }
  }
}

bistab_df <- read.csv(bistab_path)
cat(sprintf(
  "Section 18: bistability sweep complete -- %d rows across %d combinations. See day41_bistability_sweep.csv.\n",
  nrow(bistab_df), length(theta_seq_bistab) * length(ir_seq_bistab) * length(ke_seq_bistab)
))

# Flag candidate bistable points: same (theta, ir, ke, fish_level), up vs down
# fraction_of_unfished differing by more than 5% relative -- Section 17d's own
# gaps were far larger than this (0.862 vs 0.507, 0.898 vs 0.502), so this
# threshold is conservative rather than tuned to catch marginal cases.
bistab_wide <- bistab_df %>%
  select(theta, interaction_resource, knife_edge_size, fish_level, direction, fraction_of_unfished) %>%
  tidyr::pivot_wider(names_from = direction, values_from = fraction_of_unfished, names_prefix = "frac_")
bistab_wide$rel_diff <- abs(bistab_wide$frac_up - bistab_wide$frac_down) /
  pmax(bistab_wide$frac_up, bistab_wide$frac_down, 1e-12, na.rm = FALSE)

bistab_candidates <- bistab_wide %>% filter(!is.na(rel_diff), rel_diff > 0.05) %>% arrange(desc(rel_diff))
write.csv(bistab_candidates, file.path(plot_dir, "day41_bistability_candidates.csv"), row.names = FALSE)
cat(sprintf(
  "Section 18: %d candidate bistable (theta, interaction_resource, knife_edge, fish_level) points found (>5%% relative gap between up/down). See day41_bistability_candidates.csv.\n",
  nrow(bistab_candidates)
))
print(bistab_candidates)

################################################################################
# Section 19: bifurcation diagrams from the Section 18 sweep, knife_edge_size
# = 10 only. Sections 1/19's own knife_edge=5/15 rows already show both
# bistability and the fishing-induced cycle at every knife_edge tested (just
# at different rates -- more common at ke=5, rarer at ke=15) -- the phenomenon
# itself isn't a knife_edge=5 artefact, so one representative gear width
# (ke=10, this project's own default since Day 20) carries the story without
# three near-identical panels of gear-width columns competing for attention.
#
# fraction_of_unfished vs fish_level, up and down chains overlaid, one panel
# per interaction_resource, one plot per theta. Where the two coloured lines
# sit apart is exactly a candidate bistable point (Section 18's own
# rel_diff > 0.05 test, just made visible instead of only tabulated); where a
# line's own points switch from circle to triangle is the steady-to-cycle
# transition documented in the Day 42 post's own Section 1. Reads
# day41_bistability_sweep.csv fresh each call, so this is safe to rerun as-is
# on the partial sweep now and again once theta=1 finishes -- NOT run here,
# same convention as Section 18 itself.
#
# NA fraction_of_unfished (extinction rows, Section 18's own convention) drop
# out of the line/point geoms automatically -- an extinction shows up here as
# a broken line at the effort where it happens, which is itself the right
# picture, not a gap to fill in.
################################################################################

bistab_df <- read.csv(bistab_path)

plot_bifurcation_theta <- function(theta_val, ke_val = 10) {
  df <- bistab_df %>% filter(theta == theta_val, knife_edge_size == ke_val)
  if (nrow(df) == 0) return(NULL)

  ggplot(df, aes(x = fish_level, y = fraction_of_unfished, colour = direction,
                 group = direction)) +
    geom_line(linewidth = 0.6, na.rm = TRUE) +
    geom_point(aes(shape = conv_type), size = 2.2, na.rm = TRUE) +
    facet_wrap(~ interaction_resource, labeller = label_both, nrow = 1) +
    scale_colour_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_shape_manual(values = c(steady = 16, cycle = 17, extinction = 4),
                       drop = FALSE) +
    labs(title = sprintf("Bifurcation diagram, theta = %.2f, knife_edge = %d", theta_val, ke_val),
         subtitle = "Panels: interaction_resource. Triangle = limit cycle. Gap between lines = candidate bistable.",
         x = "fish_level (Constant effort)",
         y = "fraction of unfished total biomass",
         colour = "direction", shape = "conv_type") +
    theme_minimal()
}

for (theta_val in sort(unique(bistab_df$theta))) {
  p_bif <- plot_bifurcation_theta(theta_val, ke_val = 10)
  if (!is.null(p_bif)) {
    theta_tag <- gsub("\\.", "", sprintf("%.1f", theta_val))
    save_plot(p_bif, sprintf("day42_bifurc_ke10_th%s.png", theta_tag))
  }
}

################################################################################
# Section 20: yield envelope (min/max, not just a single-phase snapshot) over
# a FINE Constant-effort grid, 0 to 100, for one or two representative
# (theta, interaction_resource, knife_edge=10) cases. Sections 17c/17d/18 all
# read getYield() off a single projectToSteady() MizerParams result -- exact
# and correct for a genuine "steady" state, but for a "cycle" state that is
# only the yield at whatever ARBITRARY phase the run happened to stop on, not
# the cycle's own range. This section fixes that specifically: return_sim =
# TRUE keeps the whole trajectory, so the min and max yield over the settled
# window can be read off directly instead of guessed at from a single point.
#
# Two examples only (not the full Section 18 grid) -- ke=10 throughout, this
# project's own default gear width and this post's own focus:
#   1. theta=0.3, interaction_resource=1 -- Section 1's own "already-known"
#      cannibalism-driven cycling case, cycling at every effort level tested
#      in the coarse Section 18 grid. The fine grid here should show HOW the
#      yield envelope (amplitude) actually changes with effort, not just
#      that cycling happens.
#   2. theta=0, interaction_resource=1 -- Day 41 Section 8's own headline
#      bistable case (there, at a 5-point coarse grid). A fine grid here
#      should resolve the fold/jump far more precisely than Section 18's own
#      screen could, on the same up-only branch used by 17c/17d.
#
# NOT run here -- each point is a full projectToSteady() call with
# return_sim = TRUE (a saved trajectory, somewhat more expensive than the
# params-only return Section 18 uses), chained exactly as in Sections 17c/18
# (each effort seeded from the previous one's own converged state), stepping
# from the returned MizerSim back to a MizerParams via finalParams() --
# untested live this session (the console was occupied by Section 18's own
# sweep both times it was tried), so run the coarse effort_seq_test check
# below FIRST and confirm current stays a MizerParams (class(current)) and
# yield_min <= yield_mean <= yield_max everywhere before committing to the
# fine effort_seq_fine_env grid, which is ~4x the compute for ~4x the
# resolution.
################################################################################

run_yield_envelope_sweep <- function(theta_val, ir_val, ke_val = 10,
                                     effort_seq = seq(0, 100, by = 5),
                                     t_per = 0.2, t_max = 100) {
  current <- anchovy_params(theta_val, ir_val, knife_edge_size = ke_val)
  bind_rows(lapply(effort_seq, function(fl) {
    sim <- projectToSteady(current, t_per = t_per, t_max = t_max, dt = p2$dt,
                           effort = fl, return_sim = TRUE, progress_bar = FALSE)
    current <<- finalParams(sim)
    conv <- attr(sim, "convergence")

    yield_ts <- rowSums(getYield(sim))
    n <- length(yield_ts)
    # Settled window: last 3 cycle periods if a cycle was detected (matching
    # projectToSteady()'s own 3-window amplitude-stability check), otherwise
    # the back half of the saved trajectory. A genuinely steady point's
    # min/max/mean collapse to (near) the same value under either choice, so
    # this only changes anything for a real cycle.
    window_n <- if (identical(conv$type, "cycle") && !is.na(conv$period)) {
      min(n, max(2, round(3 * conv$period / t_per)))
    } else {
      max(2, n %/% 2)
    }
    tail_ts <- utils::tail(yield_ts, window_n)

    data.frame(fish_level = fl, conv_type = conv$type, conv_years = conv$years,
              conv_period = conv$period, yield_mean = mean(tail_ts),
              yield_min = min(tail_ts), yield_max = max(tail_ts))
  }))
}

plot_yield_envelope <- function(df, title_suffix) {
  ggplot(df, aes(x = fish_level)) +
    geom_ribbon(aes(ymin = yield_min, ymax = yield_max), alpha = 0.25, fill = "#1b9e77") +
    geom_line(aes(y = yield_mean), colour = "#1b9e77", linewidth = 0.7) +
    geom_point(aes(y = yield_mean, shape = conv_type), size = 2, colour = "#1b9e77") +
    scale_shape_manual(values = c(steady = 16, cycle = 17, extinction = 4), drop = FALSE) +
    labs(title = sprintf("Yield envelope, %s", title_suffix),
        subtitle = "Ribbon = min-to-max yield over the settled window (the cycle's own amplitude, where one exists).",
        x = "fish_level (Constant effort)", y = "yield (g/year)", shape = "conv_type") +
    theme_minimal()
}

## -- Quick coarse check first: confirms the chaining/window logic works
## before committing to the fine grid below. --
effort_seq_test <- c(0, 20, 40, 60, 80, 100)
env_test_th03 <- run_yield_envelope_sweep(0.3, 1, 10, effort_seq = effort_seq_test)
print(env_test_th03)

## -- Fine grid, 0 to 100, the two examples -- only run once the check above
## looks right (conv_type/conv_years sane, yield_min <= yield_mean <= yield_max
## everywhere, current stayed a MizerParams throughout). --
effort_seq_fine_env <- seq(0, 100, by = 5)

env_th03_ir1 <- run_yield_envelope_sweep(0.3, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th03_ir1, file.path(plot_dir, "day42_yield_env_th03_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th03_ir1, "theta=0.3, ir=1, ke=10"), "day42_yield_env_th03.png")

env_th0_ir1 <- run_yield_envelope_sweep(0, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th0_ir1, file.path(plot_dir, "day42_yield_env_th0_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th0_ir1, "theta=0, ir=1, ke=10"), "day42_yield_env_th0.png")

################################################################################
# Section 21: bifurcation diagrams with THETA as the swept parameter, not
# fish_level -- fixed knife_edge=10, fixed fish_level=10 (close to unfished,
# where Section 19's own ke=10 figures showed the widest up/down gaps), two
# examples only: interaction_resource=1 and =5.
#
# Motivation, read straight off Section 18's own already-completed rows at
# ke=10/fish_level=10 (the only ones examined here; that's 3 discrete theta
# points, not yet a real curve):
#   ir=1: theta=0 is a bistable STEADY fold (0.87 up vs 0.68 down, fraction
#     of unfished -- a 22% relative gap); theta=0.3 and 0.7 are CYCLES
#     instead, with the up/down gap shrunk to ~5%, right at this project's
#     own bistability threshold. The fold and the onset of cycling look like
#     they sit close together in theta -- a fine sweep between 0 and 0.3 is
#     the only way to see whether the fold turns directly into the cycle
#     boundary or whether there is a gap between them.
#   ir=5: bistability is strong at every theta tested so far, but NOT
#     monotonically -- a 42% relative gap at theta=0, a much larger 70% gap
#     at theta=0.3, back down to 16% at theta=0.7. Three points can't tell a
#     genuine local maximum in bistability strength around theta=0.3 apart
#     from three points that just happen to land that way -- this sweep is
#     the direct test.
#
# Mechanism: theta is baked into the MizerParams structure itself (the
# interaction/cannibalism matrix), so it can't be chained the way fish_level
# is in Section 18/19/20 (a plain argument to projectToSteady()). Each step
# rebuilds a fresh anchovy_params() at the new theta, then copies the
# PREVIOUS theta's converged abundance state into it via initialN()<-/
# initialNResource()<- before calling projectToSteady() -- carrying the
# state across a theta step the same way Section 18 carries it across an
# effort step, just via the explicit accessor setters instead of an
# argument, since there is no "theta=" argument to lean on here.
#
# NOT run here -- attempted live twice this session and both calls (one of
# them just Sys.time(), no model code at all) timed out after 120s with the
# console occupied elsewhere, so this is UNVERIFIED end-to-end. The
# individual pieces are each separately confirmed, though: initialN()<-/
# initialNResource()<- against the installed docs this session, and
# projectToSteady()/getBiomass()/getYield()/anchovy_params() already proven
# throughout the rest of this file. Sanity-check the small theta_seq_test
# grid first -- conv_type/conv_years should look sane and mean_total should
# stay positive throughout -- before committing to the fine grid below.
################################################################################

run_theta_chain <- function(ir_val, ke_val, fl, theta_seq, t_per = 0.2, t_max = 80) {
  current <- anchovy_params(theta_seq[1], ir_val, knife_edge_size = ke_val)
  bind_rows(lapply(theta_seq, function(th) {
    params_th <- anchovy_params(th, ir_val, knife_edge_size = ke_val)
    initialN(params_th) <- initialN(current)
    initialNResource(params_th) <- initialNResource(current)
    p_run <- projectToSteady(params_th, t_per = t_per, t_max = t_max, dt = p2$dt,
                             effort = fl, progress_bar = FALSE)
    current <<- p_run
    conv <- attr(p_run, "convergence")
    data.frame(theta = th, mean_total = unname(getBiomass(p_run)),
              mean_yield = unname(getYield(p_run)), conv_type = conv$type,
              conv_years = conv$years)
  }))
}

plot_theta_bifurcation <- function(up_df, down_df, title_suffix) {
  df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down"))
  ggplot(df, aes(x = theta, y = mean_total, colour = direction, group = direction)) +
    geom_line(linewidth = 0.6) +
    geom_point(aes(shape = conv_type), size = 2.2) +
    scale_colour_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_shape_manual(values = c(steady = 16, cycle = 17, extinction = 4), drop = FALSE) +
    labs(title = sprintf("Bifurcation diagram vs theta, %s", title_suffix),
        subtitle = "fish_level fixed at 10, knife_edge=10. Triangle = limit cycle. Gap between lines = candidate bistable.",
        x = "theta (cannibalism strength)", y = "total biomass (g)",
        colour = "direction", shape = "conv_type") +
    theme_minimal()
}

## -- Quick check first: 4-point grid, up direction only, ir=1. --
theta_seq_test <- c(0, 0.3, 0.7, 1)
theta_test_up <- run_theta_chain(ir_val = 1, ke_val = 10, fl = 10, theta_seq = theta_seq_test)
print(theta_test_up)

## -- Fine grid, both examples, up and down -- only once the check above
## looks right. --
theta_seq_fine <- seq(0, 1, by = 0.1)

for (ir_val in c(1, 5)) {
  up_df   <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 10, theta_seq = theta_seq_fine)
  down_df <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 10, theta_seq = rev(theta_seq_fine))

  out_df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down")) %>%
    mutate(interaction_resource = ir_val, knife_edge_size = 10, fish_level = 10)
  write.csv(out_df, file.path(plot_dir, sprintf("day42_theta_bifurc_ir%d.csv", ir_val)), row.names = FALSE)

  p_theta <- plot_theta_bifurcation(up_df, down_df,
                                    sprintf("interaction_resource=%d, ke=10, fish_level=10", ir_val))
  save_plot(p_theta, sprintf("day42_theta_bifurc_ir%d.png", ir_val))
}

################################################################################
# Section 22: Section 19's own fishing-effort bifurcation diagrams exist for
# theta=0/0.3/0.7 at knife_edge=10 (day42_bifurc_ke10_th00/03/07.png) but not
# theta=1 -- the overnight Section 18 sweep has only completed theta=1's own
# ir=1/knife_edge=5 combination so far, not knife_edge=10 at all. Rather than
# wait for the rest of Section 18's grid (which also covers knife_edge=5/15,
# not needed for this specific gap), this fills in just the 4 missing
# theta=1/knife_edge=10 combinations (interaction_resource = 1, 2, 3, 5),
# reusing Section 18's own run_chained_sweep()/ir_seq_bistab/
# effort_seq_bistab and appending to the SAME day41_bistability_sweep.csv
# Section 19 already reads -- rerunning Section 19 afterwards should produce
# day42_bifurc_ke10_th10.png with no other changes needed.
#
# NOT run here -- same reasons as everything else in this file today.
################################################################################

for (ir_val in ir_seq_bistab) {
  ke_val <- 10
  theta_val <- 1

  params_bistab <- anchovy_params(theta_val, ir_val, knife_edge_size = ke_val)

  params_unfished_bistab <- projectToSteady(params_bistab, t_per = 0.2, t_max = 150,
                                            dt = p2$dt, effort = 0, progress_bar = FALSE)
  total_unfished_bistab <- unname(getBiomass(params_unfished_bistab))

  up_df <- run_chained_sweep(params_unfished_bistab, effort_seq_bistab, "up")

  params_high_bistab <- projectToSteady(params_unfished_bistab, t_per = 0.2, t_max = 150,
                                        dt = p2$dt, effort = max(effort_seq_bistab),
                                        progress_bar = FALSE)
  down_df <- run_chained_sweep(params_high_bistab, rev(effort_seq_bistab), "down")

  cell_df <- bind_rows(up_df, down_df) %>%
    mutate(theta = theta_val, interaction_resource = ir_val, knife_edge_size = ke_val,
          fraction_of_unfished = mean_total / total_unfished_bistab)

  write.table(cell_df, bistab_path, sep = ",", row.names = FALSE,
             col.names = !file.exists(bistab_path), append = file.exists(bistab_path))
  cat(sprintf("Section 22: theta=1, ir=%.2f, ke=10 done.\n", ir_val))
}

cat("Section 22: theta=1/knife_edge=10 complete -- rerun Section 19 to get day42_bifurc_ke10_th10.png.\n")

################################################################################
# Section 23: does Section 20's own "mean hides a real interior peak in the
# max envelope" finding (theta=0.3, ir=1, ke=10) generalise across theta, or
# is it specific to that one point? ir=1/ke=10 cycles at every effort level
# tested for theta=0.3, 0.7 AND 1 (Section 18's own rows confirm this --
# theta=0 is the only one of the four that stays steady throughout, already
# covered by day42_yield_env_th0.png). This reruns Section 20's own
# run_yield_envelope_sweep()/plot_yield_envelope() unchanged, just at
# theta=0.7 and theta=1, same ir=1/ke=10/fine effort grid, so the three
# resulting figures are directly comparable to the existing theta=0.3 one.
#
# theta=0.7 was already dispatched once live this session and had not
# finished within this tool's own wait window when checked -- it may
# complete on its own regardless (R keeps running even after the calling
# tool gives up waiting), so check for day42_yield_env_th07.png/.csv before
# rerunning that half to avoid duplicating a still-in-flight run.
################################################################################

env_th07_ir1 <- run_yield_envelope_sweep(0.7, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th07_ir1, file.path(plot_dir, "day42_yield_env_th07_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th07_ir1, "theta=0.7, ir=1, ke=10"), "day42_yield_env_th07.png")

env_th10_ir1 <- run_yield_envelope_sweep(1, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th10_ir1, file.path(plot_dir, "day42_yield_env_th10_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th10_ir1, "theta=1, ir=1, ke=10"), "day42_yield_env_th10.png")

################################################################################
# What's Next
################################################################################
#
# 0. Sections 8-11 confirm a real pattern across the four (theta, ir) points
#    now tested: NONE of them gives a clean single-peaked sustainable-yield
#    curve in [1,100]. ir=1 (Sections 1/3) turns over and then RECOVERS
#    (peak-dip-rise, via the juvenile-boom compositional shift). ir=1.3
#    (Section 7), theta=0.5/ir=2 (Section 10), and theta=0.7/ir=5 (Section 11)
#    all climb monotonically instead, never turning over at all -- just at
#    very different RATES of decline, from theta=0.5/ir=2's genuine ~38% drop
#    down to theta=0.7/ir=5's population actually growing under fishing. The
#    peak-dip-rise shape looks specific to ir sitting near 1, not a general
#    property of theta=0.3 -- directly bears on Section 6's own open question
#    (was theta=0.3/interaction_resource=1 ever the right point to study?):
#    apparently not, if a clean sustainable-yield curve was the goal, since
#    none of the four points tested gives one within [1,100].
# 0b. Every point tested so far stops at fish_level=100. theta=0.5/ir=2's
#    yield was still rising (not plateauing) at 100, and ir=1.3/theta=0.7-ir=5
#    likewise show no sign of turning over -- worth extending the grid past
#    100 for at least the two most novel points (Sections 10-11) to check
#    whether any of them turns over at higher effort, or whether the absence
#    of a peak in [1,100] is a boundary artefact rather than the real shape.
# 1. The Overnight interaction grid above (theta x interaction_resource) still
#    needs its own follow-up now that it has actually finished: at FIXED
#    mortality, is theta=0.3/interaction_resource=1 still the right point to
#    study, or does a different cell serve the project's aim better? Section 0
#    at the top of this file only set up the comparison; nothing has read the
#    grid's own story yet.
# 2. Section 4's regime-shift finding (fish_level=100 is a faster, shallower-
#    harvestable-compartment cycle, not a noisier version of fish_level=9) was
#    read off 3 representative fish_level values. A sweep of the full
#    selected/total time series across every point in Section 3's fine grid
#    (the run_layered_ke_case_with_series() convention from the Day 40 blog
#    post's own Section 3) would show exactly where the transition happens,
#    not just that it happens somewhere between 20 and 100.
# 3. Section 2's tr_bdf2/second_order_w check found the documented fix for
#    large-dt numerical diffusion collapses this model under this file's own
#    settle-and-kick fork convention -- worth a proper investigation (a real
#    steady()-based calibration for second_order_w=TRUE, per the
#    calibrate-model skill, rather than the ad-hoc 10yr settle from an
#    arbitrary low spectrum) before concluding tr_bdf2 doesn't work here at
#    all, rather than just that this project's shortcut doesn't suit it.
# 4. Redo Day 40 Section 6/7's threshold_frac x boost heatmap under the fixed
#    mortality (Day 40's own item 11) -- still not done, and Section 5 above
#    shows knife_edge=10's fishing response itself changed somewhat under the
#    fix, so the heatmap's own optimum (troughs, threshold_frac=0.4, boost=30)
#    is not yet confirmed to survive.
################################################################################
