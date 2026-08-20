library(mizer)
library(dplyr)
library(ggplot2)

# Day 43: `40_changed_mort_experiments.R` had grown to 2700+ lines, so this
# starts a fresh file rather than appending further -- same self-contained
# convention since Day 20 (helpers redefined here, verbatim from
# `40_changed_mort_experiments.R`'s own Section 0), not a source() of the old
# file. Continues Day 42's own Section 20/23 work: does the "mean yield hides
# a real interior peak in the max envelope" finding generalise across theta,
# or is it specific to theta=0.3?
#
# This file's first task is a live rerun of theta=0 and theta=0.3 (ir=1,
# ke=10) specifically -- both had already run once during Day 42 itself
# (day42_yield_env_th0.png/day42_yield_env_th03.png already exist), but a
# live attempt to rerun them got stuck queued behind another long call in the
# same R console and never confirmed completion, so this makes them
# reproducible from a clean script instead of relying on that stuck session.

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
# Section 0: the model builder, ported verbatim from
# `40_changed_mort_experiments.R`'s own Section 0 (itself ported from the
# CURRENT `39_experiments.R`) -- unchanged, just relocated so this file does
# not depend on the old one being sourced or already run in the session.
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

################################################################################
# Section 1: yield-envelope sweep, ported verbatim from
# `40_changed_mort_experiments.R`'s own Section 20 -- return_sim = TRUE keeps
# the trajectory so min/max yield over the settled window can be read off
# directly, instead of the single arbitrary-phase snapshot a plain
# projectToSteady() MizerParams result gives for a cycling state.
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

effort_seq_fine_env <- seq(0, 100, by = 5)

################################################################################
# Section 2: theta=0 and theta=0.3, ir=1, ke=10 -- the two values already
# reported in the Day 42 post. Rerun here from a clean, self-contained script
# instead of relying on the earlier live session, where an attempt to rerun
# both got stuck queued behind a still-running theta=0.7 call and never
# confirmed completion. Output filenames match what the Day 42 post already
# references, so this is a straight reproducibility rerun, not a new figure.
################################################################################

env_th0_ir1 <- run_yield_envelope_sweep(0, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th0_ir1, file.path(plot_dir, "day42_yield_env_th0_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th0_ir1, "theta=0, ir=1, ke=10"), "day42_yield_env_th0.png")
cat("Section 2: theta=0 done.\n")

env_th03_ir1 <- run_yield_envelope_sweep(0.3, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th03_ir1, file.path(plot_dir, "day42_yield_env_th03_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th03_ir1, "theta=0.3, ir=1, ke=10"), "day42_yield_env_th03.png")
cat("Section 2: theta=0.3 done.\n")

################################################################################
# Section 3: theta=0.7 and theta=1, ir=1, ke=10 -- the same comparison,
# extended to the two remaining theta values that also cycle at every effort
# level at this (ir, ke) (confirmed via Section 18's own rows in
# `40_changed_mort_experiments.R`; theta=0 above is the one exception, always
# steady, which is why its own ribbon is trivial). Ported verbatim from that
# file's own Section 23 -- kept here too, alongside theta=0/0.3, so this file
# is the single, complete home for the across-theta yield-envelope
# comparison rather than splitting it across two files.
################################################################################

env_th07_ir1 <- run_yield_envelope_sweep(0.7, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th07_ir1, file.path(plot_dir, "day42_yield_env_th07_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th07_ir1, "theta=0.7, ir=1, ke=10"), "day42_yield_env_th07.png")
cat("Section 3: theta=0.7 done.\n")

env_th10_ir1 <- run_yield_envelope_sweep(1, 1, 10, effort_seq = effort_seq_fine_env)
write.csv(env_th10_ir1, file.path(plot_dir, "day42_yield_env_th10_ir1.csv"), row.names = FALSE)
save_plot(plot_yield_envelope(env_th10_ir1, "theta=1, ir=1, ke=10"), "day42_yield_env_th10.png")
cat("Section 3: theta=1 done.\n")

################################################################################
# Section 4: the same min/max yield-envelope technique, but chained BOTH
# directions (up from unfished, down from fish_level=100) on the SAME fine
# effort grid Sections 2/3 used -- Section 20/23's own sweeps (and Sections
# 2/3 above) only ever went up, so any bistability between the up and down
# branches would be invisible in them, exactly the gap Section 18 exists to
# close for the coarse 5-point grid. This closes it at the fine 21-point
# resolution instead, combining both this file's own envelope technique and
# `40_changed_mort_experiments.R` Section 18's own up/down chaining into one
# figure per theta.
#
# run_yield_envelope_chain() factors the per-effort-point body of Section 1's
# own run_yield_envelope_sweep() out so both directions can share it; the
# down chain seeds from a single large jump straight to fish_level=100 (same
# convention as Section 18's own params_high_bistab), then steps down.
################################################################################

run_yield_envelope_chain <- function(start_params, effort_seq, direction,
                                     t_per = 0.2, t_max = 100) {
  current <- start_params
  bind_rows(lapply(effort_seq, function(fl) {
    sim <- projectToSteady(current, t_per = t_per, t_max = t_max, dt = p2$dt,
                           effort = fl, return_sim = TRUE, progress_bar = FALSE)
    current <<- finalParams(sim)
    conv <- attr(sim, "convergence")

    yield_ts <- rowSums(getYield(sim))
    n <- length(yield_ts)
    window_n <- if (identical(conv$type, "cycle") && !is.na(conv$period)) {
      min(n, max(2, round(3 * conv$period / t_per)))
    } else {
      max(2, n %/% 2)
    }
    tail_ts <- utils::tail(yield_ts, window_n)

    data.frame(fish_level = fl, direction = direction, conv_type = conv$type,
              conv_years = conv$years, conv_period = conv$period,
              yield_mean = mean(tail_ts), yield_min = min(tail_ts), yield_max = max(tail_ts))
  }))
}

run_yield_envelope_bifurcation <- function(theta_val, ir_val, ke_val = 10,
                                           effort_seq = seq(0, 100, by = 5),
                                           t_per = 0.2, t_max = 100) {
  base_params <- anchovy_params(theta_val, ir_val, knife_edge_size = ke_val)

  up_df <- run_yield_envelope_chain(base_params, effort_seq, "up", t_per, t_max)

  sim_high <- projectToSteady(base_params, t_per = t_per, t_max = t_max, dt = p2$dt,
                              effort = max(effort_seq), return_sim = TRUE,
                              progress_bar = FALSE)
  params_high <- finalParams(sim_high)
  down_df <- run_yield_envelope_chain(params_high, rev(effort_seq), "down", t_per, t_max)

  bind_rows(up_df, down_df)
}

plot_yield_envelope_bifurcation <- function(df, title_suffix) {
  ggplot(df, aes(x = fish_level, fill = direction, colour = direction)) +
    geom_ribbon(aes(ymin = yield_min, ymax = yield_max), alpha = 0.25) +
    geom_line(aes(y = yield_mean), linewidth = 0.7) +
    geom_point(aes(y = yield_mean, shape = conv_type), size = 2) +
    scale_fill_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_colour_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_shape_manual(values = c(steady = 16, cycle = 17, extinction = 4), drop = FALSE) +
    labs(title = sprintf("Yield bifurcation (up + down), %s", title_suffix),
        subtitle = "Ribbon = min-to-max yield over the settled window, both directions overlaid.",
        x = "fish_level (Constant effort)", y = "yield (g/year)",
        fill = "direction", colour = "direction", shape = "conv_type") +
    theme_minimal()
}

for (theta_val in c(0, 0.3, 0.7, 1)) {
  bifurc_df <- run_yield_envelope_bifurcation(theta_val, ir_val = 1, ke_val = 10,
                                              effort_seq = effort_seq_fine_env)
  theta_tag <- gsub("\\.", "", sprintf("%.1f", theta_val))
  write.csv(bifurc_df, file.path(plot_dir, sprintf("day43_yield_bifurc_th%s.csv", theta_tag)),
           row.names = FALSE)
  p_bifurc <- plot_yield_envelope_bifurcation(bifurc_df, sprintf("theta=%.1f, ir=1, ke=10", theta_val))
  save_plot(p_bifurc, sprintf("day43_yield_bifurc_th%s.png", theta_tag))
  cat(sprintf("Section 4: theta=%.1f up+down done.\n", theta_val))
}
