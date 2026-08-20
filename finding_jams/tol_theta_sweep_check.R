library(mizer)
library(dplyr)
library(ggplot2)

plot_dir <- "interesting_plots"
dir.create(plot_dir, showWarnings = FALSE)

save_plot <- function(plot, filename, width = 9, height = 6, dpi = 150) {
  print(plot)
  ggsave(file.path(plot_dir, filename), plot = plot, width = width, height = height, dpi = dpi)
}

# --- Model builder -----------------------------------------------------

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

# --- Theta sweep, default tol / t_max, second-order scheme ---------------
# Same chaining trick as Section 21 (40_changed_mort_experiments.R): theta is
# rebuilt via anchovy_params() at each step, previous step's converged state
# carried across via initialN()<-/initialNResource()<-. tol/t_max set back
# to this project's usual defaults (0.02 / 80) here -- see
# tol_hysteresis_check.R for the tightened-tolerance version of this same
# question applied to the fish_level sweep instead of theta.
#
# method = "tr_bdf2" and dt = 0.02 (vs the first-order default and this
# project's usual dt = p2$dt = 0.001 elsewhere) -- the larger step is only
# usable because tr_bdf2 is second-order; this also directly addresses the
# "scheme-dependence untested" limitation flagged for this sweep in
# draft_report/report.qmd Section 4, not just a speed change.

tol_val    <- 1e-5   # 0.02, this project's usual default
t_max_val  <- 300      # this project's usual default (Section 21)
dt_val     <- 0.02    # vs p2$dt = 0.001 used elsewhere in this project
method_val <- "tr_bdf2"

# run_theta_chain() used to read mean_total/mean_yield as a single
# getBiomass()/getYield() snapshot at whatever instant the chain happened to
# stop -- fine for a genuine fixed point, but for a "cycle" classification
# that is one arbitrary phase of the cycle, not a summary of it. Direct
# inspection of theta=1/ir=1/ke=10/fish_level=10 (the point that kept coming
# back "not_converged") showed a clean, perfectly regular limit cycle
# swinging roughly between 0.04 and 0.55 -- a single snapshot from that could
# land almost anywhere in that range, which is enough on its own to produce
# an apparent "gap" between two branches riding the SAME cycle at different
# phases. Same fix as Section 20's run_yield_envelope_sweep(): return_sim =
# TRUE keeps the trajectory, and mean/min/max are read from a settled tail
# window (last 3 cycle periods if conv_type == "cycle", else the back half
# of the run) instead of the single final instant.

run_theta_chain <- function(ir_val, ke_val, fl, theta_seq,
                            tol = tol_val, t_per = 0.2, t_max = t_max_val,
                            dt = dt_val, method = method_val) {
  current <- anchovy_params(theta_seq[1], ir_val, knife_edge_size = ke_val)
  bind_rows(lapply(theta_seq, function(th) {
    params_th <- anchovy_params(th, ir_val, knife_edge_size = ke_val)
    initialN(params_th) <- initialN(current)
    initialNResource(params_th) <- initialNResource(current)
    sim <- projectToSteady(params_th, t_per = t_per, t_max = t_max, tol = tol,
                           dt = dt, method = method, effort = fl,
                           return_sim = TRUE, progress_bar = FALSE)
    current <<- finalParams(sim)
    conv <- attr(sim, "convergence")

    biomass_ts <- rowSums(getBiomass(sim))
    yield_ts   <- rowSums(getYield(sim))
    n <- length(biomass_ts)
    window_n <- if (identical(conv$type, "cycle") && !is.na(conv$period)) {
      min(n, max(2, round(3 * conv$period / t_per)))
    } else {
      max(2, n %/% 2)
    }
    b_tail <- utils::tail(biomass_ts, window_n)
    y_tail <- utils::tail(yield_ts, window_n)

    data.frame(theta = th,
              mean_total = mean(b_tail), min_total = min(b_tail), max_total = max(b_tail),
              mean_yield = mean(y_tail), min_yield = min(y_tail), max_yield = max(y_tail),
              conv_type = conv$type, conv_years = conv$years,
              conv_period = conv$period, residual = conv$residual)
  }))
}

plot_theta_bifurcation <- function(up_df, down_df, title_suffix) {
  df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down"))
  ggplot(df, aes(x = theta, colour = direction, fill = direction, group = direction)) +
    geom_ribbon(aes(ymin = min_total, ymax = max_total), alpha = 0.2, colour = NA) +
    geom_line(aes(y = mean_total), linewidth = 0.6) +
    geom_point(aes(y = mean_total, shape = conv_type), size = 2.2) +
    scale_colour_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_fill_manual(values = c(up = "#d95f02", down = "#1b9e77")) +
    scale_shape_manual(values = c(steady = 16, cycle = 17, extinction = 4), drop = FALSE) +
    labs(title = sprintf("Bifurcation diagram vs theta (%s, dt=%.2f), %s", method_val, dt_val, title_suffix),
        subtitle = sprintf("tol=%.5f, t_max=%d. fish_level=10, knife_edge=10. Ribbon = min-max over the settled window.", tol_val, t_max_val),
        x = "theta (cannibalism strength)", y = "total biomass (g)",
        colour = "direction", fill = "direction", shape = "conv_type") +
    theme_minimal()
}

theta_seq_fine <- seq(0, 1, by = 0.1)

for (ir_val in c(1, 5)) {
  up_df   <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 10, theta_seq = theta_seq_fine)
  down_df <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 10, theta_seq = rev(theta_seq_fine))

  out_df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down")) %>%
    mutate(interaction_resource = ir_val, knife_edge_size = 10, fish_level = 10,
          tol = tol_val, t_max = t_max_val)
  write.csv(out_df, file.path(plot_dir, sprintf("tol_theta_bifurc_ir%d.csv", ir_val)),
           row.names = FALSE)

  p_theta <- plot_theta_bifurcation(up_df, down_df,
                                    sprintf("interaction_resource=%d, ke=10, fish_level=10", ir_val))
  save_plot(p_theta, sprintf("tol_theta_bifurc_ir%d.png", ir_val))
  cat(sprintf("ir=%d done.\n", ir_val))
}

# --- Same sweep, no fishing at all (fish_level = 0) -----------------------
# Is the theta-crossing structure intrinsic to the cannibalism/resource-
# competition dynamics, or does it require some minimum fishing forcing to
# appear? Everything else (tol, t_max, ir values, theta grid, chaining
# method) unchanged from the fish_level=10 sweep above.

for (ir_val in c(1, 5)) {
  up_df   <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 0, theta_seq = theta_seq_fine)
  down_df <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 0, theta_seq = rev(theta_seq_fine))

  out_df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down")) %>%
    mutate(interaction_resource = ir_val, knife_edge_size = 10, fish_level = 0,
          tol = tol_val, t_max = t_max_val)
  write.csv(out_df, file.path(plot_dir, sprintf("tol_theta_bifurc_nofish_ir%d.csv", ir_val)),
           row.names = FALSE)

  p_theta <- plot_theta_bifurcation(up_df, down_df,
                                    sprintf("interaction_resource=%d, ke=10, fish_level=0", ir_val))
  save_plot(p_theta, sprintf("tol_theta_bifurc_nofish_ir%d.png", ir_val))
  cat(sprintf("no-fishing ir=%d done.\n", ir_val))
}

# --- Same sweep, fish_level = 25 -------------------------------------------
# fl=25 sits inside the fish_level window where the original theta=0/ir=1/
# ke=10 effort-sweep hysteresis was found (Day 41 Section 8; also the point
# tested directly in tol_hysteresis_check.R) -- this checks whether the
# theta-crossing structure looks the same at that specific forcing level as
# it does at fl=0 (above) and fl=10 (the main sweep).

for (ir_val in c(1, 5)) {
  up_df   <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 25, theta_seq = theta_seq_fine)
  down_df <- run_theta_chain(ir_val = ir_val, ke_val = 10, fl = 25, theta_seq = rev(theta_seq_fine))

  out_df <- bind_rows(mutate(up_df, direction = "up"), mutate(down_df, direction = "down")) %>%
    mutate(interaction_resource = ir_val, knife_edge_size = 10, fish_level = 25,
          tol = tol_val, t_max = t_max_val)
  write.csv(out_df, file.path(plot_dir, sprintf("tol_theta_bifurc_fl25_ir%d.csv", ir_val)),
           row.names = FALSE)

  p_theta <- plot_theta_bifurcation(up_df, down_df,
                                    sprintf("interaction_resource=%d, ke=10, fish_level=25", ir_val))
  save_plot(p_theta, sprintf("tol_theta_bifurc_fl25_ir%d.png", ir_val))
  cat(sprintf("fish_level=25 ir=%d done.\n", ir_val))
}
