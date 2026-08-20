library(mizer)
library(dplyr)
library(ggplot2)

plot_dir <- "interesting_plots"
dir.create(plot_dir, showWarnings = FALSE)

save_plot <- function(plot, filename, width = 9, height = 6, dpi = 150) {
  print(plot)
  ggsave(file.path(plot_dir, filename), plot = plot, width = width, height = height, dpi = dpi)
}

# --- Model builder ---------------------------------------------------------

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

# --- Yield-envelope bifurcation sweep (up + down) ---------------------------

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

# --- theta = 0, ir = 1, ke = 10 ---------------------------------------------

bifurc_df <- run_yield_envelope_bifurcation(theta_val = 0, ir_val = 1, ke_val = 10,
                                            effort_seq = seq(0, 100, by = 5))
write.csv(bifurc_df, file.path(plot_dir, "day43_yield_bifurc_th00.csv"), row.names = FALSE)
save_plot(plot_yield_envelope_bifurcation(bifurc_df, "theta=0, ir=1, ke=10"),
         "day43_yield_bifurc_th00.png")
