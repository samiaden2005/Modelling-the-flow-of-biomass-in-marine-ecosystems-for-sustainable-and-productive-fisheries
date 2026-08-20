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
plankton_state$time <- 0
plankton_state$factor <- 1

exact_logistic_immigration_step <- function(n, rate, capacity, immigration, mortality, dt) {
  result <- n
  active <- is.finite(n) & is.finite(rate) & is.finite(capacity) &
    is.finite(immigration) & is.finite(mortality) & rate > 0 & capacity > 0 & immigration >= 0
  if (dt == 0 || !any(active)) return(result)
  n0 <- n[active]; r <- rate[active]; k <- capacity[active]; i <- immigration[active]; mu <- mortality[active]
  a <- r - mu; b <- r / k
  next_n <- numeric(length(n0))
  has_immigration <- i > 0
  if (any(has_immigration)) {
    idx <- which(has_immigration)
    ai <- a[idx]; bi <- b[idx]; ii <- i[idx]
    d <- sqrt(ai^2 + 4 * bi * ii)
    n_plus <- ifelse(ai >= 0, (ai + d) / (2 * bi), 2 * ii / (d - ai))
    n_minus <- ifelse(ai <= 0, (ai - d) / (2 * bi), -2 * ii / (ai + d))
    ratio <- ((n0[idx] - n_plus) / (n0[idx] - n_minus)) * exp(-d * dt)
    next_n[idx] <- (n_plus - ratio * n_minus) / (1 - ratio)
  }
  no_immigration <- !has_immigration
  if (any(no_immigration)) {
    idx <- which(no_immigration)
    az <- a[idx]; bz <- b[idx]; nz <- n0[idx]
    value <- numeric(length(idx))
    zero_rate <- az == 0
    value[zero_rate] <- nz[zero_rate] / (1 + bz[zero_rate] * nz[zero_rate] * dt)
    positive <- az > 0 & nz > 0
    phi <- -expm1(-az[positive] * dt) / az[positive]
    value[positive] <- nz[positive] / (exp(-az[positive] * dt) + bz[positive] * nz[positive] * phi)
    negative <- az < 0
    exp_adt <- exp(az[negative] * dt)
    phi <- expm1(az[negative] * dt) / az[negative]
    value[negative] <- nz[negative] * exp_adt / (1 + bz[negative] * nz[negative] * phi)
    next_n[idx] <- value
  }
  result[active] <- pmax(next_n, 0)
  result
}

plankton_logistic <- function(params, n, n_pp, n_other, rates, dt = 0.1, ...) {
  plankton_state$time <- plankton_state$time + dt
  exact_logistic_immigration_step(n = n_pp, rate = params@rr_pp, capacity = params@cc_pp * plankton_state$factor,
                                  immigration = anchovy_immigration, mortality = rates$resource_mort, dt = dt)
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

anchovy_params <- function(interaction_val = 1, interaction_resource_val = 1, knife_edge_size = p2$w_mat, p = p2) {
  kappa <- p$a0 * exp(-6.9 * (p$lambda - 1))
  species_params_df <- data.frame(
    species = "Anchovy", w_min = p$w_min, w_mat = p$w_mat, m = p$rho_inf + 2/3,
    w_inf = p$w_inf, erepro = p$epsilon_R, alpha = p$K, ks = 0, gamma = p$gamma,
    q = p$alpha, ppmr_min = p$ppmr_min, ppmr_max = p$ppmr_max,
    pred_kernel_type = "norm_box", h = Inf, R_max = Inf, linecolour = "brown",
    stringsAsFactors = FALSE
  )
  params <- newMultispeciesParams(species_params_df, no_w = round(log(p$w_inf / p$w_min) / p$dx),
                                   lambda = p$lambda, kappa = kappa, w_pp_cutoff = p$w_pp_cutoff,
                                   resource_dynamics = "plankton_logistic")
  resource_rate(params) <- p$r0 * w_full(params)^(p$rho - 1)
  interaction_matrix(params) <- interaction_val
  species_params(params)$interaction_resource <- interaction_resource_val
  gp <- gear_params(params)
  gp$sel_func <- "knife_edge"
  gp$knife_edge_size <- knife_edge_size
  gp$catchability <- 1
  gear_params(params) <- gp
  setAnchovyMort(params, p)
}

p_scan <- anchovy_params()
anchovy_immigration <- p2$i0 * w_full(p_scan)^(-p2$lambda) * exp(-6.9 * (p2$lambda - 1))

################################################################################
# Flux check (report Section 3.3, Figure 4) -- the last of the four claims
# re-examined under the tightened settings that already eliminated the other
# three (tol_theta_sweep_check.R, tol_hysteresis_check.R): tol = 1e-5,
# t_max = 300, method = "tr_bdf2", dt = 0.02, effort = 0, knife_edge = 10.
#
# Two scenarios, the extremes of the original four-way comparison:
#   "default"  theta=1, ir=1 -- originally described as static, unimodal flux
#              peaking at w=1-2g, 0.395 g/year.
#   "both"     theta=0.3, ir=3 -- originally described as a static, bimodal
#              flux with a trough where "default" peaks.
#
# The "default" scenario does NOT converge to a fixed point under these
# settings -- it converges to a limit cycle. Its flux is unimodal at every
# phase, but the peak travels across w rather than sitting still, so a
# single getFlux() snapshot (as originally taken) is not a fixed property of
# the state. This script makes that explicit: it samples getFlux() across one
# full cycle period (via return_sim = TRUE and continuing the trajectory) and
# compares "both"'s static flux against the FULL min-max envelope the
# "default" state visits, not against one arbitrary phase of it.
################################################################################

tol_val    <- 1e-5
t_max_val  <- 300
dt_val     <- 0.02
method_val <- "tr_bdf2"

params_default <- anchovy_params(1, 1, knife_edge_size = 10)
params_both    <- anchovy_params(0.3, 3, knife_edge_size = 10)

p_default <- projectToSteady(params_default, t_per = 0.2, t_max = t_max_val, tol = tol_val,
                             dt = dt_val, method = method_val, effort = 0, progress_bar = FALSE)
p_both    <- projectToSteady(params_both, t_per = 0.2, t_max = t_max_val, tol = tol_val,
                             dt = dt_val, method = method_val, effort = 0, progress_bar = FALSE)

conv_default <- attr(p_default, "convergence")
conv_both    <- attr(p_both, "convergence")
cat(sprintf("default: type=%s, years=%.1f, residual=%.3g\n",
           conv_default$type, conv_default$years, conv_default$residual))
cat(sprintf("both:    type=%s, years=%.1f, residual=%.3g\n",
           conv_both$type, conv_both$years, conv_both$residual))

# "both" is a genuine fixed point (verified above): a single getFlux() call
# on the converged MizerParams is the exact steady-state flux.
flux_both_vec <- as.numeric(getFlux(p_both, power = 1))

# "default" is a limit cycle: sample flux across one full period rather than
# reading a single instant. t_save spaces 10 points evenly across the period.
stopifnot(identical(conv_default$type, "cycle"), !is.na(conv_default$period))
period <- conv_default$period
sim_cycle <- project(p_default, t_max = period, dt = dt_val, method = method_val,
                     t_save = period / 10, effort = 0, progress_bar = FALSE)

flux_sim <- getFlux(sim_cycle, power = 1)
w_vals <- as.numeric(dimnames(flux_sim)$w)
times  <- as.numeric(dimnames(flux_sim)$time)

flux_df <- do.call(rbind, lapply(seq_along(times), function(i) {
  data.frame(time = times[i], w = w_vals, flux = as.numeric(flux_sim[i, 1, ]))
}))

env_df <- flux_df %>%
  group_by(w) %>%
  summarise(flux_min = min(flux), flux_max = max(flux), .groups = "drop") %>%
  mutate(flux_both = flux_both_vec)

write.csv(env_df, file.path(plot_dir, "tol_flux_check.csv"), row.names = FALSE)

p_flux_check <- ggplot(env_df, aes(x = w)) +
  geom_ribbon(aes(ymin = flux_min, ymax = flux_max, fill = "default (theta=1,ir=1) cycle envelope"), alpha = 0.6) +
  geom_line(aes(y = flux_both, colour = "both (theta=0.3,ir=3), steady"), linewidth = 0.8) +
  scale_fill_manual(name = NULL, values = c("default (theta=1,ir=1) cycle envelope" = "grey70")) +
  scale_colour_manual(name = NULL, values = c("both (theta=0.3,ir=3), steady" = "#d95f02")) +
  scale_x_log10() +
  labs(title = "Flux check under tightened settings: bimodal 'both' vs default's full cycle envelope",
       subtitle = sprintf("effort=0, ke=10, tol=%.0e, t_max=%d, %s, dt=%.2f", tol_val, t_max_val, method_val, dt_val),
       x = "weight (g)", y = "biomass flux (g/year)") +
  theme_minimal() +
  theme(legend.position = "bottom")

save_plot(p_flux_check, "tol_flux_check.png")
cat("Flux check done -- see tol_flux_check.png / tol_flux_check.csv.\n")
