library(mizer)
library(dplyr)
library(ggplot2)

plot_dir <- "interesting_plots"
dir.create(plot_dir, showWarnings = FALSE)

# --- Model builder (verbatim, see finding_jams/40_changed_mort_experiments.R
# Section 0 / finding_jams/43_experiments.R for the same code with its own
# derivation comments) ------------------------------------------------------

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
# Does the theta=0/ir=1/ke=10 hysteresis (Day 41 Section 8, the project's
# original and most-tested bistability claim) survive a much tighter
# convergence tolerance and a longer t_max, or is it an artefact of the
# default tol=0.1*t_per=0.02 stopping both branches early on a shared slow
# crawl toward a single fixed point (a saddle-node "ghost" -- distance between
# states t_per apart can go small algebraically slowly near a fold, long
# before the state has actually stopped moving)?
#
# `tol` has never been overridden anywhere in this project before this file --
# every sweep so far (40_changed_mort_experiments.R, 43_experiments.R) used
# the default. This also captures $residual (getSteadyResidual(), the actual
# per-capita rate of change at the final state) for the first time in this
# project -- a direct check independent of tol/distance_func, unlike $type
# and $years, which were the only fields any earlier sweep recorded.
#
# Both branches are single large jumps directly to fish_level=25 (from
# unfished, and from fish_level=100), not chained through intermediate
# effort levels -- if anything a STRICTER test of genuine bistability than
# the original chained hysteresis test, since it removes any path-dependence
# the chaining itself could introduce from not-fully-converged intermediate
# seeds.
#
# t_max=1000 is a real commitment (vs 100-150 used everywhere else in this
# project) -- if the tight-tol run still hasn't converged at that cap, that
# is itself informative (consistent with a slow crawl), not a failure to fix.
################################################################################

fl_test <- 25

run_hysteresis_check <- function(tol_val, t_max_val, label) {
  params0 <- anchovy_params(0, 1, knife_edge_size = 10)

  p_up <- projectToSteady(params0, t_per = 0.2, t_max = t_max_val, dt = p2$dt,
                          tol = tol_val, effort = fl_test, progress_bar = FALSE)
  conv_up <- attr(p_up, "convergence")

  p_high <- projectToSteady(params0, t_per = 0.2, t_max = t_max_val, dt = p2$dt,
                            tol = tol_val, effort = 100, progress_bar = FALSE)
  p_down <- projectToSteady(p_high, t_per = 0.2, t_max = t_max_val, dt = p2$dt,
                            tol = tol_val, effort = fl_test, progress_bar = FALSE)
  conv_down <- attr(p_down, "convergence")

  data.frame(
    setting = label, tol = tol_val, t_max = t_max_val,
    branch = c("up", "down"),
    biomass = c(unname(getBiomass(p_up)), unname(getBiomass(p_down))),
    conv_type = c(conv_up$type, conv_down$type),
    conv_years = c(conv_up$years, conv_down$years),
    residual = c(conv_up$residual, conv_down$residual)
  )
}

result_default <- run_hysteresis_check(tol_val = 0.1 * 0.2, t_max_val = 1000,
                                       label = "default_tol_0.02")
result_tight   <- run_hysteresis_check(tol_val = 0.1 * 0.2 / 100, t_max_val = 1000,
                                       label = "tight_tol_0.0002")

result <- bind_rows(result_default, result_tight)
write.csv(result, file.path(plot_dir, "tol_hysteresis_check.csv"), row.names = FALSE)
print(result)

rel_diff <- result %>%
  group_by(setting) %>%
  summarise(rel_diff = abs(diff(biomass)) / max(biomass), .groups = "drop")
cat("Relative up/down biomass gap at fish_level=25, by tol setting:\n")
print(rel_diff)
cat(paste(
  "If rel_diff stays large under the tight tol AND residual is genuinely",
  "small (near machine precision, not just below tol) on BOTH branches,",
  "that is evidence for real bistability. If rel_diff collapses under the",
  "tight tol, or residual stays large (the state is still visibly moving)",
  "under the default tol, that supports the tol-artefact explanation and",
  "the report's bifurcation claims need to be revisited before submission.\n"
))
