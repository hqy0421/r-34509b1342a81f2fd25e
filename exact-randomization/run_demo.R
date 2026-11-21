#!/usr/bin/env Rscript
## ============================================================================
## 精确随机化检验：演示 + 暴力枚举校验 + 大方案数精确性演示
## 运行：Rscript --vanilla run_demo.R
## ============================================================================

args <- commandArgs(trailingOnly = FALSE)
file_arg <- grep("^--file=", args, value = TRUE)
this_dir <- if (length(file_arg)) dirname(normalizePath(sub("^--file=", "", file_arg[1L]))) else getwd()
source(file.path(this_dir, "exact_randomization.R"), encoding = "UTF-8")
suppressPackageStartupMessages(library(tibble))

## ---------------------------------------------------------------------------
## 0. 大整数自检
## ---------------------------------------------------------------------------
stopifnot(
  bn_to_string(bn_mul(bn_from_int(123456789), bn_from_int(987654321))) == "121932631112635269",
  bn_to_string(bn_add(bn_from_int(999999999999), bn_from_int(1))) == "1000000000000",
  bn_to_string(bn_sub(bn_from_int(1), bn_from_int(1000000000000))) == "-999999999999",
  bn_to_string(.choose_bn(50, 25)) == "126410606437752",
  bn_floor_div(bn_from_int(-7), 2) == -4, bn_ceil_div(bn_from_int(-7), 2) == -3,
  bn_floor_div(bn_from_int(7), 2) == 3,   bn_ceil_div(bn_from_int(7), 2) == 4
)
cat("[OK] 大整数运算自检通过\n\n")

print_result <- function(res, title) {
  cat("================================================================\n")
  cat(title, "\n")
  cat("================================================================\n")
  cat("-- 分层摘要（层内处理人数保持实际值）--\n")
  print(res$strata)
  cat("\n实测总金额单位：分（退款为负值）\n")
  cat("实测处理组总金额 T_obs =", res$observed_total, "\n")
  cat("随机化期望   E[T]  =", res$expected$fraction, "≈", sprintf("%.6f", res$expected$decimal), "\n")
  cat("方案总数     N     =", res$n_assignments, "\n")
  tr <- res$p_value$tail_region
  cat("双侧尾部区域：T <=", tr["lower"], "或 T >=", tr["upper"],
      "（|T-E| >= |T_obs-E|，边界计入）\n")
  cat("尾部方案数 =", res$p_value$tail_count, "\n")
  cat("精确 p 值  =", res$p_value$fraction, "\n")
  cat("          ≈", sprintf("%.8g", res$p_value$decimal), "\n")
  cat("-- 各总额方案数表（相同总额已合并，仅列非零；共",
      nrow(res$distribution), "个不同总额）--\n")
  print(res$distribution, n = 14)
  cat("\n")
  invisible(res)
}

## 独立校验：由分布重算期望，验证 Σ x·f(x)·Q == P·N（精确恒等式）
check_expectation_identity <- function(res_totals, res_counts, P, Q, N_bn) {
  S1 <- bn_from_int(0)
  for (r in seq_along(res_totals)) {
    row <- res_counts[r, ]
    if (any(row != 0))
      S1 <- bn_add(S1, bn_mul(bn_from_int(res_totals[r]), .bn_new(1L, row)))
  }
  identical(bn_to_string(bn_mul(S1, bn_from_int(Q))),
            bn_to_string(bn_mul(P, N_bn)))
}

## ---------------------------------------------------------------------------
## 例 1：小规模门店促销数据（可用暴力枚举完全验证）
##   3 个分层；金额含退款负值、同额顾客；N = C(5,2)·C(6,3)·C(4,2) = 1200
## ---------------------------------------------------------------------------
demo_small <- tibble::tribble(
  ~stratum, ~group,      ~amount,
  # 分层 A：5 人，处理 2 人；有两名同额 800 的顾客、一笔 -300 退款
  "A", "treatment", 1200L,
  "A", "control",    800L,
  "A", "treatment",  800L,
  "A", "control",   -300L,
  "A", "control",    450L,
  # 分层 B：6 人，处理 3 人；两笔 -500 退款
  "B", "treatment", 2000L,
  "B", "control",   1500L,
  "B", "control",   -500L,
  "B", "treatment", -500L,
  "B", "control",    700L,
  "B", "treatment",    0L,
  # 分层 C：4 人，处理 2 人；三名同额 300 的顾客
  "C", "control",    300L,
  "C", "treatment",  300L,
  "C", "control",    300L,
  "C", "treatment",  100L
)

res1 <- exact_randomization_test(demo_small)
print_result(res1, "例 1：门店促销 A/B 实验（3 个分层，N = 1200）")

## ---- 暴力枚举全部 1200 种方案，逐一核对 ----
brute_force <- function(data, treated = "treatment") {
  strata <- unique(data$stratum)
  combos <- lapply(strata, function(s) {
    idx <- which(data$stratum == s)
    combn(idx, sum(data$group[idx] == treated), simplify = FALSE)
  })
  grid <- expand.grid(lapply(combos, seq_along))
  sums <- apply(grid, 1L, function(row) {
    tot <- 0
    for (s in seq_along(strata)) tot <- tot + sum(data$amount[combos[[s]][[row[s]]]])
    tot
  })
  table(sums)
}

bf <- brute_force(demo_small)
bf_counts <- as.integer(bf)
bf_totals <- as.integer(names(bf))
tab1 <- res1$distribution
m <- match(tab1$total, bf_totals)
stopifnot(
  !anyNA(m),                                  # DP 的每个总额都在枚举中
  identical(as.integer(tab1$assignments), bf_counts[m]),  # 方案数完全一致
  identical(sum(bf_counts), 1200L),
  res1$n_assignments == "1200"
)

## 暴力法 p 值（精确有理数距离）
Q1 <- 60   # lcm(5,6,4)
P1 <- 2 * sum(demo_small$amount[demo_small$stratum == "A"]) * 12 +
      3 * sum(demo_small$amount[demo_small$stratum == "B"]) * 10 +
      2 * sum(demo_small$amount[demo_small$stratum == "C"]) * 15
sums_all <- rep(bf_totals, bf_counts)
v <- abs(sums_all * Q1 - P1)
v_obs <- abs(res1$observed_total * Q1 - P1)
tail_brute <- sum(v >= v_obs)
stopifnot(
  res1$p_value$tail_count == as.character(tail_brute),
  res1$p_value$fraction == paste0(tail_brute, "/1200"),
  all.equal(res1$p_value$decimal, tail_brute / 1200),
  res1$expected$fraction == "3280"
)
cat("[OK] 例 1：分布表、期望、尾部方案数、p 值与 1200 种方案的暴力枚举完全一致\n\n")

## ---------------------------------------------------------------------------
## 例 2：方案数超过 2^53（双精度已无法精确表示），验证大整数精确性
##   N = C(30,15)·C(30,14)·C(10,5) = 155117520·145422675·252
## ---------------------------------------------------------------------------
mk_stratum <- function(n, t, offset) {
  amounts <- ((seq_len(n) * 37L + offset * 11L) %% 201L) - 100L  # -100..100 分，含负值与同额
  data.frame(stratum = paste0("S", offset),
             group = c(rep("treatment", t), rep("control", n - t)),
             amount = amounts, stringsAsFactors = FALSE)
}
demo_mid <- dplyr::bind_rows(mk_stratum(30L, 15L, 1L),
                             mk_stratum(30L, 14L, 2L),
                             mk_stratum(10L,  5L, 3L))

t0 <- proc.time()[["elapsed"]]
res2 <- exact_randomization_test(demo_mid)
elapsed <- proc.time()[["elapsed"]] - t0
print_result(res2, "例 2：较大分层（N ≈ 5.68×10^18 > 2^53，计数仍精确）")
cat(sprintf("（例 2 计算耗时 %.2f 秒）\n", elapsed))

## 交叉验证：N 与独立计算的 ∏ C(n_s,t_s) 一致（主函数内已 stopifnot），
## 且 N 的十进制字符串与理论值一致
N_theory <- bn_mul(bn_mul(bn_from_int(155117520), bn_from_int(145422675)), bn_from_int(252))
stopifnot(identical(res2$n_assignments, bn_to_string(N_theory)))
cat("[OK] 例 2：方案总数 N =", res2$n_assignments, "（> 2^53）与 ∏C(n_s,t_s) 精确一致\n")

## 期望恒等式校验（用主函数内部状态重算一遍分布层面的期望）
## —— 直接利用函数返回值无法拿到 counts 矩阵，这里重算一次分布做校验
chk <- local({
  strata <- unique(demo_mid$stratum)
  ds <- lapply(strata, function(s) {
    idx <- which(demo_mid$stratum == s)
    .stratum_dist(demo_mid$amount[idx], sum(demo_mid$group[idx] == "treatment"))
  })
  totals <- ds[[1]]$totals; counts <- ds[[1]]$counts
  for (s in 2:length(ds)) {
    cv <- .dist_convolve(totals, counts, ds[[s]]$totals, ds[[s]]$counts)
    totals <- cv$totals; counts <- cv$counts
  }
  n_s <- vapply(strata, function(s) sum(demo_mid$stratum == s), integer(1))
  t_s <- vapply(strata, function(s) sum(demo_mid$group[demo_mid$stratum == s] == "treatment"), integer(1))
  tot_s <- vapply(strata, function(s) sum(demo_mid$amount[demo_mid$stratum == s]), numeric(1))
  Q <- Reduce(.lcm, n_s)
  P <- bn_from_int(0)
  for (s in seq_along(strata))
    P <- bn_add(P, bn_mul(bn_from_int(t_s[s] * (Q / n_s[s])), bn_from_int(tot_s[s])))
  N_bn <- .rowsum_bn(counts, seq_len(nrow(counts)))
  list(ok = check_expectation_identity(totals, counts, P, Q, N_bn),
       N = bn_to_string(N_bn))
})
stopifnot(chk$ok, chk$N == res2$n_assignments)
cat("[OK] 例 2：由分布重算的期望与精确有理数期望完全一致（Σx·f(x)·Q == P·N）\n")

## 保存两张分布表（方案数以十进制字符串保存，不丢精度）
write.csv(res1$distribution, file.path(this_dir, "distribution_example1.csv"), row.names = FALSE)
write.csv(res2$distribution, file.path(this_dir, "distribution_example2.csv"), row.names = FALSE)
cat("\n分布表已写出：distribution_example1.csv / distribution_example2.csv\n")
cat("全部校验通过。\n")
