## ============================================================================
## 精确随机化检验（分层 A/B 实验，处理组总金额）
##
## 设计：
##   * 每个分层内处理组人数固定为实际人数 t_s；层内全体顾客的 C(n_s, t_s)
##     种划分等可能，各层独立 => 方案总数 N = ∏ C(n_s, t_s)。
##   * 统计量 T = 处理组总金额（整数分，退款为负值）。
##   * 双侧 p 值 = 满足 |T - E[T]| >= |T_obs - E[T]| 的方案数 / N（边界计入，
##     用精确有理数比较，不用浮点）。
##   * 金额相同的顾客按不同记录计数（DP 按“顾客记录”逐条处理，而非按金额取值）。
##
## 方法（不枚举、不抽样）：
##   每层用生成函数 DP：逐条顾客记录更新 “恰好选 j 人、和为 s 的方案数”，
##   得到该层恰选 t_s 人时总金额的精确分布；各层分布做精确整数卷积。
##   方案数用纯 R 实现的任意精度大整数（1e7 进制）保存，再大也不丢精度。
##
## 用法：
##   source("exact_randomization.R")
##   res <- exact_randomization_test(df)   # df 含 stratum / group / amount 三列
##   res$observed_total; res$expected; res$distribution; res$p_value
##
## 复杂度：DP 为 O(n · t · S)（S = 层内平移后金额和），卷积为 O(宽度乘积)。
## 金额以“分”为单位时一般很快；若金额有大的公因子，可先约分再算。
## ============================================================================

## ---------------------------------------------------------------------------
## 1. 任意精度有符号整数（纯 R；limbs 小端、基数 1e7、高位无零；sign ∈ -1/0/1）
## ---------------------------------------------------------------------------

BIG_BASE <- 1e7

.bn_new <- function(sign, limbs) {
  while (length(limbs) > 0L && limbs[length(limbs)] == 0) {
    limbs <- limbs[-length(limbs)]
  }
  if (length(limbs) == 0L) {
    sign <- 0L
  }
  structure(list(sign = as.integer(sign), limbs = limbs), class = "bignum")
}

bn_from_int <- function(x) {
  # x 为整数值数值，|x| < 2^53
  if (x == 0) {
    return(.bn_new(0L, numeric(0)))
  }
  s <- if (x < 0) -1L else 1L
  x <- abs(x)
  limbs <- numeric(0)
  while (x > 0) {
    r <- x %% BIG_BASE # x < 2^53，精确
    limbs <- c(limbs, r)
    x <- (x - r) / BIG_BASE
  }
  .bn_new(s, limbs)
}

.bn_cmp_mag <- function(a, b) {
  # 比较 |a| 与 |b|，返回 -1/0/1
  if (length(a) != length(b)) {
    return(if (length(a) < length(b)) -1L else 1L)
  }
  if (length(a) == 0L) {
    return(0L)
  }
  for (i in length(a):1) {
    if (a[i] != b[i]) return(if (a[i] < b[i]) -1L else 1L)
  }
  0L
}

.bn_add_mag <- function(a, b) {
  # |a| + |b|
  n <- max(length(a), length(b))
  a <- c(a, rep(0, n - length(a)))
  b <- c(b, rep(0, n - length(b)))
  s <- a + b
  carry <- 0
  for (i in seq_len(n)) {
    v <- s[i] + carry
    if (v >= BIG_BASE) {
      s[i] <- v - BIG_BASE
      carry <- 1
    } else {
      s[i] <- v
      carry <- 0
    }
  }
  if (carry) {
    s <- c(s, 1)
  }
  s
}

.bn_sub_mag <- function(a, b) {
  # |a| - |b|，要求 |a| >= |b|
  n <- length(a)
  b <- c(b, rep(0, n - length(b)))
  d <- a - b
  borrow <- 0
  for (i in seq_len(n)) {
    v <- d[i] - borrow
    if (v < 0) {
      d[i] <- v + BIG_BASE
      borrow <- 1
    } else {
      d[i] <- v
      borrow <- 0
    }
  }
  d
}

bn_add <- function(x, y) {
  if (x$sign == 0L) {
    return(y)
  }
  if (y$sign == 0L) {
    return(x)
  }
  if (x$sign == y$sign) {
    return(.bn_new(x$sign, .bn_add_mag(x$limbs, y$limbs)))
  }
  cmp <- .bn_cmp_mag(x$limbs, y$limbs)
  if (cmp == 0L) {
    return(.bn_new(0L, numeric(0)))
  }
  if (cmp > 0L) {
    .bn_new(x$sign, .bn_sub_mag(x$limbs, y$limbs))
  } else {
    .bn_new(y$sign, .bn_sub_mag(y$limbs, x$limbs))
  }
}

bn_neg <- function(x) .bn_new(-x$sign, x$limbs)
bn_sub <- function(x, y) bn_add(x, bn_neg(y))

bn_mul <- function(x, y) {
  if (x$sign == 0L || y$sign == 0L) {
    return(.bn_new(0L, numeric(0)))
  }
  a <- x$limbs
  b <- y$limbs
  na <- length(a)
  nb <- length(b)
  acc <- numeric(na + nb)
  i <- 1L
  while (i <= na) {
    blk <- min(i + 39L, na) # 每块 ≤40 次累加：40·(1e7-1)^2 < 2^53，精确
    for (j in i:blk) {
      idx <- j:(j + nb - 1L)
      acc[idx] <- acc[idx] + a[j] * b # 单项 < 1e14，精确
    }
    carry <- 0 # 块末立即进位规范化
    for (k in seq_along(acc)) {
      v <- acc[k] + carry
      r <- v %% BIG_BASE
      carry <- (v - r) / BIG_BASE
      acc[k] <- r
    }
    while (carry > 0) {
      r <- carry %% BIG_BASE
      acc <- c(acc, r)
      carry <- (carry - r) / BIG_BASE
    }
    i <- blk + 1L
  }
  .bn_new(x$sign * y$sign, acc)
}

bn_div_small <- function(x, d) {
  # x >= 0，d 为正整数（< ~9e8）；整除分解
  stopifnot(x$sign >= 0L, d >= 1)
  if (length(x$limbs) == 0L) {
    return(list(quotient = bn_from_int(0), remainder = 0))
  }
  q <- numeric(length(x$limbs))
  rem <- 0
  for (i in length(x$limbs):1) {
    cur <- rem * BIG_BASE + x$limbs[i] # < d·1e7 + 1e7 < 2^53，精确
    q[i] <- cur %/% d
    rem <- cur %% d
  }
  list(quotient = .bn_new(1L, q), remainder = rem)
}

bn_floor_div <- function(x, d) {
  # floor(x/d)，d 正整数；商假定 < 2^53
  mag <- .bn_new(1L, x$limbs)
  qd <- bn_div_small(mag, d)
  q <- bn_to_double(qd$quotient)
  if (x$sign >= 0L) {
    q
  } else if (qd$remainder > 0) {
    -(q + 1)
  } else {
    -q
  }
}
bn_ceil_div <- function(x, d) -bn_floor_div(bn_neg(x), d)

bn_to_double <- function(x) {
  # 可能 Inf（仅供显示/阈值，不参与判定）
  v <- 0
  if (length(x$limbs) > 0L) {
    for (i in length(x$limbs):1) {
      v <- v * BIG_BASE + x$limbs[i]
    }
  }
  x$sign * v
}

.limbs_to_str <- function(limbs) {
  while (length(limbs) > 0L && limbs[length(limbs)] == 0) {
    limbs <- limbs[-length(limbs)]
  }
  if (length(limbs) == 0L) {
    return("0")
  }
  hi <- format(limbs[length(limbs)], scientific = FALSE, trim = TRUE)
  lo <- if (length(limbs) > 1L) {
    paste0(sprintf("%07.0f", rev(limbs[-length(limbs)])), collapse = "")
  } else {
    ""
  }
  paste0(hi, lo)
}

bn_to_string <- function(x) {
  if (x$sign < 0L) {
    paste0("-", .limbs_to_str(x$limbs))
  } else {
    .limbs_to_str(x$limbs)
  }
}

bn_ratio_approx <- function(num, den) {
  # num/den 的浮点近似（取前两个 limb，~7 位有效数字）
  la <- num$limbs
  lb <- den$limbs
  if (length(la) == 0L) {
    return(0)
  }
  top2 <- function(L) {
    L[length(L)] + if (length(L) > 1L) L[length(L) - 1L] / BIG_BASE else 0
  }
  (top2(la) / top2(lb)) * BIG_BASE^(length(la) - length(lb))
}

.choose_bn <- function(n, k) {
  # 精确二项式系数（逐步整除）
  k <- min(k, n - k)
  res <- bn_from_int(1)
  if (k >= 1L) {
    for (i in seq_len(k)) {
      res <- bn_mul(res, bn_from_int(n - i + 1))
      dv <- bn_div_small(res, i)
      stopifnot(dv$remainder == 0) # 组合数性质保证整除
      res <- dv$quotient
    }
  }
  res
}

.gcd <- function(a, b) {
  while (b != 0) {
    r <- a %% b
    a <- b
    b <- r
  }
  a
}
.lcm <- function(a, b) a / .gcd(a, b) * b # 结果 < 2^53 时精确

## ---------------------------------------------------------------------------
## 2. 分布表示：totals（连续整数总额）+ counts（行=总额，列=大整数 limb，非负）
## ---------------------------------------------------------------------------

.norm_count_rows <- function(M, rows) {
  # 对指定行做 limb 进位规范化（值非负）
  L <- ncol(M)
  l <- 1L
  while (l <= L) {
    col <- M[rows, l]
    carry <- floor(col / BIG_BASE) # col < 2^53，精确
    if (any(carry != 0)) {
      M[rows, l] <- col - carry * BIG_BASE
      if (l == L) {
        M <- cbind(M, 0)
        L <- L + 1L
      }
      M[rows, l + 1L] <- M[rows, l + 1L] + carry
    }
    l <- l + 1L
  }
  M
}

.pad_cols <- function(M, L) {
  if (ncol(M) >= L) M else cbind(M, matrix(0, nrow(M), L - ncol(M)))
}

.rowsum_bn <- function(counts, rows) {
  # 指定行的计数之和 -> 大整数
  cs <- colSums(counts[rows, , drop = FALSE]) # < 1e7·行数，行数 << 9e8 时精确
  M <- .norm_count_rows(matrix(cs, nrow = 1L), 1L)
  .bn_new(1L, M[1L, ])
}

## 单分层：恰好选 t 人的子集和分布（生成函数 DP，按顾客记录逐条处理）
.stratum_dist <- function(amounts, t) {
  n <- length(amounts)
  stopifnot(t >= 0L, t <= n)
  if (t == 0L) {
    return(list(totals = 0, counts = matrix(1, 1L, 1L)))
  }
  sh <- if (min(amounts) < 0) -min(amounts) else 0 # 平移使金额非负
  b <- amounts + sh # 恰选 t 人时，总和只差常数 t·sh
  S <- sum(b) # 平移后最大可能总和
  W <- vector("list", t + 1L) # W[[k]]：恰选 k-1 人的计数矩阵
  for (k in seq_len(t + 1L)) {
    W[[k]] <- matrix(0, nrow = S + 1L, ncol = 1L)
  }
  W[[1L]][1L, 1L] <- 1 # 选 0 人、和为 0：1 种
  cum <- 0
  for (i in seq_len(n)) {
    a <- b[i]
    cum <- cum + a
    kmax <- min(i, t) + 1L # 处理 i 条记录后最多选 min(i,t) 人
    for (k in seq.int(kmax, 2L, by = -1L)) {
      # 倒序，避免复用本轮记录
      src <- .pad_cols(W[[k - 1L]], max(ncol(W[[k - 1L]]), ncol(W[[k]])))
      dst <- .pad_cols(W[[k]], ncol(src))
      rows_src <- seq_len(cum + 1L - a) # 前 i-1 条记录可达的和：0..(cum-a)
      dst[rows_src + a, ] <- dst[rows_src + a, ] + src[rows_src, ]
      W[[k - 1L]] <- src
      W[[k]] <- .norm_count_rows(dst, rows_src + a)
    }
  }
  counts <- W[[t + 1L]]
  nz <- which(rowSums(counts) != 0) # 行元素 < 1e7，行和精确
  keep <- min(nz):max(nz)
  list(
    totals = (keep - 1L) - t * sh, # 还原平移：实际总额 = 平移和 - t·sh
    counts = counts[keep, , drop = FALSE]
  )
}

## 两个分布的精确卷积（大整数计数，直接法）
.dist_convolve <- function(tot1, cnt1, tot2, cnt2) {
  n1 <- length(tot1)
  n2 <- length(tot2)
  L1 <- ncol(cnt1)
  L2 <- ncol(cnt2)
  out <- matrix(0, nrow = n1 + n2 - 1L, ncol = L1 + L2 + 1L)
  for (i in seq_len(n1)) {
    ai <- cnt1[i, ]
    rows <- i:(i + n2 - 1L)
    for (k in which(ai != 0)) {
      cols <- k:(k + L2 - 1L)
      out[rows, cols] <- out[rows, cols] + ai[k] * cnt2 # 标量<1e7 × limb<1e7，精确
    }
    out <- .norm_count_rows(out, rows) # 每个 out limb 至多累加 L1 次（<60 安全）
  }
  nz <- which(rowSums(out) != 0)
  keep <- min(nz):max(nz)
  list(
    totals = (tot1[1L] + tot2[1L]) + (keep - 1L),
    counts = out[keep, , drop = FALSE]
  )
}

## ---------------------------------------------------------------------------
## 3. 主函数：精确随机化检验
## ---------------------------------------------------------------------------

exact_randomization_test <- function(
  data,
  stratum = "stratum",
  group = "group",
  amount = "amount",
  treated = "treatment"
) {
  stopifnot(is.data.frame(data))
  st <- data[[stratum]]
  gr <- as.character(data[[group]])
  am <- as.numeric(data[[amount]])
  stopifnot(!anyNA(st), !anyNA(gr), !anyNA(am))
  stopifnot(all(am == trunc(am)), all(abs(am) < 2^53)) # 整数分

  strata <- unique(st) # 按出现顺序
  ns <- length(strata)
  n_s <- t_s <- integer(ns)
  tot_s <- numeric(ns)
  dists <- vector("list", ns)

  for (s in seq_len(ns)) {
    idx <- which(st == strata[s])
    n_s[s] <- length(idx)
    t_s[s] <- sum(gr[idx] == treated) # 层内实际处理人数（保持不变）
    tot_s[s] <- sum(am[idx])
    dists[[s]] <- .stratum_dist(am[idx], t_s[s])
  }

  T_obs <- sum(am[gr == treated]) # 实测处理组总金额（分）

  ## 随机化期望 E[T] = Σ_s t_s·(层总额/n_s) = P/Q（精确有理数）
  Q <- Reduce(.lcm, n_s)
  stopifnot(Q < 2^53)
  P <- bn_from_int(0)
  for (s in seq_len(ns)) {
    coef <- t_s[s] * (Q / n_s[s]) # 整数，< 2^53
    P <- bn_add(P, bn_mul(bn_from_int(coef), bn_from_int(tot_s[s])))
  }

  ## 各层分布卷积 -> T 的精确分布
  totals <- dists[[1L]]$totals
  counts <- dists[[1L]]$counts
  if (ns > 1L) {
    for (s in 2L:ns) {
      cv <- .dist_convolve(totals, counts, dists[[s]]$totals, dists[[s]]$counts)
      totals <- cv$totals
      counts <- cv$counts
    }
  }

  ## 方案总数 N：分布计数求和，并与 ∏ C(n_s, t_s) 独立交叉验证
  N_bn <- .rowsum_bn(counts, seq_len(nrow(counts)))
  N_check <- bn_from_int(1)
  for (s in seq_len(ns)) {
    N_check <- bn_mul(N_check, .choose_bn(n_s[s], t_s[s]))
  }
  stopifnot(identical(bn_to_string(N_bn), bn_to_string(N_check)))

  ## 双侧尾部：|x·Q - P| >= |T_obs·Q - P|（精确比较有理数距离，边界计入）
  v_obs <- bn_sub(bn_mul(bn_from_int(T_obs), bn_from_int(Q)), P)
  a_obs <- .bn_new(1L, v_obs$limbs) # |T_obs·Q - P|
  hi <- bn_ceil_div(bn_add(P, a_obs), Q) # x >= hi 进入右尾
  lo <- bn_floor_div(bn_sub(P, a_obs), Q) # x <= lo 进入左尾
  tail_rows <- which(totals <= lo | totals >= hi)
  tail_bn <- .rowsum_bn(counts, tail_rows)

  ## 期望约分显示
  rem <- bn_div_small(.bn_new(1L, P$limbs), Q)$remainder
  g <- .gcd(Q, rem)
  P_red <- .bn_new(P$sign, bn_div_small(.bn_new(1L, P$limbs), g)$quotient$limbs)
  Q_red <- Q / g
  exp_frac <- if (P$sign == 0L) {
    "0"
  } else {
    paste0(
      bn_to_string(P_red),
      if (Q_red != 1) paste0("/", format(Q_red, scientific = FALSE)) else ""
    )
  }
  exp_dec <- P$sign * bn_ratio_approx(.bn_new(1L, P$limbs), bn_from_int(Q))

  ## 各总额方案数表（相同总额已合并为一行；仅列出方案数非零的总额）
  nz <- which(rowSums(counts) != 0)
  tab <- data.frame(
    total = totals[nz],
    assignments = vapply(
      nz,
      function(r) .limbs_to_str(counts[r, ]),
      character(1L)
    ),
    probability = vapply(
      nz,
      function(r) bn_ratio_approx(.bn_new(1L, counts[r, ]), N_bn),
      numeric(1L)
    ),
    stringsAsFactors = FALSE
  )
  if (requireNamespace("tibble", quietly = TRUE)) {
    tab <- tibble::as_tibble(tab)
  }

  strata_summary <- data.frame(
    stratum = as.character(strata),
    n = n_s,
    treated = t_s,
    control = n_s - t_s,
    stratum_total = tot_s,
    expected_contribution = t_s * tot_s / n_s,
    stringsAsFactors = FALSE
  )
  if (requireNamespace("tibble", quietly = TRUE)) {
    strata_summary <- tibble::as_tibble(strata_summary)
  }

  list(
    observed_total = T_obs, # 实测处理组总金额（分）
    expected = list(fraction = exp_frac, decimal = exp_dec), # 随机化期望（分）
    n_assignments = bn_to_string(N_bn), # 方案总数 N（精确）
    distribution = tab, # 各总额方案数表
    p_value = list(
      fraction = paste0(bn_to_string(tail_bn), "/", bn_to_string(N_bn)),
      decimal = bn_ratio_approx(tail_bn, N_bn),
      tail_count = bn_to_string(tail_bn),
      tail_region = c(lower = lo, upper = hi) # T <= lo 或 T >= hi 计入尾部
    ),
    strata = strata_summary
  )
}
