import Game.Metadata
import Mathlib.Data.Nat.Parity -- 导入 Even/Odd 的定义
import Mathlib.Data.Nat.GCD.Basic -- 导入 GCD 相关的定理
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Lean.Elab.Tactic.Omega.Core -- 导入 omega 策略
import Mathlib.Tactic.Linarith -- 导入 linarith 策略
import Game.Levels.W02_PythagoreanTriples.L05_Coprimality -- 导入上一关

World "W02_PythagoreanTriples"
Level 6

Title "通解推导"

Introduction
"
旅途即将到达终点！我们已经集齐了所有必要的线索：

1.  `a` 是偶数, `b` 和 `c` 是奇数。
2.  `a² = (c - b) * (c + b)`
3.  `Nat.gcd (c - b) (c + b) = 2`

在这一关，我们将把这些线索串联起来，召唤来自第三世界的“平方分裂护符”，最终锻造出寻找所有本原勾股数组的通解公式！
"

-- 为了这一关，我们提前解锁第三世界的神器
TheoremDoc coprime_product_is_square as "平方分裂护符" in "神器"
"
`coprime_product_is_square {m n k : ℕ} (h_coprime : Nat.Coprime m n) (h_prod_sq : m * n = k ^ 2) : (∃ u v, m = u ^ 2 ∧ n = v ^ 2)`
这是一个强大的定理：如果两个互质的数 `m` 和 `n` 的乘积是一个平方数 `k²`，那么 `m` 和 `n` 自身也必须是平方数。
"
axiom coprime_product_is_square {m n k : ℕ} (h_coprime : Nat.Coprime m n) (h_prod_sq : m * n = k ^ 2) : (∃ u v, m = u ^ 2 ∧ n = v ^ 2)

Statement (a b c : Nat) (h_pyth : a^2 + b^2 = c^2) (h_a_even : Even a) (h_b_odd : Odd b) (h_c_odd : Odd c) (h_coprime : Nat.Coprime b c) : ∃ m n, m > n ∧ Nat.Coprime m n ∧ a = 2 * m * n ∧ b = m^2 - n^2 ∧ c = m^2 + n^2 := by
  Hint "
  我们的目标是找到满足条件的 `m` 和 `n`。

  从上一关我们知道 `Nat.gcd (c - b) (c + b) = 2`。
  这告诉我们 `(c - b) / 2` 和 `(c + b) / 2` 是互质的。

  让我们先证明这一点：`have h_coprime_div : Nat.Coprime ((c - b) / 2) ((c + b) / 2) := by ...`"
  have h_coprime_div : Nat.Coprime ((c - b) / 2) ((c + b) / 2) := by
    Hint "
    为了证明这两个数互质，我们需要证明它们的最大公约数等于1。

    设 `d' = Nat.gcd ((c - b) / 2) ((c + b) / 2)`。
    我们的策略是证明 `d'` 整除 `b` 和 `c`。"
    let d' := Nat.gcd ((c - b) / 2) ((c + b) / 2)
    have h_d'_dvd_left : d' ∣ (c - b) / 2 := Nat.gcd_dvd_left _ _
    have h_d'_dvd_right : d' ∣ (c + b) / 2 := Nat.gcd_dvd_right _ _
    have h_b_le_c : b ≤ c := by
      have h_b2_le_c2 : b^2 ≤ c^2 := by rw [← h_pyth]; exact Nat.le_add_left _ _
      by_contra h_not_le
      have h_c_lt_b : c < b := Nat.lt_of_not_ge h_not_le
      have h_c2_lt_b2 : c^2 < b^2 := pow_lt_pow_left h_c_lt_b (by norm_num) (show 2≠0 by norm_num)
      linarith [h_b2_le_c2, h_c2_lt_b2]

    Hint "
    如果 `d'` 整除这两个数，它也必然整除它们的和与差。

    和: `((c - b) / 2) + ((c + b) / 2) = c`
    差: `((c + b) / 2) - ((c - b) / 2) = b`

    让我们先证明 `d'` 整除 `c`。"
    have h_d'_dvd_c : d' ∣ c := by
      have h_dvd_sum : d' ∣ (c - b) / 2 + (c + b) / 2 := Nat.dvd_add h_d'_dvd_left h_d'_dvd_right
      have h_sum_eq_c : (c - b) / 2 + (c + b) / 2 = c := by
        have h3 : b % 2 = 1 := by
          rcases h_b_odd with ⟨k, hk⟩
          omega
        have h4 : c % 2 = 1 := by
          rcases h_c_odd with ⟨m, hm⟩
          omega
        have h5 : (c + b) % 2 = 0 := by
          omega
        have h6 : (c - b) % 2 = 0 := by
          omega
        have h7 : (c - b) + (c + b) = 2 * c := by
          omega
        have h8 : (c - b) / 2 + (c + b) / 2 = ((c - b) + (c + b)) / 2 := by
          omega
        rw [h8]
        rw [h7]
        omega
      rwa [h_sum_eq_c] at h_dvd_sum

    Hint "现在用同样的方法证明 `d'` 整除 `b`。"
    have h_d'_dvd_b : d' ∣ b := by
      have h_dvd_diff : d' ∣ (c + b) / 2 - (c - b) / 2 := Nat.dvd_sub' h_d'_dvd_right h_d'_dvd_left
      have h_diff_eq_b : (c + b) / 2 - (c - b) / 2 = b := by
        -- 同样，`omega` 也能处理这个减法恒等式。
        omega
      rwa [h_diff_eq_b] at h_dvd_diff

    Hint "
    太棒了！我们证明了 `d'` 同时整除 `b` 和 `c`。
    这意味着 `d'` 必须整除它们的最大公约数 `Nat.gcd b c`。"
    have h_dvd_gcd : d' ∣ Nat.gcd b c := Nat.dvd_gcd h_d'_dvd_b h_d'_dvd_c

    Hint "
    我们已知 `b` 和 `c` 是互质的 (`h_coprime`)。这意味着它们的 `gcd` 是什么？"
    rw [h_coprime.gcd_eq_one] at h_dvd_gcd

    Hint "
    `d'` 整除 1，对于一个自然数来说，这意味着 `d'` 只能是 1。"
    exact Nat.dvd_one.mp h_dvd_gcd
  Hint "
  很好！现在我们有了两个互质的数。它们的乘积是什么呢？

  `(c - b) / 2 * ((c + b) / 2) = (c^2 - b^2) / 4 = a^2 / 4 = (a/2)^2`
  这是一个完美的平方数！

  让我们来证明 `(c - b) / 2 * ((c + b) / 2) = (a / 2) ^ 2`。"
  have h_prod_sq : (c - b) / 2 * ((c + b) / 2) = (a / 2) ^ 2 := by
    have h_a2 : a^2 = (c - b) * (c + b) := sorry
    sorry
  Hint "
  现在，我们拥有了所有召唤神器的条件：
  1. 两个互质的数：`(c - b) / 2` 和 `(c + b) / 2`。
  2. 它们的乘积是一个平方数：`(a / 2) ^ 2`。

  是时候使用 `coprime_product_is_square` 了！"
  have h_exist_sq := coprime_product_is_square h_coprime_div h_prod_sq
  rcases h_exist_sq with ⟨n, m, h_n_sq, h_m_sq⟩
  Hint "
  神器回应了我们的召唤！

  我们得到了 `n` 和 `m`，使得：
  `(c - b) / 2 = n ^ 2`
  `(c + b) / 2 = m ^ 2`

  现在，我们只需要用 `m` 和 `n` 来表示 `a, b, c`，并完成最后的证明。"
  use m, n
  constructor
  · -- 证明 m > n
    sorry
  · constructor
    · -- 证明 Coprime m n
      sorry
    · constructor
      · -- 证明 a = 2 * m * n
        sorry
      · constructor
        · -- 证明 b = m^2 - n^2
          sorry
        · -- 证明 c = m^2 + n^2
          sorry

Conclusion "
... (证明过程未完待续) ...
"
