import Game.Metadata
import Mathlib.Data.Nat.Parity -- 导入 Even/Odd 的定义
import Mathlib.Data.Nat.GCD.Basic -- 导入 GCD 相关的定理
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Mathlib.Tactic.Linarith -- 导入 linarith 策略
import Game.Levels.W02_PythagoreanTriples.L04_DifferenceOfSquares -- 导入上一关

World "W02_PythagoreanTriples"
Level 5

Title "互质性 (Coprimality)"

Introduction
"
在上一关，我们得到了 `a² = (c - b) * (c + b)`。这是一个关于乘积的等式。

为了利用第三大关的“平方分裂护符”，我们需要证明 `(c - b)` 和 `(c + b)` 这两个因数是互质的（或者说，它们除了公因数2之外没有其他公因数）。

在这一关，我们的目标就是证明 `gcd(c - b, c + b) = 2`。我们将通过证明它们的最大公约数 `d` 既整除 2 又被 2 整除来完成。
"

Statement (a b c : Nat) (h_pyth : a^2 + b^2 = c^2) (h_a_even : Even a) (h_b_odd : Odd b) (h_c_odd : Odd c) (h_coprime : Nat.Coprime b c) : Nat.gcd (c - b) (c + b) = 2 := by
  Hint "
  我们的目标是证明 `Nat.gcd (c - b) (c + b) = 2`。

  首先，让我们设 `d = Nat.gcd (c - b) (c + b)`。
  根据最大公约数的定义，`d` 必须整除 `(c - b)` 和 `(c + b)`。"
  let d := Nat.gcd (c - b) (c + b)
  have h_d_div_sub : d ∣ c - b := Nat.gcd_dvd_left (c - b) (c + b)
  have h_d_div_add : d ∣ c + b := Nat.gcd_dvd_right (c - b) (c + b)
  Hint "
  如果 `d` 整除两个数，那么它也整除这两个数的和与差。

  和: `(c + b) + (c - b) = 2 * c`
  差: `(c + b) - (c - b) = 2 * b`

  让我们来证明 `d` 整除 `2 * c` 和 `2 * b`。"
  have h_b_le_c : b ≤ c := by
    have h_b2_le_c2 : b^2 ≤ c^2 := by rw [← h_pyth]; exact Nat.le_add_left _ _
    by_contra h_not_le
    have h_c_lt_b : c < b := Nat.lt_of_not_ge h_not_le
    have h_c2_lt_b2 : c^2 < b^2 := pow_lt_pow_left h_c_lt_b (by norm_num) (show 2≠0 by norm_num)
    linarith [h_b2_le_c2, h_c2_lt_b2]
  have h_d_div_2c : d ∣ 2 * c := by
    have h_d_div_sum : d ∣ (c - b) + (c + b) := Nat.dvd_add h_d_div_sub h_d_div_add
    rw [Nat.add_comm (c - b), Nat.add_assoc, Nat.add_sub_cancel' h_b_le_c, ← Nat.two_mul] at h_d_div_sum
    exact h_d_div_sum
  have h_d_div_2b : d ∣ 2 * b := by
    have h_d_div_diff : d ∣ (c + b) - (c - b) := Nat.dvd_sub' h_d_div_add h_d_div_sub
    rw [Nat.add_sub_sub_cancel h_b_le_c,← Nat.two_mul] at h_d_div_diff
    exact h_d_div_diff
  Hint "
  现在我们知道 `d` 整除 `2*b` 和 `2*c`。这意味着 `d` 是 `2*b` 和 `2*c` 的公约数，所以它必须整除它们的最大公约数 `Nat.gcd (2 * b) (2 * c)`。"
  have h_d_div_gcd_2bc : d ∣ Nat.gcd (2 * b) (2 * c) := Nat.dvd_gcd h_d_div_2b h_d_div_2c
  Hint "
  接下来，我们需要化简 `Nat.gcd (2 * b) (2 * c)`。
  利用 `Nat.gcd_mul_left` 定理，我们可以提出公因数2。

  已知 `b` 和 `c` 互质 (`h_coprime`)，所以 `Nat.gcd b c = 1`。

  `have h_gcd_is_2 : Nat.gcd (2 * b) (2 * c) = 2 := by ...`"
  have h_gcd_is_2 : Nat.gcd (2 * b) (2 * c) = 2 := by
    rw [Nat.gcd_mul_left, h_coprime.gcd_eq_one, mul_one]
  have h_d_div_2 : d ∣ 2 := by rwa [h_gcd_is_2] at h_d_div_gcd_2bc
  Hint "
  太棒了！我们证明了 `d` 整除 2。这意味着 `d` 只可能是 1 或 2。

  现在，我们还需要证明 2 也整除 `d`。
  为此，我们只需证明 `c - b` 和 `c + b` 都是偶数，即都能被2整除。"
  have h_2_div_d : 2 ∣ d := by
    have h_sub_mod_2 : (c - b) % 2 = 0 := by
      sorry
    have h_add_mod_2 : (c + b) % 2 = 0 := by
      sorry
    have h_2_div_sub : 2 ∣ c - b := Nat.dvd_of_mod_eq_zero h_sub_mod_2
    have h_2_div_add : 2 ∣ c + b := Nat.dvd_of_mod_eq_zero h_add_mod_2
    exact Nat.dvd_gcd h_2_div_sub h_2_div_add
  Hint "
  最后一步！
  我们已经证明了 `d ∣ 2` 和 `2 ∣ d`。
  根据整除的反对称性，这只能意味着 `d = 2`。

  使用 `exact Nat.dvd_antisymm ...`"
  exact Nat.dvd_antisymm h_d_div_2 h_2_div_d

Conclusion "
无懈可击的证明！

你已经完成了第二大关中最困难的一步。我们现在知道了 `a² = (c - b) * (c + b)`，并且 `c - b` 和 `c + b` 的最大公因数是 2。

这意味着 `(c-b)/2` 和 `(c+b)/2` 是互质的！它们的乘积是 `a²/4 = (a/2)²`，一个完美的平方数。

是时候进入最后一关，召唤“平方分裂护符”，推导出最终的通解公式了！
"
