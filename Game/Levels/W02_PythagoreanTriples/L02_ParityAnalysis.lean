import Game.Metadata
import Mathlib.Data.Nat.Parity -- 导入 Even/Odd 的定义
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Mathlib.Tactic.Linarith -- 导入 linarith 策略
import Game.Levels.W02_PythagoreanTriples.L01_EvensAndOdds -- 导入上一关，这样才能使用其中定义的定理

World "W02_PythagoreanTriples"
Level 2

Title "勾股数的奇偶分析"

Introduction
"
在上一关，我们掌握了平方数的奇偶性。现在，是时候将这些知识应用到真正的战场上了：`a² + b² = c²`。

一个“本原”勾股数组指的是 `a`, `b`, `c` 两两互质。这意味着 `a` 和 `b` 不可能都是偶数（否则它们有公因数2）。

那么，`a` 和 `b` 的奇偶性只剩下三种可能：一偶一奇，一奇一偶，或者两奇。

在这一关，我们的目标就是证明：**`a` 和 `b` 不可能同时为奇数**。我们将使用反证法来完成这个证明。
"

-- 为了这一关，我们提供一个有用的引理。
-- `even_iff_even_sq` 指出：一个自然数是偶数，当且仅当它的平方是偶数。
TheoremDoc even_iff_even_sq as "even_iff_even_sq" in "奇偶性"
"
`even_iff_even_sq (n : Nat) : Even n ↔ Even (n ^ 2)` 是一个强大的双向引理。它告诉我们，一个数 `n` 和它的平方 `n^2` 的奇偶性是完全一致的。
"
axiom even_iff_even_sq (n : Nat) : Even n ↔ Even (n ^ 2)

Statement (a b c : Nat) (h_pyth : a^2 + b^2 = c^2) (h_a_odd : Odd a) (h_b_odd : Odd b) : False := by
  Hint "
  我们的目标是 `False`，这强烈暗示了我们要使用反证法。实际上，我们已经身处反证法的逻辑之中了：我们假设了 `a` 和 `b` 都是奇数，并要从中导出一个矛盾。

  首先，根据上一关的结论 `Odd_sq_of_odd`，我们知道 `a^2` 和 `b^2` 也是奇数。
  让我们用 `have` 来声明这两个新事实。"
  have h_a_sq_odd : Odd (a ^ 2) := Odd_sq_of_odd a h_a_odd
  have h_b_sq_odd : Odd (b ^ 2) := Odd_sq_of_odd b h_b_odd
  Hint "
  很好。现在我们知道 `a^2` 和 `b^2` 都是奇数。那么它们的和 `a^2 + b^2` 呢？

  两个奇数的和是偶数。让我们来证明这一点。
  `have h_sum_even : Even (a^2 + b^2) := by ...`"
  have h_sum_even : Even (a^2 + b^2) := by
    rcases h_a_sq_odd with ⟨k, h_a_eq⟩
    rcases h_b_sq_odd with ⟨l, h_b_eq⟩
    rw [h_a_eq, h_b_eq]
    use k + l + 1
    ring
  Hint "
  太棒了！我们证明了 `a^2 + b^2` 是偶数。

  再看看我们的已知条件 `h_pyth : a^2 + b^2 = c^2`。这说明 `c^2` 也是偶数！
  使用 `rw [h_pyth] at h_sum_even` 来更新我们的结论。"
  rw [h_pyth] at h_sum_even
  Hint "
  现在我们有了 `h_c_sq_even : Even (c^2) := h_sum_even`。

  是时候使用我们为你提供的强大引理 `even_iff_even_sq` 了。它告诉我们，如果 `c^2` 是偶数，那么 `c` 本身也必须是偶数。"
  have h_c_even : Even c := by
    rw [even_iff_even_sq]
    exact h_sum_even
  Hint "
  我们离矛盾越来越近了！

  我们已经有了 `a`, `b` 是奇数，`c` 是偶数。让我们把它们的定义展开，并为每个等式命名。"
  rcases h_a_odd with ⟨k, ha⟩
  rcases h_b_odd with ⟨l, hb⟩
  rcases h_c_even with ⟨m, hc⟩
  Hint "
  现在，将这些代入最初的等式 `h_pyth` 中。
  使用 `have h_contra := h_pyth`，然后用 `rw` 把所有变量都替换掉。"
  have h_contra := h_pyth
  rw [ha, hb, hc] at h_contra
  Hint "
  是时候让 `ring` 大显身手了！`ring` 策略可以直接作用于一个假设。
  使用 `ring_nf at h_contra` 来化简这个等式。"
  ring_nf at h_contra
  Hint "
  化简后我们得到 `4 * k ^ 2 + 4 * k + 4 * l ^ 2 + 4 * l + 2 = 4 * m ^ 2`。

  这个等式的左边除以2是奇数，右边除以2是偶数。这是一个矛盾！

  为了让 Lean “看”到这个矛盾，我们可以两边同时除以2。
  `have h_almost_there : 2 * (k ^ 2 + k + l ^ 2 + l) + 1 = 2 * m ^ 2 := by ...`"
  have h_almost_there : 2 * (k ^ 2 + k + l ^ 2 + l) + 1 = 2 * m ^ 2 := by
    -- `linarith` is a powerful tactic for linear arithmetic
    linarith [h_contra]
  Hint "
  `2 * ... + 1 = 2 * ...`

  这告诉我们一个奇数等于一个偶数。这是不可能的！

  有一个非常巧妙的方法来揭示这个矛盾：对等式两边同时进行模2运算。

  使用 `have h_mod_2 := congr_arg (fun n => n % 2) h_almost_there`。"
  have h_mod_2 := congr_arg (fun n => n % 2) h_almost_there
  Hint "
  太棒了！我们得到了一个新的假设 `h_mod_2`。

  Lean 有时会用 `(fun n => n % 2) (...)` 这种函数形式来表示模运算，而不是我们更熟悉的 `(...) % 2`。
  为了让 `rw` 策略能看懂这个表达式，我们先用 `dsimp at h_mod_2` (definitional simplify) 来把它化简成标准形式。"
  dsimp at h_mod_2
  Hint "
  现在 `h_mod_2` 变成了 `(2 * ... + 1) % 2 = (2 * m ^ 2) % 2`。
  我们可以处理等式的左边了。根据模运算的加法法则 (`Nat.add_mod`)，这等于 `((2 * ...) % 2 + 1 % 2) % 2`。

  使用 `rw [Nat.add_mod] at h_mod_2`。"
  rw [Nat.add_mod] at h_mod_2
  Hint "
  很好！现在我们来处理 `(2 * ...) % 2`。任何2的倍数模2都等于0。

  使用 `rw [Nat.mul_mod_right] at h_mod_2` 来化简两边的表达式。"
  rw [Nat.mul_mod_right] at h_mod_2
  Hint "
  `h_mod_2 : (0 + 1) % 2 = 0`

  我们离终点只有一步之遥！`norm_num` 策略非常强大，它不仅能计算出 `(0+1)%2` 的结果是 `1`，还能立刻发现 `1 = 0` 是一个无法成立的矛盾，并直接用它来解决我们的 `False` 目标！

  使用 `norm_num at h_mod_2` 来给予最后一击！"
  norm_num at h_mod_2

Conclusion "
干得漂亮！你通过严谨的推理，证明了 `a` 和 `b` 不可能同时为奇数，成功排除了一个重要的错误情况。

现在我们知道了，对于任何本原勾股数组，`a` 和 `b` 必然一奇一偶。这个结论将是后续推导通解公式的关键。
"
