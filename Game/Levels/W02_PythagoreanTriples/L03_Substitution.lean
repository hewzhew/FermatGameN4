import Game.Metadata
import Mathlib.Data.Nat.Parity -- 导入 Even/Odd 的定义
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Game.Levels.W02_PythagoreanTriples.L02_ParityAnalysis -- 导入上一关

World "W02_PythagoreanTriples"
Level 3

Title "代换与简化"

Introduction
"
在上一关，我们成功证明了对于一个本原勾股数组 `(a, b, c)`，`a` 和 `b` 必然一奇一偶。

现在，我们可以不失一般性地**假设 `a` 是偶数，`b` 是奇数**。（因为如果 `a` 是奇数 `b` 是偶数，我们只需交换它们的位置即可，结论是相同的。）

我们的目标是，将这个奇偶性的信息代入 `a² + b² = c²` 中，看看能得到什么新的线索。
"

Statement (a b c : Nat) (h_pyth : a^2 + b^2 = c^2) (h_a_even : Even a) (h_b_odd : Odd b) : Even (a^2) ∧ Odd (b^2) ∧ Odd (c^2) := by
  Hint "
  在这一关，我们的目标是证明三个关于平方数奇偶性的结论。

  1. `Even (a^2)` (偶数的平方是偶数)
  2. `Odd (b^2)` (奇数的平方是奇数)
  3. `Odd (c^2)` (一个偶数和一个奇数的平方和是奇数)

  让我们用 `constructor` 来逐个解决它们。"
  constructor
  Hint "
  第一个目标 `Even (a^2)`。
  我们已知 `h_a_even : Even a`。利用第一关学到的 `Even_sq_of_even` 定理来证明它。"
  · exact Even_sq_of_even a h_a_even
  Hint "
  很好！现在是第二个目标 `Odd (b^2)`。
  同样，利用 `Odd_sq_of_odd` 定理。"
  · constructor
    · exact Odd_sq_of_odd b h_b_odd
    Hint "
    最后，我们需要证明 `Odd (c^2)`。

    我们知道 `c^2 = a^2 + b^2`。而我们已经知道 `a^2` 是偶数，`b^2` 是奇数。
    一个偶数和一个奇数的和是奇数。

    让我们用 `rw [←h_pyth]` 将目标替换为 `Odd (a^2 + b^2)`。"
    · rw [←h_pyth]
      Hint "
      目标是 `Odd (a^2 + b^2)`。

      我们已知 `Even (a^2)` 和 `Odd (b^2)`。让我们把它们的定义展开。"
      have h_a_sq_even := Even_sq_of_even a h_a_even
      have h_b_sq_odd := Odd_sq_of_odd b h_b_odd
      rcases h_a_sq_even with ⟨k, ha2⟩
      rcases h_b_sq_odd with ⟨l, hb2⟩
      rw [ha2, hb2]
      Hint "
      目标 `Odd (2 * k + (2 * l + 1))`。

      我们需要把它整理成 `2 * m + 1` 的形式。
      使用 `use k + l`。"
      use k + l
      Hint "
      最后一步，交给 `ring`！"
      ring

Conclusion "
非常出色！

通过简单的代换，我们不仅再次确认了平方数的奇偶性，还得到了一个至关重要的信息：**`c` 本身也必须是奇数**。

现在我们明确了 `a` 是偶数，`b` 是奇数，`c` 是奇数。在下一关，我们将利用这个信息，进行一次天才般的代数变形——平方差公式！"
