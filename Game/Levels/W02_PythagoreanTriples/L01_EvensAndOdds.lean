import Game.Metadata
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Mathlib.Data.Nat.Parity
-- 导入 Even 和 Odd 的定义

World "W02_PythagoreanTriples"
Level 1

Title "偶数与奇数 (Evens and Odds)"

Introduction
"
欢迎来到勾股数的世界！在开始探索 `a² + b² = c²` 的奥秘之前，我们需要先掌握一些关于数字奇偶性的基本工具。

在 Lean 中，一个自然数 `n` 是：
* **偶数 (Even)**，如果它能被写作 `2 * k` 的形式，其中 `k` 是某个自然数。
* **奇数 (Odd)**，如果它能被写作 `2 * k + 1` 的形式。

在这一关，我们将证明关于平方数奇偶性的两个重要引理。
"

TheoremDoc Even_sq_of_even as "Even_sq_of_even" in "奇偶性"
"
`Even_sq_of_even (n : Nat) (h_even : Even n) : Even (n ^ 2)` 是一个引理，它证明了如果一个自然数 `n` 是偶数，那么它的平方 `n^2` 也一定是偶数。
"

Statement Even_sq_of_even (n : Nat) (h_even : Even n) : Even (n ^ 2) := by
  Hint "
  我们的目标是证明：如果 `n` 是偶数，那么 `n^2` 也是偶数。

  已知 `h_even : Even n`，这意味着存在一个自然数 `k`，使得 `n = 2 * k`。

  使用 `rcases h_even with ⟨k, rfl⟩` 来分解这个假设。`rfl` 会自动将 `n` 替换为 `2 * k`。"
  rcases h_even with ⟨k, rfl⟩
  Hint "
  很好！现在我们的目标变成了证明 `Even ((2 * k) ^ 2)`。

  根据偶数的定义，我们需要找到一个自然数（称之为 `m`），使得 `(2 * k) ^ 2 = 2 * m`。

  首先，让我们展开 `(2 * k) ^ 2`。强大的 `ring` 策略可以帮我们处理多项式计算。"
  ring
  Hint "
  `ring` 策略已经将目标简化为 `Even (4 * k ^ 2)`。

  现在，我们需要明确地给出一个自然数 `m`，使得 `4 * k ^ 2 = 2 * m`。

  看起来 `m` 应该是 `2 * k ^ 2`。使用 `use 2 * k ^ 2` 来告诉 Lean 你的构造。"
  use 2 * k ^ 2
  Hint "
  最后一步！目标变成了 `4 * k ^ 2 = 2 * (2 * k ^ 2)`。

  这又是一个纯粹的代数计算。再次使用 `ring` 来终结它！"
  ring

NewTheorem Even_sq_of_even

Conclusion
"
漂亮！你证明了偶数的平方仍然是偶数。

现在，让我们用类似的方法来证明奇数的情况。
"

TheoremDoc Odd_sq_of_odd as "Odd_sq_of_odd" in "奇偶性"
"
`Odd_sq_of_odd (n : Nat) (h_odd : Odd n) : Odd (n ^ 2)` 是一个引理，它证明了如果一个自然数 `n` 是奇数，那么它的平方 `n^2` 也一定是奇数。
"

Statement Odd_sq_of_odd (n : Nat) (h_odd : Odd n) : Odd (n ^ 2) := by
  Hint "
  这次，我们的目标是证明奇数的平方仍然是奇数。

  和刚才一样，先用 `rcases h_odd with ⟨k, rfl⟩` 来分解 `Odd n` 的定义。"
  rcases h_odd with ⟨k, rfl⟩
  Hint "
  目标变成了 `Odd ((2 * k + 1) ^ 2)`。

  根据奇数的定义，我们需要找到一个自然数 `m`，使得 `(2 * k + 1) ^ 2 = 2 * m + 1`。

  同样，先用 `ring` 展开左边的表达式。"
  ring
  Hint "
  目标是 `Odd (4 * k ^ 2 + 4 * k + 1)`。

  我们需要把它整理成 `2 * m + 1` 的形式。

  `4 * k ^ 2 + 4 * k` 显然可以提出一个因子2。`m` 应该是什么呢？

  使用 `use 2 * k ^ 2 + 2 * k`。"
  use 2 * k ^ 2 + 2 * k
  Hint "
  最后一步，`ring` 会出手相助。"
  ring

NewTheorem Odd_sq_of_odd

Conclusion
"
完美！你已经掌握了处理奇偶数平方的基本技巧。

这两个看似简单的引理，将是我们在后续关卡中分析勾股数性质的基石。准备好进入下一关，看看它们如何发挥作用吧！
"

/- Use these commands to add items to the game's inventory. -/

NewDefinition Nat.Even Nat.Odd
