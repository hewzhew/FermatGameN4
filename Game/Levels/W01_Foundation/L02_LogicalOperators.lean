import Game.Metadata

World "W01_Foundation"
Level 2

Title "蕴含与假设 (Implication and Hypotheses)"

Introduction
"
在上一关中，我们证明了一个简单的等式。现在，让我们来处理更复杂的逻辑结构！

在数学中，我们经常需要证明形如 **“如果 P 成立，那么 Q 也成立”** 的命题。在 Lean 中，这被写作 `P → Q`。

要证明 `P → Q`，标准的做法是：
1.  我们先**假设** `P` 是真的。
2.  在这个假设下，我们推导出 `Q` 也必须是真的。

在 Lean 中，我们使用 `intro` 策略来引入一个假设。
"

Statement (x : Nat) (h_x_is_2 : x = 2) : x + x = 4 := by
  Hint "
  在这一关，你的目标是 `x + x = 4`，并且你有一个已知条件 `h_x_is_2 : x = 2`。

  `rw` 策略非常强大。当你使用 `rw [h_x_is_2]` 时，它不仅会把目标中的 `x` 替换为 `2`，还会自动尝试用 `rfl` 来关闭简化后的目标。

  试试看，只用一步 `rw` 能不能直接解决问题！"
  rw [h_x_is_2]

Conclusion
"
非常出色！一步到位！

你刚刚见识到了 `rw` 策略的强大之处。它在重写之后，会自动进行一次“微不足道的”尝试（比如 `rfl`），这在很多情况下能帮你节省一步操作。

你已经学会了如何利用已知条件来推进证明。在下一关，我们将正式学习如何处理 `P → Q` 形式的目标，并亲自使用 `intro` 策略来创造你自己的假设！
"

/- Use these commands to add items to the game's inventory. -/

NewTactic rw
NewDefinition Nat
