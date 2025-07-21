import Game.Metadata
import Mathlib.Tactic.Basic -- 导入 Mathlib 的基础策略库，其中包含了 by_contra

World "W01_Foundation"
Level 4

Title "反证法 (Proof by Contradiction)"

Introduction
"
欢迎来到第一世界的最终挑战！你将学习一种威力无穷的证明技巧：**反证法**。

反证法的思想非常优美：
1.  要证明一个命题 `P` 是真的。
2.  我们先**假设 `P` 是假的** (即 `¬P` 成立)。
3.  从这个“错误的”假设出发，进行一系列逻辑推理，最终导出一个**荒谬的、自相矛盾**的结论 (在 Lean 中，这个终极矛盾被称为 `False`)。
4.  既然一个错误的假设导出了一个荒谬的结果，那就说明我们最初的假设一定是错的。因此，`P` 必须为真！

在 Lean 中，`by_contra h` 策略就是为此而生。它会帮你假设一个 `h : ¬P`，并把你的目标直接变成 `False`。
"

Statement (x : Nat) (h_x_neq_0 : x ≠ 0) : x + 1 ≠ 1 := by
  Hint "
  我们的目标是证明 `x + 1 ≠ 1`。

  让我们用反证法来证明它。请在下方输入 `by_contra h_contra`，这会引入一个假设 `h_contra`，它是我们目标的否定，即 `¬(x + 1 ≠ 1)`。"
  by_contra h_contra
  Hint "
  太棒了！你的目标现在是 `False`，并且你获得了一个新假设 `h_contra : ¬(x + 1 ≠ 1)`。

  一个“非不等于”就是“等于”。所以 `h_contra` 实际上就意味着 `x + 1 = 1`。

  现在，我们已知 `x + 1 = 1`，我们可以从中推断出 `x = 0`。Lean 有一个定理叫 `Nat.add_right_cancel` 可以帮我们做到这一点。

  使用 `have h_x_is_0 : x = 0 := Nat.add_right_cancel h_contra` 来得到这个新事实。"
  have h_x_is_0 : x = 0 := Nat.add_right_cancel h_contra
  Hint "
  现在，请仔细审视你的已知条件！你同时拥有：

  1. `h_x_neq_0 : x ≠ 0` (即 `x = 0 → False`)
  2. `h_x_is_0 : x = 0`

  这显然是一个尖锐的矛盾。`h_x_neq_0` 就像一个函数，你只要给它一个 `x=0` 的证明（也就是 `h_x_is_0`），它就能产出 `False`——这正是我们当前的目标！

  使用 `exact h_x_neq_0 h_x_is_0` 来引爆这个矛盾，完成证明！"
  exact h_x_neq_0 h_x_is_0

Conclusion
"
完美！你已经成功地运用了反证法，并完成了第一大关的所有挑战！

`by_contra` 是一个极其强大的策略。在未来的旅程中，当你面对一个看似显然，却又不知如何正面下手的难题时，不妨试试反证法，或许就能柳暗花明。

恭喜你完成了基础训练！现在，你已经解锁了通往更广阔数学世界的道路。
"

/- Use these commands to add items to the game's inventory. -/

NewTactic by_contra
NewDefinition False
