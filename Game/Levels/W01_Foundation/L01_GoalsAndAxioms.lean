import Game.Metadata

World "W01_Foundation"
Level 1

Title "目标与公理 (Goals and Axioms)"

Introduction
"
欢迎来到 Lean 的世界，证明者！

在你的屏幕右侧，你会看到一个 **目标 (Goal)**。你的任务就是运用逻辑和策略，向 Lean 证明这个目标是真的。

目前的目标是：
```
⊢ 2 + 2 = 4
```
这里的 `⊢` 符号读作“证明目标”(turnstile)。它左边是你的已知条件（现在是空的），右边是需要你证明的结论。

让我们从最简单的策略开始吧！
"

Statement :(2 + 2 = 4) := by
  Hint "当目标 `⊢ P` 中的 `P` 在计算上为真时（例如 `2+2` 的计算结果就是 `4`），你可以使用 `rfl` (reflexivity, 反身性) 策略来完成证明。请在下方代码框中输入 `rfl` 并点击“执行”。"
  rfl

Conclusion
"
太棒了！你已经完成了你的第一个证明！

你刚刚学会了 Lean 中最基础也是最重要的策略之一：`rfl`。它用于证明那些“不言自明”的等式。

让我们进入下一关，学习更多强大的策略吧！
"

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
NewDefinition Nat Add Eq
