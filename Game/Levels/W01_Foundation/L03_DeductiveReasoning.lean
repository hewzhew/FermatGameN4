import Game.Metadata

World "W01_Foundation"
Level 3

Title "演绎推理 (Deductive Reasoning)"

Introduction
"
做得好！你已经准备好学习 Lean 中最核心的逻辑推理方式之一了。

正如我们在上一关的介绍中提到的，要证明一个 **“如果 P 则 Q”** (`P → Q`) 的命题，我们通常会假设 `P` 成立，然后在此基础上证明 `Q`。

Lean 通过 `intro` 策略完美地实现了这一点。当你的目标是 `P → Q` 时，执行 `intro h` 会：
1.  将 `P` 作为一个新的假设 `h : P` 添加到你的已知条件中。
2.  将你的证明目标更新为 `Q`。

让我们来亲手实践一下吧！
"

Statement (x : Nat) : x = 2 → x + x = 4 := by
  Hint "
  你当前的目标是 `x = 2 → x + x = 4`。这是一个蕴含式。

  请在下面的代码框中输入 `intro hx`，然后点击“执行”，看看你的目标和已知条件会发生什么变化。"
  intro hx
  Hint "
  看到了吗？`intro hx` 就像施展了魔法：

  1.  `x = 2` 不再是目标的一部分，而是变成了你的一个已知条件 `hx : x = 2`。
  2.  你的新目标简化为了 `x + x = 4`。

  现在的情况和你上一关的处境一模一样。使用你已经掌握的 `rw` 策略来完成最后的证明吧！"
  rw [hx]

Conclusion
"
太精彩了！

你已经掌握了证明蕴含命题的核心方法：`intro`。这个策略是你工具箱里最重要的工具之一，它能帮你把复杂的问题分解成“假设”和“新目标”这样更小的部分。

在下一关，我们将面对一个更具挑战性的逻辑谜题：反证法。
"

/- Use these commands to add items to the game's inventory. -/

NewTactic intro
NewDefinition Nat
