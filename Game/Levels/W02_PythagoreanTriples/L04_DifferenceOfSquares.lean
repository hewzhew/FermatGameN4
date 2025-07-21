import Game.Metadata
import Mathlib.Data.Nat.Parity -- 导入 Even/Odd 的定义
import Mathlib.Tactic.Ring -- 导入 ring 策略
import Game.Levels.W02_PythagoreanTriples.L03_Substitution -- 导入上一关

World "W02_PythagoreanTriples"
Level 4

Title "平方差公式"

Introduction
"
在上一关，我们确定了本原勾股数组 `(a, b, c)` 中 `a` 是偶数，而 `b` 和 `c` 都是奇数。

现在，让我们对 `a² + b² = c²` 这个核心等式进行一次巧妙的变形。我们的目标是孤立偶数项 `a²`，看看能发现什么。
"

Statement (a b c : Nat) (h_pyth : a^2 + b^2 = c^2) : a^2 = (c - b) * (c + b) := by
  Hint "
  我们的目标是证明 `a^2 = (c - b) * (c + b)`。

  我们将从等式的右边开始，利用著名的平方差公式 `c^2 - b^2 = (c + b) * (c - b)` 来进行重写。

  请注意，我们目标中的乘法顺序是 `(c - b) * (c + b)`，而定理 `Nat.sq_sub_sq` 中的是 `(c + b) * (c - b)`。
  为了让 `rw` 能够匹配，我们首先需要使用乘法交换律 `mul_comm` 来交换目标中乘法的顺序。

  使用 `rw [mul_comm]`。"
  rw [mul_comm]
  Hint "
  很好！目标现在是 `a^2 = (c + b) * (c - b)`，这与平方差公式的结构完全匹配了。

  现在使用 `rw [←Nat.sq_sub_sq]`。"
  rw [←Nat.sq_sub_sq]
  Hint "
  太棒了！目标变成了 `a^2 = c^2 - b^2`。

  这个等式可以通过移项从 `a^2 + b^2 = c^2` 得到。

  让我们使用 `rw [←h_pyth]`，将 `c^2` 替换为 `a^2 + b^2`。"
  rw [←h_pyth]
  Hint "
  目标现在是 `a^2 = a^2 + b^2 - b^2`。

  根据自然数的减法性质，`x + y - y = x`。

  使用 `rw [Nat.add_sub_cancel]` 来完成最后的证明。"
  rw [Nat.add_sub_cancel]

Conclusion "
非常漂亮！

你已经成功地将加法关系 `a² + b² = c²` 转化为了一个关于乘法的关系 `a² = (c - b) * (c + b)`。

这个看似简单的变形是解开整个谜题的钥匙。它告诉我们，`a²` 这个平方数可以被分解为两个因数 `(c - b)` 和 `(c + b)` 的乘积。

在下一关，我们将深入研究这两个因数的性质，特别是它们的互质性。
"
