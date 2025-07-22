import GameServer.Commands

-- ========================================================================== --
--  1. 导入所有世界 (Import all Worlds)
-- ========================================================================== --

import Game.Levels.W01_Foundation
import Game.Levels.W02_PythagoreanTriples
import Game.Levels.W03_NumberTheoryArmory
import Game.Levels.W04_InfiniteDescent
import Game.Levels.W05_ConqueringFermat


-- ========================================================================== --
--  2. 游戏主屏幕信息 (Game Title Screen Information)
-- ========================================================================== --

Title "费马大定理：n=4的陨落"

Introduction
"
欢迎来到 Lean 的世界，证明者！

在这场史诗般的旅程中，你将不仅仅是学习一门新的语言，更是要亲手重现数学史上最璀璨的明珠之一——费马大定理（n=4情况）的证明。

我们将从 Lean 的最基本操作开始，一步步为你装备强大的数论工具和逻辑策略。你将揭开勾股数的秘密，掌握“无限下降法”这门古老的证明艺术，并最终集结所有智慧，向费马的终极挑战发起冲击。

准备好了吗？让我们开始铸造你的第一个证明吧！
"

Info "
### 游戏信息

* **游戏名称:** 费马大定理：n=4的陨落
* **版本:** 0.1
* **学习目标:**
    * 掌握 Lean 4 的基本证明技巧。
    * 理解勾股数的通解公式推导。
    * 掌握“无限下降法”的证明思想。
    * 独立完成费马大定理 n=4 情况的完整形式化证明。
* **致谢:**
    * 本游戏的证明思路基于历史上众多数学家的伟大工作。
    * 游戏框架由 `lean4game` 社区提供。
* **项目仓库:** [FermatGameN4 on GitHub](https://github.com/你的用户名/FermatGameN4)
"


-- ========================================================================== --
--  3. 服务器着陆页信息 (Server Landing Page Information)
-- ========================================================================== --

Languages "English, Chinese"
CaptionShort "费马大定理 n=4 证明"
CaptionLong "一个引导式的 Lean 教程游戏，带领玩家从零开始，逐步完成费马大定理 n=4 情况的形式化证明。"
-- CoverImage "images/cover.png" -- 准备好封面图片后，再取消这行的注释


-- ========================================================================== --
--  4. 设置世界依赖关系 (Set World Dependencies)
--  【已修正】将依赖关系简化为一条清晰的线性路径，以避免引擎bug。
-- ========================================================================== --

Dependency W01_Foundation → W02_PythagoreanTriples
Dependency W02_PythagoreanTriples → W03_NumberTheoryArmory
Dependency W03_NumberTheoryArmory → W04_InfiniteDescent
Dependency W04_InfiniteDescent → W05_ConqueringFermat


-- ========================================================================== --
--  5. 构建游戏 (Build the Game)
-- ========================================================================== --

MakeGame
