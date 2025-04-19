import Mathlib.Tactic

/-
这份教程将为你提供一份Lean语言的基本介绍，Lean语言是一门形式化语言，使用这一语言让人们可以把数学内容--包括各种定义与定理（以及定理的证明），“翻译”成为计算机语言。对我来说，学习Lean的过程更像是在学习一门语言而不是一项计算机技术，你需要通过了解更多“词汇”以及“语法”来把你在数学世界中所看到的一切“翻译”出来，更具体地说，我们在数学中遇到的内容，往往由一些定义以及一些定理组成，我们将会逐步学习与这些内容相对应的Lean语法。

我们的计划大致分成三部分：
第一部分中我们将让你能够初步认识并且使用Lean语言，在这部分中你会了解到：一.如何使用Lean给出一个数学定义或者一个数学定理的陈述部分的形式化，这是相对简单的部分，因为它们往往具有固定的格式以及重复的关键词，你只需要阅读少数的例子就可以掌握；二.如何使用Lean语言来完成一些简单的证明，这是相对困难的部分，因为Lean中有大量的“词汇”（官方的说法是tactic）来完成各种各样的证明，在这一部分中，我们将介绍那些使用得最为频繁，并且也是最为简单的tactic，使用它们你已经可以完成一些证明；三.这一部分的最后一个内容是一些与Lean相关的资源，包括Lean的定理搜索工具，以及Lean的社区，我们将介绍一些为你的形式化工作带来方便的资源。在学完这一部分之后，你应该已经能够粗略地读懂Lean的代码，并且独立完成一些简单的定理陈述与证明了。
第二部分中我们将介绍更多的tactic，其中一些tactic出现的频率同样很高，在一些特殊的情况下使用它们是必要的或者是能够节省大量时间的。另外一些则是一些“自动证明器”，使用它们可以在很多情况下省去大量的功夫。在学完这一部分之后，你应该可以完成大部分的数学内容的形式化工作了。（如果你在数学上已经理解了！）
第三部分我们将逐次少量地介绍更多更“高级”的tactic，它们的使用频率不如在这之前你学到的那些，并且在使用上也更为复杂，然而熟练地掌握并使用这些tactic能够帮助你更轻松地完成绝大部分的工作。在学习完这一部分后，你应该已经初步掌握Lean语言了。

我们的侧重点是Lean的使用，因此我们会介绍更多的tactic，而忽略一些原理性的讲述。这份教程不需要任何的前置知识，就算你认为自己的数学水平还相对较低，也没有任何计算机基础，也可以放心读下去。希望这份教程能够为你带来一些帮助：）

在正式开始所有内容之前，让我们回顾一些目前我们需要使用到的简单的类型论知识。目前来说，你需要记住的全部事情是：任何东西都有类型！让我们看几个简单的例子：
-/

#check 1
#check (1 : ℝ)
#check √2
#check 2 + 2
#check 2 + 2 = 4
#check mul_comm

/-
运行这段代码，你会看到Lean代码的操作界面分为两个部分，其中左边是代码的写作区，而右边是infoview的部分，代码运行的各种结果会展示在这一部分。注意到，代码中出现了第一个我们没有见过的内容“#check”，它的作用是检查任何内容的类型，如你所见，你只需要把你想要检查的内容写在“#check”后面即可，点击对应的位置，你可以在Lean语言的infoview部分看到元素的类型，在第一个例子中，你会看到这样的输出“1 : ℕ”，这代表你所检查的数字1的类型是自然数，Lean中的类型总是以这样的格式展示出来，以“:”分隔，之前是内容，之后是内容的类型。第二个例子中，我们同样检查数字1的类型，但我们按照上述格式，将1声明成类型“ℝ”，于是得到输出“1 : ℝ”。第三个例子中，我们检查了√2的类型，得到了“√2 : ℝ”。第四个例子中，我们检查了一个加法表达式的类型，它的类型仍然是“ℕ”。第五个例子中，我们检查一个等式的类型，得到“2 + 2 = 4 : Prop”，意味着“2 + 2 = 4”的类型是一个命题。第六个例子中，我们检查了“mul_comm”的类型，这是Lean中已经定义的乘法交换律的名字，我们在infoview中看到“a * b = b * a”，这是乘法交换律的结论。你暂时还不需要完全理解为什么我们要将定理的类型给定成定理的结论，但这是一件方便的事情，因为如果你不了解一个定理的具体内容，你总是可以#check它来得到有关的信息。

下面我们看一个完整的Lean形式化的定理的例子，在我们做出解释之前，希望你能先运行并观察一下这段代码，尝试尽可能多地理解其中你能理解的部分，并且尽可能多地找到你不能理解的部分，你可以点击代码中的不同位置，观察infoview的内容，来获得更多信息：
-/

theorem The_frist_example {G : Type*} [Group G] {a b c d e f : G} (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  apply mul_assoc c d f

/-
我们逐步观察这段代码，首先是一个关键词“theorem”，这说明我们将要给出一个定理的陈述，接下来是“the_first_example”，这是我们给这个定理的命名，再之后直到“a * (b * e) = c * (d * f)”之前，是这个定理的所需要的参数，以及假设，或许你发现了在这一段内容里，同时出现了花括号，方括号和圆括号，我们会在之后解释它们分别具有什么含义，之后是“:”作为分隔，“:”后是我们希望证明的结论“a * (b * e) = c * (d * f)”，之后由“:= by”说明我们已经完成了定理的陈述，将开始证明这个定理。在证明的部分，你可以点击不同的位置来观察infoview的结果，你会发现，在定理的证明过程中，infoview总会给出当前所有的参数与假设，以及需要证明的目标，而随着证明的过程，你会发现目标在逐步改变，直到“No goals”代表证明完全完成。

第一个例子给出了一个完整的定理陈述与证明，现在我们已经知道，我们可以按照这样的格式来完成各种定理的陈述与证明，下面我们将逐步介绍各个部分具体应该怎样实现：
-/

theorem /-name-/The_frist_example' /-parameters-/{G : Type*} [Group G] (a b c d e f : G) (h : a * b = c * d) (h' : e = f) : /-goal-/a * (b * e) = c * (d * f) := by/-proof-/
  rw [h']
  rw [← mul_assoc]
  rw [h]
  apply mul_assoc

/-
首先我们看证明部分，出现了两个tactic：“rw”和“apply”。“rw”是“rewrite”的缩写，它的格式是“rw [...]”或者你也可以使用逗号分隔填入的多个内容“rw [..., ..., ...]”，它的作用是依据方括号内填写的内容，来改写当前的目标，具体来说，你可以在方括号内填写一些结论是等式的定理，或者如你在例子中看到的，结论是等式的假设，rw会在当前目标中寻找与等式左边相匹配的内容，将其替换为等式右边的内容。或者，你可以填写类似等式的内容，在一些情况下“rw”也能完成转换，一个例子是填写一个当且仅当的命题，“rw”会将与当且仅当左边的内容一致的目标转换为与当且仅当右边内容一致的目标。

“apply”的格式是“apply ...”，它的作用是使用一个定理来证明当前的目标，如果定理的结论是你所需要证明的结论，则完成这个证明。一个功能非常类似的tactic是“exact”，区别是后者只能在能够在一步之内完成定理证明时使用。

需要额外解释的是，在第一个例子中，“apply”使用定理后填入了参数c，d，f，而第二次例子中则没有填入任何参数，两个例子都能够正常地运行。这是因为，我们已经注意到，在Lean中，陈述一个定理时，需要首先给出一系列的参数，再给出这个定理的结论。这像是数学定理需要先给出一系列的假设，再给出条件。因此在使用定理时，也需要首先给出这些参数，才能得到定理的结论。我们会在后续更精确地解释这件事。而在第二个例子中，没有填入参数的情况下，Lean会尝试自动推断这些参数的内容，如果能够成功推断，则完成证明，如果未能成功推断，则Lean会将这些参数作为新的目标。

下面我们将进一步讲解关于参数的问题，先看一个简单的例子：
-/

theorem my_lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans
  apply h1
  apply h2


theorem rewrite {a b c d : ℝ} (h1 : a = c) (h2 : b = d) : a * b = c * d := by
  rw [h1]
  rw [h2]

/-
注意到在这个定理的陈述中出现了花括号和圆括号，它们都给出了这个定理所需要的一些参数，区别在于，由花括号括起来的内容称为隐式参数，而由圆括号括起来的内容，称为显式参数，所谓隐式参数，是指那些在使用定理时不需要填入（也不能够填入），而是由Lean自行推断的参数，而显示参数则是那些在使用定理时需要填入的参数，注意如前面一个例子所展示的，显式参数在一些情况下也可以不填入，而交给Lean自动推断。在例子中，由于h1和h2中已经包含了a，b，c的信息，所以我们可以将a，b，c设置为隐式参数。在这样的设置下，Lean中的定理成为一个由它的参数和结论共同构成的推理链，例如，例子中的定理可以看成是“h1 → h2 → a < c”这样一个链，而填入一个参数后，例如填入h1后，它会变成“h2 → a < c”。

而在一些特殊情况下，我们想要填入隐式参数的值，这时候需要使用“（参数名 := 参数）”的格式来填入，或者我们想要忽略一些参数，先填写位于它后面的参数，这时候可以使用“_” 或 “?_”作为占位符。在下面两个例子中，我们展示了这种写法。
-/

theorem my_lt_trans' {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans (b := b)
  apply h1
  apply h2

theorem my_lt_trans'' {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans ?_ h2
  apply h1

/-
现在我们已经了解了关于定理陈述部分的显式参数和隐式参数，它们分别对应于圆括号和花括号，在之前的例子中还使用了一种方括号，下面我们将解释它的含义。

首先我们介绍两个关键词：structure 和 class，它们的意义是将一些信息打包起来，它们的作用是给出一些需要多个参数或者多个条件来描述的数学定义，下面我们看一些例子：
-/

structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

/-
最简单的例子是使用structure来给出一个三维实空间中点的定义，它由它的三个坐标值来给出，注意structure的写法格式，“x，y，z”是我们给三个坐标值的名称，你可以尝试任意改动这三个名称，而它们的类型我们要求是实数，下一个例子是线性函数：
-/

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

/-
在这个例子中我们给定了一个参数，它是一个实数集到实数集的映射，这个structure描述了这个映射是线性需要满足的两个条件，“is_additive”和“preserves_mul”是我们给这两个条件的名称。它们的类型要求是一个命题，分别是线性性的其中一个条件。同样地，我们也可以用class关键词来打包这些信息，它们的用法是类似的：
-/

class IsLinear' (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

/-
区别在于，使用class来打包的信息，可以使用关键词instance来给出例子，比如，我们使用关键词fun来给出一个函数，并使用instance来说明它是线性的：
-/

instance : IsLinear' (fun x => x) where
  is_additive := by
    intro x y
    rfl
  preserves_mul := by
    intro x c
    rfl

/-
上一个例子说明了单位映射是一个线性映射，证明中的细节将留到后续说明。而使用方括号相当于要求满足一个class中的信息，我们可以使用点“.”来使用这些信息，例如：
-/

theorem linear_fun (f : ℝ → ℝ) [IsLinear' f] : ∀ x c, f (c * x) = c * f x := by
  exact IsLinear'.preserves_mul

/-
至此，我们对于Lean中定理的陈述部分已经较为熟悉，请大家再次回顾一下我们所介绍的内容，包括定理陈述的格式，以及三种括号的意义以及使用方法。

下面我们介绍一个新的关键词，用来给出数学定义：
-/
def f : ℝ → ℝ := (fun x => x)

/-
使用“def”可以给出一些数学定义，例如上面的例子给出了一个函数的定义，请大家自行总结“def”的写法格式。

下面我们进入定理的证明部分，介绍更多的tactic：
-/

example {a b : ℝ} : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

/-
这是一个简单的例子，但是其中出现了一个此前没有出现过的符号“←”，它的含义是在“rw”使用一个等式时，将等式的左右两端调换过来，也就是说，原本“rw”的作用是，在目标中寻找与等式左边相匹配的内容，用等式右边进行替代，而现在则是在目标中寻找与等式右边相匹配的内容，使用等式左边来替代。
-/

section a

variable (a b c d e f : ℝ)

example (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

example : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

end a
/-
在上面两个例子中，出现了一些新的关键词和两个新的tactic，我们逐一进行说明，首先，第一个关键词variable的作用是将原本需要写在定理陈述中的参数提前写出来，这些参数会对variable后的所有函数起作用，它的常用使用方法是与section和end一起用，一个section...end的部分会划定一个区域，在这个区域中给出的variable只会影响end之前的内容，而不会影响end之后的内容，variable的具体作用细节较为复杂，我们将留到后续部分进行讲解。

在第一个例子中，出现了一个新的tactic：“nth_rw”它是“rw”的一种变体，它的作用是更改目标中与给定等式相匹配的第n项，例如，例子中改变了目标中的第二个“a + b”，根据“h”使用“c”来替代它。这适用于我们只想改变目标中的特定位置时使用。

第二个例子中，出现了另一个新的tactic：“have”，它的作用是暂时改变目标先证明一个引理，在例子中，我们不太方便直接证明目标，所以我们使用“have”来先证明引理“h”，它的格式是“have 名称 : 内容 := by 证明”，事实上，“have”并不是一个tactic，而是一个关键词，但在这里我们还没有给出这两件事情的定义，我们将在后面的部分中对这些内容进行更进一步地解释。

下面将展示更多的例子介绍一些用来处理简单逻辑学命题的tactic，在进行讲解之前，希望你能自己阅读这些例子，并且使用鼠标检查各个部分：
-/

variable {x y : ℝ}

example (h₀ : x ≤ y) (h₁ : x ≠ y) : x ≤ y ∧ x ≠ y := by
  constructor
  · apply h₀
  · apply h₁

example (h : (y > 0) ∧ (y < 8)) : y > 0 ∨ y < -1 := by
  left
  apply h.left

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := by
  intro a b hab
  apply h
  apply hab

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 3
  constructor
  · norm_num
  · norm_num

example (h : x < 0) : ¬ 0 ≤ x := by
  push_neg
  apply h

/-
前两个例子关于且命题和或命题，且命题可以使用“constructor”将它们分成两个目标来证明，或命题可以使用“left”或“right”来选择一边进行证明。

后两个例子是关于全称量词和存在量词，出现全称量词的命题，可以使用“intro”，来把“任取”部分的内容转化成参数，“intro”后的内容为按顺序给这些参数的命名，注意到，“intro”也会把“→”之前的部分转化成参数，出现存在量词的命题，可以使用“use”来实际给出一个例子。

最后一个例子是关于否命题，可以使用“push_neg”来把一个命题的否定转化为它的否命题。

下面使用一些例子介绍这些逻辑命题出现在条件中时的处理方法：
-/
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  apply lt_of_le_of_ne
  apply h.left
  apply h.right

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  rcases h with ⟨h1, h2⟩
  apply lt_of_le_of_ne
  apply h1
  apply h2

example {x : ℝ} (h : x = 3 ∨ x = 5) : x = 3 ∨ x = 5 := by
  rcases h with h | h
  · left
    apply h
  · right
    apply h

example {x : ℝ} (h : ¬ 0 ≤ x) : x < 0 := by
  push_neg at h
  exact h

/-
在第一个例子中，我们使用了且命题中的两个部分，只需要使用“.left”与“.right”的写法就可以使用一个且命题的左半部分与右半部分。更为简单的写法是“.1”与“.2”，类似地，带有“↔”的命题也可以使用“.1”与“.2”来获取“→”与“←”的命题。

在第二个例子中，我们展示了另一种使用且命题的方式，使用“rcases...with ⟨..., ...⟩”的方法来拆分且命题，而第三个命题中我们类似地展示了使用“rcases...with ... | ...”的方法也可以拆分或命题。

最后一个例子中，我们使用了“push_neg at”的写法，在假设“h”处做出了转换，实际上“at”不仅可以接在“push_neg”后使用，它可以应用在很多的tactic后，对一些假设做出转换，我们学过的“rw”和“apply”，都可以衔接“at”来使用。

最后我们简单介绍一些能够自动完成证明的tactic，下面是一些例子：
-/

variable (a b c d : ℝ)

example : a - b = a + -b :=
  rfl

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring

example : c * b * a = b * (a * c) := by
  ring

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

/-
这里使用了三个tactic，第一个是“rfl”，它能够解决等式的问题，如果等式两侧基本相等，“rfl”可以结束证明，第二个是“ring”，它能够解决一些简单的关于加法，减法和乘法的运算问题，最后一个是linarith，它能够解决简单的不等式问题。

另一个能够自动完成证明的tactic是“simp”，这里没有放任何例子来介绍它的功能，这是因为它的功能十分强大，可以在很多情况下完成对问题的简化，这些情况很难用一些例子或者一些解释来概括，比如上面的所有问题都可以使用“simp”来直接解决，你可以在各种问题中尝试使用“simp”，来总结它的使用方法。
-/

/-
讲解的例题：
-/
example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by sorry--apply

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by sorry

example {a b c : ℝ} (h : a + b = c + b) : a = c := by sorry --rw

open Nat Real
example (a b c d e : ℝ) (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]--have

-- example : ∃ x : ℝ, 2 < x ∧ x < 4 := by sorry

-- example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by sorry --constructor

-- variable {α : Type*} [PartialOrder α]
-- variable (s : Set α) (a b : α)

-- def SetUb (s : Set α) (a : α) :=
--   ∀ x, x ∈ s → x ≤ a

-- example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
--   intro x xs
--   apply le_trans (h x xs) h'

-- example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
--   fun x xs ↦ le_trans (h x xs) h'

-- open Function

-- example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
--   intro x₁ x₂ h'
--   apply (mul_right_inj' h).mp h'--任取

-- def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
--   ∀ x, f x ≤ a

-- def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
--   ∀ x, a ≤ f x

-- def FnHasUb (f : ℝ → ℝ) :=
--   ∃ a, FnUb f a

-- def FnHasLb (f : ℝ → ℝ) :=
--   ∃ a, FnLb f a

-- example (f g : ℝ → ℝ) (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
--   rcases lbf with ⟨a, lbfa⟩
--   rcases lbg with ⟨b, lbgb⟩
--   use a + b
--   intro x
--   exact add_le_add (lbfa x) (lbgb x)

-- example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
--   rcases ubf with ⟨a, ubfa⟩
--   use c * a
--   intro x
--   exact mul_le_mul_of_nonneg_left (ubfa x) h

-- example (a b c : ℤ) (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
--   rcases divab with ⟨d, rfl⟩
--   rcases divbc with ⟨e, rfl⟩
--   use d * e; ring

-- example (a b c : ℤ) (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
--   rcases divab with ⟨d, rfl⟩
--   rcases divac with ⟨e, rfl⟩
--   use d + e; ring--存在命题

-- example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
--   push_neg at h
--   exact h--否定

/-
下面是本节练习题：
-/

/-
1. 陈述并证明1 + 1 = 2
2. 陈述并证明实数x ≤ y, y ≤ z 则x ≤ z
2. 陈述并证明完全平方公式
3. 陈述并证明平方差公式
4. 定义实数集上的恒等映射，并说明它是双射
5. 陈述并证明命题p为真，命题q为真，则命题p ∧ q为真
-/

/-
第二段例题
-/
example (x y : ℝ) : x ⊓ y = y ⊓ x := by sorry

example (a b : ℝ) : max a b = max b a := by sorry --apply



/-
第二段练习题
-/
open Nat Real
variable {a b c d e : ℝ}
variable {x y z w : ℤ}

example (a b c : ℕ) : a * b * c = a * (b * c) := by sorry

example (a b : ℝ) (h : a ≤ b ∧ -a ≤ b) : |a| ≤ b := by sorry

example : min a b + c = min (a + c) (b + c) := by sorry

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by sorry

example : x ∣ y * x * z := by sorry

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by sorry

example (a b : ℝ) : min a b = min b a := by sorry

example : min (min a b) c = min a (min b c) := by sorry --apply

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by sorry

example (a b c : ℕ) : a * b * c = b * (a * c) := by sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by sorry

example {a b : ℝ} (h : a + b = 0) : -a = b := by sorry--rw

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by sorry

example {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by sorry

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by sorry

example : min a b + c = min (a + c) (b + c) := by sorry --have

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by sorry

example (a b : ℝ) : a < b ↔ a ≤ b ∧ a ≠ b := by sorry

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by sorry

example (m n k : ℕ) : Nat.lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k := by sorry

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by sorry--constructor
