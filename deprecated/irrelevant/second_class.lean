import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
/-
这节课我们的目标有两个，一是让大家（理论上）能够独立地完成大部分数学内容的形式化工作，二是让大家学习更多的Lean中的类型论知识，以便能够更清楚当我们谈论代码的时候，我们在谈论什么。

关于第一点，真正对数学进行形式化的工作当然还是比较复杂并且比较有些时候比较繁琐的，没有一定的经验积累很难说可以独立地完成相对困难的工作，因此，更精确的说，这节课的目标是教会大家足以形式化大部分数学内容的tactic和它们的基础使用方法，并且展示一些在形式化工作中很有用的资源，最后我们会处理一些相对复杂的题目，并在这个过程中展示形式化工作的大体流程。

而关于第二点，我们会讲解一些理论，但是仍然不会很多，理论的内容我们会在后续的课程中持续地进行补充和深入，但是（至少目前而言）对你来说更为重要的事情不是纠结于这些理论本身，而是使用它们更好地理解你阅读的代码与写作的代码，以便能够更为顺利地理解他人的代码以及写出更简洁和优雅的代码。

最后我想要说明的是，如果你一开始不能理解某一部分理论，没办法把它和实际的代码很好地对应起来，不必担心这件事，因为即使你对这些理论完全没有概念，也可以完成相当一部分的形式化工作，你有很多的时间来一边提高你的实际操作水平，一边完善自己对于理论部分的理解。

首先我们回顾一下对于Lean中的类型论我们的全部知识--“任何东西都有类型！”。以及我们在最开始学习到的工具：“#check”，它能够很方便地帮助我们检查各种东西的类型。我们用形如“1 : ℕ”地形式来表示一个元素的类型，在Lean的类型论中，我们将冒号前的内容称为元素（Term），冒号后的内容称为类型（Type）。我们已经见过一些例子：
-/

#check 1
#check (1 : ℝ)
#check √2
#check 2 + 2
#check 2 + 2 = 4
#check mul_comm

/-
这其中有ℕ，ℝ，Prop等多个类型，那么既然任何东西都有类型，ℕ，ℝ，Prop本身的类型是什么？让我们检查一下：
-/

#check ℕ
#check ℝ
#check Prop

/-
我们得到了它们的类型--“Type”，事实上，这是Lean中绝大部分内容的类型，如果你继续追问：“Type”的类型是什么呢？
-/

#check Type


/-
答案是--“Type 1”！这是一件非常神奇的事情，有点像是罗素提出的那个问题--“包含全部集合的集合存在吗？”，在类型论中同样存在这样的问题，如果我们把类型的类型设置为类型，会导致悖论，我们不打算在这里解释这件事，有兴趣的同学可以自行上网搜索。但总之，人们为了解决这个问题，提出了这样的方案，如果一个东西是类型的类型，那么我们让它升级，变成“Type 1”，而聪明的同学想必已经想到了“Type 1”的类型是“Type 2”，这些东西就这么子子孙孙无穷匮也地增长下去。这种解决方案被称为“宇宙”，诸如“ℕ，ℝ”等以“Type”为类型的类型，为第0层宇宙（universe）（除了Prop），而“Type”则位于第一层宇宙，“Type 1”则更高一层……

但“Prop”在这其中的地位是有些特殊的，因为对于任何的“p : Prop”来说，“p”本身仍然可以构成一个类型，但是对于其他位于第0层宇宙的内容来说，这件事是不成立的，例如“1 : ℕ”，我们完全没有理由设定“1”可以是一个类型。让我们考虑一下这件事，“p : Prop”对于我们来说，意义是“p是一个命题”，此时它可以是真命题或是假命题，这合乎我们对数学的认识，而如果我们继续写“h : p”，这对于我们来说意味着“h假设p成立”（如果你感到疑惑，可以回头看看昨天写过的例子），或者换句话说，这意味着“h是p为真的一个证明”，按后者的方式理解更合乎Lean中类型论的思想。

考虑一些第0层宇宙的内容，比如“ℕ”，“1 : ℕ”对我们来说意味着“1是ℕ的一个元素”，按照上面的想法来解释“1是ℕ的一个证明”似乎是很奇怪的，但我们可以将这理解为“1是ℕ非空的一个证明”。当然，再真正形式化数学内容时，我们将这理解为“1是集合ℕ中的一个元素”也是没有问题的。

在理解了上述内容之后，我们也不难理解在Lean中证明一个定理实际上是需要给出一个对应这个类型的“Term”，在证明中使用的“:=”即意味着“后面的内容定义了一个所需要的Term”，因此，我们可以这样完成一个证明：
-/

theorem add_comm' (a b : ℝ) : a + b = b + a := add_comm a b

/-
你可以使用“#check”来检查“add_comm a b”的类型，会发现这正是我们所需要的内容，如果你感到疑惑，可以回看我们之前提过的定理的类型是它所证明的内容，但这样的写法在有些时候并不方便，例如：
-/

example (a b c d e f : ℝ) (h₁ : b * d = f * e) (h₂ : f * c = 1) : a * b * c * d = a * e :=
    (mul_assoc (a * b) c d).symm ▸ (mul_comm d c) ▸ (mul_assoc (a * b) d c) ▸ (mul_assoc a b d).symm ▸ h₁.symm ▸ (mul_comm e f) ▸ (mul_assoc a e f) ▸ (mul_assoc (a * e) f c).symm ▸ h₂.symm ▸ (mul_one (a * e))

/-
证明中的“▸”可以被理解为“rw”的意思，但是这样书写的代码会有很长的一行，这会导致很难进行思考，也很难进行纠错，使用起来并不方便，于是Lean提供了tactic的写法，可以允许我们在“:=”后添加“by”关键词，来说明后续使用的内容我们会使用tactic进行写作，tactic模式允许我们对目标进行分布转化，直到出现我们想要的形式，这是一种更为方便的写法。当然，在有些情况下，适当使用Term来进行证明会使我们的代码更为简洁。

下面介绍几个新的tactic：
-/

example (P Q R : Prop) (h₁ : P → R) (h₂ : Q) (h₃ : Q → P) : R := by
  suffices h : P from h₁ h
  exact h₃ h₂

example (a b : ℝ) (h : a = b) : a = b := by
  assumption

example (a b c : ℝ) : a + b + c = a + (b + c) := by
  refine add_assoc a b c

example (P Q R : Prop) (h1 : P) (h2 : Q) (h3 : P → R) : Q ∧ R := by
  refine ⟨h2, h3 h1⟩

#help tactic refine

/-
上面的例子中展示了三个新的tactic，下面我们一一介绍：

第一个例子中使用了“suffices”，它的含义是“要证明目标，只需证明h”。此时，需要说明两件事，第一是“如何通过h证明目标”，第二件事是“如何证明h”，因此，“suffices”的使用格式是“suffices 名称（h） : 只需证明的结论 from 如何通过h证明目标 （换行） 如何证明h”，在“from”后的部分，我们需要通过“suffices”提出的假设“h（此处可以自己命名）”，以及原有的假设，来证明目标。在证明完目标后，我们需要通过原有的假设，来证明提出的假设“h”。

第二个例子中使用了“assumption”，它的作用非常简单，使用“assumption”将会搜索假设的列表，如果找到与当前目标相匹配的内容，则完成此证明。另外，tactic“rwa”会在使用完“rw”之后使用一次“assumption”。

第三个例子中使用了“refine”，它的作用类似于我们介绍过的“apply”，事实上，它们也可以在很多情况下转化，区别在于，“refine”在使用定理时，需要提供所有的参数，而没有像“apply”一样的自动推断功能。另外，“refine”的一个非常方便的功能如最后一个例子中所展示的，可以使用“⟨...,...⟩”的格式来直接证明且命题，在尖括号内需要填入对应的两个Term来完成证明，或者，对于较长的证明，你也可以使用“by”关键词来开启tactic模式，这里的尖括号事实上是实现了一个构造函数，这部分内容我们将在后续进一步介绍。

最后我们再介绍一个非常好用的tactic：
-/
open Real

example (x y : ℝ) (h1 : 0 < x) (h2 : 0 < y) (h : log x = log y) : x = y := by
  calc
    _ = exp (log x) := by rw [exp_log h1]
    _ = exp (log y) := by rw [h]
    _ = _ := by rw [exp_log h2]

/-
如例子中所演示的，“calc”的作用是将一个难以在一步之内证明的等式分成多步来完成，其中“_”符号作为占位符，代表了上一个等式的结果，例如，第一行中“_”的位置代表“x”，请注意它的格式和缩进。事实上，“calc”也可以用于证明不等式的结论，使用方法是一样的，只需把证明中的等号改为不等号：
-/

    




/-
我还需要写些什么？：自动证明的内容需要教一些，但最好是拿出几个大题目来展示，包括rw？apply？simp？这些，然后Leansearch，还有community里面的资源。equality也可以再提一嘴。这一天主要准备很多题目来做练习吧。然后如何读代码也需要展示一下。
-/

/-
习题部分：
-/
example (m n : ℕ) (h : ¬m.Coprime n) (nezero : m ≠ 0 ∧ n ≠ 0) : m.primeFactors ∩ n.primeFactors ≠ ∅ := by
  suffices h' : ∃ p, p.Prime ∧ p ∣ n ∧ p ∣ m from by
    rcases h' with ⟨p, hp₁, hp₂, hp₃⟩
    rw [Finset.nonempty_iff_ne_empty.symm, Finset.Nonempty]
    use p
    simp [hp₁, hp₂, hp₃, nezero]
  use (m.gcd n).minFac
  rw [Nat.Coprime] at h
  constructor
  · exact Nat.minFac_prime h
  constructor
  · apply Nat.dvd_trans (b := m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_right m n
  · apply Nat.dvd_trans (b := m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_left m n

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this

open Nat in
example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  have hpp : Nat.Prime p := by
    apply minFac_prime
    apply Nat.ne_of_gt
    apply succ_lt_succ
    apply factorial_pos _
  have hnp : n ≤ p := by
    by_contra hc
    push_neg at hc
    have h1 : p ∣ n ! := by
      simp only [p] at hc
      apply dvd_factorial (minFac_pos _)
      apply le_of_lt hc
    have h2 : p ∣ 1 := by
      apply (Nat.dvd_add_iff_right h1).2
      apply minFac_dvd _
    apply Nat.Prime.not_dvd_one hpp h2
  use p


/-
练习题
-/

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by

example : |a| - |b| ≤ |a - b| := by sorry --calc
