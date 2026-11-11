/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Basic norm estimates for right Hilbert C⋆-modules

Right Hilbert `A`-modules are represented with Mathlib's class as `CStarModule Aᵐᵒᵖ E`: the right
action is `x a = MulOpposite.op a • x` and the usual `A`-valued inner product is
`⟨x, y⟩_A = MulOpposite.unop (inner Aᵐᵒᵖ x y)`. This file restates Mathlib's inner-product
identities and Cauchy–Schwarz inequalities in this right-module form, and proves the basic norm
estimates for the right action. The coefficient-valued inner product also separates vectors in
either variable, so identities of module operators can be checked by pairing against arbitrary
vectors, without a scalar-valued Riesz theorem.

The key computation is that `⟨x a, x a⟩_A = (|x| a)⋆ (|x| a)` for the positive square root
`|x| = ⟨x, x⟩_A ^ (1/2)`. Hence `‖x a‖ = ‖|x| a‖ ≤ ‖x‖ ‖a‖`, and likewise
`‖x a - x‖ = ‖|x| a - |x|‖`. The second identity shows that the right action is essential:
`x e → x` along any filter `e` with `b e → b` for every `b ∈ A`, in particular along an
approximate unit of `A`, with no boundedness assumption on the approximate unit.

## Main declarations

* `CStarModule.inner_polarization`: the polarization identity expressing `⟪x, y⟫_A` through the
  inner products `⟪z, z⟫_A`.
* `CStarModule.ext_inner_left`, `CStarModule.ext_inner_right`: vectors are determined by their
  inner products against all vectors.
* `CStarModule.star_unop_inner_mul_unop_inner_le`: the Cauchy–Schwarz inequality
  `⟨x, y⟩_A⋆ ⟨x, y⟩_A ≤ ‖x‖² ⟨y, y⟩_A`.
* `CStarModule.isGreatest_norm_unop_inner`: norm recovery, `‖x‖` is the largest value of
  `‖⟨y, x⟩_A‖` over the closed unit ball.
* `CStarModule.norm_op_smul_le`: `‖x a‖ ≤ ‖x‖ ‖a‖`.
* `CStarModule.tendsto_op_smul`: the right action is essential, `x e → x` along a right
  approximate unit.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite Filter Topology Complex

namespace CStarModule

/-! ### Algebraic identities -/

section Algebraic

variable {A E : Type*}

section Right

variable [NonUnitalSeminormedRing A] [StarRing A] [Module ℂ A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The `A`-valued inner product is conjugate-linear for the right action in its first variable:
`⟨x a, y⟩_A = a⋆ ⟨x, y⟩_A`. -/
lemma unop_inner_op_smul_left (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ (op a • x) y) = star a * unop (inner Aᵐᵒᵖ x y) := by
  simp

/-- The `A`-valued inner product is linear for the right action in its second variable:
`⟨x, y a⟩_A = ⟨x, y⟩_A a`. -/
lemma unop_inner_op_smul_right (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ x (op a • y)) = unop (inner Aᵐᵒᵖ x y) * a := by
  simp

end Right

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- The polarization identity: the `A`-valued inner product, conjugate-linear in its first
variable, is determined by its values `⟪z, z⟫_A` on the diagonal. This holds for either side
convention, in particular for right Hilbert modules `CStarModule Aᵐᵒᵖ E`. -/
lemma inner_polarization (x y : E) :
    inner A x y = (4 : ℂ)⁻¹ • (inner A (x + y) (x + y) - inner A (x - y) (x - y) -
      I • inner A (x + I • y) (x + I • y) + I • inner A (x - I • y) (x - I • y)) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left_complex, inner_smul_right_complex, Complex.star_def, conj_I, smul_add,
    smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
  module

/-- Vectors are determined by their inner products against all vectors in the first slot. -/
theorem ext_inner_left {x y : E} (h : ∀ z, inner A z x = inner A z y) : x = y := by
  apply sub_eq_zero.mp
  apply (inner_self (A := A)).mp
  simp [inner_sub_right, h]

/-- Vectors are determined by their inner products against all vectors in the second slot. -/
theorem ext_inner_right {x y : E} (h : ∀ z, inner A x z = inner A y z) : x = y := by
  apply ext_inner_left (A := A)
  intro z
  simpa using congrArg star (h z)

end Algebraic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Cauchy–Schwarz and norm recovery in right-module form -/

section Norm

variable [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The Cauchy–Schwarz inequality for a right Hilbert C⋆-module, in the C⋆-algebra:
`⟨x, y⟩_A⋆ ⟨x, y⟩_A ≤ ‖x‖² ⟨y, y⟩_A`. -/
theorem star_unop_inner_mul_unop_inner_le (x y : E) :
    star (unop (inner Aᵐᵒᵖ x y)) * unop (inner Aᵐᵒᵖ x y) ≤ ‖x‖ ^ 2 • unop (inner Aᵐᵒᵖ y y) := by
  have h := unop_le_unop.mpr (inner_mul_inner_swap_le (A := Aᵐᵒᵖ) (x := x) (y := y))
  rwa [unop_mul, unop_smul, ← star_inner x y, unop_star] at h

/-- The Cauchy–Schwarz inequality for a right Hilbert C⋆-module, in norm:
`‖⟨x, y⟩_A‖ ≤ ‖x‖ ‖y‖`. -/
theorem norm_unop_inner_le (x y : E) : ‖unop (inner Aᵐᵒᵖ x y)‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_unop]
  exact norm_inner_le E

/-- Norm recovery: `‖x‖` is the largest value of `‖⟨y, x⟩_A‖` for `y` in the closed unit ball,
attained at `y = ‖x‖⁻¹ x`. -/
theorem isGreatest_norm_unop_inner (x : E) :
    IsGreatest {‖unop (inner Aᵐᵒᵖ y x)‖ | (y : E) (_ : ‖y‖ ≤ 1)} ‖x‖ := by
  refine ⟨⟨(‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩, ?_⟩
  · rw [(normedSpaceCore Aᵐᵒᵖ).norm_smul, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (CStarModule.norm_nonneg Aᵐᵒᵖ)]
    exact inv_mul_le_one_of_le₀ le_rfl (CStarModule.norm_nonneg Aᵐᵒᵖ)
  · rw [inner_smul_left_complex, unop_smul, norm_smul, norm_star, norm_inv, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (CStarModule.norm_nonneg Aᵐᵒᵖ), norm_unop,
      ← norm_sq_eq Aᵐᵒᵖ, sq, ← mul_assoc, inv_mul_mul_self]
  · rintro - ⟨y, hy, rfl⟩
    calc ‖unop (inner Aᵐᵒᵖ y x)‖ ≤ ‖y‖ * ‖x‖ := norm_unop_inner_le y x
      _ ≤ 1 * ‖x‖ := by gcongr; exact CStarModule.norm_nonneg Aᵐᵒᵖ
      _ = ‖x‖ := one_mul _

/-! ### Norm of the right action -/

/-- The inner product of `x a` with itself is `(|x| a)⋆ (|x| a)`, where
`|x| = CFC.sqrt ⟨x, x⟩_A`. -/
lemma unop_inner_op_smul_op_smul (a : A) (x : E) :
    unop (inner Aᵐᵒᵖ (op a • x) (op a • x)) =
      star (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a) * (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a) := by
  set s := CFC.sqrt (unop (inner Aᵐᵒᵖ x x))
  have hs : s * s = unop (inner Aᵐᵒᵖ x x) :=
    CFC.sqrt_mul_sqrt_self _ (unop_nonneg.mpr inner_self_nonneg)
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  rw [unop_inner_op_smul_left, unop_inner_op_smul_right, star_mul, hs', ← hs]
  noncomm_ring

/-- The inner product of `x a - x` with itself is `(|x| a - |x|)⋆ (|x| a - |x|)`, where
`|x| = CFC.sqrt ⟨x, x⟩_A`. -/
lemma unop_inner_op_smul_sub_self (a : A) (x : E) :
    unop (inner Aᵐᵒᵖ (op a • x - x) (op a • x - x)) =
      star (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))) *
        (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))) := by
  set s := CFC.sqrt (unop (inner Aᵐᵒᵖ x x))
  have hs : s * s = unop (inner Aᵐᵒᵖ x x) :=
    CFC.sqrt_mul_sqrt_self _ (unop_nonneg.mpr inner_self_nonneg)
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  simp only [inner_sub_left, inner_sub_right, unop_sub, unop_inner_op_smul_left,
    unop_inner_op_smul_right, star_sub, star_mul, hs', ← hs]
  noncomm_ring

/-- The norm of `x a` is the norm of `|x| a` in `A`, where `|x| = CFC.sqrt ⟨x, x⟩_A`. -/
theorem norm_op_smul (a : A) (x : E) :
    ‖op a • x‖ = ‖CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ), ← norm_unop, unop_inner_op_smul_op_smul,
    CStarRing.norm_star_mul_self, Real.sqrt_mul_self (norm_nonneg _)]

/-- The norm of `x a - x` is the norm of `|x| a - |x|` in `A`, where `|x| = CFC.sqrt ⟨x, x⟩_A`. -/
theorem norm_op_smul_sub_self (a : A) (x : E) :
    ‖op a • x - x‖ =
      ‖CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ), ← norm_unop, unop_inner_op_smul_sub_self,
    CStarRing.norm_star_mul_self, Real.sqrt_mul_self (norm_nonneg _)]

/-- The right action of a C⋆-algebra on a right Hilbert module is bounded:
`‖x a‖ ≤ ‖x‖ ‖a‖`. -/
theorem norm_op_smul_le (a : A) (x : E) : ‖op a • x‖ ≤ ‖x‖ * ‖a‖ := by
  rw [norm_op_smul]
  refine (norm_mul_le _ _).trans_eq ?_
  rw [CFC.norm_sqrt _ (unop_nonneg.mpr inner_self_nonneg), norm_unop,
    ← norm_eq_sqrt_norm_inner_self]

end Norm

/-! ### The right action is essential -/

variable [NormedAddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- The right action on a right Hilbert C⋆-module is essential: `x e → x` along any filter `l`
on `A` such that `b e → b` for every `b ∈ A`. This applies to any approximate unit `l` of `A`
through `Filter.IsApproximateUnit.tendsto_mul_left`; no norm bound on `l` is needed. -/
theorem tendsto_op_smul {l : Filter A} (hl : ∀ b : A, Tendsto (b * ·) l (𝓝 b)) (x : E) :
    Tendsto (fun e ↦ op e • x) l (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_op_smul_sub_self]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hl _)

end CStarModule
