/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt
import TauCeti.Analysis.CStarAlgebra.Module.Semidefinite

/-!
# Basic norm estimates for Hilbert C⋆-modules

For a Hilbert C⋆-module `CStarModule A E`, this file proves vector separation by inner products,
norm recovery from inner products against the closed unit ball, and essentiality of the `A`-action
from the difference identity `‖a x - x‖ = ‖a |x| - |x|‖` for `|x| = ⟪x, x⟫_A ^ (1/2)`. Hence
`e x → x` along any filter `e` with `e b → b` for every `b ∈ A`, in particular along an
approximate unit of `A`, with no boundedness assumption on the approximate unit. The polarization
identity, right-module inner-product/Cauchy–Schwarz identities, and boundedness `‖a x‖ ≤ ‖a‖ ‖x‖`
and `‖x a‖ ≤ ‖x‖ ‖a‖` hold more generally without definiteness and live in
`TauCeti.Analysis.CStarAlgebra.Module.Semidefinite` under `TauCeti.SemiCStarModule` (applying to
every `CStarModule` via the `CStarModule`-to-`SemiCStarModule` instance).

Right Hilbert `A`-modules are represented with Mathlib's class as `CStarModule Aᵐᵒᵖ E`: the right
action is `x a = MulOpposite.op a • x` and the usual `A`-valued inner product is
`⟨x, y⟩_A = MulOpposite.unop (inner Aᵐᵒᵖ x y)`. This file states norm recovery,
`⟨x a, x a⟩_A = (|x| a)⋆ (|x| a)`, `‖x a‖ = ‖|x| a‖`, `‖x a - x‖ = ‖|x| a - |x|‖`, and `x e → x`
in this right-module form. The coefficient-valued inner product also separates vectors in either
variable, so identities of module operators can be checked by pairing against arbitrary vectors,
without a scalar-valued Riesz theorem.

## Main declarations

* `CStarModule.ext_inner_left`, `CStarModule.ext_inner_right`: vectors are determined by their
  inner products against all vectors.
* `CStarModule.isGreatest_norm_inner`: norm recovery, `‖x‖` is the largest value of
  `‖⟪y, x⟫_A‖` over the closed unit ball.
* `CStarModule.norm_smul_sub_self`, `CStarModule.tendsto_smul`: `‖a x - x‖ = ‖a |x| - |x|‖` and
  essentiality of the action (`e x → x` along an approximate unit).
* `CStarModule.isGreatest_norm_unop_inner`, `CStarModule.norm_op_smul`,
  `CStarModule.norm_op_smul_sub_self`, `CStarModule.tendsto_op_smul`: norm recovery, `‖x a‖`,
  `‖x a - x‖`, and essentiality of the action for right modules.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite Filter Topology Complex

namespace CStarModule

/-! ### Vector separation by inner products -/

section Algebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

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

/-! ### Norm recovery and difference identities -/

section Norm

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Norm recovery: `‖x‖` is the largest value of `‖⟪y, x⟫_A‖` for `y` in the closed unit ball,
attained at `y = ‖x‖⁻¹ x`. -/
theorem isGreatest_norm_inner (x : E) :
    IsGreatest {‖inner A y x‖ | (y : E) (_ : ‖y‖ ≤ 1)} ‖x‖ := by
  refine ⟨⟨(‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩, ?_⟩
  · rw [(normedSpaceCore A).norm_smul, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (CStarModule.norm_nonneg A)]
    exact inv_mul_le_one_of_le₀ le_rfl (CStarModule.norm_nonneg A)
  · rw [inner_smul_left_complex, norm_smul, norm_star, norm_inv, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (CStarModule.norm_nonneg A), ← norm_sq_eq A, sq,
      ← mul_assoc, inv_mul_mul_self]
  · rintro - ⟨y, hy, rfl⟩
    calc ‖inner A y x‖ ≤ ‖y‖ * ‖x‖ := norm_inner_le E
      _ ≤ 1 * ‖x‖ := by gcongr; exact CStarModule.norm_nonneg A
      _ = ‖x‖ := one_mul _

/-- The inner product of `a x - x` with itself is `(a |x| - |x|) (a |x| - |x|)⋆`, where
`|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_sub_self (a : A) (x : E) :
    inner A (a • x - x) (a • x - x) =
      (a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) *
        star (a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) := by
  set s := CFC.sqrt (inner A x x)
  have hs : s * s = inner A x x := CFC.sqrt_mul_sqrt_self _ inner_self_nonneg
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  simp only [inner_sub_left, inner_sub_right, inner_op_smul_left, inner_op_smul_right, star_sub,
    star_mul, hs', ← hs]
  noncomm_ring

/-- The norm of `a x - x` is the norm of `a |x| - |x|` in `A`, where `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
theorem norm_smul_sub_self (a : A) (x : E) :
    ‖a • x - x‖ = ‖a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), inner_smul_sub_self, CStarRing.norm_self_mul_star,
    Real.sqrt_mul_self (norm_nonneg _)]

end Norm

/-! ### Norm recovery and difference identities in right-module form -/

section Right

variable [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- Norm recovery for a right Hilbert C⋆-module: `‖x‖` is the largest value of `‖⟨y, x⟩_A‖` for
`y` in the closed unit ball, attained at `y = ‖x‖⁻¹ x`. -/
theorem isGreatest_norm_unop_inner (x : E) :
    IsGreatest {‖unop (inner Aᵐᵒᵖ y x)‖ | (y : E) (_ : ‖y‖ ≤ 1)} ‖x‖ := by
  simpa only [norm_unop] using isGreatest_norm_inner (A := Aᵐᵒᵖ) x

/-- The inner product of `x a` with itself is `(|x| a)⋆ (|x| a)`, where
`|x| = CFC.sqrt ⟨x, x⟩_A`. -/
lemma unop_inner_op_smul_op_smul (a : A) (x : E) :
    unop (inner Aᵐᵒᵖ (op a • x) (op a • x)) =
      star (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a) * (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a) := by
  simp only [TauCeti.SemiCStarModule.inner_smul_smul, unop_mul, unop_star, unop_op, CFC.unop_sqrt]

/-- The inner product of `x a - x` with itself is `(|x| a - |x|)⋆ (|x| a - |x|)`, where
`|x| = CFC.sqrt ⟨x, x⟩_A`. -/
lemma unop_inner_op_smul_sub_self (a : A) (x : E) :
    unop (inner Aᵐᵒᵖ (op a • x - x) (op a • x - x)) =
      star (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))) *
        (CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))) := by
  simp only [inner_smul_sub_self, unop_mul, unop_star, unop_sub, unop_op, CFC.unop_sqrt]

/-- The norm of `x a` is the norm of `|x| a` in `A`, where `|x| = CFC.sqrt ⟨x, x⟩_A`. -/
theorem norm_op_smul (a : A) (x : E) :
    ‖op a • x‖ = ‖CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a‖ := by
  rw [TauCeti.SemiCStarModule.norm_smul, ← norm_unop, unop_mul, unop_op, CFC.unop_sqrt (A := A)]

/-- The norm of `x a - x` is the norm of `|x| a - |x|` in `A`, where `|x| = CFC.sqrt ⟨x, x⟩_A`. -/
theorem norm_op_smul_sub_self (a : A) (x : E) :
    ‖op a • x - x‖ =
      ‖CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))‖ := by
  rw [norm_smul_sub_self, ← norm_unop, unop_sub, unop_mul, unop_op, CFC.unop_sqrt (A := A)]

end Right

/-! ### The action is essential -/

variable [NormedAddCommGroup E] [Module ℂ E]

/-- The action on a Hilbert C⋆-module is essential: `e x → x` along any filter `l` on `A` such
that `e b → b` for every `b ∈ A`. -/
theorem tendsto_smul [SMul A E] [CStarModule A E] {l : Filter A}
    (hl : ∀ b : A, Tendsto (· * b) l (𝓝 b)) (x : E) : Tendsto (· • x) l (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_smul_sub_self]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hl _)

/-- The right action on a right Hilbert C⋆-module is essential: `x e → x` along any filter `l`
on `A` such that `b e → b` for every `b ∈ A`. This applies to any approximate unit `l` of `A`
through `Filter.IsApproximateUnit.tendsto_mul_left`; no norm bound on `l` is needed. -/
theorem tendsto_op_smul [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] {l : Filter A}
    (hl : ∀ b : A, Tendsto (b * ·) l (𝓝 b)) (x : E) :
    Tendsto (fun e ↦ op e • x) l (𝓝 x) := by
  refine (tendsto_smul (A := Aᵐᵒᵖ) (l := l.map op) (fun b ↦ ?_) x).comp tendsto_map
  rw [tendsto_map'_iff]
  simpa [Function.comp_def] using (continuous_op.tendsto (unop b)).comp (hl (unop b))

end CStarModule
