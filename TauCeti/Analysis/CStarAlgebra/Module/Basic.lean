/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Semidef
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt

/-!
# Basic norm estimates for Hilbert C⋆-modules

For a Hilbert C⋆-module `CStarModule A E`, this file proves norm recovery from inner products
against the closed unit ball, and the basic norm estimates for the action of `A`. The key
computation is that `⟪a x, a x⟫_A = (a |x|) (a |x|)⋆` for the positive square root
`|x| = ⟪x, x⟫_A ^ (1/2)`. Hence `‖a x‖ = ‖a |x|‖ ≤ ‖a‖ ‖x‖`, and likewise
`‖a x - x‖ = ‖a |x| - |x|‖`. The second identity shows that the action is essential:
`e x → x` along any filter `e` with `e b → b` for every `b ∈ A`, in particular along an
approximate unit of `A`, with no boundedness assumption on the approximate unit.

Right Hilbert `A`-modules are represented with Mathlib's class as `CStarModule Aᵐᵒᵖ E`: the right
action is `x a = MulOpposite.op a • x` and the usual `A`-valued inner product is
`⟨x, y⟩_A = MulOpposite.unop (inner Aᵐᵒᵖ x y)`. This file restates Mathlib's inner-product
identities and Cauchy–Schwarz inequalities and the results above in this right-module form, where
they read `⟨x a, x a⟩_A = (|x| a)⋆ (|x| a)`, `‖x a‖ ≤ ‖x‖ ‖a‖`, and `x e → x`. The
coefficient-valued inner product also separates vectors in either variable, so identities of
module operators can be checked by pairing against arbitrary vectors, without a scalar-valued
Riesz theorem.

## Main declarations

* `CStarModule.inner_zero_left'`, `CStarModule.inner_zero_right'`, `CStarModule.inner_neg_left'`,
  `CStarModule.inner_neg_right'`: zero and negation inner-product identities without
  `[StarModule ℂ A]`.
* `CStarModule.inner_map_polarization`, `CStarModule.inner_polarization`: polarization identities
  expressing `⟪S x, T y⟫_A` and `⟪x, y⟫_A` through diagonal inner products.
* `CStarModule.ext_inner_left`, `CStarModule.ext_inner_right`: vectors are determined by their
  inner products against all vectors.
* `CStarModule.eq_of_forall_inner_map_self`,
  `CStarModule.inner_map_map_iff_forall_inner_map_map_self`: complex-linear endomorphisms are
  determined by diagonal inner products `⟪x, T x⟫_A`, and a complex-linear map preserves all inner
  products iff it preserves the diagonal inner products `⟪x, x⟫_A`.
* `CStarModule.isGreatest_norm_inner`: norm recovery, `‖x‖` is the largest value of
  `‖⟪y, x⟫_A‖` over the closed unit ball.
* `CStarModule.norm_smul_le`: `‖a x‖ ≤ ‖a‖ ‖x‖`.
* `CStarModule.lipschitzWith_const_smul`, `CStarModule.continuous_const_smul`: continuity of
  `x ↦ a • x`.
* `CStarModule.inner_map_map_le_norm_sq_smul`: Paschke's inequality
  `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` for any bounded `A`-linear operator `T : E →L[ℂ] F`.
* `CStarModule.tendsto_smul`: the action is essential, `e x → x` along an approximate unit.
* `CStarModule.star_unop_inner_mul_unop_inner_le`: the Cauchy–Schwarz inequality
  `⟨x, y⟩_A⋆ ⟨x, y⟩_A ≤ ‖x‖² ⟨y, y⟩_A` for right modules.
* `CStarModule.isGreatest_norm_unop_inner`, `CStarModule.norm_op_smul_le`,
  `CStarModule.tendsto_op_smul`: norm recovery, `‖x a‖ ≤ ‖x‖ ‖a‖`, and essentiality of the
  action for right modules.

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

section NoStarModule

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Left zero inner product `⟪0, y⟫_A = 0`, without requiring `[StarModule ℂ A]` (compare
Mathlib's `CStarModule.inner_zero_left`). -/
@[simp]
theorem inner_zero_left' {y : E} : inner A (0 : E) y = 0 := by
  simpa using inner_add_left (A := A) (x := (0 : E)) (y := 0) (z := y)

/-- Right zero inner product `⟪x, 0⟫_A = 0`, without requiring `[StarModule ℂ A]` (compare
Mathlib's `CStarModule.inner_zero_right`). -/
@[simp]
theorem inner_zero_right' {x : E} : inner A x (0 : E) = 0 := by
  simpa using inner_add_right (A := A) (x := x) (y := (0 : E)) (z := 0)

/-- Left negation inner product `⟪-x, y⟫_A = -⟪x, y⟫_A`, without requiring `[StarModule ℂ A]`
(compare Mathlib's `CStarModule.inner_neg_left`). -/
@[simp]
theorem inner_neg_left' {x y : E} : inner A (-x) y = -inner A x y :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← inner_add_left, neg_add_cancel, inner_zero_left']

/-- Right negation inner product `⟪x, -y⟫_A = -⟪x, y⟫_A`, without requiring `[StarModule ℂ A]`
(compare Mathlib's `CStarModule.inner_neg_right`). -/
@[simp]
theorem inner_neg_right' {x y : E} : inner A x (-y) = -inner A x y :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← inner_add_right, neg_add_cancel, inner_zero_right']

/-- Vectors are determined by their inner products against all vectors in the first slot. -/
theorem ext_inner_left {x y : E} (h : ∀ z, inner A z x = inner A z y) : x = y := by
  apply sub_eq_zero.mp
  apply (inner_self (A := A)).mp
  rw [sub_eq_add_neg, inner_add_right, inner_neg_right', h, add_neg_cancel]

/-- Vectors are determined by their inner products against all vectors in the second slot. -/
theorem ext_inner_right {x y : E} (h : ∀ z, inner A x z = inner A y z) : x = y := by
  apply ext_inner_left (A := A)
  intro z
  simpa using congrArg star (h z)

end NoStarModule

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Polarization for a pair of complex-linear maps into a C⋆-module: the sesquilinear pairing
`⟪S x, T y⟫_A` is determined by its diagonal values `⟪S z, T z⟫_A`. -/
lemma inner_map_polarization {V M₁ M₂ : Type*} [AddCommGroup V] [Module ℂ V]
    [FunLike M₁ V E] [LinearMapClass M₁ ℂ V E] [FunLike M₂ V E] [LinearMapClass M₂ ℂ V E]
    (S : M₁) (T : M₂) (x y : V) :
    inner A (S x) (T y) = (4 : ℂ)⁻¹ • (inner A (S (x + y)) (T (x + y)) -
      inner A (S (x - y)) (T (x - y)) - I • inner A (S (x + I • y)) (T (x + I • y)) +
      I • inner A (S (x - I • y)) (T (x - I • y))) := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left_complex, inner_smul_right_complex, Complex.star_def, conj_I,
    smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
  module

/-- The polarization identity: the `A`-valued inner product, conjugate-linear in its first
variable, is determined by its values `⟪z, z⟫_A` on the diagonal. This holds for either side
convention, in particular for right Hilbert modules `CStarModule Aᵐᵒᵖ E`. -/
lemma inner_polarization (x y : E) :
    inner A x y = (4 : ℂ)⁻¹ • (inner A (x + y) (x + y) - inner A (x - y) (x - y) -
      I • inner A (x + I • y) (x + I • y) + I • inner A (x - I • y) (x - I • y)) :=
  inner_map_polarization (LinearMap.id : E →ₗ[ℂ] E) (LinearMap.id : E →ₗ[ℂ] E) x y

/-- Complex-linear endomorphisms of a C⋆-module are determined by their diagonal inner products
`⟪x, T x⟫_A`. -/
theorem eq_of_forall_inner_map_self {M : Type*} [FunLike M E E] [LinearMapClass M ℂ E E]
    {S T : M} (h : ∀ x : E, inner A x (S x) = inner A x (T x)) : S = T :=
  DFunLike.ext S T fun y ↦ ext_inner_left (A := A) fun x ↦ by
    have hS := inner_map_polarization (A := A) (LinearMap.id : E →ₗ[ℂ] E) S x y
    have hT := inner_map_polarization (A := A) (LinearMap.id : E →ₗ[ℂ] E) T x y
    simp only [LinearMap.id_apply, h] at hS hT
    exact hS.trans hT.symm

/-- A complex-linear map between C⋆-modules preserves all inner products if and only if it
preserves diagonal inner products `⟪x, x⟫_A`. -/
theorem inner_map_map_iff_forall_inner_map_map_self {F M : Type*} [AddCommGroup F] [Module ℂ F]
    [SMul A F] [Norm F] [CStarModule A F] [FunLike M E F] [LinearMapClass M ℂ E F] (U : M) :
    (∀ x y : E, inner A (U x) (U y) = inner A x y) ↔
      ∀ x : E, inner A (U x) (U x) = inner A x x :=
  ⟨fun h x ↦ h x x, fun h x y ↦ by
    rw [inner_map_polarization (A := A) U U x y, inner_polarization (A := A) x y]
    simp only [h]⟩

omit [StarModule ℂ A] in
/-- Any plain function from a C⋆-module into a type with an `A`-valued inner product that preserves
the `A`-valued inner product is injective. -/
theorem injective_of_inner_map_map {F : Type*} [Inner A F] {f : E → F}
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    Function.Injective f := fun x y hxy ↦
  ext_inner_left (A := A) fun z ↦ by
    rw [← hf z x, ← hf z y, hxy]

omit [StarModule ℂ A] in
/-- Vectors with equal diagonal `A`-valued inner products have equal norms. -/
theorem norm_eq_of_inner_self_eq {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F]
    [Norm F] [CStarModule A F] {x : E} {y : F} (h : inner A x x = inner A y y) :
    ‖x‖ = ‖y‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), norm_eq_sqrt_norm_inner_self (A := A) (x := y), h]

end Algebraic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Norm recovery and the norm of the action -/

section Norm

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Monotonicity of the module norm in the diagonal `A`-valued inner product: if
`⟪x, x⟫_A ≤ ⟪y, y⟫_A`, then `‖x‖ ≤ ‖y‖`. -/
theorem norm_le_of_inner_self_le {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F]
    [Norm F] [CStarModule A F] {x : E} {y : F} (h : inner A x x ≤ inner A y y) :
    ‖x‖ ≤ ‖y‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), norm_eq_sqrt_norm_inner_self (A := A) (x := y)]
  exact Real.sqrt_le_sqrt (CStarAlgebra.norm_le_norm_of_le_of_nonneg h inner_self_nonneg)

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

/-- The inner product of `a x` with itself is `(a |x|) (a |x|)⋆`, where
`|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_smul (a : A) (x : E) :
    inner A (a • x) (a • x) =
      a * CFC.sqrt (inner A x x) * star (a * CFC.sqrt (inner A x x)) :=
  TauCeti.IsPosSemidefCStarModuleAlong.inner_smul_smul (NonUnitalStarAlgHom.id ℂ A) a x

/-- The inner product of `a x - x` with itself is `(a |x| - |x|) (a |x| - |x|)⋆`, where
`|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_sub_self (a : A) (x : E) :
    inner A (a • x - x) (a • x - x) =
      (a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) *
        star (a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) :=
  TauCeti.IsPosSemidefCStarModuleAlong.inner_smul_sub_self (NonUnitalStarAlgHom.id ℂ A) a x

/-- The norm of `a x` is the norm of `a |x|` in `A`, where `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
protected theorem norm_smul (a : A) (x : E) : ‖a • x‖ = ‖a * CFC.sqrt (inner A x x)‖ :=
  TauCeti.IsPosSemidefCStarModuleAlong.norm_smul (NonUnitalStarAlgHom.id ℂ A) a x

/-- The norm of `a x - x` is the norm of `a |x| - |x|` in `A`, where `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
theorem norm_smul_sub_self (a : A) (x : E) :
    ‖a • x - x‖ = ‖a * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)‖ :=
  TauCeti.IsPosSemidefCStarModuleAlong.norm_smul_sub_self (NonUnitalStarAlgHom.id ℂ A) a x

/-- The action of a C⋆-algebra on a Hilbert C⋆-module is bounded: `‖a x‖ ≤ ‖a‖ ‖x‖`. -/
protected theorem norm_smul_le (a : A) (x : E) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ :=
  TauCeti.IsPosSemidefCStarModuleAlong.norm_smul_le (NonUnitalStarAlgHom.id ℂ A) a x

end Norm

/-! ### Cauchy–Schwarz, norm recovery, and the norm of the action in right-module form -/

section Right

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
  simp only [inner_smul_smul, unop_mul, unop_star, unop_op, CFC.unop_sqrt]

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
  rw [CStarModule.norm_smul, ← norm_unop, unop_mul, unop_op, CFC.unop_sqrt (A := A)]

/-- The norm of `x a - x` is the norm of `|x| a - |x|` in `A`, where `|x| = CFC.sqrt ⟨x, x⟩_A`. -/
theorem norm_op_smul_sub_self (a : A) (x : E) :
    ‖op a • x - x‖ =
      ‖CFC.sqrt (unop (inner Aᵐᵒᵖ x x)) * a - CFC.sqrt (unop (inner Aᵐᵒᵖ x x))‖ := by
  rw [norm_smul_sub_self, ← norm_unop, unop_sub, unop_mul, unop_op, CFC.unop_sqrt (A := A)]

/-- The right action of a C⋆-algebra on a right Hilbert module is bounded:
`‖x a‖ ≤ ‖x‖ ‖a‖`. -/
theorem norm_op_smul_le (a : A) (x : E) : ‖op a • x‖ ≤ ‖x‖ * ‖a‖ := by
  rw [mul_comm, ← norm_op a]
  exact CStarModule.norm_smul_le _ x

end Right

/-! ### The action is essential -/

section Essential

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

/-- Coefficient multiplication `x ↦ a • x` is Lipschitz with constant `‖a‖₊` on any pre-Hilbert
C⋆-module. -/
theorem lipschitzWith_const_smul [SMul A E] [CStarModule A E] (a : A) :
    LipschitzWith ‖a‖₊ (fun x : E ↦ a • x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hsub : a • x - a • y = a • (x - y) :=
    ext_inner_left (A := A) fun z ↦ by simp [inner_sub_right, inner_op_smul_right, mul_sub]
  rw [dist_eq_norm, dist_eq_norm, hsub, coe_nnNorm]
  exact CStarModule.norm_smul_le a (x - y)

/-- Coefficient multiplication `x ↦ a • x` is continuous on any pre-Hilbert C⋆-module. -/
@[continuity, fun_prop]
theorem continuous_const_smul [SMul A E] [CStarModule A E] (a : A) :
    Continuous (fun x : E ↦ a • x) :=
  (lipschitzWith_const_smul (A := A) (E := E) a).continuous

end Essential

/-! ### Paschke's inequality -/

section Paschke

open scoped ComplexOrder Ring

omit [StarOrderedRing A] in
/-- The diagonal inner product of `u.fst • z + u.snd • z` embeds into `Unitization ℂ A` as
`u * ⟪z, z⟫_A * star u`. -/
private lemma inr_inner_unitization_smul {E : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E]
    [Norm E] [CStarModule A E] (u : Unitization ℂ A) (z : E) :
    (inner A (u.fst • z + u.snd • z) (u.fst • z + u.snd • z) : Unitization ℂ A) =
      u * (inner A z z : Unitization ℂ A) * star u := by
  ext
  · simp [Unitization.fst_mul]
  · simp only [Unitization.snd_inr, Unitization.snd_mul, Unitization.fst_mul, Unitization.fst_inr,
      Unitization.fst_star, Unitization.snd_star, zero_mul, zero_smul, zero_add, add_zero,
      inner_add_left, inner_add_right, inner_smul_left_complex, inner_smul_right_complex,
      inner_op_smul_left, inner_op_smul_right, smul_add, smul_smul, mul_add, mul_smul_comm,
      mul_assoc]

/-- Regularized Paschke estimate: for any strictly positive majorant `b ≥ ⟪x, x⟫_A` in
`Unitization ℂ A`, we have `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • b`.

The proof normalizes `x` by `v = √(b⁻¹)`, forming `y = v • x` in the unit ball of `E`;
boundedness of `T` then bounds `v ⟪T x, T x⟫_A v = ⟪T y, T y⟫_A` by `‖T‖ ^ 2`, and
`CFC.conjSqrt_ringInverse_le_algebraMap_iff` conjugates back by `√b`. -/
private lemma inr_inner_map_map_le_norm_sq_smul_of_le {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul A F] [CStarModule A F] (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) (x : E) {b : Unitization ℂ A}
    (hb : IsStrictlyPositive b) (hxb : (inner A x x : Unitization ℂ A) ≤ b) :
    (inner A (T x) (T x) : Unitization ℂ A) ≤ ‖T‖ ^ 2 • b := by
  set q : Unitization ℂ A := (inner A x x : Unitization ℂ A)
  set p : Unitization ℂ A := (inner A (T x) (T x) : Unitization ℂ A)
  -- Normalize `x` via the unitization action of `v = √(b⁻¹)`.
  set v : Unitization ℂ A := CFC.sqrt b⁻¹ʳ
  have hv_sa : IsSelfAdjoint v := (CFC.sqrt_nonneg _).isSelfAdjoint
  set y : E := v.fst • x + v.snd • x
  have hy_inner : (inner A y y : Unitization ℂ A) = CFC.conjSqrt b⁻¹ʳ q := by
    rw [CFC.conjSqrt_apply]
    simpa only [hv_sa.star_eq] using inr_inner_unitization_smul v x
  have hTy_inner : (inner A (T y) (T y) : Unitization ℂ A) = CFC.conjSqrt b⁻¹ʳ p := by
    have hTy : T y = v.fst • T x + v.snd • T x := by simp only [y, map_add, map_smul, hT]
    rw [CFC.conjSqrt_apply]
    simpa only [hTy, hv_sa.star_eq] using inr_inner_unitization_smul v (T x)
  -- The majorant `q ≤ b` forces `⟪y, y⟫_A = √(b⁻¹) q √(b⁻¹) ≤ 1`, hence `‖y‖² ≤ 1`.
  have hvqv_nonneg : 0 ≤ CFC.conjSqrt b⁻¹ʳ q :=
    hv_sa.conjugate_nonneg (Unitization.inr_nonneg ℂ _ inner_self_nonneg)
  have hvqv_le : CFC.conjSqrt b⁻¹ʳ q ≤ 1 :=
    (CFC.conjSqrt_le_conjSqrt hxb).trans_eq (CFC.conjSqrt_ringInverse_self b hb)
  have hy_norm_sq : ‖y‖ ^ 2 ≤ 1 := by
    rw [CStarModule.norm_sq_eq A, ← Unitization.norm_inr (𝕜 := ℂ), hy_inner]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hvqv_nonneg).mpr hvqv_le
  -- Boundedness of `T` on the normalized vector `y` bounds `√(b⁻¹) p √(b⁻¹)` by `‖T‖²`.
  have hvpv_nonneg : 0 ≤ CFC.conjSqrt b⁻¹ʳ p :=
    hv_sa.conjugate_nonneg (Unitization.inr_nonneg ℂ _ inner_self_nonneg)
  have hvpv_norm : ‖CFC.conjSqrt b⁻¹ʳ p‖ ≤ ‖T‖ ^ 2 := by
    rw [← hTy_inner, Unitization.norm_inr (𝕜 := ℂ), ← CStarModule.norm_sq_eq A]
    calc ‖T y‖ ^ 2 ≤ (‖T‖ * ‖y‖) ^ 2 := by gcongr; exact T.le_opNorm y
      _ = ‖T‖ ^ 2 * ‖y‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖T‖ ^ 2 * 1 := by gcongr
      _ = ‖T‖ ^ 2 := mul_one _
  have hvpv_le : CFC.conjSqrt b⁻¹ʳ p ≤ algebraMap ℝ (Unitization ℂ A) (‖T‖ ^ 2) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖T‖) hvpv_nonneg).mp hvpv_norm
  -- Conjugate back by `√b` to recover `p ≤ ‖T‖² • b`.
  exact (CFC.conjSqrt_ringInverse_le_algebraMap_iff hb).mp hvpv_le

/-- Paschke's inequality for bounded `A`-linear operators between Hilbert C⋆-modules:
`⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A`, with no adjointability or completeness assumptions
(Lance, Proposition 1.2). -/
theorem inner_map_map_le_norm_sq_smul {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A E] [CStarModule A E] [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (T : E →L[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  -- Pass to `Unitization ℂ A`, regularize `⟪x, x⟫_A` by `+ ε`, and let `ε → 0⁺`.
  rw [← Unitization.inr_le_inr_iff ℂ, Unitization.inr_smul]
  set q : Unitization ℂ A := (inner A x x : Unitization ℂ A)
  have hq : 0 ≤ q := Unitization.inr_nonneg ℂ _ inner_self_nonneg
  have hle (ε : ℝ) (hε : 0 < ε) :
      (inner A (T x) (T x) : Unitization ℂ A) ≤
        ‖T‖ ^ 2 • (q + algebraMap ℝ (Unitization ℂ A) ε) := by
    have hε_pos : IsStrictlyPositive (algebraMap ℝ (Unitization ℂ A) ε) :=
      isStrictlyPositive_algebraMap hε
    exact inr_inner_map_map_le_norm_sq_smul_of_le T hT x
      (IsStrictlyPositive.nonneg_add hq hε_pos) (le_add_of_nonneg_right hε_pos.nonneg)
  have hcont : Continuous (fun ε : ℝ ↦ ‖T‖ ^ 2 • (q + algebraMap ℝ (Unitization ℂ A) ε)) := by
    fun_prop
  have htend : Tendsto (fun ε : ℝ ↦ ‖T‖ ^ 2 • (q + algebraMap ℝ (Unitization ℂ A) ε))
      (𝓝[>] 0) (𝓝 (‖T‖ ^ 2 • q)) := by
    simpa only [map_zero, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hle)

end Paschke

end CStarModule
