/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import TauCeti.Algebra.Star.Opposite
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Positive semidefinite C⋆-modules, dense `⋆`-subalgebra actions, and separated quotients

This file develops positive semidefinite inner-product modules over C⋆-algebras and over dense
`⋆`-subalgebras whose positivity and norm are measured in a specified C⋆-completion, together with
their separated quotients and universal properties.

A positive semidefinite `A`-module (`TauCeti.PosSemidefCStarModule A E`) satisfies all axioms of
Mathlib's `CStarModule A E` except definiteness `⟪x, x⟫_A = 0 ↔ x = 0`. More generally, for a
nonunital `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A` into a C⋆-algebra `A` (such as
`NonUnitalStarSubalgebraClass.subtype S` for a `NonUnitalStarSubalgebra ℂ A`),
`TauCeti.PosSemidefCStarModuleAlong ι E` records an `A`-valued positive semidefinite inner product
on an `A₀`-module `E` satisfying `⟪x, a₀ • y⟫_A = ι a₀ * ⟪x, y⟫_A` and `‖x‖ = √‖⟪x, x⟫_A‖`.
Neither a norm nor an order is required on `A₀`; positivity `0 ≤ ⟪x, x⟫_A` and the seminorm
`√‖⟪x, x⟫_A‖` are measured in `A`.

When `ι` has dense range in `A` (in particular for `PosSemidefCStarModule A E`, where
`ι = NonUnitalStarAlgHom.id ℂ A`), approximating `⟪x, y⟫_A` by elements `ι a₀` and passing to the
order-closed limit yields the C⋆-algebra Cauchy–Schwarz inequality
`⟪x, y⟫_A * ⟪y, x⟫_A ≤ ‖x‖ ^ 2 • ⟪y, y⟫_A` even in the presence of nonzero null vectors, hence
`‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` and the triangle inequality for `√‖⟪x, x⟫_A‖`. When `E` carries no
pre-existing seminorm, `TauCeti.PosSemidefCStarModule.DenseCore` (and its specialization
`TauCeti.PosSemidefCStarModule.Core`) builds the `SeminormedAddCommGroup E` and `NormedSpace ℂ E`
structures from the pairing alone.

Quotienting by the null submodule (`nullSubmodule ℂ E`) via `SeparationQuotient E` kills null
vectors, descends the `A`-valued inner product and the `A₀`-action, and makes
`SeparationQuotient E` a pre-Hilbert `A`-module (`CStarModule A (SeparationQuotient E)`) when
`A₀ = A`. Bounded module maps into Hausdorff spaces lift uniquely with equal operator norm via
`SeparationQuotient.liftCLM`, while complex-linear inner-product-preserving maps into pre-Hilbert
`A`-modules automatically intertwine the coefficient action and lift uniquely to inner-product- and
action-preserving linear isometries (`SeparationQuotient.liftOfInner`).

## Main declarations

* `TauCeti.PosSemidefCStarModule`: positive semidefinite C⋆-modules over `A`, extending `Inner A E`
  and generalizing `CStarModule A E`.
* `TauCeti.PosSemidefCStarModuleAlong`: positive semidefinite modules over `A₀` along
  `ι : A₀ →⋆ₙₐ[ℂ] A` with positivity and norm measured in `A`.
* `TauCeti.PosSemidefCStarModule.DenseCore`, `TauCeti.PosSemidefCStarModule.Core`: constructors
  producing the seminormed space structure from a positive semidefinite pairing, with pullback
  `DenseCore.comap` and `A₀`-valued pairing constructor `DenseCore.ofInnerHom`.
* `TauCeti.PosSemidefCStarModuleAlong.inner_mul_inner_swap_le`,
  `TauCeti.PosSemidefCStarModuleAlong.norm_inner_le`: C⋆-algebra and norm Cauchy–Schwarz
  inequalities without definiteness.
* `TauCeti.PosSemidefCStarModuleAlong.map_smul_of_inner_eq`: any complex-linear map into a
  `CStarModule A F` preserving the `A`-valued inner product automatically satisfies
  `f (a₀ • x) = ι a₀ • f x`.
* `SeparationQuotient.instCStarModule`: `CStarModule A (SeparationQuotient E)` for a positive
  semidefinite `A`-module `E`.
* `SeparationQuotient.liftOfInner`: universal property of `SeparationQuotient E` for
  inner-product-preserving linear maps.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2, Lemma 2.16.
-/

public section

open MulOpposite Complex
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

/-! ### Classes for positive semidefinite modules and dense `⋆`-subalgebra actions -/

/-- A positive semidefinite C⋆-module over `A`: a complex module `E` with an action of `A` and an
`A`-valued positive semidefinite inner product inducing the seminorm `‖x‖ = √‖⟪x, x⟫_A‖`, without
assuming definiteness `⟪x, x⟫_A = 0 ↔ x = 0`. For right `B`-modules, take `A = Bᵐᵒᵖ`. -/
class PosSemidefCStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x y z : E} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x : E} : 0 ≤ inner x x
  inner_op_smul_right {a : A} {x y : E} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner x (z • y) = z • inner x y
  star_inner (x y : E) : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self (x : E) : ‖x‖ = √‖inner x x‖

attribute [simp] PosSemidefCStarModule.inner_add_right PosSemidefCStarModule.star_inner
  PosSemidefCStarModule.inner_op_smul_right PosSemidefCStarModule.inner_smul_right_complex

/-- Every pre-Hilbert C⋆-module (`CStarModule A E`) is positive semidefinite. -/
instance PosSemidefCStarModule.ofCStarModule {A E : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [CStarModule A E] : PosSemidefCStarModule A E where
  toInner := inferInstance
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner := CStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := CStarModule.norm_eq_sqrt_norm_inner_self

/-- A positive semidefinite `A`-module satisfying definiteness `⟪x, x⟫_A = 0 → x = 0` is a
pre-Hilbert C⋆-module. -/
abbrev PosSemidefCStarModule.toCStarModule {A E : Type*} [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E]
    [Norm A] [Norm E] [PosSemidefCStarModule A E]
    (hdef : ∀ x : E, inner A x x = 0 → x = 0) : CStarModule A E where
  toInner := inferInstance
  inner_add_right := PosSemidefCStarModule.inner_add_right
  inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg
  inner_self {x} := ⟨hdef x, fun hx ↦ by
    subst hx
    have h0 := PosSemidefCStarModule.inner_add_right (A := A) (x := (0 : E)) (y := 0) (z := 0)
    rw [add_zero] at h0
    simpa using congrArg (· - inner A (0 : E) 0) h0.symm⟩
  inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right
  inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex
  star_inner := PosSemidefCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self

/-- A positive semidefinite module over `A₀` along a nonunital `⋆`-algebra homomorphism
`ι : A₀ →⋆ₙₐ[ℂ] A`, where positivity `0 ≤ ⟪x, x⟫_A` and seminorm `‖x‖ = √‖⟪x, x⟫_A‖` are measured
in `A`. No norm or order is required on `A₀`. -/
class PosSemidefCStarModuleAlong {A₀ A : Type*}
    [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    (ι : A₀ →⋆ₙₐ[ℂ] A) (E : Type*)
    [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E] : Prop where
  inner_add_right {x y z : E} : inner A x (y + z) = inner A x y + inner A x z
  inner_self_nonneg {x : E} : 0 ≤ inner A x x
  inner_op_smul_right {a₀ : A₀} {x y : E} : inner A x (a₀ • y) = ι a₀ * inner A x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner A x (z • y) = z • inner A x y
  star_inner (x y : E) : star (inner A x y) = inner A y x
  norm_eq_sqrt_norm_inner_self (x : E) : ‖x‖ = √‖inner A x x‖

/-- A `PosSemidefCStarModule A E` is a `PosSemidefCStarModuleAlong` for the identity map on `A`. -/
instance PosSemidefCStarModule.instAlongId {A E : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] :
    PosSemidefCStarModuleAlong (NonUnitalStarAlgHom.id ℂ A) E where
  inner_add_right := PosSemidefCStarModule.inner_add_right
  inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg
  inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right
  inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex
  star_inner := PosSemidefCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self

/-- Restricting the scalar action of a `PosSemidefCStarModule A E` to a `NonUnitalStarSubalgebra`
`S` of `A` yields a `PosSemidefCStarModuleAlong` along `NonUnitalStarSubalgebraClass.subtype S`. -/
instance PosSemidefCStarModule.instAlongSubalgebra {A E : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] (S : NonUnitalStarSubalgebra ℂ A) :
    PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S) E where
  inner_add_right := PosSemidefCStarModule.inner_add_right
  inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg
  inner_op_smul_right {s _ _} := PosSemidefCStarModule.inner_op_smul_right (a := (s : A))
  inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex
  star_inner := PosSemidefCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self

namespace PosSemidefCStarModuleAlong

/-! ### Algebraic consequences -/

section Algebraic

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]

include ι in
lemma inner_add_left (x y z : E) : inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_star (r := inner A (x + y) z), star_inner (ι := ι),
    inner_add_right (ι := ι), star_add, star_inner (ι := ι), star_inner (ι := ι)]

lemma inner_op_smul_left (a₀ : A₀) (x y : E) :
    inner A (a₀ • x) y = inner A x y * star (ι a₀) := by
  rw [← star_star (r := inner A (a₀ • x) y), star_inner (ι := ι),
    inner_op_smul_right (ι := ι), star_mul, star_inner (ι := ι)]

include ι in
lemma isSelfAdjoint_inner_self (x : E) : IsSelfAdjoint (inner A x x) :=
  star_inner (ι := ι) x x

include ι in
lemma inner_smul_right_real (r : ℝ) (x y : E) : inner A x (r • y) = r • inner A x y := by
  have hr : r • y = (r : ℂ) • y := by simp
  rw [hr, inner_smul_right_complex (ι := ι)]
  simp

section StarModule

variable [StarModule ℂ A]

include ι in
lemma inner_smul_left_complex (z : ℂ) (x y : E) :
    inner A (z • x) y = star z • inner A x y := by
  rw [← star_star (r := inner A (z • x) y), star_inner (ι := ι),
    inner_smul_right_complex (ι := ι), star_smul, star_inner (ι := ι)]

include ι in
lemma inner_smul_left_real (r : ℝ) (x y : E) : inner A (r • x) y = r • inner A x y := by
  have hr : r • x = (r : ℂ) • x := by simp
  rw [hr, inner_smul_left_complex (ι := ι)]
  simp

/-- The pairing `⟪x, y⟫_A` bundled as a sesquilinear map. -/
def innerₛₗ (ι : A₀ →⋆ₙₐ[ℂ] A) [PosSemidefCStarModuleAlong ι E] : E →ₗ⋆[ℂ] E →ₗ[ℂ] A where
  toFun x :=
    { toFun y := inner A x y
      map_add' y z := inner_add_right (ι := ι)
      map_smul' c y := inner_smul_right_complex (ι := ι) }
  map_add' x y := by ext z; exact inner_add_left (ι := ι) x y z
  map_smul' c x := by ext z; exact inner_smul_left_complex (ι := ι) c x z

@[simp]
lemma innerₛₗ_apply (x y : E) : innerₛₗ ι x y = inner A x y := (rfl)

include ι in
lemma inner_zero_right (x : E) : inner A x 0 = 0 := map_zero (innerₛₗ ι x)

include ι in
lemma inner_zero_left (x : E) : inner A 0 x = 0 :=
  LinearMap.congr_fun (map_zero (innerₛₗ ι)) x

include ι in
lemma inner_neg_right (x y : E) : inner A x (-y) = -inner A x y := map_neg (innerₛₗ ι x) y

include ι in
lemma inner_neg_left (x y : E) : inner A (-x) y = -inner A x y :=
  LinearMap.congr_fun (map_neg (innerₛₗ ι) x) y

include ι in
lemma inner_sub_right (x y z : E) : inner A x (y - z) = inner A x y - inner A x z :=
  map_sub (innerₛₗ ι x) y z

include ι in
lemma inner_sub_left (x y z : E) : inner A (x - y) z = inner A x z - inner A y z :=
  LinearMap.congr_fun (map_sub (innerₛₗ ι) x y) z

include ι in
/-- Polarization identity for a positive semidefinite pairing. -/
lemma inner_polarization (x y : E) :
    inner A x y = (4 : ℂ)⁻¹ • (inner A (x + y) (x + y) - inner A (x - y) (x - y) -
      I • inner A (x + I • y) (x + I • y) + I • inner A (x - I • y) (x - I • y)) := by
  simp only [inner_add_left (ι := ι), inner_add_right (ι := ι), inner_sub_left (ι := ι),
    inner_sub_right (ι := ι), inner_smul_left_complex (ι := ι), inner_smul_right_complex (ι := ι),
    Complex.star_def, conj_I, smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
  module

/-- Any complex-linear map into a definite `CStarModule A F` that preserves the `A`-valued inner
product automatically intertwines the `A₀`-action with the `A`-action along `ι`, without assuming
continuity or dense range. -/
theorem map_smul_of_inner_eq {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a₀ : A₀) (x : E) : f (a₀ • x) = ι a₀ • f x := by
  apply sub_eq_zero.mp
  apply (CStarModule.inner_self (A := A)).mp
  simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, hf,
    inner_op_smul_left (ι := ι), inner_op_smul_right (ι := ι)]
  noncomm_ring

end StarModule

end Algebraic

/-! ### Cauchy–Schwarz and action bounds -/

section Analytic

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]

include ι in
lemma norm_sq_eq (x : E) : ‖x‖ ^ 2 = ‖inner A x x‖ := by
  simp [norm_eq_sqrt_norm_inner_self (ι := ι)]

include ι in
protected lemma norm_nonneg (x : E) : 0 ≤ ‖x‖ := by
  simp [norm_eq_sqrt_norm_inner_self (ι := ι)]

include ι in
protected lemma norm_zero : ‖(0 : E)‖ = 0 := by
  simp [norm_eq_sqrt_norm_inner_self (ι := ι), inner_zero_right (ι := ι)]

include ι in
/-- Vanishing of the seminorm is equivalent to vanishing of the self-inner product `⟪x, x⟫_A`. -/
theorem norm_eq_zero_iff_inner_self_eq_zero (x : E) : ‖x‖ = 0 ↔ inner A x x = 0 := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι), Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]

include ι in
protected lemma norm_smul_complex (c : ℂ) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι) (c • x), norm_eq_sqrt_norm_inner_self (ι := ι) x,
    inner_smul_left_complex (ι := ι), inner_smul_right_complex (ι := ι), smul_smul,
    norm_smul, norm_mul, norm_star, Real.sqrt_mul (by positivity),
    Real.sqrt_mul_self (norm_nonneg c)]

variable [StarOrderedRing A]

private lemma inner_quad_nonneg (hι : DenseRange ι) (x y : E) (t : ℝ) :
    (0 : A) ≤ ‖x‖ ^ 2 • (inner A x y * inner A y x) -
      t • (inner A x y * inner A y x) - t • (inner A x y * inner A y x) +
      (t ^ 2) • inner A y y := by
  have hstep (a₀ : A₀) :
      (0 : A) ≤ ‖x‖ ^ 2 • (ι a₀ * star (ι a₀)) - t • (ι a₀ * inner A y x) -
        t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y := by
    calc (0 : A) ≤ inner A (a₀ • x - t • y) (a₀ • x - t • y) := inner_self_nonneg (ι := ι)
      _ = ι a₀ * inner A x x * star (ι a₀) - t • (ι a₀ * inner A y x) -
            t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y := by
          simp only [inner_sub_right (ι := ι), inner_sub_left (ι := ι),
            inner_op_smul_right (ι := ι), inner_op_smul_left (ι := ι),
            inner_smul_right_real (ι := ι), inner_smul_left_real (ι := ι),
            mul_smul_comm, smul_mul_assoc, smul_smul, ← sq, mul_assoc]
          abel
      _ ≤ ‖x‖ ^ 2 • (ι a₀ * star (ι a₀)) - t • (ι a₀ * inner A y x) -
            t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y := by
          gcongr
          rw [norm_sq_eq (ι := ι)]
          exact CStarAlgebra.star_right_conjugate_le_norm_smul (ι a₀) (inner A x x)
            (isSelfAdjoint_inner_self (ι := ι) x)
  let P (a : A) : Prop := (0 : A) ≤ ‖x‖ ^ 2 • (a * star a) -
    t • (a * inner A y x) - t • (inner A x y * star a) + (t ^ 2) • inner A y y
  have hclosed : IsClosed {a : A | P a} := isClosed_le (by fun_prop) (by fun_prop)
  have hlim : P (inner A x y) :=
    hι.induction (P := P) (fun a ⟨a₀, ha₀⟩ ↦ ha₀ ▸ hstep a₀) hclosed (inner A x y)
  simpa only [P, star_inner (ι := ι)] using hlim

/-- The C⋆-algebra Cauchy–Schwarz inequality for a positive semidefinite module over a dense
`⋆`-subalgebra: `⟪x, y⟫_A * ⟪y, x⟫_A ≤ ‖x‖ ^ 2 • ⟪y, y⟫_A`. -/
theorem inner_mul_inner_swap_le (hι : DenseRange ι) (x y : E) :
    inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y := by
  set p := inner A x y * inner A y x
  rcases (norm_nonneg (inner A x x)).eq_or_lt with hr | hr
  · -- Null-vector case `‖⟪x, x⟫_A‖ = 0`: bound `‖p‖ ≤ (t / 2) * ‖⟪y, y⟫_A‖` for all `t > 0`.
    have hx0 : ‖x‖ ^ 2 = 0 := by rw [norm_sq_eq (ι := ι), ← hr]
    have hp_nonneg : 0 ≤ p := by
      dsimp only [p]
      rw [← star_inner (ι := ι) x y]
      exact mul_star_self_nonneg (inner A x y)
    have hp_bound (t : ℝ) (ht : 0 < t) : ‖p‖ ≤ t / 2 * ‖inner A y y‖ := by
      have ht2 : 0 < 2 * t := by positivity
      have hmul : 2 * t * (t / 2) = t ^ 2 := by ring
      have hle : (2 * t) • p ≤ (2 * t) • ((t / 2) • inner A y y) := by
        have hq := inner_quad_nonneg hι x y t
        have hq_eq : ‖x‖ ^ 2 • p - t • p - t • p + t ^ 2 • inner A y y =
            (2 * t) • ((t / 2) • inner A y y) - (2 * t) • p := by
          rw [hx0, zero_smul, smul_smul, hmul, two_mul, add_smul]
          abel
        rwa [hq_eq, sub_nonneg] at hq
      have hle' : p ≤ (t / 2) • inner A y y := (smul_le_smul_iff_of_pos_left ht2).mp hle
      simpa [norm_smul, abs_of_pos ht] using
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hle' hp_nonneg
    have hp0 : p = 0 := by
      rw [← norm_le_zero_iff]
      by_contra! hp_pos
      have hy_pos : 0 < ‖inner A y y‖ := by
        have h1 := hp_bound 1 one_pos
        linarith
      have hhalf := hp_bound (‖p‖ / ‖inner A y y‖) (div_pos hp_pos hy_pos)
      have hsimp : (‖p‖ / ‖inner A y y‖) / 2 * ‖inner A y y‖ = ‖p‖ / 2 := by field_simp
      linarith
    simp [hp0, hx0]
  · -- Positive-norm case `0 < ‖⟪x, x⟫_A‖`: evaluate `inner_quad_nonneg` at `t = ‖x‖ ^ 2`.
    have hx_pos : 0 < ‖x‖ ^ 2 := by rwa [norm_sq_eq (ι := ι)]
    have hq := inner_quad_nonneg hι x y (‖x‖ ^ 2)
    have hq_eq : ‖x‖ ^ 2 • p - ‖x‖ ^ 2 • p - ‖x‖ ^ 2 • p + (‖x‖ ^ 2) ^ 2 • inner A y y =
        ‖x‖ ^ 2 • (‖x‖ ^ 2 • inner A y y) - ‖x‖ ^ 2 • p := by
      rw [smul_smul, ← sq]
      abel
    rw [hq_eq, sub_nonneg] at hq
    exact (smul_le_smul_iff_of_pos_left hx_pos).mp hq

/-- The norm Cauchy–Schwarz inequality `‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` for a positive semidefinite module
over a dense `⋆`-subalgebra. -/
theorem norm_inner_le (hι : DenseRange ι) (x y : E) : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hsq : ‖inner A x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
    calc ‖inner A x y‖ ^ 2 = ‖inner A x y * inner A y x‖ := by
            rw [← star_inner (ι := ι) x y, CStarRing.norm_self_mul_star, sq]
      _ ≤ ‖‖x‖ ^ 2 • inner A y y‖ := by
            refine CStarAlgebra.norm_le_norm_of_le_of_nonneg
              (inner_mul_inner_swap_le hι x y) ?_
            rw [← star_inner (ι := ι) x y]
            exact mul_star_self_nonneg _
      _ = (‖x‖ * ‖y‖) ^ 2 := by
            rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _), ← norm_sq_eq (ι := ι) y, mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (PosSemidefCStarModuleAlong.norm_nonneg (ι := ι) x)
      (PosSemidefCStarModuleAlong.norm_nonneg (ι := ι) y)) (by simp)).mp hsq

/-- Triangle inequality for the seminorm `√‖⟪x, x⟫_A‖`. -/
protected theorem norm_triangle (hι : DenseRange ι) (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    calc ‖x + y‖ ^ 2 = ‖inner A (x + y) (x + y)‖ := norm_sq_eq (ι := ι) (x + y)
      _ ≤ ‖inner A x x + inner A y x‖ + ‖inner A x y‖ + ‖inner A y y‖ := by
            rw [inner_add_right (ι := ι), inner_add_left (ι := ι), inner_add_left (ι := ι),
              ← add_assoc]
            exact norm_add₃_le
      _ ≤ ‖inner A x x‖ + ‖inner A y x‖ + ‖inner A x y‖ + ‖inner A y y‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
            rw [← norm_sq_eq (ι := ι) x, ← norm_sq_eq (ι := ι) y]
            gcongr <;> exact norm_inner_le hι _ _
      _ = (‖x‖ + ‖y‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (PosSemidefCStarModuleAlong.norm_nonneg (ι := ι) (x + y))
    (add_nonneg (PosSemidefCStarModuleAlong.norm_nonneg (ι := ι) x)
      (PosSemidefCStarModuleAlong.norm_nonneg (ι := ι) y)) (by simp)).mp h

/-- `SeminormedSpace.Core` induced by a positive semidefinite pairing over a dense
`⋆`-subalgebra. -/
lemma seminormedSpaceCore (hι : DenseRange ι) : SeminormedSpace.Core ℂ E where
  norm_nonneg := PosSemidefCStarModuleAlong.norm_nonneg (ι := ι)
  norm_smul := PosSemidefCStarModuleAlong.norm_smul_complex (ι := ι)
  norm_triangle := PosSemidefCStarModuleAlong.norm_triangle hι

/-- Diagonal inner-product identity for `a₀ • x` in terms of `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_smul (a₀ : A₀) (x : E) :
    inner A (a₀ • x) (a₀ • x) =
      ι a₀ * CFC.sqrt (inner A x x) * star (ι a₀ * CFC.sqrt (inner A x x)) := by
  set s := CFC.sqrt (inner A x x)
  have hs : s * s = inner A x x := CFC.sqrt_mul_sqrt_self _ (inner_self_nonneg (ι := ι))
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  rw [inner_op_smul_left (ι := ι), inner_op_smul_right (ι := ι), star_mul, hs', ← hs]
  noncomm_ring

/-- Norm of `a₀ • x`, measured in `A` via `|x| = CFC.sqrt ⟪x, x⟫_A`; does not require
`DenseRange ι`. -/
protected theorem norm_smul (a₀ : A₀) (x : E) :
    ‖a₀ • x‖ = ‖ι a₀ * CFC.sqrt (inner A x x)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι), inner_smul_smul (ι := ι),
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (norm_nonneg _)]

/-- Bound `‖a₀ • x‖ ≤ ‖ι a₀‖ * ‖x‖`, without requiring `DenseRange ι`. -/
protected theorem norm_smul_le (a₀ : A₀) (x : E) : ‖a₀ • x‖ ≤ ‖ι a₀‖ * ‖x‖ := by
  rw [PosSemidefCStarModuleAlong.norm_smul (ι := ι)]
  refine (norm_mul_le _ _).trans_eq ?_
  rw [CFC.norm_sqrt _ (inner_self_nonneg (ι := ι)), ← norm_eq_sqrt_norm_inner_self (ι := ι)]

/-- Norm bound on `(a₀ • x - b₀ • x)` in terms of `‖ι a₀ - ι b₀‖ * ‖x‖`, even without assuming
additivity of the `A₀`-action on `E`. -/
theorem norm_smul_sub_smul_le {A₀ : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
    {ι : A₀ →⋆ₙₐ[ℂ] A} [SMul A₀ E] [PosSemidefCStarModuleAlong ι E]
    (a₀ b₀ : A₀) (x : E) : ‖a₀ • x - b₀ • x‖ ≤ ‖ι a₀ - ι b₀‖ * ‖x‖ := by
  set s := CFC.sqrt (inner A x x)
  have hs : s * s = inner A x x := CFC.sqrt_mul_sqrt_self _ (inner_self_nonneg (ι := ι))
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hdiag : inner A (a₀ • x - b₀ • x) (a₀ • x - b₀ • x) =
      ((ι a₀ - ι b₀) * s) * star ((ι a₀ - ι b₀) * s) := by
    simp only [inner_sub_left (ι := ι), inner_sub_right (ι := ι),
      inner_op_smul_left (ι := ι), inner_op_smul_right (ι := ι), star_mul, star_sub, hs', ← hs]
    noncomm_ring
  rw [norm_eq_sqrt_norm_inner_self (ι := ι) (a₀ • x - b₀ • x), hdiag,
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (norm_nonneg _)]
  refine (norm_mul_le _ _).trans_eq ?_
  rw [CFC.norm_sqrt _ (inner_self_nonneg (ι := ι)), ← norm_eq_sqrt_norm_inner_self (ι := ι)]

end Analytic

/-! ### Null space and continuity on seminormed modules -/

section Seminormed

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E]

section Module

variable [Module ℂ E] [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E]
  [StarOrderedRing A]

/-- Norm estimate `‖a₀ • x - a₀ • y‖ ≤ ‖ι a₀‖ * ‖x - y‖` in each vector variable. -/
theorem norm_smul_sub_smul_right_le (a₀ : A₀) (x y : E) :
    ‖a₀ • x - a₀ • y‖ ≤ ‖ι a₀‖ * ‖x - y‖ := by
  set w := (a₀ • x - a₀ • y) - a₀ • (x - y)
  have hw : ‖w‖ = 0 := by
    rw [norm_eq_zero_iff_inner_self_eq_zero (ι := ι)]
    simp only [w, inner_sub_right (ι := ι), inner_op_smul_right (ι := ι), mul_sub]
    abel
  calc ‖a₀ • x - a₀ • y‖ = ‖w + a₀ • (x - y)‖ := by simp [w]
    _ ≤ ‖w‖ + ‖a₀ • (x - y)‖ := norm_add_le _ _
    _ ≤ 0 + ‖ι a₀‖ * ‖x - y‖ := by
        rw [hw]
        gcongr
        exact PosSemidefCStarModuleAlong.norm_smul_le (ι := ι) a₀ (x - y)
    _ = ‖ι a₀‖ * ‖x - y‖ := zero_add _

include ι in
/-- Uniform continuity of `x ↦ a₀ • x` on `E` for each `a₀ : A₀`. -/
theorem uniformContinuousConstSMul : UniformContinuousConstSMul A₀ E where
  uniformContinuous_const_smul a₀ := by
    refine Metric.uniformContinuous_iff.mpr fun ε hε ↦ ?_
    refine ⟨ε / (‖ι a₀‖ + 1), div_pos hε (by positivity), fun {x y} hxy ↦ ?_⟩
    rw [dist_eq_norm] at hxy ⊢
    calc ‖a₀ • x - a₀ • y‖ ≤ ‖ι a₀‖ * ‖x - y‖ := norm_smul_sub_smul_right_le (ι := ι) a₀ x y
      _ ≤ (‖ι a₀‖ + 1) * ‖x - y‖ := by gcongr; linarith
      _ < (‖ι a₀‖ + 1) * (ε / (‖ι a₀‖ + 1)) := by gcongr
      _ = ε := mul_div_cancel₀ _ (by positivity)

end Module

section NormedSpace

variable [NormedSpace ℂ E] [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E]

include ι in
/-- Membership in `nullSubmodule ℂ E` is equivalent to `⟪x, x⟫_A = 0`. -/
theorem mem_nullSubmodule_iff_inner_self_eq_zero (x : E) :
    x ∈ nullSubmodule ℂ E ↔ inner A x x = 0 := by
  rw [mem_nullSubmodule_iff, norm_eq_zero_iff_inner_self_eq_zero (ι := ι)]

include ι in
/-- Difference `(a₀ • x - a₀ • y) - a₀ • (x - y)` is always a null vector, even before quotienting
by `nullSubmodule ℂ E`. -/
theorem smul_sub_sub_smul_sub_mem_nullSubmodule (a₀ : A₀) (x y : E) :
    (a₀ • x - a₀ • y) - a₀ • (x - y) ∈ nullSubmodule ℂ E := by
  rw [mem_nullSubmodule_iff_inner_self_eq_zero (ι := ι)]
  simp only [inner_sub_right (ι := ι), inner_op_smul_right (ι := ι), mul_sub]
  abel

variable [StarOrderedRing A]

/-- Under `DenseRange ι`, a vector is null iff it is orthogonal to every vector in the first
slot. -/
theorem mem_nullSubmodule_iff_forall_inner_left (hι : DenseRange ι) (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A y x = 0 := by
  rw [mem_nullSubmodule_iff]
  refine ⟨fun hx y ↦ norm_le_zero_iff.mp ?_, fun h ↦ ?_⟩
  · simpa [hx] using norm_inner_le hι y x
  · rw [norm_eq_zero_iff_inner_self_eq_zero (ι := ι)]
    exact h x

/-- Under `DenseRange ι`, a vector is null iff it is orthogonal to every vector in the second
slot. -/
theorem mem_nullSubmodule_iff_forall_inner_right (hι : DenseRange ι) (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A x y = 0 := by
  rw [mem_nullSubmodule_iff_forall_inner_left hι]
  exact ⟨fun h y ↦ by simpa [star_inner (ι := ι)] using congrArg star (h y),
    fun h y ↦ by simpa [star_inner (ι := ι)] using congrArg star (h y)⟩

include ι in
/-- The `A₀`-action preserves the null submodule `nullSubmodule ℂ E`. -/
theorem smul_mem_nullSubmodule (a₀ : A₀) {x : E} (hx : x ∈ nullSubmodule ℂ E) :
    a₀ • x ∈ nullSubmodule ℂ E := by
  rw [mem_nullSubmodule_iff] at hx ⊢
  have h := PosSemidefCStarModuleAlong.norm_smul_le (ι := ι) a₀ x
  rw [hx, mul_zero] at h
  exact le_antisymm h (norm_nonneg _)

/-- Under `DenseRange ι`, the pairing `⟪·, ·⟫_A` is a continuous sesquilinear map of norm `≤ 1`. -/
noncomputable def innerSL (hι : DenseRange ι) : E →L⋆[ℂ] E →L[ℂ] A :=
  LinearMap.mkContinuous₂ (innerₛₗ ι) 1 fun x y ↦ by
    simpa [innerₛₗ_apply] using norm_inner_le hι x y

@[simp]
lemma innerSL_apply (hι : DenseRange ι) (x y : E) : innerSL hι x y = inner A x y := (rfl)

/-- Joint continuity of `⟪·, ·⟫_A : E × E → A`. -/
theorem continuous_inner (hι : DenseRange ι) : Continuous fun p : E × E ↦ inner A p.1 p.2 := by
  simp_rw [← innerSL_apply hι]
  fun_prop

/-- Inseparable vectors have equal `A`-valued inner products. -/
theorem inseparable_inner_eq (hι : DenseRange ι) {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) :
    inner A x₁ y₁ = inner A x₂ y₂ :=
  ((hx.prod hy).map (continuous_inner hι)).eq

end NormedSpace

end Seminormed

end PosSemidefCStarModuleAlong

/-! ### Specializations and `Core` constructors for `PosSemidefCStarModule` -/

namespace PosSemidefCStarModule

section DenseCore

/-- Data constructing a positive semidefinite module over `A₀` along `ι : A₀ →⋆ₙₐ[ℂ] A` on a type
`E` that carries no pre-existing seminorm. Determined extensionally by its `A`-valued pairing. -/
structure DenseCore {A₀ A : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
    (ι : A₀ →⋆ₙₐ[ℂ] A) (E : Type*) [AddCommGroup E] [Module ℂ E] [SMul A₀ E]
    extends Inner A E where
  inner_add_right {x y z : E} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x : E} : 0 ≤ inner x x
  inner_op_smul_right {a₀ : A₀} {x y : E} : inner x (a₀ • y) = ι a₀ * inner x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner x (z • y) = z • inner x y
  star_inner (x y : E) : star (inner x y) = inner y x

/-- Data constructing a positive semidefinite `A`-module on a type `E` with no pre-existing
seminorm. -/
abbrev Core (A E : Type*) [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] :=
  DenseCore (NonUnitalStarAlgHom.id ℂ A) E

/-- Extract the underlying `Core A E` from a `PosSemidefCStarModule A E`. -/
def Core.ofPosSemidefCStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
    [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] : Core A E where
  toInner := inferInstance
  inner_add_right := PosSemidefCStarModule.inner_add_right
  inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg
  inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right
  inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex
  star_inner := PosSemidefCStarModule.star_inner

namespace DenseCore

section General

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E]

/-- Two `DenseCore` structures are equal iff their inner products agree everywhere. -/
@[ext]
theorem ext {c₁ c₂ : DenseCore ι E} (h : ∀ x y, c₁.inner x y = c₂.inner x y) : c₁ = c₂ := by
  rcases c₁ with ⟨⟨i₁⟩, _, _, _, _, _⟩
  rcases c₂ with ⟨⟨i₂⟩, _, _, _, _, _⟩
  congr
  ext x y
  exact h x y

/-- Pull a `DenseCore` back along a complex-linear `A₀`-equivariant map `f : F →ₗ[ℂ] E`. When `f`
has nontrivial kernel, this produces a genuinely indefinite positive semidefinite module with null
space containing `LinearMap.ker f`. -/
def comap {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A₀ F] (c : DenseCore ι E)
    (f : F →ₗ[ℂ] E) (hf : ∀ (a₀ : A₀) (x : F), f (a₀ • x) = a₀ • f x) : DenseCore ι F where
  inner x y := c.inner (f x) (f y)
  inner_add_right := by simp [c.inner_add_right]
  inner_self_nonneg := c.inner_self_nonneg
  inner_op_smul_right := by simp [hf, c.inner_op_smul_right]
  inner_smul_right_complex := by simp [c.inner_smul_right_complex]
  star_inner x y := c.star_inner (f x) (f y)

@[simp]
theorem comap_inner {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A₀ F] (c : DenseCore ι E)
    (f : F →ₗ[ℂ] E) (hf : ∀ (a₀ : A₀) (x : F), f (a₀ • x) = a₀ • f x) (x y : F) :
    (c.comap f hf).inner x y = c.inner (f x) (f y) :=
  (rfl)

/-- Build a `DenseCore ι E` from an `A₀`-valued pairing `inner₀ : E → E → A₀` whose positivity
`0 ≤ ι (inner₀ x x)` is measured in the target `A` along `ι : A₀ →⋆ₙₐ[ℂ] A`. -/
def ofInnerHom (ι : A₀ →⋆ₙₐ[ℂ] A) (inner₀ : E → E → A₀)
    (hadd : ∀ x y z, inner₀ x (y + z) = inner₀ x y + inner₀ x z)
    (hpos : ∀ x, 0 ≤ ι (inner₀ x x))
    (hsmul : ∀ (a₀ : A₀) (x y : E), inner₀ x (a₀ • y) = a₀ * inner₀ x y)
    (hc : ∀ (z : ℂ) (x y : E), inner₀ x (z • y) = z • inner₀ x y)
    (hstar : ∀ x y, star (inner₀ x y) = inner₀ y x) : DenseCore ι E where
  inner x y := ι (inner₀ x y)
  inner_add_right := by simp [hadd]
  inner_self_nonneg := hpos _
  inner_op_smul_right := by simp [hsmul]
  inner_smul_right_complex := by simp [hc]
  star_inner x y := by rw [← map_star, hstar]

@[simp]
theorem ofInnerHom_inner (ι : A₀ →⋆ₙₐ[ℂ] A) (inner₀ : E → E → A₀)
    (hadd : ∀ x y z, inner₀ x (y + z) = inner₀ x y + inner₀ x z)
    (hpos : ∀ x, 0 ≤ ι (inner₀ x x))
    (hsmul : ∀ (a₀ : A₀) (x y : E), inner₀ x (a₀ • y) = a₀ * inner₀ x y)
    (hc : ∀ (z : ℂ) (x y : E), inner₀ x (z • y) = z • inner₀ x y)
    (hstar : ∀ x y, star (inner₀ x y) = inner₀ y x) (x y : E) :
    (ofInnerHom ι inner₀ hadd hpos hsmul hc hstar).inner x y = ι (inner₀ x y) :=
  (rfl)

end General

section NormConstruction

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E]

/-- Norm `‖x‖ = √‖c.inner x x‖` induced by a `DenseCore`. Not registered as an instance to avoid
colliding with pre-existing norms. -/
noncomputable abbrev toNorm (c : DenseCore ι E) : Norm E :=
  @CStarModule.norm A E _ c.toInner

/-- `PosSemidefCStarModuleAlong` satisfied by `c` with respect to `c.toInner` and `c.toNorm`. -/
theorem toPosSemidefCStarModuleAlong (c : DenseCore ι E) :
    @PosSemidefCStarModuleAlong A₀ A _ _ _ _ _ _ _ _ ι E _ _ _ c.toNorm c.toInner :=
  let : Inner A E := c.toInner
  let : Norm E := c.toNorm
  { inner_add_right := c.inner_add_right
    inner_self_nonneg := c.inner_self_nonneg
    inner_op_smul_right := c.inner_op_smul_right
    inner_smul_right_complex := c.inner_smul_right_complex
    star_inner := c.star_inner
    norm_eq_sqrt_norm_inner_self := fun _ ↦ rfl }

variable [StarOrderedRing A]

/-- `SeminormedSpace.Core ℂ E` constructed from `c` when `ι` has dense range. -/
theorem toSeminormedSpaceCore (c : DenseCore ι E) (hι : DenseRange ι) :
    @SeminormedSpace.Core ℂ E _ _ c.toNorm _ :=
  let : Inner A E := c.toInner
  let : Norm E := c.toNorm
  have : PosSemidefCStarModuleAlong ι E := c.toPosSemidefCStarModuleAlong
  PosSemidefCStarModuleAlong.seminormedSpaceCore hι

/-- `SeminormedAddCommGroup E` constructed from `c` when `ι` has dense range. -/
noncomputable abbrev toSeminormedAddCommGroup (c : DenseCore ι E) (hι : DenseRange ι) :
    SeminormedAddCommGroup E :=
  letI : Norm E := c.toNorm
  SeminormedAddCommGroup.ofCore (c.toSeminormedSpaceCore hι)

/-- `NormedSpace ℂ E` constructed from `c` when `ι` has dense range. -/
noncomputable abbrev toNormedSpace (c : DenseCore ι E) (hι : DenseRange ι) :
    @NormedSpace ℂ E _ (c.toSeminormedAddCommGroup hι) :=
  letI : SeminormedAddCommGroup E := c.toSeminormedAddCommGroup hι
  { norm_smul_le r x := ((c.toSeminormedSpaceCore hι).norm_smul r x).le }

end NormConstruction

end DenseCore

/-- Build a `PosSemidefCStarModule A E` from `c : Core A E` on `c.toSeminormedAddCommGroup`. -/
noncomputable abbrev Core.toPosSemidefCStarModule {A E : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommGroup E] [Module ℂ E] [SMul A E]
    (c : Core A E) :
    @PosSemidefCStarModule A E _ _ _ _ _ _ _ _
      (c.toSeminormedAddCommGroup denseRange_id).toNorm :=
  letI : SeminormedAddCommGroup E := c.toSeminormedAddCommGroup denseRange_id
  { toInner := c.toInner
    inner_add_right := c.inner_add_right
    inner_self_nonneg := c.inner_self_nonneg
    inner_op_smul_right := c.inner_op_smul_right
    inner_smul_right_complex := c.inner_smul_right_complex
    star_inner := c.star_inner
    norm_eq_sqrt_norm_inner_self := fun _ ↦ rfl }

end DenseCore

/-! ### Direct API for `PosSemidefCStarModule A E` -/

section Direct

section Algebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
  [PosSemidefCStarModule A E]

@[simp]
lemma inner_add_left {x y z : E} : inner A (x + y) z = inner A x z + inner A y z :=
  PosSemidefCStarModuleAlong.inner_add_left (ι := NonUnitalStarAlgHom.id ℂ A) x y z

@[simp]
lemma inner_op_smul_left {a : A} {x y : E} : inner A (a • x) y = inner A x y * star a :=
  PosSemidefCStarModuleAlong.inner_op_smul_left (ι := NonUnitalStarAlgHom.id ℂ A) a x y

variable [StarModule ℂ A]

@[simp]
lemma inner_smul_left_complex {z : ℂ} {x y : E} : inner A (z • x) y = star z • inner A x y :=
  PosSemidefCStarModuleAlong.inner_smul_left_complex (ι := NonUnitalStarAlgHom.id ℂ A) z x y

@[simp]
lemma inner_zero_right {x : E} : inner A x 0 = 0 :=
  PosSemidefCStarModuleAlong.inner_zero_right (ι := NonUnitalStarAlgHom.id ℂ A) x

@[simp]
lemma inner_zero_left {x : E} : inner A 0 x = 0 :=
  PosSemidefCStarModuleAlong.inner_zero_left (ι := NonUnitalStarAlgHom.id ℂ A) x

@[simp]
lemma inner_neg_right {x y : E} : inner A x (-y) = -inner A x y :=
  PosSemidefCStarModuleAlong.inner_neg_right (ι := NonUnitalStarAlgHom.id ℂ A) x y

@[simp]
lemma inner_neg_left {x y : E} : inner A (-x) y = -inner A x y :=
  PosSemidefCStarModuleAlong.inner_neg_left (ι := NonUnitalStarAlgHom.id ℂ A) x y

@[simp]
lemma inner_sub_right {x y z : E} : inner A x (y - z) = inner A x y - inner A x z :=
  PosSemidefCStarModuleAlong.inner_sub_right (ι := NonUnitalStarAlgHom.id ℂ A) x y z

@[simp]
lemma inner_sub_left {x y z : E} : inner A (x - y) z = inner A x z - inner A y z :=
  PosSemidefCStarModuleAlong.inner_sub_left (ι := NonUnitalStarAlgHom.id ℂ A) x y z

/-- Any complex-linear map from `PosSemidefCStarModule A E` to `CStarModule A F` preserving
`inner A` automatically commutes with the `A`-action. -/
theorem map_smul_of_inner_eq {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a : A) (x : E) : f (a • x) = a • f x :=
  PosSemidefCStarModuleAlong.map_smul_of_inner_eq (ι := NonUnitalStarAlgHom.id ℂ A) f hf a x

end Algebraic

section Norm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- On a separated normed space (`NormedAddCommGroup E`), any `PosSemidefCStarModule A E` is
automatically definite, hence a `CStarModule A E`. -/
abbrev toCStarModuleOfNormedAddCommGroup {E : Type*} [NormedAddCommGroup E] [Module ℂ E]
    [SMul A E] [PosSemidefCStarModule A E] : CStarModule A E :=
  toCStarModule fun x hx ↦ norm_eq_zero.mp <|
    (PosSemidefCStarModuleAlong.norm_eq_zero_iff_inner_self_eq_zero
      (ι := NonUnitalStarAlgHom.id ℂ A) x).mpr hx

variable [StarOrderedRing A]

section AddCommGroup

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [PosSemidefCStarModule A E]

/-- C⋆-algebra Cauchy–Schwarz inequality for `PosSemidefCStarModule A E`. -/
theorem inner_mul_inner_swap_le (x y : E) :
    inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y :=
  PosSemidefCStarModuleAlong.inner_mul_inner_swap_le
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id x y

/-- Norm Cauchy–Schwarz inequality `‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` for `PosSemidefCStarModule A E`. -/
theorem norm_inner_le (x y : E) : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ :=
  PosSemidefCStarModuleAlong.norm_inner_le (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id x y

include A in
/-- `SeminormedSpace.Core ℂ E` induced by `PosSemidefCStarModule A E`. -/
lemma seminormedSpaceCore : SeminormedSpace.Core ℂ E :=
  PosSemidefCStarModuleAlong.seminormedSpaceCore (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id

/-- Bound `‖a • x‖ ≤ ‖a‖ * ‖x‖` on a positive semidefinite `A`-module. -/
protected theorem norm_smul_le (a : A) (x : E) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ :=
  PosSemidefCStarModuleAlong.norm_smul_le (ι := NonUnitalStarAlgHom.id ℂ A) a x

end AddCommGroup

section Seminormed

variable [SeminormedAddCommGroup E]

/-- Jointly bounded action `IsBoundedSMul A E` on a positive semidefinite `A`-module. -/
instance instIsBoundedSMul [Module ℂ E] [SMul A E] [PosSemidefCStarModule A E] :
    IsBoundedSMul A E where
  dist_smul_pair' a x y := by
    simp only [dist_eq_norm, sub_zero]
    exact PosSemidefCStarModuleAlong.norm_smul_sub_smul_right_le
      (ι := NonUnitalStarAlgHom.id ℂ A) a x y
  dist_pair_smul' a b x := by
    simp only [dist_eq_norm, sub_zero]
    exact PosSemidefCStarModuleAlong.norm_smul_sub_smul_le
      (ι := NonUnitalStarAlgHom.id ℂ A) a b x

@[continuity, fun_prop]
theorem continuous_inner [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E] :
    Continuous fun p : E × E ↦ inner A p.1 p.2 :=
  PosSemidefCStarModuleAlong.continuous_inner (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id

end Seminormed

end Norm

end Direct

end PosSemidefCStarModule

end TauCeti

/-! ### Concrete witnesses: complex pre-inner product spaces and `⋆`-subalgebra self-modules -/

/-- Any complex seminormed `InnerProductSpace ℂ E` (possibly with nonzero null vectors) is a
`PosSemidefCStarModule ℂ E`, generalizing `WithCStarModule.instCStarModuleComplex`. -/
noncomputable instance WithCStarModule.instPosSemidefCStarModuleComplex {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] : TauCeti.PosSemidefCStarModule ℂ E where
  inner x y := ⟪x, y⟫_ℂ
  inner_add_right := by simp [_root_.inner_add_right]
  inner_self_nonneg {x} := by
    rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_op_smul_right := by simp [inner_smul_right]
  inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self x := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x

/-- A `NonUnitalStarSubalgebra ℂ A` of a C⋆-algebra `A` is a right module over itself (`Sᵐᵒᵖ`)
whose `Aᵐᵒᵖ`-valued inner product `⟨x, y⟩_A = star x * y` has positivity and norm measured in `A`
along `(NonUnitalStarSubalgebraClass.subtype S).op`. -/
noncomputable def NonUnitalStarSubalgebra.rightModuleDenseCore {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (S : NonUnitalStarSubalgebra ℂ A) :
    TauCeti.PosSemidefCStarModule.DenseCore
      (NonUnitalStarSubalgebraClass.subtype S).op S where
  inner x y := op (star (x : A) * (y : A))
  inner_add_right := by simp [mul_add]
  inner_self_nonneg := op_nonneg.mpr (star_mul_self_nonneg _)
  inner_op_smul_right {s x y} := by
    obtain ⟨s, rfl⟩ := MulOpposite.op_surjective s
    apply unop_injective
    simp [mul_assoc]
  inner_smul_right_complex := by simp [mul_smul_comm]
  star_inner _ _ := by simp

@[simp]
theorem NonUnitalStarSubalgebra.rightModuleDenseCore_inner {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (S : NonUnitalStarSubalgebra ℂ A) (x y : S) :
    S.rightModuleDenseCore.inner x y = op (star (x : A) * (y : A)) :=
  (rfl)

-- Concrete witness that `PosSemidefCStarModule` admits genuinely indefinite pairings with nonzero
-- null vectors: pulling back any `CStarModule A E` along `LinearMap.fst` to `E × F` makes `(0, y)`
-- a nonzero null vector whenever `y ≠ 0`.
example {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [SMul A F] (y : F) (hy : y ≠ 0) :
    let c : TauCeti.PosSemidefCStarModule.Core A (E × F) :=
      (TauCeti.PosSemidefCStarModule.Core.ofPosSemidefCStarModule A E).comap
        (LinearMap.fst ℂ E F) (fun _ _ ↦ rfl)
    letI := c.toSeminormedAddCommGroup denseRange_id
    letI := c.toPosSemidefCStarModule
    ((0, y) : E × F) ≠ 0 ∧ inner A ((0, y) : E × F) (0, y) = 0 := by
  refine ⟨by simp [hy], ?_⟩
  -- Unfold the pulled-back pairing `(c.comap fst _).inner (0, y) (0, y) = inner A 0 0`.
  change inner A (0 : E) 0 = 0
  exact CStarModule.inner_zero_right

/-! ### Separated quotient and its universal properties -/

namespace SeparationQuotient

open TauCeti

section Along

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]

/-- Descend the `A`-valued inner product of a positive semidefinite module along a dense
`⋆`-homomorphism `ι` to `SeparationQuotient E`. -/
@[instance_reducible]
noncomputable def innerOfAlong (hι : DenseRange ι) : Inner A (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner A) fun _ _ _ _ ↦
    PosSemidefCStarModuleAlong.inseparable_inner_eq hι

/-- Descend the `A₀`-action to `SeparationQuotient E` (requires no `DenseRange` assumption). -/
@[instance_reducible]
noncomputable def smulOfAlong (ι : A₀ →⋆ₙₐ[ℂ] A) [PosSemidefCStarModuleAlong ι E] :
    SMul A₀ (SeparationQuotient E) :=
  haveI : UniformContinuousConstSMul A₀ E :=
    PosSemidefCStarModuleAlong.uniformContinuousConstSMul (ι := ι)
  inferInstance

/-- On `SeparationQuotient E`, `innerOfAlong` and `smulOfAlong` form a definite pre-Hilbert module
over `A₀` along `ι`: `⟪z, z⟫_A = 0 ↔ z = 0` holds in addition to `PosSemidefCStarModuleAlong`. -/
theorem posSemidefCStarModuleAlong (hι : DenseRange ι) :
    @PosSemidefCStarModuleAlong A₀ A _ _ _ _ _ _ _ _ ι (SeparationQuotient E) _ _
      (smulOfAlong ι) _ (innerOfAlong hι) := by
  let : Inner A (SeparationQuotient E) := innerOfAlong hι
  let : SMul A₀ (SeparationQuotient E) := smulOfAlong ι
  have : UniformContinuousConstSMul A₀ E :=
    PosSemidefCStarModuleAlong.uniformContinuousConstSMul (ι := ι)
  refine
    { inner_add_right := fun {x y z} ↦ ?_
      inner_self_nonneg := fun {x} ↦ ?_
      inner_op_smul_right := fun {a₀ x y} ↦ ?_
      inner_smul_right_complex := fun {z x y} ↦ ?_
      star_inner := fun x y ↦ ?_
      norm_eq_sqrt_norm_inner_self := fun x ↦ ?_ }
  · obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    obtain ⟨z, rfl⟩ := surjective_mk z
    exact PosSemidefCStarModuleAlong.inner_add_right (ι := ι) (x := x) (y := y) (z := z)
  · obtain ⟨x, rfl⟩ := surjective_mk x
    exact PosSemidefCStarModuleAlong.inner_self_nonneg (ι := ι) (x := x)
  · obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    -- Rewrite `a₀ • mk y = mk (a₀ • y)` on `SeparationQuotient E` and reduce to `E`.
    rw [← mk_smul]
    exact PosSemidefCStarModuleAlong.inner_op_smul_right (ι := ι)
  · obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    rw [← mk_smul]
    exact PosSemidefCStarModuleAlong.inner_smul_right_complex (ι := ι)
  · obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    exact PosSemidefCStarModuleAlong.star_inner (ι := ι) x y
  · obtain ⟨x, rfl⟩ := surjective_mk x
    rw [norm_mk]
    exact PosSemidefCStarModuleAlong.norm_eq_sqrt_norm_inner_self (ι := ι) x

end Along

section Direct

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

section StarOrdered

variable [StarOrderedRing A]

/-- `A`-valued inner product on the separated quotient of a positive semidefinite `A`-module. -/
noncomputable instance instInnerCStarModule : Inner A (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner A) fun _ _ _ _ ↦
    PosSemidefCStarModuleAlong.inseparable_inner_eq
      (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id

@[simp]
theorem cstarInner_mk_mk (x y : E) : inner A (mk x) (mk y) = inner A x y :=
  (rfl)

/-- The separated quotient of a positive semidefinite `A`-module is a pre-Hilbert `A`-module
(`CStarModule A (SeparationQuotient E)`). -/
noncomputable instance instCStarModule : CStarModule A (SeparationQuotient E) where
  toInner := instInnerCStarModule
  inner_add_right {x y z} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    obtain ⟨z, rfl⟩ := surjective_mk z
    rw [← mk_add, cstarInner_mk_mk, cstarInner_mk_mk, cstarInner_mk_mk,
      PosSemidefCStarModule.inner_add_right]
  inner_self_nonneg {x} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    exact PosSemidefCStarModule.inner_self_nonneg (x := x)
  inner_self {x} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    rw [cstarInner_mk_mk, ← norm_eq_zero (a := mk x), norm_mk,
      PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
      Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]
  inner_op_smul_right {a x y} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    rw [← mk_smul, cstarInner_mk_mk, cstarInner_mk_mk,
      PosSemidefCStarModule.inner_op_smul_right]
  inner_smul_right_complex {z x y} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    rw [← mk_smul, cstarInner_mk_mk, cstarInner_mk_mk,
      PosSemidefCStarModule.inner_smul_right_complex]
  star_inner x y := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    obtain ⟨y, rfl⟩ := surjective_mk y
    exact PosSemidefCStarModule.star_inner x y
  norm_eq_sqrt_norm_inner_self x := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    rw [norm_mk, cstarInner_mk_mk,
      PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]

-- Ensures that at `A = ℂ`, `SeparationQuotient.instCStarModule` is definitionally equal to
-- `WithCStarModule.instCStarModuleComplex` on `SeparationQuotient H`.
example {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (SeparationQuotient H)) =
      WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

end StarOrdered

/-! #### Universal property of `SeparationQuotient E` for inner-product-preserving maps -/

/-- **Universal property of `SeparationQuotient E` for inner-product-preserving maps:** any
`ℂ`-linear map `f : E →ₗ[ℂ] F` into a pre-Hilbert `A`-module `F` preserving `inner A` lifts to a
linear isometry `SeparationQuotient E →ₗᵢ[ℂ] F`, without assuming continuity or `A`-linearity of
`f` in advance. -/
noncomputable def liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    SeparationQuotient E →ₗᵢ[ℂ] F := by
  have hnorm (x : E) : ‖f x‖ = ‖x‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
      PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]
  let fCLM : E →L[ℂ] F := f.mkContinuous 1 fun x ↦ by rw [one_mul, hnorm]
  have hinsep : ∀ x y : E, Inseparable x y → fCLM x = fCLM y :=
    fun _ _ h ↦ (h.map fCLM.continuous).eq
  exact
    { liftCLM fCLM hinsep with
      norm_map' := surjective_mk.forall.2 fun x ↦ by
        rw [ContinuousLinearMap.coe_coe, liftCLM_mk, norm_mk]
        exact hnorm x }

@[simp]
theorem liftOfInner_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (x : E) : liftOfInner f hf (mk x) = f x :=
  (rfl)

/-- Uniqueness of `liftOfInner`: `liftOfInner f hf` is the unique map on `SeparationQuotient E`
factoring `f` through `SeparationQuotient.mk`. -/
theorem eq_liftOfInner_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (g : SeparationQuotient E →ₗᵢ[ℂ] F) :
    g = liftOfInner f hf ↔ ∀ x : E, g (mk x) = f x := by
  refine ⟨fun h x ↦ by rw [h, liftOfInner_mk], fun h ↦ ?_⟩
  ext u
  obtain ⟨x, rfl⟩ := surjective_mk u
  rw [h, liftOfInner_mk]

section StarOrderedLift

variable [StarOrderedRing A]

@[simp]
theorem inner_liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (u v : SeparationQuotient E) :
    inner A (liftOfInner f hf u) (liftOfInner f hf v) = inner A u v := by
  obtain ⟨x, rfl⟩ := surjective_mk u
  obtain ⟨y, rfl⟩ := surjective_mk v
  exact hf x y

/-- The lifted isometry `liftOfInner f hf` automatically commutes with the `A`-action. -/
@[simp]
theorem liftOfInner_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
    [CStarModule A F] (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a : A) (u : SeparationQuotient E) :
    liftOfInner f hf (a • u) = a • liftOfInner f hf u := by
  obtain ⟨x, rfl⟩ := surjective_mk u
  rw [← mk_smul, liftOfInner_mk, liftOfInner_mk,
    PosSemidefCStarModule.map_smul_of_inner_eq f hf a x]

end StarOrderedLift

end Direct

end SeparationQuotient
