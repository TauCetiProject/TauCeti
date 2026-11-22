/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Positive semidefinite C⋆-modules, dense `⋆`-subalgebra actions, and separated quotients

`PosSemidefCStarModule A E` drops definiteness `⟪x, x⟫_A = 0 ↔ x = 0` from `CStarModule A E`.
For `ι : A₀ →⋆ₙₐ[ℂ] A` into a C⋆-algebra `A`, `IsPosSemidefCStarModuleAlong ι E` records a positive
semidefinite `A`-valued pairing on an `A₀`-module `E` with `⟪x, a₀ • y⟫_A = ι a₀ * ⟪x, y⟫_A` and
`‖x‖ = √‖⟪x, x⟫_A‖`, assuming no norm or order on `A₀`; `CoreAlong` and `Core` build the seminormed
structure when `DenseRange ι`, and `SeparationQuotient E` kills null vectors.

## Main declarations

* `TauCeti.PosSemidefCStarModule`, `TauCeti.IsPosSemidefCStarModuleAlong`, `CoreAlong`, `Core`.
* `TauCeti.IsPosSemidefCStarModuleAlong.inner_mul_inner_swap_le`, `norm_inner_le`,
  `map_smul_of_inner_eq`: C⋆-algebra and norm Cauchy–Schwarz inequalities without definiteness, and
  automatic `A₀`-equivariance of inner-product-preserving maps into definite C⋆-modules.
* `TauCeti.IsPosSemidefCStarModuleAlong.linearIsometryOfInner`: any plain inner-product-preserving
  map into a definite C⋆-module is a `ℂ`-linear isometry; `inner_map_polarization` and
  `of_map_inner` give polarization for maps and a constructor from an `A₀`-valued form.
* `TauCeti.PosSemidefCStarModule.star_unop_inner_mul_unop_inner_le`, `norm_unop_inner_le`,
  `norm_op_smul_le`: right-module Cauchy–Schwarz and action bounds without definiteness.
* `TauCeti.PosSemidefCStarModule.rightModuleCoreAlong`, `isPosSemidefCStarModuleAlong_op`, and
  scoped instances `TauCeti.IsPosSemidefCStarModuleAlong.instInnerRightModule`,
  `instIsPosSemidefCStarModuleAlongOp`.
* `SeparationQuotient.instCStarModule`, `separationQuotientInner`, `separationQuotientSMul`,
  `separationQuotientLiftOfInner`: separated-quotient structure and universal property.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2, Lemma 2.16.
* `inner_mul_inner_swap_le` and `norm_inner_le` adapt `CStarModule.inner_mul_inner_swap_le` and
  `CStarModule.norm_inner_le` (`Mathlib.Analysis.CStarAlgebra.Module.Defs`), extended by density
  along `ι` and a `t → 0⁺` limit for null vectors.
-/

public section

open MulOpposite Complex
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

/-! ### Classes for positive semidefinite modules and dense `⋆`-subalgebra actions -/

/-- A positive semidefinite C⋆-module over `A`: a complex module `E` with an action of `A` and an
`A`-valued positive semidefinite inner product inducing `‖x‖ = √‖⟪x, x⟫_A‖`, without assuming
`⟪x, x⟫_A = 0 ↔ x = 0`. For right `B`-modules, take `A = Bᵐᵒᵖ`. -/
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
    [CStarModule A E] : PosSemidefCStarModule A E :=
  { toInner := inferInstance, inner_add_right := CStarModule.inner_add_right,
    inner_self_nonneg := CStarModule.inner_self_nonneg,
    inner_op_smul_right := CStarModule.inner_op_smul_right,
    inner_smul_right_complex := CStarModule.inner_smul_right_complex,
    star_inner := CStarModule.star_inner,
    norm_eq_sqrt_norm_inner_self := CStarModule.norm_eq_sqrt_norm_inner_self }

/-- A positive semidefinite `A`-module satisfying `⟪x, x⟫_A = 0 → x = 0` is a `CStarModule A E`. -/
abbrev PosSemidefCStarModule.toCStarModule {A E : Type*} [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] (hdef : ∀ x : E, inner A x x = 0 → x = 0) : CStarModule A E :=
  { toInner := inferInstance, inner_add_right := PosSemidefCStarModule.inner_add_right,
    inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg,
    inner_self := fun {x} ↦ ⟨hdef x, by
      rintro rfl
      have h := PosSemidefCStarModule.inner_add_right (A := A) (x := (0 : E)) (y := 0) (z := 0)
      rw [add_zero] at h; exact add_eq_left.mp h.symm⟩,
    inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right,
    inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex,
    star_inner := PosSemidefCStarModule.star_inner,
    norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self }

/-- A positive semidefinite module over `A₀` along `ι : A₀ →⋆ₙₐ[ℂ] A`, where positivity and
seminorm `‖x‖ = √‖⟪x, x⟫_A‖` are measured in `A` (requiring no norm or order on `A₀`). -/
class IsPosSemidefCStarModuleAlong {A₀ A : Type*} [NonUnitalSemiring A₀] [StarRing A₀]
    [Module ℂ A₀] [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    (ι : A₀ →⋆ₙₐ[ℂ] A) (E : Type*) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E]
    [Inner A E] : Prop where
  inner_add_right {x y z : E} : inner A x (y + z) = inner A x y + inner A x z
  inner_self_nonneg {x : E} : 0 ≤ inner A x x
  inner_op_smul_right {a₀ : A₀} {x y : E} : inner A x (a₀ • y) = ι a₀ * inner A x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner A x (z • y) = z • inner A x y
  star_inner (x y : E) : star (inner A x y) = inner A y x
  norm_eq_sqrt_norm_inner_self (x : E) : ‖x‖ = √‖inner A x x‖

/-- A `PosSemidefCStarModule A E` satisfies `IsPosSemidefCStarModuleAlong` for `id` on `A`. -/
instance PosSemidefCStarModule.instAlongId {A E : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] : IsPosSemidefCStarModuleAlong (NonUnitalStarAlgHom.id ℂ A) E :=
  { inner_add_right := PosSemidefCStarModule.inner_add_right,
    inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg,
    inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right,
    inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex,
    star_inner := PosSemidefCStarModule.star_inner,
    norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self }

/-- Restricting the scalar action of `PosSemidefCStarModule A E` to a `⋆`-subsemiring `s` of `A`
yields `IsPosSemidefCStarModuleAlong` along `NonUnitalStarSubalgebraClass.subtype s`. -/
instance PosSemidefCStarModule.instAlongSubalgebra {A E S : Type*} [NonUnitalSemiring A]
    [StarRing A] [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E]
    [Norm A] [Norm E] [PosSemidefCStarModule A E] [SetLike S A]
    [NonUnitalSubsemiringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] (s : S) :
    IsPosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype s) E :=
  { inner_add_right := PosSemidefCStarModule.inner_add_right,
    inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg,
    inner_op_smul_right := fun {r _ _} ↦ PosSemidefCStarModule.inner_op_smul_right (a := (r : A)),
    inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex,
    star_inner := PosSemidefCStarModule.star_inner,
    norm_eq_sqrt_norm_inner_self := PosSemidefCStarModule.norm_eq_sqrt_norm_inner_self }

/-- Build `IsPosSemidefCStarModuleAlong ι E` from an `A₀`-valued sesquilinear form whose images
`ι ⟪x, x⟫_{A₀}` are nonnegative in `A`, when the `A`-valued pairing is `ι ∘ ⟪·, ·⟫_{A₀}`. -/
theorem IsPosSemidefCStarModuleAlong.of_map_inner {A₀ A E : Type*}
    [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    (ι : A₀ →⋆ₙₐ[ℂ] A) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E]
    [Inner A₀ E] [Inner A E]
    (hmap : ∀ x y : E, inner A x y = ι (inner A₀ x y))
    (hadd : ∀ x y z : E, inner A₀ x (y + z) = inner A₀ x y + inner A₀ x z)
    (hnonneg : ∀ x : E, 0 ≤ ι (inner A₀ x x))
    (hsmul : ∀ (a₀ : A₀) (x y : E), inner A₀ x (a₀ • y) = a₀ * inner A₀ x y)
    (hcpx : ∀ (z : ℂ) (x y : E), inner A₀ x (z • y) = z • inner A₀ x y)
    (hstar : ∀ x y : E, star (inner A₀ x y) = inner A₀ y x)
    (hnorm : ∀ x : E, ‖x‖ = √‖ι (inner A₀ x x)‖) : IsPosSemidefCStarModuleAlong ι E where
  inner_add_right := by simp [hmap, hadd]
  inner_self_nonneg {x} := by rw [hmap]; exact hnonneg x
  inner_op_smul_right := by simp [hmap, hsmul]
  inner_smul_right_complex := by simp [hmap, hcpx]
  star_inner x y := by rw [hmap, hmap, ← map_star, hstar]
  norm_eq_sqrt_norm_inner_self x := by rw [hmap, hnorm]

namespace IsPosSemidefCStarModuleAlong

/-! ### Algebraic consequences -/

section Algebraic

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  (ι : A₀ →⋆ₙₐ[ℂ] A) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E]
include ι

lemma inner_add_left (x y z : E) : inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_star (r := inner A (x + y) z), star_inner (ι := ι), inner_add_right (ι := ι),
    star_add, star_inner (ι := ι), star_inner (ι := ι)]
lemma inner_op_smul_left (a₀ : A₀) (x y : E) :
    inner A (a₀ • x) y = inner A x y * star (ι a₀) := by
  rw [← star_star (r := inner A (a₀ • x) y), star_inner (ι := ι), inner_op_smul_right (ι := ι),
    star_mul, star_inner (ι := ι)]
lemma isSelfAdjoint_inner_self (x : E) : IsSelfAdjoint (inner A x x) := star_inner (ι := ι) x x
lemma inner_smul_right_real (r : ℝ) (x y : E) : inner A x (r • y) = r • inner A x y := by
  simpa only [coe_smul] using inner_smul_right_complex (ι := ι) (z := (r : ℂ)) (x := x) (y := y)

variable [StarModule ℂ A]

lemma inner_smul_left_complex (z : ℂ) (x y : E) :
    inner A (z • x) y = star z • inner A x y := by
  rw [← star_star (r := inner A (z • x) y), star_inner (ι := ι),
    inner_smul_right_complex (ι := ι), star_smul, star_inner (ι := ι)]
lemma inner_smul_left_real (r : ℝ) (x y : E) : inner A (r • x) y = r • inner A x y := by
  simpa only [coe_smul, Complex.star_def, conj_ofReal] using inner_smul_left_complex ι (r : ℂ) x y

/-- The pairing `⟪x, y⟫_A` bundled as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A where
  toFun x := ⟨⟨inner A x, fun _ _ ↦ inner_add_right (ι := ι)⟩,
    fun _ _ ↦ inner_smul_right_complex (ι := ι)⟩
  map_add' x y := LinearMap.ext <| inner_add_left ι x y
  map_smul' c x := LinearMap.ext <| inner_smul_left_complex ι c x

@[simp] lemma innerₛₗ_apply (x y : E) : innerₛₗ ι x y = inner A x y := (rfl)
lemma inner_zero_right (x : E) : inner A x 0 = 0 := map_zero (innerₛₗ ι x)
lemma inner_zero_left (x : E) : inner A 0 x = 0 := LinearMap.congr_fun (map_zero (innerₛₗ ι)) x
lemma inner_neg_right (x y : E) : inner A x (-y) = -inner A x y := map_neg (innerₛₗ ι x) y
lemma inner_neg_left (x y : E) : inner A (-x) y = -inner A x y :=
  LinearMap.congr_fun (map_neg (innerₛₗ ι) x) y
lemma inner_sub_right (x y z : E) : inner A x (y - z) = inner A x y - inner A x z :=
  map_sub (innerₛₗ ι x) y z
lemma inner_sub_left (x y z : E) : inner A (x - y) z = inner A x z - inner A y z :=
  LinearMap.congr_fun (map_sub (innerₛₗ ι) x y) z
lemma inner_sum_right {κ : Type*} (s : Finset κ) (x : E) (y : κ → E) :
    inner A x (∑ i ∈ s, y i) = ∑ i ∈ s, inner A x (y i) := map_sum (innerₛₗ ι x) y s
lemma inner_sum_left {κ : Type*} (s : Finset κ) (x : κ → E) (y : E) :
    inner A (∑ i ∈ s, x i) y = ∑ i ∈ s, inner A (x i) y := map_sum ((innerₛₗ ι).flip y) x s

/-- Polarization identity for a positive semidefinite pairing. -/
lemma inner_polarization (x y : E) :
    inner A x y = (4 : ℂ)⁻¹ • (inner A (x + y) (x + y) - inner A (x - y) (x - y) -
      I • inner A (x + I • y) (x + I • y) + I • inner A (x - I • y) (x - I • y)) := by
  simp only [inner_add_left ι, inner_add_right (ι := ι), inner_sub_left ι, inner_sub_right ι,
    inner_smul_left_complex ι, inner_smul_right_complex (ι := ι), Complex.star_def, conj_I,
    smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]; module

lemma inner_smul_sub_sub_smul_sub_right (a₀ : A₀) (x y z : E) :
    inner A x ((a₀ • y - a₀ • z) - a₀ • (y - z)) = 0 := by
  simp only [inner_sub_right ι, inner_op_smul_right (ι := ι), mul_sub]; abel

/-- Polarization for a pair of complex-linear maps into a positive semidefinite module: the
pairing `⟪S x, T y⟫_A` is determined by its diagonal values `⟪S z, T z⟫_A`. -/
lemma inner_map_polarization {V M₁ M₂ : Type*} [AddCommGroup V] [Module ℂ V]
    [FunLike M₁ V E] [LinearMapClass M₁ ℂ V E] [FunLike M₂ V E] [LinearMapClass M₂ ℂ V E]
    (S : M₁) (T : M₂) (x y : V) :
    inner A (S x) (T y) = (4 : ℂ)⁻¹ • (inner A (S (x + y)) (T (x + y)) -
      inner A (S (x - y)) (T (x - y)) - I • inner A (S (x + I • y)) (T (x + I • y)) +
      I • inner A (S (x - I • y)) (T (x - I • y))) := by
  simp only [map_add, map_sub, map_smul, inner_add_left ι, inner_add_right (ι := ι),
    inner_sub_left ι, inner_sub_right ι, inner_smul_left_complex ι,
    inner_smul_right_complex (ι := ι), Complex.star_def, conj_I, smul_add, smul_sub, smul_neg,
    smul_smul, neg_smul, I_mul_I]
  module

section InnerPreserving

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  {f : E → F} (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include hf

/-- Any map into a definite `CStarModule A F` preserving `inner A` automatically intertwines the
`A₀`-action with the `A`-action along `ι`. -/
theorem map_smul_of_inner_eq (a₀ : A₀) (x : E) : f (a₀ • x) = ι a₀ • f x := by
  apply sub_eq_zero.mp; apply (CStarModule.inner_self (A := A)).mp
  simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, hf,
    inner_op_smul_left ι, inner_op_smul_right (ι := ι)]; noncomm_ring

/-- Any map into a definite `CStarModule A F` preserving `inner A` sends `0` to `0`. -/
theorem map_zero_of_inner : f 0 = 0 :=
  (CStarModule.inner_self (A := A)).mp <| by rw [hf, inner_zero_right ι]

omit [StarModule ℂ A] in
/-- Any map into a definite `CStarModule A F` preserving `inner A` preserves norms. -/
theorem norm_map_of_inner (x : E) : ‖f x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
    norm_eq_sqrt_norm_inner_self (ι := ι) x]

/-- Any map into a definite `CStarModule A F` preserving `inner A` is additive. -/
theorem map_add_of_inner (x y : E) : f (x + y) = f x + f y := by
  rw [← sub_eq_zero, ← CStarModule.inner_self (A := A)]
  simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right, CStarModule.inner_add_left,
    CStarModule.inner_add_right, hf, inner_add_left ι, inner_add_right (ι := ι)]
  abel

/-- Any map into a definite `CStarModule A F` preserving `inner A` is `ℂ`-homogeneous. -/
theorem map_smul_complex_of_inner (c : ℂ) (x : E) : f (c • x) = c • f x := by
  rw [← sub_eq_zero, ← CStarModule.inner_self (A := A)]
  simp [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex, hf,
    inner_smul_left_complex ι, inner_smul_right_complex (ι := ι), smul_smul]

end InnerPreserving

end Algebraic

section LinearIsometryOfInner

variable {A₀ A E F : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  (ι : A₀ →⋆ₙₐ[ℂ] A) [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E] [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]
  [CStarModule A F] (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- Any plain map into a definite `CStarModule A F` preserving `inner A` is a `ℂ`-linear isometry;
compose with `separationQuotientLiftOfInner` or `liftOfInner` for the universal properties. -/
def linearIsometryOfInner : E →ₗᵢ[ℂ] F where
  toFun := f
  map_add' := map_add_of_inner ι hf
  map_smul' := map_smul_complex_of_inner ι hf
  norm_map' := norm_map_of_inner ι hf

@[simp] theorem coe_linearIsometryOfInner : ⇑(linearIsometryOfInner ι f hf) = f := (rfl)

end LinearIsometryOfInner

/-! ### Cauchy–Schwarz and action bounds -/

section Analytic

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E]

section NormBasic

variable (ι : A₀ →⋆ₙₐ[ℂ] A) [IsPosSemidefCStarModuleAlong ι E]
include ι

lemma norm_sq_eq (x : E) : ‖x‖ ^ 2 = ‖inner A x x‖ := by
  simp [norm_eq_sqrt_norm_inner_self (ι := ι)]
protected lemma norm_nonneg (x : E) : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (ι := ι)]
protected lemma norm_zero : ‖(0 : E)‖ = 0 := by
  simp [norm_eq_sqrt_norm_inner_self (ι := ι), inner_zero_right ι]
theorem norm_eq_zero_iff_inner_self_eq_zero (x : E) : ‖x‖ = 0 ↔ inner A x x = 0 := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι), Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]
protected lemma norm_smul_complex (c : ℂ) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι) (c • x), norm_eq_sqrt_norm_inner_self (ι := ι) x,
    inner_smul_left_complex ι, inner_smul_right_complex (ι := ι), smul_smul, norm_smul, norm_mul,
    norm_star, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg c)]

end NormBasic

variable [StarOrderedRing A]

section CauchySchwarz

variable {ι : A₀ →⋆ₙₐ[ℂ] A} [IsPosSemidefCStarModuleAlong ι E]
include ι

private lemma inner_quad_nonneg (hι : DenseRange ι) (x y : E) (t : ℝ) :
    (0 : A) ≤ ‖x‖ ^ 2 • (inner A x y * inner A y x) -
      t • (inner A x y * inner A y x) - t • (inner A x y * inner A y x) +
      (t ^ 2) • inner A y y := by
  have hstep (a₀ : A₀) :
      (0 : A) ≤ ‖x‖ ^ 2 • (ι a₀ * star (ι a₀)) - t • (ι a₀ * inner A y x) -
        t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y :=
    calc (0 : A) ≤ inner A (a₀ • x - t • y) (a₀ • x - t • y) := inner_self_nonneg (ι := ι)
      _ = ι a₀ * inner A x x * star (ι a₀) - t • (ι a₀ * inner A y x) -
            t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y := by
          simp only [inner_sub_right ι, inner_sub_left ι, inner_op_smul_right (ι := ι),
            inner_op_smul_left ι, inner_smul_right_real ι, inner_smul_left_real ι,
            mul_smul_comm, smul_mul_assoc, smul_smul, ← sq, mul_assoc]; abel
      _ ≤ ‖x‖ ^ 2 • (ι a₀ * star (ι a₀)) - t • (ι a₀ * inner A y x) -
            t • (inner A x y * star (ι a₀)) + (t ^ 2) • inner A y y := by
          gcongr; rw [norm_sq_eq ι]
          exact CStarAlgebra.star_right_conjugate_le_norm_smul _ _ (isSelfAdjoint_inner_self ι x)
  let P (a : A) : Prop := (0 : A) ≤ ‖x‖ ^ 2 • (a * star a) -
    t • (a * inner A y x) - t • (inner A x y * star a) + (t ^ 2) • inner A y y
  simpa only [P, star_inner (ι := ι)] using hι.induction (P := P)
    (fun _ ⟨a₀, ha₀⟩ ↦ ha₀ ▸ hstep a₀) (isClosed_le (by fun_prop) (by fun_prop)) (inner A x y)

/-- The C⋆-algebra Cauchy–Schwarz inequality `⟪x, y⟫_A * ⟪y, x⟫_A ≤ ‖x‖ ^ 2 • ⟪y, y⟫_A` over a
dense `⋆`-subalgebra. -/
theorem inner_mul_inner_swap_le (hι : DenseRange ι) (x y : E) :
    inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y := by
  set p := inner A x y * inner A y x
  rcases (sq_nonneg ‖x‖).eq_or_lt with hx0 | hx_pos
  · have hpos : Set.Ioi (0 : ℝ) ⊆ {t : ℝ | p ≤ (t / 2) • inner A y y} := fun t (ht : 0 < t) ↦ by
      have hq := inner_quad_nonneg hι x y t
      have hmul : 2 * t * (t / 2) = t ^ 2 := by ring
      have hq_eq : ‖x‖ ^ 2 • p - t • p - t • p + t ^ 2 • inner A y y =
          (2 * t) • ((t / 2) • inner A y y) - (2 * t) • p := by
        rw [← hx0, zero_smul, smul_smul, hmul, two_mul, add_smul]; abel
      rw [hq_eq, sub_nonneg] at hq
      exact (smul_le_smul_iff_of_pos_left (by positivity)).mp hq
    simpa [← hx0] using closure_minimal hpos
      (isClosed_le continuous_const (by fun_prop)) (by simp [closure_Ioi] : (0 : ℝ) ∈ _)
  · have hq := inner_quad_nonneg hι x y (‖x‖ ^ 2)
    have hq_eq : ‖x‖ ^ 2 • p - ‖x‖ ^ 2 • p - ‖x‖ ^ 2 • p + (‖x‖ ^ 2) ^ 2 • inner A y y =
        ‖x‖ ^ 2 • (‖x‖ ^ 2 • inner A y y) - ‖x‖ ^ 2 • p := by rw [smul_smul, ← sq]; abel
    rw [hq_eq, sub_nonneg] at hq; exact (smul_le_smul_iff_of_pos_left hx_pos).mp hq

/-- The norm Cauchy–Schwarz inequality `‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` over a dense `⋆`-subalgebra. -/
theorem norm_inner_le (hι : DenseRange ι) (x y : E) : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine (pow_le_pow_iff_left₀ (n := 2) (norm_nonneg _)
    (mul_nonneg (IsPosSemidefCStarModuleAlong.norm_nonneg ι x)
      (IsPosSemidefCStarModuleAlong.norm_nonneg ι y)) (by decide)).mp ?_
  calc ‖inner A x y‖ ^ 2 = ‖inner A x y * inner A y x‖ := by
        rw [← star_inner (ι := ι) x y, CStarRing.norm_self_mul_star, sq]
    _ ≤ ‖‖x‖ ^ 2 • inner A y y‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (inner_mul_inner_swap_le hι x y)
        (by rw [← star_inner (ι := ι) x y]; exact mul_star_self_nonneg _)
    _ = (‖x‖ * ‖y‖) ^ 2 := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _), ← norm_sq_eq ι y, mul_pow]

protected theorem norm_triangle (hι : DenseRange ι) (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (pow_le_pow_iff_left₀ (n := 2) (IsPosSemidefCStarModuleAlong.norm_nonneg ι (x + y))
    (add_nonneg (IsPosSemidefCStarModuleAlong.norm_nonneg ι x)
      (IsPosSemidefCStarModuleAlong.norm_nonneg ι y)) (by decide)).mp ?_
  calc ‖x + y‖ ^ 2 = ‖inner A (x + y) (x + y)‖ := norm_sq_eq ι (x + y)
    _ ≤ ‖inner A x x + inner A y x‖ + ‖inner A x y‖ + ‖inner A y y‖ := by
        rw [inner_add_right (ι := ι), inner_add_left ι, inner_add_left ι, ← add_assoc]
        exact norm_add₃_le
    _ ≤ ‖inner A x x‖ + ‖inner A y x‖ + ‖inner A x y‖ + ‖inner A y y‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
        rw [← norm_sq_eq ι x, ← norm_sq_eq ι y]; gcongr <;> exact norm_inner_le hι _ _
    _ = (‖x‖ + ‖y‖) ^ 2 := by ring

/-- Over a dense `⋆`-subalgebra, vectors of seminorm zero are left-orthogonal to every vector. -/
theorem inner_eq_zero_of_norm_eq_zero_left (hι : DenseRange ι) {x : E} (hx : ‖x‖ = 0) (y : E) :
    inner A x y = 0 :=
  norm_le_zero_iff.mp <| by simpa [hx] using norm_inner_le hι x y

/-- Over a dense `⋆`-subalgebra, vectors of seminorm zero are right-orthogonal to every vector. -/
theorem inner_eq_zero_of_norm_eq_zero_right (hι : DenseRange ι) (x : E) {y : E} (hy : ‖y‖ = 0) :
    inner A x y = 0 :=
  norm_le_zero_iff.mp <| by simpa [hy] using norm_inner_le hι x y

lemma seminormedSpaceCore (hι : DenseRange ι) : SeminormedSpace.Core ℂ E :=
  { norm_nonneg := IsPosSemidefCStarModuleAlong.norm_nonneg ι,
    norm_smul := IsPosSemidefCStarModuleAlong.norm_smul_complex ι,
    norm_triangle := IsPosSemidefCStarModuleAlong.norm_triangle hι }

end CauchySchwarz

section ActionBounds

variable (ι : A₀ →⋆ₙₐ[ℂ] A) [IsPosSemidefCStarModuleAlong ι E]
include ι

lemma sqrt_inner_self_mul_self (x : E) :
    CFC.sqrt (inner A x x) * CFC.sqrt (inner A x x) = inner A x x :=
  CFC.sqrt_mul_sqrt_self _ (inner_self_nonneg (ι := ι))
lemma mul_inner_self_mul_star (b : A) (x : E) :
    b * inner A x x * star b =
      (b * CFC.sqrt (inner A x x)) * star (b * CFC.sqrt (inner A x x)) := by
  rw [star_mul, (CFC.sqrt_nonneg (a := inner A x x)).isSelfAdjoint.star_eq,
    ← mul_assoc, mul_assoc b (CFC.sqrt _), sqrt_inner_self_mul_self ι]
lemma norm_mul_sqrt_inner_self_le (b : A) (x : E) :
    ‖b * CFC.sqrt (inner A x x)‖ ≤ ‖b‖ * ‖x‖ :=
  (norm_mul_le _ _).trans_eq <| by
    rw [CFC.norm_sqrt _ (inner_self_nonneg (ι := ι)), ← norm_eq_sqrt_norm_inner_self (ι := ι)]
lemma inner_smul_smul (a₀ : A₀) (x : E) :
    inner A (a₀ • x) (a₀ • x) =
      ι a₀ * CFC.sqrt (inner A x x) * star (ι a₀ * CFC.sqrt (inner A x x)) := by
  rw [inner_op_smul_left ι, inner_op_smul_right (ι := ι), mul_inner_self_mul_star ι]
lemma inner_smul_sub_self (a₀ : A₀) (x : E) :
    inner A (a₀ • x - x) (a₀ • x - x) =
      (ι a₀ * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) *
        star (ι a₀ * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)) := by
  have hs := sqrt_inner_self_mul_self ι x
  have hs' := (CFC.sqrt_nonneg (a := inner A x x)).isSelfAdjoint.star_eq
  generalize CFC.sqrt (inner A x x) = s at hs hs' ⊢
  simp only [inner_sub_left ι, inner_sub_right ι, inner_op_smul_left ι,
    inner_op_smul_right (ι := ι), star_sub, star_mul, hs', ← hs]; noncomm_ring
protected theorem norm_smul (a₀ : A₀) (x : E) :
    ‖a₀ • x‖ = ‖ι a₀ * CFC.sqrt (inner A x x)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι), inner_smul_smul ι,
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (norm_nonneg _)]
theorem norm_smul_sub_self (a₀ : A₀) (x : E) :
    ‖a₀ • x - x‖ = ‖ι a₀ * CFC.sqrt (inner A x x) - CFC.sqrt (inner A x x)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (ι := ι), inner_smul_sub_self ι,
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (norm_nonneg _)]
protected theorem norm_smul_le (a₀ : A₀) (x : E) : ‖a₀ • x‖ ≤ ‖ι a₀‖ * ‖x‖ :=
  (IsPosSemidefCStarModuleAlong.norm_smul ι a₀ x).trans_le (norm_mul_sqrt_inner_self_le ι (ι a₀) x)

/-- Norm bound `‖a₀ • x - b₀ • x‖ ≤ ‖ι a₀ - ι b₀‖ * ‖x‖`, without assuming subtraction on `A₀`. -/
theorem norm_smul_sub_smul_le (a₀ b₀ : A₀) (x : E) :
    ‖a₀ • x - b₀ • x‖ ≤ ‖ι a₀ - ι b₀‖ * ‖x‖ := by
  have hdiag : inner A (a₀ • x - b₀ • x) (a₀ • x - b₀ • x) =
      (ι a₀ - ι b₀) * inner A x x * star (ι a₀ - ι b₀) := by
    simp only [inner_sub_left ι, inner_sub_right ι, inner_op_smul_left ι,
      inner_op_smul_right (ι := ι), star_sub]; noncomm_ring
  rw [norm_eq_sqrt_norm_inner_self (ι := ι) (a₀ • x - b₀ • x), hdiag, mul_inner_self_mul_star ι,
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (norm_nonneg _)]
  exact norm_mul_sqrt_inner_self_le ι (ι a₀ - ι b₀) x

end ActionBounds
end Analytic

/-! ### Null space and continuity on seminormed modules -/

section Seminormed

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [SeminormedAddCommGroup E]

section Module

variable (ι : A₀ →⋆ₙₐ[ℂ] A) [Module ℂ E] [SMul A₀ E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E] [StarOrderedRing A]
include ι

theorem norm_smul_sub_smul_right_le (a₀ : A₀) (x y : E) :
    ‖a₀ • x - a₀ • y‖ ≤ ‖ι a₀‖ * ‖x - y‖ := by
  set w := (a₀ • x - a₀ • y) - a₀ • (x - y)
  have hw : ‖w‖ = 0 := (norm_eq_zero_iff_inner_self_eq_zero ι w).mpr
    (inner_smul_sub_sub_smul_sub_right ι a₀ w x y)
  calc ‖a₀ • x - a₀ • y‖ = ‖w + a₀ • (x - y)‖ := by simp [w]
    _ ≤ ‖w‖ + ‖a₀ • (x - y)‖ := norm_add_le _ _
    _ ≤ ‖ι a₀‖ * ‖x - y‖ := by
        simpa [hw] using IsPosSemidefCStarModuleAlong.norm_smul_le ι a₀ (x - y)
theorem uniformContinuousConstSMul : UniformContinuousConstSMul A₀ E :=
  ⟨fun a₀ ↦ (LipschitzWith.of_dist_le_mul (K := ‖ι a₀‖₊) fun x y ↦ by
    simpa [dist_eq_norm] using norm_smul_sub_smul_right_le ι a₀ x y).uniformContinuous⟩

end Module

section NormedSpace

variable [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]

section Explicit

variable (ι : A₀ →⋆ₙₐ[ℂ] A) [IsPosSemidefCStarModuleAlong ι E]
include ι

theorem mem_nullSubmodule_iff_inner_self_eq_zero (x : E) :
    x ∈ nullSubmodule ℂ E ↔ inner A x x = 0 := by
  rw [mem_nullSubmodule_iff, norm_eq_zero_iff_inner_self_eq_zero ι]
theorem smul_sub_sub_smul_sub_mem_nullSubmodule (a₀ : A₀) (x y : E) :
    (a₀ • x - a₀ • y) - a₀ • (x - y) ∈ nullSubmodule ℂ E :=
  (mem_nullSubmodule_iff_inner_self_eq_zero ι _).mpr
    (inner_smul_sub_sub_smul_sub_right ι a₀ _ x y)
theorem smul_mem_nullSubmodule [StarOrderedRing A] (a₀ : A₀) {x : E}
    (hx : x ∈ nullSubmodule ℂ E) : a₀ • x ∈ nullSubmodule ℂ E := by
  rw [mem_nullSubmodule_iff] at hx ⊢
  exact norm_le_zero_iff.mp <| by
    simpa [hx] using IsPosSemidefCStarModuleAlong.norm_smul_le ι a₀ x

end Explicit

section DenseRange

variable [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A} [IsPosSemidefCStarModuleAlong ι E]

theorem mem_nullSubmodule_iff_forall_inner_left (hι : DenseRange ι) (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A y x = 0 := by
  rw [mem_nullSubmodule_iff]
  exact ⟨fun hx y ↦ norm_le_zero_iff.mp (by simpa [hx] using norm_inner_le hι y x),
    fun h ↦ (norm_eq_zero_iff_inner_self_eq_zero ι x).mpr (h x)⟩
theorem mem_nullSubmodule_iff_forall_inner_right (hι : DenseRange ι) (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A x y = 0 := by
  rw [mem_nullSubmodule_iff_forall_inner_left hι]
  exact ⟨fun h y ↦ by simpa [star_inner (ι := ι)] using congrArg star (h y),
    fun h y ↦ by simpa [star_inner (ι := ι)] using congrArg star (h y)⟩

/-- Under `DenseRange ι`, the pairing `⟪·, ·⟫_A` is a continuous sesquilinear map of norm `≤ 1`. -/
noncomputable def innerSL (hι : DenseRange ι) : E →L⋆[ℂ] E →L[ℂ] A :=
  LinearMap.mkContinuous₂ (innerₛₗ ι) 1 fun x y ↦ by simpa using norm_inner_le hι x y

@[simp] lemma innerSL_apply (hι : DenseRange ι) (x y : E) : innerSL hι x y = inner A x y := (rfl)
theorem continuous_inner (hι : DenseRange ι) : Continuous fun p : E × E ↦ inner A p.1 p.2 := by
  simp_rw [← innerSL_apply hι]; fun_prop

/-- Inseparable vectors have equal `A`-valued inner products. -/
theorem inner_eq_inner_of_inseparable (hι : DenseRange ι) {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) : inner A x₁ y₁ = inner A x₂ y₂ :=
  ((hx.prod hy).map (continuous_inner hι)).eq

end DenseRange
end NormedSpace
end Seminormed
end IsPosSemidefCStarModuleAlong

/-! ### Specializations and `Core` constructors for `PosSemidefCStarModule` -/

namespace PosSemidefCStarModule

section CoreAlong

/-- Data constructing a positive semidefinite module over `A₀` along `ι : A₀ →⋆ₙₐ[ℂ] A` on a type
`E` that carries no pre-existing seminorm. Determined extensionally by its `A`-valued pairing. -/
structure CoreAlong {A₀ A : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
    (ι : A₀ →⋆ₙₐ[ℂ] A) (E : Type*) [AddCommGroup E] [Module ℂ E] [SMul A₀ E]
    extends Inner A E where
  inner_add_right {x y z : E} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x : E} : 0 ≤ inner x x
  inner_op_smul_right {a₀ : A₀} {x y : E} : inner x (a₀ • y) = ι a₀ * inner x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner x (z • y) = z • inner x y
  star_inner (x y : E) : star (inner x y) = inner y x

/-- Data constructing a positive semidefinite `A`-module on `E` with no pre-existing seminorm. -/
abbrev Core (A E : Type*) [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] : Type _ :=
  CoreAlong (NonUnitalStarAlgHom.id ℂ A) E

/-- Extract the underlying `Core A E` from a `PosSemidefCStarModule A E`. -/
def Core.ofPosSemidefCStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
    [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [PosSemidefCStarModule A E] : Core A E :=
  { toInner := inferInstance, inner_add_right := PosSemidefCStarModule.inner_add_right,
    inner_self_nonneg := PosSemidefCStarModule.inner_self_nonneg,
    inner_op_smul_right := PosSemidefCStarModule.inner_op_smul_right,
    inner_smul_right_complex := PosSemidefCStarModule.inner_smul_right_complex,
    star_inner := PosSemidefCStarModule.star_inner }

@[simp] theorem Core.ofPosSemidefCStarModule_inner {A E : Type*} [NonUnitalSemiring A]
    [StarRing A] [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E]
    [Norm A] [Norm E] [PosSemidefCStarModule A E] (x y : E) :
    (Core.ofPosSemidefCStarModule A E).inner x y = inner A x y := (rfl)

namespace CoreAlong

section General

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E]

@[ext] theorem ext {c₁ c₂ : CoreAlong ι E} (h : ∀ x y, c₁.inner x y = c₂.inner x y) : c₁ = c₂ := by
  rcases c₁ with ⟨⟨_⟩, _, _, _, _, _⟩; rcases c₂ with ⟨⟨_⟩, _, _, _, _, _⟩
  congr; ext x y; exact h x y

/-- Pull a `CoreAlong` back along a complex-linear `A₀`-equivariant map `f : F →ₗ[ℂ] E`. -/
def comap {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A₀ F] (c : CoreAlong ι E)
    (f : F →ₗ[ℂ] E) (hf : ∀ (a₀ : A₀) (x : F), f (a₀ • x) = a₀ • f x) : CoreAlong ι F :=
  { inner x y := c.inner (f x) (f y), inner_add_right := by simp [c.inner_add_right],
    inner_self_nonneg := c.inner_self_nonneg,
    inner_op_smul_right := by simp [hf, c.inner_op_smul_right],
    inner_smul_right_complex := by simp [c.inner_smul_right_complex],
    star_inner x y := c.star_inner (f x) (f y) }

@[simp] theorem comap_inner {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A₀ F]
    (c : CoreAlong ι E) (f : F →ₗ[ℂ] E) (hf : ∀ (a₀ : A₀) (x : F), f (a₀ • x) = a₀ • f x)
    (x y : F) : (c.comap f hf).inner x y = c.inner (f x) (f y) := (rfl)

end General

section NormConstruction

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A} [AddCommGroup E] [Module ℂ E] [SMul A₀ E]

/-- Norm `‖x‖ = √‖c.inner x x‖` induced by a `CoreAlong` (non-instance). -/
noncomputable abbrev toNorm (c : CoreAlong ι E) : Norm E := @CStarModule.norm A E _ c.toInner
@[simp] theorem norm_toNorm (c : CoreAlong ι E) (x : E) :
    (letI := c.toNorm; ‖x‖) = √‖c.inner x x‖ := (rfl)
theorem toIsPosSemidefCStarModuleAlong (c : CoreAlong ι E) :
    @IsPosSemidefCStarModuleAlong A₀ A _ _ _ _ _ _ _ _ ι E _ _ _ c.toNorm c.toInner :=
  let : Inner A E := c.toInner; let : Norm E := c.toNorm
  { inner_add_right := c.inner_add_right, inner_self_nonneg := c.inner_self_nonneg,
    inner_op_smul_right := c.inner_op_smul_right,
    inner_smul_right_complex := c.inner_smul_right_complex, star_inner := c.star_inner,
    norm_eq_sqrt_norm_inner_self := fun _ ↦ rfl }

variable [StarOrderedRing A]

theorem toSeminormedSpaceCore (c : CoreAlong ι E) (hι : DenseRange ι) :
    @SeminormedSpace.Core ℂ E _ _ c.toNorm _ :=
  let : Inner A E := c.toInner; let : Norm E := c.toNorm
  have : IsPosSemidefCStarModuleAlong ι E := c.toIsPosSemidefCStarModuleAlong
  IsPosSemidefCStarModuleAlong.seminormedSpaceCore hι

/-- `SeminormedAddCommGroup E` constructed from `c` when `ι` has dense range. -/
noncomputable abbrev toSeminormedAddCommGroup (c : CoreAlong ι E) (hι : DenseRange ι) :
    SeminormedAddCommGroup E :=
  letI : Norm E := c.toNorm; SeminormedAddCommGroup.ofCore (c.toSeminormedSpaceCore hι)

/-- `NormedSpace ℂ E` constructed from `c` when `ι` has dense range. -/
noncomputable abbrev toNormedSpace (c : CoreAlong ι E) (hι : DenseRange ι) :
    @NormedSpace ℂ E _ (c.toSeminormedAddCommGroup hι) :=
  letI : SeminormedAddCommGroup E := c.toSeminormedAddCommGroup hι
  { norm_smul_le r x := ((c.toSeminormedSpaceCore hι).norm_smul r x).le }

end NormConstruction
end CoreAlong

/-- Build a `PosSemidefCStarModule A E` from `c : Core A E` on `c.toSeminormedAddCommGroup`. -/
noncomputable abbrev Core.toPosSemidefCStarModule {A E : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommGroup E] [Module ℂ E] [SMul A E]
    (c : Core A E) :
    @PosSemidefCStarModule A E _ _ _ _ _ _ _ _ (c.toSeminormedAddCommGroup denseRange_id).toNorm :=
  letI : SeminormedAddCommGroup E := c.toSeminormedAddCommGroup denseRange_id
  { toInner := c.toInner, inner_add_right := c.inner_add_right,
    inner_self_nonneg := c.inner_self_nonneg, inner_op_smul_right := c.inner_op_smul_right,
    inner_smul_right_complex := c.inner_smul_right_complex, star_inner := c.star_inner,
    norm_eq_sqrt_norm_inner_self := fun _ ↦ rfl }

end CoreAlong

/-! ### Direct API for `PosSemidefCStarModule A E` -/

section Direct

section Algebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
  [PosSemidefCStarModule A E]

@[simp] lemma inner_add_left {x y z : E} : inner A (x + y) z = inner A x z + inner A y z :=
  IsPosSemidefCStarModuleAlong.inner_add_left (.id ℂ A) x y z
@[simp] lemma inner_op_smul_left {a : A} {x y : E} : inner A (a • x) y = inner A x y * star a :=
  IsPosSemidefCStarModuleAlong.inner_op_smul_left (.id ℂ A) a x y
@[simp] lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint (inner A x x) :=
  IsPosSemidefCStarModuleAlong.isSelfAdjoint_inner_self (.id ℂ A) x
@[simp] lemma inner_smul_right_real {r : ℝ} {x y : E} : inner A x (r • y) = r • inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_smul_right_real (.id ℂ A) r x y

variable [StarModule ℂ A]

@[simp] lemma inner_smul_left_complex {z : ℂ} {x y : E} :
    inner A (z • x) y = star z • inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_smul_left_complex (.id ℂ A) z x y
@[simp] lemma inner_smul_left_real {r : ℝ} {x y : E} : inner A (r • x) y = r • inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_smul_left_real (.id ℂ A) r x y
@[simp] lemma inner_zero_right {x : E} : inner A x 0 = 0 :=
  IsPosSemidefCStarModuleAlong.inner_zero_right (.id ℂ A) x
@[simp] lemma inner_zero_left {x : E} : inner A 0 x = 0 :=
  IsPosSemidefCStarModuleAlong.inner_zero_left (.id ℂ A) x
@[simp] lemma inner_neg_right {x y : E} : inner A x (-y) = -inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_neg_right (.id ℂ A) x y
@[simp] lemma inner_neg_left {x y : E} : inner A (-x) y = -inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_neg_left (.id ℂ A) x y
@[simp] lemma inner_sub_right {x y z : E} : inner A x (y - z) = inner A x y - inner A x z :=
  IsPosSemidefCStarModuleAlong.inner_sub_right (.id ℂ A) x y z
@[simp] lemma inner_sub_left {x y z : E} : inner A (x - y) z = inner A x z - inner A y z :=
  IsPosSemidefCStarModuleAlong.inner_sub_left (.id ℂ A) x y z
@[simp] lemma inner_sum_right {κ : Type*} {s : Finset κ} {x : E} {y : κ → E} :
    inner A x (∑ i ∈ s, y i) = ∑ i ∈ s, inner A x (y i) :=
  IsPosSemidefCStarModuleAlong.inner_sum_right (.id ℂ A) s x y
@[simp] lemma inner_sum_left {κ : Type*} {s : Finset κ} {x : κ → E} {y : E} :
    inner A (∑ i ∈ s, x i) y = ∑ i ∈ s, inner A (x i) y :=
  IsPosSemidefCStarModuleAlong.inner_sum_left (.id ℂ A) s x y
theorem map_smul_of_inner_eq {F : Type*} [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F]
    [CStarModule A F] {f : E → F} (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a : A) (x : E) : f (a • x) = a • f x :=
  IsPosSemidefCStarModuleAlong.map_smul_of_inner_eq (.id ℂ A) hf a x

end Algebraic

section Norm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

theorem norm_eq_zero_iff_inner_self_eq_zero [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [PosSemidefCStarModule A E] (x : E) : ‖x‖ = 0 ↔ inner A x x = 0 :=
  IsPosSemidefCStarModuleAlong.norm_eq_zero_iff_inner_self_eq_zero (.id ℂ A) x

/-- On a separated normed space (`NormedAddCommGroup E`), any `PosSemidefCStarModule A E` is
automatically definite, hence a `CStarModule A E`. -/
abbrev toCStarModuleOfNormedAddCommGroup {E : Type*} [NormedAddCommGroup E] [Module ℂ E]
    [SMul A E] [PosSemidefCStarModule A E] : CStarModule A E :=
  toCStarModule fun x hx ↦ norm_eq_zero.mp <| (norm_eq_zero_iff_inner_self_eq_zero x).mpr hx

theorem mem_nullSubmodule_iff_inner_self_eq_zero [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A E] [PosSemidefCStarModule A E] (x : E) :
    x ∈ nullSubmodule ℂ E ↔ inner A x x = 0 :=
  IsPosSemidefCStarModuleAlong.mem_nullSubmodule_iff_inner_self_eq_zero (.id ℂ A) x

variable [StarOrderedRing A]

section AddCommGroup

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [PosSemidefCStarModule A E]

theorem inner_mul_inner_swap_le (x y : E) : inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y :=
  IsPosSemidefCStarModuleAlong.inner_mul_inner_swap_le (ι := .id ℂ A) denseRange_id x y
theorem norm_inner_le (x y : E) : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ :=
  IsPosSemidefCStarModuleAlong.norm_inner_le (ι := .id ℂ A) denseRange_id x y
include A in
variable (A) in
lemma seminormedSpaceCore : SeminormedSpace.Core ℂ E :=
  IsPosSemidefCStarModuleAlong.seminormedSpaceCore (ι := .id ℂ A) denseRange_id
protected theorem norm_smul_le (a : A) (x : E) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ :=
  IsPosSemidefCStarModuleAlong.norm_smul_le (.id ℂ A) a x

end AddCommGroup

/-! #### Right modules: `PosSemidefCStarModule Aᵐᵒᵖ E` with `⟨x, y⟩_A = unop ⟪x, y⟫_Aᵐᵒᵖ` -/

section Right

variable [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [PosSemidefCStarModule Aᵐᵒᵖ E]

omit [StarOrderedRing A] in
/-- Conjugate-linearity of a right-module pairing in the first slot: `⟨x a, y⟩_A = a⋆ ⟨x, y⟩_A`. -/
lemma unop_inner_op_smul_left (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ (op a • x) y) = star a * unop (inner Aᵐᵒᵖ x y) := by
  simp

omit [StarOrderedRing A] in
/-- Linearity of a right-module pairing in the second slot: `⟨x, y a⟩_A = ⟨x, y⟩_A a`. -/
lemma unop_inner_op_smul_right (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ x (op a • y)) = unop (inner Aᵐᵒᵖ x y) * a := by
  simp

/-- Right-module Cauchy–Schwarz without definiteness: `⟨x, y⟩_A⋆ ⟨x, y⟩_A ≤ ‖x‖² ⟨y, y⟩_A`. -/
theorem star_unop_inner_mul_unop_inner_le (x y : E) :
    star (unop (inner Aᵐᵒᵖ x y)) * unop (inner Aᵐᵒᵖ x y) ≤ ‖x‖ ^ 2 • unop (inner Aᵐᵒᵖ y y) := by
  have h := unop_le_unop.mpr (inner_mul_inner_swap_le (A := Aᵐᵒᵖ) x y)
  rwa [unop_mul, unop_smul, ← PosSemidefCStarModule.star_inner (A := Aᵐᵒᵖ) x y, unop_star] at h

/-- Right-module norm Cauchy–Schwarz without definiteness: `‖⟨x, y⟩_A‖ ≤ ‖x‖ ‖y‖`. -/
theorem norm_unop_inner_le (x y : E) : ‖unop (inner Aᵐᵒᵖ x y)‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_unop]; exact norm_inner_le x y

/-- The right action on a positive semidefinite right module is bounded: `‖x a‖ ≤ ‖x‖ ‖a‖`. -/
theorem norm_op_smul_le (a : A) (x : E) : ‖op a • x‖ ≤ ‖x‖ * ‖a‖ := by
  rw [mul_comm, ← norm_op a]; exact PosSemidefCStarModule.norm_smul_le _ x

end Right

section Seminormed

variable [SeminormedAddCommGroup E]

/-- Jointly bounded action `IsBoundedSMul A E` on a positive semidefinite `A`-module. -/
instance instIsBoundedSMul [Module ℂ E] [SMul A E] [PosSemidefCStarModule A E] :
    IsBoundedSMul A E where
  dist_smul_pair' a x y := by
    simpa [dist_eq_norm] using
      IsPosSemidefCStarModuleAlong.norm_smul_sub_smul_right_le (.id ℂ A) a x y
  dist_pair_smul' a b x := by
    simpa [dist_eq_norm] using IsPosSemidefCStarModuleAlong.norm_smul_sub_smul_le (.id ℂ A) a b x

variable [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

theorem mem_nullSubmodule_iff_forall_inner_left (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A y x = 0 :=
  IsPosSemidefCStarModuleAlong.mem_nullSubmodule_iff_forall_inner_left
    (ι := .id ℂ A) denseRange_id x
theorem mem_nullSubmodule_iff_forall_inner_right (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A x y = 0 :=
  IsPosSemidefCStarModuleAlong.mem_nullSubmodule_iff_forall_inner_right
    (ι := .id ℂ A) denseRange_id x
theorem smul_mem_nullSubmodule (a : A) {x : E} (hx : x ∈ nullSubmodule ℂ E) :
    a • x ∈ nullSubmodule ℂ E :=
  IsPosSemidefCStarModuleAlong.smul_mem_nullSubmodule (.id ℂ A) a hx
@[continuity, fun_prop]
theorem continuous_inner : Continuous fun p : E × E ↦ inner A p.1 p.2 :=
  IsPosSemidefCStarModuleAlong.continuous_inner (ι := .id ℂ A) denseRange_id

end Seminormed
end Norm
end Direct
end PosSemidefCStarModule
end TauCeti

/-! ### Concrete witnesses: complex pre-inner product spaces and `⋆`-subalgebra self-modules -/

/-- Any complex seminormed `InnerProductSpace ℂ E` (possibly with nonzero null vectors) is a
`PosSemidefCStarModule ℂ E`, generalizing `WithCStarModule.instCStarModuleComplex`. -/
noncomputable instance WithCStarModule.instPosSemidefCStarModuleComplex {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] : TauCeti.PosSemidefCStarModule ℂ E :=
  { inner x y := ⟪x, y⟫_ℂ, inner_add_right := by simp [_root_.inner_add_right],
    inner_self_nonneg := fun {_} ↦ by
      rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]; exact inner_self_nonneg,
    inner_op_smul_right := by simp [inner_smul_right],
    inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul],
    star_inner _ _ := by simp,
    norm_eq_sqrt_norm_inner_self x := by
      simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x }

namespace TauCeti
section SubalgebraRightModule

variable {A S : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]

namespace PosSemidefCStarModule

/-- Any `⋆`-subalgebra `s` of a C⋆-algebra `A` is a right module over itself (`sᵐᵒᵖ`) with
`Aᵐᵒᵖ`-valued inner product `op (star (x : A) * (y : A))` along `(subtype s).op`. -/
noncomputable def rightModuleCoreAlong (s : S) :
    CoreAlong (NonUnitalStarSubalgebraClass.subtype s).op s :=
  { inner x y := op (star (x : A) * (y : A)), inner_add_right := by simp [mul_add],
    inner_self_nonneg := op_nonneg.mpr (star_mul_self_nonneg _),
    inner_op_smul_right := fun {r _ _} ↦ by
      rcases MulOpposite.op_surjective r with ⟨r, rfl⟩; exact unop_injective (by simp [mul_assoc]),
    inner_smul_right_complex := by simp [mul_smul_comm], star_inner _ _ := by simp }

@[simp] theorem rightModuleCoreAlong_inner (s : S) (x y : s) :
    (rightModuleCoreAlong s).inner x y = op (star (x : A) * (y : A)) := (rfl)

/-- With its subtype norm and right multiplication over `sᵐᵒᵖ`, any `⋆`-subalgebra `s` of a
C⋆-algebra `A` satisfies `IsPosSemidefCStarModuleAlong (subtype s).op s`. -/
theorem isPosSemidefCStarModuleAlong_op (s : S) :
    letI : Inner Aᵐᵒᵖ s := (rightModuleCoreAlong s).toInner
    IsPosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype s).op s := by
  let : Inner Aᵐᵒᵖ s := (rightModuleCoreAlong s).toInner
  refine ⟨(rightModuleCoreAlong s).inner_add_right, (rightModuleCoreAlong s).inner_self_nonneg,
    (rightModuleCoreAlong s).inner_op_smul_right,
    (rightModuleCoreAlong s).inner_smul_right_complex, (rightModuleCoreAlong s).star_inner,
    fun x ↦ ?_⟩
  have h : inner Aᵐᵒᵖ x x = op (star (x : A) * (x : A)) := rightModuleCoreAlong_inner s x x
  rw [h, AddSubgroupClass.coe_norm, MulOpposite.norm_op, CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg _)]

end PosSemidefCStarModule

namespace IsPosSemidefCStarModuleAlong

/-- Right-module `Aᵐᵒᵖ`-valued inner product `MulOpposite.op (star (x : A) * (y : A))` on a
`⋆`-subalgebra `s` of `A`. -/
noncomputable scoped instance instInnerRightModule (s : S) : Inner Aᵐᵒᵖ s :=
  (PosSemidefCStarModule.rightModuleCoreAlong s).toInner

/-- Right-module `IsPosSemidefCStarModuleAlong` instance on a `⋆`-subalgebra `s` of `A`. -/
scoped instance instIsPosSemidefCStarModuleAlongOp (s : S) :
    IsPosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype s).op s :=
  PosSemidefCStarModule.isPosSemidefCStarModuleAlong_op s

end IsPosSemidefCStarModuleAlong
end SubalgebraRightModule
end TauCeti

-- Witness that `PosSemidefCStarModule` admits nonzero null vectors (pullback along `fst`).
example {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [SMul A F] (y : F) (hy : y ≠ 0) :
    let c : TauCeti.PosSemidefCStarModule.Core A (E × F) :=
      (TauCeti.PosSemidefCStarModule.Core.ofPosSemidefCStarModule A E).comap
        (LinearMap.fst ℂ E F) (fun _ _ ↦ rfl)
    letI := c.toSeminormedAddCommGroup denseRange_id
    letI := TauCeti.PosSemidefCStarModule.Core.toPosSemidefCStarModule c
    ((0, y) : E × F) ≠ 0 ∧ inner A ((0, y) : E × F) (0, y) = 0 :=
  ⟨by simp [hy], CStarModule.inner_zero_right (A := A) (x := (0 : E))⟩

/-! ### Separated quotient and its universal properties -/

namespace TauCeti.IsPosSemidefCStarModuleAlong

section SeparationQuotient

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]

section QuotientStructure

variable [StarOrderedRing A]

/-- Descend the `A`-valued inner product along a dense `ι` to `SeparationQuotient E`. -/
noncomputable abbrev separationQuotientInner {ι : A₀ →⋆ₙₐ[ℂ] A}
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) : Inner A (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner A) fun _ _ _ _ ↦ inner_eq_inner_of_inseparable hι

@[simp] theorem separationQuotientInner_mk_mk {ι : A₀ →⋆ₙₐ[ℂ] A}
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) (x y : E) :
    (letI := separationQuotientInner (E := E) hι;
      inner A (SeparationQuotient.mk x) (SeparationQuotient.mk y)) = inner A x y := (rfl)

/-- Descend the `A₀`-action to `SeparationQuotient E` (requires no `DenseRange` assumption). -/
noncomputable abbrev separationQuotientSMul (ι : A₀ →⋆ₙₐ[ℂ] A)
    [IsPosSemidefCStarModuleAlong ι E] : SMul A₀ (SeparationQuotient E) :=
  haveI : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι; inferInstance

theorem separationQuotientSMul_mk (ι : A₀ →⋆ₙₐ[ℂ] A) [IsPosSemidefCStarModuleAlong ι E]
    (a₀ : A₀) (x : E) :
    (letI := separationQuotientSMul (E := E) ι; a₀ • SeparationQuotient.mk x) =
      SeparationQuotient.mk (a₀ • x) := (rfl)

/-- On `SeparationQuotient E`, `separationQuotientInner` and `separationQuotientSMul` satisfy
`IsPosSemidefCStarModuleAlong`. -/
theorem isPosSemidefCStarModuleAlong_separationQuotient {ι : A₀ →⋆ₙₐ[ℂ] A}
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    @IsPosSemidefCStarModuleAlong A₀ A _ _ _ _ _ _ _ _ ι (SeparationQuotient E) _ _
      (separationQuotientSMul ι) _ (separationQuotientInner hι) := by
  let : Inner A (SeparationQuotient E) := separationQuotientInner hι
  let : SMul A₀ (SeparationQuotient E) := separationQuotientSMul ι
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  have hmk := SeparationQuotient.surjective_mk (X := E)
  exact
    { inner_add_right := fun {x y z} ↦ by
        rcases hmk x with ⟨x, rfl⟩; rcases hmk y with ⟨y, rfl⟩; rcases hmk z with ⟨z, rfl⟩
        exact inner_add_right (ι := ι) (x := x) (y := y) (z := z)
      inner_self_nonneg := fun {x} ↦ by
        rcases hmk x with ⟨x, rfl⟩; exact inner_self_nonneg (ι := ι) (x := x)
      inner_op_smul_right := fun {a₀ x y} ↦ by
        rcases hmk x with ⟨x, rfl⟩; rcases hmk y with ⟨y, rfl⟩
        exact inner_op_smul_right (ι := ι) (a₀ := a₀) (x := x) (y := y)
      inner_smul_right_complex := fun {z x y} ↦ by
        rcases hmk x with ⟨x, rfl⟩; rcases hmk y with ⟨y, rfl⟩
        exact inner_smul_right_complex (ι := ι) (z := z) (x := x) (y := y)
      star_inner := fun x y ↦ by
        rcases hmk x with ⟨x, rfl⟩; rcases hmk y with ⟨y, rfl⟩; exact star_inner (ι := ι) x y
      norm_eq_sqrt_norm_inner_self := fun x ↦ by
        rcases hmk x with ⟨x, rfl⟩
        rw [SeparationQuotient.norm_mk]; exact norm_eq_sqrt_norm_inner_self (ι := ι) x }

end QuotientStructure

section LiftOfInner

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

section Explicit

variable (ι : A₀ →⋆ₙₐ[ℂ] A) [IsPosSemidefCStarModuleAlong ι E]
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- **Universal property of `SeparationQuotient E` for inner-product-preserving maps:** any
`ℂ`-linear map `f : E →ₗ[ℂ] F` into a pre-Hilbert `A`-module `F` preserving `inner A` lifts to a
linear isometry `SeparationQuotient E →ₗᵢ[ℂ] F`. -/
noncomputable def separationQuotientLiftOfInner : SeparationQuotient E →ₗᵢ[ℂ] F :=
  SeparationQuotient.liftₗᵢ ⟨f, fun x ↦ by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
      norm_eq_sqrt_norm_inner_self (ι := ι) x]⟩

@[simp] theorem separationQuotientLiftOfInner_mk (x : E) :
    separationQuotientLiftOfInner ι f hf (SeparationQuotient.mk x) = f x :=
  SeparationQuotient.liftₗᵢ_mk _ x
theorem eq_separationQuotientLiftOfInner_iff (g : SeparationQuotient E →ₗᵢ[ℂ] F) :
    g = separationQuotientLiftOfInner ι f hf ↔
      ∀ x : E, g (SeparationQuotient.mk x) = f x :=
  SeparationQuotient.eq_liftₗᵢ_iff _ g
@[simp] theorem separationQuotientLiftOfInner_smul [StarOrderedRing A]
    (a₀ : A₀) (u : SeparationQuotient E) :
    separationQuotientLiftOfInner ι f hf (letI := separationQuotientSMul (E := E) ι; a₀ • u) =
      ι a₀ • separationQuotientLiftOfInner ι f hf u := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  exact SeparationQuotient.liftₗᵢ_smul _ (map_smul_of_inner_eq ι hf a₀) u

end Explicit

@[simp] theorem inner_separationQuotientLiftOfInner [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (u v : SeparationQuotient E) :
    inner A (separationQuotientLiftOfInner ι f hf u) (separationQuotientLiftOfInner ι f hf v) =
      (letI := separationQuotientInner (E := E) hι; inner A u v) := by
  rcases SeparationQuotient.surjective_mk u with ⟨x, rfl⟩
  rcases SeparationQuotient.surjective_mk v with ⟨y, rfl⟩; simp [hf]

end LiftOfInner
end SeparationQuotient
end TauCeti.IsPosSemidefCStarModuleAlong

namespace SeparationQuotient

open TauCeti

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

/-- `A`-valued inner product on the separated quotient of a positive semidefinite `A`-module. -/
noncomputable instance instInnerCStarModule : Inner A (SeparationQuotient E) :=
  IsPosSemidefCStarModuleAlong.separationQuotientInner (ι := .id ℂ A) denseRange_id

/-- The separated quotient of a positive semidefinite `A`-module is a pre-Hilbert `A`-module
(`CStarModule A (SeparationQuotient E)`). -/
noncomputable instance instCStarModule : CStarModule A (SeparationQuotient E) :=
  let h := IsPosSemidefCStarModuleAlong.isPosSemidefCStarModuleAlong_separationQuotient
    (E := E) (ι := .id ℂ A) denseRange_id
  letI : PosSemidefCStarModule A (SeparationQuotient E) :=
    { toInner := instInnerCStarModule, inner_add_right := h.inner_add_right,
      inner_self_nonneg := h.inner_self_nonneg, inner_op_smul_right := h.inner_op_smul_right,
      inner_smul_right_complex := h.inner_smul_right_complex, star_inner := h.star_inner,
      norm_eq_sqrt_norm_inner_self := h.norm_eq_sqrt_norm_inner_self }
  PosSemidefCStarModule.toCStarModuleOfNormedAddCommGroup

-- Ensures `instCStarModule` at `A = ℂ` is defeq to `WithCStarModule.instCStarModuleComplex`.
example {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (SeparationQuotient H)) =
      WithCStarModule.instCStarModuleComplex := by with_reducible_and_instances rfl

end SeparationQuotient

namespace TauCeti.PosSemidefCStarModule

@[simp] theorem inner_mk_mk {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [PosSemidefCStarModule A E] (x y : E) :
    inner A (SeparationQuotient.mk x) (SeparationQuotient.mk y) = inner A x y := (rfl)

end TauCeti.PosSemidefCStarModule
