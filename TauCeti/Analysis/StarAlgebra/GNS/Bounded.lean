/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Bounded GNS operators and Hilbert-space completions

Given a positive linear functional `φ : StarPositiveFunctional A` on a complex star algebra `A`,
the algebraic GNS quotient `φ.GNS` is an inner product space carrying left multiplication
`φ.leftMul a : Module.End ℂ φ.GNS`, which need not be bounded. Completing `φ.GNS` produces the
Hilbert space `φ.HilbertGNS := UniformSpace.Completion φ.GNS` together with the dense class map
`φ.hilbertClassMap : A →ₗ[ℂ] φ.HilbertGNS`.

For `a : A` and `R ≥ 0`, left multiplication `φ.leftMul a` is bounded by `R` on `φ.GNS` if and only
if the quadratic-form inequality
`φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)`
holds for every `b : A`. Because `φ.leftMul (star a)` is the formal adjoint of `φ.leftMul a` on
`φ.GNS`, Cauchy–Schwarz shows that this bound is equivalent to the symmetric inequality for
`star a`: boundedness of `φ.leftMul a` implies boundedness of `φ.leftMul (star a)` with the same
norm bound. Extending `φ.leftMulCLM ha` to the completion produces `φ.hilbertLeftMul ha`, an
operator on `φ.HilbertGNS` of the same norm whose Hilbert-space adjoint is `φ.hilbertLeftMul` for
`star a`.

When `A` is unital, the elements `a : A` with `Continuous (φ.leftMul a)` form a unital star
subalgebra `φ.boundedSubalgebra : StarSubalgebra ℂ A` with a canonical `⋆`-representation in the
C⋆-algebra `φ.HilbertGNS →L[ℂ] φ.HilbertGNS`. Whenever a star-generating set of `A` acts boundedly,
`φ.boundedSubalgebra = ⊤` and `φ` is realized as the vector functional
`φ.hilbertPositiveLinearMap` at `φ.hilbertCyclicVector` (a unit vector when `φ 1 = 1`). Conversely,
any realization of `φ` through a `⋆`-homomorphism into a C⋆-algebra satisfies the quadratic-form
bound with `R = ‖f a‖`.

## Main definitions

* `TauCeti.StarPositiveFunctional.HilbertGNS`: the Hilbert-space completion of `φ.GNS`.
* `TauCeti.StarPositiveFunctional.hilbertClassMap`: the dense linear class map
  `A →ₗ[ℂ] φ.HilbertGNS`.
* `TauCeti.StarPositiveFunctional.leftMulCLM`, `TauCeti.StarPositiveFunctional.hilbertLeftMul`:
  bounded left multiplication on `φ.GNS` and on `φ.HilbertGNS`.
* `TauCeti.StarPositiveFunctional.hilbertCyclicVector`,
  `TauCeti.StarPositiveFunctional.hilbertPositiveLinearMap`: the cyclic vector in `φ.HilbertGNS`
  and its positive vector functional on `φ.HilbertGNS →L[ℂ] φ.HilbertGNS`.
* `TauCeti.StarPositiveFunctional.boundedSubalgebra`,
  `TauCeti.StarPositiveFunctional.boundedSubalgebraRepresentation`,
  `TauCeti.StarPositiveFunctional.boundedRepresentation`: the `⋆`-subalgebra of boundedly acting
  elements and its Hilbert-space `⋆`-representation.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
* K. Schmüdgen, *Unbounded Operator Algebras and Representation Theory*, §8.6.
-/

public section

noncomputable section

open UniformSpace
open scoped ComplexOrder InnerProductSpace InnerProduct

namespace TauCeti

namespace StarPositiveFunctional

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (φ : StarPositiveFunctional A)

/-- The Hilbert-space completion of the algebraic GNS inner product space `φ.GNS`. -/
abbrev HilbertGNS : Type _ := Completion φ.GNS

/-- The canonical linear map sending an algebra element to its class in the completed GNS Hilbert
space. -/
def hilbertClassMap : A →ₗ[ℂ] φ.HilbertGNS :=
  (Completion.toComplₗᵢ (𝕜 := ℂ) (E := φ.GNS)).toLinearMap.comp φ.classMap

theorem hilbertClassMap_apply (a : A) :
    φ.hilbertClassMap a = (φ.classMap a : φ.HilbertGNS) := by
  simp [hilbertClassMap]

/-- Algebra classes are dense in the completed GNS Hilbert space. -/
theorem denseRange_hilbertClassMap : DenseRange φ.hilbertClassMap := by
  have hcoe : (⇑φ.hilbertClassMap : A → φ.HilbertGNS) =
      (fun x : φ.GNS => (x : φ.HilbertGNS)) ∘ φ.classMap :=
    funext φ.hilbertClassMap_apply
  rw [hcoe]
  exact Completion.denseRange_coe.comp φ.classMap_surjective.denseRange
    (Completion.continuous_coe φ.GNS)

/-- Continuous linear maps out of `φ.HilbertGNS` into a Hausdorff space are determined by their
values on algebra classes. -/
theorem hilbertClassMap_clm_ext {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [T2Space E] {f g : φ.HilbertGNS →L[ℂ] E}
    (h : ∀ a, f (φ.hilbertClassMap a) = g (φ.hilbertClassMap a)) : f = g :=
  DFunLike.coe_injective <|
    φ.denseRange_hilbertClassMap.equalizer f.continuous g.continuous (funext h)

@[simp]
theorem inner_hilbertClassMap (a b : A) :
    ⟪φ.hilbertClassMap a, φ.hilbertClassMap b⟫_ℂ = φ (star a * b) := by
  rw [φ.hilbertClassMap_apply, φ.hilbertClassMap_apply, Completion.inner_coe, φ.inner_classMap]

@[simp]
theorem norm_hilbertClassMap (a : A) :
    ‖φ.hilbertClassMap a‖ = ‖φ.classMap a‖ := by
  rw [φ.hilbertClassMap_apply, Completion.norm_coe]

theorem norm_hilbertClassMap_sq (a : A) :
    ‖φ.hilbertClassMap a‖ ^ 2 = (φ (star a * a)).re := by
  rw [φ.norm_hilbertClassMap, φ.norm_classMap_sq]

@[simp]
theorem hilbertClassMap_eq_zero_iff (a : A) :
    φ.hilbertClassMap a = 0 ↔ φ (star a * a) = 0 := by
  rw [← norm_eq_zero (a := φ.hilbertClassMap a), φ.norm_hilbertClassMap, norm_eq_zero,
    φ.classMap_eq_zero_iff]

/-- The quadratic-form inequality `φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)` is
the squared GNS norm bound for `φ.leftMul a` at `φ.classMap b`. -/
theorem apply_star_mul_self_le_iff_norm_leftMul_sq_le (a b : A) (R : ℝ) :
    φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) ↔
      ‖φ.leftMul a (φ.classMap b)‖ ^ 2 ≤ R ^ 2 * ‖φ.classMap b‖ ^ 2 := by
  have him₁ : (φ (star b * star a * a * b)).im = 0 := by
    simpa [mul_assoc] using (φ.square_nonneg (a * b)).2.symm
  have him₂ : (φ (star b * b)).im = 0 := (φ.square_nonneg b).2.symm
  have hre₁ : ‖φ.leftMul a (φ.classMap b)‖ ^ 2 = (φ (star b * star a * a * b)).re := by
    simpa [mul_assoc] using φ.norm_classMap_sq (a * b)
  rw [← Complex.ofReal_pow, Complex.le_def, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    him₁, him₂, mul_zero, eq_self, and_true, hre₁, φ.norm_classMap_sq b]

/-- For `R ≥ 0`, left multiplication by `a` on `φ.GNS` is bounded by `R` if and only if
`φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)` for all `b : A`. -/
theorem forall_norm_leftMul_le_iff {a : A} {R : ℝ} (hR : 0 ≤ R) :
    (∀ x : φ.GNS, ‖φ.leftMul a x‖ ≤ R * ‖x‖) ↔
      ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  rw [φ.classMap_surjective.forall]
  refine forall_congr' fun b => ?_
  rw [φ.apply_star_mul_self_le_iff_norm_leftMul_sq_le, ← mul_pow,
    sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))]

/-- Boundedness of `φ.leftMul a` by `R` on `φ.GNS` is symmetric under passing to `star a`, because
`φ.leftMul (star a)` is the formal adjoint of `φ.leftMul a` on `φ.GNS`. -/
theorem forall_norm_leftMul_star_le_iff (a : A) (R : ℝ) :
    (∀ x : φ.GNS, ‖φ.leftMul (star a) x‖ ≤ R * ‖x‖) ↔
      ∀ x : φ.GNS, ‖φ.leftMul a x‖ ≤ R * ‖x‖ := by
  suffices ∀ c : A, (∀ x : φ.GNS, ‖φ.leftMul c x‖ ≤ R * ‖x‖) →
      ∀ y : φ.GNS, ‖φ.leftMul (star c) y‖ ≤ R * ‖y‖ from
    ⟨fun h x => by simpa using this (star a) h x, this a⟩
  intro c hc y
  set z := φ.leftMul (star c) y
  rcases (norm_nonneg z).eq_or_lt with hz | hz
  · exact hz.symm.trans_le ((norm_nonneg _).trans (hc y))
  · have hsq : ‖z‖ ^ 2 ≤ R * ‖y‖ * ‖z‖ := by
      calc ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) z
        _ = RCLike.re ⟪y, φ.leftMul c z⟫_ℂ := by
          simpa [z] using congrArg RCLike.re (φ.inner_leftMul (star c) y z)
        _ ≤ ‖⟪y, φ.leftMul c z⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖y‖ * ‖φ.leftMul c z‖ := norm_inner_le_norm y (φ.leftMul c z)
        _ ≤ ‖y‖ * (R * ‖z‖) := by gcongr; exact hc z
        _ = R * ‖y‖ * ‖z‖ := by ring
    nlinarith

/-- The quadratic-form bound for `star a` is equivalent to the same bound for `a`. -/
theorem forall_apply_star_mul_self_star_le_iff (a : A) (R : ℝ) :
    (∀ b : A, φ (star b * a * star a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)) ↔
      ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  have h1 := φ.forall_norm_leftMul_le_iff (a := star a) (abs_nonneg R)
  have h2 := φ.forall_norm_leftMul_le_iff (a := a) (abs_nonneg R)
  have hRsq : ((|R| : ℝ) : ℂ) ^ 2 = (R : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [star_star, hRsq] at h1
  rw [hRsq] at h2
  exact h1.symm.trans ((φ.forall_norm_leftMul_star_le_iff a |R|).trans h2)

/-- Left multiplication by `a` on `φ.GNS` is continuous if and only if some `R ≥ 0` bounds all
quadratic pairings `φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)`. -/
theorem continuous_leftMul_iff (a : A) :
    Continuous (φ.leftMul a) ↔
      ∃ R : ℝ, 0 ≤ R ∧ ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  constructor
  · intro ha
    obtain ⟨R, hR, hbound⟩ := SemilinearMapClass.bound_of_continuous (φ.leftMul a) ha
    exact ⟨R, hR.le, (φ.forall_norm_leftMul_le_iff hR.le).mp hbound⟩
  · rintro ⟨R, hR, hbound⟩
    exact ((φ.leftMul a).mkContinuousOfExistsBound
      ⟨R, (φ.forall_norm_leftMul_le_iff hR).mpr hbound⟩).continuous

/-- Continuity of `φ.leftMul (star a)` is equivalent to continuity of `φ.leftMul a`. -/
@[simp]
theorem continuous_leftMul_star_iff (a : A) :
    Continuous (φ.leftMul (star a)) ↔ Continuous (φ.leftMul a) := by
  simp_rw [φ.continuous_leftMul_iff, star_star, φ.forall_apply_star_mul_self_star_le_iff]

/-- Bounded left multiplication on the algebraic GNS space `φ.GNS` as a continuous linear map. -/
def leftMulCLM {a : A} (ha : Continuous (φ.leftMul a)) : φ.GNS →L[ℂ] φ.GNS :=
  ⟨φ.leftMul a, ha⟩

@[simp]
theorem leftMulCLM_toLinearMap {a : A} (ha : Continuous (φ.leftMul a)) :
    (φ.leftMulCLM ha).toLinearMap = φ.leftMul a :=
  (rfl)

@[simp]
theorem leftMulCLM_apply {a : A} (ha : Continuous (φ.leftMul a)) (x : φ.GNS) :
    φ.leftMulCLM ha x = φ.leftMul a x :=
  (rfl)

theorem norm_leftMulCLM_le_iff {a : A} (ha : Continuous (φ.leftMul a)) {R : ℝ} (hR : 0 ≤ R) :
    ‖φ.leftMulCLM ha‖ ≤ R ↔
      ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) :=
  ((φ.leftMulCLM ha).opNorm_le_iff hR).trans (φ.forall_norm_leftMul_le_iff hR)

/-- Bounded left multiplication extended by continuity to the completed GNS Hilbert space
`φ.HilbertGNS`. -/
def hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) : φ.HilbertGNS →L[ℂ] φ.HilbertGNS :=
  (φ.leftMulCLM ha).completion

@[simp]
theorem hilbertLeftMul_coe {a : A} (ha : Continuous (φ.leftMul a)) (x : φ.GNS) :
    φ.hilbertLeftMul ha (x : φ.HilbertGNS) = (φ.leftMul a x : φ.HilbertGNS) :=
  ContinuousLinearMap.completion_apply_coe (φ.leftMulCLM ha) x

@[simp]
theorem hilbertLeftMul_hilbertClassMap {a : A} (ha : Continuous (φ.leftMul a)) (b : A) :
    φ.hilbertLeftMul ha (φ.hilbertClassMap b) = φ.hilbertClassMap (a * b) := by
  rw [φ.hilbertClassMap_apply, φ.hilbertLeftMul_coe, φ.leftMul_classMap, φ.hilbertClassMap_apply]

@[simp]
theorem norm_hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) :
    ‖φ.hilbertLeftMul ha‖ = ‖φ.leftMulCLM ha‖ := by
  rw [hilbertLeftMul, ContinuousLinearMap.norm_completion]

/-- For `R ≥ 0`, the operator norm of `φ.hilbertLeftMul ha` is at most `R` if and only if
`φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b)` for all `b : A`. -/
theorem norm_hilbertLeftMul_le_iff {a : A} (ha : Continuous (φ.leftMul a)) {R : ℝ} (hR : 0 ≤ R) :
    ‖φ.hilbertLeftMul ha‖ ≤ R ↔
      ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  rw [φ.norm_hilbertLeftMul, φ.norm_leftMulCLM_le_iff ha hR]

/-- Left multiplication on `φ.HilbertGNS` respects inner products with `star a`. -/
theorem inner_hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) (x y : φ.HilbertGNS) :
    ⟪φ.hilbertLeftMul ha x, y⟫_ℂ =
      ⟪x, φ.hilbertLeftMul ((φ.continuous_leftMul_star_iff a).mpr ha) y⟫_ℂ := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y => simp [φ.inner_leftMul]

/-- The Hilbert-space adjoint of `φ.hilbertLeftMul ha` is `φ.hilbertLeftMul` for `star a`. -/
@[simp]
theorem adjoint_hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) :
    (φ.hilbertLeftMul ha)† = φ.hilbertLeftMul ((φ.continuous_leftMul_star_iff a).mpr ha) :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    rw [← inner_conj_symm, ← inner_conj_symm x, φ.inner_hilbertLeftMul ha y x]).symm

/-- The C⋆-involution on `φ.HilbertGNS →L[ℂ] φ.HilbertGNS` sends `φ.hilbertLeftMul ha` to
`φ.hilbertLeftMul` for `star a`. -/
@[simp]
theorem star_hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) :
    star (φ.hilbertLeftMul ha) = φ.hilbertLeftMul ((φ.continuous_leftMul_star_iff a).mpr ha) := by
  rw [ContinuousLinearMap.star_eq_adjoint, φ.adjoint_hilbertLeftMul]

theorem continuous_leftMul_zero : Continuous (φ.leftMul (0 : A)) := by
  have h : φ.leftMul (0 : A) = 0 := by
    rw [← φ.nonUnitalRepresentation_apply, map_zero]
  rw [h]
  exact continuous_zero

theorem continuous_leftMul_add {a b : A} (ha : Continuous (φ.leftMul a))
    (hb : Continuous (φ.leftMul b)) : Continuous (φ.leftMul (a + b)) := by
  have h : φ.leftMul (a + b) = φ.leftMul a + φ.leftMul b := by
    simp only [← φ.nonUnitalRepresentation_apply, map_add]
  rw [h]
  exact ha.add hb

theorem continuous_leftMul_smul (c : ℂ) {a : A} (ha : Continuous (φ.leftMul a)) :
    Continuous (φ.leftMul (c • a)) := by
  have h : φ.leftMul (c • a) = c • φ.leftMul a := by
    simp only [← φ.nonUnitalRepresentation_apply, map_smul]
  rw [h]
  exact ha.const_smul c

theorem continuous_leftMul_mul {a b : A} (ha : Continuous (φ.leftMul a))
    (hb : Continuous (φ.leftMul b)) : Continuous (φ.leftMul (a * b)) := by
  have h : ⇑(φ.leftMul (a * b)) = ⇑(φ.leftMul a) ∘ ⇑(φ.leftMul b) := by
    ext x
    obtain ⟨c, rfl⟩ := φ.classMap_surjective x
    simp [mul_assoc]
  rw [h]
  exact ha.comp hb

@[simp]
theorem hilbertLeftMul_zero : φ.hilbertLeftMul φ.continuous_leftMul_zero = 0 :=
  φ.hilbertClassMap_clm_ext fun b => by simp

theorem hilbertLeftMul_add {a b : A} (ha : Continuous (φ.leftMul a))
    (hb : Continuous (φ.leftMul b)) :
    φ.hilbertLeftMul (φ.continuous_leftMul_add ha hb) =
      φ.hilbertLeftMul ha + φ.hilbertLeftMul hb :=
  φ.hilbertClassMap_clm_ext fun c => by simp [add_mul]

theorem hilbertLeftMul_smul (r : ℂ) {a : A} (ha : Continuous (φ.leftMul a)) :
    φ.hilbertLeftMul (φ.continuous_leftMul_smul r ha) = r • φ.hilbertLeftMul ha :=
  φ.hilbertClassMap_clm_ext fun b => by simp [smul_mul_assoc]

theorem hilbertLeftMul_mul {a b : A} (ha : Continuous (φ.leftMul a))
    (hb : Continuous (φ.leftMul b)) :
    φ.hilbertLeftMul (φ.continuous_leftMul_mul ha hb) =
      φ.hilbertLeftMul ha * φ.hilbertLeftMul hb :=
  φ.hilbertClassMap_clm_ext fun c => by simp [mul_assoc]

end NonUnital

/-- Any realization of `φ` through a `⋆`-homomorphism `f` into a C⋆-algebra `C` with a positive
functional `ω` forces the quadratic-form bound with constant `R` whenever `‖f a‖ ≤ R`. -/
theorem apply_star_mul_self_le_of_cstar {A C : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A]
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C] (φ : StarPositiveFunctional A)
    (ω : C →ₚ[ℂ] ℂ) {F : Type*} [FunLike F A C] [NonUnitalAlgHomClass F ℂ A C]
    [StarHomClass F A C] (f : F) (hφ : ∀ x, ω (f x) = φ x) {a : A} {R : ℝ} (ha : ‖f a‖ ≤ R)
    (b : A) :
    φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  have hle : star (f b) * (star (f a) * f a) * f b ≤ (R ^ 2) • (star (f b) * f b) := by
    calc star (f b) * (star (f a) * f a) * f b
        ≤ ‖star (f a) * f a‖ • (star (f b) * f b) :=
          CStarAlgebra.star_left_conjugate_le_norm_smul (f b) (star (f a) * f a)
      _ = (‖f a‖ ^ 2) • (star (f b) * f b) := by
          rw [CStarRing.norm_star_mul_self, sq]
      _ ≤ (R ^ 2) • (star (f b) * f b) :=
          smul_le_smul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ha 2)
            (star_mul_self_nonneg (f b))
  have hω := OrderHomClass.mono ω hle
  rw [LinearMapClass.map_smul_of_tower, Complex.real_smul, Complex.ofReal_pow] at hω
  simp_rw [← StarHomClass.map_star f, ← map_mul f, hφ, ← mul_assoc] at hω
  exact hω

section Unital

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (φ : StarPositiveFunctional A)

theorem continuous_leftMul_one : Continuous (φ.leftMul (1 : A)) := by
  have h : φ.leftMul (1 : A) = LinearMap.id := by
    rw [← φ.representation_apply, map_one]
    rfl
  rw [h]
  exact continuous_id

theorem continuous_leftMul_algebraMap (r : ℂ) : Continuous (φ.leftMul (algebraMap ℂ A r)) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact φ.continuous_leftMul_smul r φ.continuous_leftMul_one

@[simp]
theorem hilbertLeftMul_one : φ.hilbertLeftMul φ.continuous_leftMul_one = 1 :=
  φ.hilbertClassMap_clm_ext fun b => by simp

theorem hilbertLeftMul_algebraMap (r : ℂ) :
    φ.hilbertLeftMul (φ.continuous_leftMul_algebraMap r) =
      algebraMap ℂ (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) r :=
  φ.hilbertClassMap_clm_ext fun b => by simp [Algebra.algebraMap_eq_smul_one]

/-- The canonical cyclic vector in the completed GNS Hilbert space: the class of `1`. -/
def hilbertCyclicVector : φ.HilbertGNS :=
  (φ.cyclicVector : φ.HilbertGNS)

theorem hilbertCyclicVector_def : φ.hilbertCyclicVector = φ.hilbertClassMap 1 := by
  rw [hilbertCyclicVector, φ.cyclicVector_def, φ.hilbertClassMap_apply]

@[simp]
theorem hilbertLeftMul_hilbertCyclicVector {a : A} (ha : Continuous (φ.leftMul a)) :
    φ.hilbertLeftMul ha φ.hilbertCyclicVector = φ.hilbertClassMap a := by
  simp [φ.hilbertCyclicVector_def]

@[simp]
theorem inner_hilbertCyclicVector_hilbertClassMap (a : A) :
    ⟪φ.hilbertCyclicVector, φ.hilbertClassMap a⟫_ℂ = φ a := by
  simp [φ.hilbertCyclicVector_def]

@[simp]
theorem inner_hilbertClassMap_hilbertCyclicVector (a : A) :
    ⟪φ.hilbertClassMap a, φ.hilbertCyclicVector⟫_ℂ = φ (star a) := by
  simp [φ.hilbertCyclicVector_def]

@[simp high]
theorem inner_hilbertCyclicVector_self :
    ⟪φ.hilbertCyclicVector, φ.hilbertCyclicVector⟫_ℂ = φ 1 := by
  rw [φ.hilbertCyclicVector_def, φ.inner_hilbertClassMap]
  simp

@[simp]
theorem norm_hilbertCyclicVector_eq : ‖φ.hilbertCyclicVector‖ = ‖φ.cyclicVector‖ :=
  Completion.norm_coe φ.cyclicVector

theorem norm_hilbertCyclicVector_sq : ‖φ.hilbertCyclicVector‖ ^ 2 = (φ 1).re := by
  rw [φ.norm_hilbertCyclicVector_eq, φ.norm_cyclicVector_sq]

/-- A normalized positive functional gives a unit cyclic vector in the completed GNS Hilbert
space. -/
theorem norm_hilbertCyclicVector (hφ : φ 1 = 1) : ‖φ.hilbertCyclicVector‖ = 1 := by
  rw [φ.norm_hilbertCyclicVector_eq, φ.norm_cyclicVector hφ]

/-- The vector functional `T ↦ ⟪φ.hilbertCyclicVector, T φ.hilbertCyclicVector⟫_ℂ` on bounded
operators of the completed GNS Hilbert space, as a `PositiveLinearMap`. When `φ 1 = 1`, it is a
state on the C⋆-algebra `φ.HilbertGNS →L[ℂ] φ.HilbertGNS`. -/
def hilbertPositiveLinearMap : (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) →ₚ[ℂ] ℂ :=
  ContinuousLinearMap.innerPositiveLinearMap ℂ φ.hilbertCyclicVector

theorem hilbertPositiveLinearMap_def :
    φ.hilbertPositiveLinearMap =
      ContinuousLinearMap.innerPositiveLinearMap ℂ φ.hilbertCyclicVector :=
  (rfl)

@[simp]
theorem hilbertPositiveLinearMap_apply (T : φ.HilbertGNS →L[ℂ] φ.HilbertGNS) :
    φ.hilbertPositiveLinearMap T = ⟪φ.hilbertCyclicVector, T φ.hilbertCyclicVector⟫_ℂ := by
  simp [hilbertPositiveLinearMap]

theorem hilbertPositiveLinearMap_one : φ.hilbertPositiveLinearMap 1 = φ 1 := by
  simp

theorem hilbertPositiveLinearMap_hilbertLeftMul {a : A} (ha : Continuous (φ.leftMul a)) :
    φ.hilbertPositiveLinearMap (φ.hilbertLeftMul ha) = φ a := by
  simp

/-- The unital star subalgebra of elements `a : A` whose GNS left multiplication is continuous. -/
def boundedSubalgebra : StarSubalgebra ℂ A where
  carrier := {a : A | Continuous (φ.leftMul a)}
  mul_mem' := φ.continuous_leftMul_mul
  one_mem' := φ.continuous_leftMul_one
  add_mem' := φ.continuous_leftMul_add
  zero_mem' := φ.continuous_leftMul_zero
  algebraMap_mem' := φ.continuous_leftMul_algebraMap
  star_mem' {a} ha := (φ.continuous_leftMul_star_iff a).mpr ha

@[simp]
theorem mem_boundedSubalgebra {a : A} :
    a ∈ φ.boundedSubalgebra ↔ Continuous (φ.leftMul a) := by
  rfl

/-- The canonical `⋆`-representation of `φ.boundedSubalgebra` by bounded operators on the completed
GNS Hilbert space `φ.HilbertGNS`. -/
def boundedSubalgebraRepresentation :
    φ.boundedSubalgebra →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) where
  toFun x := φ.hilbertLeftMul (φ.mem_boundedSubalgebra.mp x.2)
  map_one' := φ.hilbertLeftMul_one
  map_mul' x y := φ.hilbertLeftMul_mul (φ.mem_boundedSubalgebra.mp x.2)
    (φ.mem_boundedSubalgebra.mp y.2)
  map_zero' := φ.hilbertLeftMul_zero
  map_add' x y := φ.hilbertLeftMul_add (φ.mem_boundedSubalgebra.mp x.2)
    (φ.mem_boundedSubalgebra.mp y.2)
  commutes' r := φ.hilbertLeftMul_algebraMap r
  map_star' x := (φ.star_hilbertLeftMul (φ.mem_boundedSubalgebra.mp x.2)).symm

@[simp]
theorem boundedSubalgebraRepresentation_apply (x : φ.boundedSubalgebra) :
    φ.boundedSubalgebraRepresentation x = φ.hilbertLeftMul (φ.mem_boundedSubalgebra.mp x.2) :=
  (rfl)

/-- If every element of a star-generating set acts boundedly on `φ.GNS`, then every element of `A`
acts boundedly. -/
theorem boundedSubalgebra_eq_top_of_adjoin_eq_top {s : Set A}
    (hs : StarAlgebra.adjoin ℂ s = ⊤) (hb : ∀ a ∈ s, Continuous (φ.leftMul a)) :
    φ.boundedSubalgebra = ⊤ :=
  eq_top_iff.mpr (hs ▸ StarAlgebra.adjoin_le fun a ha => φ.mem_boundedSubalgebra.mpr (hb a ha))

theorem continuous_leftMul_of_adjoin_eq_top {s : Set A} (hs : StarAlgebra.adjoin ℂ s = ⊤)
    (hb : ∀ a ∈ s, Continuous (φ.leftMul a)) (a : A) : Continuous (φ.leftMul a) :=
  φ.mem_boundedSubalgebra.mp <| (φ.boundedSubalgebra_eq_top_of_adjoin_eq_top hs hb).symm ▸ trivial

/-- When every element of `A` acts continuously on `φ.GNS`, left multiplication extends to a global
unital `⋆`-representation of `A` in the C⋆-algebra `φ.HilbertGNS →L[ℂ] φ.HilbertGNS`. -/
def boundedRepresentation (hA : ∀ a : A, Continuous (φ.leftMul a)) :
    A →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) where
  toFun a := φ.hilbertLeftMul (hA a)
  map_one' := φ.hilbertLeftMul_one
  map_mul' a b := φ.hilbertLeftMul_mul (hA a) (hA b)
  map_zero' := φ.hilbertLeftMul_zero
  map_add' a b := φ.hilbertLeftMul_add (hA a) (hA b)
  commutes' r := φ.hilbertLeftMul_algebraMap r
  map_star' a := (φ.star_hilbertLeftMul (hA a)).symm

theorem boundedRepresentation_apply (hA : ∀ a : A, Continuous (φ.leftMul a)) (a : A) :
    φ.boundedRepresentation hA a = φ.hilbertLeftMul (hA a) :=
  (rfl)

@[simp]
theorem boundedRepresentation_hilbertClassMap (hA : ∀ a : A, Continuous (φ.leftMul a))
    (a b : A) :
    φ.boundedRepresentation hA a (φ.hilbertClassMap b) = φ.hilbertClassMap (a * b) :=
  φ.hilbertLeftMul_hilbertClassMap (hA a) b

@[simp]
theorem boundedRepresentation_hilbertCyclicVector (hA : ∀ a : A, Continuous (φ.leftMul a))
    (a : A) :
    φ.boundedRepresentation hA a φ.hilbertCyclicVector = φ.hilbertClassMap a :=
  φ.hilbertLeftMul_hilbertCyclicVector (hA a)

/-- The canonical cyclic vector has dense orbit under `φ.boundedRepresentation hA`. -/
theorem denseRange_boundedRepresentation_hilbertCyclicVector
    (hA : ∀ a : A, Continuous (φ.leftMul a)) :
    DenseRange (fun a => φ.boundedRepresentation hA a φ.hilbertCyclicVector) := by
  simpa using φ.denseRange_hilbertClassMap

theorem hilbertPositiveLinearMap_boundedRepresentation
    (hA : ∀ a : A, Continuous (φ.leftMul a)) (a : A) :
    φ.hilbertPositiveLinearMap (φ.boundedRepresentation hA a) = φ a :=
  φ.hilbertPositiveLinearMap_hilbertLeftMul (hA a)

/-- `φ.boundedRepresentation hA` is the unique `⋆`-representation of `A` on `φ.HilbertGNS` sending
each `(a, [b])` to `[a * b]`. -/
theorem eq_boundedRepresentation {hA : ∀ a : A, Continuous (φ.leftMul a)}
    {π : A →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS)}
    (hπ : ∀ a b, π a (φ.hilbertClassMap b) = φ.hilbertClassMap (a * b)) :
    π = φ.boundedRepresentation hA := by
  ext a : 1
  exact φ.hilbertClassMap_clm_ext fun b => by simp [hπ]

end Unital

end StarPositiveFunctional

end TauCeti
