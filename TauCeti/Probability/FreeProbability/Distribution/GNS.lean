/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
public import TauCeti.Probability.FreeProbability.Distribution.Star
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.TFAE

/-!
# Algebraic and bounded GNS realizations of `⋆`-distributions

Given a positive linear functional `φ : StarPositiveFunctional (StarPolynomial ℂ ι)` on the
noncommutative `⋆`-polynomials, the GNS construction produces two distinct levels of operator
realization:

1. **Algebraic pre-Hilbert realization.** Without any boundedness hypothesis, `φ.GNS` is a complex
   inner product space carrying `φ.representation : StarPolynomial ℂ ι →ₐ[ℂ] Module.End ℂ φ.GNS`
   and the cyclic vector `φ.cyclicVector` (a unit vector when `φ 1 = 1`). Each generator pair
   `φ.representation (X i)` and `φ.representation (star (X i))` consists of formal adjoints on
   `φ.GNS`, and the pre-Hilbert vector functional `φ.algebraicPositiveLinearMap` recovers `φ` on all
   `⋆`-polynomials.
2. **Bounded C⋆-realization.** Fixing `R : ι → ℝ` with `0 ≤ R i`, left multiplication by `X i` on
   `φ.GNS` is bounded with norm at most `R i` if and only if
   `φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p)` for every
   `p : StarPolynomial ℂ ι`, which is automatically equivalent to the adjoint-generator inequality
   `φ (star p * X i * star (X i) * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p)`. Because the generators
   `X i` generate `StarPolynomial ℂ ι` as a `⋆`-algebra, continuity of `φ.leftMul (X i)` for every
   `i` extends `φ.representation` to a unital `⋆`-representation
   `φ.starPolynomialRepresentation hX : StarPolynomial ℂ ι →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS)`
   into bounded operators on the completed Hilbert space `φ.HilbertGNS`, with both
   `‖φ.starPolynomialRepresentation hX (X i)‖ ≤ R i` and
   `‖φ.starPolynomialRepresentation hX (star (X i))‖ ≤ R i`, realizing `φ` as the `⋆`-distribution
   of `i ↦ φ.starPolynomialRepresentation hX (X i)` under `φ.hilbertPositiveLinearMap`.

Conversely, any realization of `φ` as the `⋆`-distribution of a family `c` in a C⋆-algebra under a
positive linear functional with `‖c i‖ ≤ R i` forces the generator inequalities. Together these
yield `StarPositiveFunctional.boundedGNS_TFAE` and
`StarPositiveFunctional.exists_cstar_starDistribution_eq_iff`. Finally,
`exists_starPositiveFunctional_apply_one_not_continuous_leftMul_X` exhibits an explicit normalized
positive functional on `StarPolynomial ℂ ι` whose generator left multiplications are unbounded,
showing that positivity and normalization alone do not imply C⋆-realizability.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
* K. Schmüdgen, *Unbounded Operator Algebras and Representation Theory*, §8.6.
-/

public section

noncomputable section

namespace TauCeti

open StarPolynomial
open scoped ComplexOrder InnerProductSpace

section PullbackDistribution

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- The `⋆`-distribution of a family `a : ι → A` with respect to a positive functional `ψ`, bundled
as a `StarPositiveFunctional` on `StarPolynomial ℂ ι`. -/
def starDistributionPositiveFunctional (ψ : StarPositiveFunctional A) (a : ι → A) :
    StarPositiveFunctional (StarPolynomial ℂ ι) :=
  ψ.comp (StarPolynomial.lift a)

@[simp]
theorem starDistributionPositiveFunctional_apply (ψ : StarPositiveFunctional A) (a : ι → A)
    (p : StarPolynomial ℂ ι) :
    starDistributionPositiveFunctional ψ a p = starDistribution ψ.toLinearMap a p := by
  simp [starDistributionPositiveFunctional]

@[simp]
theorem toLinearMap_starDistributionPositiveFunctional (ψ : StarPositiveFunctional A) (a : ι → A) :
    (starDistributionPositiveFunctional ψ a).toLinearMap = starDistribution ψ.toLinearMap a := by
  ext p
  exact starDistributionPositiveFunctional_apply ψ a p

theorem starDistributionPositiveFunctional_one (ψ : StarPositiveFunctional A) (a : ι → A) :
    starDistributionPositiveFunctional ψ a 1 = ψ 1 := by
  simp

@[simp]
theorem starDistributionPositiveFunctional_X {ι : Type*}
    (φ : StarPositiveFunctional (StarPolynomial ℂ ι)) :
    starDistributionPositiveFunctional φ X = φ := by
  ext p
  simp

end PullbackDistribution

namespace StarPositiveFunctional

section AlgebraicRealization

variable {ι : Type*} (φ : StarPositiveFunctional (StarPolynomial ℂ ι))

/-- Free-algebra evaluation of the formal-adjoint generator pair `φ.representation ∘ withStar X`
recovers `φ.representation` on every `⋆`-polynomial. -/
theorem freeAlgebraLift_representation_withStar (p : StarPolynomial ℂ ι) :
    FreeAlgebra.lift ℂ (φ.representation ∘ withStar (X (R := ℂ) (ι := ι)))
      (toFreeAlgebra ℂ ι p) = φ.representation p := by
  induction p using StarPolynomial.induction with
  | algebraMap r => simp
  | X i => simp
  | star_X i => simp
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Every positive functional on `StarPolynomial ℂ ι` is realized algebraically on its pre-Hilbert
GNS space `φ.GNS` as the joint distribution of the formal-adjoint pair family
`φ.representation ∘ withStar X` under `φ.algebraicPositiveLinearMap`. -/
@[simp]
theorem jointDistribution_algebraicPositiveLinearMap_comp_toFreeAlgebra :
    (jointDistribution φ.algebraicPositiveLinearMap.toLinearMap
        (φ.representation ∘ withStar (X (R := ℂ) (ι := ι)))).comp
      (toFreeAlgebra ℂ ι).toLinearMap = φ.toLinearMap := by
  ext p
  simp [jointDistribution_apply, φ.freeAlgebraLift_representation_withStar]

/-- For a positive functional `ψ` and family `a`, the algebraic GNS representation of
`starDistributionPositiveFunctional ψ a` realizes the joint distribution of `withStar a`. -/
theorem jointDistribution_algebraicPositiveLinearMap_starDistribution {A : Type*} [Ring A]
    [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ψ : StarPositiveFunctional A) (a : ι → A) :
    jointDistribution
        (starDistributionPositiveFunctional ψ a).algebraicPositiveLinearMap.toLinearMap
        ((starDistributionPositiveFunctional ψ a).representation ∘
          withStar (X (R := ℂ) (ι := ι))) =
      jointDistribution ψ.toLinearMap (withStar a) := by
  ext p
  obtain ⟨q, rfl⟩ := (toFreeAlgebra ℂ ι).surjective p
  have h := LinearMap.congr_fun
    (jointDistribution_algebraicPositiveLinearMap_comp_toFreeAlgebra
      (starDistributionPositiveFunctional ψ a)) q
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    toLinearMap_starDistributionPositiveFunctional, starDistribution_eq_jointDistribution_comp]
    using h

end AlgebraicRealization

section BoundedRealization

variable {ι : Type*} (φ : StarPositiveFunctional (StarPolynomial ℂ ι))

/-- If left multiplication by every generator `X i` is continuous on `φ.GNS`, then left
multiplication by every `⋆`-polynomial is continuous on `φ.GNS`. -/
theorem continuous_leftMul_of_X (hX : ∀ i, Continuous (φ.leftMul (X i)))
    (p : StarPolynomial ℂ ι) : Continuous (φ.leftMul p) :=
  φ.continuous_leftMul_of_adjoin_eq_top StarPolynomial.adjoin_range_X
    (by rintro _ ⟨i, rfl⟩; exact hX i) p

/-- Continuity of GNS left multiplication on all `⋆`-polynomials is equivalent to continuity on the
generators `X i`. -/
theorem continuous_leftMul_forall_iff_X :
    (∀ p : StarPolynomial ℂ ι, Continuous (φ.leftMul p)) ↔
      ∀ i : ι, Continuous (φ.leftMul (X i)) :=
  ⟨fun h i => h (X i), φ.continuous_leftMul_of_X⟩

theorem boundedSubalgebra_eq_top_iff_X :
    φ.boundedSubalgebra = ⊤ ↔ ∀ i : ι, Continuous (φ.leftMul (X i)) := by
  rw [StarSubalgebra.eq_top_iff]
  simp_rw [φ.mem_boundedSubalgebra]
  exact φ.continuous_leftMul_forall_iff_X

/-- The unital `⋆`-representation of `StarPolynomial ℂ ι` by bounded operators on the completed GNS
Hilbert space `φ.HilbertGNS`, constructed from continuity of generator left multiplications. -/
def starPolynomialRepresentation (hX : ∀ i, Continuous (φ.leftMul (X i))) :
    StarPolynomial ℂ ι →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) :=
  φ.boundedRepresentation (φ.continuous_leftMul_of_X hX)

theorem starPolynomialRepresentation_apply (hX : ∀ i, Continuous (φ.leftMul (X i)))
    (p : StarPolynomial ℂ ι) :
    φ.starPolynomialRepresentation hX p = φ.hilbertLeftMul (φ.continuous_leftMul_of_X hX p) := by
  rw [starPolynomialRepresentation, φ.boundedRepresentation_apply]

theorem starPolynomialRepresentation_X (hX : ∀ i, Continuous (φ.leftMul (X i))) (i : ι) :
    φ.starPolynomialRepresentation hX (X i) = φ.hilbertLeftMul (hX i) := by
  rw [φ.starPolynomialRepresentation_apply]

theorem starPolynomialRepresentation_star_X (hX : ∀ i, Continuous (φ.leftMul (X i))) (i : ι) :
    φ.starPolynomialRepresentation hX (star (X i)) =
      ContinuousLinearMap.adjoint (φ.hilbertLeftMul (hX i)) := by
  rw [StarHomClass.map_star, φ.starPolynomialRepresentation_X,
    ContinuousLinearMap.star_eq_adjoint]

@[simp]
theorem starPolynomialRepresentation_hilbertClassMap (hX : ∀ i, Continuous (φ.leftMul (X i)))
    (p q : StarPolynomial ℂ ι) :
    φ.starPolynomialRepresentation hX p (φ.hilbertClassMap q) = φ.hilbertClassMap (p * q) :=
  φ.boundedRepresentation_hilbertClassMap (φ.continuous_leftMul_of_X hX) p q

@[simp]
theorem starPolynomialRepresentation_hilbertCyclicVector (hX : ∀ i, Continuous (φ.leftMul (X i)))
    (p : StarPolynomial ℂ ι) :
    φ.starPolynomialRepresentation hX p φ.hilbertCyclicVector = φ.hilbertClassMap p :=
  φ.boundedRepresentation_hilbertCyclicVector (φ.continuous_leftMul_of_X hX) p

/-- The cyclic vector `φ.hilbertCyclicVector` has dense orbit under
`φ.starPolynomialRepresentation hX`. -/
theorem denseRange_starPolynomialRepresentation_hilbertCyclicVector
    (hX : ∀ i, Continuous (φ.leftMul (X i))) :
    DenseRange (fun p => φ.starPolynomialRepresentation hX p φ.hilbertCyclicVector) :=
  φ.denseRange_boundedRepresentation_hilbertCyclicVector (φ.continuous_leftMul_of_X hX)

@[simp]
theorem lift_starPolynomialRepresentation_X (hX : ∀ i, Continuous (φ.leftMul (X i))) :
    StarPolynomial.lift (fun i => φ.starPolynomialRepresentation hX (X i)) =
      φ.starPolynomialRepresentation hX :=
  StarPolynomial.hom_ext fun i => by simp

/-- Evaluating the bounded GNS `⋆`-representation at the positive vector functional
`φ.hilbertPositiveLinearMap` recovers `φ` as the `⋆`-distribution of the bounded operator family
`i ↦ φ.starPolynomialRepresentation hX (X i)`. -/
@[simp]
theorem starDistribution_hilbertPositiveLinearMap (hX : ∀ i, Continuous (φ.leftMul (X i))) :
    starDistribution φ.hilbertPositiveLinearMap.toLinearMap
        (fun i => φ.starPolynomialRepresentation hX (X i)) =
      φ.toLinearMap := by
  ext p
  rw [starDistribution_apply, φ.lift_starPolynomialRepresentation_X]
  exact φ.hilbertPositiveLinearMap_boundedRepresentation (φ.continuous_leftMul_of_X hX) p

/-- The adjoint-generator inequality `φ (star p * X i * star (X i) * p) ≤ R² φ (star p * p)` for all
`⋆`-polynomials `p` is equivalent to the generator inequality
`φ (star p * star (X i) * X i * p) ≤ R² φ (star p * p)` for all `p`. -/
theorem forall_apply_X_mul_star_X_le_iff (i : ι) (R : ℝ) :
    (∀ p : StarPolynomial ℂ ι, φ (star p * X i * star (X i) * p) ≤ (R : ℂ) ^ 2 * φ (star p * p)) ↔
      ∀ p : StarPolynomial ℂ ι,
        φ (star p * star (X i) * X i * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) :=
  φ.forall_apply_star_mul_self_star_le_iff (X i) R

/-- Generator quadratic-form inequalities `φ (star p * star (X i) * X i * p) ≤ R_i² φ (star p * p)`
with `0 ≤ R i` give continuity of GNS left multiplication by each generator `X i`. -/
theorem continuous_leftMul_X_of_bound {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i (p : StarPolynomial ℂ ι),
      φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p))
    (i : ι) : Continuous (φ.leftMul (X i)) :=
  (φ.continuous_leftMul_iff (X i)).mpr ⟨R i, hR i, hbound i⟩

/-- For `0 ≤ R`, the operator norm of `φ.starPolynomialRepresentation hX (X i)` is at most `R` if
and only if `φ (star p * star (X i) * X i * p) ≤ (R : ℂ) ^ 2 * φ (star p * p)` for all `p`. -/
theorem norm_starPolynomialRepresentation_X_le_iff (hX : ∀ i, Continuous (φ.leftMul (X i)))
    {i : ι} {R : ℝ} (hR : 0 ≤ R) :
    ‖φ.starPolynomialRepresentation hX (X i)‖ ≤ R ↔
      ∀ p : StarPolynomial ℂ ι,
        φ (star p * star (X i) * X i * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) := by
  rw [φ.starPolynomialRepresentation_X]
  exact φ.norm_hilbertLeftMul_le_iff (hX i) hR

/-- Under the generator inequalities with constants `R i ≥ 0`, each represented generator has
operator norm at most `R i`. -/
theorem norm_starPolynomialRepresentation_X_le {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i (p : StarPolynomial ℂ ι),
      φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p))
    (i : ι) :
    ‖φ.starPolynomialRepresentation (φ.continuous_leftMul_X_of_bound hR hbound) (X i)‖ ≤ R i :=
  (φ.norm_starPolynomialRepresentation_X_le_iff (φ.continuous_leftMul_X_of_bound hR hbound)
    (hR i)).mpr (hbound i)

/-- Under the generator inequalities with constants `R i ≥ 0`, each represented adjoint generator
`star (X i)` also has operator norm at most `R i`. -/
theorem norm_starPolynomialRepresentation_star_X_le {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i (p : StarPolynomial ℂ ι),
      φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p))
    (i : ι) :
    ‖φ.starPolynomialRepresentation (φ.continuous_leftMul_X_of_bound hR hbound) (star (X i))‖ ≤
      R i := by
  rw [StarHomClass.map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint.norm_map]
  exact φ.norm_starPolynomialRepresentation_X_le hR hbound i

/-- Any realization of `φ` as the `⋆`-distribution of a family `c` in a C⋆-algebra `C` under a
positive linear map `ω` forces `φ (star p * star (X i) * X i * p) ≤ R² φ (star p * p)` whenever
`‖c i‖ ≤ R`. -/
theorem apply_star_X_mul_le_of_cstar_starDistribution {C : Type*} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (ω : C →ₚ[ℂ] ℂ) (c : ι → C)
    (hφ : starDistribution ω.toLinearMap c = φ.toLinearMap) {i : ι} {R : ℝ} (hc : ‖c i‖ ≤ R)
    (p : StarPolynomial ℂ ι) :
    φ (star p * star (X i) * X i * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) :=
  φ.apply_star_mul_self_le_of_cstar ω (StarPolynomial.lift c)
    (fun q => by simpa using LinearMap.congr_fun hφ q) (by simpa using hc) p

/-- Any realization of `φ` as the `⋆`-distribution of a family `c` in a C⋆-algebra `C` under a
positive linear map `ω` forces the adjoint-generator inequality
`φ (star p * X i * star (X i) * p) ≤ R² φ (star p * p)` whenever `‖c i‖ ≤ R`. -/
theorem apply_X_mul_star_X_le_of_cstar_starDistribution {C : Type*} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (ω : C →ₚ[ℂ] ℂ) (c : ι → C)
    (hφ : starDistribution ω.toLinearMap c = φ.toLinearMap) {i : ι} {R : ℝ} (hc : ‖c i‖ ≤ R)
    (p : StarPolynomial ℂ ι) :
    φ (star p * X i * star (X i) * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) := by
  simpa only [star_star] using
    φ.apply_star_mul_self_le_of_cstar ω (StarPolynomial.lift c)
      (fun q => by simpa using LinearMap.congr_fun hφ q)
      (a := star (X i)) (by simpa [norm_star] using hc) p

/-- Characterization of bounded GNS realizations with prescribed generator norm bounds `R i ≥ 0`:
generator inequalities, generator and adjoint-generator inequalities, boundedness of GNS left
multiplication, bounded GNS Hilbert representations, Hilbert-space vector-functional realizations,
and C⋆-algebra realizations are all equivalent. -/
theorem boundedGNS_TFAE {ι : Type u} (φ : StarPositiveFunctional (StarPolynomial ℂ ι))
    {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i) :
    [ ∀ i (p : StarPolynomial ℂ ι),
        φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p),
      (∀ i (p : StarPolynomial ℂ ι),
          φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p)) ∧
        ∀ i (p : StarPolynomial ℂ ι),
          φ (star p * X i * star (X i) * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p),
      ∀ i (x : φ.GNS), ‖φ.leftMul (X i) x‖ ≤ R i * ‖x‖,
      ∃ hX : ∀ i, Continuous (φ.leftMul (X i)),
        ∀ i, ‖φ.starPolynomialRepresentation hX (X i)‖ ≤ R i,
      ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (ξ : H) (T : ι → H →L[ℂ] H),
        (∀ i, ‖T i‖ ≤ R i) ∧
          starDistribution (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap T =
            φ.toLinearMap,
      ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)
        (ω : C →ₚ[ℂ] ℂ) (c : ι → C),
        (∀ i, ‖c i‖ ≤ R i) ∧ starDistribution ω.toLinearMap c = φ.toLinearMap ].TFAE := by
  tfae_have 1 → 2 := fun h => ⟨h, fun i => (φ.forall_apply_X_mul_star_X_le_iff i (R i)).mpr (h i)⟩
  tfae_have 2 → 3 := fun h i => (φ.forall_norm_leftMul_le_iff (hR i)).mpr (h.1 i)
  tfae_have 3 → 4 := fun h => by
    have hbound : ∀ i p, φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p) :=
      fun i => (φ.forall_norm_leftMul_le_iff (hR i)).mp (h i)
    exact ⟨φ.continuous_leftMul_X_of_bound hR hbound,
      φ.norm_starPolynomialRepresentation_X_le hR hbound⟩
  tfae_have 4 → 5 := by
    rintro ⟨hX, hnorm⟩
    refine ⟨φ.HilbertGNS, inferInstance, inferInstance, inferInstance, φ.hilbertCyclicVector,
      fun i => φ.starPolynomialRepresentation hX (X i), hnorm, ?_⟩
    rw [← φ.hilbertPositiveLinearMap_def]
    exact φ.starDistribution_hilbertPositiveLinearMap hX
  tfae_have 5 → 6 := by
    rintro ⟨H, _, _, _, ξ, T, hnorm, hdist⟩
    exact ⟨H →L[ℂ] H, inferInstance, inferInstance, inferInstance,
      ContinuousLinearMap.innerPositiveLinearMap ℂ ξ, T, hnorm, hdist⟩
  tfae_have 6 → 1 := by
    rintro ⟨C, _, _, _, ω, c, hnorm, hdist⟩ i p
    exact φ.apply_star_X_mul_le_of_cstar_starDistribution ω c hdist (hnorm i) p
  tfae_finish

/-- A positive functional `φ` on `StarPolynomial ℂ ι` is the `⋆`-distribution of some family in a
unital C⋆-algebra under a positive linear functional if and only if each generator `X i` satisfies a
quadratic-form inequality `φ (star p * star (X i) * X i * p) ≤ R_i² φ (star p * p)`. -/
theorem exists_cstar_starDistribution_eq_iff {ι : Type u}
    (φ : StarPositiveFunctional (StarPolynomial ℂ ι)) :
    (∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)
        (ω : C →ₚ[ℂ] ℂ) (c : ι → C),
        starDistribution ω.toLinearMap c = φ.toLinearMap) ↔
      ∃ R : ι → ℝ, (∀ i, 0 ≤ R i) ∧ ∀ i (p : StarPolynomial ℂ ι),
        φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p) := by
  constructor
  · rintro ⟨C, _, _, _, ω, c, hdist⟩
    exact ⟨fun i => ‖c i‖, fun i => norm_nonneg (c i), fun i p =>
      φ.apply_star_X_mul_le_of_cstar_starDistribution ω c hdist le_rfl p⟩
  · rintro ⟨R, hR, hbound⟩
    let hX := φ.continuous_leftMul_X_of_bound hR hbound
    exact ⟨φ.HilbertGNS →L[ℂ] φ.HilbertGNS, inferInstance, inferInstance, inferInstance,
      φ.hilbertPositiveLinearMap, fun i => φ.starPolynomialRepresentation hX (X i),
      φ.starDistribution_hilbertPositiveLinearMap hX⟩

/-- Normalized state version of `exists_cstar_starDistribution_eq_iff`: when `φ 1 = 1`, `φ` is the
`⋆`-distribution of a family in a unital C⋆-algebra with respect to a normalized positive state
(`ω 1 = 1`) if and only if the generator inequalities hold. -/
theorem exists_cstar_state_starDistribution_eq_iff {ι : Type u}
    (φ : StarPositiveFunctional (StarPolynomial ℂ ι)) (hφ₁ : φ 1 = 1) :
    (∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)
        (ω : C →ₚ[ℂ] ℂ) (c : ι → C),
        ω 1 = 1 ∧ starDistribution ω.toLinearMap c = φ.toLinearMap) ↔
      ∃ R : ι → ℝ, (∀ i, 0 ≤ R i) ∧ ∀ i (p : StarPolynomial ℂ ι),
        φ (star p * star (X i) * X i * p) ≤ (R i : ℂ) ^ 2 * φ (star p * p) := by
  constructor
  · rintro ⟨C, hC₁, hC₂, hC₃, ω, c, -, hdist⟩
    exact φ.exists_cstar_starDistribution_eq_iff.mp ⟨C, hC₁, hC₂, hC₃, ω, c, hdist⟩
  · rintro ⟨R, hR, hbound⟩
    let hX := φ.continuous_leftMul_X_of_bound hR hbound
    exact ⟨φ.HilbertGNS →L[ℂ] φ.HilbertGNS, inferInstance, inferInstance, inferInstance,
      φ.hilbertPositiveLinearMap, fun i => φ.starPolynomialRepresentation hX (X i),
      by simp [hφ₁], φ.starDistribution_hilbertPositiveLinearMap hX⟩

end BoundedRealization

end StarPositiveFunctional

section Counterexample

/-! ### Positivity alone does not imply boundedness

For any index type `ι`, evaluating every generator `X i` at `n + 1` and averaging against the
normalized geometric weights `2^{-(n + 1)}` yields a positive normalized functional `φ` on
`StarPolynomial ℂ ι` for which left multiplication by every generator `X i` on `φ.GNS` is
unbounded. -/

private def counterexampleEval {ι : Type*} (n : ℕ) : StarPolynomial ℂ ι →⋆ₐ[ℂ] ℂ :=
  StarPolynomial.lift fun _ => ((n + 1 : ℕ) : ℂ)

@[simp]
private theorem counterexampleEval_X {ι : Type*} (n : ℕ) (i : ι) :
    counterexampleEval n (X (R := ℂ) i) = ((n + 1 : ℕ) : ℂ) := by
  rw [counterexampleEval, lift_X]

@[simp]
private theorem counterexampleEval_star_X {ι : Type*} (n : ℕ) (i : ι) :
    counterexampleEval n (star (X (R := ℂ) i)) = ((n + 1 : ℕ) : ℂ) := by
  rw [counterexampleEval, lift_star_X, Complex.star_def, RCLike.conj_natCast]

@[simp]
private theorem counterexampleEval_algebraMap {ι : Type*} (n : ℕ) (r : ℂ) :
    counterexampleEval n (algebraMap ℂ (StarPolynomial ℂ ι) r) = r :=
  (counterexampleEval n).commutes r

private theorem exists_norm_counterexampleEval_le {ι : Type*} (p : StarPolynomial ℂ ι) :
    ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧
      ∀ n : ℕ, ‖counterexampleEval n p‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ d := by
  induction p using StarPolynomial.induction with
  | algebraMap r =>
    refine ⟨‖r‖, 0, norm_nonneg r, fun n => ?_⟩
    simp
  | X i =>
    refine ⟨1, 1, zero_le_one, fun n => ?_⟩
    simpa only [counterexampleEval_X, pow_one, one_mul] using (Complex.norm_natCast (n + 1)).le
  | star_X i =>
    refine ⟨1, 1, zero_le_one, fun n => ?_⟩
    simpa only [counterexampleEval_star_X, pow_one, one_mul] using (Complex.norm_natCast (n + 1)).le
  | mul p q hp hq =>
    obtain ⟨Cp, dp, hCp, hp⟩ := hp
    obtain ⟨Cq, dq, hCq, hq⟩ := hq
    refine ⟨Cp * Cq, dp + dq, mul_nonneg hCp hCq, fun n => ?_⟩
    calc ‖counterexampleEval n (p * q)‖
        = ‖counterexampleEval n p‖ * ‖counterexampleEval n q‖ := by simp
      _ ≤ (Cp * ((n + 1 : ℕ) : ℝ) ^ dp) * (Cq * ((n + 1 : ℕ) : ℝ) ^ dq) :=
          mul_le_mul (hp n) (hq n) (norm_nonneg _) (by positivity)
      _ = Cp * Cq * ((n + 1 : ℕ) : ℝ) ^ (dp + dq) := by rw [pow_add]; ring
  | add p q hp hq =>
    obtain ⟨Cp, dp, hCp, hp⟩ := hp
    obtain ⟨Cq, dq, hCq, hq⟩ := hq
    refine ⟨Cp + Cq, max dp dq, add_nonneg hCp hCq, fun n => ?_⟩
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    calc ‖counterexampleEval n (p + q)‖
        ≤ ‖counterexampleEval n p‖ + ‖counterexampleEval n q‖ := by
          rw [map_add]
          exact norm_add_le _ _
      _ ≤ Cp * ((n + 1 : ℕ) : ℝ) ^ dp + Cq * ((n + 1 : ℕ) : ℝ) ^ dq := add_le_add (hp n) (hq n)
      _ ≤ Cp * ((n + 1 : ℕ) : ℝ) ^ max dp dq + Cq * ((n + 1 : ℕ) : ℝ) ^ max dp dq :=
          add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn (le_max_left dp dq)) hCp)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn (le_max_right dp dq)) hCq)
      _ = (Cp + Cq) * ((n + 1 : ℕ) : ℝ) ^ max dp dq := by ring

private theorem summable_counterexampleTerm_real {ι : Type*} (p : StarPolynomial ℂ ι) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖) := by
  obtain ⟨C, d, _, hbound⟩ := exists_norm_counterexampleEval_le p
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    norm_num
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_nat_add_iff 1 (f := fun k : ℕ => (k : ℝ) ^ d * (1 / 2 : ℝ) ^ k)).mpr
      (summable_pow_mul_geometric_of_norm_lt_one d hr)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) (hsum.mul_left C)
  calc (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖
      ≤ (1 / 2 : ℝ) ^ (n + 1) * (C * ((n + 1 : ℕ) : ℝ) ^ d) := by gcongr; exact hbound n
    _ = C * (((n + 1 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (n + 1)) := by ring

private theorem summable_counterexampleTerm {ι : Type*} (p : StarPolynomial ℂ ι) :
    Summable (fun n : ℕ => (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * counterexampleEval n p) := by
  refine Summable.of_norm_bounded (summable_counterexampleTerm_real p) fun n => ?_
  have hw : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  rw [norm_mul, Complex.norm_of_nonneg hw]

private theorem summable_counterexampleNormSq {ι : Type*} (p : StarPolynomial ℂ ι) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖ ^ 2) := by
  simpa only [map_mul, StarHomClass.map_star, norm_mul, norm_star, ← sq] using
    summable_counterexampleTerm_real (star p * p)

private theorem counterexampleTerm_star_mul_self {ι : Type*} (p : StarPolynomial ℂ ι) (n : ℕ) :
    (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * counterexampleEval n (star p * p) =
      (((1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, StarHomClass.map_star, Complex.star_def, RCLike.conj_mul]
  push_cast
  rfl

private def unboundedPositiveFunctional (ι : Type*) :
    StarPositiveFunctional (StarPolynomial ℂ ι) where
  toLinearMap :=
    { toFun p := ∑' n : ℕ, (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * counterexampleEval n p
      map_add' p q := by
        simp only [map_add, mul_add]
        exact (summable_counterexampleTerm p).tsum_add (summable_counterexampleTerm q)
      map_smul' c p := by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm _ c]
        exact tsum_mul_left }
  square_nonneg p := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, counterexampleTerm_star_mul_self,
      ← Complex.ofReal_tsum]
    exact Complex.zero_le_real.mpr (tsum_nonneg fun _ => by positivity)

private theorem unboundedPositiveFunctional_apply {ι : Type*} (p : StarPolynomial ℂ ι) :
    unboundedPositiveFunctional ι p =
      ∑' n : ℕ, (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * counterexampleEval n p :=
  (rfl)

private theorem unboundedPositiveFunctional_star_mul_self {ι : Type*} (p : StarPolynomial ℂ ι) :
    unboundedPositiveFunctional ι (star p * p) =
      ((∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖ ^ 2 : ℝ) : ℂ) := by
  rw [unboundedPositiveFunctional_apply]
  simp only [counterexampleTerm_star_mul_self, ← Complex.ofReal_tsum]

private theorem unboundedPositiveFunctional_one (ι : Type*) :
    unboundedPositiveFunctional ι 1 = 1 := by
  have h1 : (1 : StarPolynomial ℂ ι) = star 1 * 1 := by simp
  rw [h1, unboundedPositiveFunctional_star_mul_self]
  simp only [map_one, norm_one, one_pow, mul_one, pow_succ']
  rw [tsum_mul_left, tsum_geometric_two]
  norm_num

private def lagrangePoly {ι : Type*} (i : ι) : ℕ → StarPolynomial ℂ ι
  | 0 => 1
  | k + 1 => lagrangePoly i k * (X i - algebraMap ℂ (StarPolynomial ℂ ι) ((k + 1 : ℕ) : ℂ))

private theorem counterexampleEval_lagrangePoly {ι : Type*} (i : ι) (n m : ℕ) :
    counterexampleEval n (lagrangePoly i m) =
      ∏ j ∈ Finset.range m, (((n + 1 : ℕ) : ℂ) - ((j + 1 : ℕ) : ℂ)) := by
  induction m with
  | zero => simp [lagrangePoly]
  | succ k ih =>
    rw [lagrangePoly, map_mul, ih, map_sub, counterexampleEval_X, counterexampleEval_algebraMap,
      Finset.prod_range_succ]

private theorem counterexampleEval_lagrangePoly_eq_zero {ι : Type*} (i : ι) {n m : ℕ}
    (hn : n < m) : counterexampleEval n (lagrangePoly i m) = 0 := by
  rw [counterexampleEval_lagrangePoly]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (sub_self _)

private theorem counterexampleEval_lagrangePoly_ne_zero {ι : Type*} (i : ι) (m : ℕ) :
    counterexampleEval m (lagrangePoly i m) ≠ 0 := by
  rw [counterexampleEval_lagrangePoly, Finset.prod_ne_zero_iff]
  intro j hj
  rw [sub_ne_zero]
  have hjm : j < m := Finset.mem_range.mp hj
  exact_mod_cast (by omega : m + 1 ≠ j + 1)

private theorem not_continuous_leftMul_unboundedPositiveFunctional {ι : Type*} (i : ι) :
    ¬ Continuous ((unboundedPositiveFunctional ι).leftMul (X i)) := by
  intro hc
  obtain ⟨R, hR, hbound⟩ := ((unboundedPositiveFunctional ι).continuous_leftMul_iff (X i)).mp hc
  set m : ℕ := Nat.ceil R
  let p : StarPolynomial ℂ ι := lagrangePoly i m
  set S : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖ ^ 2
  set T : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n (X i * p)‖ ^ 2
  have hS_pos : 0 < S := by
    have hm_pos : 0 < (1 / 2 : ℝ) ^ (m + 1) * ‖counterexampleEval m p‖ ^ 2 :=
      mul_pos (by positivity)
        (sq_pos_of_pos (norm_pos_iff.mpr (counterexampleEval_lagrangePoly_ne_zero i m)))
    exact hm_pos.trans_le ((summable_counterexampleNormSq p).le_tsum m fun _ _ => by positivity)
  have hST_ge : ((m + 1 : ℕ) : ℝ) ^ 2 * S ≤ T := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_)
      ((summable_counterexampleNormSq p).mul_left _) (summable_counterexampleNormSq (X i * p))
    rcases lt_or_ge n m with hnm | hmn
    · simp [p, counterexampleEval_lagrangePoly_eq_zero i hnm]
    · have hmn' : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hmn
      have hsq : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmn' 2
      have hnorm : ‖counterexampleEval n (X i * p)‖ ^ 2 =
          ((n + 1 : ℕ) : ℝ) ^ 2 * ‖counterexampleEval n p‖ ^ 2 := by
        rw [map_mul, norm_mul, counterexampleEval_X, Complex.norm_natCast, mul_pow]
      rw [hnorm]
      calc ((m + 1 : ℕ) : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ (n + 1) * ‖counterexampleEval n p‖ ^ 2)
          = (1 / 2 : ℝ) ^ (n + 1) * (((m + 1 : ℕ) : ℝ) ^ 2 * ‖counterexampleEval n p‖ ^ 2) := by
            ring
        _ ≤ (1 / 2 : ℝ) ^ (n + 1) * (((n + 1 : ℕ) : ℝ) ^ 2 * ‖counterexampleEval n p‖ ^ 2) := by
            gcongr
  have hTp : star p * star (X i) * X i * p = star (X i * p) * (X i * p) := by
    simp [mul_assoc]
  have hTS_le : T ≤ R ^ 2 * S := by
    have hp_ineq := hbound p
    rw [hTp, unboundedPositiveFunctional_star_mul_self (X i * p),
      unboundedPositiveFunctional_star_mul_self p, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      at hp_ineq
    exact Complex.real_le_real.mp hp_ineq
  have hRm : R < ((m + 1 : ℕ) : ℝ) := by
    calc R ≤ (m : ℝ) := Nat.le_ceil R
      _ < (m : ℝ) + 1 := lt_add_one (m : ℝ)
      _ = ((m + 1 : ℕ) : ℝ) := by norm_cast
  have hR_sq : R ^ 2 < ((m + 1 : ℕ) : ℝ) ^ 2 := (sq_lt_sq₀ hR (by positivity)).mpr hRm
  nlinarith

/-- Positivity and normalization alone do not imply boundedness of GNS left multiplication: for
every index type `ι`, there is a positive functional `φ` on `StarPolynomial ℂ ι` with `φ 1 = 1`
such that `φ.leftMul (X i)` is discontinuous on `φ.GNS` for every `i : ι`. -/
theorem exists_starPositiveFunctional_apply_one_not_continuous_leftMul_X (ι : Type*) :
    ∃ φ : StarPositiveFunctional (StarPolynomial ℂ ι),
      φ 1 = 1 ∧ ∀ i : ι, ¬ Continuous (φ.leftMul (X i)) :=
  ⟨unboundedPositiveFunctional ι, unboundedPositiveFunctional_one ι,
    not_continuous_leftMul_unboundedPositiveFunctional⟩

/-- Over any nonempty index type `ι`, there exists a normalized positive functional on
`StarPolynomial ℂ ι` that cannot be realized as the `⋆`-distribution of any family in any unital
C⋆-algebra (in any universe) with respect to a positive linear functional. -/
theorem exists_starPositiveFunctional_apply_one_not_exists_cstar_starDistribution
    (ι : Type*) [Nonempty ι] :
    ∃ φ : StarPositiveFunctional (StarPolynomial ℂ ι), φ 1 = 1 ∧
      ∀ (C : Type v) [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
        (ω : C →ₚ[ℂ] ℂ) (c : ι → C), starDistribution ω.toLinearMap c ≠ φ.toLinearMap := by
  obtain ⟨φ, hφ₁, hunb⟩ := exists_starPositiveFunctional_apply_one_not_continuous_leftMul_X ι
  refine ⟨φ, hφ₁, fun C _ _ _ ω c hdist => ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact hunb i₀ <| φ.continuous_leftMul_X_of_bound (fun i => norm_nonneg (c i))
    (fun i p => φ.apply_star_X_mul_le_of_cstar_starDistribution ω c hdist le_rfl p) i₀

end Counterexample

end TauCeti
