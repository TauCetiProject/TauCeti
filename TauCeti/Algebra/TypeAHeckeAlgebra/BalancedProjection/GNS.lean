/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Projection
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Star

/-!
# GNS representations of the balanced projection algebra

When `τ : ℂ` is real (`Fact (IsSelfAdjoint τ)`), `BalancedProjectionAlgebra ℂ τ` is generated as a
`ℂ`-algebra by the star projections `e τ i`. Every `StarPositiveFunctional` `φ` therefore satisfies
`0 ≤ φ (star x * e τ i * x) ≤ φ (star x * x)`, has `φ.boundedSubalgebra = ⊤`, and induces a
canonical unital `⋆`-representation `gnsRepresentation φ` on `φ.HilbertGNS`, so algebraic positivity
is equivalent to factoring through a unital C⋆-representation.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.gnsRepresentation`, `exists_cstar_representation_iff`:
  bounded Hilbert-space GNS representation and C⋆-characterization of positivity.
* `TauCeti.BalancedProjectionAlgebra.characterPositiveFunctional`: scalar characters as positive
  functionals.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§4, 11.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.BalancedProjectionAlgebra

section GNS

variable {τ : ℂ} [Fact (IsSelfAdjoint τ)]

section Functional

variable (φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ τ))

/-- Every generator `e τ i` satisfies `0 ≤ φ (star x * e τ i * x)`. -/
theorem apply_star_mul_e_mul_nonneg (i : ℕ) (x : BalancedProjectionAlgebra ℂ τ) :
    0 ≤ φ (star x * e τ i * x) :=
  φ.apply_star_mul_mul_nonneg_of_isStarProjection (isStarProjection_e i) x

/-- Every generator `e τ i` satisfies `φ (star x * e τ i * x) ≤ φ (star x * x)`. -/
theorem apply_star_mul_e_mul_le (i : ℕ) (x : BalancedProjectionAlgebra ℂ τ) :
    φ (star x * e τ i * x) ≤ φ (star x * x) :=
  φ.apply_star_mul_mul_le_of_isStarProjection (isStarProjection_e i) x

/-- Every element of `BalancedProjectionAlgebra ℂ τ` acts boundedly on `φ.GNS`. -/
theorem boundedSubalgebra_eq_top : φ.boundedSubalgebra = ⊤ :=
  φ.boundedSubalgebra_eq_top_of_adjoin_isStarProjection adjoin_range_e
    (by rintro _ ⟨i, rfl⟩; exact isStarProjection_e i)

/-- Left multiplication on `φ.GNS` is continuous for every element. -/
theorem continuous_leftMul (x : BalancedProjectionAlgebra ℂ τ) : Continuous (φ.leftMul x) :=
  φ.continuous_leftMul_of_boundedSubalgebra_eq_top (boundedSubalgebra_eq_top φ) x

/-- The canonical unital `⋆`-representation of `BalancedProjectionAlgebra ℂ τ` on
`φ.HilbertGNS`. -/
def gnsRepresentation :
    BalancedProjectionAlgebra ℂ τ →⋆ₐ[ℂ] (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) :=
  φ.boundedRepresentation (continuous_leftMul φ)

/-- `gnsRepresentation φ` agrees with `φ.boundedRepresentation (continuous_leftMul φ)`. -/
theorem gnsRepresentation_eq_boundedRepresentation :
    gnsRepresentation φ = φ.boundedRepresentation (continuous_leftMul φ) := (rfl)

@[simp]
theorem gnsRepresentation_hilbertClassMap (x y : BalancedProjectionAlgebra ℂ τ) :
    gnsRepresentation φ x (φ.hilbertClassMap y) = φ.hilbertClassMap (x * y) :=
  φ.boundedRepresentation_hilbertClassMap (continuous_leftMul φ) x y

@[simp]
theorem gnsRepresentation_hilbertCyclicVector (x : BalancedProjectionAlgebra ℂ τ) :
    gnsRepresentation φ x φ.hilbertCyclicVector = φ.hilbertClassMap x :=
  φ.boundedRepresentation_hilbertCyclicVector (continuous_leftMul φ) x

/-- The cyclic vector functional recovers `φ` along `gnsRepresentation φ`. -/
theorem hilbertPositiveLinearMap_gnsRepresentation (x : BalancedProjectionAlgebra ℂ τ) :
    φ.hilbertPositiveLinearMap (gnsRepresentation φ x) = φ x :=
  φ.hilbertPositiveLinearMap_boundedRepresentation (continuous_leftMul φ) x

/-- Every generator `e τ i` acts as a star projection on `φ.HilbertGNS`. -/
theorem isStarProjection_gnsRepresentation_e (i : ℕ) :
    IsStarProjection (gnsRepresentation φ (e τ i)) :=
  (isStarProjection_e i).map (gnsRepresentation φ)

/-- Every generator `e τ i` acts on `φ.HilbertGNS` with operator norm at most `1`. -/
theorem norm_gnsRepresentation_e_le_one (i : ℕ) : ‖gnsRepresentation φ (e τ i)‖ ≤ 1 := by
  rw [gnsRepresentation_eq_boundedRepresentation, φ.boundedRepresentation_apply]
  exact φ.norm_hilbertLeftMul_le_one_of_isStarProjection (isStarProjection_e i)

end Functional

/-- Algebraic positivity of a linear functional on `BalancedProjectionAlgebra ℂ τ` is equivalent to
factoring through a unital `⋆`-representation in a C⋆-algebra. -/
theorem exists_cstar_representation_iff {f : BalancedProjectionAlgebra ℂ τ →ₗ[ℂ] ℂ} :
    (∃ (C : Type) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)
        (ω : C →ₚ[ℂ] ℂ) (π : BalancedProjectionAlgebra ℂ τ →⋆ₐ[ℂ] C), ∀ x, ω (π x) = f x) ↔
      ∀ x : BalancedProjectionAlgebra ℂ τ, 0 ≤ f (star x * x) :=
  StarPositiveFunctional.exists_cstar_representation_iff_forall_nonneg_of_forall_continuous_leftMul
    continuous_leftMul

/-- Normalized state version of `exists_cstar_representation_iff`. -/
theorem exists_cstar_state_representation_iff {f : BalancedProjectionAlgebra ℂ τ →ₗ[ℂ] ℂ} :
    (∃ (C : Type) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C)
        (ω : C →ₚ[ℂ] ℂ) (π : BalancedProjectionAlgebra ℂ τ →⋆ₐ[ℂ] C),
        ω 1 = 1 ∧ ∀ x, ω (π x) = f x) ↔
      f 1 = 1 ∧ ∀ x : BalancedProjectionAlgebra ℂ τ, 0 ≤ f (star x * x) :=
  StarPositiveFunctional.exists_cstar_state_representation_iff_of_forall_continuous_leftMul
    continuous_leftMul

/-- The scalar character at a star projection `c : ℂ` as a `StarPositiveFunctional`. -/
def characterPositiveFunctional (c : ℂ) (hc : IsStarProjection c) :
    StarPositiveFunctional (BalancedProjectionAlgebra ℂ τ) :=
  (StarPositiveFunctional.ofPositiveLinearMap (.id ℂ ℂ)).comp (characterStarAlgHom c hc)

@[simp]
theorem characterPositiveFunctional_apply (c : ℂ) (hc : IsStarProjection c)
    (x : BalancedProjectionAlgebra ℂ τ) :
    characterPositiveFunctional c hc x = character c hc.isIdempotentElem x := by
  simp [characterPositiveFunctional]

@[simp]
theorem toLinearMap_characterPositiveFunctional (c : ℂ) (hc : IsStarProjection c) :
    (characterPositiveFunctional (τ := τ) c hc).toLinearMap =
      (character c hc.isIdempotentElem).toLinearMap :=
  LinearMap.ext fun _ ↦ by simp

/-- Every scalar character at a star projection `c : ℂ` is nonnegative on algebraic squares. -/
theorem character_star_mul_self_nonneg (c : ℂ) (hc : IsStarProjection c)
    (x : BalancedProjectionAlgebra ℂ τ) :
    0 ≤ character c hc.isIdempotentElem (star x * x) := by
  simpa using (characterPositiveFunctional (τ := τ) c hc).square_nonneg x

end GNS

end TauCeti.BalancedProjectionAlgebra
