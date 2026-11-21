/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Projection
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.MarkovTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Collapse
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Zero
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# GNS representations and positive Markov traces of the balanced projection algebra

When `τ : ℂ` is real (`Fact (IsSelfAdjoint τ)`), `BalancedProjectionAlgebra ℂ τ` is generated as a
`ℂ`-algebra by the star projections `e τ i`. Every `StarPositiveFunctional` `φ` therefore satisfies
`0 ≤ φ (star x * e τ i * x) ≤ φ (star x * x)`, has `φ.boundedSubalgebra = ⊤`, and induces a
canonical unital `⋆`-representation `gnsRepresentation φ` on `φ.HilbertGNS`, so algebraic positivity
is equivalent to factoring through a unital C⋆-representation.

Combining `gnsRepresentation` with the proper-star and C⋆-algebra theorems yields functional-level
consequences without assuming an ambient C⋆-representation:
* at `τ = 0`, every algebraically positive functional is automatically tracial;
* for `τ ∉ [0, 1)`, every positive functional is a nonnegative combination of the scalar characters
  `e i ↦ 1, 0`, and the positive Markov traces are precisely `(0, character 0 .zero)` and
  `(1, character 1 .one)`.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.gnsRepresentation`, `exists_cstar_representation_iff`:
  bounded Hilbert-space GNS representation and C⋆-characterization of positivity.
* `TauCeti.BalancedProjectionAlgebra.characterPositiveFunctional`: scalar characters as positive
  functionals.
* `TauCeti.BalancedProjectionAlgebra.apply_mul_comm_of_zero`: positive functionals at `τ = 0` are
  tracial.
* `TauCeti.BalancedProjectionAlgebra.apply_eq_character_mul_add_character_mul`,
  `isMarkovTrace_and_forall_star_mul_self_nonneg_iff`: character decomposition and positive Markov
  trace classification for `τ ∉ [0, 1)`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§4, 11.
* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
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
  φ.mem_boundedSubalgebra.mp <| (boundedSubalgebra_eq_top φ).symm ▸ trivial

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

/-! ### The commutative endpoint `τ = 0` -/

section ZeroEndpoint

/-- At `τ = 0`, the bounded GNS representation of any positive functional has commutative image. -/
theorem commute_gnsRepresentation_of_zero
    (φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ 0))
    (x y : BalancedProjectionAlgebra ℂ 0) :
    Commute (gnsRepresentation φ x) (gnsRepresentation φ y) := by
  have : IsProperStar (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) := by
    let _ : CStarAlgebra (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) := inferInstance
    exact inferInstance
  exact commute_map_of_zero (gnsRepresentation φ) (isStarProjection_gnsRepresentation_e φ) x y

/-- At `τ = 0`, every algebraically positive linear functional is automatically tracial. -/
theorem apply_mul_comm_of_zero (φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ 0))
    (x y : BalancedProjectionAlgebra ℂ 0) : φ (x * y) = φ (y * x) := by
  rw [← hilbertPositiveLinearMap_gnsRepresentation φ, map_mul,
    (commute_gnsRepresentation_of_zero φ x y).eq, ← map_mul,
    hilbertPositiveLinearMap_gnsRepresentation]

end ZeroEndpoint

/-! ### Collapse of positive functionals and Markov traces outside `[0, 1)` -/

section CollapseRegime

variable {τ : ℂ} [Fact (IsSelfAdjoint τ)]

/-- For `τ ∉ [0, 1)`, the GNS representation of any positive functional sends every generator
`e τ i` to `gnsRepresentation φ (e τ 0)`. -/
theorem gnsRepresentation_e_eq_gnsRepresentation_e_zero
    (φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ τ))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (i : ℕ) :
    gnsRepresentation φ (e τ i) = gnsRepresentation φ (e τ 0) :=
  map_e_eq_map_e_zero (gnsRepresentation φ) (isStarProjection_gnsRepresentation_e φ) hτ i

/-- For `τ ∉ [0, 1)`, every positive functional `φ` decomposes along `character 1 .one` and
`character 0 .zero` with weights `φ (e τ 0)` and `φ 1 - φ (e τ 0)`. -/
theorem apply_eq_character_mul_add_character_mul
    (φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ τ))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (x : BalancedProjectionAlgebra ℂ τ) :
    φ x = character 1 .one x * φ (e τ 0) + character 0 .zero x * (φ 1 - φ (e τ 0)) := by
  simpa only [hilbertPositiveLinearMap_gnsRepresentation, map_add, map_smul, map_sub, map_one,
    φ.hilbertPositiveLinearMap_one, smul_eq_mul] using
    congrArg φ.hilbertPositiveLinearMap
      (map_eq_character_smul_add_character_smul (gnsRepresentation φ)
        (isStarProjection_gnsRepresentation_e φ) hτ x)

/-- **Classification of positive Markov traces outside `[0, 1)`.** For self-adjoint `τ ∉ [0, 1)`,
a linear functional `μ` is an algebraically positive Markov trace with parameter `η` iff either
`η = 0` and `μ = character 0 .zero`, or `η = 1` and `μ = character 1 .one`. -/
theorem isMarkovTrace_and_forall_star_mul_self_nonneg_iff
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) {η : ℂ}
    {μ : BalancedProjectionAlgebra ℂ τ →ₗ[ℂ] ℂ} :
    (IsMarkovTrace η μ ∧ ∀ x, 0 ≤ μ (star x * x)) ↔
      (η = 0 ∧ μ = (character 0 .zero).toLinearMap) ∨
        (η = 1 ∧ μ = (character 1 .one).toLinearMap) := by
  constructor
  · rintro ⟨hμ, hpos⟩
    let φ : StarPositiveFunctional (BalancedProjectionAlgebra ℂ τ) := ⟨μ, hpos⟩
    have h1 : φ.hilbertPositiveLinearMap 1 = 1 := by simpa [φ] using hμ.map_one
    have hmarkov : ∀ n w, w ∈ stage ℂ τ (n + 1) →
        φ.hilbertPositiveLinearMap (gnsRepresentation φ (w * e τ n)) =
          η * φ.hilbertPositiveLinearMap (gnsRepresentation φ w) := fun n w hw ↦ by
      simpa [hilbertPositiveLinearMap_gnsRepresentation, φ] using hμ.map_mul_e hw
    have hη := isIdempotentElem_of_markov (gnsRepresentation φ)
      (isStarProjection_gnsRepresentation_e φ) hτ h1 hmarkov
    have hchar : μ = (character η hη).toLinearMap := LinearMap.ext fun x ↦ by
      simpa [hilbertPositiveLinearMap_gnsRepresentation, φ] using
        apply_map_eq_character_of_markov (gnsRepresentation φ)
          (isStarProjection_gnsRepresentation_e φ) hτ h1 hmarkov x
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hη with rfl | rfl
    · exact Or.inl ⟨rfl, hchar⟩
    · exact Or.inr ⟨rfl, hchar⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨isMarkovTrace_character 0 .zero, character_star_mul_self_nonneg 0 (.zero ℂ)⟩
    · exact ⟨isMarkovTrace_character 1 .one, character_star_mul_self_nonneg 1 (.one ℂ)⟩

end CollapseRegime

end TauCeti.BalancedProjectionAlgebra
