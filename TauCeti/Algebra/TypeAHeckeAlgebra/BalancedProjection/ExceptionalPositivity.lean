/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Collapse
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.GNS
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.MarkovTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Zero

/-!
# Exceptional-parameter positivity of the balanced projection algebra

Combining `BalancedProjectionAlgebra.gnsRepresentation` with the proper-star and C⋆-algebra collapse
theorems yields functional-level consequences without assuming an ambient C⋆-representation:
* at `τ = 0`, every algebraically positive functional is automatically tracial;
* for `τ ∉ [0, 1)`, every positive functional is a nonnegative combination of the scalar characters
  `e i ↦ 1, 0`, and the positive Markov traces are precisely `(0, character 0 .zero)` and
  `(1, character 1 .one)`.

## Main results

* `TauCeti.BalancedProjectionAlgebra.commute_gnsRepresentation_of_zero`,
  `TauCeti.BalancedProjectionAlgebra.apply_mul_comm_of_zero`: positive functionals at `τ = 0` are
  tracial.
* `TauCeti.BalancedProjectionAlgebra.gnsRepresentation_e_eq_gnsRepresentation_e_zero`,
  `TauCeti.BalancedProjectionAlgebra.apply_eq_character_mul_add_character_mul`,
  `TauCeti.BalancedProjectionAlgebra.isMarkovTrace_and_forall_star_mul_self_nonneg_iff`: character
  decomposition and positive Markov trace classification for `τ ∉ [0, 1)`.

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
