/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.Monogenic
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex

/-!
# The lower index of a quotient of a Galois group

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field, normal over `K`, so that restriction `G → Gal(L/K)` identifies
`Gal(L/K)` with the quotient `G / H` by `H = Gal(M/L)`. Serre's lower index
`i_G(σ) = min_{x ∈ 𝒪[M]} v_M(σ x - x)` (`TauCeti.IsLocalRing.lowerIndex`) encodes the lower
ramification filtration, since `σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`. This file proves how it behaves
under passage to the quotient:

`e(M/L) · i_{G/H}(σ') = ∑_{σ ↦ σ'} i_G(σ)`,

where `e(M/L)` is the ramification index of `M/L`. The identity is stated in `ℕ∞`, where it
holds for every `σ'`: at `σ' = 1` both sides are `⊤`. It is the input from which Herbrand's
theorem, the compatibility of the upper numbering with quotients, is derived.

## Main results

* `TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum`: for
  `σ : Gal(M/K)`, `e(M/L) · i(σ|_L) = ∑_{τ ∈ Gal(M/L)} i(σ τ)`, the sum over the coset `σ H`.
* `TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_eq_sum`: for
  `σ' : Gal(L/K)`, `e(M/L) · i(σ') = ∑_{σ|_L = σ'} i(σ)`, the sum over the fibre of restriction.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3.
-/

public section
noncomputable section

open ValuativeRel
open TauCeti.IsLocalRing (lowerIndex)

namespace TauCeti.LocalFieldsRamification

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [Normal K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]
  [IsScalarTower K L M]

omit [IsGalois K M] in
/-- **Serre's quotient formula for the lower index**, over a coset. For an intermediate field
`L` of `M/K` normal over `K` and `σ : Gal(M/K)`,
`e(M/L) · i_{L/K}(σ|_L) = ∑_{τ ∈ Gal(M/L)} i_{M/K}(σ τ)`. -/
theorem ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum [IsGalois L M]
    (σ : M ≃ₐ[K] M) :
    (ramificationIndex L M : ℕ∞) * lowerIndex 𝒪[L] (σ.restrictNormal L) =
      ∑ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) := by
  obtain ⟨x, hx⟩ := TauCeti.exists_integerRing_adjoin_eq_top K M
  obtain ⟨y, hy⟩ := TauCeti.exists_integerRing_adjoin_eq_top K L
  rw [ramificationIndex_eq_ramificationIdx, ← finsum_eq_sum_of_fintype]
  exact TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_eq_finsum_of_adjoin_eq_top hx hy
    (AlgEquiv.smul_algebraMap_integerRing σ) (AlgEquiv.restrictScalars_smul_integerRing (K := K))

open scoped Classical in
/-- **Serre's quotient formula for the lower index**. For an intermediate field `L` of `M/K`
normal over `K` and `σ' : Gal(L/K)`, `e(M/L) · i_{L/K}(σ') = ∑_{σ|_L = σ'} i_{M/K}(σ)`, the sum
running over the automorphisms of `M/K` restricting to `σ'`. -/
theorem ramificationIndex_mul_lowerIndex_eq_sum (σ' : L ≃ₐ[K] L) :
    (ramificationIndex L M : ℕ∞) * lowerIndex 𝒪[L] σ' =
      ∑ σ : M ≃ₐ[K] M with σ.restrictNormal L = σ', lowerIndex 𝒪[M] σ := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ'
  have hmul (ρ₁ ρ₂ : M ≃ₐ[K] M) :
      (ρ₁ * ρ₂).restrictNormal L = ρ₁.restrictNormal L * ρ₂.restrictNormal L :=
    map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L) ρ₁ ρ₂
  -- Rewrite only the left side to leave the fibre sum unchanged.
  conv_lhs => rw [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M,
    ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum]
  refine Finset.sum_nbij (fun τ ↦ σ₀ * τ.restrictScalars K) (fun τ _ ↦ ?_) (fun τ₁ _ τ₂ _ h ↦ ?_)
    (fun σ hσ ↦ ?_) fun _ _ ↦ rfl
  · rw [Finset.mem_filter, hmul,
      (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M
        (τ.restrictScalars K)).1 ⟨τ, rfl⟩, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · exact AlgEquiv.restrictScalars_injective K (mul_left_cancel h)
  · have hσ' : (σ₀⁻¹ * σ).restrictNormal L = 1 := by
      rw [hmul, (Finset.mem_filter.1 hσ).2,
        AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, ← hmul, inv_mul_cancel]
      exact map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
    obtain ⟨τ, hτ⟩ :=
      (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M (σ₀⁻¹ * σ)).2 hσ'
    have hτ' : τ.restrictScalars K = σ₀⁻¹ * σ := by
      simpa only [AlgEquiv.restrictScalarsHom_apply] using hτ
    exact ⟨τ, Finset.mem_univ _, by
      -- Expose the function supplied to `sum_nbij` before rewriting its value.
      change σ₀ * τ.restrictScalars K = σ
      rw [hτ', mul_inv_cancel_left]⟩

end TauCeti.LocalFieldsRamification
