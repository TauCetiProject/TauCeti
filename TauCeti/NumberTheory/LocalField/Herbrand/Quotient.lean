/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
public import TauCeti.NumberTheory.LocalField.LowerIndex

/-!
# Herbrand's theorem: the lower filtration of a quotient

Let `M/K` be a finite normal extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field, normal over `K` and with `M/L` Galois, so that restriction
`G → Gal(L/K)` identifies `Gal(L/K)` with the quotient `G / H` by `H = Gal(M/L)`. The lower
numbering is not compatible with this quotient, but **Herbrand's theorem** says exactly how it
fails: the image of `G_u` in `Gal(L/K)` is the lower ramification group at the index
`φ_{M/L}(u)`,

`(G/H)_{φ_{M/L}(u)} = G_u H / H`  for every `u ≥ -1`.

This is the statement through which the Herbrand function passes to quotients: the
transitivity `φ_{M/K} = φ_{L/K} ∘ φ_{M/L}` and the upper-numbering compatibility
`(G/H)^v = G^v H / H` both rest on it. The file also records Serre's lemma comparing the lower
indices of a lift `σ` of largest lower index in its coset and of its restriction `σ|_L`, which is
the finite-index content of the theorem.

## Main results

* `TauCeti.LocalFieldsRamification.lowerIndex_mul_restrictScalars_of_forall_le`:
  `i_G(σ τ) = min (i_H(τ), i_G(σ))` for `σ` of largest lower index in its coset.
* `TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum_card`:
  `e(M/L) · i_{G/H}(σ|_L) = ∑_{k < i_G(σ)} #H_k` for such `σ`.
* `TauCeti.LocalFieldsRamification.coe_herbrand_lowerIndex_sub_one`: Serre's lemma
  `φ_{M/L}(i_G(σ) - 1) = i_{G/H}(σ|_L) - 1` for such `σ`.
* `TauCeti.LocalFieldsRamification.map_restrictNormalHom_lowerRamificationGroupReal`:
  **Herbrand's theorem**, `(G/H)_{φ_{M/L}(u)} = G_u H / H`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_map_inverseHerbrand`: the same
  statement read at `v = φ_{M/L}(u)`, that is `(G/H)_v = G_{ψ_{M/L}(v)} H / H`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Lemmas 4 and 5.
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
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M] [IsGalois L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsScalarTower K L M]

omit [ValuativeExtension K L] [Module.Finite K L] [Normal K L] [IsGalois L M] in
/-- If `σ` has the largest lower index in its coset `σ H`, `H = Gal(M/L)`, then
`i_G(σ τ) = min (i_H(τ), i_G(σ))` for every `τ ∈ H`. -/
theorem lowerIndex_mul_restrictScalars_of_forall_le (σ : M ≃ₐ[K] M)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ)
    (τ : M ≃ₐ[L] M) :
    lowerIndex 𝒪[M] (σ * τ.restrictScalars K) =
      min (lowerIndex 𝒪[M] τ) (lowerIndex 𝒪[M] σ) := by
  rw [← lowerIndex_restrictScalars (K := K) τ]
  exact TauCeti.IsLocalRing.lowerIndex_mul_eq_min_of_le (hσ τ)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [Module.Finite K L] [Normal K L] [ValuativeExtension L M] [Module.Finite L M] [IsGalois L M] in
/-- Every coset `σ H` contains an element of largest lower index. -/
theorem exists_forall_lowerIndex_mul_restrictScalars_le (σ : M ≃ₐ[K] M) :
    ∃ τ₀ : M ≃ₐ[L] M, ∀ τ : M ≃ₐ[L] M,
      lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K * τ.restrictScalars K) ≤
        lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K) := by
  obtain ⟨_, ⟨τ₀, rfl⟩, hτ₀⟩ := Subgroup.exists_mem_forall_lowerIndex_mul_le
    (S := 𝒪[M]) (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range σ
  refine ⟨τ₀, fun τ ↦ ?_⟩
  simpa only [AlgEquiv.restrictScalarsHom_apply] using hτ₀ _ ⟨τ, rfl⟩

/-- **Serre's lemma on the lower index of a quotient**, in counting form. If `σ` has the
largest lower index in its coset `σ H`, and `i_G(σ) = j` is finite, then
`e(M/L) · i_{G/H}(σ|_L) = ∑_{k < j} #H_k`. -/
theorem ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum_card (σ : M ≃ₐ[K] M) {j : ℕ}
    (hj : lowerIndex 𝒪[M] σ = j)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ) :
    (ramificationIndex L M : ℕ∞) * lowerIndex 𝒪[L] (σ.restrictNormal L) =
      ∑ k ∈ Finset.range j, (Nat.card (lowerRamificationGroup L M k) : ℕ∞) := by
  rw [ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum σ]
  simp_rw [lowerIndex_mul_restrictScalars_of_forall_le σ hσ, hj, lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.sum_min_lowerIndex_natCast (G := M ≃ₐ[L] M) (S := 𝒪[M]) j

/-- If `σ` has the largest lower index in its coset `σ H` and `i_G(σ)` is finite, then so is
`i_{G/H}(σ|_L)`: a restriction of largest lower index among its lifts is trivial only when the
lift is. -/
theorem lowerIndex_restrictNormal_ne_top (σ : M ≃ₐ[K] M) (hj : lowerIndex 𝒪[M] σ ≠ ⊤)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ) :
    lowerIndex 𝒪[L] (σ.restrictNormal L) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj
  intro htop
  have hsum := ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum_card σ hj.symm hσ
  have he : (ramificationIndex L M : ℕ∞) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos (K := L) (L := M)).ne'
  rw [htop, ENat.mul_top he, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

/-- **Serre's lemma on the lower index of a quotient.** If `σ` has the largest lower index in its
coset `σ H`, and `i_G(σ) = j` is finite, then `φ_{M/L}(j - 1) = i_{G/H}(σ|_L) - 1`. -/
theorem coe_herbrand_lowerIndex_sub_one (σ : M ≃ₐ[K] M) {j : ℕ}
    (hj : lowerIndex 𝒪[M] σ = j)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ) :
    (herbrand L M ⟨(j : ℝ) - 1, by simp⟩ : ℝ) =
      ((lowerIndex 𝒪[L] (σ.restrictNormal L)).toNat : ℝ) - 1 := by
  have hsum := ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum_card σ hj hσ
  rw [← natCard_lowerRamificationGroup_zero] at hsum
  simp_rw [lowerRamificationGroup_def] at hsum
  rw [coe_herbrand_eq_herbrandFun]
  exact TauCeti.IsLocalRing.herbrandFun_sub_one_of_card_mul_eq_sum (M ≃ₐ[L] M) 𝒪[M]
    (lowerIndex_restrictNormal_ne_top σ (hj ▸ ENat.natCast_ne_top j) hσ) hsum

/-- For `σ` of largest lower index in its coset `σ H`, the restriction `σ|_L` lies in the lower
ramification group of `L/K` at `φ_{M/L}(u)` exactly when `σ` lies in that of `M/K` at `u`. -/
theorem restrictNormal_mem_lowerRamificationGroupReal_herbrand_iff (σ : M ≃ₐ[K] M)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ)
    (u : RamificationIndexDomain) :
    σ.restrictNormal L ∈ lowerRamificationGroupReal K L (herbrand L M u) ↔
      σ ∈ lowerRamificationGroupReal K M u := by
  rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M,
    lowerRamificationGroupReal_eq_ramificationGroupReal,
    lowerRamificationGroupReal_eq_ramificationGroupReal, coe_herbrand_eq_herbrandFun]
  exact TauCeti.IsLocalRing.apply_mem_ramificationGroupReal_iff
    (TauCeti.IsLocalRing.herbrandFun_strictMono (M ≃ₐ[L] M) 𝒪[M])
    (lowerIndex_restrictNormal_ne_top σ · hσ)
    (fun hj ↦ by
      simpa [coe_herbrand_eq_herbrandFun, AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M]
        using coe_herbrand_lowerIndex_sub_one σ hj hσ)
    u

/-- **Herbrand's theorem.** For `M/K` finite normal, `L/K` a normal subextension and
`H = Gal(M/L)`, the image of the lower ramification group `G_u` of `M/K` under restriction to
`L` is the lower ramification group of `L/K` at `φ_{M/L}(u)`:
`(G/H)_{φ_{M/L}(u)} = G_u H / H`. -/
@[simp]
theorem map_restrictNormalHom_lowerRamificationGroupReal [Normal K M]
    (u : RamificationIndexDomain) :
    (lowerRamificationGroupReal K M u).map (AlgEquiv.restrictNormalHom L) =
      lowerRamificationGroupReal K L (herbrand L M u) := by
  rw [lowerRamificationGroupReal_eq_ramificationGroupReal,
    lowerRamificationGroupReal_eq_ramificationGroupReal, coe_herbrand_eq_herbrandFun]
  exact TauCeti.IsLocalRing.map_ramificationGroupReal_eq_of_surjective
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M))
    (TauCeti.IsLocalRing.herbrandFun_strictMono (M ≃ₐ[L] M) 𝒪[M])
    (fun σ hσ htop ↦ lowerIndex_restrictNormal_ne_top σ htop fun τ ↦
      hσ _ ((AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M).le ⟨τ, rfl⟩))
    (fun σ hσ {j} hj ↦ by
      simpa [coe_herbrand_eq_herbrandFun, AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M]
        using coe_herbrand_lowerIndex_sub_one σ hj fun τ ↦
          hσ _ ((AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M).le ⟨τ, rfl⟩))
    u

/-- Herbrand's theorem read at `v = φ_{M/L}(u)`: `(G/H)_v = G_{ψ_{M/L}(v)} H / H`. -/
theorem lowerRamificationGroupReal_eq_map_inverseHerbrand [Normal K M]
    (v : RamificationIndexDomain) :
    lowerRamificationGroupReal K L v =
      (lowerRamificationGroupReal K M (inverseHerbrand L M v)).map
        (AlgEquiv.restrictNormalHom L) := by
  rw [map_restrictNormalHom_lowerRamificationGroupReal, herbrand_inverseHerbrand]

end TauCeti.LocalFieldsRamification
