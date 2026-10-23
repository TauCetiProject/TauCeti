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
  set τ' := τ.restrictScalars K
  -- `i(σ τ) ≥ min (i(σ), i(τ))`, and `i(τ) = i(σ⁻¹ (σ τ)) ≥ min (i(σ), i(σ τ)) = i(σ τ)`.
  have h₁ := TauCeti.IsLocalRing.min_le_lowerIndex_mul (S := 𝒪[M]) σ τ'
  have h₂ := TauCeti.IsLocalRing.min_le_lowerIndex_mul (S := 𝒪[M]) σ⁻¹ (σ * τ')
  rw [inv_mul_cancel_left, TauCeti.IsLocalRing.lowerIndex_inv, min_eq_right (hσ τ)] at h₂
  exact le_antisymm (le_min h₂ (hσ τ)) (by rw [min_comm]; exact h₁)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [Module.Finite K L] [Normal K L] [ValuativeExtension L M] [IsGalois L M] in
/-- Every coset `σ H` contains an element of largest lower index. -/
theorem exists_forall_lowerIndex_mul_restrictScalars_le (σ : M ≃ₐ[K] M) :
    ∃ τ₀ : M ≃ₐ[L] M, ∀ τ : M ≃ₐ[L] M,
      lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K * τ.restrictScalars K) ≤
        lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K) := by
  obtain ⟨τ₀, -, hτ₀⟩ := Finset.exists_max_image (Finset.univ : Finset (M ≃ₐ[L] M))
    (fun τ ↦ lowerIndex 𝒪[M] (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ ?_⟩
  have := hτ₀ (τ₀ * τ) (Finset.mem_univ _)
  rwa [← AlgEquiv.restrictScalarsHom_apply K (τ₀ * τ), map_mul, AlgEquiv.restrictScalarsHom_apply,
    AlgEquiv.restrictScalarsHom_apply, ← mul_assoc] at this

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
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_restrictNormal_ne_top σ (hj ▸ ENat.natCast_ne_top j) hσ)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj, ← natCard_lowerRamificationGroup_zero]
    at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (lowerRamificationGroup L M 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rcases j with _ | m
  · -- `j = 0`: both sides are `-1`.
    rw [herbrand_of_coe_le_zero L M (by simp)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or]
      at hsum
    simp [hsum]
  · -- `j = m + 1`: `#H_0 · n = #H_0 + (#H_1 + ⋯ + #H_m)` and `φ(m) = (#H_1 + ⋯ + #H_m) / #H_0`.
    rw [coe_herbrand_of_coe_eq_natCast L M m (by push_cast; ring), div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (lowerRamificationGroup L M 0) : ℝ) * n =
        Nat.card (lowerRamificationGroup L M 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (lowerRamificationGroup L M i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

/-- For `σ` of largest lower index in its coset `σ H`, the restriction `σ|_L` lies in the lower
ramification group of `L/K` at `φ_{M/L}(u)` exactly when `σ` lies in that of `M/K` at `u`. -/
theorem restrictNormal_mem_lowerRamificationGroupReal_herbrand_iff (σ : M ≃ₐ[K] M)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ)
    (u : RamificationIndexDomain) :
    σ.restrictNormal L ∈ lowerRamificationGroupReal K L (herbrand L M u) ↔
      σ ∈ lowerRamificationGroupReal K M u := by
  rcases eq_or_ne (lowerIndex 𝒪[M] σ) ⊤ with htop | htop
  · -- `i_G(σ) = ⊤` means `σ = 1`, and both sides hold.
    rw [TauCeti.IsLocalRing.lowerIndex_eq_top_iff] at htop
    subst htop
    rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, map_one]
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_restrictNormal_ne_top σ htop hσ)).symm,
    ← coe_herbrand_lowerIndex_sub_one σ hj.symm hσ,
    mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hj.symm]
  exact Subtype.coe_le_coe.trans (herbrand_strictMono L M).le_iff_le

/-- **Herbrand's theorem.** For `M/K` finite normal, `L/K` a normal subextension and
`H = Gal(M/L)`, the image of the lower ramification group `G_u` of `M/K` under restriction to
`L` is the lower ramification group of `L/K` at `φ_{M/L}(u)`:
`(G/H)_{φ_{M/L}(u)} = G_u H / H`. -/
@[simp]
theorem map_restrictNormalHom_lowerRamificationGroupReal [Normal K M]
    (u : RamificationIndexDomain) :
    (lowerRamificationGroupReal K M u).map (AlgEquiv.restrictNormalHom L) =
      lowerRamificationGroupReal K L (herbrand L M u) := by
  ext σ'
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_restrictScalars_le (L := L) σ
    rw [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
      ← AlgEquiv.restrictNormal_mul_restrictScalars K L M σ τ₀,
      restrictNormal_mem_lowerRamificationGroupReal_herbrand_iff _ hτ₀]
    -- `σ ∈ G_u` and `i(σ) ≤ i(σ τ₀)` give `σ τ₀ ∈ G_u`.
    have hle : lowerIndex 𝒪[M] σ ≤ lowerIndex 𝒪[M] (σ * τ₀.restrictScalars K) := by
      have := hτ₀ τ₀⁻¹
      simp only [← AlgEquiv.restrictScalarsHom_apply, map_inv, mul_inv_cancel_right] at this
      exact this
    rw [mem_lowerRamificationGroupReal_iff, mem_lowerRamificationGroup_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans hle
  · intro h
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ'
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_restrictScalars_le (L := L) σ
    refine ⟨σ * τ₀.restrictScalars K, ?_, ?_⟩
    · rw [← restrictNormal_mem_lowerRamificationGroupReal_herbrand_iff _ hτ₀,
        AlgEquiv.restrictNormal_mul_restrictScalars]
      exact h
    · rw [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
        AlgEquiv.restrictNormal_mul_restrictScalars,
        AlgEquiv.restrictNormalHom_apply_eq_restrictNormal]

/-- Herbrand's theorem read at `v = φ_{M/L}(u)`: `(G/H)_v = G_{ψ_{M/L}(v)} H / H`. -/
theorem lowerRamificationGroupReal_eq_map_inverseHerbrand [Normal K M]
    (v : RamificationIndexDomain) :
    lowerRamificationGroupReal K L v =
      (lowerRamificationGroupReal K M (inverseHerbrand L M v)).map
        (AlgEquiv.restrictNormalHom L) := by
  rw [map_restrictNormalHom_lowerRamificationGroupReal, herbrand_inverseHerbrand]

end TauCeti.LocalFieldsRamification
