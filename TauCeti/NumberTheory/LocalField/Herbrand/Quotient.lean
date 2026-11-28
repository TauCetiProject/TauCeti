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

All declarations live in `TauCeti.LocalFieldsRamification`.

* `lowerIndex_mul_restrictScalars_of_forall_le`:
  `i_G(σ τ) = min (i_H(τ), i_G(σ))` for `σ` of largest lower index in its coset.
* `ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum_card`:
  `e(M/L) · i_{G/H}(σ|_L) = ∑_{k < i_G(σ)} #H_k` for such `σ`.
* `coe_herbrand_lowerIndex_sub_one`: Serre's lemma
  `φ_{M/L}(i_G(σ) - 1) = i_{G/H}(σ|_L) - 1` for such `σ`.
* `map_restrictNormalHom_lowerRamificationGroupReal`:
  **Herbrand's theorem**, `(G/H)_{φ_{M/L}(u)} = G_u H / H`.
* `lowerRamificationGroupReal_eq_map_inverseHerbrand`: the same
  statement read at `v = φ_{M/L}(u)`, that is `(G/H)_v = G_{ψ_{M/L}(v)} H / H`.
* `natCard_lowerRamificationGroupReal_herbrand_mul`: Herbrand's
  theorem in counting form, `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`.
* `lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand`:
  the filtration of `L/K` is constant on `(φ_{M/L}(a), φ_{M/L}(b)]` when that of `M/K` is
  constant on `(a, b]`.

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

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [Module.Finite K L] [ValuativeExtension L M] [Module.Finite L M] [IsGalois L M] in
private theorem forall_mem_ker_restrictNormalHom {σ : M ≃ₐ[K] M}
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ) :
    ∀ h ∈ (AlgEquiv.restrictNormalHom L : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)).ker,
      lowerIndex 𝒪[M] (σ * h) ≤ lowerIndex 𝒪[M] σ := by
  intro h hh
  obtain ⟨τ, rfl⟩ := (AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M).ge hh
  exact hσ τ

omit [ValuativeExtension L M] [Module.Finite L M] [IsGalois L M] in
/-- If `σ` has the largest lower index in its coset `σ H` and `i_G(σ)` is finite, then so is
`i_{G/H}(σ|_L)`: a restriction of largest lower index among its lifts is trivial only when the
lift is. -/
theorem lowerIndex_restrictNormal_ne_top (σ : M ≃ₐ[K] M) (hj : lowerIndex 𝒪[M] σ ≠ ⊤)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ) :
    lowerIndex 𝒪[L] (σ.restrictNormal L) ≠ ⊤ :=
  TauCeti.IsLocalRing.lowerIndex_ne_top_of_forall_mem_ker_le hj
    (forall_mem_ker_restrictNormalHom hσ)

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

private theorem herbrandFun_lowerIndex_sub_one_restrictNormalHom (σ : M ≃ₐ[K] M) {j : ℕ}
    (hj : lowerIndex 𝒪[M] σ = j)
    (hσ : ∀ h ∈ (AlgEquiv.restrictNormalHom L : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)).ker,
      lowerIndex 𝒪[M] (σ * h) ≤ lowerIndex 𝒪[M] σ) :
    TauCeti.IsLocalRing.herbrandFun (M ≃ₐ[L] M) 𝒪[M] ((j : ℝ) - 1) =
      ((lowerIndex 𝒪[L] (AlgEquiv.restrictNormalHom L σ)).toNat : ℝ) - 1 := by
  rw [← coe_herbrand_eq_herbrandFun L M ⟨(j : ℝ) - 1, by simp⟩,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal]
  exact coe_herbrand_lowerIndex_sub_one σ hj fun τ ↦
    hσ _ ((AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M).le ⟨τ, rfl⟩)

/-- For `σ` of largest lower index in its coset `σ H`, the restriction `σ|_L` lies in the lower
ramification group of `L/K` at `φ_{M/L}(u)` exactly when `σ` lies in that of `M/K` at `u`. -/
theorem restrictNormal_mem_lowerRamificationGroupReal_herbrand_iff (σ : M ≃ₐ[K] M)
    (hσ : ∀ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) ≤ lowerIndex 𝒪[M] σ)
    (u : RamificationIndexDomain) :
    σ.restrictNormal L ∈ lowerRamificationGroupReal K L (herbrand L M u) ↔
      σ ∈ lowerRamificationGroupReal K M u := by
  have hσ' := forall_mem_ker_restrictNormalHom hσ
  rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M,
    lowerRamificationGroupReal_eq_ramificationGroupReal,
    lowerRamificationGroupReal_eq_ramificationGroupReal, coe_herbrand_eq_herbrandFun]
  exact TauCeti.IsLocalRing.apply_mem_ramificationGroupReal_iff
    (TauCeti.IsLocalRing.herbrandFun_strictMono (M ≃ₐ[L] M) 𝒪[M])
    (fun hj ↦ TauCeti.IsLocalRing.lowerIndex_ne_top_of_forall_mem_ker_le hj hσ')
    (fun hj ↦ herbrandFun_lowerIndex_sub_one_restrictNormalHom σ hj hσ') u

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
    (fun _ hσ hj ↦ TauCeti.IsLocalRing.lowerIndex_ne_top_of_forall_mem_ker_le hj hσ)
    (fun σ hσ _ hj ↦ herbrandFun_lowerIndex_sub_one_restrictNormalHom σ hj hσ) u

/-- Herbrand's theorem read at `v = φ_{M/L}(u)`: `(G/H)_v = G_{ψ_{M/L}(v)} H / H`. -/
theorem lowerRamificationGroupReal_eq_map_inverseHerbrand [Normal K M]
    (v : RamificationIndexDomain) :
    lowerRamificationGroupReal K L v =
      (lowerRamificationGroupReal K M (inverseHerbrand L M v)).map
        (AlgEquiv.restrictNormalHom L) := by
  rw [map_restrictNormalHom_lowerRamificationGroupReal, herbrand_inverseHerbrand]

section Counting

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M]
  [IsScalarTower K L M]

/-- **Herbrand's theorem in counting form.** For `G = Gal(M/K)`, `H = Gal(M/L)` and
`G/H = Gal(L/K)`, the orders satisfy `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`: the lower ramification
group of the quotient at `φ_{M/L}(u)` is the image of `G_u` under restriction to `L`, and the
kernel of restriction on `G_u` is `H ∩ G_u = H_u`. -/
theorem natCard_lowerRamificationGroupReal_herbrand_mul [Normal K L] [IsGalois L M] [Normal K M]
    (u : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) *
        Nat.card (lowerRamificationGroupReal L M u) =
      Nat.card (lowerRamificationGroupReal K M u) := by
  have : Module.Finite K M := Module.Finite.trans L M
  rw [← map_restrictNormalHom_lowerRamificationGroupReal (K := K) (L := L) (M := M) u,
    ← MonoidHom.domRestrict_range,
    ← Subgroup.card_map_of_injective (K := lowerRamificationGroupReal L M u)
      (AlgEquiv.restrictScalarsHom_injective K),
    map_restrictScalarsHom_lowerRamificationGroupReal K M L u,
    AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M,
    ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype, ← MonoidHom.ker_domRestrict,
    mul_comm, Subgroup.card_ker_mul_card_range]

/-- Through Herbrand's theorem, the lower filtration of `L/K` is constant on the interval
`(φ_{M/L}(a), φ_{M/L}(b)]` as soon as that of `M/K` is constant on `(a, b]`. -/
theorem lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand [Normal K L]
    [IsGalois L M] [Normal K M] {a b : RamificationIndexDomain} {t : ℝ}
    (ht₁ : (herbrand L M a : ℝ) < t) (ht₂ : t ≤ herbrand L M b) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    (∀ s : ℝ, (a : ℝ) < s → s ≤ b →
      lowerRamificationGroupReal K M s = lowerRamificationGroupReal K M b) →
    lowerRamificationGroupReal K L t = lowerRamificationGroupReal K L (herbrand L M b) := by
  have : Module.Finite K M := Module.Finite.trans L M
  intro h
  set s : RamificationIndexDomain := ⟨t, Set.mem_Ici.2 ((herbrand L M a).property.trans ht₁.le)⟩
  -- `t = φ_{M/L}(ψ_{M/L}(t))` with `a < ψ_{M/L}(t) ≤ b`.
  have hs₁ : a < inverseHerbrand L M s := by
    rw [← inverseHerbrand_herbrand L M a]
    exact inverseHerbrand_strictMono L M (Subtype.coe_lt_coe.1 ht₁)
  have hs₂ : inverseHerbrand L M s ≤ b := by
    rw [← inverseHerbrand_herbrand L M b]
    exact (inverseHerbrand_strictMono L M).monotone (Subtype.coe_le_coe.1 ht₂)
  have ht : t = herbrand L M (inverseHerbrand L M s) := by rw [herbrand_inverseHerbrand]
  rw [ht, ← map_restrictNormalHom_lowerRamificationGroupReal,
    ← map_restrictNormalHom_lowerRamificationGroupReal, h _ hs₁ hs₂]

end Counting

end TauCeti.LocalFieldsRamification
