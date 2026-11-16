/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
import Mathlib.Data.Nat.Log
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.GroupTheory.Index.Basic
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Tower
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Herbrand.HasseArf.Abelian

/-!
# Orbit counts and Artin slopes of a separable subextension

Let `L/K` be a finite separable extension of nonarchimedean local fields embedded in a finite
Galois extension `M/K` with `G = Gal(M/K)` and `H = Gal(M/L) = TauCeti.embeddingSubgroup K L M`.
For each upper ramification index `u ≥ -1`, `TauCeti.embeddingOrbitCount K L M u = [G : G^u H]`
counts the `G^u`-orbits on `K`-embeddings `L →ₐ[K] M` and is independent of `M` by Herbrand's
theorem. Beyond wild inertia `G_1`, every step index `[G_i H : G_{i+1} H]` (`i ≥ 1`) is a power
of `p = ringChar 𝓀[K]`; listing `φ_{M/K}(i) + 1` with multiplicity `log_p [G_i H : G_{i+1} H]`
yields the nondecreasing list of Artin slopes `TauCeti.artinSlopeList K L M`.

## Main definitions

* `TauCeti.embeddingSubgroup K L M`: the fixing subgroup `H = Gal(M/L)` inside `Gal(M/K)`.
* `TauCeti.embeddingOrbitCount K L M u`: the orbit count `[G : G^u H]` at upper index `u`.
* `TauCeti.artinSlopeList K L M`: the nondecreasing list of Artin slopes of `L/K`.

## Main results

* `TauCeti.embeddingOrbitCount_eq`: independence of `embeddingOrbitCount K L M u` from `M`.
* `TauCeti.exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList` and
  `TauCeti.artinSlopeList_eq`: multiplicity recovery from jump ratios and independence from `M`.
* `TauCeti.length_artinSlopeList` and `TauCeti.artinSlopeList_eq_nil_iff`: length equals
  `wildRamificationExponent K L`, empty iff tamely ramified.
* `TauCeti.exists_nat_eq_of_mem_artinSlopeList_self`: Hasse–Arf integrality for abelian `M/K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de
  caractéristique 0*, Appendix, §A.6.
-/

public section
noncomputable section

open IntermediateField ValuativeRel IsLocalRing TauCeti.LocalFieldsRamification

namespace TauCeti

/-! ### The fixing subgroup of an intermediate extension -/

section EmbeddingSubgroup

variable (K L M : Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The subgroup `H = Gal(M/L)` of `G = Gal(M/K)` fixing the image of `L` inside `M`. -/
def embeddingSubgroup : Subgroup (M ≃ₐ[K] M) :=
  (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup

/-- Defining formula for `embeddingSubgroup` as the fixing subgroup of the image of `L` in `M`. -/
theorem embeddingSubgroup_def :
    embeddingSubgroup K L M = (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup :=
  (rfl)

variable {K L M} in
/-- An automorphism `σ : M ≃ₐ[K] M` belongs to `embeddingSubgroup K L M` iff it fixes every
element in the image of `L`. -/
@[simp]
theorem mem_embeddingSubgroup_iff {σ : M ≃ₐ[K] M} :
    σ ∈ embeddingSubgroup K L M ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  rw [embeddingSubgroup_def, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x ↦ h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ ↦ hx ▸ h x⟩

/-- `embeddingSubgroup K L M` is the image of
`AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)`. No normality or finiteness is needed. -/
theorem range_restrictScalarsHom_eq_embeddingSubgroup :
    (AlgEquiv.restrictScalarsHom (S := L) K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range =
      embeddingSubgroup K L M := by
  ext σ
  rw [MonoidHom.mem_range, mem_embeddingSubgroup_iff]
  exact ⟨fun ⟨τ, h⟩ x ↦ h ▸ τ.commutes x,
    fun h ↦ ⟨{ σ with commutes' := h }, rfl⟩⟩

/-- For `L = M`, the fixing subgroup of `M` in `Gal(M/K)` is trivial. -/
@[simp]
theorem embeddingSubgroup_self : embeddingSubgroup K M M = ⊥ := by
  ext; simp [AlgEquiv.ext_iff]

/-- For `L = K`, every `K`-automorphism of `M` fixes the image of `K`. -/
@[simp]
theorem embeddingSubgroup_base : embeddingSubgroup K K M = ⊤ := by
  ext; simp

/-- In a tower `M / L / E / K`, the fixing subgroup of `L` is contained in that of `E`. -/
theorem embeddingSubgroup_antitone (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [Algebra E M] [IsScalarTower K E M] [IsScalarTower E L M] :
    embeddingSubgroup K L M ≤ embeddingSubgroup K E M := fun _ hσ ↦
  mem_embeddingSubgroup_iff.2 fun x ↦ by
    rw [IsScalarTower.algebraMap_apply E L M]
    exact mem_embeddingSubgroup_iff.1 hσ _

/-- In a finite Galois extension `M/K` containing `L`, the order of `embeddingSubgroup K L M`
equals `[M : L]`. -/
theorem natCard_embeddingSubgroup [Module.Finite K M] [IsGalois K M] :
    Nat.card (embeddingSubgroup K L M) = Module.finrank L M := by
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  rw [← range_restrictScalarsHom_eq_embeddingSubgroup K L M, ← Subgroup.map_top,
    Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective K),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank L M]

/-- In a finite Galois extension `M/K` containing `L`, the index of `embeddingSubgroup K L M` in
`Gal(M/K)` equals `[L : K]`. -/
@[simp]
theorem index_embeddingSubgroup [Module.Finite K M] [IsGalois K M] :
    (embeddingSubgroup K L M).index = Module.finrank K L := by
  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have h := (embeddingSubgroup K L M).index_mul_card
  rw [natCard_embeddingSubgroup K L M, IsGalois.card_aut_eq_finrank K M,
    ← Module.finrank_mul_finrank K L M] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

/-- In a tower `M' / M / L / K` with `M/K` normal, pulling `embeddingSubgroup K L M` back along
restriction `Gal(M'/K) →* Gal(M/K)` recovers `embeddingSubgroup K L M'`. -/
theorem comap_restrictNormalHom_embeddingSubgroup (M' : Type*) [Field M']
    [Algebra K M'] [Algebra L M'] [Algebra M M']
    [IsScalarTower K M M'] [IsScalarTower L M M'] [IsScalarTower K L M'] [Normal K M] :
    (embeddingSubgroup K L M).comap
        (AlgEquiv.restrictNormalHom M : (M' ≃ₐ[K] M') →* (M ≃ₐ[K] M)) =
      embeddingSubgroup K L M' := by
  ext σ'
  simp only [Subgroup.mem_comap, mem_embeddingSubgroup_iff]
  refine forall_congr' fun x ↦ ?_
  rw [← (algebraMap M M').injective.eq_iff]
  change algebraMap M M' (σ'.restrictNormal M _) = _ ↔ _
  rw [σ'.restrictNormal_commutes, ← IsScalarTower.algebraMap_apply L M M']

/-- Transport of `embeddingSubgroup` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem map_autCongr_embeddingSubgroup {M' : Type*} [Field M'] [Algebra K M'] [Algebra L M']
    [IsScalarTower K L M'] (e : M ≃ₐ[L] M') :
    (embeddingSubgroup K L M).map ((e.restrictScalars K).autCongr :
        (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) =
      embeddingSubgroup K L M' := by
  let eK : M ≃ₐ[K] M' := e.restrictScalars K
  ext σ'
  simp only [Subgroup.mem_map, mem_embeddingSubgroup_iff]
  refine ⟨fun ⟨σ, hσ, h⟩ x ↦ ?_,
    fun h ↦ ⟨eK.autCongr.symm σ', fun x ↦ ?_, eK.autCongr.apply_symm_apply σ'⟩⟩
  · rw [← h]
    simpa [eK, AlgEquiv.autCongr_apply, e.symm.commutes x, e.commutes x] using congrArg e (hσ x)
  · simpa [eK, AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, e.commutes x, e.symm.commutes x]
      using congrArg e.symm (h x)

end EmbeddingSubgroup

namespace LocalFieldsRamification

variable (K M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]

/-- At `J + 1 = (largestLowerJump K M).toNat + 1`, the lower ramification group of `M/K` is
trivial. -/
theorem lowerRamificationGroup_toNat_largestLowerJump_add_one :
    lowerRamificationGroup K M (((largestLowerJump K M).toNat + 1 : ℕ) : ℤ) = ⊥ :=
  lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
    (by have := neg_one_le_largestLowerJump K M; omega)

/-- In a finite Galois local-field extension, the index of the inertia group `G_0` is the
inertia degree. -/
theorem index_lowerRamificationGroup_zero [IsGalois K M] :
    (lowerRamificationGroup K M 0).index = inertiaDegree K M := by
  have h := (lowerRamificationGroup K M 0).index_mul_card
  rw [natCard_lowerRamificationGroup_zero K M, IsGalois.card_aut_eq_finrank K M,
    ← ramificationIndex_mul_inertiaDegree (K := K) (L := M), mul_comm _ (inertiaDegree K M)] at h
  exact Nat.eq_of_mul_eq_mul_right ramificationIndex_pos h

/-- In a finite Galois local-field extension, the index of wild inertia `G_1` is
`inertiaDegree K M * tameRamificationIndex K M`. -/
theorem index_lowerRamificationGroup_one [IsGalois K M] :
    (lowerRamificationGroup K M 1).index = inertiaDegree K M * tameRamificationIndex K M := by
  rw [← Subgroup.relIndex_mul_index
      (lowerRamificationGroup_antitone K M (by omega : (0 : ℤ) ≤ 1)),
    relIndex_lowerRamificationGroup_one_zero K M, index_lowerRamificationGroup_zero K M, mul_comm]

/-- For `v ∈ (φ_{M/K}(i), φ_{M/K}(i + 1)]` (`i : ℕ`), the upper ramification group `G^v` equals
the lower ramification group `G_{i + 1}`. -/
theorem upperRamificationGroup_eq_of_herbrand_lt_of_le [IsGalois K M] {i : ℕ}
    {v : RamificationIndexDomain}
    (hv₁ : herbrand K M ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ < v)
    (hv₂ : v ≤ herbrand K M ⟨((i + 1 : ℕ) : ℝ),
      Nat.cast_mem_ramificationIndexDomain (i + 1)⟩) :
    upperRamificationGroup K M v = lowerRamificationGroup K M ((i + 1 : ℕ) : ℤ) := by
  have h₁ := inverseHerbrand_strictMono K M hv₁
  have h₂ := (inverseHerbrand_strictMono K M).monotone hv₂
  rw [inverseHerbrand_herbrand] at h₁ h₂
  rw [upperRamificationGroup_def]
  exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((i + 1 : ℕ) : ℤ))
    (by have := Subtype.mk_lt_mk.1 h₁; push_cast; linarith)
    (by exact_mod_cast Subtype.mk_le_mk.1 h₂)

end LocalFieldsRamification

/-! ### Orbit counts of the upper ramification filtration -/

section OrbitCount

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

/-- The orbit count `[G : G^u H]` of the upper ramification group `G^u` of `M/K` acting on the
coset space `G / H` of `K`-embeddings of `L` into `M`. -/
def embeddingOrbitCount (u : RamificationIndexDomain) : ℕ :=
  (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).index

/-- Defining formula for `embeddingOrbitCount`. -/
theorem embeddingOrbitCount_def (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u =
      (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).index :=
  (rfl)

/-- The orbit count is positive at every upper ramification index. -/
theorem embeddingOrbitCount_pos (u : RamificationIndexDomain) :
    0 < embeddingOrbitCount K L M u := by
  have : Finite (M ≃ₐ[K] M) := Nat.finite_of_card_ne_zero (by
    rw [IsGalois.card_aut_eq_finrank K M]; exact Module.finrank_pos.ne')
  exact Subgroup.index_pos

/-- The orbit count is nondecreasing in the upper index `u`, because the upper ramification
filtration is antitone. -/
theorem embeddingOrbitCount_mono : Monotone (embeddingOrbitCount K L M) := fun _ _ h ↦
  Subgroup.index_antitone (sup_le_sup_right (upperRamificationGroup_antitone K M h) _)

/-- The orbit count never exceeds `[L : K]`. -/
theorem embeddingOrbitCount_le_finrank (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u ≤ Module.finrank K L := by
  rw [← index_embeddingSubgroup K L M]; exact Subgroup.index_antitone le_sup_right

/-- For `L = M`, `embeddingSubgroup K M M = ⊥`, so the orbit count is the index of `G^u` in
`Gal(M/K)`. -/
@[simp]
theorem embeddingOrbitCount_self_right (u : RamificationIndexDomain) :
    embeddingOrbitCount K M M u = (upperRamificationGroup K M u).index := by
  simp [embeddingOrbitCount_def]

/-- For `L = K`, `embeddingSubgroup K K M = ⊤`, so the orbit count is identically `1`. -/
@[simp]
theorem embeddingOrbitCount_self_left (u : RamificationIndexDomain) :
    embeddingOrbitCount K K M u = 1 := by
  simp [embeddingOrbitCount_def]

/-- At `u = -1`, `G^{-1} = Gal(M/K)`, so the orbit count is `1`. -/
@[simp]
theorem embeddingOrbitCount_neg_one :
    embeddingOrbitCount K L M ⟨-1, le_rfl⟩ = 1 := by
  have h1 := lowerRamificationGroupReal_intCast K M (-1)
  simp only [Int.cast_neg, Int.cast_one] at h1
  rw [embeddingOrbitCount_def, upperRamificationGroup_of_coe_le_zero K M (by norm_num), h1,
    lowerRamificationGroup_eq_top_of_le_neg_one K M le_rfl, top_sup_eq, Subgroup.index_top]

/-- Beyond `φ_{M/K}(N - 1)` where `G_N = ⊥`, the upper ramification group `G^u` is trivial and
the orbit count reaches `[L : K]`. -/
theorem embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot {N : ℕ}
    (hN : lowerRamificationGroup K M N = ⊥) {u : RamificationIndexDomain}
    (hu : (match N with
      | 0 => (-1 : ℝ)
      | m + 1 =>
        (herbrand K M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩ : ℝ)) < (u : ℝ)) :
    embeddingOrbitCount K L M u = Module.finrank K L := by
  have hbot : upperRamificationGroup K M u = ⊥ := by
    rw [upperRamificationGroup_def, lowerRamificationGroupReal_def, ← le_bot_iff, ← hN]
    have hlt : (((N : ℤ) - 1 : ℤ) : ℝ) < inverseHerbrand K M u := by
      cases N with
      | zero =>
        have hψ := inverseHerbrand_strictMono K M (Subtype.mk_lt_mk.2 hu : ⟨-1, le_rfl⟩ < u)
        rw [inverseHerbrand_of_coe_le_zero K M (by norm_num)] at hψ
        simpa using Subtype.mk_lt_mk.1 hψ
      | succ m =>
        have hψ := inverseHerbrand_strictMono K M (Subtype.mk_lt_mk.2 hu :
          herbrand K M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩ < u)
        rw [inverseHerbrand_herbrand] at hψ
        simpa using Subtype.mk_lt_mk.1 hψ
    have hceil : (N : ℤ) - 1 < ⌈(inverseHerbrand K M u : ℝ)⌉ := Int.lt_ceil.2 hlt
    exact lowerRamificationGroup_antitone K M (by omega)
  rw [embeddingOrbitCount_def, hbot, bot_sup_eq, index_embeddingSubgroup]

/-- **Tower invariance of `embeddingOrbitCount`.** In a tower `M' / M / L / K` of local fields
with both `M/K` and `M'/K` finite Galois, `embeddingOrbitCount K L M' u` agrees with
`embeddingOrbitCount K L M u`. -/
theorem embeddingOrbitCount_tower_eq (M' : Type*)
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L M'] [Algebra M M']
    [IsScalarTower K M M'] [IsScalarTower L M M'] [IsScalarTower K L M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M' u = embeddingOrbitCount K L M u := by
  have : Algebra.IsAlgebraic K M' := Algebra.IsAlgebraic.of_finite K M'
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : ValuativeExtension M M' := .of_isScalarTower (K := K)
  have : Module.Finite M M' := .of_restrictScalars_finite K M M'
  let π : (M' ≃ₐ[K] M') →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hsurj : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective M'
  have hker : π.ker ≤ embeddingSubgroup K L M' :=
    comap_restrictNormalHom_embeddingSubgroup K L M M' ▸ Subgroup.comap_mono bot_le
  have hmap : (upperRamificationGroup K M' u ⊔ embeddingSubgroup K L M').map π =
      upperRamificationGroup K M u ⊔ embeddingSubgroup K L M := by
    rw [Subgroup.map_sup, map_restrictNormalHom_upperRamificationGroup K M M' u,
      ← comap_restrictNormalHom_embeddingSubgroup K L M M',
      Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def,
    ← Subgroup.index_comap_of_surjective _ hsurj, ← hmap,
    Subgroup.comap_map_eq_self (hker.trans le_sup_right)]

/-- Transport of `embeddingOrbitCount` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem embeddingOrbitCount_eq_of_algEquiv {M' : Type*}
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L M'] [IsScalarTower K L M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (e : M ≃ₐ[L] M') (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L M' u := by
  let eK : M ≃ₐ[K] M' := e.restrictScalars K
  have hsup : (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).map
      (eK.autCongr : (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) =
      upperRamificationGroup K M' u ⊔ embeddingSubgroup K L M' := by
    rw [Subgroup.map_sup, map_autCongr_upperRamificationGroup eK u,
      map_autCongr_embeddingSubgroup K L M e]
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def, ← hsup]
  exact (Subgroup.index_map_equiv _ eK.autCongr).symm

/-- Helper comparing `embeddingOrbitCount K L M u` against a finite Galois intermediate field
`N` of `AlgebraicClosure L` containing the image of `M`. -/
private theorem embeddingOrbitCount_eq_intermediateField
    {N : IntermediateField K (AlgebraicClosure L)} [Module.Finite K N] [IsGalois K N]
    [ValuativeRel N] [TopologicalSpace N] [IsNonarchimedeanLocalField N]
    [ValuativeExtension K N] [Algebra L N] [IsScalarTower K L N]
    (hLN : ∀ x : L, ((algebraMap L N x : N) : AlgebraicClosure L) = algebraMap L _ x)
    (ι : M →ₐ[L] AlgebraicClosure L) (hFN : (ι.restrictScalars K).fieldRange ≤ N)
    (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L N u := by
  let Ω := AlgebraicClosure L
  let F : IntermediateField K Ω := (ι.restrictScalars K).fieldRange
  let eK : M ≃ₐ[K] F := AlgEquiv.ofInjectiveField (ι.restrictScalars K)
  have : Module.Finite K F := Module.Finite.equiv eK.toLinearEquiv
  have : IsGalois K F := IsGalois.of_algEquiv eK
  let _ := finiteIntermediateFieldValuativeRel K Ω F
  let _ := finiteIntermediateFieldTopology K Ω F
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω F
  have := finiteIntermediateField_valuativeExtension K Ω F
  let _ : Algebra L F := ((eK : M →+* F).comp (algebraMap L M)).toAlgebra
  have : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply K L M]
    exact (eK.commutes x).symm
  let j : F →ₐ[K] N := IntermediateField.inclusion hFN
  let _ : Algebra F N := j.toRingHom.toAlgebra
  have : IsScalarTower K F N := IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  have : IsScalarTower L F N := IsScalarTower.of_algebraMap_eq fun x ↦
    Subtype.ext ((hLN x).trans (ι.commutes x).symm)
  rw [embeddingOrbitCount_eq_of_algEquiv K L M ({ eK with commutes' := fun _ ↦ rfl }) u,
    ← embeddingOrbitCount_tower_eq K L F N u]

/-- **Independence of the finite Galois overfield.** For any two finite Galois extensions `M₁/K`
and `M₂/K` of nonarchimedean local fields containing `L`, the orbit counts
`embeddingOrbitCount K L M₁ u` and `embeddingOrbitCount K L M₂ u` agree. -/
theorem embeddingOrbitCount_eq (M₂ : Type*)
    [Field M₂] [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [Algebra K M₂] [Algebra L M₂] [IsScalarTower K L M₂]
    [ValuativeExtension K M₂] [Module.Finite K M₂] [IsGalois K M₂]
    (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L M₂ u := by
  let Ω := AlgebraicClosure L
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have : Module.Finite L M₂ := .of_restrictScalars_finite K L M₂
  have : Algebra.IsAlgebraic L M := Algebra.IsAlgebraic.of_finite L M
  have : Algebra.IsAlgebraic L M₂ := Algebra.IsAlgebraic.of_finite L M₂
  let ι₁ : M →ₐ[L] Ω := IsAlgClosed.lift
  let ι₂ : M₂ →ₐ[L] Ω := IsAlgClosed.lift
  let F₁ : IntermediateField K Ω := (ι₁.restrictScalars K).fieldRange
  let F₂ : IntermediateField K Ω := (ι₂.restrictScalars K).fieldRange
  let N : IntermediateField K Ω := F₁ ⊔ F₂
  have : Module.Finite K F₁ :=
    Module.Finite.equiv (AlgEquiv.ofInjectiveField (ι₁.restrictScalars K)).toLinearEquiv
  have : Module.Finite K F₂ :=
    Module.Finite.equiv (AlgEquiv.ofInjectiveField (ι₂.restrictScalars K)).toLinearEquiv
  have : IsGalois K F₁ :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField (ι₁.restrictScalars K))
  have : IsGalois K F₂ :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField (ι₂.restrictScalars K))
  have : Module.Finite K N := IntermediateField.finiteDimensional_sup F₁ F₂
  have : IsGalois K N := inferInstance
  let _ := finiteIntermediateFieldValuativeRel K Ω N
  let _ := finiteIntermediateFieldTopology K Ω N
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω N
  have := finiteIntermediateField_valuativeExtension K Ω N
  let _ : Algebra L N := ((algebraMap L Ω).codRestrict N.toSubring fun x ↦
    le_sup_left (a := F₁) (b := F₂) ⟨algebraMap L M x, ι₁.commutes x⟩).toAlgebra
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext
    (IsScalarTower.algebraMap_apply K L Ω x)
  rw [embeddingOrbitCount_eq_intermediateField K L M (N := N) (fun _ ↦ rfl) ι₁ le_sup_left u,
    embeddingOrbitCount_eq_intermediateField K L M₂ (N := N) (fun _ ↦ rfl) ι₂ le_sup_right u]

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

omit [IsGalois K M] in
/-- For a tower `M/L/K` with `M/K` Galois, the relative index of `lowerRamificationGroup K M i`
in `embeddingSubgroup K L M` equals the index of `lowerRamificationGroup L M i` in `Gal(M/L)`. -/
private theorem relIndex_lowerRamificationGroup_embeddingSubgroup (i : ℤ) :
    haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
    haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
    haveI : ValuativeExtension L M := .of_isScalarTower (K := K)
    haveI : Module.Finite L M := .of_restrictScalars_finite K L M
    (lowerRamificationGroup K M i).relIndex (embeddingSubgroup K L M) =
      (lowerRamificationGroup L M i).index := by
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  let f : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M) := AlgEquiv.restrictScalarsHom K
  rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L i,
    ← range_restrictScalarsHom_eq_embeddingSubgroup K L M, Subgroup.relIndex,
    ← Subgroup.index_comap_of_surjective _ (fun ⟨_, σ, h⟩ ↦ ⟨σ, Subtype.ext h⟩ :
      Function.Surjective f.rangeRestrict)]
  rfl

/-- The index `[G : G_0 H]` of inertia joined with `H` equals the inertia degree `f(L/K)`. -/
@[simp]
theorem index_lowerRamificationGroup_zero_sup_embeddingSubgroup :
    (lowerRamificationGroup K M 0 ⊔ embeddingSubgroup K L M).index = inertiaDegree K L := by
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  have hmul : (lowerRamificationGroup K M 0).relIndex (embeddingSubgroup K L M) *
      (lowerRamificationGroup K M 0 ⊔ embeddingSubgroup K L M).index =
        (lowerRamificationGroup K M 0).index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  rw [relIndex_lowerRamificationGroup_embeddingSubgroup K L M 0,
    index_lowerRamificationGroup_zero L M, index_lowerRamificationGroup_zero K M,
    inertiaDegree_tower (K := K) (L := L) M, mul_comm (inertiaDegree K L)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (inertiaDegree_pos (K := L) (L := M)) hmul

/-- On `(-1, 0]`, the upper ramification group `G^u` equals inertia `G_0`, so the orbit count is
`inertiaDegree K L`. -/
theorem embeddingOrbitCount_of_mem_Ioc_zero {u : RamificationIndexDomain}
    (hu₁ : (-1 : ℝ) < u) (hu₂ : (u : ℝ) ≤ 0) :
    embeddingOrbitCount K L M u = inertiaDegree K L := by
  rw [embeddingOrbitCount_def, upperRamificationGroup_of_coe_le_zero K M hu₂,
    lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := 0)
      (by simpa using hu₁) (by simpa using hu₂),
    index_lowerRamificationGroup_zero_sup_embeddingSubgroup]

/-- At `u = 0`, the orbit count equals `inertiaDegree K L`. -/
@[simp]
theorem embeddingOrbitCount_zero :
    embeddingOrbitCount K L M ⟨0, by norm_num⟩ = inertiaDegree K L :=
  embeddingOrbitCount_of_mem_Ioc_zero K L M (by norm_num) le_rfl

/-- The index `[G : G_1 H]` of wild inertia joined with `H` equals
`inertiaDegree K L * tameRamificationIndex K L`. -/
@[simp]
theorem index_lowerRamificationGroup_one_sup_embeddingSubgroup :
    (lowerRamificationGroup K M 1 ⊔ embeddingSubgroup K L M).index =
      inertiaDegree K L * tameRamificationIndex K L := by
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  have hmul : (lowerRamificationGroup K M 1).relIndex (embeddingSubgroup K L M) *
      (lowerRamificationGroup K M 1 ⊔ embeddingSubgroup K L M).index =
        (lowerRamificationGroup K M 1).index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  rw [relIndex_lowerRamificationGroup_embeddingSubgroup K L M 1,
    index_lowerRamificationGroup_one L M, index_lowerRamificationGroup_one K M,
    inertiaDegree_tower (K := K) (L := L) M, tameRamificationIndex_tower K L M] at hmul
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (inertiaDegree_pos (K := L) (L := M)) (tameRamificationIndex_pos L M)) ?_
  linear_combination hmul

/-- The relative index `[G_1 H : H]` equals `p ^ wildRamificationExponent K L`, where `p` is the
residue characteristic of `K`. -/
theorem relIndex_embeddingSubgroup_lowerRamificationGroup_one :
    (embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M 1 ⊔ embeddingSubgroup K L M) =
      ringChar 𝓀[K] ^ wildRamificationExponent K L := by
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_right : embeddingSubgroup K L M ≤
      lowerRamificationGroup K M 1 ⊔ embeddingSubgroup K L M)
  rw [index_lowerRamificationGroup_one_sup_embeddingSubgroup K L M,
    index_embeddingSubgroup K L M, ← ramificationIndex_mul_inertiaDegree (K := K) (L := L),
    ← tameRamificationIndex_mul_pow_wildRamificationExponent K L] at hmul
  refine Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (inertiaDegree_pos (K := K) (L := L)) (tameRamificationIndex_pos K L)) ?_
  linear_combination hmul

end OrbitCount

/-! ### The Artin slope list -/

section ArtinSlopeList

private theorem list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n <;> simp [List.range_succ, Finset.sum_range_succ, *]

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

/-- The **Artin slopes** of `L/K` read in a finite Galois extension `M/K`, in nondecreasing order
with multiplicity: for each integer lower index `1 ≤ i ≤ largestLowerJump K M` of `G = Gal(M/K)`,
the value `φ_{M/K}(i) + 1` is listed `log_p [G_i H : G_{i+1} H]` times, where
`H = embeddingSubgroup K L M` and `p = ringChar 𝓀[K]`. -/
def artinSlopeList : List ℝ :=
  (List.range (largestLowerJump K M).toNat).flatMap fun j =>
    List.replicate
      (Nat.log (ringChar 𝓀[K])
        ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)))
      ((herbrand K M ⟨((j + 1 : ℕ) : ℝ),
        Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1)

/-- Defining formula for `artinSlopeList`. -/
theorem artinSlopeList_def :
    artinSlopeList K L M =
      (List.range (largestLowerJump K M).toNat).flatMap fun j =>
        List.replicate
          (Nat.log (ringChar 𝓀[K])
            ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
              (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)))
          ((herbrand K M ⟨((j + 1 : ℕ) : ℝ),
            Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1) :=
  (rfl)

/-- Every Artin slope of `L/K` is strictly greater than `1`. -/
theorem one_lt_of_mem_artinSlopeList {a : ℝ} (ha : a ∈ artinSlopeList K L M) :
    1 < a := by
  rw [artinSlopeList_def, List.mem_flatMap] at ha
  obtain ⟨j, -, hj⟩ := ha
  obtain ⟨-, rfl⟩ := List.mem_replicate.1 hj
  have hpos := Subtype.mk_lt_mk.1 (herbrand_strictMono K M
    (Subtype.mk_lt_mk.2 (by positivity) : (⟨0, by norm_num⟩ : RamificationIndexDomain) <
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩))
  rw [herbrand_of_coe_le_zero K M le_rfl] at hpos
  linarith

/-- `artinSlopeList K L M` is sorted in nondecreasing order. -/
theorem pairwise_le_artinSlopeList :
    (artinSlopeList K L M).Pairwise (· ≤ ·) := by
  rw [artinSlopeList_def, List.pairwise_flatMap]
  refine ⟨fun _ _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl),
    List.Pairwise.imp (R := (· < ·)) (fun {i j} hij _ ha _ hb ↦ ?_) List.pairwise_lt_range⟩
  rw [(List.mem_replicate.1 ha).2, (List.mem_replicate.1 hb).2]
  have hlt := Subtype.mk_lt_mk.1 (herbrand_strictMono K M
    (Subtype.mk_lt_mk.2 (by exact_mod_cast Nat.add_lt_add_right hij 1) :
      (⟨((i + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ :
        RamificationIndexDomain) <
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩))
  linarith

/-- **Multiplicity in `artinSlopeList` from `embeddingOrbitCount`.** For every real `a > 1`,
putting `u = a - 1`, there is `w > u` such that for every `v ∈ (u, w]`, the `p`-logarithm of the
jump ratio `embeddingOrbitCount K L M v / embeddingOrbitCount K L M u` equals the multiplicity of
`a` in `artinSlopeList K L M`. -/
theorem exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList {a : ℝ}
    (ha : 1 < a) :
    ∃ w : RamificationIndexDomain,
      (⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ : RamificationIndexDomain) < w ∧
      ∀ v : RamificationIndexDomain,
        (⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ : RamificationIndexDomain) < v → v ≤ w →
          Nat.log (ringChar 𝓀[K])
            (embeddingOrbitCount K L M v /
              embeddingOrbitCount K L M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩) =
              (artinSlopeList K L M).count a := by
  set u : RamificationIndexDomain := ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩
  set J := (largestLowerJump K M).toNat
  set H := embeddingSubgroup K L M
  let d : ℕ → ℕ := fun j ↦ Nat.log (ringChar 𝓀[K])
    ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H).relIndex
      (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H))
  let val : ℕ → ℝ := fun j ↦
    (herbrand K M ⟨((j + 1 : ℕ) : ℝ),
      Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1
  have hval_inj : Function.Injective val := fun i j hij ↦ by
    have hφ : (⟨((i + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ :
        RamificationIndexDomain) =
        ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
      (herbrand_strictMono K M).injective (Subtype.ext (by dsimp [val] at hij; linarith))
    have hval := congrArg Subtype.val hφ
    exact_mod_cast (by dsimp at hval; push_cast at hval; linarith : (i : ℝ) = j)
  have hcount_zero (h : ∀ j < J, val j ≠ a) : (artinSlopeList K L M).count a = 0 := by
    rw [List.count_eq_zero, artinSlopeList_def, List.mem_flatMap]
    rintro ⟨j, hj, hm⟩
    exact h j (List.mem_range.1 hj) (List.mem_replicate.1 hm).2.symm
  set x := inverseHerbrand K M u with hx_def
  have hx_pos : (0 : ℝ) < x := by
    have hψ := inverseHerbrand_strictMono K M
      (Subtype.mk_lt_mk.2 (sub_pos.2 ha) : ⟨0, by norm_num⟩ < u)
    rw [inverseHerbrand_of_coe_le_zero K M le_rfl] at hψ
    exact Subtype.mk_lt_mk.1 hψ
  by_cases hint : ∃ j : ℕ, (x : ℝ) = ((j + 1 : ℕ) : ℝ)
  · obtain ⟨j, hj⟩ := hint
    have hx_eq : x = ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
      Subtype.ext hj
    have hu_φ : herbrand K M ⟨((j + 1 : ℕ) : ℝ),
        Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ = u := by
      rw [← hx_eq, hx_def, herbrand_inverseHerbrand]
    have ha_eq : val j = a := by
      have := congrArg Subtype.val hu_φ; dsimp [val, u] at this ⊢; linarith
    let w := herbrand K M ⟨((j + 2 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 2)⟩
    refine ⟨w, hu_φ ▸ herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by push_cast; linarith)),
      fun v huv hvw ↦ ?_⟩
    have hGu : upperRamificationGroup K M u = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def, ← hx_def, hx_eq]
      simpa using lowerRamificationGroupReal_intCast K M ((j + 1 : ℕ) : ℤ)
    have hGv : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) :=
      upperRamificationGroup_eq_of_herbrand_lt_of_le K M (i := j + 1) (hu_φ.symm ▸ huv) hvw
    have hdiv : embeddingOrbitCount K L M v / embeddingOrbitCount K L M u =
        (lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H).relIndex
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H) := by
      have hmul := Subgroup.relIndex_mul_index
        (sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H :
          lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H ≤
            lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H)
      rw [embeddingOrbitCount_def, embeddingOrbitCount_def, hGv, hGu, ← hmul]
      exact Nat.mul_div_left _
        (by rw [← hGu, ← embeddingOrbitCount_def]; exact embeddingOrbitCount_pos K L M u)
    rw [hdiv]
    by_cases hjJ : j < J
    · rw [artinSlopeList_def, List.count_flatMap]
      symm
      rw [list_sum_map_range, Finset.sum_eq_single j]
      · change List.count a (List.replicate (d j) (val j)) = d j
        rw [ha_eq, List.count_replicate_self]
      · intro k _ hkj
        change List.count a (List.replicate (d k) (val k)) = 0
        exact List.count_eq_zero.2 fun hm ↦
          hkj (hval_inj ((List.mem_replicate.1 hm).2.symm.trans ha_eq.symm))
      · exact fun h ↦ absurd (Finset.mem_range.2 hjJ) h
    · have hbot₁ : lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) = ⊥ :=
        lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
          (by have := neg_one_le_largestLowerJump K M; omega)
      have hbot₂ : lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) = ⊥ :=
        lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
          (by have := neg_one_le_largestLowerJump K M; omega)
      rw [hbot₁, hbot₂, Subgroup.relIndex_self, Nat.log_one_right,
        hcount_zero fun k hk hka ↦ hjJ (hval_inj (hka.trans ha_eq.symm) ▸ hk)]
  · push Not at hint
    have hceil_pos : (0 : ℤ) < ⌈(x : ℝ)⌉ := Int.lt_ceil.2 (by simpa using hx_pos)
    obtain ⟨j, hj_ceil⟩ : ∃ j : ℕ, ⌈(x : ℝ)⌉ = ((j + 1 : ℕ) : ℤ) :=
      ⟨(⌈(x : ℝ)⌉ - 1).toNat, by omega⟩
    have hxj₁ : (j : ℝ) < x := by
      have h1 : (((j + 1 : ℕ) : ℤ) : ℝ) - 1 < x :=
        hj_ceil ▸ sub_lt_iff_lt_add.2 (Int.ceil_lt_add_one (x : ℝ))
      push_cast at h1; linarith
    have hxj₂ : (x : ℝ) < ((j + 1 : ℕ) : ℝ) :=
      lt_of_le_of_ne (by have h := Int.le_ceil (x : ℝ); rw [hj_ceil] at h; exact_mod_cast h)
        (hint j)
    let w := herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩
    have hφj_lt : herbrand K M ⟨j, Nat.cast_mem_ramificationIndexDomain j⟩ < u := by
      rw [← herbrand_inverseHerbrand K M u]
      exact herbrand_strictMono K M (Subtype.mk_lt_mk.2 hxj₁)
    have huw : u < w := by
      rw [← herbrand_inverseHerbrand K M u]
      exact herbrand_strictMono K M (Subtype.mk_lt_mk.2 hxj₂)
    refine ⟨w, huw, fun v huv hvw ↦ ?_⟩
    have hGu : upperRamificationGroup K M u = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) :=
      upperRamificationGroup_eq_of_herbrand_lt_of_le K M hφj_lt huw.le
    have hGv : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) :=
      upperRamificationGroup_eq_of_herbrand_lt_of_le K M (hφj_lt.trans huv) hvw
    rw [show embeddingOrbitCount K L M v = embeddingOrbitCount K L M u by
        rw [embeddingOrbitCount_def, embeddingOrbitCount_def, hGv, hGu],
      Nat.div_self (embeddingOrbitCount_pos K L M u), Nat.log_one_right,
      hcount_zero fun k _ hka ↦ hint k <| by
        have h := inverseHerbrand_herbrand K M
          ⟨((k + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (k + 1)⟩
        rw [show herbrand K M _ = u from Subtype.ext (by dsimp [val, u] at hka ⊢; linarith),
          ← hx_def] at h
        exact congrArg Subtype.val h]

/-- **Independence of `artinSlopeList` from the finite Galois overfield.** For any two finite
Galois extensions `M/K` and `M₂/K` containing `L`, `artinSlopeList K L M = artinSlopeList K L M₂`.
-/
theorem artinSlopeList_eq (M₂ : Type*)
    [Field M₂] [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [Algebra K M₂] [Algebra L M₂] [IsScalarTower K L M₂]
    [ValuativeExtension K M₂] [Module.Finite K M₂] [IsGalois K M₂] :
    artinSlopeList K L M = artinSlopeList K L M₂ := by
  refine List.Perm.eq_of_pairwise'
    (pairwise_le_artinSlopeList K L M) (pairwise_le_artinSlopeList K L M₂)
    (List.perm_iff_count.2 fun a ↦ ?_)
  by_cases ha : 1 < a
  · obtain ⟨w₁, huw₁, hw₁⟩ :=
      exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L M ha
    obtain ⟨w₂, huw₂, hw₂⟩ :=
      exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L M₂ ha
    rw [← hw₁ (min w₁ w₂) (lt_min huw₁ huw₂) (min_le_left _ _),
      ← hw₂ (min w₁ w₂) (lt_min huw₁ huw₂) (min_le_right _ _),
      embeddingOrbitCount_eq K L M M₂ _, embeddingOrbitCount_eq K L M M₂ _]
  · simp [List.count_eq_zero.2 fun hm ↦ ha (one_lt_of_mem_artinSlopeList K L _ hm)]

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

/-- Every step index `[G_{i+1} H : G_{i+2} H]` (`i ≥ 0`) divides
`p ^ wildRamificationExponent K L`, hence equals `p ^ log_p [G_{i+1} H : G_{i+2} H]`. -/
theorem pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup (j : ℕ) :
    ringChar 𝓀[K] ^
        Nat.log (ringChar 𝓀[K])
          ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
            (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) =
      (lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  set H := embeddingSubgroup K L M
  set K₂ := lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H
  set K₁ := lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H
  set K₀ := lowerRamificationGroup K M 1 ⊔ H
  have h₂₁ : K₂ ≤ K₁ :=
    sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have h₁₀ : K₁ ≤ K₀ :=
    sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have hdvd : K₂.relIndex K₁ ∣ ringChar 𝓀[K] ^ wildRamificationExponent K L := by
    rw [← relIndex_embeddingSubgroup_lowerRamificationGroup_one K L M,
      ← Subgroup.relIndex_mul_relIndex H K₁ K₀ (le_sup_right.trans h₂₁) h₁₀,
      ← Subgroup.relIndex_mul_relIndex H K₂ K₁ le_sup_right h₂₁]
    exact ⟨H.relIndex K₂ * K₁.relIndex K₀, by ring⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hm, Nat.log_pow hp.one_lt]

/-- The product of the step indices `[G_{j+1} H : G_{j+2} H]` over
`j < (largestLowerJump K M).toNat` equals `[G_1 H : H] = p ^ wildRamificationExponent K L`. -/
private theorem prod_relIndex_lowerRamificationGroup_sup_embeddingSubgroup :
    ∏ j ∈ Finset.range (largestLowerJump K M).toNat,
        ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) =
      ringChar 𝓀[K] ^ wildRamificationExponent K L := by
  set H := embeddingSubgroup K L M
  set A : ℕ → Subgroup (M ≃ₐ[K] M) :=
    fun n ↦ lowerRamificationGroup K M (((n + 1 : ℕ) : ℤ)) ⊔ H
  have hchain (n : ℕ) :
      ∏ j ∈ Finset.range n, (A (j + 1)).relIndex (A j) = (A n).relIndex (A 0) := by
    induction n with
    | zero => simp [Subgroup.relIndex_self]
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, mul_comm]
      exact Subgroup.relIndex_mul_relIndex (A (m + 1)) (A m) (A 0)
        (sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H)
        (sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H)
  rw [hchain (largestLowerJump K M).toNat]
  dsimp only [A]
  rw [lowerRamificationGroup_toNat_largestLowerJump_add_one, bot_sup_eq]
  simpa using relIndex_embeddingSubgroup_lowerRamificationGroup_one K L M

/-- The number of Artin slopes (counted with multiplicity) equals the wild ramification exponent
`w(L/K) = v_p(e(L/K))`. -/
@[simp]
theorem length_artinSlopeList :
    (artinSlopeList K L M).length = wildRamificationExponent K L := by
  apply Nat.pow_right_injective (CharP.prime_ringChar 𝓀[K]).two_le
  dsimp only
  rw [artinSlopeList_def, List.length_flatMap, list_sum_map_range,
    ← Finset.prod_pow_eq_pow_sum,
    ← prod_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M]
  exact Finset.prod_congr rfl fun j _ ↦ by
    simpa [List.length_replicate] using
      pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M j

/-- `artinSlopeList K L M` is empty if and only if `L/K` is tamely ramified. -/
@[simp]
theorem artinSlopeList_eq_nil_iff :
    artinSlopeList K L M = [] ↔ IsTamelyRamified K L := by
  rw [← List.length_eq_zero_iff, length_artinSlopeList, wildRamificationExponent_eq_zero_iff]

end ArtinSlopeList

/-- **Hasse–Arf integrality of abelian Galois Artin slopes.** When `M/K` is a finite abelian
Galois extension, every entry of `artinSlopeList K M M` is a natural number `n ≥ 2`. -/
theorem exists_nat_eq_of_mem_artinSlopeList_self (K M : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsAbelianGalois K M] {a : ℝ}
    (ha : a ∈ artinSlopeList K M M) :
    ∃ n : ℕ, 2 ≤ n ∧ a = n := by
  have ha1 := one_lt_of_mem_artinSlopeList K M M ha
  rw [artinSlopeList_def, List.mem_flatMap] at ha
  obtain ⟨j, -, hj⟩ := ha
  obtain ⟨hlog, rfl⟩ := List.mem_replicate.1 hj
  rw [embeddingSubgroup_self, sup_bot_eq, sup_bot_eq] at hlog
  have hlt : lowerRamificationGroup K M (((j + 1 : ℕ) : ℤ) + 1) <
      lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) :=
    lt_of_le_of_ne (lowerRamificationGroup_antitone K M (by omega)) fun heq ↦
      hlog (by rw [show ((j + 2 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1 by omega, heq,
        Subgroup.relIndex_self, Nat.log_one_right])
  have hlower : LowerJump K M
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
    (lowerJump_intCast_iff K M (i := ((j + 1 : ℕ) : ℤ))
      (by simpa using Nat.cast_mem_ramificationIndexDomain (j + 1))).2 hlt
  obtain ⟨z, hz⟩ := hasseArf K M ((upperJump_herbrand_iff K M _).2 hlower)
  rw [hz] at ha1 ⊢
  have hz_pos : (0 : ℤ) < z := by exact_mod_cast (by linarith : (0 : ℝ) < z)
  exact ⟨(z + 1).toNat, by omega, by exact_mod_cast (Int.toNat_of_nonneg (by omega) :
    (((z + 1).toNat : ℕ) : ℤ) = z + 1).symm⟩

end TauCeti
