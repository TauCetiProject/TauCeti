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
Galois extension `M/K` with Galois group `G = Gal(M/K)`, and let `H = Gal(M/L)` be the subgroup
of `G` fixing the image of `L` in `M` (`TauCeti.embeddingSubgroup K L M`). Left cosets `G / H`
are in bijection with `K`-embeddings `L →ₐ[K] M`.

For each upper ramification index `u ≥ -1`, the upper ramification group `G^u` acts on `G / H`
with orbit space `G / (G^u H)` of cardinality `[G : G^u H]`
(`TauCeti.embeddingOrbitCount K L M u`). By Herbrand's theorem `(G/N)^u = G^u N / N`, this orbit
count is independent of the choice of finite Galois overfield `M/K`:
* at `u = -1`, `G^{-1} = G` acts transitively and the orbit count is `1`;
* for `u ∈ (-1, 0]`, `G^u = G_0` and the orbit count is the residue degree `f(L/K)`;
* immediately past `0` (where `G^u = G_1` is wild inertia), the orbit count is
  `f(L/K) · ε(L/K)`, where `ε(L/K)` is the tame ramification index;
* for sufficiently large `u`, `G^u = 1` and the orbit count reaches `[L : K]`.

Beyond `G_1`, the chain of subgroups `G_i H` (`i ≥ 1`) refines `G_1 H ≥ H`, whose index
`[G_1 H : H]` equals `p ^ w(L/K)` for `p = ringChar 𝓀[K]` and `w(L/K)` the wild ramification
exponent. Consequently every step index `[G_i H : G_{i+1} H]` (`i ≥ 1`) is a power of `p`, and
listing `φ_{M/K}(i) + 1` with multiplicity `log_p [G_i H : G_{i+1} H]` for
`1 ≤ i ≤ largestLowerJump K M` defines the nondecreasing list of **Artin slopes**
(`TauCeti.artinSlopeList K L M`). Its length is `wildRamificationExponent K L`, its entries are
all strictly greater than `1`, the multiplicity of every real number `a` in the list is read off
the right-hand jump ratio of `embeddingOrbitCount K L M` at `a - 1`, and therefore
`artinSlopeList K L M` is likewise independent of the finite Galois overfield `M`. When `L = M`
and `Gal(M/K)` is abelian, Hasse–Arf implies that every entry of `artinSlopeList K M M` is an
integer at least `2`.

## Main definitions

* `TauCeti.embeddingSubgroup K L M`: the subgroup `H = Gal(M/L)` of `Gal(M/K)` fixing the image
  of `L`.
* `TauCeti.embeddingOrbitCount K L M u`: the orbit count `[G : G^u H]` at upper index `u`.
* `TauCeti.artinSlopeList K L M`: the nondecreasing list of Artin slopes of `L/K` with
  multiplicities.

## Main results

* `TauCeti.embeddingOrbitCount_neg_one`, `TauCeti.embeddingOrbitCount_of_mem_Ioc_zero`,
  `TauCeti.index_lowerRamificationGroup_one_sup_embeddingSubgroup`,
  `TauCeti.embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot`: values of the orbit
  count along the canonical ramification filtration.
* `TauCeti.embeddingOrbitCount_eq`: independence of `embeddingOrbitCount K L M u` from the finite
  Galois overfield `M`.
* `TauCeti.length_artinSlopeList`: `(artinSlopeList K L M).length = wildRamificationExponent K L`.
* `TauCeti.artinSlopeList_eq_nil_iff`: `artinSlopeList K L M = [] ↔ IsTamelyRamified K L`.
* `TauCeti.exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList`: multiplicity
  in `artinSlopeList` as the right-hand `p`-logarithmic jump ratio of `embeddingOrbitCount`.
* `TauCeti.artinSlopeList_eq`: independence of `artinSlopeList K L M` from `M`.
* `TauCeti.exists_nat_eq_of_mem_artinSlopeList_self`: Hasse–Arf integrality of Galois Artin
  slopes in the abelian case.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  in *Représentations des groupes réductifs sur un corps local*, Hermann, 1984, Appendix, §A.6.
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
/-- An automorphism `σ : M ≃ₐ[K] M` belongs to `embeddingSubgroup K L M` if and only if it fixes
every element in the image of `L`. -/
@[simp]
theorem mem_embeddingSubgroup_iff {σ : M ≃ₐ[K] M} :
    σ ∈ embeddingSubgroup K L M ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  rw [embeddingSubgroup_def, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x ↦ h _ ⟨x, rfl⟩, by rintro h _ ⟨x, rfl⟩; exact h x⟩

/-- `embeddingSubgroup K L M` is the image of
`AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)`. No normality or finiteness is needed. -/
theorem range_restrictScalarsHom_eq_embeddingSubgroup :
    (AlgEquiv.restrictScalarsHom (S := L) K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range =
      embeddingSubgroup K L M := by
  ext σ
  rw [MonoidHom.mem_range, mem_embeddingSubgroup_iff]
  refine ⟨?_, fun hσ ↦ ⟨{ σ with commutes' := hσ }, rfl⟩⟩
  rintro ⟨τ, rfl⟩ x
  exact τ.commutes x

/-- For `L = M`, the fixing subgroup of `M` in `Gal(M/K)` is trivial. -/
@[simp]
theorem embeddingSubgroup_self : embeddingSubgroup K M M = ⊥ := by
  ext σ
  simp [AlgEquiv.ext_iff]

/-- For `L = K`, every `K`-automorphism of `M` fixes the image of `K`. -/
@[simp]
theorem embeddingSubgroup_base : embeddingSubgroup K K M = ⊤ := by
  ext σ
  simp

/-- In a tower `M / L / E / K`, the fixing subgroup of `L` is contained in that of `E`. -/
theorem embeddingSubgroup_antitone (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [Algebra E M] [IsScalarTower K E M] [IsScalarTower E L M] :
    embeddingSubgroup K L M ≤ embeddingSubgroup K E M := by
  intro σ hσ
  rw [mem_embeddingSubgroup_iff] at hσ ⊢
  intro x
  rw [IsScalarTower.algebraMap_apply E L M]
  exact hσ (algebraMap E L x)

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
  have hmul := (embeddingSubgroup K L M).index_mul_card
  rw [natCard_embeddingSubgroup K L M, IsGalois.card_aut_eq_finrank K M,
    ← Module.finrank_mul_finrank K L M] at hmul
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos hmul

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
  have hcomm (x : L) :
      algebraMap M M' ((AlgEquiv.restrictNormalHom M σ') (algebraMap L M x)) =
        σ' (algebraMap L M' x) := by
    rw [IsScalarTower.algebraMap_apply L M M']
    exact σ'.restrictNormal_commutes M (algebraMap L M x)
  refine ⟨fun h x ↦ ?_, fun h x ↦ (algebraMap M M').injective ?_⟩
  · rw [← hcomm x, h x, ← IsScalarTower.algebraMap_apply L M M']
  · rw [hcomm x, h x, IsScalarTower.algebraMap_apply L M M']

/-- Transport of `embeddingSubgroup` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem map_autCongr_embeddingSubgroup {M' : Type*} [Field M'] [Algebra K M'] [Algebra L M']
    [IsScalarTower K L M'] (e : M ≃ₐ[L] M') :
    (embeddingSubgroup K L M).map ((e.restrictScalars K).autCongr :
        (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) =
      embeddingSubgroup K L M' := by
  let eK : M ≃ₐ[K] M' := e.restrictScalars K
  ext σ'
  simp only [Subgroup.mem_map, mem_embeddingSubgroup_iff]
  refine ⟨?_, fun h ↦ ⟨eK.autCongr.symm σ', fun x ↦ ?_, eK.autCongr.apply_symm_apply σ'⟩⟩
  · rintro ⟨σ, hσ, rfl⟩ x
    have hx1 : eK.symm (algebraMap L M' x) = algebraMap L M x := e.symm.commutes x
    have hx2 : eK (algebraMap L M x) = algebraMap L M' x := e.commutes x
    change (eK.autCongr σ) (algebraMap L M' x) = algebraMap L M' x
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, hx1, hσ x, hx2]
  · have hx1 : eK (algebraMap L M x) = algebraMap L M' x := e.commutes x
    have hx2 : eK.symm (algebraMap L M' x) = algebraMap L M x := e.symm.commutes x
    rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.trans_apply, AlgEquiv.symm_symm, hx1, h x, hx2]

end EmbeddingSubgroup

namespace LocalFieldsRamification

variable (K M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]

/-- At `J + 1 = (largestLowerJump K M).toNat + 1`, the lower ramification group of `M/K` is
trivial. -/
theorem lowerRamificationGroup_toNat_largestLowerJump_add_one :
    lowerRamificationGroup K M (((largestLowerJump K M).toNat + 1 : ℕ) : ℤ) = ⊥ := by
  apply lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
  have := neg_one_le_largestLowerJump K M
  omega

/-- In a finite Galois local-field extension, the index of the inertia group `G_0` is the
inertia degree. -/
theorem index_lowerRamificationGroup_zero [IsGalois K M] :
    (lowerRamificationGroup K M 0).index = inertiaDegree K M := by
  have hmul := (lowerRamificationGroup K M 0).index_mul_card
  rw [natCard_lowerRamificationGroup_zero K M, IsGalois.card_aut_eq_finrank K M,
    ← ramificationIndex_mul_inertiaDegree (K := K) (L := M), mul_comm _ (inertiaDegree K M)] at hmul
  exact Nat.eq_of_mul_eq_mul_right ramificationIndex_pos hmul

/-- In a finite Galois local-field extension, the index of wild inertia `G_1` is
`inertiaDegree K M * tameRamificationIndex K M`. -/
theorem index_lowerRamificationGroup_one [IsGalois K M] :
    (lowerRamificationGroup K M 1).index = inertiaDegree K M * tameRamificationIndex K M := by
  have hle : lowerRamificationGroup K M 1 ≤ lowerRamificationGroup K M 0 :=
    lowerRamificationGroup_antitone K M (by omega)
  rw [← Subgroup.relIndex_mul_index hle, relIndex_lowerRamificationGroup_one_zero K M,
    index_lowerRamificationGroup_zero K M, mul_comm]

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
  have hcard : Nat.card (M ≃ₐ[K] M) ≠ 0 := by
    rw [IsGalois.card_aut_eq_finrank K M]
    exact Module.finrank_pos.ne'
  have : Finite (M ≃ₐ[K] M) := Nat.finite_of_card_ne_zero hcard
  exact Subgroup.index_pos

/-- The orbit count is nondecreasing in the upper index `u`, because the upper ramification
filtration is antitone. -/
theorem embeddingOrbitCount_mono : Monotone (embeddingOrbitCount K L M) := by
  intro u v huv
  exact Subgroup.index_antitone (sup_le_sup_right (upperRamificationGroup_antitone K M huv) _)

/-- The orbit count never exceeds `[L : K]`. -/
theorem embeddingOrbitCount_le_finrank (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u ≤ Module.finrank K L := by
  rw [← index_embeddingSubgroup K L M]
  exact Subgroup.index_antitone le_sup_right

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
  have htop : upperRamificationGroup K M ⟨-1, le_rfl⟩ = ⊤ := by
    rw [upperRamificationGroup_of_coe_le_zero K M (by norm_num)]
    have h1 := lowerRamificationGroupReal_intCast K M (-1)
    simp only [Int.cast_neg, Int.cast_one] at h1
    rw [h1]
    exact lowerRamificationGroup_eq_top_of_le_neg_one K M le_rfl
  rw [embeddingOrbitCount_def, htop, top_sup_eq, Subgroup.index_top]

/-- Beyond `φ_{M/K}(N - 1)` where `G_N = ⊥`, the upper ramification group `G^u` is trivial and the
orbit count reaches `[L : K]`. -/
theorem embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot {N : ℕ}
    (hN : lowerRamificationGroup K M N = ⊥) {u : RamificationIndexDomain}
    (hu : (match N with
      | 0 => (-1 : ℝ)
      | m + 1 => (herbrand K M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩ : ℝ)) < (u : ℝ)) :
    embeddingOrbitCount K L M u = Module.finrank K L := by
  have hbot : upperRamificationGroup K M u = ⊥ := by
    rw [upperRamificationGroup_def, lowerRamificationGroupReal_def, ← le_bot_iff, ← hN]
    apply lowerRamificationGroup_antitone K M
    cases N with
    | zero =>
      have hneg : (⟨-1, le_rfl⟩ : RamificationIndexDomain) < u := Subtype.mk_lt_mk.2 hu
      have hψ := inverseHerbrand_strictMono K M hneg
      rw [inverseHerbrand_of_coe_le_zero K M (by norm_num)] at hψ
      exact Int.lt_ceil.2 (by exact_mod_cast Subtype.mk_lt_mk.1 hψ)
    | succ m =>
      have hm : herbrand K M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩ < u :=
        Subtype.mk_lt_mk.2 hu
      have hψ := inverseHerbrand_strictMono K M hm
      rw [inverseHerbrand_herbrand] at hψ
      exact Int.lt_ceil.2 (by exact_mod_cast Subtype.mk_lt_mk.1 hψ)
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
  have hker : π.ker ≤ embeddingSubgroup K L M' := by
    rw [← comap_restrictNormalHom_embeddingSubgroup K L M M']
    exact Subgroup.comap_mono bot_le
  have hcomap : (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).comap π =
      upperRamificationGroup K M' u ⊔ embeddingSubgroup K L M' := by
    have hmap : (upperRamificationGroup K M' u ⊔ embeddingSubgroup K L M').map π =
        upperRamificationGroup K M u ⊔ embeddingSubgroup K L M := by
      rw [Subgroup.map_sup, map_restrictNormalHom_upperRamificationGroup K M M' u,
        ← comap_restrictNormalHom_embeddingSubgroup K L M M',
        Subgroup.map_comap_eq_self_of_surjective hsurj]
    rw [← hmap, Subgroup.comap_map_eq_self (hker.trans le_sup_right)]
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def, ← hcomap,
    Subgroup.index_comap_of_surjective _ hsurj]

/-- Transport of `embeddingOrbitCount` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem embeddingOrbitCount_eq_of_algEquiv {M' : Type*}
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L M'] [IsScalarTower K L M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (e : M ≃ₐ[L] M') (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L M' u := by
  let eK : M ≃ₐ[K] M' := e.restrictScalars K
  have hupper : (upperRamificationGroup K M u).map (eK.autCongr :
      (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) = upperRamificationGroup K M' u := by
    rw [upperRamificationGroup_def, upperRamificationGroup_def]
    have hψ : inverseHerbrand K M u = inverseHerbrand K M' u := by
      apply (herbrand_strictMono K M').injective
      rw [herbrand_inverseHerbrand, ← herbrand_eq_of_algEquiv eK, herbrand_inverseHerbrand]
    rw [hψ, lowerRamificationGroupReal_def, lowerRamificationGroupReal_def,
      map_autCongr_lowerRamificationGroup eK]
  have hsup : (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).map
      (eK.autCongr : (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) =
        upperRamificationGroup K M' u ⊔ embeddingSubgroup K L M' := by
    rw [Subgroup.map_sup, hupper, map_autCongr_embeddingSubgroup K L M e]
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def, ← hsup]
  exact (Subgroup.index_map_equiv _ eK.autCongr).symm

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
  let e₁K : M ≃ₐ[K] F₁ := AlgEquiv.ofInjectiveField (ι₁.restrictScalars K)
  let e₂K : M₂ ≃ₐ[K] F₂ := AlgEquiv.ofInjectiveField (ι₂.restrictScalars K)
  have : Module.Finite K F₁ := Module.Finite.equiv e₁K.toLinearEquiv
  have : Module.Finite K F₂ := Module.Finite.equiv e₂K.toLinearEquiv
  have : IsGalois K F₁ := IsGalois.of_algEquiv e₁K
  have : IsGalois K F₂ := IsGalois.of_algEquiv e₂K
  have : Module.Finite K N := IntermediateField.finiteDimensional_sup F₁ F₂
  have : IsGalois K N := inferInstance
  let _ := finiteIntermediateFieldValuativeRel K Ω F₁
  let _ := finiteIntermediateFieldTopology K Ω F₁
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω F₁
  have := finiteIntermediateField_valuativeExtension K Ω F₁
  let _ := finiteIntermediateFieldValuativeRel K Ω F₂
  let _ := finiteIntermediateFieldTopology K Ω F₂
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω F₂
  have := finiteIntermediateField_valuativeExtension K Ω F₂
  let _ := finiteIntermediateFieldValuativeRel K Ω N
  let _ := finiteIntermediateFieldTopology K Ω N
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω N
  have := finiteIntermediateField_valuativeExtension K Ω N
  let _ : Algebra L F₁ := ((e₁K : M →+* F₁).comp (algebraMap L M)).toAlgebra
  have : IsScalarTower K L F₁ := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply K L M]
    exact (e₁K.commutes x).symm
  let e₁ : M ≃ₐ[L] F₁ := { e₁K with commutes' := fun _ ↦ rfl }
  let _ : Algebra L F₂ := ((e₂K : M₂ →+* F₂).comp (algebraMap L M₂)).toAlgebra
  have : IsScalarTower K L F₂ := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply K L M₂]
    exact (e₂K.commutes x).symm
  let e₂ : M₂ ≃ₐ[L] F₂ := { e₂K with commutes' := fun _ ↦ rfl }
  let j₁ : F₁ →ₐ[K] N := IntermediateField.inclusion le_sup_left
  let j₂ : F₂ →ₐ[K] N := IntermediateField.inclusion le_sup_right
  let _ : Algebra F₁ N := j₁.toRingHom.toAlgebra
  let _ : Algebra F₂ N := j₂.toRingHom.toAlgebra
  have : IsScalarTower K F₁ N := IsScalarTower.of_algebraMap_eq fun x ↦ (j₁.commutes x).symm
  have : IsScalarTower K F₂ N := IsScalarTower.of_algebraMap_eq fun x ↦ (j₂.commutes x).symm
  let _ : Algebra L N := ((algebraMap L Ω).codRestrict N.toSubring fun x ↦ by
    refine le_sup_left (a := F₁) (b := F₂) ⟨algebraMap L M x, ?_⟩
    exact ι₁.commutes x).toAlgebra
  have hLN₁ : ∀ x : L, j₁ (algebraMap L F₁ x) = algebraMap L N x := fun x ↦ by
    apply Subtype.ext
    exact ι₁.commutes x
  have hLN₂ : ∀ x : L, j₂ (algebraMap L F₂ x) = algebraMap L N x := fun x ↦ by
    apply Subtype.ext
    exact ι₂.commutes x
  have : IsScalarTower L F₁ N := IsScalarTower.of_algebraMap_eq fun x ↦ (hLN₁ x).symm
  have : IsScalarTower L F₂ N := IsScalarTower.of_algebraMap_eq fun x ↦ (hLN₂ x).symm
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [← hLN₁ (algebraMap K L x), ← IsScalarTower.algebraMap_apply K L F₁, j₁.commutes]
  rw [embeddingOrbitCount_eq_of_algEquiv K L M e₁ u,
    ← embeddingOrbitCount_tower_eq K L F₁ N u,
    embeddingOrbitCount_tower_eq K L F₂ N u,
    ← embeddingOrbitCount_eq_of_algEquiv K L M₂ e₂ u]

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
  have hf : Function.Injective f := AlgEquiv.restrictScalarsHom_injective K
  rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L i,
    ← range_restrictScalarsHom_eq_embeddingSubgroup K L M, Subgroup.relIndex]
  let e : (M ≃ₐ[L] M) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun a b hab ↦ hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩
  have hcomap : ((lowerRamificationGroup K M i).comap f).map (e : (M ≃ₐ[L] M) →* f.range) =
      (lowerRamificationGroup K M i).subgroupOf f.range := by
    ext ⟨σ, hσ⟩
    obtain ⟨τ, rfl⟩ := hσ
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine ⟨?_, fun h ↦ ⟨τ, h, rfl⟩⟩
    rintro ⟨τ', hτ', h_eq⟩
    have : τ' = τ := hf (congrArg Subtype.val h_eq)
    rwa [← this]
  rw [← hcomap]
  exact Subgroup.index_map_equiv _ e

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
  have hG : upperRamificationGroup K M u = lowerRamificationGroup K M 0 := by
    rw [upperRamificationGroup_of_coe_le_zero K M hu₂]
    exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := 0)
      (by simpa using hu₁) (by simpa using hu₂)
  rw [embeddingOrbitCount_def, hG, index_lowerRamificationGroup_zero_sup_embeddingSubgroup]

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
  have hpos : 0 < inertiaDegree L M * tameRamificationIndex L M :=
    Nat.mul_pos inertiaDegree_pos (tameRamificationIndex_pos L M)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
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
  have hpos : 0 < inertiaDegree K L * tameRamificationIndex K L :=
    Nat.mul_pos inertiaDegree_pos (tameRamificationIndex_pos K L)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  linear_combination hmul

end OrbitCount

/-! ### The Artin slope list -/

section ArtinSlopeList

private theorem list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

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
      ((herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1)

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
  have h0 : (herbrand K M ⟨0, by norm_num⟩ : ℝ) = 0 := by
    rw [herbrand_of_coe_le_zero K M le_rfl]
  have hpos : (0 : ℝ) <
      herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ := by
    rw [← h0]
    exact Subtype.mk_lt_mk.1 (herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by positivity)))
  linarith

/-- `artinSlopeList K L M` is sorted in nondecreasing order. -/
theorem pairwise_le_artinSlopeList :
    (artinSlopeList K L M).Pairwise (· ≤ ·) := by
  rw [artinSlopeList_def]
  set J := (largestLowerJump K M).toNat
  let d : ℕ → ℕ := fun j ↦
    Nat.log (ringChar 𝓀[K])
      ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M))
  let val : ℕ → ℝ := fun j ↦
    (herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1
  have hmono : StrictMono val := fun i j hij ↦ by
    have hlt : (⟨((i + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ :
        RamificationIndexDomain) <
          ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
      Subtype.mk_lt_mk.2 (by exact_mod_cast Nat.add_lt_add_right hij 1)
    have := Subtype.mk_lt_mk.1 (herbrand_strictMono K M hlt)
    dsimp [val]
    linarith
  change ((List.range J).flatMap fun j ↦ List.replicate (d j) (val j)).Pairwise (· ≤ ·)
  rw [List.pairwise_flatMap]
  refine ⟨fun j _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  refine List.Pairwise.imp (R := (· < ·)) (fun {i j} hij a ha b hb ↦ ?_) List.pairwise_lt_range
  rw [(List.mem_replicate.1 ha).2, (List.mem_replicate.1 hb).2]
  exact (hmono hij).le

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
  set p := ringChar 𝓀[K]
  set J := (largestLowerJump K M).toNat
  set H := embeddingSubgroup K L M
  let d : ℕ → ℕ := fun j ↦
    Nat.log p
      ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H))
  let val : ℕ → ℝ := fun j ↦
    (herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1
  have hval_inj : Function.Injective val := fun i j hij ↦ by
    have hφ : herbrand K M ⟨((i + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ =
        herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
      Subtype.ext (by dsimp [val] at hij; linarith)
    have := (herbrand_strictMono K M).injective hφ
    have hcast : ((i + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) := congrArg Subtype.val this
    exact Nat.add_right_cancel (Nat.cast_injective hcast)
  have hcount_eq (h_match : ∀ j < J, val j ≠ a) : (artinSlopeList K L M).count a = 0 := by
    rw [List.count_eq_zero, artinSlopeList_def, List.mem_flatMap]
    rintro ⟨j, hj, hmem⟩
    exact h_match j (List.mem_range.1 hj) (List.mem_replicate.1 hmem).2.symm
  set x := inverseHerbrand K M u with hx_def
  have hx_pos : (0 : ℝ) < x := by
    have h0 : inverseHerbrand K M ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
      inverseHerbrand_of_coe_le_zero K M le_rfl
    have hlt : (⟨0, by norm_num⟩ : RamificationIndexDomain) < u :=
      Subtype.mk_lt_mk.2 (by exact sub_pos.2 ha)
    have hψ := inverseHerbrand_strictMono K M hlt
    rw [h0, ← hx_def] at hψ
    exact Subtype.mk_lt_mk.1 hψ
  by_cases hint : ∃ j : ℕ, (x : ℝ) = ((j + 1 : ℕ) : ℝ)
  · obtain ⟨j, hj⟩ := hint
    have hx_eq : x = ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
      Subtype.ext hj
    have ha_eq : val j = a := by
      have hu_φ : herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ =
          u := by
        rw [← hx_eq, hx_def]
        exact herbrand_inverseHerbrand K M u
      have := congrArg Subtype.val hu_φ
      dsimp [val, u] at this ⊢
      linarith
    let w := herbrand K M ⟨((j + 2 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 2)⟩
    have huw : u < w := by
      rw [← herbrand_inverseHerbrand K M u, ← hx_def, hx_eq]
      exact herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by push_cast; linarith))
    refine ⟨w, huw, fun v huv hvw ↦ ?_⟩
    have hGu : upperRamificationGroup K M u = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def, ← hx_def, hx_eq]
      simpa using lowerRamificationGroupReal_intCast K M ((j + 1 : ℕ) : ℤ)
    have hGv : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def]
      apply lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((j + 2 : ℕ) : ℤ))
      · have hlt : (x : ℝ) < (inverseHerbrand K M v : ℝ) :=
          Subtype.mk_lt_mk.1 (hx_def ▸ inverseHerbrand_strictMono K M huv)
        rw [hj] at hlt
        push_cast at hlt ⊢
        linarith
      · have hle : (inverseHerbrand K M v : ℝ) ≤ (inverseHerbrand K M w : ℝ) :=
          Subtype.mk_le_mk.1 ((inverseHerbrand_strictMono K M).monotone hvw)
        rw [show w = herbrand K M _ from rfl, inverseHerbrand_herbrand] at hle
        exact_mod_cast hle
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
      have hmap : ((List.range J).map fun k ↦
          (List.replicate (d k) (val k)).count a).sum = d j := by
        rw [list_sum_map_range, Finset.sum_eq_single j]
        · simp [ha_eq]
        · intro k _ hkj
          have hne : val k ≠ a := fun hka ↦ hkj (hval_inj (hka.trans ha_eq.symm))
          simp [List.count_replicate, hne]
        · intro hj_not
          exact absurd (Finset.mem_range.2 hjJ) hj_not
      exact hmap.symm
    · have hbot₁ : lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) = ⊥ :=
        lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
          (by have := neg_one_le_largestLowerJump K M; omega)
      have hbot₂ : lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) = ⊥ :=
        lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
          (by have := neg_one_le_largestLowerJump K M; omega)
      rw [hbot₁, hbot₂, Subgroup.relIndex_self, Nat.log_one_right,
        hcount_eq fun k hk hka ↦ hjJ (hval_inj (hka.trans ha_eq.symm) ▸ hk)]
  · push Not at hint
    have hceil_pos : (0 : ℤ) < ⌈(x : ℝ)⌉ := Int.lt_ceil.2 (by simpa using hx_pos)
    obtain ⟨j, hj_ceil⟩ : ∃ j : ℕ, ⌈(x : ℝ)⌉ = ((j + 1 : ℕ) : ℤ) :=
      ⟨(⌈(x : ℝ)⌉ - 1).toNat, by omega⟩
    have hxj₁ : (j : ℝ) < x := by
      have h1 : (((j + 1 : ℕ) : ℤ) : ℝ) - 1 < x := by
        rw [← hj_ceil]
        exact sub_lt_iff_lt_add.2 (Int.ceil_lt_add_one (x : ℝ))
      push_cast at h1
      linarith
    have hxj₂ : (x : ℝ) < ((j + 1 : ℕ) : ℝ) := by
      have hle : (x : ℝ) ≤ (((j + 1 : ℕ) : ℤ) : ℝ) := hj_ceil ▸ Int.le_ceil (x : ℝ)
      exact lt_of_le_of_ne (by simpa using hle) (hint j)
    let w := herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩
    have huw : u < w := by
      rw [← herbrand_inverseHerbrand K M u, ← hx_def]
      exact herbrand_strictMono K M (Subtype.mk_lt_mk.2 hxj₂)
    refine ⟨w, huw, fun v huv hvw ↦ ?_⟩
    have hGu : upperRamificationGroup K M u = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def, ← hx_def]
      exact lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((j + 1 : ℕ) : ℤ))
        (by push_cast; linarith) (by exact_mod_cast hxj₂.le)
    have hGv : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def]
      apply lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := ((j + 1 : ℕ) : ℤ))
      · have hlt : (x : ℝ) < (inverseHerbrand K M v : ℝ) :=
          Subtype.mk_lt_mk.1 (hx_def ▸ inverseHerbrand_strictMono K M huv)
        push_cast
        linarith
      · have hle : (inverseHerbrand K M v : ℝ) ≤ (inverseHerbrand K M w : ℝ) :=
          Subtype.mk_le_mk.1 ((inverseHerbrand_strictMono K M).monotone hvw)
        rw [show w = herbrand K M _ from rfl, inverseHerbrand_herbrand] at hle
        exact_mod_cast hle
    have heq_occ : embeddingOrbitCount K L M v = embeddingOrbitCount K L M u := by
      rw [embeddingOrbitCount_def, embeddingOrbitCount_def, hGv, hGu]
    rw [heq_occ, Nat.div_self (embeddingOrbitCount_pos K L M u), Nat.log_one_right,
      hcount_eq fun k _ hka ↦ ?_]
    have hu_φ : herbrand K M ⟨((k + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (k + 1)⟩ =
        u := Subtype.ext (by dsimp [val, u] at hka ⊢; linarith)
    have hxk : x = ⟨((k + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (k + 1)⟩ := by
      rw [hx_def, ← hu_φ, inverseHerbrand_herbrand]
    exact hint k (congrArg Subtype.val hxk)

/-- **Independence of `artinSlopeList` from the finite Galois overfield.** For any two finite
Galois extensions `M/K` and `M₂/K` containing `L`, `artinSlopeList K L M = artinSlopeList K L M₂`.
-/
theorem artinSlopeList_eq (M₂ : Type*)
    [Field M₂] [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [Algebra K M₂] [Algebra L M₂] [IsScalarTower K L M₂]
    [ValuativeExtension K M₂] [Module.Finite K M₂] [IsGalois K M₂] :
    artinSlopeList K L M = artinSlopeList K L M₂ := by
  refine List.Perm.eq_of_pairwise'
    (pairwise_le_artinSlopeList K L M) (pairwise_le_artinSlopeList K L M₂) ?_
  rw [List.perm_iff_count]
  intro a
  by_cases ha : 1 < a
  · obtain ⟨w₁, huw₁, hw₁⟩ :=
      exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L M ha
    obtain ⟨w₂, huw₂, hw₂⟩ :=
      exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L M₂ ha
    let v := min w₁ w₂
    have huv : (⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ : RamificationIndexDomain) < v :=
      lt_min huw₁ huw₂
    rw [← hw₁ v huv (min_le_left _ _), ← hw₂ v huv (min_le_right _ _),
      embeddingOrbitCount_eq K L M M₂ v,
      embeddingOrbitCount_eq K L M M₂ ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩]
  · have hc₁ : (artinSlopeList K L M).count a = 0 :=
      List.count_eq_zero.2 fun hmem ↦ ha (one_lt_of_mem_artinSlopeList K L M hmem)
    have hc₂ : (artinSlopeList K L M₂).count a = 0 :=
      List.count_eq_zero.2 fun hmem ↦ ha (one_lt_of_mem_artinSlopeList K L M₂ hmem)
    rw [hc₁, hc₂]

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

/-- Every step index `[G_{i+1} H : G_{i+2} H]` (`i ≥ 0`) divides `p ^ wildRamificationExponent K L`,
and therefore equals `p ^ log_p [G_{i+1} H : G_{i+2} H]`. -/
theorem pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup (j : ℕ) :
    ringChar 𝓀[K] ^
        Nat.log (ringChar 𝓀[K])
          ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
            (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) =
      (lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  set H := embeddingSubgroup K L M
  set K₂ := lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H
  set K₁ := lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H
  set K₀ := lowerRamificationGroup K M 1 ⊔ H
  have hH₂ : H ≤ K₂ := le_sup_right
  have h₂₁ : K₂ ≤ K₁ := sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have h₁₀ : K₁ ≤ K₀ := sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have hdvd : K₂.relIndex K₁ ∣ p ^ wildRamificationExponent K L := by
    rw [← relIndex_embeddingSubgroup_lowerRamificationGroup_one K L M,
      ← Subgroup.relIndex_mul_relIndex H K₁ K₀ (hH₂.trans h₂₁) h₁₀,
      ← Subgroup.relIndex_mul_relIndex H K₂ K₁ hH₂ h₂₁]
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
  have hAJ : A (largestLowerJump K M).toNat = H := by
    simp only [A, lowerRamificationGroup_toNat_largestLowerJump_add_one K M, bot_sup_eq]
  have hA0 : A 0 = lowerRamificationGroup K M 1 ⊔ H := by simp [A]
  rw [hAJ, hA0, relIndex_embeddingSubgroup_lowerRamificationGroup_one K L M]

/-- The number of Artin slopes (counted with multiplicity) equals the wild ramification exponent
`w(L/K) = v_p(e(L/K))`. -/
@[simp]
theorem length_artinSlopeList :
    (artinSlopeList K L M).length = wildRamificationExponent K L := by
  let p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  let d : ℕ → ℕ := fun j ↦
    Nat.log p
      ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M))
  have hlen : (artinSlopeList K L M).length =
      ∑ j ∈ Finset.range (largestLowerJump K M).toNat, d j := by
    rw [artinSlopeList_def, List.length_flatMap]
    simpa [d] using list_sum_map_range (largestLowerJump K M).toNat d
  rw [hlen]
  apply Nat.pow_right_injective hp.two_le
  have hpow : p ^ ∑ j ∈ Finset.range (largestLowerJump K M).toNat, d j =
      ∏ j ∈ Finset.range (largestLowerJump K M).toNat, p ^ d j :=
    (Finset.prod_pow_eq_pow_sum _ _ _).symm
  refine hpow.trans ?_
  dsimp only [p]
  rw [← prod_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M]
  exact Finset.prod_congr rfl fun j _ ↦
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
  have hrel_ne : (lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ)).relIndex
      (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ)) ≠ 1 := by
    intro h1
    rw [h1, Nat.log_one_right] at hlog
    exact hlog rfl
  have hlt : lowerRamificationGroup K M (((j + 1 : ℕ) : ℤ) + 1) <
      lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
    refine lt_of_le_of_ne (lowerRamificationGroup_antitone K M (by omega)) fun heq ↦ hrel_ne ?_
    have hidx : ((j + 2 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1 := by omega
    rw [hidx, heq, Subgroup.relIndex_self]
  have hlower : LowerJump K M
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
    (lowerJump_intCast_iff K M (i := ((j + 1 : ℕ) : ℤ))
      (by simpa using Nat.cast_mem_ramificationIndexDomain (j + 1))).2 hlt
  obtain ⟨z, hz⟩ := hasseArf K M ((upperJump_herbrand_iff K M _).2 hlower)
  rw [hz] at ha1 ⊢
  have hz1 : 1 ≤ z := by
    have : (0 : ℝ) < z := by linarith
    have : (0 : ℤ) < z := by exact_mod_cast this
    omega
  refine ⟨(z + 1).toNat, by omega, ?_⟩
  have hcast : (((z + 1).toNat : ℕ) : ℤ) = z + 1 := Int.toNat_of_nonneg (by omega)
  exact_mod_cast hcast.symm

end TauCeti
