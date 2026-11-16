/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import TauCeti.FieldTheory.Galois.Restriction
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

Let `L/K` be a finite separable extension of nonarchimedean local fields in a finite Galois
extension `M/K`, with `G = Gal(M/K)` and `H = embeddingSubgroup K L M`. For `u ≥ -1`,
`TauCeti.embeddingOrbitCount K L M u = [G : G^u H]` counts the `G^u`-orbits on `L →ₐ[K] M` and is
independent of `M`. Listing `φ_{M/K}(i) + 1` with multiplicity `log_p [G_i H : G_{i+1} H]` (`i ≥ 1`)
yields `TauCeti.artinSlopeList K L M`.

## Main definitions

* `TauCeti.embeddingOrbitCount`, `TauCeti.artinSlopeList`.

## Main results

* `TauCeti.embeddingOrbitCount_eq`, `TauCeti.embeddingOrbitCount_eq_of_algEquiv_left`,
  `TauCeti.artinSlopeList_eq`, `TauCeti.artinSlopeList_eq_of_algEquiv`: overfield independence and
  `L ≃ₐ[K] L'` invariance.
* `TauCeti.count_artinSlopeList_herbrand_add_one`,
  `TauCeti.exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList`,
  `TauCeti.mem_artinSlopeList_iff`, `TauCeti.mem_artinSlopeList_self_iff`: multiplicity and
  membership characterizations.
* `TauCeti.index_lowerRamificationGroup_succ_sup_embeddingSubgroup`,
  `TauCeti.length_artinSlopeList`, `TauCeti.artinSlopeList_eq_nil_iff`,
  `TauCeti.exists_nat_eq_of_mem_artinSlopeList_self`: wild indices, length `w(L/K)`, tameness, and
  Hasse–Arf integrality.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3, and Chapter V, §7.
* P. Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
  in *Représentations des groupes réductifs sur un corps local*, Hermann, 1984, Appendix, §A.6.
* J. W. Jones and D. P. Roberts, *A database of local fields*, J. Symbolic Comput. 41 (2006),
  80–97 (arXiv:math/0309309), §§3–4.
* The LMFDB Collaboration, *The L-functions and modular forms database*, local-field knowls
  `lf.slopes` and `lf.slope_content`.
-/

public section
noncomputable section

open IntermediateField ValuativeRel IsLocalRing TauCeti.LocalFieldsRamification

namespace TauCeti

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
      (upperRamificationGroup K M u ⊔ embeddingSubgroup K L M).index := (rfl)

/-- The orbit count is positive at every upper ramification index. -/
theorem embeddingOrbitCount_pos (u : RamificationIndexDomain) :
    0 < embeddingOrbitCount K L M u :=
  have := Nat.finite_of_card_ne_zero (IsGalois.card_aut_eq_finrank K M ▸ Module.finrank_pos.ne')
  Subgroup.index_pos

/-- For `u ≤ v`, the orbit count at `u` divides the orbit count at `v`. -/
theorem embeddingOrbitCount_dvd_of_le {u v : RamificationIndexDomain} (h : u ≤ v) :
    embeddingOrbitCount K L M u ∣ embeddingOrbitCount K L M v :=
  Subgroup.index_dvd_of_le (sup_le_sup_right (upperRamificationGroup_antitone K M h) _)

/-- The orbit count is nondecreasing in the upper index `u`. -/
theorem embeddingOrbitCount_mono : Monotone (embeddingOrbitCount K L M) := fun _ _ h ↦
  Subgroup.index_antitone (sup_le_sup_right (upperRamificationGroup_antitone K M h) _)

/-- In a tower `M / L / E / K`, the orbit count for `E` is at most that for `L`. -/
theorem embeddingOrbitCount_le_of_tower (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [Algebra E M] [IsScalarTower K E M] [IsScalarTower E L M] (u : RamificationIndexDomain) :
    embeddingOrbitCount K E M u ≤ embeddingOrbitCount K L M u :=
  Subgroup.index_antitone (sup_le_sup_left (embeddingSubgroup_antitone K L M E) _)

/-- The orbit count never exceeds `[L : K]`. -/
theorem embeddingOrbitCount_le_finrank (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u ≤ Module.finrank K L := by
  rw [← index_embeddingSubgroup K L M]; exact Subgroup.index_antitone le_sup_right

/-- For `L = M`, the orbit count is the index of `G^u` in `Gal(M/K)`. -/
@[simp]
theorem embeddingOrbitCount_self_right (u : RamificationIndexDomain) :
    embeddingOrbitCount K M M u = (upperRamificationGroup K M u).index := by
  simp [embeddingOrbitCount_def]

/-- For `L = K`, the orbit count is identically `1`. -/
@[simp]
theorem embeddingOrbitCount_self_left (u : RamificationIndexDomain) :
    embeddingOrbitCount K K M u = 1 := by simp [embeddingOrbitCount_def]

/-- At `u = -1`, `G^{-1} = Gal(M/K)`, so the orbit count is `1`. -/
@[simp]
theorem embeddingOrbitCount_neg_one : embeddingOrbitCount K L M ⟨-1, le_rfl⟩ = 1 := by
  have h1 := lowerRamificationGroupReal_intCast K M (-1)
  simp only [Int.cast_neg, Int.cast_one] at h1
  rw [embeddingOrbitCount_def, upperRamificationGroup_of_coe_le_zero K M (by norm_num), h1,
    lowerRamificationGroup_eq_top_of_le_neg_one K M le_rfl, top_sup_eq, Subgroup.index_top]

/-- At `φ_{M/K}(u)`, the orbit count equals `[G : G_u H]`. -/
@[simp]
theorem embeddingOrbitCount_herbrand (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M (herbrand K M u) =
      (lowerRamificationGroupReal K M u ⊔ embeddingSubgroup K L M).index := by
  rw [embeddingOrbitCount_def, upperRamificationGroup_herbrand]

/-- The orbit count reaches `[L : K]` if and only if `G^u ≤ H`. -/
theorem embeddingOrbitCount_eq_finrank_iff (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = Module.finrank K L ↔
      upperRamificationGroup K M u ≤ embeddingSubgroup K L M := by
  have : Module.Finite K L := .left K L M
  rw [embeddingOrbitCount_def, ← index_embeddingSubgroup K L M]
  refine ⟨fun h ↦ le_sup_left.trans <| Subgroup.relIndex_eq_one.1 <|
    Nat.eq_of_mul_eq_mul_right (index_embeddingSubgroup K L M ▸ Module.finrank_pos)
      (h ▸ Subgroup.relIndex_mul_index (le_sup_right : embeddingSubgroup K L M ≤ _)
        |>.trans (one_mul _).symm), fun h ↦ by rw [sup_eq_right.2 h]⟩

/-- Beyond `φ_{M/K}(N - 1)` where `G_N = ⊥`, the upper ramification group `G^u` is trivial and
the orbit count reaches `[L : K]`. -/
theorem embeddingOrbitCount_eq_finrank_of_lowerRamificationGroup_eq_bot {N : ℕ}
    (hN : lowerRamificationGroup K M N = ⊥) {u : RamificationIndexDomain}
    (hu : herbrand K M ⟨(N : ℝ) - 1, Set.mem_Ici.2 (by linarith [Nat.cast_nonneg (α := ℝ) N])⟩ <
      u) :
    embeddingOrbitCount K L M u = Module.finrank K L := by
  rw [embeddingOrbitCount_eq_finrank_iff, upperRamificationGroup_def,
    lowerRamificationGroupReal_def]
  have hψ := inverseHerbrand_herbrand K M _ ▸ inverseHerbrand_strictMono K M hu
  have hceil : (N : ℤ) - 1 < ⌈(inverseHerbrand K M u : ℝ)⌉ :=
    Int.lt_ceil.2 (by simpa using Subtype.coe_lt_coe.2 hψ)
  exact ((lowerRamificationGroup_antitone K M (by omega)).trans hN.le).trans bot_le

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
  have : Algebra.IsAlgebraic K M' := .of_finite K M'
  have : Algebra.IsAlgebraic K M := .of_finite K M
  have : ValuativeExtension M M' := .of_isScalarTower (K := K)
  have : Module.Finite M M' := .of_restrictScalars_finite K M M'
  let π : (M' ≃ₐ[K] M') →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hsurj : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective M'
  have hker : π.ker ≤ embeddingSubgroup K L M' :=
    comap_restrictNormalHom_embeddingSubgroup K L M M' ▸ Subgroup.comap_mono bot_le
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def,
    ← Subgroup.index_comap_of_surjective _ hsurj]
  congr 1
  rw [← Subgroup.comap_map_eq_self (hker.trans le_sup_right), Subgroup.map_sup,
    map_restrictNormalHom_upperRamificationGroup K M M' u,
    ← comap_restrictNormalHom_embeddingSubgroup K L M M',
    Subgroup.map_comap_eq_self_of_surjective hsurj]

/-- Transport of `embeddingOrbitCount` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem embeddingOrbitCount_eq_of_algEquiv {M' : Type*}
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L M'] [IsScalarTower K L M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (e : M ≃ₐ[L] M') (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L M' u := by
  let eK : M ≃ₐ[K] M' := e.restrictScalars K
  rw [embeddingOrbitCount_def, embeddingOrbitCount_def, ← map_autCongr_upperRamificationGroup eK u,
    ← map_autCongr_embeddingSubgroup K L M e, ← Subgroup.map_sup]
  exact (Subgroup.index_map_equiv _ eK.autCongr).symm

/-- Helper comparing `embeddingOrbitCount K L M u` against a finite Galois intermediate field `N`
of `AlgebraicClosure L` containing the image of `M`. -/
private theorem embeddingOrbitCount_eq_intermediateField
    {N : IntermediateField K (AlgebraicClosure L)} [Module.Finite K N] [IsGalois K N]
    [ValuativeRel N] [TopologicalSpace N] [IsNonarchimedeanLocalField N]
    [ValuativeExtension K N] [Algebra L N] [IsScalarTower K L N]
    (hLN : ∀ x : L, ((algebraMap L N x : N) : AlgebraicClosure L) = algebraMap L _ x)
    (ι : M →ₐ[L] AlgebraicClosure L) (hFN : (ι.restrictScalars K).fieldRange ≤ N)
    (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L N u := by
  let Ω := AlgebraicClosure L; let F : IntermediateField K Ω := (ι.restrictScalars K).fieldRange
  let eK : M ≃ₐ[K] F := AlgEquiv.ofInjectiveField (ι.restrictScalars K)
  have : Module.Finite K F := .equiv eK.toLinearEquiv; have : IsGalois K F := .of_algEquiv eK
  let _ := finiteIntermediateFieldValuativeRel K Ω F
  let _ := finiteIntermediateFieldTopology K Ω F
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω F
  have := finiteIntermediateField_valuativeExtension K Ω F
  let _ : Algebra L F := ((eK : M →+* F).comp (algebraMap L M)).toAlgebra
  have : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply K L M]
    exact (eK.commutes x).symm
  let _ : Algebra F N := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  have : IsScalarTower K F N := IsScalarTower.of_algebraMap_eq fun x ↦
    ((IntermediateField.inclusion hFN).commutes x).symm
  have : IsScalarTower L F N := IsScalarTower.of_algebraMap_eq fun x ↦
    Subtype.ext ((hLN x).trans (ι.commutes x).symm)
  rw [embeddingOrbitCount_eq_of_algEquiv K L M ({ eK with commutes' := fun _ ↦ rfl }) u,
    ← embeddingOrbitCount_tower_eq K L F N u]

/-- **Independence of the finite Galois overfield.** For any two finite Galois extensions `M/K`
and `M₂/K` of nonarchimedean local fields containing `L`, the orbit counts agree. -/
theorem embeddingOrbitCount_eq (M₂ : Type*)
    [Field M₂] [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [Algebra K M₂] [Algebra L M₂] [IsScalarTower K L M₂]
    [ValuativeExtension K M₂] [Module.Finite K M₂] [IsGalois K M₂]
    (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L M₂ u := by
  let Ω := AlgebraicClosure L
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have : Module.Finite L M₂ := .of_restrictScalars_finite K L M₂
  have : Algebra.IsAlgebraic L M := .of_finite L M
  have : Algebra.IsAlgebraic L M₂ := .of_finite L M₂
  let ι₁ : M →ₐ[L] Ω := IsAlgClosed.lift; let ι₂ : M₂ →ₐ[L] Ω := IsAlgClosed.lift
  let e₁ := AlgEquiv.ofInjectiveField (ι₁.restrictScalars K)
  let e₂ := AlgEquiv.ofInjectiveField (ι₂.restrictScalars K)
  have : Module.Finite K (ι₁.restrictScalars K).fieldRange := .equiv e₁.toLinearEquiv
  have : Module.Finite K (ι₂.restrictScalars K).fieldRange := .equiv e₂.toLinearEquiv
  have : IsGalois K (ι₁.restrictScalars K).fieldRange := .of_algEquiv e₁
  have : IsGalois K (ι₂.restrictScalars K).fieldRange := .of_algEquiv e₂
  let N := (ι₁.restrictScalars K).fieldRange ⊔ (ι₂.restrictScalars K).fieldRange
  have : Module.Finite K N := IntermediateField.finiteDimensional_sup _ _
  let _ := finiteIntermediateFieldValuativeRel K Ω N
  let _ := finiteIntermediateFieldTopology K Ω N
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω N
  have := finiteIntermediateField_valuativeExtension K Ω N
  let _ : Algebra L N := ((algebraMap L Ω).codRestrict N.toSubring fun x ↦
    le_sup_left (b := (ι₂.restrictScalars K).fieldRange)
      ⟨algebraMap L M x, ι₁.commutes x⟩).toAlgebra
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun x ↦
    Subtype.ext (IsScalarTower.algebraMap_apply K L Ω x)
  rw [embeddingOrbitCount_eq_intermediateField K L M (N := N) (fun _ ↦ rfl) ι₁ le_sup_left u,
    embeddingOrbitCount_eq_intermediateField K L M₂ (N := N) (fun _ ↦ rfl) ι₂ le_sup_right u]

/-- Invariance of `embeddingOrbitCount` under a `K`-algebra equivalence `e : L ≃ₐ[K] L'` between
subextensions embedded in possibly different finite Galois overfields `M` and `M'`. -/
theorem embeddingOrbitCount_eq_of_algEquiv_left {L' M' : Type*}
    [Field L'] [Algebra K L']
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L' M'] [IsScalarTower K L' M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (e : L ≃ₐ[K] L') (u : RamificationIndexDomain) :
    embeddingOrbitCount K L M u = embeddingOrbitCount K L' M' u := by
  let _ : Algebra L M' := ((algebraMap L' M').comp (e : L →+* L')).toAlgebra
  have : IsScalarTower K L M' := IsScalarTower.of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply K L' M']
  have hemb : embeddingSubgroup K L M' = embeddingSubgroup K L' M' := by
    ext σ; simp only [mem_embeddingSubgroup_iff, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    exact ⟨fun h y ↦ by simpa using h (e.symm y), fun h x ↦ h (e x)⟩
  rw [embeddingOrbitCount_eq K L M M' u, embeddingOrbitCount_def, embeddingOrbitCount_def, hemb]

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

omit [IsGalois K M] [ValuativeExtension K L] in
/-- For a tower `M/L/K`, the relative index of `lowerRamificationGroup K M i` in
`embeddingSubgroup K L M` equals the index of `lowerRamificationGroup L M i` in `Gal(M/L)`. -/
theorem relIndex_lowerRamificationGroup_embeddingSubgroup [ValuativeExtension L M]
    [Module.Finite L M] (i : ℤ) :
    (lowerRamificationGroup K M i).relIndex (embeddingSubgroup K L M) =
      (lowerRamificationGroup L M i).index := by
  rw [← comap_restrictScalarsHom_lowerRamificationGroup K M L i,
    Subgroup.index_comap, range_restrictScalarsHom_eq_embeddingSubgroup K L M]

omit [IsGalois K M] [ValuativeExtension K L] in
private theorem index_lowerRamificationGroup_mul_index_sup [ValuativeExtension L M]
    [Module.Finite L M] (i : ℤ) :
    (lowerRamificationGroup L M i).index *
        (lowerRamificationGroup K M i ⊔ embeddingSubgroup K L M).index =
      (lowerRamificationGroup K M i).index := by
  rw [← relIndex_lowerRamificationGroup_embeddingSubgroup K L M i, ← Subgroup.relIndex_sup_left,
    Subgroup.relIndex_mul_index le_sup_left]

omit [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem withTowerTop {P : Prop}
    (h : [Algebra.IsAlgebraic K M] → [Algebra.IsAlgebraic K L] → [ValuativeExtension L M] →
      [Module.Finite L M] → [IsGalois L M] → P) : P := by
  have : Algebra.IsAlgebraic K M := .of_finite K M
  have : Algebra.IsAlgebraic K L := .tower_bot K L M
  have : ValuativeExtension L M := .of_isScalarTower (K := K)
  have : Module.Finite L M := .of_restrictScalars_finite K L M
  have := IsGalois.tower_top_of_isGalois K L M
  exact h

/-- The index `[G : G_0 H]` of inertia joined with `H` equals the inertia degree `f(L/K)`. -/
@[simp]
theorem index_lowerRamificationGroup_zero_sup_embeddingSubgroup :
    (lowerRamificationGroup K M 0 ⊔ embeddingSubgroup K L M).index = inertiaDegree K L :=
  withTowerTop K L M (by
    intro _ _ _ _ _
    have hmul := index_lowerRamificationGroup_mul_index_sup K L M 0
    rw [index_lowerRamificationGroup_zero L M, index_lowerRamificationGroup_zero K M,
      inertiaDegree_tower (K := K) (L := L) M, mul_comm (inertiaDegree K L)] at hmul
    exact Nat.eq_of_mul_eq_mul_left (inertiaDegree_pos (K := L) (L := M)) hmul)

/-- On `(-1, 0]`, `G^u = G_0`, so the orbit count is `inertiaDegree K L`. -/
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
      inertiaDegree K L * tameRamificationIndex K L :=
  withTowerTop K L M (by
    intro _ _ _ _ _
    have hmul := index_lowerRamificationGroup_mul_index_sup K L M 1
    rw [index_lowerRamificationGroup_one L M, index_lowerRamificationGroup_one K M,
      inertiaDegree_tower (K := K) (L := L) M, tameRamificationIndex_tower K L M] at hmul
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (inertiaDegree_pos (K := L) (L := M)) (tameRamificationIndex_pos L M))
      (by linear_combination hmul))

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
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (inertiaDegree_pos (K := K) (L := L)) (tameRamificationIndex_pos K L))
    (by linear_combination hmul)

end OrbitCount

/-! ### The Artin slope list -/

section ArtinSlopeList

variable (K L M : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]

/-- The **Artin slopes** of `L/K` read in a finite Galois extension `M/K`, in nondecreasing order
with multiplicity: for each integer lower index `1 ≤ i ≤ largestLowerJump K M`, `φ_{M/K}(i) + 1`
is listed `log_p [G_i H : G_{i+1} H]` times, where `H = embeddingSubgroup K L M` and
`p = ringChar 𝓀[K]`. -/
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
            Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1) := (rfl)

/-- For `L = K`, the Artin slope list is empty. -/
@[simp]
theorem artinSlopeList_self_left : artinSlopeList K K M = [] := by
  simp [artinSlopeList_def, Subgroup.relIndex_self]

/-- Every Artin slope of `L/K` is strictly greater than `1`. -/
theorem one_lt_of_mem_artinSlopeList {a : ℝ} (ha : a ∈ artinSlopeList K L M) : 1 < a := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 ha
  obtain ⟨-, rfl⟩ := List.mem_replicate.1 hj
  have hpos := Subtype.coe_lt_coe.2 (herbrand_strictMono K M
    (Subtype.mk_lt_mk.2 (by positivity) : (⟨0, by norm_num⟩ : RamificationIndexDomain) <
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩))
  rw [herbrand_of_coe_le_zero K M le_rfl] at hpos; linarith

/-- `artinSlopeList K L M` is sorted in nondecreasing order. -/
theorem pairwise_le_artinSlopeList : (artinSlopeList K L M).Pairwise (· ≤ ·) := by
  rw [artinSlopeList_def, List.pairwise_flatMap]
  refine ⟨fun _ _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl),
    List.Pairwise.imp (R := (· < ·)) (fun {i j} hij _ ha _ hb ↦ ?_) List.pairwise_lt_range⟩
  rw [(List.mem_replicate.1 ha).2, (List.mem_replicate.1 hb).2]
  linarith [Subtype.coe_lt_coe.2 (herbrand_strictMono K M (Subtype.mk_lt_mk.2
    (by exact_mod_cast Nat.add_lt_add_right hij 1) :
      (⟨((i + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ : _) <
      ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩))]

/-- Every step index `[G_{j + 1} H : G_{j + 2} H]` divides
`p ^ wildRamificationExponent K M`, hence equals `p ^ log_p [G_{j + 1} H : G_{j + 2} H]`. -/
theorem pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup (j : ℕ) :
    ringChar 𝓀[K] ^ Nat.log (ringChar 𝓀[K])
        ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) =
      (lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
        (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  set H := embeddingSubgroup K L M
  set K₂ := lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ H
  set K₁ := lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ H
  set K₀ := lowerRamificationGroup K M 1 ⊔ H
  have h₂₁ : K₂ ≤ K₁ := sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have h₁₀ : K₁ ≤ K₀ := sup_le_sup_right (lowerRamificationGroup_antitone K M (by omega)) H
  have hdvd₁ : K₂.relIndex K₁ ∣ H.relIndex K₀ := by
    rw [← Subgroup.relIndex_mul_relIndex H K₁ K₀ (le_sup_right.trans h₂₁) h₁₀,
      ← Subgroup.relIndex_mul_relIndex H K₂ K₁ le_sup_right h₂₁]
    exact ⟨H.relIndex K₂ * K₁.relIndex K₀, by ring⟩
  have hdvd₂ : H.relIndex K₀ ∣ ringChar 𝓀[K] ^ wildRamificationExponent K M := by
    dsimp only [K₀]
    rw [sup_comm, Subgroup.relIndex_sup_of_le_normalizer Subgroup.le_normalizer_of_normal,
      ← natCard_lowerRamificationGroup_one K M]
    exact Subgroup.relIndex_dvd_card H (lowerRamificationGroup K M 1)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (hdvd₁.trans hdvd₂)
  rw [hm, Nat.log_pow hp.one_lt]

/-- The multiplicity of `φ_{M/K}(j + 1) + 1` in `artinSlopeList K L M` equals
`log_p [G_{j + 1} H : G_{j + 2} H]`. -/
theorem count_artinSlopeList_herbrand_add_one (j : ℕ) :
    (artinSlopeList K L M).count ((herbrand K M ⟨((j + 1 : ℕ) : ℝ),
        Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ : ℝ) + 1) =
      Nat.log (ringChar 𝓀[K])
        ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
          (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) := by
  have hval_inj : Function.Injective fun k : ℕ ↦
      (herbrand K M ⟨((k + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (k + 1)⟩ : ℝ) + 1 :=
    fun k₁ k₂ hk ↦ by
      have hφ := congrArg Subtype.val ((herbrand_strictMono K M).injective (Subtype.ext
        (by linarith) : herbrand K M ⟨((k₁ + 1 : ℕ) : ℝ),
          Nat.cast_mem_ramificationIndexDomain (k₁ + 1)⟩ = _))
      exact_mod_cast (by dsimp at hφ; push_cast at hφ; linarith : (k₁ : ℝ) = k₂)
  by_cases hjJ : j < (largestLowerJump K M).toNat
  · rw [artinSlopeList_def, List.count_flatMap, ← List.sum_toFinset _ List.nodup_range,
      List.toFinset_range, Finset.sum_eq_single j]
    · exact List.count_replicate_self ..
    · exact fun k _ hkj ↦ List.count_eq_zero.2 fun hm ↦
        hkj (hval_inj (List.mem_replicate.1 hm).2.symm)
    · exact fun h ↦ absurd (Finset.mem_range.2 hjJ) h
  · have hbot (m : ℕ) (hm : (largestLowerJump K M).toNat < m) :
        lowerRamificationGroup K M (m : ℤ) = ⊥ :=
      lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (K := K) (L := M)
        (by have := neg_one_le_largestLowerJump K M; omega)
    rw [hbot (j + 1) (by omega), hbot (j + 2) (by omega), Subgroup.relIndex_self,
      Nat.log_one_right, List.count_eq_zero, artinSlopeList_def, List.mem_flatMap]
    rintro ⟨k, hk, hm⟩
    exact hjJ (hval_inj (List.mem_replicate.1 hm).2 ▸ List.mem_range.1 hk)

/-- If `u > 0` and `ψ_{M/K}(u)` is not a positive integer, then `G^v = G^u` on a right
neighborhood `(u, w]`. -/
private theorem exists_gt_forall_upperRamificationGroup_eq_of_ne_succ
    {u : RamificationIndexDomain} (hu : (0 : ℝ) < u)
    (hnot : ∀ j : ℕ, (inverseHerbrand K M u : ℝ) ≠ ((j + 1 : ℕ) : ℝ)) :
    ∃ w : RamificationIndexDomain, u < w ∧ ∀ v : RamificationIndexDomain, u < v → v ≤ w →
      upperRamificationGroup K M v = upperRamificationGroup K M u := by
  set x := inverseHerbrand K M u
  have hx_pos : (0 : ℝ) < x := by
    have hψ := inverseHerbrand_strictMono K M (Subtype.mk_lt_mk.2 hu : (⟨0, by norm_num⟩ : _) < u)
    rw [inverseHerbrand_of_coe_le_zero K M le_rfl] at hψ; exact Subtype.coe_lt_coe.2 hψ
  let j := ⌊(x : ℝ)⌋₊
  have hxj₁ : (j : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx_pos.le) fun h ↦ by
    cases hj : j with
    | zero => rw [hj, Nat.cast_zero] at h; linarith
    | succ k => exact hnot k (by rw [← h, hj])
  have hφj_lt : herbrand K M ⟨j, Nat.cast_mem_ramificationIndexDomain j⟩ < u :=
    herbrand_inverseHerbrand K M u ▸ herbrand_strictMono K M (Subtype.mk_lt_mk.2 hxj₁)
  have huw : u < herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ :=
    herbrand_inverseHerbrand K M u ▸ herbrand_strictMono K M
      (Subtype.mk_lt_mk.2 (by push_cast; exact Nat.lt_floor_add_one _))
  exact ⟨_, huw, fun v huv hvw ↦ by
    rw [upperRamificationGroup_eq_of_herbrand_lt_of_le K M (hφj_lt.trans huv) hvw,
      upperRamificationGroup_eq_of_herbrand_lt_of_le K M hφj_lt huw.le]⟩

/-- Right-hand jump formula for `embeddingOrbitCount` at `u > 0`: immediately past `u`, the orbit
count multiplies by `p ^ ((artinSlopeList K L M).count ((u : ℝ) + 1))`. -/
private theorem exists_gt_forall_embeddingOrbitCount_eq_mul_pow_count
    {u : RamificationIndexDomain} (hu : (0 : ℝ) < u) :
    ∃ w : RamificationIndexDomain, u < w ∧ ∀ v : RamificationIndexDomain, u < v → v ≤ w →
      embeddingOrbitCount K L M v = embeddingOrbitCount K L M u *
        ringChar 𝓀[K] ^ (artinSlopeList K L M).count ((u : ℝ) + 1) := by
  by_cases hint : ∃ j : ℕ, (inverseHerbrand K M u : ℝ) = ((j + 1 : ℕ) : ℝ)
  · obtain ⟨j, hj⟩ := hint
    have hx : inverseHerbrand K M u =
        ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ := Subtype.ext hj
    have hu_φ : herbrand K M ⟨((j + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 1)⟩ =
        u := by rw [← hx, herbrand_inverseHerbrand]
    refine ⟨herbrand K M ⟨((j + 2 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (j + 2)⟩,
      hu_φ ▸ herbrand_strictMono K M (Subtype.mk_lt_mk.2 (by push_cast; linarith)), fun v huv hvw ↦
      ?_⟩
    have hGu : upperRamificationGroup K M u = lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) := by
      rw [upperRamificationGroup_def, hx]
      simpa using lowerRamificationGroupReal_intCast K M ((j + 1 : ℕ) : ℤ)
    have hGv : upperRamificationGroup K M v = lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) :=
      upperRamificationGroup_eq_of_herbrand_lt_of_le K M (i := j + 1) (hu_φ.symm ▸ huv) hvw
    rw [← hu_φ, count_artinSlopeList_herbrand_add_one K L M j,
      pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M j,
      embeddingOrbitCount_def, embeddingOrbitCount_def, hu_φ, hGv, hGu, mul_comm,
      Subgroup.relIndex_mul_index (sup_le_sup_right
        (lowerRamificationGroup_antitone K M (by omega)) _)]
  · push Not at hint
    obtain ⟨w, huw, hw⟩ := exists_gt_forall_upperRamificationGroup_eq_of_ne_succ K M hu hint
    have hcnt0 : (artinSlopeList K L M).count ((u : ℝ) + 1) = 0 := by
      rw [List.count_eq_zero, artinSlopeList_def, List.mem_flatMap]
      rintro ⟨k, -, hm⟩
      have hinv := congrArg (fun z ↦ (inverseHerbrand K M z : ℝ))
        (Subtype.ext (by linarith [(List.mem_replicate.1 hm).2]) :
          herbrand K M ⟨((k + 1 : ℕ) : ℝ), Nat.cast_mem_ramificationIndexDomain (k + 1)⟩ = u)
      rw [inverseHerbrand_herbrand] at hinv; exact hint k hinv.symm
    exact ⟨w, huw, fun v huv hvw ↦ by
      rw [hcnt0, pow_zero, mul_one, embeddingOrbitCount_def, embeddingOrbitCount_def, hw v huv hvw]⟩

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
          Nat.log (ringChar 𝓀[K]) (embeddingOrbitCount K L M v /
            embeddingOrbitCount K L M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩) =
            (artinSlopeList K L M).count a := by
  obtain ⟨w, huw, hw⟩ := exists_gt_forall_embeddingOrbitCount_eq_mul_pow_count K L M
    (u := ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩) (sub_pos.2 ha)
  exact ⟨w, huw, fun v huv hvw ↦ by
    rw [hw v huv hvw, Nat.mul_div_cancel_left _ (embeddingOrbitCount_pos K L M _),
      Nat.log_pow (CharP.prime_ringChar 𝓀[K]).one_lt]; simp⟩

/-- A real number `a` belongs to `artinSlopeList K L M` if and only if `1 < a` and the orbit count
strictly increases immediately past `u = a - 1`. -/
theorem mem_artinSlopeList_iff {a : ℝ} :
    a ∈ artinSlopeList K L M ↔
      ∃ ha : 1 < a, ∀ v : RamificationIndexDomain,
        (⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ : RamificationIndexDomain) < v →
          embeddingOrbitCount K L M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ <
            embeddingOrbitCount K L M v := by
  refine ⟨fun hmem ↦ ?_, fun ⟨ha, hstrict⟩ ↦ ?_⟩
  · have ha := one_lt_of_mem_artinSlopeList K L M hmem
    obtain ⟨w, huw, hw⟩ := exists_gt_forall_embeddingOrbitCount_eq_mul_pow_count K L M
      (u := ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩) (sub_pos.2 ha)
    refine ⟨ha, fun v hv ↦ lt_of_lt_of_le ?_ (embeddingOrbitCount_mono K L M (min_le_left v w))⟩
    rw [hw (min v w) (lt_min hv huw) (min_le_right v w)]; simp only [sub_add_cancel]
    exact lt_mul_of_one_lt_right (embeddingOrbitCount_pos K L M _)
      (one_lt_pow₀ (CharP.prime_ringChar 𝓀[K]).one_lt (List.count_pos_iff.2 hmem).ne')
  · obtain ⟨w, huw, hw⟩ := exists_gt_forall_embeddingOrbitCount_eq_mul_pow_count K L M
      (u := ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩) (sub_pos.2 ha)
    have hlt := hstrict w huw; rw [hw w huw le_rfl] at hlt; simp only [sub_add_cancel] at hlt
    exact List.count_pos_iff.1 (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hlt)

/-- For a Galois extension `M/K`, the entries of `artinSlopeList K M M` are precisely `u + 1` as
`u` ranges over the positive upper ramification jumps of `M/K`. -/
theorem mem_artinSlopeList_self_iff {a : ℝ} :
    a ∈ artinSlopeList K M M ↔
      ∃ ha : 1 < a, UpperJump K M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩ := by
  rw [mem_artinSlopeList_iff]
  refine exists_congr fun ha ↦ ?_
  rw [upperJump_iff]
  refine forall₂_congr fun v hv ↦ ?_
  simp only [embeddingOrbitCount_self_right]
  have hle := upperRamificationGroup_antitone K M hv.le
  refine ⟨fun hlt ↦ lt_of_le_of_ne hle fun h ↦ hlt.ne (congrArg Subgroup.index h.symm), fun hlt ↦
    ?_⟩
  have hmul := Subgroup.relIndex_mul_index hle
  have hpos : 0 < (upperRamificationGroup K M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩).index := by
    simpa using embeddingOrbitCount_pos K M M ⟨a - 1, Set.mem_Ici.2 (by linarith)⟩
  have hvpos : 0 < (upperRamificationGroup K M v).index := by
    simpa using embeddingOrbitCount_pos K M M v
  have hrpos : 0 < (upperRamificationGroup K M v).relIndex _ :=
    Nat.pos_of_mul_pos_right (hmul.symm ▸ hvpos)
  have hne : (upperRamificationGroup K M v).relIndex _ ≠ 1 :=
    mt Subgroup.relIndex_eq_one.1 hlt.not_ge
  exact hmul ▸ lt_mul_of_one_lt_left hpos (by omega)

private theorem artinSlopeList_eq_of_embeddingOrbitCount_eq {L' M' : Type*}
    [Field L'] [Algebra K L']
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L' M'] [IsScalarTower K L' M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (h : ∀ u, embeddingOrbitCount K L M u = embeddingOrbitCount K L' M' u) :
    artinSlopeList K L M = artinSlopeList K L' M' :=
  List.Perm.eq_of_pairwise' (pairwise_le_artinSlopeList K L M) (pairwise_le_artinSlopeList K L' M')
    (List.perm_iff_count.2 fun a ↦ by
      by_cases ha : 1 < a
      · obtain ⟨w₁, huw₁, hw₁⟩ :=
          exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L M ha
        obtain ⟨w₂, huw₂, hw₂⟩ :=
          exists_gt_forall_natLog_div_embeddingOrbitCount_eq_count_artinSlopeList K L' M' ha
        rw [← hw₁ (min w₁ w₂) (lt_min huw₁ huw₂) (min_le_left _ _),
          ← hw₂ (min w₁ w₂) (lt_min huw₁ huw₂) (min_le_right _ _), h _, h _]
      · simp [List.count_eq_zero.2 fun hm ↦ ha (one_lt_of_mem_artinSlopeList K _ _ hm)])

/-- **Independence of `artinSlopeList` from the finite Galois overfield.** -/
theorem artinSlopeList_eq (M₂ : Type*)
    [Field M₂] [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [Algebra K M₂] [Algebra L M₂] [IsScalarTower K L M₂]
    [ValuativeExtension K M₂] [Module.Finite K M₂] [IsGalois K M₂] :
    artinSlopeList K L M = artinSlopeList K L M₂ :=
  artinSlopeList_eq_of_embeddingOrbitCount_eq K L M (embeddingOrbitCount_eq K L M M₂)

/-- Invariance of `artinSlopeList` under a `K`-algebra equivalence `e : L ≃ₐ[K] L'` between
subextensions embedded in possibly different finite Galois overfields `M` and `M'`. -/
theorem artinSlopeList_eq_of_algEquiv {L' M' : Type*}
    [Field L'] [Algebra K L']
    [Field M'] [ValuativeRel M'] [TopologicalSpace M'] [IsNonarchimedeanLocalField M']
    [Algebra K M'] [Algebra L' M'] [IsScalarTower K L' M']
    [ValuativeExtension K M'] [Module.Finite K M'] [IsGalois K M']
    (e : L ≃ₐ[K] L') :
    artinSlopeList K L M = artinSlopeList K L' M' :=
  artinSlopeList_eq_of_embeddingOrbitCount_eq K L M
    (embeddingOrbitCount_eq_of_algEquiv_left K L M e)

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

/-- Cumulative-index formula past wild inertia: for every `k : ℕ`,
`[G : G_{k + 1} H] = f(L/K) · ε(L/K) · p ^ (∑ j < k, log_p [G_{j + 1} H : G_{j + 2} H])`. -/
theorem index_lowerRamificationGroup_succ_sup_embeddingSubgroup (k : ℕ) :
    (lowerRamificationGroup K M ((k + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).index =
      inertiaDegree K L * tameRamificationIndex K L *
        ringChar 𝓀[K] ^ ∑ j ∈ Finset.range k, Nat.log (ringChar 𝓀[K])
          ((lowerRamificationGroup K M ((j + 2 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M).relIndex
            (lowerRamificationGroup K M ((j + 1 : ℕ) : ℤ) ⊔ embeddingSubgroup K L M)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Subgroup.relIndex_mul_index (sup_le_sup_right
        (lowerRamificationGroup_antitone K M (by omega : ((k + 1 : ℕ) : ℤ) ≤ ((k + 2 : ℕ) : ℤ)))
        _), ih, ← pow_natLog_relIndex_lowerRamificationGroup_sup_embeddingSubgroup K L M k,
      Finset.sum_range_succ, pow_add]; ring

/-- The number of Artin slopes (counted with multiplicity) equals `wildRamificationExponent K L`. -/
@[simp]
theorem length_artinSlopeList :
    (artinSlopeList K L M).length = wildRamificationExponent K L := by
  have hJ := index_lowerRamificationGroup_succ_sup_embeddingSubgroup K L M
    (largestLowerJump K M).toNat
  rw [lowerRamificationGroup_toNat_largestLowerJump_add_one, bot_sup_eq,
    index_embeddingSubgroup, ← ramificationIndex_mul_inertiaDegree (K := K) (L := L),
    ← tameRamificationIndex_mul_pow_wildRamificationExponent K L, mul_right_comm,
    mul_comm (tameRamificationIndex K L)] at hJ
  have hpow := Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (inertiaDegree_pos (K := K) (L := L)) (tameRamificationIndex_pos K L)) hJ
  rw [artinSlopeList_def, List.length_flatMap, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range]
  simpa [List.length_replicate] using
    (Nat.pow_right_injective (CharP.prime_ringChar 𝓀[K]).two_le hpow).symm

/-- `artinSlopeList K L M` is empty if and only if `L/K` is tamely ramified. -/
@[simp]
theorem artinSlopeList_eq_nil_iff : artinSlopeList K L M = [] ↔ IsTamelyRamified K L := by
  rw [← List.length_eq_zero_iff, length_artinSlopeList, wildRamificationExponent_eq_zero_iff]

end ArtinSlopeList

/-- **Hasse–Arf integrality of abelian Galois Artin slopes.** When `M/K` is a finite abelian
Galois extension, every entry of `artinSlopeList K M M` is a natural number `n ≥ 2`. -/
theorem exists_nat_eq_of_mem_artinSlopeList_self (K M : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsAbelianGalois K M] {a : ℝ}
    (ha : a ∈ artinSlopeList K M M) : ∃ n : ℕ, 2 ≤ n ∧ a = n := by
  obtain ⟨ha1, hj⟩ := (mem_artinSlopeList_self_iff K M).1 ha
  obtain ⟨z, hz⟩ := hasseArf K M hj; rw [Subtype.coe_mk] at hz
  have hz_pos : (0 : ℤ) < z := by exact_mod_cast (by linarith : (0 : ℝ) < z)
  have hcast : (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ z + 1)
  exact ⟨(z + 1).toNat, by omega, by linarith⟩

end TauCeti
