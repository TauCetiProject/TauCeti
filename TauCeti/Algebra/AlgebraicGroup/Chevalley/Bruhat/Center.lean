/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injectivity
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centre of a Chevalley group

Using the Bruhat decomposition, the opposite-unipotent intersection theorems, and the longest
Weyl-element action on the positive unipotent subgroup, we determine the full centre of both
`D.extendedElementarySubgroup K` and `D.elementarySubgroup K` over every field `K` (including
finite fields such as `𝔽₂`).

## Main results

* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_elementarySubgroup`: over every
  field `K`, every element of `D.extendedElementarySubgroup K` centralizing
  `D.elementarySubgroup K` lies in the actual torus `T(K)` and centralizes
  `D.rootTorusSubgroup K`.
* `ChevalleyDatum.torusPoints_mem_center_extendedElementarySubgroup_iff` and
  `ChevalleyDatum.torusPoints_mem_center_elementarySubgroup_iff`: `@[simp]` centre membership
  criteria for torus points in terms of coordinate root characters.
* `ChevalleyDatum.centerExtendedElementarySubgroupEquiv`: over every field `K` and for every
  Chevalley datum `D`, the centre of `D.extendedElementarySubgroup K` is canonically
  isomorphic to `AddChar (Λ(D) / Q) Kˣ`, expressed in the chosen basis of `Λ(D)`.
* `DynkinType.scChevalleyDatum_torusPoints_mem_center_elementarySubgroup_iff` and
  `DynkinType.scChevalleyDatumCenterElementarySubgroupEquiv`: for the simply connected datum
  over every field `K`, the extended and elementary subgroups coincide and the centre of
  `(t.scChevalleyDatum ht).elementarySubgroup K` is canonically isomorphic to
  `AddChar (P / Q) Kˣ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28 and Corollary 1 to
  Theorem 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1–7.2 and §8.4.
-/

public section

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid}

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht) (K : Type v) [Field K]

private theorem weylProjection_eq_one_of_mem_bruhatCell_of_conj_positivePoints
    {g : D.points K} {n : D.weylSubgroup K}
    (hg : g ∈ D.bruhatCell K (D.weylProjection K n))
    (hconj : ∀ y ∈ D.positivePoints K, g * y * g⁻¹ ∈ D.positivePoints K) :
    D.weylProjection K n = 1 := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  rw [D.bruhatCell_weylProjection K n] at hg
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  by_contra hw
  obtain ⟨γ, hγ⟩ := inversions_nonempty_of_ne_one
    (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) hw
  have hγpos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [t.posRoots_rationalRootSystem ht]
    exact inversions_subset_posRoots _ _ _ hγ
  set δ := (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n) γ
  have hδneg : δ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [t.negRoots_rationalRootSystem ht]
    exact mapsTo_inversions_negRoots _ _ _ hγ
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints K n γ
  let x := D.rootSubgroupPoints γ K (ofAdd ((c⁻¹ : Kˣ) : K))
  let y := b₂⁻¹ * x * b₂
  have hyU : y ∈ D.positivePoints K := by
    have hxU : x ∈ D.positivePoints K := D.rootSubgroupPoints_mem_positivePoints K hγpos _
    have h := (Subgroup.mem_normalizer_iff.mp
      (D.borelSubgroup_le_normalizer_positivePoints K ((D.borelSubgroup K).inv_mem hb₂))
      x).mp hxU
    simpa only [y, inv_inv] using h
  have hgyU : (b₁ * (n : D.points K) * b₂) * y * (b₁ * (n : D.points K) * b₂)⁻¹ ∈
      D.positivePoints K := hconj y hyU
  have hnx_eq : (n : D.points K) * x * (n : D.points K)⁻¹ =
      b₁⁻¹ * ((b₁ * (n : D.points K) * b₂) * y * (b₁ * (n : D.points K) * b₂)⁻¹) * b₁ := by
    dsimp only [y]
    group
  have hnxB : D.rootSubgroupPoints δ K (ofAdd 1) ∈ D.borelSubgroup K := by
    have hconj' : (n : D.points K) * x * (n : D.points K)⁻¹ =
        D.rootSubgroupPoints δ K (ofAdd 1) := by
      simpa only [x, MulAut.conj_apply, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (Units.ne_zero c)] using hc ((c⁻¹ : Kˣ) : K)
    rw [← hconj', hnx_eq]
    exact (D.borelSubgroup K).mul_mem
      ((D.borelSubgroup K).mul_mem ((D.borelSubgroup K).inv_mem hb₁)
        (D.positivePoints_le_borelSubgroup K hgyU))
      hb₁
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K δ
    ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hδneg _).mp hnxB)

private theorem mem_borelSubgroup_of_mem_extendedElementarySubgroup_inf_centralizer
    {g : D.points K} (hgE : g ∈ D.extendedElementarySubgroup K)
    (hgC : g ∈ Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K))) :
    g ∈ D.borelSubgroup K := by
  obtain ⟨w, hwcell, _⟩ := D.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup K hgE
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
  have hconj : ∀ y ∈ D.positivePoints K, g * y * g⁻¹ ∈ D.positivePoints K := by
    intro y hyU
    have hyE : y ∈ D.elementarySubgroup K :=
      D.positivePoints_le_iff.mpr
        (fun _ _ u => D.rootSubgroupPoints_mem_elementarySubgroup K _ u) hyU
    have hcomm := (Subgroup.mem_centralizer_iff.mp hgC y hyE).symm
    simpa only [mul_inv_eq_iff_eq_mul.mpr hcomm] using hyU
  have hproj1 :=
    D.weylProjection_eq_one_of_mem_bruhatCell_of_conj_positivePoints K hwcell hconj
  rw [hproj1, D.bruhatCell_one] at hwcell
  exact hwcell

private theorem mem_range_torusPoints_of_mem_borelSubgroup_of_commute_longestElement
    {g : D.points K} (hgB : g ∈ D.borelSubgroup K) (n₀ : D.weylSubgroup K)
    (hn₀w : D.weylProjection K n₀ =
      let _ := t.isReduced_simplyConnectedRootDatum ht
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht))
    (hcomm : Commute (n₀ : D.points K) g) :
    g ∈ (D.torusPoints K).range := by
  obtain ⟨u, huU, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
  have hconj_u : (n₀ : D.points K) * u * (n₀ : D.points K)⁻¹ ∈ D.negativePoints K := by
    rw [← D.map_positivePoints_conj_longestElement K n₀ hn₀w]
    exact ⟨u, huU, rfl⟩
  have hconj_t : (n₀ : D.points K) * D.torusPoints K s * (n₀ : D.points K)⁻¹ ∈
      (D.torusPoints K).range :=
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints K n₀.property) (D.torusPoints K s)).mp
        ⟨s, rfl⟩
  have hu_eq : u = ((n₀ : D.points K) * u * (n₀ : D.points K)⁻¹) *
      (((n₀ : D.points K) * D.torusPoints K s * (n₀ : D.points K)⁻¹) *
        (D.torusPoints K s)⁻¹) := by
    have h := congrArg (fun x => x * (D.torusPoints K s)⁻¹)
      (mul_inv_eq_iff_eq_mul.mpr hcomm.eq)
    calc
      u = u * D.torusPoints K s * (D.torusPoints K s)⁻¹ := by group
      _ = (n₀ : D.points K) * (u * D.torusPoints K s) * (n₀ : D.points K)⁻¹ *
            (D.torusPoints K s)⁻¹ := h.symm
      _ = ((n₀ : D.points K) * u * (n₀ : D.points K)⁻¹) *
            (((n₀ : D.points K) * D.torusPoints K s * (n₀ : D.points K)⁻¹) *
              (D.torusPoints K s)⁻¹) := by group
  have hu1 : u = 1 := by
    rw [← Subgroup.mem_bot,
      ← D.positivePoints_inf_negativePoints_sup_range_torusPoints_eq_bot K]
    refine ⟨huU, ?_⟩
    rw [hu_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hconj_u)
      (Subgroup.mem_sup_right
        ((D.torusPoints K).range.mul_mem hconj_t ((D.torusPoints K).range.inv_mem ⟨s, rfl⟩)))
  simp [hu1]

/-- Over every field `K`, every element of `D.extendedElementarySubgroup K` centralizing
`D.elementarySubgroup K` lies in the actual character-lattice torus and centralizes the full
root-and-torus subgroup. -/
theorem extendedElementarySubgroup_inf_centralizer_elementarySubgroup :
    D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  apply le_antisymm
  · rintro g ⟨hgE, hgC⟩
    have hgB :=
      D.mem_borelSubgroup_of_mem_extendedElementarySubgroup_inf_centralizer K hgE hgC
    let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    obtain ⟨n₀, hn₀E, hn₀w⟩ := D.exists_mem_elementarySubgroup_weylProjection_eq K w₀
    have hcomm : Commute (n₀ : D.points K) g :=
      Subgroup.mem_centralizer_iff.mp hgC n₀ hn₀E
    obtain ⟨s, rfl⟩ :=
      D.mem_range_torusPoints_of_mem_borelSubgroup_of_commute_longestElement K hgB n₀ hn₀w hcomm
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K] at hh
    obtain ⟨e, he, r, rfl⟩ := (D.mem_extendedElementarySubgroup_iff K h).mp hh
    have hec := Subgroup.mem_centralizer_iff.mp hgC e he
    have hrc : D.torusPoints K r * D.torusPoints K s = D.torusPoints K s * D.torusPoints K r := by
      rw [← map_mul, mul_comm r s, map_mul]
    calc
      e * D.torusPoints K r * D.torusPoints K s = e * (D.torusPoints K s * D.torusPoints K r) := by
        rw [mul_assoc, hrc]
      _ = D.torusPoints K s * (e * D.torusPoints K r) := by
        rw [← mul_assoc, hec, mul_assoc]
  · refine le_inf (inf_le_left.trans ?_) (inf_le_right.trans (Subgroup.centralizer_le ?_))
    · rintro _ ⟨s, rfl⟩
      exact D.torusPoints_mem_extendedElementarySubgroup K s
    · rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K]
      exact D.elementarySubgroup_le_extendedElementarySubgroup K

private theorem map_center_subtype {G : Type*} [Group G] (H : Subgroup G) :
    (Subgroup.center H).map H.subtype = H ⊓ Subgroup.centralizer (H : Set G) := by
  have him : H.subtype '' Set.univ = (H : Set G) := by
    rw [Set.image_univ, ← MonoidHom.coe_range, Subgroup.range_subtype]
  rw [← Subgroup.centralizer_univ,
    ← Subgroup.comap_centralizer_image_of_injective H.subtype_injective Set.univ, him,
    Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- Over every field `K`, the centre of `D.extendedElementarySubgroup K` embeds into `D.points K`
as the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_extendedElementarySubgroup :
    (Subgroup.center (D.extendedElementarySubgroup K)).map
        (D.extendedElementarySubgroup K).subtype =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  rw [map_center_subtype, ← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]
  apply le_antisymm
  · exact inf_le_inf_left _
      (Subgroup.centralizer_le (D.elementarySubgroup_le_extendedElementarySubgroup K))
  · rw [D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K,
      D.extendedElementarySubgroup_eq_rootTorusSubgroup K]
    refine le_inf (inf_le_left.trans ?_) inf_le_right
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_rootTorusSubgroup K s

/-- Over every field `K`, the centre of `D.elementarySubgroup K` consists of the elementary
points lying in the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_elementarySubgroup :
    (Subgroup.center (D.elementarySubgroup K)).map (D.elementarySubgroup K).subtype =
      D.elementarySubgroup K ⊓
        ((D.torusPoints K).range ⊓
          Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) := by
  rw [map_center_subtype]
  nth_rw 1 [← inf_eq_left.mpr (D.elementarySubgroup_le_extendedElementarySubgroup K)]
  rw [inf_assoc, D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]

/-- Over every field `K`, a torus point of `D.extendedElementarySubgroup K` lies in the centre
if and only if every coordinate root character vanishes on it. -/
@[simp]
theorem torusPoints_mem_center_extendedElementarySubgroup_iff (s : Fin t.rank → Kˣ) :
    (⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ :
        D.extendedElementarySubgroup K) ∈
      Subgroup.center (D.extendedElementarySubgroup K) ↔
    ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [← Subgroup.mem_map_iff_mem (D.extendedElementarySubgroup K).subtype_injective,
    D.map_center_extendedElementarySubgroup K, Subgroup.coe_subtype, Subgroup.mem_inf,
    and_iff_right ⟨s, rfl⟩,
    D.torusPoints_mem_centralizer_rootTorusSubgroup_iff (D.rootSubgroupPoints_injective K)]

/-- Over every field `K`, a torus point lying in `D.elementarySubgroup K` lies in the centre of
`D.elementarySubgroup K` if and only if every coordinate root character vanishes on it. -/
@[simp]
theorem torusPoints_mem_center_elementarySubgroup_iff (s : Fin t.rank → Kˣ)
    (hs : D.torusPoints K s ∈ D.elementarySubgroup K) :
    (⟨D.torusPoints K s, hs⟩ : D.elementarySubgroup K) ∈
      Subgroup.center (D.elementarySubgroup K) ↔
    ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [← Subgroup.mem_map_iff_mem (D.elementarySubgroup K).subtype_injective,
    D.map_center_elementarySubgroup K, Subgroup.coe_subtype, Subgroup.mem_inf,
    Subgroup.mem_inf, and_iff_right hs, and_iff_right ⟨s, rfl⟩,
    D.torusPoints_mem_centralizer_rootTorusSubgroup_iff (D.rootSubgroupPoints_injective K)]

private theorem coe_equivMapOfInjective_symm_subgroupCongr {G A : Type*} [Group G] [Group A]
    {H T : Subgroup G} (hmap : (Subgroup.center H).map H.subtype = T) (e : A ≃* T) (χ : A) :
    ((((((Subgroup.center H).equivMapOfInjective H.subtype H.subtype_injective).symm
        ((MulEquiv.subgroupCongr hmap.symm) (e χ)) : Subgroup.center H) : H) : G)) =
      (e χ : G) := by
  let f := (Subgroup.center H).equivMapOfInjective H.subtype H.subtype_injective
  have h1 : (((f.symm ((MulEquiv.subgroupCongr hmap.symm) (e χ)) : Subgroup.center H) : H) : G) =
      (f (f.symm ((MulEquiv.subgroupCongr hmap.symm) (e χ))) : G) :=
    rfl
  rw [h1, MulEquiv.apply_symm_apply, MulEquiv.subgroupCongr_apply]

/-- **Centre of an extended elementary Chevalley group.** Over every field `K` and for every
Chevalley datum `D`, unit-valued characters of `Λ(D) / Q` (in the chosen basis of `Λ(D)`)
canonically identify with `Subgroup.center (D.extendedElementarySubgroup K)`. -/
def centerExtendedElementarySubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup K) :=
  (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K)).trans
    ((MulEquiv.subgroupCongr (D.map_center_extendedElementarySubgroup K).symm).trans
      ((Subgroup.center (D.extendedElementarySubgroup K)).equivMapOfInjective
        (D.extendedElementarySubgroup K).subtype
        (D.extendedElementarySubgroup K).subtype_injective).symm)

/-- The forward equivalence sends a character of `Λ(D) / Q` to the corresponding torus point. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv K χ : D.extendedElementarySubgroup K) :
        D.points K) =
      D.torusPoints K (quotientCharTorusPoint _ χ) :=
  (coe_equivMapOfInjective_symm_subgroupCongr
      (D.map_center_extendedElementarySubgroup K)
      (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K)) χ).trans
    (D.coe_torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K) χ)

/-- The inverse equivalence recovers the character on a quotient class by evaluating the torus
parameter. -/
@[simp]
theorem centerExtendedElementarySubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → Kˣ)
    (hg : (⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩ :
        D.extendedElementarySubgroup K) ∈ Subgroup.center (D.extendedElementarySubgroup K))
    (μ : Fin t.rank → ℤ) :
    (D.centerExtendedElementarySubgroupEquiv K).symm
      ⟨⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hgT : D.torusPoints K s ∈ (D.torusPoints K).range ⊓
      Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) :=
    (D.map_center_extendedElementarySubgroup K).le ⟨_, hg, rfl⟩
  have hsub :
      ((MulEquiv.subgroupCongr (D.map_center_extendedElementarySubgroup K).symm).symm
        (((Subgroup.center (D.extendedElementarySubgroup K)).equivMapOfInjective
            (D.extendedElementarySubgroup K).subtype
            (D.extendedElementarySubgroup K).subtype_injective)
          ⟨⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩, hg⟩)) =
        ⟨D.torusPoints K s, hgT⟩ :=
    Subtype.ext rfl
  rw [centerExtendedElementarySubgroupEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, hsub]
  exact D.torusInfCentralizerRootTorusSubgroupEquiv_symm_apply_mk K
    (D.rootSubgroupPoints_injective K) s hgT μ

end ChevalleyDatum

variable (t ht)

/-- Over every field `K`, the centre of the simply connected elementary Chevalley group embeds
into the ambient points as the toral centralizer. -/
theorem map_center_scChevalleyDatum_elementarySubgroup (K : Type v) [Field K] :
    (Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K)).map
        ((t.scChevalleyDatum ht).elementarySubgroup K).subtype =
      ((t.scChevalleyDatum ht).torusPoints K).range ⊓
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup K :
          Set ((t.scChevalleyDatum ht).points K)) := by
  rw [← t.scChevalleyDatum_extendedElementarySubgroup ht K]
  exact (t.scChevalleyDatum ht).map_center_extendedElementarySubgroup K

/-- Over every field `K`, a torus point of the simply connected elementary Chevalley group lies in
its centre if and only if every root character vanishes on it in fundamental-weight coordinates. -/
theorem scChevalleyDatum_torusPoints_mem_center_elementarySubgroup_iff (K : Type v) [Field K]
    (s : Fin t.rank → Kˣ)
    (hs : (t.scChevalleyDatum ht).torusPoints K s ∈
      (t.scChevalleyDatum ht).elementarySubgroup K) :
    (⟨(t.scChevalleyDatum ht).torusPoints K s, hs⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) ↔
    ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  simpa only [scChevalleyDatum_coordinateRoot] using
    (t.scChevalleyDatum ht).torusPoints_mem_center_elementarySubgroup_iff K s hs

private def addCharQuotEquiv {M C : Type*} [AddCommGroup M] [Module ℤ M] [CommMonoid C]
    {P Q : Submodule ℤ M} (h : P = Q) :
    AddChar (M ⧸ Q) C ≃* AddChar (M ⧸ P) C where
  toFun χ := χ.compAddMonoidHom (Submodule.quotEquivOfEq P Q h).toAddMonoidHom
  invFun χ := χ.compAddMonoidHom (Submodule.quotEquivOfEq P Q h).symm.toAddMonoidHom
  left_inv χ := by ext ⟨x⟩; rfl
  right_inv χ := by ext ⟨x⟩; rfl
  map_mul' _ _ := by ext ⟨x⟩; rfl

private theorem quotientCharTorusPoint_addCharQuotEquiv {κ R : Type*} [DecidableEq κ]
    [CommRing R] {P Q : Submodule ℤ (κ → ℤ)} (h : P = Q) (χ : AddChar ((κ → ℤ) ⧸ Q) Rˣ) :
    quotientCharTorusPoint P (addCharQuotEquiv h χ) = quotientCharTorusPoint Q χ := by
  ext i
  simp only [quotientCharTorusPoint_apply, Submodule.mkQ_apply, addCharQuotEquiv,
    MulEquiv.coe_mk, Equiv.coe_fn_mk, AddChar.compAddMonoidHom_apply]
  change (χ (Submodule.quotEquivOfEq P Q h (Submodule.Quotient.mk (Pi.single i 1))) : R) = _
  rw [Submodule.quotEquivOfEq_mk]

/-- **Centre of the simply connected Chevalley group.** Over every field `K`, unit-valued
characters of `P / Q` canonically identify with the centre of
`(t.scChevalleyDatum ht).elementarySubgroup K`. -/
def scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K] :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) :=
  (addCharQuotEquiv (C := Kˣ) (by
      simp only [funext (t.scChevalleyDatum_coordinateRoot ht), RootPairing.rootSpan])).trans
    (((t.scChevalleyDatum ht).centerExtendedElementarySubgroupEquiv K).trans
      (Subgroup.centerCongr
        (MulEquiv.subgroupCongr (t.scChevalleyDatum_extendedElementarySubgroup ht K))))

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point. -/
@[simp]
theorem coe_scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K]
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ) :
    ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).elementarySubgroup K) : (t.scChevalleyDatum ht).points K) =
      (t.scChevalleyDatum ht).torusPoints K (quotientCharTorusPoint _ χ) := by
  change (((t.scChevalleyDatum ht).centerExtendedElementarySubgroupEquiv K
      (addCharQuotEquiv (C := Kˣ) _ χ) :
      (t.scChevalleyDatum ht).extendedElementarySubgroup K) :
      (t.scChevalleyDatum ht).points K) = _
  rw [ChevalleyDatum.coe_centerExtendedElementarySubgroupEquiv,
    quotientCharTorusPoint_addCharQuotEquiv]

/-- The inverse simply connected centre equivalence evaluates a weight class by the character
of the given torus parameter. -/
@[simp]
theorem scChevalleyDatumCenterElementarySubgroupEquiv_symm_apply_mk (K : Type v) [Field K]
    (s : Fin t.rank → Kˣ)
    (hs : (t.scChevalleyDatum ht).torusPoints K s ∈
      (t.scChevalleyDatum ht).elementarySubgroup K)
    (hg : (⟨(t.scChevalleyDatum ht).torusPoints K s, hs⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K))
    (μ : Fin t.rank → ℤ) :
    (t.scChevalleyDatumCenterElementarySubgroupEquiv ht K).symm
      ⟨⟨(t.scChevalleyDatum ht).torusPoints K s, hs⟩, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hgE : (⟨(t.scChevalleyDatum ht).torusPoints K s,
      (t.scChevalleyDatum ht).torusPoints_mem_extendedElementarySubgroup K s⟩ :
      (t.scChevalleyDatum ht).extendedElementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).extendedElementarySubgroup K) :=
    ((t.scChevalleyDatum ht).torusPoints_mem_center_extendedElementarySubgroup_iff K s).mpr
      fun γ => by
        simpa only [t.scChevalleyDatum_coordinateRoot ht] using
          (t.scChevalleyDatum_torusPoints_mem_center_elementarySubgroup_iff ht K s hs).mp hg γ
  have hmem :
      (Subgroup.centerCongr
        (MulEquiv.subgroupCongr (t.scChevalleyDatum_extendedElementarySubgroup ht K))).symm
        ⟨⟨(t.scChevalleyDatum ht).torusPoints K s, hs⟩, hg⟩ =
        ⟨⟨(t.scChevalleyDatum ht).torusPoints K s,
          (t.scChevalleyDatum ht).torusPoints_mem_extendedElementarySubgroup K s⟩, hgE⟩ :=
    Subtype.ext (Subtype.ext rfl)
  rw [scChevalleyDatumCenterElementarySubgroupEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_trans_apply, hmem]
  change ((t.scChevalleyDatum ht).centerExtendedElementarySubgroupEquiv K).symm
      ⟨⟨(t.scChevalleyDatum ht).torusPoints K s,
        (t.scChevalleyDatum ht).torusPoints_mem_extendedElementarySubgroup K s⟩, hgE⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ
  exact (t.scChevalleyDatum ht).centerExtendedElementarySubgroupEquiv_symm_apply_mk K s hgE μ

end

end TauCeti.DynkinType
