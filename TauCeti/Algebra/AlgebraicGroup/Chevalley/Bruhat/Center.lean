/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Generation
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.LongestElement
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Torus centralizer, torus normalizer, and centre of a Chevalley group

Using the unique Bruhat normal form and the opposite-unipotent intersection theorems, we
determine the centralizer and normalizer of the actual character-lattice torus and the full
centre of the generated Chevalley group over any field.

## Main results

* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_range_torusPoints` and
  `ChevalleyDatum.extendedElementarySubgroup_inf_normalizer_range_torusPoints`: over any
  infinite field `K`, inside `D.extendedElementarySubgroup K`, the centralizer of the actual
  torus `T(K)` is `T(K)` and its normalizer is the Weyl subgroup `N(K)`.
* `ChevalleyDatum.extendedElementarySubgroup_inf_centralizer_elementarySubgroup`: over every
  field `K` (including finite fields such as `𝔽₂`), every element of
  `D.extendedElementarySubgroup K` centralizing `D.elementarySubgroup K` lies in the actual
  torus `T(K)` and centralizes `D.rootTorusSubgroup K`.
* `ChevalleyDatum.centerExtendedElementarySubgroupEquiv`: over every field `K` and for every
  Chevalley datum `D`, the centre of `D.extendedElementarySubgroup K` is canonically
  isomorphic to `AddChar (Λ(D) / Q) Kˣ`, expressed in the chosen basis of `Λ(D)`.
* `DynkinType.scChevalleyDatumCenterElementarySubgroupEquiv`: for the simply connected datum
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

section InfiniteField

variable [Infinite K]

/-- Over an infinite field, no nonidentity positive point normalizes the actual torus. -/
@[simp]
theorem positivePoints_inf_normalizer_range_torusPoints :
    D.positivePoints K ⊓ Subgroup.normalizer (Set.range (D.torusPoints K)) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hvU, hvN⟩
  rw [← D.positivePoints_inf_centralizer_range_torusPoints K]
  refine ⟨hvU, Subgroup.mem_centralizer_iff.mpr ?_⟩
  rintro _ ⟨r, rfl⟩
  have hT : v * D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹ ∈ (D.torusPoints K).range :=
    (D.torusPoints K).range.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hvN (D.torusPoints K r)).mp ⟨r, rfl⟩)
      ((D.torusPoints K).range.inv_mem ⟨r, rfl⟩)
  have hU : v * D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹ ∈ D.positivePoints K := by
    have hconj : D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹ ∈ D.positivePoints K :=
      (Subgroup.mem_normalizer_iff.mp
        (D.range_torusPoints_le_normalizer_positivePoints K ⟨r, rfl⟩) v⁻¹).mp
        ((D.positivePoints K).inv_mem hvU)
    have heq : v * D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹ =
        v * (D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹) := by group
    rw [heq]
    exact (D.positivePoints K).mul_mem hvU hconj
  have h1 : v * D.torusPoints K r * v⁻¹ * (D.torusPoints K r)⁻¹ = 1 := by
    rw [← Subgroup.mem_bot, ← D.positivePoints_inf_range_torusPoints_eq_bot K]
    exact ⟨hU, hT⟩
  have hcomm : D.torusPoints K r * v = v * D.torusPoints K r := by
    have := congrArg (fun x => x * D.torusPoints K r * v) h1
    simpa [mul_assoc] using this.symm
  exact hcomm

/-- Over an infinite field, the actual torus is self-normalizing inside the Borel-type
subgroup. -/
@[simp]
theorem borelSubgroup_inf_normalizer_range_torusPoints :
    D.borelSubgroup K ⊓ Subgroup.normalizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  have hT : (D.torusPoints K).range ≤ Subgroup.normalizer (Set.range (D.torusPoints K)) := by
    simpa only [MonoidHom.coe_range] using (D.torusPoints K).range.le_normalizer
  rw [D.borelSubgroup_def, inf_comm,
    ← Subgroup.inf_sup_assoc_of_le
      (Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (D.range_torusPoints_le_normalizer_positivePoints K))
      hT,
    inf_comm, D.positivePoints_inf_normalizer_range_torusPoints K, bot_sup_eq]

omit [Infinite K] in
private theorem torus_conj_inversionPoints_mem (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (r : Fin t.rank → Kˣ) {u : D.points K} (hu : u ∈ D.inversionPoints K w) :
    D.torusPoints K r * u * (D.torusPoints K r)⁻¹ ∈ D.inversionPoints K w := by
  have hle : (D.inversionPoints K w).map (MulAut.conj (D.torusPoints K r)).toMonoidHom ≤
      D.inversionPoints K w := by
    rw [Subgroup.map_le_iff_le_comap, D.inversionPoints_le_iff]
    intro γ hγ a
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ofAdd_toAdd a,
      D.torusPoints_conj_rootSubgroupPoints]
    exact D.rootSubgroupPoints_mem_inversionPoints K hγ _
  exact hle ⟨u, hu, rfl⟩

private theorem torus_conj_bruhat_eq_of_mem_normalizer (n : D.weylSubgroup K)
    (u : D.inversionPoints K (D.weylProjection K n)) (b : D.borelSubgroup K)
    {g : D.points K} (hg : (u : D.points K) * (n : D.points K) * b = g)
    (hgN : g ∈ Subgroup.normalizer (Set.range (D.torusPoints K))) :
    (u : D.points K) = 1 := by
  have huC : (u : D.points K) ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    let tr := D.torusPoints K r
    have htr' : g⁻¹ * tr * g ∈ (D.torusPoints K).range := by
      have hgNinv : g⁻¹ ∈ Subgroup.normalizer (Set.range (D.torusPoints K)) :=
        Subgroup.inv_mem _ hgN
      have h := (Subgroup.mem_normalizer_iff (H := (D.torusPoints K).range).mp hgNinv tr).mp
        ⟨r, rfl⟩
      simpa only [inv_inv] using h
    have hu' : tr * (u : D.points K) * tr⁻¹ ∈
        D.inversionPoints K (D.weylProjection K n) :=
      D.torus_conj_inversionPoints_mem K (D.weylProjection K n) r u.property
    have hnt : (n : D.points K)⁻¹ * tr * (n : D.points K) ∈ (D.torusPoints K).range := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K ((D.weylSubgroup K).inv_mem n.property))
        tr).mp ⟨r, rfl⟩
      simpa only [inv_inv] using h
    have hb' : (n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
        (g⁻¹ * tr * g)⁻¹ ∈ D.borelSubgroup K :=
      (D.borelSubgroup K).mul_mem
        ((D.borelSubgroup K).mul_mem (D.range_torusPoints_le_borelSubgroup K hnt) b.property)
        ((D.borelSubgroup K).inv_mem (D.range_torusPoints_le_borelSubgroup K htr'))
    have hprod : (tr * (u : D.points K) * tr⁻¹) * (n : D.points K) *
        ((n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
          (g⁻¹ * tr * g)⁻¹) = (u : D.points K) * (n : D.points K) * b := by
      calc
        (tr * (u : D.points K) * tr⁻¹) * (n : D.points K) *
            ((n : D.points K)⁻¹ * tr * (n : D.points K) * (b : D.points K) *
              (g⁻¹ * tr * g)⁻¹)
          = tr * ((u : D.points K) * (n : D.points K) * b) * (g⁻¹ * tr * g)⁻¹ := by group
        _ = tr * g * (g⁻¹ * tr * g)⁻¹ := by rw [hg]
        _ = g := by group
        _ = (u : D.points K) * (n : D.points K) * b := hg.symm
    have heq := (D.eq_and_eq_of_mem_map_negativePoints_conj_of_mul_eq K
      (D.inversionPoints_le_map_negativePoints_conj K n hu')
      (D.inversionPoints_le_map_negativePoints_conj K n u.property)
      hb' b.property hprod).1
    exact mul_inv_eq_iff_eq_mul.mp heq
  rw [← Subgroup.mem_bot, ← D.positivePoints_inf_centralizer_range_torusPoints K]
  exact ⟨D.inversionPoints_le_positivePoints K _ u.property, huC⟩

/-- **Torus normalizer in the extended elementary Chevalley group.** Over an infinite field,
the normalizer of the actual character-lattice torus inside `D.extendedElementarySubgroup K`
is precisely the Weyl subgroup `D.weylSubgroup K`. -/
@[simp]
theorem extendedElementarySubgroup_inf_normalizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.normalizer (Set.range (D.torusPoints K)) =
      D.weylSubgroup K := by
  have hW : D.weylSubgroup K ≤ Subgroup.normalizer (Set.range (D.torusPoints K)) := by
    simpa only [MonoidHom.coe_range] using D.weylSubgroup_le_normalizer_range_torusPoints K
  apply le_antisymm
  · rintro g ⟨hgE, hgN⟩
    obtain ⟨w, hw, _⟩ := D.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup K hgE
    obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
    obtain ⟨⟨u, b⟩, hub, _⟩ := D.existsUnique_mul_mul_eq_of_mem_bruhatCell K n hw
    have hu1 : (u : D.points K) = 1 :=
      D.torus_conj_bruhat_eq_of_mem_normalizer K n u b hub hgN
    have hnb : (n : D.points K) * b = g := by simpa [hu1] using hub
    have hbN : (b : D.points K) ∈ Subgroup.normalizer (Set.range (D.torusPoints K)) := by
      have heq : (b : D.points K) = (n : D.points K)⁻¹ * g := eq_inv_mul_of_mul_eq hnb
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW n.property)) hgN
    have hbT : (b : D.points K) ∈ (D.torusPoints K).range := by
      rw [← D.borelSubgroup_inf_normalizer_range_torusPoints K]
      exact ⟨b.property, hbN⟩
    obtain ⟨s, hs⟩ := hbT
    rw [← hnb, ← hs]
    exact (D.weylSubgroup K).mul_mem n.property (D.torusPoints_mem_weylSubgroup K s)
  · exact le_inf (D.weylSubgroup_le_extendedElementarySubgroup K) hW

/-- **Torus centralizer in the extended elementary Chevalley group.** Over an infinite field,
the actual character-lattice torus is self-centralizing inside
`D.extendedElementarySubgroup K`. -/
@[simp]
theorem extendedElementarySubgroup_inf_centralizer_range_torusPoints :
    D.extendedElementarySubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  apply le_antisymm
  · rintro g ⟨hgE, hgC⟩
    have hgN : g ∈ Subgroup.normalizer (Set.range (D.torusPoints K)) :=
      Subgroup.centralizer_le_normalizer _ hgC
    have hgW : g ∈ D.weylSubgroup K := by
      rw [← D.extendedElementarySubgroup_inf_normalizer_range_torusPoints K]
      exact ⟨hgE, hgN⟩
    have hproj1 : D.weylProjection K ⟨g, hgW⟩ = 1 := by
      rw [D.weylProjection_eq_one_iff K]
      intro s
      have hc : Commute g (D.torusPoints K (D.fullWeightTorusRestriction K s)) :=
        (Subgroup.mem_centralizer_iff.mp hgC _ ⟨_, rfl⟩).symm
      simpa only [Subgroup.coe_subtype, D.coe_torusPoints, ← D.kostantTorusMatrix_weight,
        kostantTorusMatrix_apply] using hc.map (D.points K).subtype
    have hker : (⟨g, hgW⟩ : D.weylSubgroup K) ∈ (D.weylProjection K).ker := hproj1
    rwa [D.ker_weylProjection K, Subgroup.mem_subgroupOf] at hker
  · refine le_inf ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact D.torusPoints_mem_extendedElementarySubgroup K s
    · simpa only [MonoidHom.coe_range] using Subgroup.le_centralizer (D.torusPoints K).range

end InfiniteField

section Center

private theorem mem_borelSubgroup_of_mem_extendedElementarySubgroup_inf_centralizer
    {g : D.points K} (hgE : g ∈ D.extendedElementarySubgroup K)
    (hgC : g ∈ Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K))) :
    g ∈ D.borelSubgroup K := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨w, hwcell, _⟩ := D.existsUnique_mem_bruhatCell_of_mem_extendedElementarySubgroup K hgE
  obtain ⟨n, rfl⟩ := D.weylProjection_surjective K w
  rw [D.bruhatCell_weylProjection K n] at hwcell
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hwcell
  have hproj1 : D.weylProjection K n = 1 := by
    by_contra hw
    obtain ⟨γ, hγ⟩ := inversions_nonempty_of_ne_one
      (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) hw
    have hγpos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [t.posRoots_rationalRootSystem ht]
      exact inversions_subset_posRoots _ _ _ hγ
    set δ := (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K n) γ
    have hδneg : δ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [← not_mem_posRoots_iff_mem_negRoots, t.posRoots_rationalRootSystem ht,
        not_mem_posRoots_iff_mem_negRoots]
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
    have hyE : y ∈ D.elementarySubgroup K :=
      D.positivePoints_le_iff.mpr
        (fun _ _ u => D.rootSubgroupPoints_mem_elementarySubgroup K _ u) hyU
    have hcomm : y * (b₁ * (n : D.points K) * b₂) = (b₁ * (n : D.points K) * b₂) * y :=
      Subgroup.mem_centralizer_iff.mp hgC y hyE
    have hnx_eq : (n : D.points K) * x * (n : D.points K)⁻¹ = b₁⁻¹ * y * b₁ := by
      have hgy : (b₁ * (n : D.points K) * b₂) * y * (b₁ * (n : D.points K) * b₂)⁻¹ = y :=
        mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      calc
        (n : D.points K) * x * (n : D.points K)⁻¹
          = b₁⁻¹ * ((b₁ * (n : D.points K) * b₂) * (b₂⁻¹ * x * b₂) *
              (b₁ * (n : D.points K) * b₂)⁻¹) * b₁ := by group
        _ = b₁⁻¹ * y * b₁ := by rw [hgy]
    have hnxB : D.rootSubgroupPoints δ K (ofAdd 1) ∈ D.borelSubgroup K := by
      have hconj : (n : D.points K) * x * (n : D.points K)⁻¹ =
          D.rootSubgroupPoints δ K (ofAdd 1) := by
        simpa only [x, MulAut.conj_apply, Units.val_inv_eq_inv_val,
          mul_inv_cancel₀ (Units.ne_zero c)] using hc ((c⁻¹ : Kˣ) : K)
      rw [← hconj, hnx_eq]
      exact (D.borelSubgroup K).mul_mem
        ((D.borelSubgroup K).mul_mem ((D.borelSubgroup K).inv_mem hb₁)
          (D.positivePoints_le_borelSubgroup K hyU))
        hb₁
    exact D.rootSubgroupPoints_ofAdd_one_ne_one K δ
      ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hδneg _).mp hnxB)
  have hnT : (n : D.points K) ∈ (D.torusPoints K).range := by
    have : n ∈ (D.weylProjection K).ker := hproj1
    rwa [D.ker_weylProjection K, Subgroup.mem_subgroupOf] at this
  exact (D.borelSubgroup K).mul_mem
    ((D.borelSubgroup K).mul_mem hb₁ (D.range_torusPoints_le_borelSubgroup K hnT)) hb₂

private theorem map_positivePoints_conj_longestElement_le_negativePoints
    (n₀ : D.weylSubgroup K)
    (hn₀w : D.weylProjection K n₀ =
      let _ := t.isReduced_simplyConnectedRootDatum ht
      longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) :
    (D.positivePoints K).map (MulAut.conj (n₀ : D.points K)).toMonoidHom ≤
      D.negativePoints K := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  rw [D.positivePoints_eq_iSup K, D.map_iSup_rootSubgroupPoints_conj K n₀, hn₀w]
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨γ, hγpos, rfl⟩ := hδ
  rw [t.posRoots_rationalRootSystem ht] at hγpos
  have hδneg : (t.simplyConnectedRootDatum ht).weylGroupToPerm
      (longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)) γ ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [← not_mem_posRoots_iff_mem_negRoots, t.posRoots_rationalRootSystem ht,
      not_mem_posRoots_iff_mem_negRoots]
    exact mapsTo_posRoots_negRoots_longestElement _ _ hγpos
  rintro _ ⟨a, rfl⟩
  exact D.rootSubgroupPoints_mem_negativePoints K hδneg a

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
    obtain ⟨u, huU, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    let w₀ := longestElement (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    obtain ⟨n₀, hn₀E, hn₀w⟩ := D.exists_mem_elementarySubgroup_weylProjection_eq K w₀
    have hconj_u : (n₀ : D.points K) * u * (n₀ : D.points K)⁻¹ ∈ D.negativePoints K :=
      D.map_positivePoints_conj_longestElement_le_negativePoints K n₀ hn₀w ⟨u, huU, rfl⟩
    have hconj_t : (n₀ : D.points K) * D.torusPoints K s * (n₀ : D.points K)⁻¹ ∈
        (D.torusPoints K).range :=
      (Subgroup.mem_normalizer_iff.mp
        (D.weylSubgroup_le_normalizer_range_torusPoints K n₀.property) (D.torusPoints K s)).mp
          ⟨s, rfl⟩
    have hcomm : (n₀ : D.points K) * (u * D.torusPoints K s) * (n₀ : D.points K)⁻¹ =
        u * D.torusPoints K s :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hgC n₀ hn₀E)
    have hu_eq : u = ((n₀ : D.points K) * u * (n₀ : D.points K)⁻¹) *
        (((n₀ : D.points K) * D.torusPoints K s * (n₀ : D.points K)⁻¹) *
          (D.torusPoints K s)⁻¹) := by
      have h := congrArg (fun x => x * (D.torusPoints K s)⁻¹) hcomm
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
    subst hu1
    rw [one_mul] at hgC ⊢
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

/-- Over every field `K`, the centre of `D.extendedElementarySubgroup K` embeds into `D.points K`
as the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_extendedElementarySubgroup :
    (Subgroup.center (D.extendedElementarySubgroup K)).map
        (D.extendedElementarySubgroup K).subtype =
      (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) := by
  rw [← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]
  apply le_antisymm
  · rintro _ ⟨⟨g, hgE⟩, hgZ, rfl⟩
    refine ⟨hgE, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hgZ ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup K he⟩)
  · rintro g ⟨hgE, hgC⟩
    have hgRT : g ∈ Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) :=
      ((D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K).le ⟨hgE, hgC⟩).2
    refine ⟨⟨g, hgE⟩, Subgroup.mem_center_iff.mpr fun ⟨h, hh⟩ => Subtype.ext ?_, rfl⟩
    rw [D.extendedElementarySubgroup_eq_rootTorusSubgroup K] at hh
    exact Subgroup.mem_centralizer_iff.mp hgRT h hh

/-- Over every field `K`, the centre of `D.elementarySubgroup K` consists of the elementary
points lying in the toral centralizer `T(K) ∩ C(D.rootTorusSubgroup K)`. -/
theorem map_center_elementarySubgroup :
    (Subgroup.center (D.elementarySubgroup K)).map (D.elementarySubgroup K).subtype =
      D.elementarySubgroup K ⊓
        ((D.torusPoints K).range ⊓
          Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hgE₀⟩, hgZ, rfl⟩
    have hgInf : g ∈ D.extendedElementarySubgroup K ⊓
        Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) :=
      ⟨D.elementarySubgroup_le_extendedElementarySubgroup K hgE₀,
        Subgroup.mem_centralizer_iff.mpr fun e he =>
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hgZ ⟨e, he⟩)⟩
    exact ⟨hgE₀, (D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K).le hgInf⟩
  · rintro g ⟨hgE₀, _, hgC⟩
    refine ⟨⟨g, hgE₀⟩, Subgroup.mem_center_iff.mpr fun ⟨e, he⟩ => Subtype.ext ?_, rfl⟩
    apply Subgroup.mem_centralizer_iff.mp hgC e
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K]
    exact D.elementarySubgroup_le_extendedElementarySubgroup K he

/-- **Centre of an extended elementary Chevalley group.** Over every field `K` and for every
Chevalley datum `D`, unit-valued characters of `Λ(D) / Q` (in the chosen basis of `Λ(D)`)
canonically identify with `Subgroup.center (D.extendedElementarySubgroup K)`. -/
def centerExtendedElementarySubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup K) :=
  (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K)).trans
    ((MulEquiv.subgroupCongr (D.map_center_extendedElementarySubgroup K).symm).trans
      ((Subgroup.center (D.extendedElementarySubgroup K)).equivMapOfInjective
        (D.extendedElementarySubgroup K).subtype Subtype.val_injective).symm)

/-- The forward equivalence sends a character of `Λ(D) / Q` to the corresponding torus point. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv K χ : D.extendedElementarySubgroup K) :
        D.points K) =
      D.torusPoints K (quotientCharTorusPoint _ χ) := by
  let e := (Subgroup.center (D.extendedElementarySubgroup K)).equivMapOfInjective
    (D.extendedElementarySubgroup K).subtype Subtype.val_injective
  have h1 : ((D.centerExtendedElementarySubgroupEquiv K χ : D.extendedElementarySubgroup K) :
        D.points K) =
      (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K) χ :
        D.points K) :=
    congrArg Subtype.val (e.apply_symm_apply
      ((MulEquiv.subgroupCongr (D.map_center_extendedElementarySubgroup K).symm)
        (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K) χ)))
  exact h1.trans (D.coe_torusInfCentralizerRootTorusSubgroupEquiv K
    (D.rootSubgroupPoints_injective K) χ)

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
  have hcoord : quotientCharTorusPoint _
      ((D.centerExtendedElementarySubgroupEquiv K).symm
        ⟨⟨D.torusPoints K s, D.torusPoints_mem_extendedElementarySubgroup K s⟩, hg⟩) = s := by
    apply D.torusPoints_injective K
    rw [← D.coe_centerExtendedElementarySubgroupEquiv K, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end Center

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
  rw [ChevalleyDatum.map_center_elementarySubgroup,
    ← t.scChevalleyDatum_extendedElementarySubgroup ht K, inf_eq_right]
  refine inf_le_left.trans ?_
  rintro _ ⟨s, rfl⟩
  exact (t.scChevalleyDatum ht).torusPoints_mem_extendedElementarySubgroup K s

/-- **Centre of the simply connected Chevalley group.** Over every field `K`, unit-valued
characters of `P / Q` canonically identify with the centre of
`(t.scChevalleyDatum ht).elementarySubgroup K`. -/
def scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K] :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) :=
  (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht K).trans
    ((MulEquiv.subgroupCongr (t.map_center_scChevalleyDatum_elementarySubgroup ht K).symm).trans
      ((Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K)).equivMapOfInjective
        ((t.scChevalleyDatum ht).elementarySubgroup K).subtype Subtype.val_injective).symm)

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point. -/
@[simp]
theorem coe_scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K]
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ) :
    ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).elementarySubgroup K) : (t.scChevalleyDatum ht).points K) =
      (t.scChevalleyDatum ht).torusPoints K (quotientCharTorusPoint _ χ) := by
  let e := (Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K)).equivMapOfInjective
    ((t.scChevalleyDatum ht).elementarySubgroup K).subtype Subtype.val_injective
  have h1 : ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).elementarySubgroup K) : (t.scChevalleyDatum ht).points K) =
      (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).points K) :=
    congrArg Subtype.val (e.apply_symm_apply
      ((MulEquiv.subgroupCongr (t.map_center_scChevalleyDatum_elementarySubgroup ht K).symm)
        (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht K χ)))
  exact h1.trans (t.coe_scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht K χ)

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
  have hcoord : quotientCharTorusPoint _
      ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K).symm
        ⟨⟨(t.scChevalleyDatum ht).torusPoints K s, hs⟩, hg⟩) = s := by
    apply (t.scChevalleyDatum ht).torusPoints_injective K
    rw [← t.coe_scChevalleyDatumCenterElementarySubgroupEquiv ht K, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end

end TauCeti.DynkinType
