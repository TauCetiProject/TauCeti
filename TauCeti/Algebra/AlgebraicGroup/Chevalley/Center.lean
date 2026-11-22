/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Center
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Bruhat.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injectivity
import TauCeti.Algebra.Group.Subgroup.Map
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
* `ChevalleyDatum.mem_center_extendedElementarySubgroup_iff`,
  `ChevalleyDatum.mem_center_elementarySubgroup_iff`,
  `ChevalleyDatum.torusPoints_mem_center_extendedElementarySubgroup_iff`, and
  `ChevalleyDatum.torusPoints_mem_center_elementarySubgroup_iff`: centre membership criteria for
  arbitrary points and `@[simp]` criteria for torus points in terms of coordinate root characters.
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

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

universe v

private def equivSubgroupOfMapEq {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {A : Subgroup G} {B : Subgroup H}
    (h : A.map f = B) : B ≃* A :=
  (MulEquiv.subgroupCongr h.symm).trans (A.equivMapOfInjective f hf).symm

private theorem coe_equivSubgroupOfMapEq_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {A : Subgroup G} {B : Subgroup H}
    (h : A.map f = B) (y : B) :
    f (equivSubgroupOfMapEq f hf h y : G) = (y : H) := by
  rw [equivSubgroupOfMapEq, MulEquiv.trans_apply, Subgroup.apply_coe_equivMapOfInjective_symm,
    MulEquiv.subgroupCongr_apply]

private theorem coe_equivSubgroupOfMapEq_symm_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {A : Subgroup G} {B : Subgroup H}
    (h : A.map f = B) (x : A) :
    ((equivSubgroupOfMapEq f hf h).symm x : H) = f (x : G) := by
  rw [equivSubgroupOfMapEq, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.subgroupCongr_symm_apply, Subgroup.coe_equivMapOfInjective_apply]

variable {t : DynkinType} {ht : t.Valid}

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht) (K : Type v) [Field K]

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
    refine ⟨⟨s, rfl⟩, ?_⟩
    rw [← D.extendedElementarySubgroup_eq_rootTorusSubgroup K, D.extendedElementarySubgroup_def K,
      Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    exact (Set.centralizer_union
      (S := (D.elementarySubgroup K : Set (D.points K)))
      (T := ((D.torusPoints K).range : Set (D.points K)))).ge
      ⟨hgC, Subgroup.le_centralizer _ ⟨s, rfl⟩⟩
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
  rw [Subgroup.map_center_subtype,
    ← D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]
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
  calc
    (Subgroup.center (D.elementarySubgroup K)).map (D.elementarySubgroup K).subtype
      = D.elementarySubgroup K ⊓
          Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) :=
        Subgroup.map_center_subtype _
    _ = (D.elementarySubgroup K ⊓ D.extendedElementarySubgroup K) ⊓
          Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K)) := by
        rw [inf_eq_left.mpr (D.elementarySubgroup_le_extendedElementarySubgroup K)]
    _ = D.elementarySubgroup K ⊓
          (D.extendedElementarySubgroup K ⊓
            Subgroup.centralizer (D.elementarySubgroup K : Set (D.points K))) :=
        inf_assoc _ _ _
    _ = D.elementarySubgroup K ⊓
          ((D.torusPoints K).range ⊓
            Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K))) := by
        rw [D.extendedElementarySubgroup_inf_centralizer_elementarySubgroup K]

private theorem mem_range_torusPoints_inf_centralizer_rootTorusSubgroup_iff (g : D.points K) :
    g ∈ (D.torusPoints K).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup K : Set (D.points K)) ↔
      ∃ s : Fin t.rank → Kˣ,
        g = D.torusPoints K s ∧
          ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨s, rfl⟩, hC⟩
    exact ⟨s, rfl, (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff
      (D.rootSubgroupPoints_injective K) s).mp hC⟩
  · rintro ⟨s, rfl, hχ⟩
    exact ⟨⟨s, rfl⟩, (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff
      (D.rootSubgroupPoints_injective K) s).mpr hχ⟩

/-- Over every field `K`, an arbitrary point of `D.extendedElementarySubgroup K` lies in the
centre if and only if its ambient point is `D.torusPoints K s` for some parameter `s` on which
every coordinate root character vanishes. -/
theorem mem_center_extendedElementarySubgroup_iff (g : D.extendedElementarySubgroup K) :
    g ∈ Subgroup.center (D.extendedElementarySubgroup K) ↔
      ∃ s : Fin t.rank → Kˣ,
        (g : D.points K) = D.torusPoints K s ∧
          ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [← Subgroup.mem_map_iff_mem (D.extendedElementarySubgroup K).subtype_injective,
    D.map_center_extendedElementarySubgroup K, Subgroup.coe_subtype]
  exact D.mem_range_torusPoints_inf_centralizer_rootTorusSubgroup_iff K _

/-- Over every field `K`, an arbitrary point of `D.elementarySubgroup K` lies in the centre if and
only if its ambient point is `D.torusPoints K s` for some parameter `s` on which every coordinate
root character vanishes. -/
theorem mem_center_elementarySubgroup_iff (g : D.elementarySubgroup K) :
    g ∈ Subgroup.center (D.elementarySubgroup K) ↔
      ∃ s : Fin t.rank → Kˣ,
        (g : D.points K) = D.torusPoints K s ∧
          ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  rw [← Subgroup.mem_map_iff_mem (D.elementarySubgroup K).subtype_injective,
    D.map_center_elementarySubgroup K, Subgroup.coe_subtype, Subgroup.mem_inf,
    and_iff_right g.property]
  exact D.mem_range_torusPoints_inf_centralizer_rootTorusSubgroup_iff K _

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

private theorem torusCharacter_symm_apply_mk {M : Submodule ℤ (Fin t.rank → ℤ)}
    {G : Subgroup (D.points K)}
    (e : AddChar ((Fin t.rank → ℤ) ⧸ M) Kˣ ≃* Subgroup.center G)
    (hcoe : ∀ χ, ((e χ : G) : D.points K) = D.torusPoints K (quotientCharTorusPoint M χ))
    (s : Fin t.rank → Kˣ) (hs : D.torusPoints K s ∈ G)
    (hg : (⟨D.torusPoints K s, hs⟩ : G) ∈ Subgroup.center G) (μ : Fin t.rank → ℤ) :
    e.symm ⟨⟨D.torusPoints K s, hs⟩, hg⟩ (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint M (e.symm ⟨⟨D.torusPoints K s, hs⟩, hg⟩) = s := by
    apply D.torusPoints_injective K
    rw [← hcoe, MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

/-- **Centre of an extended elementary Chevalley group.** Over every field `K` and for every
Chevalley datum `D`, unit-valued characters of `Λ(D) / Q` (in the chosen basis of `Λ(D)`)
canonically identify with `Subgroup.center (D.extendedElementarySubgroup K)`. -/
def centerExtendedElementarySubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ ≃*
      Subgroup.center (D.extendedElementarySubgroup K) :=
  (D.torusInfCentralizerRootTorusSubgroupEquiv K (D.rootSubgroupPoints_injective K)).trans
    (equivSubgroupOfMapEq (D.extendedElementarySubgroup K).subtype
      (D.extendedElementarySubgroup K).subtype_injective
      (D.map_center_extendedElementarySubgroup K))

/-- The forward equivalence sends a character of `Λ(D) / Q` to the corresponding torus point. -/
@[simp]
theorem coe_centerExtendedElementarySubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Kˣ) :
    ((D.centerExtendedElementarySubgroupEquiv K χ : D.extendedElementarySubgroup K) :
        D.points K) =
      D.torusPoints K (quotientCharTorusPoint _ χ) := by
  rw [centerExtendedElementarySubgroupEquiv, MulEquiv.trans_apply, ← Subgroup.coe_subtype,
    coe_equivSubgroupOfMapEq_apply, D.coe_torusInfCentralizerRootTorusSubgroupEquiv K]

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
      (Submodule.Quotient.mk μ) = torusCharacter s μ :=
  D.torusCharacter_symm_apply_mk K (D.centerExtendedElementarySubgroupEquiv K)
    (D.coe_centerExtendedElementarySubgroupEquiv K) s
    (D.torusPoints_mem_extendedElementarySubgroup K s) hg μ

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

/-- **Centre of the simply connected Chevalley group.** Over every field `K`, unit-valued
characters of `P / Q` canonically identify with the centre of
`(t.scChevalleyDatum ht).elementarySubgroup K`. -/
def scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K] :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ ≃*
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K) :=
  (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht K).trans
    (equivSubgroupOfMapEq ((t.scChevalleyDatum ht).elementarySubgroup K).subtype
      ((t.scChevalleyDatum ht).elementarySubgroup K).subtype_injective
      (t.map_center_scChevalleyDatum_elementarySubgroup ht K))

/-- The simply connected centre equivalence sends a character of `P / Q` to the corresponding
torus point. -/
@[simp]
theorem coe_scChevalleyDatumCenterElementarySubgroupEquiv (K : Type v) [Field K]
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Kˣ) :
    ((t.scChevalleyDatumCenterElementarySubgroupEquiv ht K χ :
        (t.scChevalleyDatum ht).elementarySubgroup K) : (t.scChevalleyDatum ht).points K) =
      (t.scChevalleyDatum ht).torusPoints K (quotientCharTorusPoint _ χ) := by
  rw [scChevalleyDatumCenterElementarySubgroupEquiv, MulEquiv.trans_apply,
    ← Subgroup.coe_subtype, coe_equivSubgroupOfMapEq_apply,
    coe_scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv]

/-- The inverse simply connected centre equivalence evaluates a weight class by the character
of the given torus parameter. -/
@[simp]
theorem scChevalleyDatumCenterElementarySubgroupEquiv_symm_apply_mk (K : Type v) [Field K]
    (s : Fin t.rank → Kˣ)
    (hg : (⟨(t.scChevalleyDatum ht).torusPoints K s,
        t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s⟩ :
        (t.scChevalleyDatum ht).elementarySubgroup K) ∈
      Subgroup.center ((t.scChevalleyDatum ht).elementarySubgroup K))
    (μ : Fin t.rank → ℤ) :
    (t.scChevalleyDatumCenterElementarySubgroupEquiv ht K).symm
      ⟨⟨(t.scChevalleyDatum ht).torusPoints K s,
        t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s⟩, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ :=
  (t.scChevalleyDatum ht).torusCharacter_symm_apply_mk K
    (t.scChevalleyDatumCenterElementarySubgroupEquiv ht K)
    (t.coe_scChevalleyDatumCenterElementarySubgroupEquiv ht K) s
    (t.scChevalleyDatum_torusPoints_mem_elementarySubgroup ht K s) hg μ

end

end TauCeti.DynkinType
