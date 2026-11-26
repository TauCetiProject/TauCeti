/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.CompleteSublattice
public import TauCeti.Algebra.Group.Subgroup.ModularLaw

/-!
# The lattice of normal subgroups

The normal subgroups of a group `G` are closed under arbitrary joins and meets in `Subgroup G`, so
they form a complete sublattice `TauCeti.normalSubgroups G`; its underlying type is
`TauCeti.NormalSubgroup G`. Unlike `Subgroup G`, which is not modular in general, this lattice
satisfies Dedekind's modular law, because the join of two normal subgroups is their product set.
This is what makes Mathlib's Jordan–Hölder theory of `CompositionSeries` apply to series of normal
subgroups of `G`, that is, to chief series.

The coercion `NormalSubgroup G → Subgroup G` is the complete lattice embedding
`(TauCeti.normalSubgroups G).subtype`, so it preserves `⊔`, `⊓`, `⊥` and `⊤`. The atoms of
`NormalSubgroup G` are the minimal normal subgroups of `G` and its coatoms are the normal
subgroups with simple quotient.

## Main definitions

* `TauCeti.normalSubgroups G`: the complete sublattice of normal subgroups of `G`.
* `TauCeti.NormalSubgroup G`: the complete lattice of normal subgroups of `G`.
* `Subgroup.IsMinimalNormal`: a nontrivial normal subgroup containing no normal subgroup of the
  ambient group other than `⊥` and itself.

## Main results

* `Subgroup.isMinimalNormal_top_iff`: the whole group is minimal normal exactly when it is simple.
* `Subgroup.exists_isMinimalNormal_le`: a nontrivial finite normal subgroup contains a minimal
  normal subgroup.
* `Subgroup.IsMinimalNormal.map_mulEquiv`: minimal normality is transported by isomorphisms.
* `Subgroup.IsMinimalNormal.disjoint_of_ne`, `Subgroup.IsMinimalNormal.commute_of_ne`: two distinct
  minimal normal subgroups intersect trivially and commute elementwise.
* `TauCeti.NormalSubgroup.instIsModularLattice`: the normal subgroups form a modular lattice.
* `TauCeti.NormalSubgroup.isAtom_iff_isMinimalNormal`: the atoms of `NormalSubgroup G` are the
  minimal normal subgroups.
* `TauCeti.NormalSubgroup.isCoatom_iff_isSimpleGroup`: the coatoms of `NormalSubgroup G` are the
  normal subgroups with simple quotient.
-/

public section

open Subgroup

variable {G : Type*} [Group G]

/-- A **minimal normal subgroup** of `G`: a nontrivial normal subgroup of `G` containing no normal
subgroup of `G` other than `⊥` and itself. -/
def Subgroup.IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M ≤ N, M.Normal → M = ⊥ ∨ M = N

theorem Subgroup.isMinimalNormal_iff {N : Subgroup G} :
    N.IsMinimalNormal ↔ N.Normal ∧ N ≠ ⊥ ∧ ∀ M ≤ N, M.Normal → M = ⊥ ∨ M = N :=
  Iff.rfl

namespace Subgroup.IsMinimalNormal

variable {N M : Subgroup G}

theorem normal (hN : N.IsMinimalNormal) : N.Normal :=
  (isMinimalNormal_iff.1 hN).1

theorem ne_bot (hN : N.IsMinimalNormal) : N ≠ ⊥ :=
  (isMinimalNormal_iff.1 hN).2.1

/-- A normal subgroup of `G` contained in a minimal normal subgroup `N` is `⊥` or `N`. -/
theorem eq_bot_or_eq (hN : N.IsMinimalNormal) (hM : M.Normal) (hMN : M ≤ N) : M = ⊥ ∨ M = N :=
  (isMinimalNormal_iff.1 hN).2.2 M hMN hM

/-- The image of a minimal normal subgroup under a group isomorphism is minimal normal. -/
theorem map_mulEquiv {G' : Type*} [Group G'] (hN : N.IsMinimalNormal) (e : G ≃* G') :
    (N.map (e : G →* G')).IsMinimalNormal := by
  have := hN.normal
  refine isMinimalNormal_iff.2 ⟨this.map _ e.surjective,
    (map_eq_bot_iff_of_injective _ e.injective).not.2 hN.ne_bot, fun M hM hMn ↦ ?_⟩
  -- Pull `M` back along `e`, apply minimality of `N` there, and push forward again.
  have hM' : M.map (e.symm : G' →* G) ≤ N := by
    simpa [map_map] using map_mono (f := (e.symm : G' →* G)) hM
  have hback : (M.map (e.symm : G' →* G)).map (e : G →* G') = M := by
    simp [map_map]
  rcases hN.eq_bot_or_eq (hMn.map _ e.symm.surjective) hM' with h | h
  · exact Or.inl (by rw [← hback, h, Subgroup.map_bot])
  · exact Or.inr (by rw [← hback, h])

/-- A minimal normal subgroup `N` either lies in a normal subgroup `M` or meets it trivially. -/
theorem le_or_disjoint (hN : N.IsMinimalNormal) (hM : M.Normal) : N ≤ M ∨ Disjoint N M := by
  have := hN.normal
  rcases hN.eq_bot_or_eq (normal_inf_normal N M) inf_le_left with h | h
  · exact Or.inr (disjoint_iff.2 h)
  · exact Or.inl (inf_eq_left.1 h)

/-- Two distinct minimal normal subgroups intersect trivially. -/
theorem disjoint_of_ne (hN : N.IsMinimalNormal) (hM : M.IsMinimalNormal) (hne : N ≠ M) :
    Disjoint N M :=
  (hN.le_or_disjoint hM.normal).resolve_left fun hle ↦
    hne <| (hM.eq_bot_or_eq hN.normal hle).resolve_left hN.ne_bot

/-- Two distinct minimal normal subgroups commute elementwise. -/
theorem commute_of_ne (hN : N.IsMinimalNormal) (hM : M.IsMinimalNormal) (hne : N ≠ M) {x y : G}
    (hx : x ∈ N) (hy : y ∈ M) : Commute x y :=
  commute_of_normal_of_disjoint N M hN.normal hM.normal (hN.disjoint_of_ne hM hne) x y hx hy

end Subgroup.IsMinimalNormal

/-- The whole group is a minimal normal subgroup of itself exactly when it is a simple group. -/
theorem Subgroup.isMinimalNormal_top_iff : (⊤ : Subgroup G).IsMinimalNormal ↔ IsSimpleGroup G := by
  refine ⟨fun h ↦ ?_, fun h ↦ isMinimalNormal_iff.2 ⟨normal_top, top_ne_bot, fun M _ _ ↦
    IsSimpleGroup.eq_bot_or_eq_top_of_normal M⟩⟩
  have : Nontrivial G := nontrivial_iff.1 (nontrivial_of_ne _ _ h.ne_bot)
  exact ⟨fun M hM ↦ h.eq_bot_or_eq hM le_top⟩

namespace TauCeti

variable (G) in
/-- The normal subgroups of `G`, as a complete sublattice of `Subgroup G`: arbitrary joins and
meets of normal subgroups are normal. -/
def normalSubgroups : CompleteSublattice (Subgroup G) :=
  CompleteSublattice.mk' {N | N.Normal} (fun s hs ↦ sSup_normal s hs) fun s hs ↦ by
    rw [sInf_eq_iInf']
    exact normal_iInf_normal fun N : s ↦ hs N.property

@[simp]
theorem mem_normalSubgroups {N : Subgroup G} : N ∈ normalSubgroups G ↔ N.Normal :=
  Iff.rfl

variable (G) in
/-- The complete lattice of normal subgroups of `G`, ordered by inclusion. -/
abbrev NormalSubgroup : Type _ :=
  normalSubgroups G

namespace NormalSubgroup

/-- The underlying subgroup of a member of `NormalSubgroup G` is normal. -/
instance (N : NormalSubgroup G) : (N : Subgroup G).Normal :=
  N.property

@[simp, norm_cast]
theorem coe_sup (M N : NormalSubgroup G) :
    ((M ⊔ N : NormalSubgroup G) : Subgroup G) = (M : Subgroup G) ⊔ N :=
  rfl

@[simp, norm_cast]
theorem coe_inf (M N : NormalSubgroup G) :
    ((M ⊓ N : NormalSubgroup G) : Subgroup G) = (M : Subgroup G) ⊓ N :=
  rfl

@[simp, norm_cast]
theorem coe_finset_sup {ι : Type*} (s : Finset ι) (f : ι → NormalSubgroup G) :
    ((s.sup f : NormalSubgroup G) : Subgroup G) = s.sup fun i ↦ (f i : Subgroup G) :=
  map_finset_sup (normalSubgroups G).subtype s f

/-- **Dedekind's modular law** for normal subgroups: for normal `A ≤ C` and normal `B`,
`(A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)`. -/
instance instIsModularLattice : IsModularLattice (NormalSubgroup G) where
  sup_inf_le_assoc_of_le {_} B {_} h :=
    Subtype.coe_le_coe.mp (sup_inf_assoc_of_le_of_normal (B : Subgroup G) h).le

/-- The atoms of the lattice of normal subgroups are the minimal normal subgroups. -/
theorem isAtom_iff_isMinimalNormal {N : NormalSubgroup G} :
    IsAtom N ↔ (N : Subgroup G).IsMinimalNormal := by
  refine ⟨fun h ↦ ⟨N.property, fun h0 ↦ h.1 (Subtype.ext h0), fun M hM hMn ↦ ?_⟩, fun h ↦
    ⟨fun h0 ↦ h.2.1 congr(Subtype.val $h0), fun M hM ↦ Subtype.ext <|
      (h.2.2 M hM.le M.property).resolve_right fun e ↦ hM.ne (Subtype.ext e)⟩⟩
  let M' : NormalSubgroup G := ⟨M, hMn⟩
  obtain e | lt := eq_or_lt_of_le (Subtype.coe_le_coe.mp hM : M' ≤ N)
  · exact Or.inr congr(Subtype.val $e)
  · exact Or.inl congr(Subtype.val $(h.2 M' lt))

/-- The coatoms of the lattice of normal subgroups are the normal subgroups with simple
quotient. -/
theorem isCoatom_iff_isSimpleGroup {N : NormalSubgroup G} :
    IsCoatom N ↔ IsSimpleGroup (G ⧸ (N : Subgroup G)) := by
  set π := QuotientGroup.mk' (N : Subgroup G)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun hN ↦ ?_, fun M hM ↦ ?_⟩⟩
  · -- A normal subgroup `H` of the quotient pulls back to a normal subgroup containing `N`.
    have := QuotientGroup.nontrivial_iff.mpr fun hN ↦ h.1 (Subtype.ext hN)
    refine ⟨fun H hH ↦ ?_⟩
    let K : NormalSubgroup G := ⟨H.comap π, mem_normalSubgroups.mpr (hH.comap π)⟩
    have hle : N ≤ K := by
      rw [← Subtype.coe_le_coe, ← QuotientGroup.ker_mk' (N : Subgroup G)]
      exact ker_le_comap π H
    rw [← map_comap_eq_self_of_surjective hsurj H]
    obtain e | lt := eq_or_lt_of_le hle
    · have hK : H.comap π = N := congr(Subtype.val $e.symm)
      exact Or.inl (by rw [hK, QuotientGroup.map_mk'_self])
    · have hK : H.comap π = ⊤ := congr(Subtype.val $(h.2 K lt))
      exact Or.inr (by rw [hK, map_top_of_surjective π hsurj])
  · exact QuotientGroup.nontrivial_iff.mp h.toNontrivial congr(Subtype.val $hN)
  · -- A normal subgroup `M` strictly above `N` maps onto the whole simple quotient.
    have hMN : (N : Subgroup G) < M := Subtype.coe_lt_coe.mpr hM
    have hMn : ((M : Subgroup G).map π).Normal := Normal.map inferInstance π hsurj
    obtain h0 | htop := hMn.eq_bot_or_eq_top
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
      exact absurd h0 (not_le_of_gt hMN)
    · have := comap_map_eq π (M : Subgroup G)
      rw [htop, comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hMN.le] at this
      exact Subtype.ext this.symm

end NormalSubgroup

end TauCeti

open TauCeti in
/-- A nontrivial finite normal subgroup `M`, for instance any nontrivial normal subgroup of a
finite group, contains a minimal normal subgroup. -/
theorem Subgroup.exists_isMinimalNormal_le {M : Subgroup G} [M.Normal] [Finite M] (hM : M ≠ ⊥) :
    ∃ N : Subgroup G, N.IsMinimalNormal ∧ N ≤ M := by
  -- The normal subgroups of `G` below `M` form a finite, hence atomic, lattice, whose atoms are
  -- minimal normal subgroups of `G`.
  let M' : NormalSubgroup G := ⟨M, ‹M.Normal›⟩
  have hle (K : Set.Iic M') : ((K : NormalSubgroup G) : Subgroup G) ≤ M := K.property
  have : Finite (Set.Iic M') := Finite.of_injective
    (fun K : Set.Iic M' ↦ ((K : NormalSubgroup G) : Subgroup G).subgroupOf M) fun K L h ↦ by
      rw [subgroupOf_inj, inf_of_le_left (hle K), inf_of_le_left (hle L)] at h
      exact Subtype.ext (Subtype.ext h)
  obtain ⟨A, hA, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Set.Iic M')).resolve_left fun h ↦
    hM congr(Subtype.val (Subtype.val $h))
  exact ⟨_, NormalSubgroup.isAtom_iff_isMinimalNormal.1 hA.of_isAtom_coe_Iic, hle A⟩
