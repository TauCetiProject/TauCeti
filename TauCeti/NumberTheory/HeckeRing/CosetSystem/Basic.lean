/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Card
public import TauCeti.GroupTheory.DoubleCoset.Basic
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.NumberTheory.HeckeRing.Basic

/-!
# Coset systems of a double coset

Let `H` and `K` be subgroups of a group `G` and `g : G`. The double coset `HgK` is a union of left
cosets `xK`, and a *coset system* for `HgK` is an indexed family `reps : ι → G` naming each of
these left cosets exactly once:

* every `reps i` lies in `HgK`;
* the cosets `reps i • K` cover `HgK`;
* the map `i ↦ reps i • K` (that is, `i ↦ (reps i : G ⧸ K)`) is injective.

Equivalently, `HgK = ⊔ᵢ reps i • K` is a disjoint union (`Subgroup.isCosetSystem_iff`), or the
classes `(reps i : G ⧸ K)` enumerate the image of `HgK` in `G ⧸ K` without repetition
(`Subgroup.isCosetSystem_iff_injective_and_range_eq`). The predicate depends only on the classes
of the representatives modulo `K` and on the double coset, not on the chosen `g`, and it is
stable under reindexing. Any two coset systems are matched by a bijection of their index types,
so their number of members is the relative index `[H : H ∩ gKg⁻¹]`
(`Subgroup.IsCosetSystem.natCard_eq_relIndex`).

The decomposition `HgK = ⋃ᵢ σᵢ g K` over representatives `σᵢ` of `H ⧸ (H ∩ gKg⁻¹)`
(`DoubleCoset.doubleCoset_eq_iUnion_leftCosets`) is a coset system
(`Subgroup.isCosetSystem_out_mul`), so coset systems always exist. When `HgK` contains only finitely
many left cosets of `K` there is one indexed by a `Fin`; for a Hecke triple `(H, Δ, K)` this holds
for every double coset `D`, with exactly `D.degree` members.

Coset systems index the sums `a ↦ ∑ᵢ ρ(reps i) a` defining Hecke operators on `K`-invariant
vectors of a representation `ρ`, and they compute the measure of a double coset for a
left-invariant measure (`TauCeti.NumberTheory.HeckeRing.CosetSystem.Volume`).

## Main definitions

* `Subgroup.IsCosetSystem H K g reps`: `reps` names each left coset of `K` in `HgK` exactly once.
* `Subgroup.IsCosetSystem.equivCosets`: the bijection between the index type of a coset system
  and the set of left cosets of `K` contained in `HgK`.

## Main results

* `Subgroup.isCosetSystem_iff`: the disjoint-union characterization.
* `Subgroup.isCosetSystem_iff_injective_and_range_eq`: the characterization by the classes in
  `G ⧸ K`.
* `Subgroup.isCosetSystem_congr`, `Subgroup.IsCosetSystem.mul_right`: changing representatives
  within their cosets; `Subgroup.isCosetSystem_comp_equiv_iff`: reindexing;
  `Subgroup.isCosetSystem_congr_of_mem`: changing the representative `g` of the double coset.
* `Subgroup.isCosetSystem_out_mul`: the canonical coset system indexed by `H ⧸ (H ∩ gKg⁻¹)`.
* `Subgroup.IsCosetSystem.natCard_eq_relIndex`: a coset system has `[H : H ∩ gKg⁻¹]` members.
* `Subgroup.exists_isCosetSystem_fin_of_finite`, `HeckeCoset.exists_isCosetSystem_fin_degree`:
  existence of finite coset systems, in particular for a Hecke triple, where
  `Subgroup.IsCosetSystem.natCard_eq_degree` counts the members by the degree.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1.
-/

public section

open scoped Pointwise

open DoubleCoset Function

variable {G : Type*} [Group G]

namespace Subgroup

variable {H K : Subgroup G} {g : G} {ι ι' : Type*} {reps : ι → G}

/-- A **coset system** for the double coset `HgK`: a family `reps : ι → G` naming each left coset
`xK` contained in `HgK` exactly once. Each `reps i` lies in `HgK`, the cosets `reps i • K` cover
`HgK`, and distinct indices give distinct cosets. -/
structure IsCosetSystem (H K : Subgroup G) (g : G) (reps : ι → G) : Prop where
  /-- Each representative lies in the double coset `HgK`. -/
  mem_doubleCoset (i : ι) : reps i ∈ doubleCoset g H K
  /-- The left cosets `reps i • K` cover the double coset `HgK`. -/
  doubleCoset_subset_iUnion : doubleCoset g H K ⊆ ⋃ i, reps i • (K : Set G)
  /-- Distinct indices name distinct left cosets of `K`. -/
  injective : Function.Injective fun i ↦ (reps i : G ⧸ K)

namespace IsCosetSystem

/-- The left cosets of a coset system lie in the double coset. -/
theorem smul_subset (h : IsCosetSystem H K g reps) (i : ι) :
    reps i • (K : Set G) ⊆ doubleCoset g H K := by
  rintro _ ⟨k, hk, rfl⟩
  exact mul_mem_doubleCoset_of_mem_right (h.mem_doubleCoset i) hk

/-- A coset system decomposes the double coset: `HgK = ⋃ᵢ reps i • K`. -/
theorem iUnion_smul_eq (h : IsCosetSystem H K g reps) :
    ⋃ i, reps i • (K : Set G) = doubleCoset g H K :=
  (Set.iUnion_subset h.smul_subset).antisymm h.doubleCoset_subset_iUnion

/-- The left cosets of a coset system are pairwise disjoint. -/
theorem pairwise_disjoint (h : IsCosetSystem H K g reps) :
    Pairwise (Disjoint on fun i ↦ reps i • (K : Set G)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj ↦ hij (h.injective ?_)
  rw [mem_leftCoset_iff] at hxi hxj
  have hK : (reps i)⁻¹ * x * ((reps j)⁻¹ * x)⁻¹ ∈ K := K.mul_mem hxi (K.inv_mem hxj)
  exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hK)

end IsCosetSystem

/-- **The disjoint-union characterization of a coset system**: `reps` is a coset system for `HgK`
exactly when `HgK` is the disjoint union of the left cosets `reps i • K`. -/
theorem isCosetSystem_iff :
    IsCosetSystem H K g reps ↔
      ⋃ i, reps i • (K : Set G) = doubleCoset g H K ∧
        Pairwise (Disjoint on fun i ↦ reps i • (K : Set G)) := by
  refine ⟨fun h ↦ ⟨h.iUnion_smul_eq, h.pairwise_disjoint⟩, fun ⟨hU, hD⟩ ↦ ⟨fun i ↦ ?_, hU.ge, ?_⟩⟩
  · exact hU ▸ Set.mem_iUnion_of_mem i (mem_leftCoset_iff _ |>.mpr (by simp))
  · intro i j hij
    by_contra hne
    have hi : reps i ∈ reps i • (K : Set G) := (mem_leftCoset_iff _).mpr (by simp)
    exact Set.disjoint_left.mp (hD hne) hi
      ((mem_leftCoset_iff _).mpr (QuotientGroup.eq.mp hij.symm))

/-- **The quotient characterization of a coset system**: `reps` is a coset system for `HgK`
exactly when the classes `(reps i : G ⧸ K)` are pairwise distinct and are precisely the left
cosets of `K` contained in `HgK`. -/
theorem isCosetSystem_iff_injective_and_range_eq :
    IsCosetSystem H K g reps ↔
      Function.Injective (fun i ↦ (reps i : G ⧸ K)) ∧
        Set.range (fun i ↦ (reps i : G ⧸ K)) = QuotientGroup.mk '' doubleCoset g H K := by
  have hmul : ∀ x ∈ doubleCoset g H K, ∀ k ∈ K, x * k ∈ doubleCoset g H K :=
    fun _ hx _ hk ↦ mul_mem_doubleCoset_of_mem_right hx hk
  refine ⟨fun h ↦ ⟨h.injective, ?_⟩, fun ⟨hinj, hrange⟩ ↦ ⟨fun i ↦ ?_, fun x hx ↦ ?_, hinj⟩⟩
  · ext q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [mk_mem_image_iff_of_forall_mul_mem hmul]
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨i, hi⟩
      rw [← mk_mem_image_iff_of_forall_mul_mem hmul, ← hi]
      exact ⟨reps i, h.mem_doubleCoset i, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h.doubleCoset_subset_iUnion hx)
      exact ⟨i, (QuotientGroup.eq.mpr ((mem_leftCoset_iff _).mp hi))⟩
  · exact (mk_mem_image_iff_of_forall_mul_mem hmul).mp
      (hrange ▸ Set.mem_range_self i)
  · obtain ⟨i, hi⟩ := hrange.ge ⟨x, hx, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, (mem_leftCoset_iff _).mpr (QuotientGroup.eq.mp hi)⟩

/-- **Changing representatives within their cosets.** A coset system depends only on the classes
of its members modulo `K`. -/
theorem isCosetSystem_congr {reps' : ι → G} (h : ∀ i, (reps' i : G ⧸ K) = reps i) :
    IsCosetSystem H K g reps' ↔ IsCosetSystem H K g reps := by
  have hfun : (fun i ↦ (reps' i : G ⧸ K)) = fun i ↦ (reps i : G ⧸ K) := funext h
  simp only [isCosetSystem_iff_injective_and_range_eq, hfun]

/-- Multiplying each member of a coset system on the right by an element of `K` gives another
coset system. -/
theorem IsCosetSystem.mul_right (h : IsCosetSystem H K g reps) {k : ι → G} (hk : ∀ i, k i ∈ K) :
    IsCosetSystem H K g fun i ↦ reps i * k i :=
  (isCosetSystem_congr fun i ↦ (QuotientGroup.mk_mul_of_mem _ (hk i))).mpr h

/-- **Reindexing a coset system** along an equivalence of index types. -/
theorem isCosetSystem_comp_equiv_iff (e : ι' ≃ ι) :
    IsCosetSystem H K g (reps ∘ e) ↔ IsCosetSystem H K g reps := by
  simp only [isCosetSystem_iff_injective_and_range_eq]
  exact and_congr (e.injective_comp fun i ↦ (reps i : G ⧸ K))
    (Iff.of_eq (congrArg (· = _) (e.surjective.range_comp fun i ↦ (reps i : G ⧸ K))))

/-- A coset system reindexed along an equivalence is a coset system. -/
theorem IsCosetSystem.comp_equiv (h : IsCosetSystem H K g reps) (e : ι' ≃ ι) :
    IsCosetSystem H K g (reps ∘ e) :=
  (isCosetSystem_comp_equiv_iff e).mpr h

/-- **Changing the representative of the double coset.** If `g' ∈ HgK`, then `Hg'K = HgK` has the
same coset systems. -/
theorem isCosetSystem_congr_of_mem {g' : G} (hg' : g' ∈ doubleCoset g H K) :
    IsCosetSystem H K g' reps ↔ IsCosetSystem H K g reps := by
  simp only [isCosetSystem_iff, doubleCoset_eq_of_mem hg']

/-- The identity double coset `H1H = H` has the singleton coset system `{1}`. -/
theorem isCosetSystem_one (H : Subgroup G) : IsCosetSystem H H 1 fun _ : Unit ↦ (1 : G) := by
  rw [isCosetSystem_iff, TauCeti.doubleCoset_one_self]
  exact ⟨by simp only [one_smul, Set.iUnion_const], Subsingleton.pairwise⟩

/-- **The canonical coset system.** For representatives `σᵢ` of `H ⧸ (H ∩ gKg⁻¹)`, the elements
`σᵢ g` form a coset system for `HgK`. -/
theorem isCosetSystem_out_mul (H K : Subgroup G) (g : G) :
    IsCosetSystem H K g fun i : DecompQuotient H K g ↦ (i.out : G) * g where
  mem_doubleCoset i := mem_doubleCoset.mpr ⟨i.out, i.out.property, 1, K.one_mem, by simp⟩
  doubleCoset_subset_iUnion := (doubleCoset_eq_iUnion_leftCosets H K g).le
  injective := mk_out_mul_injective H K g

namespace IsCosetSystem

/-- The index type of a coset system is in bijection with the set of left cosets of `K` contained
in `HgK`, by `i ↦ reps i • K`. -/
noncomputable def equivCosets (h : IsCosetSystem H K g reps) :
    ι ≃ (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K)) :=
  (Equiv.ofInjective _ h.injective).trans
    (Set.equivOfEq (isCosetSystem_iff_injective_and_range_eq.mp h).2)

@[simp]
theorem coe_equivCosets_apply (h : IsCosetSystem H K g reps) (i : ι) :
    (h.equivCosets i : G ⧸ K) = reps i := by
  simp [equivCosets]

/-- **Coset systems of the same double coset are matched by a bijection** `e` of their index types
with `reps' (e i) • K = reps i • K`. -/
theorem exists_equiv {reps' : ι' → G} (h : IsCosetSystem H K g reps)
    (h' : IsCosetSystem H K g reps') :
    ∃ e : ι ≃ ι', ∀ i, (reps' (e i) : G ⧸ K) = reps i :=
  ⟨h.equivCosets.trans h'.equivCosets.symm, fun i ↦ by
    rw [← h'.coe_equivCosets_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
      coe_equivCosets_apply]⟩

/-- A coset system has as many members as there are left cosets of `K` in `HgK`. -/
theorem natCard_eq (h : IsCosetSystem H K g reps) :
    Nat.card ι = Nat.card (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K)) :=
  Nat.card_congr h.equivCosets

/-- **The number of members of a coset system** is the relative index `[H : H ∩ gKg⁻¹]`. Both
sides are `0` when there are infinitely many left cosets of `K` in `HgK`. -/
theorem natCard_eq_relIndex (h : IsCosetSystem H K g reps) :
    Nat.card ι = (ConjAct.toConjAct g • K).relIndex H := by
  obtain ⟨e, -⟩ := h.exists_equiv (isCosetSystem_out_mul H K g)
  rw [Nat.card_congr e, relIndex, index_eq_card]

/-- A coset system is finite exactly when `HgK` contains finitely many left cosets of `K`. -/
theorem finite_iff (h : IsCosetSystem H K g reps) :
    Finite ι ↔ (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K)).Finite := by
  rw [Set.finite_coe_iff.symm]
  exact h.equivCosets.finite_iff

end IsCosetSystem

/-- **Existence of finite coset systems.** If the double coset `HgK` contains only finitely many
left cosets of `K`, it has a coset system indexed by `Fin n` for `n` the number of these
cosets. -/
theorem exists_isCosetSystem_fin_of_finite
    (hfin : (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K)).Finite) :
    ∃ reps : Fin (Nat.card (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K))) → G,
      IsCosetSystem H K g reps := by
  have h := isCosetSystem_out_mul H K g
  have : Finite (QuotientGroup.mk '' doubleCoset g H K : Set (G ⧸ K)) := hfin.to_subtype
  exact ⟨_, h.comp_equiv (h.equivCosets.trans (Finite.equivFin _)).symm⟩

end Subgroup

namespace HeckeCoset

open Subgroup

variable {Δ : Submonoid G} {H K : Subgroup G}

/-- **Coset systems of a Hecke double coset.** For a Hecke triple `(H, Δ, K)`, every double coset
`D = HδK` has a coset system with exactly `D.degree` members. -/
theorem exists_isCosetSystem_fin_degree [IsHeckeTriple Δ H K] (D : HeckeCoset Δ H K) :
    ∃ reps : Fin D.degree → G, IsCosetSystem H K (D.rep : G) reps := by
  have h := isCosetSystem_out_mul H K (D.rep : G)
  exact ⟨_, h.comp_equiv
    (Fintype.equivFinOfCardEq (degree_eq_card_decompQuotient D).symm).symm⟩

/-- A coset system of a Hecke double coset `D` has `D.degree` members. -/
theorem _root_.Subgroup.IsCosetSystem.natCard_eq_degree {ι : Type*} {reps : ι → G}
    {D : HeckeCoset Δ H K} (h : IsCosetSystem H K (D.rep : G) reps) : Nat.card ι = D.degree :=
  h.natCard_eq_relIndex.trans (degree_eq_relIndex D).symm

end HeckeCoset
