/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Group homology of a directed union of subgroups

Let `A` be a representation of a group `G`, and let `S i` be a directed family of subgroups of `G`
whose union is `G`. Every class of `Hₙ(G, A)` is then the image of a class of `Hₙ(S i, A)` for some
`i`, under the map induced by the inclusion of `S i`
(`groupHomology.exists_map_subtype_eq`). In particular, if every `Hₙ(S i, A)` vanishes,
so does `Hₙ(G, A)` (`TauCeti.groupHomology.isZero_groupHomology_of_directed`).

This follows from the finiteness of chains. An inhomogeneous chain is a finite combination of
tuples of elements of `G`, so it involves finitely many elements of `G`, which all lie in one
`S i` (`TauCeti.groupHomology.exists_chainsMap_subtype_f_eq_of_directed`). The maps of
inhomogeneous chains induced by injective group homomorphisms are injective
(`groupHomology.chainsMap_f_map_mono`), so a chain of `S i` whose image is a cycle is itself a
cycle.

Since the singular homology of a classifying space `BG` is the group homology of `G`, every
homology class of an Eilenberg–MacLane space `K(G, 1)` comes from some `K(S i, 1)`, so `K(G, 1)` is
acyclic whenever every `K(S i, 1)` is; for instance `K(ℤ[1/2], 1)`, with `ℤ[1/2] = ⋃ᵣ 2⁻ʳ ℤ`, is
acyclic modulo two. Only this half of the comparison is proved here: a class of `S i` vanishing in
`G` is not shown to vanish in a larger member, so `Hₙ(G, A)` is not identified with the colimit of
the `Hₙ(S i, A)`.

## Main results

* `groupHomology.exists_map_subtype_eq`: a class of a directed union of subgroups comes
  from a member.
* `TauCeti.groupHomology.isZero_groupHomology_of_directed`: group homology of a directed union of
  subgroups with vanishing homology vanishes.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982
  (homology commutes with directed unions of groups).

## Implementation notes

`exists_map_subtype_eq` takes a class of `groupHomology A n` as an explicit argument, so the
dot-notation namespace lint keeps it in Mathlib's root `groupHomology` namespace rather than in a
copy of that namespace nested inside `TauCeti`. The other results are in `TauCeti.groupHomology`.
-/

public section

open CategoryTheory Limits Rep

universe u

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

/-- An inhomogeneous chain of `G` all of whose tuples have entries in a subgroup `S` is the image
of an inhomogeneous chain of `S`. -/
theorem exists_chainsMap_subtype_f_eq (S : Subgroup G) {n : ℕ}
    (x : (inhomogeneousChains A).X n) (hx : ∀ g ∈ (x : (Fin n → G) →₀ A).support, ∀ m, g m ∈ S) :
    ∃ y, (chainsMap S.subtype (𝟙 (res S.subtype A))).f n y = x := by
  -- the preimage is `x` restricted along the injective map `(Fin n → S) → (Fin n → G)`
  have hinj : Function.Injective (S.subtype ∘ · : (Fin n → S) → Fin n → G) :=
    S.subtype_injective.comp_left
  refine ⟨Finsupp.comapDomain _ (x : (Fin n → G) →₀ A) hinj.injOn, ?_⟩
  -- the coercion of a morphism of `ModuleCat` is that of its underlying linear map
  have : ((chainsMap S.subtype (𝟙 (res S.subtype A))).f n).hom
      (Finsupp.comapDomain _ (x : (Fin n → G) →₀ A) hinj.injOn) = x := by
    rw [chainsMap_f_hom]
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_comapDomain _ hinj]
    · ext g
      simp
    · intro g hg
      exact ⟨fun m ↦ ⟨g m, hx g hg m⟩, rfl⟩
  exact this

/-- In a directed family of subgroups covering `G`, every inhomogeneous chain of `G` is the image
of an inhomogeneous chain of one member. -/
theorem exists_chainsMap_subtype_f_eq_of_directed {ι : Type*} [Nonempty ι] {S : ι → Subgroup G}
    (hS : Directed (· ≤ ·) S) (hG : ⨆ i, S i = ⊤) {n : ℕ} (x : (inhomogeneousChains A).X n) :
    ∃ i y, (chainsMap (S i).subtype (𝟙 (res (S i).subtype A))).f n y = x := by
  classical
  let x' : (Fin n → G) →₀ A := x
  -- the finitely many entries of the tuples in the support of `x` lie in one member
  have hS' : Directed (· ⊆ ·) fun i ↦ (S i : Set G) := fun i j ↦
    (hS i j).imp fun _ h ↦ ⟨SetLike.coe_subset_coe.2 h.1, SetLike.coe_subset_coe.2 h.2⟩
  obtain ⟨i, hi⟩ := hS'.exists_mem_subset_of_finset_subset_biUnion
    (s := x'.support.biUnion fun g ↦ Finset.univ.image g) <| by
      rw [← Subgroup.coe_iSup_of_directed hS, hG, Subgroup.coe_top]
      exact Set.subset_univ _
  refine ⟨i, exists_chainsMap_subtype_f_eq (S i) x fun g hg m ↦ hi ?_⟩
  exact Finset.mem_coe.2 <|
    Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image_of_mem g (Finset.mem_univ m)⟩

end TauCeti.groupHomology

namespace groupHomology

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

/-- **Homology classes of a directed union of subgroups.** If `S` is a directed family of
subgroups whose union is `G`, every class of `Hₙ(G, A)` is the image of a class of `Hₙ(S i, A)`,
for some `i`, under the map induced by the inclusion of `S i`. -/
theorem exists_map_subtype_eq {ι : Type*} [Nonempty ι] {S : ι → Subgroup G}
    (hS : Directed (· ≤ ·) S) (hG : ⨆ i, S i = ⊤) {n : ℕ} (x : groupHomology A n) :
    ∃ i y, map (S i).subtype (𝟙 (res (S i).subtype A)) n y = x :=
  HomologicalComplex.exists_homologyMap_eq_of_injective n
    (fun i ↦ chainsMap (S i).subtype (𝟙 (res (S i).subtype A)))
    (fun i ↦ (ModuleCat.mono_iff_injective _).1 <|
      chainsMap_f_map_mono _ (𝟙 (res (S i).subtype A)) (S i).subtype_injective _)
    (TauCeti.groupHomology.exists_chainsMap_subtype_f_eq_of_directed hS hG) x

end groupHomology

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

/-- **Group homology of a directed union of acyclic subgroups.** If `S` is a directed family of
subgroups whose union is `G`, and `Hₙ(S i, A) = 0` for every `i`, then `Hₙ(G, A) = 0`. -/
theorem isZero_groupHomology_of_directed {ι : Type*} [Nonempty ι] {S : ι → Subgroup G}
    (hS : Directed (· ≤ ·) S) (hG : ⨆ i, S i = ⊤) {n : ℕ}
    (h : ∀ i, IsZero (groupHomology (res (S i).subtype A) n)) : IsZero (groupHomology A n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := exists_map_subtype_eq hS hG x
  have := ModuleCat.isZero_iff_subsingleton.1 (h i)
  rw [Subsingleton.elim y 0, map_zero]

end TauCeti.groupHomology
