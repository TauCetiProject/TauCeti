/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# Group homology of a directed union of subgroups

Let `A` be a representation of a group `G`, and let `S i` be a directed family of subgroups of `G`
whose union is `G`. Every class of `Hₙ(G, A)` is then the image of a class of `Hₙ(S i, A)` for some
`i`, under the map induced by the inclusion of `S i`
(`groupHomology.exists_map_subtype_eq`). In particular, if every `Hₙ(S i, A)` vanishes,
so does `Hₙ(G, A)` (`TauCeti.groupHomology.isZero_groupHomology_of_directed`). Conversely, a class
of `Hₙ(S i, A)` whose image in `Hₙ(G, A)` vanishes already vanishes in `Hₙ(S j, A)` for some
`S j ⊇ S i` (`groupHomology.exists_map_inclusion_eq_zero`). Together these are the elementwise form
of the statement that `Hₙ(G, A)` is the colimit of the `Hₙ(S i, A)`.

This follows from the finiteness of chains. An inhomogeneous chain is a finite combination of
tuples of elements of `G`, so it involves finitely many elements of `G`, which all lie in one
`S i`, which may be taken to contain any given member
(`TauCeti.groupHomology.exists_chainsMap_subtype_f_eq_of_directed`,
`TauCeti.groupHomology.exists_le_chainsMap_subtype_f_eq_of_directed`). The maps of
inhomogeneous chains induced by injective group homomorphisms are injective
(`groupHomology.chainsMap_f_map_mono`), so a chain of `S i` whose image is a cycle is itself a
cycle, and a chain of `S i` whose image is a boundary is the boundary of a chain of a larger
member.

Since the singular homology of a classifying space `BG` is the group homology of `G`, every
homology class of an Eilenberg–MacLane space `K(G, 1)` comes from some `K(S i, 1)`, so `K(G, 1)` is
acyclic whenever every `K(S i, 1)` is; for instance `K(ℤ[1/2], 1)`, with `ℤ[1/2] = ⋃ᵣ 2⁻ʳ ℤ`, is
acyclic modulo two.

The map from `Hₙ(S i, A)` to `Hₙ(S j, A)` for `S i ≤ S j` is induced along `Subgroup.inclusion`
by `Rep.resInclusionHom`.

## Main results

* `groupHomology.exists_map_subtype_eq`: a class of a directed union of subgroups comes
  from a member.
* `groupHomology.exists_map_inclusion_eq_zero`: a class of a member that vanishes in a directed
  union of subgroups vanishes in a larger member.
* `TauCeti.groupHomology.isZero_groupHomology_of_directed`: group homology of a directed union of
  subgroups with vanishing homology vanishes.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982
  (homology commutes with directed unions of groups).

## Implementation notes

`exists_map_subtype_eq` and `exists_map_inclusion_eq_zero` take a class of group homology as an
explicit argument, so the dot-notation namespace lint keeps them in Mathlib's root
`groupHomology` namespace rather than in a copy of that namespace nested inside `TauCeti`. The
other results are in `TauCeti.groupHomology`.
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

/-- In a directed family of subgroups covering `G`, every inhomogeneous chain of `G` is the image
of an inhomogeneous chain of a member containing any given member `S i₀`. -/
theorem exists_le_chainsMap_subtype_f_eq_of_directed {ι : Type*} {S : ι → Subgroup G}
    (hS : Directed (· ≤ ·) S) (hG : ⨆ i, S i = ⊤) (i₀ : ι) {n : ℕ}
    (x : (inhomogeneousChains A).X n) :
    ∃ i, ∃ _ : S i₀ ≤ S i, ∃ y, (chainsMap (S i).subtype (𝟙 (res (S i).subtype A))).f n y = x := by
  -- apply `exists_chainsMap_subtype_f_eq_of_directed` to the members containing `S i₀`
  have : Nonempty { i // S i₀ ≤ S i } := ⟨⟨i₀, le_rfl⟩⟩
  obtain ⟨⟨i, hi⟩, y, hy⟩ := exists_chainsMap_subtype_f_eq_of_directed (A := A)
    (S := fun i : { i // S i₀ ≤ S i } ↦ S i)
    (fun i j ↦ (hS i j).elim fun l hl ↦ ⟨⟨l, i.2.trans hl.1⟩, hl⟩)
    (eq_top_iff.2 <| hG ▸ iSup_le fun i ↦ by
      obtain ⟨j, hij, hi₀j⟩ := hS i i₀
      exact hij.trans (le_iSup (fun j : { i // S i₀ ≤ S i } ↦ S j) ⟨j, hi₀j⟩)) x
  exact ⟨i, hi, y, hy⟩

/-- The maps of inhomogeneous chains induced by inclusions of subgroups compose: the inclusion of
`S` into `T` followed by that of `T` into `G` is the inclusion of `S` into `G`. -/
private theorem chainsMap_inclusion_comp_chainsMap_subtype {S T : Subgroup G} (h : S ≤ T) :
    chainsMap (Subgroup.inclusion h) (Rep.resInclusionHom A h) ≫
        chainsMap T.subtype (𝟙 (res T.subtype A)) =
      chainsMap S.subtype (𝟙 (res S.subtype A)) := by
  rw [← chainsMap_comp]
  congr 1
  ext a
  exact Rep.resInclusionHom_hom_apply A h a

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

/-- **Vanishing classes of a directed union of subgroups.** If `S` is a directed family of
subgroups whose union is `G`, and the image in `Hₙ(G, A)` of a class of `Hₙ(S i, A)` vanishes,
then its image in `Hₙ(S j, A)` vanishes for some `j` with `S i ≤ S j`. -/
theorem exists_map_inclusion_eq_zero {ι : Type*} {S : ι → Subgroup G}
    (hS : Directed (· ≤ ·) S) (hG : ⨆ i, S i = ⊤) {i : ι} {n : ℕ}
    (y : groupHomology (res (S i).subtype A) n)
    (hy : map (S i).subtype (𝟙 (res (S i).subtype A)) n y = 0) :
    ∃ j, ∃ hij : S i ≤ S j, map (Subgroup.inclusion hij) (Rep.resInclusionHom A hij) n y = 0 :=
  HomologicalComplex.exists_homologyMap_eq_zero_of_injective n
    (fun j ↦ chainsMap (S j).subtype (𝟙 (res (S j).subtype A)))
    (fun j ↦ (ModuleCat.mono_iff_injective _).1 <|
      chainsMap_f_map_mono _ (𝟙 (res (S j).subtype A)) (S j).subtype_injective _)
    (ChainComplex.prev ℕ n) (P := fun j ↦ S i ≤ S j)
    (fun _ hj ↦ chainsMap (Subgroup.inclusion hj) (Rep.resInclusionHom A hj))
    (fun _ hj ↦ TauCeti.groupHomology.chainsMap_inclusion_comp_chainsMap_subtype hj)
    (TauCeti.groupHomology.exists_le_chainsMap_subtype_f_eq_of_directed hS hG i) y hy

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
