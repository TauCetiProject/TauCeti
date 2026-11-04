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

Let `G` be a group and `A` a `k`-linear representation of `G`. Suppose `G` is the directed union
of a family of subgroups `H i`: any two members lie in a common one, and every element of `G` lies
in some member. Group homology has compact supports along such a family:

* every class of `Hₙ(G, A)` is the corestriction of a class of `Hₙ(H i, A)` for some `i`
  (`groupHomology.exists_map_subtype_eq`);
* a class of `Hₙ(H i, A)` whose corestriction to `G` vanishes already vanishes in
  `Hₙ(H j, A)` for some `H j ⊇ H i` (`groupHomology.exists_map_inclusion_eq_zero`).

Together these are the elementwise form of the statement that `Hₙ(G, A)` is the colimit of the
`Hₙ(H i, A)` along the corestriction maps. In particular `Hₙ(G, A)` vanishes when every
`Hₙ(H i, A)` does (`groupHomology.isZero_of_directed`).

Both statements come from the inhomogeneous chains: an `n`-chain of `G` is a finitely supported
function on `Gⁿ`, so the finitely many group elements it involves lie in a single member `H i`,
and corestriction is injective on chains.

These are the algebraic form of the compact-supports property of the homology of
Eilenberg--MacLane spaces `K(A, 1)` of a directed union of subgroups, through the identification
of the homology of a classifying space with group homology.

## Main definitions

* `Rep.resInclusionHom`: the identity of the restriction of `A` to a subgroup `K`, as a morphism
  into the restriction to `K` of the restriction of `A` to a larger subgroup `L`. Corestriction from
  `K` to `L` is the map on group homology it induces along `Subgroup.inclusion`.

## Main results

* `groupHomology.map_inclusion_comp_map_subtype`: corestriction from `K` to `L` followed by
  corestriction from `L` to `G` is corestriction from `K` to `G`.
* `groupHomology.exists_map_subtype_eq`: a class of a directed union of subgroups comes from a
  member.
* `groupHomology.exists_map_inclusion_eq_zero`: a class of a member that vanishes in the union
  vanishes in a larger member.
* `groupHomology.isZero_of_directed`: the homology of a directed union of subgroups vanishes in
  every degree in which the homology of every member vanishes.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 2.6, on the exactness of filtered colimits of modules, and Chapter 6, on group homology.
-/

public section

noncomputable section

open CategoryTheory Limits Finsupp

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace Rep

/-- The identity of the restriction of `A` to a subgroup `K`, viewed as a morphism into the
restriction to `K` (along `Subgroup.inclusion h`) of the restriction of `A` to a larger subgroup
`L`. The two representations of `K` have the same underlying module and action. -/
@[expose] def resInclusionHom {K L : Subgroup G} (h : K ≤ L) :
    res K.subtype A ⟶ res (Subgroup.inclusion h) (res L.subtype A) :=
  𝟙 (res K.subtype A)

@[simp]
theorem resInclusionHom_hom_apply {K L : Subgroup G} (h : K ≤ L) (a : A) :
    (resInclusionHom A h).hom a = a :=
  rfl

end Rep

namespace groupHomology

/-- Corestriction from a subgroup on chains: it pushes chains forward along the inclusion. -/
private theorem chainsMap_subtype_f_apply (K : Subgroup G) (n : ℕ)
    (x : (inhomogeneousChains (Rep.res K.subtype A)).X n) :
    (chainsMap K.subtype (𝟙 (Rep.res K.subtype A))).f n x = mapDomain (K.subtype ∘ ·) x := by
  simp [chainsMap_f]

/-- Corestriction between nested subgroups on chains: it pushes chains forward along the
inclusion. -/
private theorem chainsMap_inclusion_f_apply {K L : Subgroup G} (h : K ≤ L) (n : ℕ)
    (x : (inhomogeneousChains (Rep.res K.subtype A)).X n) :
    (chainsMap (Subgroup.inclusion h) (Rep.resInclusionHom A h)).f n x =
      mapDomain (Subgroup.inclusion h ∘ ·) x := by
  simp only [chainsMap_f]
  exact mapRange_id _

private theorem chainsMap_subtype_f_injective (K : Subgroup G) (n : ℕ) :
    Function.Injective ((chainsMap K.subtype (𝟙 (Rep.res K.subtype A))).f n) :=
  (ModuleCat.mono_iff_injective _).1 (chainsMap_f_map_mono _ _ K.subtype_injective n)

private theorem chainsMap_inclusion_comp_chainsMap_subtype {K L : Subgroup G} (h : K ≤ L) :
    chainsMap (Subgroup.inclusion h) (Rep.resInclusionHom A h) ≫
        chainsMap L.subtype (𝟙 (Rep.res L.subtype A)) =
      chainsMap K.subtype (𝟙 (Rep.res K.subtype A)) := by
  refine HomologicalComplex.hom_ext _ _ fun m ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply, chainsMap_inclusion_f_apply,
    chainsMap_subtype_f_apply, chainsMap_subtype_f_apply, ← mapDomain_comp]
  rfl

/-- **Corestriction is transitive.** For subgroups `K ≤ L` of `G`, corestriction from `K` to `L`
followed by corestriction from `L` to `G` is corestriction from `K` to `G`. -/
@[reassoc (attr := simp)]
theorem map_inclusion_comp_map_subtype {K L : Subgroup G} (h : K ≤ L) (n : ℕ) :
    map (Subgroup.inclusion h) (Rep.resInclusionHom A h) n ≫
        map L.subtype (𝟙 (Rep.res L.subtype A)) n =
      map K.subtype (𝟙 (Rep.res K.subtype A)) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n) (chainsMap_inclusion_comp_chainsMap_subtype A h))

variable {A} {ι : Type*} {H : ι → Subgroup G}

/-- Every chain of a directed union of subgroups is the pushforward of a chain of a member, which
may be taken to contain any given member. -/
private theorem exists_chainsMap_subtype_f_eq (hH : Directed (· ≤ ·) H)
    (hcov : ∀ g, ∃ i, g ∈ H i) (i₀ : ι) {n : ℕ} (x : (inhomogeneousChains A).X n) :
    ∃ i, ∃ _ : H i₀ ≤ H i, ∃ y,
      (chainsMap (H i).subtype (𝟙 (Rep.res (H i).subtype A))).f n y = x := by
  classical
  choose idx hidx using hcov
  have : Nonempty ι := ⟨i₀⟩
  -- a member containing `H i₀` and every group element occurring in the support of `x`
  obtain ⟨i, hi⟩ := hH.finset_le
    (insert i₀ ((x.support.biUnion fun f ↦ Finset.univ.image f).image idx))
  refine ⟨i, hi i₀ (Finset.mem_insert_self _ _), ?_⟩
  have hinj : Function.Injective ((H i).subtype ∘ · : (Fin n → H i) → Fin n → G) :=
    (H i).subtype_injective.comp_left
  have hx : x ∈ Set.range (mapDomain ((H i).subtype ∘ · : (Fin n → H i) → Fin n → G)) := by
    rw [mem_range_mapDomain_iff _ hinj]
    intro f hf
    by_contra hfx
    refine hf ⟨fun a ↦ ⟨f a, hi (idx (f a)) ?_ (hidx (f a))⟩, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_biUnion.2 ⟨f, Finsupp.mem_support_iff.2 hfx, Finset.mem_image_of_mem _
        (Finset.mem_univ a)⟩))
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, chainsMap_subtype_f_apply A _ n y⟩

/-- **Group homology of a directed union of subgroups comes from a member.** If `G` is the
directed union of the subgroups `H i`, every class of `Hₙ(G, A)` is the corestriction of a class
of `Hₙ(H i, A)` for some `i`. -/
theorem exists_map_subtype_eq (hH : Directed (· ≤ ·) H) (hcov : ∀ g, ∃ i, g ∈ H i) {n : ℕ}
    (x : groupHomology A n) : ∃ i y, map (H i).subtype (𝟙 (Rep.res (H i).subtype A)) n y = x := by
  obtain ⟨i₀, -⟩ := hcov 1
  refine HomologicalComplex.exists_homologyMap_eq_of_injective (n := n)
    (fun i ↦ chainsMap (H i).subtype (𝟙 (Rep.res (H i).subtype A)))
    (fun i ↦ chainsMap_subtype_f_injective A (H i) _) (fun y ↦ ?_) x
  obtain ⟨i, -, z, hz⟩ := exists_chainsMap_subtype_f_eq hH hcov i₀ y
  exact ⟨i, z, hz⟩

/-- **A class of a member that vanishes in a directed union of subgroups vanishes in a larger
member.** If `G` is the directed union of the subgroups `H i`, and the corestriction to `G` of a
class of `Hₙ(H i, A)` vanishes, then its corestriction to `Hₙ(H j, A)` vanishes for some `j` with
`H i ≤ H j`. -/
theorem exists_map_inclusion_eq_zero (hH : Directed (· ≤ ·) H) (hcov : ∀ g, ∃ i, g ∈ H i)
    {i : ι} {n : ℕ} (y : groupHomology (Rep.res (H i).subtype A) n)
    (hy : map (H i).subtype (𝟙 (Rep.res (H i).subtype A)) n y = 0) :
    ∃ j, ∃ hij : H i ≤ H j, map (Subgroup.inclusion hij) (Rep.resInclusionHom A hij) n y = 0 :=
  HomologicalComplex.exists_homologyMap_eq_zero_of_injective n
    (fun j ↦ chainsMap (H j).subtype (𝟙 (Rep.res (H j).subtype A)))
    (fun j ↦ chainsMap_subtype_f_injective A (H j) n) (ChainComplex.prev ℕ n)
    (P := fun j ↦ H i ≤ H j)
    (fun _ hj ↦ chainsMap (Subgroup.inclusion hj) (Rep.resInclusionHom A hj))
    (fun _ hj ↦ chainsMap_inclusion_comp_chainsMap_subtype A hj)
    (fun x ↦ exists_chainsMap_subtype_f_eq hH hcov i x) y hy

/-- **Vanishing of the homology of a directed union of subgroups.** If `G` is the directed union of
the subgroups `H i` and `Hₙ(H i, A)` vanishes for every `i`, then `Hₙ(G, A)` vanishes. -/
theorem isZero_of_directed (hH : Directed (· ≤ ·) H) (hcov : ∀ g, ∃ i, g ∈ H i) {n : ℕ}
    (h : ∀ i, IsZero (groupHomology (Rep.res (H i).subtype A) n)) :
    IsZero (groupHomology A n) := by
  have h0 (z : groupHomology A n) : z = 0 := by
    obtain ⟨i, w, rfl⟩ := exists_map_subtype_eq hH hcov z
    rw [(ModuleCat.subsingleton_of_isZero (h i)).elim w 0, map_zero]
  have : Subsingleton (groupHomology A n) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  exact ModuleCat.isZero_of_subsingleton _

end groupHomology
