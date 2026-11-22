/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris

import TauCeti.Order.SupClosed

/-!
# Vanishing of cohomology with compact supports on unions of open sets

Let `X` be a Hausdorff space and fix a degree `n`. The vanishing of the cohomology with compact
supports `Hⁿ_c(-)` passes from open sets to two kinds of unions, with no condition on any
intersection:

* **disjoint unions**: if `X = U ∪ V` with `U` and `V` disjoint, the sum of the extensions
  `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` is an isomorphism
  (`TopCat.isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint`), so `Hⁿ_c(X)` vanishes
  when `Hⁿ_c(U)` and `Hⁿ_c(V)` do (`TopCat.isZero_compactSupportCohomology_of_disjoint`);
* **directed unions**: if `X` is the union of a directed family of open sets `U i`, every class of
  `Hⁿ_c(X)` is extended from some `Hⁿ_c(U i)`
  (`TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top`), so `Hⁿ_c(X)` vanishes when
  every `Hⁿ_c(U i)` does (`TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`).

Read for open subsets of `X`, these say that vanishing passes to the union of two disjoint open
subsets and to the union of a directed family of open subsets
(`TopCat.isZero_compactSupportCohomology_sup_of_disjoint`,
`TopCat.isZero_compactSupportCohomology_iSup_of_monotone`). Over the finite partial unions the two
combine: if `Hⁿ_c(s i)` vanishes for pairwise disjoint open subsets `s i`, so does `Hⁿ_c(⋃ i, s i)`
(`TopCat.isZero_compactSupportCohomology_iSup_of_pairwise_disjoint`).

In the proof of Poincaré duality for a manifold `M` of dimension `m` by induction over open subsets
(Hatcher, Lemma 3.36), the step from two open sets to their union compares two Mayer–Vietoris
sequences by the five lemma, which in the top degree needs `Hᵐ⁺¹_c(U ∩ V) = 0`. So the vanishing of
`Hⁿ_c` above the dimension is carried through the same induction: on convex open subsets of a chart
it is `TopCat.isZero_compactSupportCohomology_of_convex`, and the results of this file carry it to
disjoint and directed unions.

## Main results

* `TopCat.isZero_compactSupportCohomology_of_disjoint`,
  `TopCat.isZero_compactSupportCohomology_sup_of_disjoint`: vanishing on two disjoint open sets
  gives vanishing on their union.
* `TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`,
  `TopCat.isZero_compactSupportCohomology_iSup_of_monotone`: vanishing on a directed family of open
  sets gives vanishing on its union.
* `TopCat.isZero_compactSupportCohomology_iSup_of_pairwise_disjoint`: vanishing on pairwise disjoint
  open sets gives vanishing on their union.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}} [T2Space X] {n : ℕ}

/-! ### Covers -/

/-- **Cohomology with compact supports of a disjoint union.** If a Hausdorff space `X` is the union
of two disjoint open sets `U` and `V` with `Hⁿ_c(U) = 0` and `Hⁿ_c(V) = 0`, then `Hⁿ_c(X) = 0`. -/
theorem isZero_compactSupportCohomology_of_disjoint {U V : Opens X} (hUV : U ⊔ V = ⊤)
    (hd : Disjoint U V) (hU : IsZero (((toTopCat X).obj U).compactSupportCohomology R k M n))
    (hV : IsZero (((toTopCat X).obj V).compactSupportCohomology R k M n)) :
    IsZero (X.compactSupportCohomology R k M n) := by
  have := isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint R k M U V hUV hd n
  exact ((biprod_isZero_iff _ _).2 ⟨hU, hV⟩).of_iso (@asIso _ _ _ _ _ this).symm

/-- **Cohomology with compact supports of a directed union.** If a Hausdorff space `X` is the union
of a directed family of open sets `U i` with `Hⁿ_c(U i) = 0` for every `i`, then `Hⁿ_c(X) = 0`. -/
theorem isZero_compactSupportCohomology_of_iSup_eq_top {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {U : ι → Opens X} (hU : Monotone U) (hcover : ⨆ i, U i = ⊤)
    (h : ∀ i, IsZero (((toTopCat X).obj (U i)).compactSupportCohomology R k M n)) :
    IsZero (X.compactSupportCohomology R k M n) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- An empty family covers only the empty space.
    have : IsEmpty X := ⟨fun x ↦ by simpa [← hcover] using Opens.mem_top x⟩
    exact (TauCeti.isZero_singularCohomology_of_isEmpty R k M X n).of_iso
      (compactSupportCohomologyIsoOfCompactSpace n)
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x x' ↦ ?_⟩
  obtain ⟨i, z, rfl⟩ := exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
  obtain ⟨i', z', rfl⟩ := exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x'
  rw [(ModuleCat.subsingleton_of_isZero (h i)).elim z 0,
    (ModuleCat.subsingleton_of_isZero (h i')).elim z' 0, map_zero, map_zero]

/-! ### Open subsets -/

/-- For open subsets `U ≤ W` of `X`, the vanishing of `Hⁿ_c(U)` does not depend on whether `U` is
read as an open subset of `X` or of `W`. -/
private lemma isZero_compactSupportCohomology_comap_iff {U W : Opens X} (hUW : U ≤ W) :
    IsZero (((toTopCat ((toTopCat X).obj W)).obj
        ((Opens.map (inclusion' W)).obj U)).compactSupportCohomology R k M n) ↔
      IsZero (((toTopCat X).obj U).compactSupportCohomology R k M n) := by
  -- The two spaces are homeomorphic, through `x ↦ x.val.val` and `x ↦ ⟨⟨x.val, _⟩, _⟩`.
  let e : (toTopCat ((toTopCat X).obj W)).obj ((Opens.map (inclusion' W)).obj U) ≅
      (toTopCat X).obj U :=
    { hom := ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩, by fun_prop⟩
      inv := ofHom ⟨fun x ↦ ⟨⟨x.val, hUW x.property⟩, x.property⟩, by fun_prop⟩ }
  have : IsIso e.hom := e.isIso_hom
  have := isIso_compactSupportCohomologyExtend (R := R) (k := k) (M := M) (f := e.hom)
    (homeoOfIso e).isOpenEmbedding n
  exact (asIso (compactSupportCohomologyExtend (R := R) (k := k) (M := M) (f := e.hom)
    (homeoOfIso e).isOpenEmbedding n)).isZero_iff

/-- **Cohomology with compact supports of the union of two disjoint open subsets.** For disjoint
open subsets `U` and `V` of a Hausdorff space with `Hⁿ_c(U) = 0` and `Hⁿ_c(V) = 0`, also
`Hⁿ_c(U ∪ V) = 0`. -/
theorem isZero_compactSupportCohomology_sup_of_disjoint {U V : Opens X} (hd : Disjoint U V)
    (hU : IsZero (((toTopCat X).obj U).compactSupportCohomology R k M n))
    (hV : IsZero (((toTopCat X).obj V).compactSupportCohomology R k M n)) :
    IsZero (((toTopCat X).obj (U ⊔ V)).compactSupportCohomology R k M n) := by
  refine isZero_compactSupportCohomology_of_disjoint (U := (Opens.map (inclusion' (U ⊔ V))).obj U)
    (V := (Opens.map (inclusion' (U ⊔ V))).obj V) ?_ ?_
    ((isZero_compactSupportCohomology_comap_iff le_sup_left).2 hU)
    ((isZero_compactSupportCohomology_comap_iff le_sup_right).2 hV)
  · rw [eq_top_iff]
    exact fun x _ ↦ Opens.mem_sup.2 (Opens.mem_sup.1 x.property)
  · exact Opens.coe_disjoint.1 (Set.disjoint_left.2 fun x hU hV ↦
      Set.disjoint_left.1 (Opens.coe_disjoint.2 hd) hU hV)

/-- **Cohomology with compact supports of a directed union of open subsets.** For a directed family
of open subsets `U i` of a Hausdorff space with `Hⁿ_c(U i) = 0` for every `i`, also
`Hⁿ_c(⋃ i, U i) = 0`. -/
theorem isZero_compactSupportCohomology_iSup_of_monotone {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {U : ι → Opens X} (hU : Monotone U)
    (h : ∀ i, IsZero (((toTopCat X).obj (U i)).compactSupportCohomology R k M n)) :
    IsZero (((toTopCat X).obj (⨆ i, U i)).compactSupportCohomology R k M n) := by
  refine isZero_compactSupportCohomology_of_iSup_eq_top
    (U := fun i ↦ (Opens.map (inclusion' (⨆ i, U i))).obj (U i))
    (fun _ _ hij _ hx ↦ hU hij hx) ?_
    fun i ↦ (isZero_compactSupportCohomology_comap_iff (le_iSup U i)).2 (h i)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.property
  exact Opens.mem_iSup.2 ⟨i, hi⟩

/-- **Cohomology with compact supports of a union of pairwise disjoint open subsets.** For pairwise
disjoint open subsets `s i` of a Hausdorff space with `Hⁿ_c(s i) = 0` for every `i`, also
`Hⁿ_c(⋃ i, s i) = 0`. -/
theorem isZero_compactSupportCohomology_iSup_of_pairwise_disjoint {ι : Type*} {s : ι → Opens X}
    (hs : Pairwise fun i j ↦ Disjoint (s i) (s j))
    (h : ∀ i, IsZero (((toTopCat X).obj (s i)).compactSupportCohomology R k M n)) :
    IsZero (((toTopCat X).obj (⨆ i, s i)).compactSupportCohomology R k M n) := by
  refine TauCeti.iSup_of_pairwise_disjoint
    (fun W ↦ IsZero (((toTopCat X).obj W).compactSupportCohomology R k M n)) ?_
    (fun _ _ hd ↦ isZero_compactSupportCohomology_sup_of_disjoint hd)
    (fun _ ht ↦ isZero_compactSupportCohomology_iSup_of_monotone ht) hs h
  have : IsEmpty ((toTopCat X).obj ⊥) := ⟨fun x ↦ x.property⟩
  exact (TauCeti.isZero_singularCohomology_of_isEmpty R k M _ n).of_iso
    (compactSupportCohomologyIsoOfCompactSpace n)

end TopCat
