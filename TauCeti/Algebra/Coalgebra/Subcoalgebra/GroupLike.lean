/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.GroupLike.Map
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

import Mathlib.LinearAlgebra.Span.Basic
import TauCeti.Algebra.Coalgebra.Finsupp.Coderivation

/-!
# Subcoalgebras spanned by group-like elements

This file defines the subcoalgebra spanned by a set of group-like elements, together with the
singleton span, a finite-generation theorem for finite sets of group-like elements, and a
`Module.Finite` instance for singleton spans.

The subcoalgebra spanned by all group-like elements is the full subcoalgebra exactly when the
group-like elements span the carrier as a module, a condition invariant under coalgebra
equivalence and preserved by surjective coalgebra morphisms
(`CoalgHom.groupLikeSetSpan_eq_top_of_surjective`). Over a domain the group-like elements of a
torsion-free coalgebra are linearly independent, so they then form a basis, `groupLikeBasis`. Its
coordinates identify the coalgebra with the diagonal coalgebra on its group-like elements
(`groupLikeBasisCoalgEquiv`), so an element primitive relative to a group-like element is zero
(`eq_zero_of_groupLikeSetSpan_eq_top_of_comul_eq_tmul_add_tmul`).

## References

This file uses the `GroupLike` and `IsGroupLikeElem` API from
`Mathlib.RingTheory.Coalgebra.GroupLike`, by Yaël Dillies and Michał Mrugała.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

variable {R C}

/-- The subcoalgebra spanned by a set of group-like elements. -/
@[expose] def groupLikeSetSpan (s : Set (GroupLike R C)) : Subcoalgebra R C :=
  let D := Submodule.span R ((↑) '' s : Set C)
  { carrier := D
    comul_mem' := by
      intro c hc
      refine Submodule.span_induction
        (p := fun c _ =>
          Coalgebra.comul (R := R) (A := C) c ∈
            LinearMap.range (TensorProduct.map D.subtype D.subtype)) ?mem ?zero ?add ?smul hc
      · intro x hx
        rcases hx with ⟨g, hg, rfl⟩
        have hgD : (g : C) ∈ D := Submodule.subset_span ⟨g, hg, rfl⟩
        refine ⟨⟨g, hgD⟩ ⊗ₜ[R] ⟨g, hgD⟩, ?_⟩
        rw [TensorProduct.map_tmul]
        exact g.isGroupLikeElem_val.comul_eq_tmul_self.symm
      · exact ⟨0, by simp⟩
      · intro x y _ _ hx' hy'
        rcases hx' with ⟨x', hx'⟩
        rcases hy' with ⟨y', hy'⟩
        refine ⟨x' + y', ?_⟩
        rw [LinearMap.map_add, hx', hy']
        exact ((Coalgebra.comul (R := R) (A := C)).map_add x y).symm
      · intro r x _ hx'
        rcases hx' with ⟨x', hx'⟩
        refine ⟨r • x', ?_⟩
        rw [LinearMap.map_smul, hx']
        exact ((Coalgebra.comul (R := R) (A := C)).map_smul r x).symm }

/-- The underlying submodule of the subcoalgebra spanned by a set of group-like elements is the
linear span of their underlying elements. -/
@[simp]
theorem groupLikeSetSpan_toSubmodule (s : Set (GroupLike R C)) :
    (groupLikeSetSpan (R := R) (C := C) s).toSubmodule =
      Submodule.span R ((↑) '' s : Set C) :=
  rfl

@[simp]
theorem mem_groupLikeSetSpan {s : Set (GroupLike R C)} {c : C} :
    c ∈ groupLikeSetSpan (R := R) (C := C) s ↔
      c ∈ Submodule.span R ((↑) '' s : Set C) :=
  Iff.rfl

/-- A group-like element in the generating set belongs to the subcoalgebra it spans. -/
theorem groupLike_mem_groupLikeSetSpan {s : Set (GroupLike R C)} {g : GroupLike R C} (hg : g ∈ s) :
    (g : C) ∈ groupLikeSetSpan (R := R) (C := C) s := by
  rw [mem_groupLikeSetSpan]
  exact Submodule.subset_span ⟨g, hg, rfl⟩

/-- Universal property for subcoalgebras spanned by a set of group-like elements. -/
theorem groupLikeSetSpan_le {s : Set (GroupLike R C)} {D : Subcoalgebra R C} :
    groupLikeSetSpan (R := R) (C := C) s ≤ D ↔ ∀ g ∈ s, (g : C) ∈ D := by
  constructor
  · intro h g hg
    exact h (groupLike_mem_groupLikeSetSpan (R := R) (C := C) hg)
  · intro h c hc
    rw [mem_groupLikeSetSpan] at hc
    rw [← mem_toSubmodule]
    have hspan : ((↑) '' s : Set C) ⊆ D.toSubmodule := by
      rintro _ ⟨g, hg, rfl⟩
      exact (mem_toSubmodule).2 (h g hg)
    exact (Submodule.span_le.2 hspan) hc

/-- Monotonicity of the subcoalgebra spanned by a set of group-like elements. -/
theorem groupLikeSetSpan_mono {s t : Set (GroupLike R C)} (hst : s ⊆ t) :
    groupLikeSetSpan (R := R) (C := C) s ≤ groupLikeSetSpan (R := R) (C := C) t := by
  rw [groupLikeSetSpan_le]
  intro g hg
  exact groupLike_mem_groupLikeSetSpan (R := R) (C := C) (hst hg)

/-- The subcoalgebra spanned by all group-like elements is the full subcoalgebra exactly when the
underlying group-like elements span the carrier as a module. -/
theorem groupLikeSetSpan_eq_top_iff_span_eq_top :
    groupLikeSetSpan (R := R) (C := C) Set.univ = ⊤ ↔
      Submodule.span R (Set.range (GroupLike.val (R := R) (A := C))) = ⊤ := by
  constructor
  · intro h
    rw [← Set.image_univ, ← groupLikeSetSpan_toSubmodule (R := R) (C := C) Set.univ, h,
      top_toSubmodule]
  · intro h
    ext c
    rw [mem_groupLikeSetSpan, Set.image_univ, h]
    simp only [Submodule.mem_top, mem_top]

/-- A coalgebra equivalence preserves the property that the group-like elements span the whole
carrier. -/
theorem groupLikeSetSpan_eq_top_iff_of_coalgEquiv {D : Type w} [AddCommMonoid D] [Module R D]
    [Coalgebra R D] (e : C ≃ₗc[R] D) :
    groupLikeSetSpan (R := R) (C := C) Set.univ = ⊤ ↔
      groupLikeSetSpan (R := R) (C := D) Set.univ = ⊤ := by
  rw [groupLikeSetSpan_eq_top_iff_span_eq_top (R := R) (C := C),
    groupLikeSetSpan_eq_top_iff_span_eq_top (R := R) (C := D)]
  have hgroupLike :
      (e : C ≃ₗ[R] D) '' Set.range (GroupLike.val (R := R) (A := C)) =
        Set.range (GroupLike.val (R := R) (A := D)) := by
    ext d
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨e.mapGroupLike g, e.val_mapGroupLike g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨x, rfl⟩ := e.mapGroupLike.surjective g
      exact ⟨x.val, ⟨x, rfl⟩, (e.val_mapGroupLike x).symm⟩
  rw [← hgroupLike, Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

/-- The subcoalgebra spanned by a group-like element. -/
def groupLikeSpan (g : GroupLike R C) : Subcoalgebra R C :=
  groupLikeSetSpan (R := R) (C := C) {g}

/-- Universal property for the subcoalgebra spanned by one group-like element. -/
theorem groupLikeSpan_le {g : GroupLike R C} {D : Subcoalgebra R C} :
    groupLikeSpan (R := R) (C := C) g ≤ D ↔ (g : C) ∈ D := by
  rw [groupLikeSpan, groupLikeSetSpan_le]
  simp

/-- The underlying submodule of the subcoalgebra spanned by one group-like element is the
submodule generated by `(g : C)`. -/
@[simp]
theorem groupLikeSpan_toSubmodule (g : GroupLike R C) :
    (groupLikeSpan (R := R) (C := C) g).toSubmodule = R ∙ (g : C) := by
  rw [groupLikeSpan, groupLikeSetSpan_toSubmodule]
  congr 1
  ext c
  simp

/-- A group-like element belongs to its span subcoalgebra. -/
theorem groupLike_mem_groupLikeSpan (g : GroupLike R C) :
    (g : C) ∈ groupLikeSpan (R := R) (C := C) g := by
  rw [← mem_toSubmodule, groupLikeSpan_toSubmodule]
  exact Submodule.mem_span_singleton_self (g : C)

/-- Membership in the subcoalgebra spanned by a group-like element. -/
@[simp]
theorem mem_groupLikeSpan {g : GroupLike R C} {c : C} :
    c ∈ groupLikeSpan (R := R) (C := C) g ↔ ∃ r : R, r • (g : C) = c := by
  rw [← mem_toSubmodule, groupLikeSpan_toSubmodule, Submodule.mem_span_singleton]

/-- A subcoalgebra spanned by a finite set of group-like elements is finitely generated. -/
theorem groupLikeSetSpan_finite (s : Set (GroupLike R C)) (hs : s.Finite) :
    Module.Finite R (groupLikeSetSpan (R := R) (C := C) s).toSubmodule := by
  rw [groupLikeSetSpan_toSubmodule]
  exact Module.Finite.span_of_finite R (hs.image ((↑) : GroupLike R C → C))

/-- The underlying submodule of the subcoalgebra spanned by one group-like element is finitely
generated. -/
instance groupLikeSpan_finite (g : GroupLike R C) :
    Module.Finite R (groupLikeSpan (R := R) (C := C) g).toSubmodule := by
  rw [groupLikeSpan]
  exact groupLikeSetSpan_finite (R := R) (C := C) {g} (Set.finite_singleton g)

section Domain

variable {S : Type u} {D : Type v} [CommRing S] [IsDomain S] [AddCommGroup D] [Module S D]
variable [Module.IsTorsionFree S D] [Coalgebra S D]

/-- Over a domain, the group-like elements of a torsion-free coalgebra that they span form a
basis of it. -/
noncomputable def groupLikeBasis (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤) :
    Module.Basis (GroupLike S D) S D :=
  Module.Basis.mk linearIndep_groupLikeVal
    ((groupLikeSetSpan_eq_top_iff_span_eq_top (R := S) (C := D)).mp h).ge

/-- The basis vector of `groupLikeBasis` indexed by a group-like element is that element. -/
@[simp]
theorem groupLikeBasis_apply (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤)
    (g : GroupLike S D) : groupLikeBasis h g = g.val :=
  Module.Basis.mk_apply _ _ g

/-- The coordinate of a group-like element in `groupLikeBasis` is the indicator of itself. -/
@[simp]
theorem groupLikeBasis_repr_val (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤)
    (g : GroupLike S D) : (groupLikeBasis h).repr g.val = Finsupp.single g 1 := by
  rw [← groupLikeBasis_apply h g, Module.Basis.repr_self]

/-- Over a domain, a torsion-free coalgebra spanned by its group-like elements is isomorphic to
the diagonal coalgebra `GroupLike S D →₀ S` through its coordinates in `groupLikeBasis`. -/
noncomputable def groupLikeBasisCoalgEquiv
    (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤) : D ≃ₗc[S] (GroupLike S D →₀ S) :=
  { (groupLikeBasis h).repr with
    counit_comp := (groupLikeBasis h).ext fun g ↦ by
      simp [g.isGroupLikeElem_val.counit_eq_one]
    map_comp_comul := (groupLikeBasis h).ext fun g ↦ by
      simp [g.isGroupLikeElem_val.comul_eq_tmul_self] }

/-- The underlying map of `groupLikeBasisCoalgEquiv` is the coordinate map of
`groupLikeBasis`. -/
@[simp]
theorem groupLikeBasisCoalgEquiv_apply (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤)
    (x : D) : groupLikeBasisCoalgEquiv h x = (groupLikeBasis h).repr x :=
  (rfl)

/-- The inverse of `groupLikeBasisCoalgEquiv` takes a coordinate vector to the corresponding
linear combination of group-like elements. -/
@[simp]
theorem groupLikeBasisCoalgEquiv_symm_apply
    (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤) (f : GroupLike S D →₀ S) :
    (groupLikeBasisCoalgEquiv h).symm f = Finsupp.linearCombination S (groupLikeBasis h) f :=
  (groupLikeBasis h).repr_symm_apply f

/-- **A coalgebra spanned by its group-like elements has no nonzero skew-primitive elements at a
single group-like element.** Over a domain, if the group-like elements span a torsion-free
coalgebra `D`, `Δ g = g ⊗ g`, and `Δ x = x ⊗ g + g ⊗ x`, then `x = 0`. -/
theorem eq_zero_of_groupLikeSetSpan_eq_top_of_comul_eq_tmul_add_tmul
    (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤) {g x : D}
    (hg : Coalgebra.comul (R := S) g = g ⊗ₜ[S] g)
    (hx : Coalgebra.comul (R := S) x = x ⊗ₜ[S] g + g ⊗ₜ[S] x) : x = 0 := by
  -- Transport both equations to the diagonal coalgebra, where the claim is already known.
  let e := groupLikeBasisCoalgEquiv h
  refine (map_eq_zero_iff e e.injective).mp
    (Finsupp.eq_zero_of_comul_eq_tmul_add_tmul (g := e g) ?_ ?_)
  · simpa [hg] using (CoalgHomClass.map_comp_comul_apply e g).symm
  · simpa [hx] using (CoalgHomClass.map_comp_comul_apply e x).symm

end Domain

end Subcoalgebra

end TauCeti

namespace CoalgHom

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A]
  [Module R B] [Coalgebra R A] [Coalgebra R B]

/-- A surjective coalgebra morphism preserves spanning by group-like elements. -/
theorem groupLikeSetSpan_eq_top_of_surjective (f : A →ₗc[R] B) (hf : Function.Surjective f)
    (hA : TauCeti.Subcoalgebra.groupLikeSetSpan (R := R) (C := A) Set.univ = ⊤) :
    TauCeti.Subcoalgebra.groupLikeSetSpan (R := R) (C := B) Set.univ = ⊤ := by
  rw [TauCeti.Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top] at hA ⊢
  refine top_unique ?_
  rw [← LinearMap.range_eq_top_of_surjective (f : A →ₗ[R] B) hf, LinearMap.range_eq_map,
    ← hA, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨⟨f g, g.isGroupLikeElem_val.map f⟩, rfl⟩

end CoalgHom
