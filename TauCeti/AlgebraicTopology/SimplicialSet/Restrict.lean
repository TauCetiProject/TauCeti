/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair

/-!
# Restricting a pair of simplicial sets to a subcomplex

For a pair of simplicial sets `P`, given by a monomorphism `P.hom : P.left ⟶ P.right`, and a
subcomplex `S` of the ambient simplicial set `P.right`, the restriction `P.restrict S` is the pair
`(S, S ∩ P.left)`, whose subcomplex is the preimage of `S` under `P.hom`.  The inclusions of `S`
and of its preimage assemble into a morphism of pairs `P.restrictι S : P.restrict S ⟶ P`, and a
morphism of pairs `f : P ⟶ P'` carrying `S` into `S'` restricts to a morphism
`SSetPair.restrictMap f h : P.restrict S ⟶ P'.restrict S'`.  Restriction of morphisms is compatible
with the inclusions (`SSetPair.restrictMap_comp_restrictι`), with identities
(`SSetPair.restrictMap_id`) and with composition (`SSetPair.restrictMap_comp`).

Restriction is the combinatorial step of excision for singular homology, where the singular pair
of a topological pair is restricted to the simplices subordinate to an open cover; the comparison
of relative homology is in `TauCeti.AlgebraicTopology.SimplicialSet.Homology.Restrict`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Theorem 2.20.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w

namespace SSet.Subcomplex

variable {X Y : SSet.{w}} (S : X.Subcomplex) (p : Y ⟶ X)

instance [Mono p] : Mono (S.fromPreimage p) := mono_of_mono_fac (S.fromPreimage_ι p)

/-- A simplex of `S` lies in the image of the preimage of `S` under `p` exactly when it lies in
the image of `p`. -/
lemma mem_range_fromPreimage_app_iff {n : SimplexCategoryᵒᵖ} (x : (S : SSet).obj n) :
    x ∈ Set.range ((S.fromPreimage p).app n) ↔ x.1 ∈ Set.range (p.app n) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    rw [preimage_obj, Set.mem_preimage, ha]
    exact x.2

end SSet.Subcomplex

namespace SSetPair

variable (P : SSetPair.{w}) (S : P.right.Subcomplex)

/-- The restriction of a pair of simplicial sets `P` to a subcomplex `S` of its ambient simplicial
set: the pair `(S, S ∩ P.left)`, whose subcomplex is the preimage of `S` under `P.hom`. -/
abbrev restrict : SSetPair.{w} := SSetPair.of (S.fromPreimage P.hom)

/-- The inclusion of the restriction of a pair to a subcomplex into the pair. -/
def restrictι : P.restrict S ⟶ P :=
  SSetPair.homMk (S.preimage P.hom).ι S.ι

@[simp]
lemma restrictι_left : (P.restrictι S).left = (S.preimage P.hom).ι := (rfl)

@[simp]
lemma restrictι_right : (P.restrictι S).right = S.ι := (rfl)

/-- A simplex of the restricted pair comes from its subcomplex exactly when the underlying simplex
of `P` comes from the subcomplex of `P`. -/
lemma mem_range_restrict_hom_app_iff {n : SimplexCategoryᵒᵖ} (x : (P.restrict S).right.obj n) :
    x ∈ Set.range ((P.restrict S).hom.app n) ↔ x.1 ∈ Set.range (P.hom.app n) :=
  S.mem_range_fromPreimage_app_iff P.hom x

variable {P S} {P' : SSetPair.{w}} {S' : P'.right.Subcomplex} (f : P ⟶ P')
  (h : S ≤ S'.preimage f.right)

include h in
private lemma range_ι_comp_right_le : SSet.Subcomplex.range (S.ι ≫ f.right) ≤ S' := by
  rintro n _ ⟨x, rfl⟩
  exact h n x.2

include h in
private lemma range_ι_comp_left_le :
    SSet.Subcomplex.range ((S.preimage P.hom).ι ≫ f.left) ≤ S'.preimage P'.hom := by
  rintro n _ ⟨x, rfl⟩
  have hx : f.right.app n (P.hom.app n x.1) ∈ S'.obj n := h n x.2
  have hw : P'.hom.app n (f.left.app n x.1) = f.right.app n (P.hom.app n x.1) := by
    have := congr($(f.w).app n x.1)
    simpa using this
  simpa [hw] using hx

/-- A morphism of pairs `f : P ⟶ P'` carrying a subcomplex `S` of `P.right` into a subcomplex `S'`
of `P'.right` restricts to a morphism of the restricted pairs. -/
def restrictMap : P.restrict S ⟶ P'.restrict S' :=
  SSetPair.homMk
    (SSet.Subcomplex.lift ((S.preimage P.hom).ι ≫ f.left) (range_ι_comp_left_le f h))
    (SSet.Subcomplex.lift (S.ι ≫ f.right) (range_ι_comp_right_le f h)) (by
      have hw : f.left ≫ P'.hom = P.hom ≫ f.right := by simpa using f.w
      ext n x
      apply Subtype.ext
      exact congr($(hw).app n x.1))

@[simp]
lemma restrictMap_left_app_coe {n : SimplexCategoryᵒᵖ} (x : (P.restrict S).left.obj n) :
    ((restrictMap f h).left.app n x).1 = f.left.app n x.1 := (rfl)

@[simp]
lemma restrictMap_right_app_coe {n : SimplexCategoryᵒᵖ} (x : (P.restrict S).right.obj n) :
    ((restrictMap f h).right.app n x).1 = f.right.app n x.1 := (rfl)

/-- The restriction of a morphism of pairs commutes with the inclusions of the restricted pairs. -/
@[reassoc]
lemma restrictMap_comp_restrictι :
    restrictMap f h ≫ P'.restrictι S' = P.restrictι S ≫ f := by
  ext : 2 <;> rfl

variable (P S) in
/-- Restricting the identity of a pair gives the identity of the restricted pair. -/
@[simp]
lemma restrictMap_id (h : S ≤ S.preimage (𝟙 P.right)) :
    restrictMap (𝟙 P) h = 𝟙 (P.restrict S) := by
  ext : 2 <;> rfl

/-- Restricting a composite of morphisms of pairs gives the composite of the restrictions. -/
@[reassoc]
lemma restrictMap_comp {P'' : SSetPair.{w}} {S'' : P''.right.Subcomplex} (g : P' ⟶ P'')
    (h' : S' ≤ S''.preimage g.right) :
    restrictMap f h ≫ restrictMap g h' =
      restrictMap (f ≫ g) (h.trans (SSet.Subcomplex.preimage_monotone f.right h')) := by
  ext : 2 <;> rfl

end SSetPair
