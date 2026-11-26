/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData.Map
public import TauCeti.Topology.Category.TopCat.GlueData.Reindex

/-!
# Isomorphisms of open gluing data

An isomorphism `α : D.Iso D'` of open gluing data consists of a bijection between the index
types together with homeomorphisms between corresponding pieces and between corresponding
overlaps, which commute with the inclusions of the overlaps and with the transition maps.
The two gluing data may live in different universes. Isomorphisms compose
(`TopCat.GlueData.Iso.trans`) and invert (`TopCat.GlueData.Iso.symm`), and reindexing along a
bijection gives an isomorphism (`TopCat.GlueData.reindexIso`).

An isomorphism is a bundled special case of the unbundled isomorphisms of gluing data in
`TauCeti.Topology.Category.TopCat.GlueData.Map`: its index map is a bijection, and it
preserves and reflects the identifications made by the gluing (`TopCat.GlueData.Iso.ι_eq_iff`).
So for gluing data in one universe it induces the homeomorphism
`TopCat.GlueData.gluedHomeomorph` of the existing glued carriers, given on each piece by the
piece homeomorphism; this is `TopCat.GlueData.Iso.gluedHomeomorph`. An isomorphism is determined
by its index bijection and this homeomorphism (`TopCat.GlueData.Iso.ext`), and the isomorphisms
form a groupoid.

The hypotheses of the separation, countability and connectedness criteria for glued spaces in
`TauCeti.Topology.Category.TopCat.GlueData` are invariant under isomorphisms:

* by `TopCat.GlueData.Iso.ι_eq_iff`, the piece homeomorphisms satisfy the hypothesis of
  `TopCat.GlueData.isClosed_chartRel_iff_of_homeomorph`, which transfers the input of
  `TopCat.GlueData.t2Space_iff_isClosed_chartRel`;
* the chains of nonempty overlaps correspond (`TopCat.GlueData.Iso.reflTransGen_iff`, which
  needs no nonempty piece, unlike `TopCat.GlueData.reflTransGen_nonempty_V_iff_of_surjective`),
  which is the input of `TopCat.GlueData.connectedSpace_iff_reflTransGen` and
  `TopCat.GlueData.preconnectedSpace_iff_reflTransGen`;
* the index types are equivalent and the pieces are homeomorphic, which transfers the
  countability hypotheses of `TopCat.GlueData.secondCountableTopology`.

The conclusions of these criteria are Mathlib typeclasses on the glued carriers, and they
transfer along `gluedHomeomorph` by Mathlib's `Homeomorph.t2Space`,
`Homeomorph.secondCountableTopology` and `Homeomorph.connectedSpace_iff`, and preconnectedness
by `DenseRange.preconnectedSpace` along the surjective `gluedHomeomorph`. Likewise compactness of
the glued carriers transfers by `Homeomorph.compactSpace`, and properness of maps out of or into
them by composing with `Homeomorph.isProperMap`. No separation, countability or nonemptiness
assumption is needed anywhere.

## References

* N. Bourbaki, *General Topology*, Chapter I, §3 (quotient spaces).
* The glued carriers and the gluing relation are Mathlib's `TopCat.GlueData`.
-/

public section

open CategoryTheory (eqToIso)
open Set Topology

namespace TopCat.GlueData

universe u v w

/-- An isomorphism of open gluing data: a bijection `indexEquiv` of the index types and
homeomorphisms between corresponding pieces and between corresponding overlaps, which commute
with the inclusions `f` of the overlaps and with the transition maps `t`. -/
structure Iso (D : TopCat.GlueData.{u}) (D' : TopCat.GlueData.{v}) where
  /-- The bijection between the index types. -/
  indexEquiv : D.J ≃ D'.J
  /-- The homeomorphism between the `i`-th piece and the corresponding piece. -/
  pieceHomeomorph (i : D.J) : D.U i ≃ₜ D'.U (indexEquiv i)
  /-- The homeomorphism between the overlap `V (i, j)` and the corresponding overlap. -/
  overlapHomeomorph (i j : D.J) : D.V (i, j) ≃ₜ D'.V (indexEquiv i, indexEquiv j)
  /-- The piece homeomorphisms commute with the inclusions of the overlaps. -/
  pieceHomeomorph_f (i j : D.J) (x : D.V (i, j)) :
    pieceHomeomorph i (D.f i j x) =
      D'.f (indexEquiv i) (indexEquiv j) (overlapHomeomorph i j x)
  /-- The overlap homeomorphisms commute with the transition maps. -/
  overlapHomeomorph_t (i j : D.J) (x : D.V (i, j)) :
    overlapHomeomorph j i (D.t i j x) =
      D'.t (indexEquiv i) (indexEquiv j) (overlapHomeomorph i j x)

namespace Iso

section

variable {D : TopCat.GlueData.{u}} {D' : TopCat.GlueData.{v}} {D'' : TopCat.GlueData.{w}}

/-- The identity isomorphism of gluing data. -/
-- Exposed so that the index bijection computes in the types of the piece homeomorphisms.
@[expose, simps]
def refl (D : TopCat.GlueData.{u}) : D.Iso D where
  indexEquiv := Equiv.refl D.J
  pieceHomeomorph i := Homeomorph.refl (D.U i)
  overlapHomeomorph i j := Homeomorph.refl (D.V (i, j))
  pieceHomeomorph_f _ _ _ := rfl
  overlapHomeomorph_t _ _ _ := rfl

/-- The composite of two isomorphisms of gluing data. -/
-- Exposed so that the index bijection computes in the types of the piece homeomorphisms.
@[expose, simps]
def trans (α : D.Iso D') (β : D'.Iso D'') : D.Iso D'' where
  indexEquiv := α.indexEquiv.trans β.indexEquiv
  pieceHomeomorph i := (α.pieceHomeomorph i).trans (β.pieceHomeomorph (α.indexEquiv i))
  overlapHomeomorph i j :=
    (α.overlapHomeomorph i j).trans (β.overlapHomeomorph (α.indexEquiv i) (α.indexEquiv j))
  pieceHomeomorph_f i j x :=
    (congrArg (β.pieceHomeomorph _) (α.pieceHomeomorph_f i j x)).trans (β.pieceHomeomorph_f _ _ _)
  overlapHomeomorph_t i j x :=
    (congrArg (β.overlapHomeomorph _ _) (α.overlapHomeomorph_t i j x)).trans
      (β.overlapHomeomorph_t _ _ _)

/-- Transporting a point of a piece along an equality of indices commutes with the inclusions
of the overlaps. -/
private theorem homeoOfIso_eqToIso_f (D : TopCat.GlueData.{u}) {i j i' j' : D.J} (hi : i = i')
    (hj : j = j') (x : D.V (i, j)) :
    TopCat.homeoOfIso (eqToIso (congrArg D.U hi)) (D.f i j x) =
      D.f i' j' (TopCat.homeoOfIso (eqToIso (congrArg D.V (Prod.ext hi hj : (i, j) = (i', j'))))
        x) := by
  subst hi hj
  rfl

/-- Transporting a point of an overlap along an equality of indices commutes with the transition
maps. -/
private theorem homeoOfIso_eqToIso_t (D : TopCat.GlueData.{u}) {i j i' j' : D.J} (hi : i = i')
    (hj : j = j') (x : D.V (i, j)) :
    TopCat.homeoOfIso (eqToIso (congrArg D.V (Prod.ext hj hi : (j, i) = (j', i')))) (D.t i j x) =
      D.t i' j' (TopCat.homeoOfIso (eqToIso (congrArg D.V (Prod.ext hi hj : (i, j) = (i', j'))))
        x) := by
  subst hi hj
  rfl

/-- Transporting a point of a piece along an equality of indices does not change its image in
the glued space. -/
private theorem ι_homeoOfIso_eqToIso (D : TopCat.GlueData.{u}) {i i' : D.J} (hi : i = i')
    (x : D.U i) :
    D.toGlueData.ι i' (TopCat.homeoOfIso (eqToIso (congrArg D.U hi)) x) = D.toGlueData.ι i x := by
  subst hi
  rfl

/-- The inverse of an isomorphism of gluing data. Its piece and overlap homeomorphisms are the
inverses of those of `α`, after identifying the `i`-th piece (or overlap) of `D'` with the
piece (or overlap) indexed by `α.indexEquiv (α.indexEquiv.symm i)`. -/
-- Exposed so that the index bijection computes in the types of the piece homeomorphisms.
@[expose, simps]
def symm (α : D.Iso D') : D'.Iso D where
  indexEquiv := α.indexEquiv.symm
  pieceHomeomorph i :=
    (TopCat.homeoOfIso (eqToIso (congrArg D'.U (α.indexEquiv.apply_symm_apply i).symm))).trans
      (α.pieceHomeomorph _).symm
  overlapHomeomorph i j :=
    (TopCat.homeoOfIso (eqToIso (congrArg D'.V
      (Prod.ext (α.indexEquiv.apply_symm_apply i).symm (α.indexEquiv.apply_symm_apply j).symm :
        (i, j) = (α.indexEquiv (α.indexEquiv.symm i), α.indexEquiv (α.indexEquiv.symm j)))))).trans
      (α.overlapHomeomorph _ _).symm
  pieceHomeomorph_f i j x := by
    apply (α.pieceHomeomorph _).injective
    simp only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply, α.pieceHomeomorph_f]
    exact homeoOfIso_eqToIso_f D' (α.indexEquiv.apply_symm_apply i).symm
      (α.indexEquiv.apply_symm_apply j).symm x
  overlapHomeomorph_t i j x := by
    apply (α.overlapHomeomorph _ _).injective
    simp only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply, α.overlapHomeomorph_t]
    exact homeoOfIso_eqToIso_t D' (α.indexEquiv.apply_symm_apply i).symm
      (α.indexEquiv.apply_symm_apply j).symm x

variable (α : D.Iso D')

/-- **Isomorphisms preserve and reflect the gluing.** Two points of pieces of `D` are identified
in the glued space exactly when their images in the corresponding pieces of `D'` are. -/
@[simp]
theorem ι_eq_iff {i j : D.J} (x : D.U i) (y : D.U j) :
    D'.toGlueData.ι (α.indexEquiv i) (α.pieceHomeomorph i x) =
        D'.toGlueData.ι (α.indexEquiv j) (α.pieceHomeomorph j y) ↔
      D.toGlueData.ι i x = D.toGlueData.ι j y := by
  rw [← D'.mem_chartRel_iff (p := (_, _)), ← D.mem_chartRel_iff (p := (x, y)),
    D'.mem_chartRel_iff_exists, D.mem_chartRel_iff_exists]
  constructor
  · rintro ⟨z, hx, hy⟩
    refine ⟨(α.overlapHomeomorph i j).symm z, (α.pieceHomeomorph i).injective ?_,
      (α.pieceHomeomorph j).injective ?_⟩
    · rw [α.pieceHomeomorph_f, Homeomorph.apply_symm_apply, hx]
    · rw [α.pieceHomeomorph_f, α.overlapHomeomorph_t, Homeomorph.apply_symm_apply, hy]
  · rintro ⟨z, hx, hy⟩
    exact ⟨α.overlapHomeomorph i j z, by rw [← α.pieceHomeomorph_f, hx],
      by rw [← α.overlapHomeomorph_t, ← α.pieceHomeomorph_f, hy]⟩

/-! ### The overlap graph -/

/-- Two pieces are joined by a chain of pieces with consecutive nonempty overlaps exactly when
the corresponding pieces are. This transfers the hypothesis of the connectedness criteria
`TopCat.GlueData.connectedSpace_iff_reflTransGen` and
`TopCat.GlueData.preconnectedSpace_iff_reflTransGen`. -/
theorem reflTransGen_iff (i j : D.J) :
    Relation.ReflTransGen (fun a b ↦ Nonempty (D'.V (a, b))) (α.indexEquiv i) (α.indexEquiv j) ↔
      Relation.ReflTransGen (fun a b ↦ Nonempty (D.V (a, b))) i j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Relation.ReflTransGen.lift (p := fun a b ↦ Nonempty (D'.V (a, b)))
    α.indexEquiv (fun a b ⟨z⟩ ↦ ⟨α.overlapHomeomorph a b z⟩) _ _ h⟩
  have h' : Relation.ReflTransGen (fun a b ↦ Nonempty (D.V (a, b)))
      (α.indexEquiv.symm (α.indexEquiv i)) (α.indexEquiv.symm (α.indexEquiv j)) :=
    Relation.ReflTransGen.lift (p := fun a b ↦ Nonempty (D.V (a, b))) α.indexEquiv.symm
      (fun a b hab ↦ by
        obtain ⟨a, rfl⟩ := α.indexEquiv.surjective a
        obtain ⟨b, rfl⟩ := α.indexEquiv.surjective b
        obtain ⟨z⟩ := hab
        simpa only [Function.onFun, Equiv.symm_apply_apply] using
          (⟨(α.overlapHomeomorph a b).symm z⟩ : Nonempty (D.V (a, b))))
      _ _ h
  simpa only [Equiv.symm_apply_apply] using h'

end

/-! ### The homeomorphism of glued spaces -/

variable {D D' D'' : TopCat.GlueData.{u}} (α : D.Iso D')

/-- The homeomorphism of glued spaces induced by an isomorphism of gluing data: the
`TopCat.GlueData.gluedHomeomorph` of its piece homeomorphisms, which is the corresponding piece
homeomorphism on each piece (`TopCat.GlueData.gluedHomeomorph_ι`). -/
noncomputable abbrev gluedHomeomorph : D.toGlueData.glued ≃ₜ D'.toGlueData.glued :=
  TopCat.GlueData.gluedHomeomorph α.pieceHomeomorph (fun _ _ x y ↦ α.ι_eq_iff x y)
    ((α.indexEquiv.surjective.iUnion_comp fun k ↦ range (D'.toGlueData.ι k)).trans
      D'.iUnion_range_ι)

/-- An isomorphism of gluing data is determined by its index bijection and its homeomorphism of
glued spaces. -/
@[ext]
theorem ext {α β : D.Iso D'} (he : α.indexEquiv = β.indexEquiv)
    (h : α.gluedHomeomorph = β.gluedHomeomorph) : α = β := by
  have hφ (i : D.J) (x : D.U i) :
      D'.toGlueData.ι (α.indexEquiv i) (α.pieceHomeomorph i x) =
        D'.toGlueData.ι (β.indexEquiv i) (β.pieceHomeomorph i x) := by
    simpa only [Iso.gluedHomeomorph, gluedHomeomorph_ι] using
      DFunLike.congr_fun h (D.toGlueData.ι i x)
  revert he hφ
  obtain ⟨e, φ, ψ, hf, -⟩ := α
  obtain ⟨e', φ', ψ', hf', -⟩ := β
  rintro rfl hφ
  obtain rfl : φ = φ' :=
    funext fun i ↦ Homeomorph.ext fun x ↦ D'.ι_injective (e i) (hφ i x)
  -- The overlap homeomorphisms are determined by the injective inclusions of the overlaps.
  obtain rfl : ψ = ψ' := funext fun i ↦ funext fun j ↦ Homeomorph.ext fun x ↦
    (D'.f_open (e i) (e j)).injective (by rw [← hf, ← hf'])
  rfl

/-- The identity isomorphism induces the identity homeomorphism of the glued space. -/
@[simp]
theorem gluedHomeomorph_refl : (Iso.refl D).gluedHomeomorph = Homeomorph.refl _ := by
  ext x
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
  rw [gluedHomeomorph_ι]
  -- The index `Equiv.refl D.J i` occurs in the type of the point, so `simp` cannot rewrite it;
  -- it unfolds to `i`.
  rfl

/-- The composite of isomorphisms induces the composite of the homeomorphisms of glued spaces. -/
@[simp]
theorem gluedHomeomorph_trans (β : D'.Iso D'') :
    (α.trans β).gluedHomeomorph = α.gluedHomeomorph.trans β.gluedHomeomorph := by
  ext x
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
  rw [Homeomorph.trans_apply, gluedHomeomorph_ι, gluedHomeomorph_ι, gluedHomeomorph_ι]
  -- The composite index occurs in the type of the point, so `simp` cannot rewrite it; it unfolds
  -- to the index of the two-step composite.
  rfl

/-- The inverse isomorphism induces the inverse homeomorphism of glued spaces. -/
@[simp]
theorem gluedHomeomorph_symm : α.symm.gluedHomeomorph = α.gluedHomeomorph.symm := by
  ext x
  obtain ⟨i, x, rfl⟩ := D'.ι_jointly_surjective x
  rw [Homeomorph.eq_symm_apply, gluedHomeomorph_ι, gluedHomeomorph_ι]
  -- The index `α.symm.indexEquiv i` occurs in the type of the point, so `symm_pieceHomeomorph`
  -- cannot be rewritten; it unfolds to `α.indexEquiv.symm i`.
  exact (congrArg (D'.toGlueData.ι _)
    ((α.pieceHomeomorph (α.indexEquiv.symm i)).apply_symm_apply _)).trans
      (ι_homeoOfIso_eqToIso D' (α.indexEquiv.apply_symm_apply i).symm x)

/-- Inverting an isomorphism of gluing data twice gives it back. -/
@[simp]
theorem symm_symm : α.symm.symm = α :=
  ext (Equiv.symm_symm _) (by rw [gluedHomeomorph_symm, gluedHomeomorph_symm,
    Homeomorph.symm_symm])

/-- The inverse of the identity isomorphism is the identity. -/
@[simp]
theorem refl_symm : (Iso.refl D).symm = Iso.refl D :=
  ext Equiv.refl_symm (by rw [gluedHomeomorph_symm, gluedHomeomorph_refl, Homeomorph.refl_symm])

/-- An isomorphism followed by its inverse is the identity. -/
@[simp]
theorem self_trans_symm : α.trans α.symm = Iso.refl D :=
  ext (Equiv.self_trans_symm _) (by
    rw [gluedHomeomorph_trans, gluedHomeomorph_symm, gluedHomeomorph_refl,
      Homeomorph.self_trans_symm])

/-- The inverse of an isomorphism followed by the isomorphism is the identity. -/
@[simp]
theorem symm_trans_self : α.symm.trans α = Iso.refl D' :=
  ext (Equiv.symm_trans_self _) (by
    rw [gluedHomeomorph_trans, gluedHomeomorph_symm, gluedHomeomorph_refl,
      Homeomorph.symm_trans_self])

/-- The inverse of a composite is the composite of the inverses in reverse order. -/
theorem symm_trans (β : D'.Iso D'') : (α.trans β).symm = β.symm.trans α.symm :=
  ext (Equiv.symm_trans _ _) (by
    rw [gluedHomeomorph_symm, gluedHomeomorph_trans, gluedHomeomorph_trans, gluedHomeomorph_symm,
      gluedHomeomorph_symm]
    exact Homeomorph.ext fun _ ↦ Homeomorph.symm_trans_apply _ _ _)

/-- The identity isomorphism followed by an isomorphism is that isomorphism. -/
@[simp]
theorem refl_trans : (Iso.refl D).trans α = α :=
  ext (Equiv.refl_trans _) (by
    rw [gluedHomeomorph_trans, gluedHomeomorph_refl]
    exact Homeomorph.ext fun _ ↦ rfl)

/-- An isomorphism followed by the identity isomorphism is that isomorphism. -/
@[simp]
theorem trans_refl : α.trans (Iso.refl D') = α :=
  ext (Equiv.trans_refl _) (by
    rw [gluedHomeomorph_trans, gluedHomeomorph_refl]
    exact Homeomorph.ext fun _ ↦ rfl)

/-- Composition of isomorphisms of gluing data is associative. -/
theorem trans_assoc {D''' : TopCat.GlueData.{u}} (β : D'.Iso D'') (γ : D''.Iso D''') :
    (α.trans β).trans γ = α.trans (β.trans γ) :=
  ext (Equiv.trans_assoc _ _ _) (by
    rw [gluedHomeomorph_trans, gluedHomeomorph_trans, gluedHomeomorph_trans,
      gluedHomeomorph_trans]
    exact Homeomorph.ext fun _ ↦ rfl)

end Iso

/-! ### Reindexing along a bijection -/

/-- Reindexing gluing data along a bijection of index types gives isomorphic gluing data. The
pieces, overlaps and transition maps of `D.reindex e` are literally those of `D`, so the piece
and overlap homeomorphisms are identities. -/
-- Exposed so that the index bijection computes in the types of the piece homeomorphisms.
@[expose, simps]
def reindexIso (D : TopCat.GlueData.{u}) {K : Type u} (e : K ≃ D.J) : (D.reindex e).Iso D where
  indexEquiv := e
  pieceHomeomorph i := Homeomorph.refl (D.U (e i))
  overlapHomeomorph i j := Homeomorph.refl (D.V (e i, e j))
  pieceHomeomorph_f _ _ _ := rfl
  overlapHomeomorph_t _ _ _ := rfl

/-- The homeomorphism induced by reindexing along a bijection is the canonical map
`TopCat.GlueData.reindexMap` from the reindexed gluing. -/
@[simp]
theorem coe_gluedHomeomorph_reindexIso (D : TopCat.GlueData.{u}) {K : Type u} (e : K ≃ D.J) :
    ⇑(D.reindexIso e).gluedHomeomorph = D.reindexMap e := by
  ext x
  obtain ⟨i, x, rfl⟩ := (D.reindex e).ι_jointly_surjective x
  rw [gluedHomeomorph_ι, reindexMap_ι]
  -- The piece homeomorphism of `reindexIso` is the identity of `D.U (e i)`.
  rfl

end TopCat.GlueData
