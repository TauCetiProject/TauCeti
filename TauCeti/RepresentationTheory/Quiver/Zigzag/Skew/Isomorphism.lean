/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Isomorphism
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basic

/-!
# Relabelling skew-zigzag algebras

An isomorphism of simple graphs transports a skew-zigzag parameter by relabelling its incident
edges. The induced isomorphism of doubled path algebras then carries each skew relation to the
corresponding transported relation, and hence descends to an algebra isomorphism of the relation
quotients.

Identity relabellings act as identities, composites act by composites, and reversing a graph
isomorphism undoes parameter relabelling. This makes graph automorphisms available for comparing
arbitrary, rather than vertex-fixing, isomorphism classes of skew-zigzag algebras.

## Main definitions

* `TauCeti.SkewZigzagParameter.relabel`: transport a parameter along a graph isomorphism.
* `TauCeti.SkewZigzagParameter.relabelEquiv`: relabelling is an equivalence on parameters.
* `TauCeti.skewZigzagQuotientEquiv`: the induced isomorphism of skew-zigzag relation quotients.

## Main results

* `TauCeti.SkewZigzagParameter.relabel_ratio_map`: relabelling preserves the ratio attached to a
  pair of incident edges.
* `TauCeti.isSkewZigzagRelator_pathAlgebraEquiv`: graph relabelling carries skew relators to skew
  relators for the transported parameter.
* `TauCeti.skewZigzagQuotientEquiv_skewZigzagMk`: the quotient isomorphism sends a class to the
  class of its relabelled path-algebra representative.
* `TauCeti.skewZigzagQuotientEquiv_refl`, `TauCeti.skewZigzagQuotientEquiv_trans`, and
  `TauCeti.skewZigzagQuotientEquiv_symm`: quotient relabelling is coherent with graph-isomorphism
  identities, composition, and inverses.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u v w x

namespace SkewZigzagParameter

variable {k : Type w} [Monoid k] {V : Type u} {W : Type v}
  {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport a skew-zigzag parameter along an isomorphism of simple graphs. The ratio at two
incident edges of the target is the ratio at their inverse images. -/
def relabel (e : G ≃g H) (c : SkewZigzagParameter k G) : SkewZigzagParameter k H where
  ratio _ _ _ h h' := c.ratio (e.symm.map_adj_iff.mpr h) (e.symm.map_adj_iff.mpr h')
  ratio_self _ _ _ := c.ratio_self _
  ratio_inv _ _ _ _ _ := c.ratio_inv _ _
  ratio_cocycle _ _ _ _ _ _ _ := c.ratio_cocycle _ _ _

/-- The ratio of a relabelled parameter is the ratio at the inverse-image edges. -/
@[simp]
theorem relabel_ratio (e : G ≃g H) (c : SkewZigzagParameter k G) {i j j' : W}
    (h : H.Adj i j) (h' : H.Adj i j') :
    (c.relabel e).ratio h h' =
      c.ratio (e.symm.map_adj_iff.mpr h) (e.symm.map_adj_iff.mpr h') := (rfl)

/-- Relabelling preserves the ratio attached to two incident edges. -/
theorem relabel_ratio_map (e : G ≃g H) (c : SkewZigzagParameter k G) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    (c.relabel e).ratio (e.map_adj_iff.mpr h) (e.map_adj_iff.mpr h') = c.ratio h h' := by
  simp only [relabel_ratio]
  congr <;> simp

/-- Relabelling by the identity graph isomorphism changes no parameter. -/
@[simp]
theorem relabel_refl (c : SkewZigzagParameter k G) :
    c.relabel (SimpleGraph.Iso.refl (G := G)) = c := by
  ext i j j' h h'
  rfl

/-- Relabelling along a composite graph isomorphism is successive relabelling. -/
@[simp]
theorem relabel_trans {X : Type x} {K : SimpleGraph X} (e : G ≃g H) (f : H ≃g K)
    (c : SkewZigzagParameter k G) :
    c.relabel (e.trans f) = (c.relabel e).relabel f := by
  ext i j j' h h'
  rfl

/-- Relabelling by an isomorphism and then its inverse changes no parameter. -/
@[simp]
theorem relabel_symm_relabel (e : G ≃g H) (c : SkewZigzagParameter k G) :
    (c.relabel e).relabel e.symm = c := by
  ext i j j' h h'
  simp only [relabel_ratio]
  congr <;> simp

/-- Relabelling by an inverse isomorphism and then by the original isomorphism changes no
parameter. -/
@[simp]
theorem relabel_relabel_symm (e : G ≃g H) (c : SkewZigzagParameter k H) :
    (c.relabel e.symm).relabel e = c :=
  relabel_symm_relabel e.symm c

variable (k) in
/-- A graph isomorphism induces an equivalence between the skew-zigzag parameters on the two
graphs, by relabelling incident edges. -/
def relabelEquiv (e : G ≃g H) :
    SkewZigzagParameter k G ≃ SkewZigzagParameter k H where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv := relabel_symm_relabel e
  right_inv := relabel_relabel_symm e

/-- The parameter equivalence induced by a graph isomorphism acts by relabelling. -/
@[simp]
theorem relabelEquiv_apply (e : G ≃g H) (c : SkewZigzagParameter k G) :
    relabelEquiv k e c = c.relabel e := (rfl)

/-- The inverse parameter equivalence acts by relabelling along the inverse graph isomorphism. -/
@[simp]
theorem relabelEquiv_symm_apply (e : G ≃g H) (c : SkewZigzagParameter k H) :
    (relabelEquiv k e).symm c = c.relabel e.symm := (rfl)

end SkewZigzagParameter

variable (k : Type w) [CommRing k] {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### The relators are matched -/

/-- An isomorphism of graphs carries each skew-zigzag relator to the corresponding relator for
the transported parameter. -/
theorem isSkewZigzagRelator_pathAlgebraEquiv (e : G ≃g H) (c : SkewZigzagParameter k G)
    {z : pathAlgebra k (DoubledQuiver G)} (hz : IsSkewZigzagRelator k G c z) :
    IsSkewZigzagRelator k H (c.relabel e) (pathAlgebraEquiv k e z) := by
  cases hz with
  | nonreturn p hlen hne =>
    rw [pathAlgebraEquiv_ofPath, Prefunctor.mapTotalPath_mk]
    exact IsSkewZigzagRelator.nonreturn _
      (((DoubledQuiver.map e.toHom).length_mapPath p).trans hlen)
      fun h ↦ hne ((DoubledQuiver.map_obj_bijective e).1 h)
  | backtrack_ratio h h' =>
    rw [map_sub, map_smul, pathAlgebraEquiv_backtrackElem,
      pathAlgebraEquiv_backtrackElem]
    rw [← SkewZigzagParameter.relabel_ratio_map e c h h']
    exact IsSkewZigzagRelator.backtrack_ratio _ _
  | long_path y h3 =>
    rw [pathAlgebraEquiv_ofPath]
    exact IsSkewZigzagRelator.long_path _
      ((DoubledQuiver.map e.toHom).length_mapTotalPath y ▸ h3)

/-! ### The quotient isomorphism -/

/-- Relabelling maps the skew-zigzag relation ideal onto the relation ideal of the transported
parameter. -/
private theorem skewZigzagIdeal_map_eq (e : G ≃g H) (c : SkewZigzagParameter k G) :
    (skewZigzagIdeal k H (c.relabel e)).asIdeal =
      (skewZigzagIdeal k G c).asIdeal.map (pathAlgebraEquiv k e : _ →+* _) := by
  have hforward : skewZigzagIdeal k G c ≤
      (skewZigzagIdeal k H (c.relabel e)).comap (pathAlgebraEquiv k e).toRingHom := by
    rw [skewZigzagIdeal_eq_span, TwoSidedIdeal.span_le]
    intro z hz
    apply (TwoSidedIdeal.mem_comap (pathAlgebraEquiv k e).toRingHom).mpr
    exact mem_skewZigzagIdeal_of_isSkewZigzagRelator k H (c.relabel e)
      (isSkewZigzagRelator_pathAlgebraEquiv k e c hz)
  have hbackward : skewZigzagIdeal k H (c.relabel e) ≤
      (skewZigzagIdeal k G c).comap (pathAlgebraEquiv k e).symm.toRingHom := by
    rw [skewZigzagIdeal_eq_span, TwoSidedIdeal.span_le]
    intro z hz
    apply (TwoSidedIdeal.mem_comap (pathAlgebraEquiv k e).symm.toRingHom).mpr
    have hrel := isSkewZigzagRelator_pathAlgebraEquiv k e.symm (c.relabel e) hz
    rw [SkewZigzagParameter.relabel_symm_relabel] at hrel
    rw [← DoubledQuiver.pathAlgebraEquiv_symm] at hrel
    exact mem_skewZigzagIdeal_of_isSkewZigzagRelator k G c hrel
  ext y
  constructor
  · intro hy
    apply (Ideal.mem_map_of_equiv (pathAlgebraEquiv k e) y).mpr
    exact ⟨(pathAlgebraEquiv k e).symm y,
      (TwoSidedIdeal.mem_comap (pathAlgebraEquiv k e).symm.toRingHom).mp (hbackward hy),
      (pathAlgebraEquiv k e).apply_symm_apply y⟩
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_of_equiv (pathAlgebraEquiv k e) y).mp hy
    exact (TwoSidedIdeal.mem_comap (pathAlgebraEquiv k e).toRingHom).mp (hforward hz)

/-- A graph isomorphism induces an algebra isomorphism from a skew-zigzag quotient to the quotient
for the relabelled parameter. -/
noncomputable def skewZigzagQuotientEquiv (e : G ≃g H) (c : SkewZigzagParameter k G) :
    skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k H (c.relabel e) :=
  Ideal.quotientEquivAlg (skewZigzagIdeal k G c).asIdeal
    (skewZigzagIdeal k H (c.relabel e)).asIdeal (pathAlgebraEquiv k e)
    (skewZigzagIdeal_map_eq k e c)

/-- The induced quotient isomorphism sends a class to the class of its relabelled representative. -/
@[simp]
theorem skewZigzagQuotientEquiv_skewZigzagMk (e : G ≃g H)
    (c : SkewZigzagParameter k G) (z : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagQuotientEquiv k e c (skewZigzagMk k G c z) =
      skewZigzagMk k H (c.relabel e) (pathAlgebraEquiv k e z) := by
  rw [skewZigzagMk_apply, skewZigzagMk_apply, skewZigzagQuotientEquiv,
    Ideal.quotientEquivAlg_mk]

private theorem skewZigzagMk_cast {c d : SkewZigzagParameter k G} (h : c = d)
    (x : pathAlgebra k (DoubledQuiver G)) :
    AlgEquiv.cast (R := k) h (skewZigzagMk k G c x) = skewZigzagMk k G d x := by
  subst d
  rfl

/-- The inverse quotient isomorphism is induced by inverse graph relabelling, after identifying
the twice-relabelled parameter with the original parameter. -/
@[simp]
theorem skewZigzagQuotientEquiv_symm (e : G ≃g H) (c : SkewZigzagParameter k G) :
    (skewZigzagQuotientEquiv k e c).symm =
      (skewZigzagQuotientEquiv k e.symm (c.relabel e)).trans
        (AlgEquiv.cast (SkewZigzagParameter.relabel_symm_relabel e c)) := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := skewZigzagMk_surjective k H (c.relabel e) z
  apply (skewZigzagQuotientEquiv k e c).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.trans_apply,
    skewZigzagQuotientEquiv_skewZigzagMk, skewZigzagMk_cast,
    skewZigzagQuotientEquiv_skewZigzagMk, ← DoubledQuiver.pathAlgebraEquiv_symm,
    AlgEquiv.apply_symm_apply]

/-- Relabelling by the identity graph isomorphism induces the identity quotient isomorphism,
after identifying the relabelled parameter with the original parameter. -/
@[simp]
theorem skewZigzagQuotientEquiv_refl (c : SkewZigzagParameter k G) :
    (skewZigzagQuotientEquiv k (SimpleGraph.Iso.refl (G := G)) c).trans
        (AlgEquiv.cast (SkewZigzagParameter.relabel_refl c)) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := skewZigzagMk_surjective k G c z
  rw [AlgEquiv.trans_apply, skewZigzagQuotientEquiv_skewZigzagMk,
    skewZigzagMk_cast, DoubledQuiver.pathAlgebraEquiv_refl]
  rfl

/-- Relabelling along a composite graph isomorphism agrees with successive quotient
relabellings, after identifying the two relabelled parameters. -/
theorem skewZigzagQuotientEquiv_trans {X : Type x} [Finite X] {K : SimpleGraph X} (e : G ≃g H)
    (f : H ≃g K) (c : SkewZigzagParameter k G) :
    (skewZigzagQuotientEquiv k (e.trans f) c).trans
        (AlgEquiv.cast (SkewZigzagParameter.relabel_trans e f c)) =
      (skewZigzagQuotientEquiv k e c).trans
        (skewZigzagQuotientEquiv k f (c.relabel e)) := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := skewZigzagMk_surjective k G c z
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    skewZigzagQuotientEquiv_skewZigzagMk, skewZigzagQuotientEquiv_skewZigzagMk,
    skewZigzagQuotientEquiv_skewZigzagMk, skewZigzagMk_cast,
    DoubledQuiver.pathAlgebraEquiv_trans]
  rfl

end TauCeti
