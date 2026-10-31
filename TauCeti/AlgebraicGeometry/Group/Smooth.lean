/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Smoothness of group schemes over algebraically closed fields

A reduced group scheme locally of finite type over an algebraically closed field is smooth.
This supplies the scheme-theoretic input for coordinate-ring consequences such as the
finite-type commutative Hopf algebra smoothness criterion.

## Main declarations

* `TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced`: the
  reducedness criterion for smooth group schemes over algebraically closed fields.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26.
-/

-- The proof is adapted from the private algebraically-closed-field lemma underlying
-- `AlgebraicGeometry.smooth_of_grpObj` in Mathlib.

public section

open CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- A reduced group scheme locally of finite type over an algebraically closed field is smooth. -/
theorem smooth_of_grpObj_of_isAlgClosed_of_isReduced
    {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced G] :
    Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints h f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let e := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫ GrpObj.mulRight (A := Over.mk f) y'
  have he : x' ≫ e.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, e]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have he' : e.hom.left x = y := by
    have h := congrArg Over.Hom.left he
    simp only [Over.comp_left, x', y', Over.homMk_left,
      pointEquivClosedPoint_symm_apply_coe] at h
    rw [← pointOfClosedPoint_apply f x hxc (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply f y hyc (IsLocalRing.closedPoint K)]
    exact congr(($h) (IsLocalRing.closedPoint K))
  -- `Over.w e.hom` has right-hand side `(Over.mk f).hom`, which is only definitionally `f`;
  -- restate it with `f` so `rw!` can match `hy` syntactically.
  have hef : e.hom.left ≫ f = f := Over.w e.hom
  rw! [← he', ← e.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq, hef] at hy
  exact hx hy

end TauCeti.AlgebraicGeometry
