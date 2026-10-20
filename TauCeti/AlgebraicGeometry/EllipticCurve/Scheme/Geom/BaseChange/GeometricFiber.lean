/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Nonvanishing of sections on geometric fibres

A section of an elliptic curve misses zero at a point where `N` is invertible if its pullback
is nonzero over every algebraically closed field in which `N` is invertible
(`EllipticCurveGeom.left_apply_ne_zero_of_forall_isAlgClosed`). This reduction is shared by the
Drinfeld–naive comparisons for full level structures and for points of exact order.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

universe u

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- A section misses zero on a fibre where `N` is invertible if its pullback is nonzero over
every algebraically closed field in which `N` is invertible. -/
theorem left_apply_ne_zero_of_forall_isAlgClosed
    (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) {s : S} {N : ℕ}
    (hN : (N : S.residueField s) ≠ 0)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S), (N : K) ≠ 0 →
      pointsPullback (E.isPullback_baseChange t) (by simp) P ≠ 1) :
    P.left s ≠ E.zero s := by
  let L := AlgebraicClosure (S.residueField s)
  let t : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫ S.fromSpecResidueField s
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap (S.residueField s) L)]
    exact (map_ne_zero _).mpr hN
  obtain ⟨p⟩ : Nonempty (Spec (.of L)) := inferInstance
  have htp : t p = s := Scheme.fromSpecResidueField_apply s _
  intro hs
  apply h L t hNL
  apply ((E.baseChange t).eq_one_iff_left_apply_eq_zero _ p).mpr
  exact (pointsPullback_left_apply_eq_zero_iff (E.isPullback_baseChange t)
    (by simp) P p).mpr (htp.symm ▸ hs)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
