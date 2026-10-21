/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
import TauCeti.AlgebraicGeometry.ResidueField

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
  let t := S.fromSpecAlgebraicClosure s
  obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (S.residueField s)))) := inferInstance
  have htp : t p = s := Scheme.fromSpecAlgebraicClosure_apply S s p
  intro hs
  apply h _ t hN.isUnit.natCast_ne_zero_of_algebra
  apply ((E.baseChange t).eq_one_iff_left_apply_eq_zero _ p).mpr
  exact (pointsPullback_left_apply_eq_zero_iff (E.isPullback_baseChange t)
    (by simp) P p).mpr (htp.symm ▸ hs)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
