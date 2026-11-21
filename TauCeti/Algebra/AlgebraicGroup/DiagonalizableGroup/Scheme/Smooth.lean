/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected

/-!
# Smoothness of diagonalizable groups

Let `k` be a field of exponential characteristic `p` and `G` a finitely generated commutative
group. The diagonalizable group `D(G) = Spec k[G]` is smooth exactly when `G` has no `p`-torsion.
In characteristic zero, where `p = 1`, the condition is empty and every diagonalizable group is
smooth; in characteristic `p` the group `μ_p = D(ℤ/p)` is the basic non-smooth example.

A finite-type affine group over a field is smooth exactly when it is geometrically reduced, so the
criterion is the one for geometric reducedness of the group algebra `k[G]`, in the form
`TauCeti.DiagonalizableGroup.smooth_coordinateRing_iff` for the coordinate Hopf algebra.

## Main declarations

* `TauCeti.DiagonalizableGroup.smooth_groupScheme_iff`: the structural morphism of the
  diagonalizable group scheme is smooth exactly when the character group has no `p`-torsion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.5.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u

/-- **The diagonalizable group scheme `D(G)` over a field of exponential characteristic `p` is
smooth exactly when `G` has no `p`-torsion.** In characteristic zero, where `p = 1`, the condition
is empty. -/
theorem smooth_groupScheme_iff
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (G : FGCommGrpCat.{u}) :
    Smooth (groupScheme k G).X.hom ↔ ∀ g : G, g ^ p = 1 → g = 1 := by
  rw [groupScheme_def]
  have h := (algebraSmooth_iff_smooth_hopfSpec k (coordinateRing k G).obj).symm
  rw [smoothAffineGroupSchemeProperty_iff] at h
  exact h.trans (smooth_coordinateRing_iff k p G)

end TauCeti.DiagonalizableGroup
