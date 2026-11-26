/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# The surface intersection pairing under extension of the base field

The surface intersection number of two line-bundle classes is unchanged by extension of the
ground field. The comparison uses the actual pullback classes in a cartesian square.
Quasi-compactness and quasi-separation suffice for flat base change of the truncated Euler
characteristic defining the pairing. This truncated Euler characteristic uses `Module.finrank`,
so infinite-dimensional cohomology contributes zero.

Numerical equivalence of the extended classes implies numerical equivalence of the original
classes. The converse requires testing against classes on the extended scheme that need not
descend, and does not follow just from preservation of the pairing on pullback classes.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Chow

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [CompactSpace X] [QuasiSeparatedSpace X]

include H in
/-- Extension of the ground field preserves the surface intersection number of two
line-bundle classes. -/
theorem classIntersectionNumber_pullback (a b : LineBundleClass X) :
    classIntersectionNumber K Y (LineBundleClass.pullback g a) (LineBundleClass.pullback g b) =
      classIntersectionNumber k X a b := by
  rw [classIntersectionNumber_eq, classIntersectionNumber_eq,
    ← LineBundleClass.pullback_one g, ← LineBundleClass.pullback_inv,
    ← LineBundleClass.pullback_inv, ← LineBundleClass.pullback_mul]
  simp only [LineBundleClass.eulerCharBelow_pullback H]

include H in
/-- Extension of the ground field preserves the surface intersection number of two actual
invertible sheaves. -/
theorem intersectionNumber_pullback (L M : InvertibleSheaf X) :
    intersectionNumber K Y ((InvertibleSheaf.pullback g).obj L)
        ((InvertibleSheaf.pullback g).obj M) = intersectionNumber k X L M := by
  simpa only [LineBundleClass.pullback_mk, classIntersectionNumber_mk_mk] using
    classIntersectionNumber_pullback H (LineBundleClass.mk L) (LineBundleClass.mk M)

include H in
/-- Numerical equivalence after extension of the ground field implies numerical equivalence
before extension. -/
theorem NumericallyEquivalent.of_pullback {a b : LineBundleClass X}
    (h : NumericallyEquivalent K Y (LineBundleClass.pullback g a) (LineBundleClass.pullback g b)) :
    NumericallyEquivalent k X a b := by
  rw [numericallyEquivalent_iff]
  intro c
  simpa only [classIntersectionNumber_pullback H] using
    h.classIntersectionNumber_right (LineBundleClass.pullback g c)

end

end TauCeti.AlgebraicGeometry.Chow
