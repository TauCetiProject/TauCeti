/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.AffineCover
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Line-bundle degree under extension of the base field

The Euler-characteristic degree of a line bundle on a smooth proper connected curve is
unchanged by extension of the ground field. The line bundle after base change is its actual
pullback. The result holds over arbitrary fields, without a rational point or geometric
connectedness hypothesis.

Both coefficient cohomology dimensions and both structure-sheaf dimensions are preserved by
field extension. This makes degree, and hence the subgroup of degree-zero line-bundle classes,
compatible with extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [ConnectedSpace X]

namespace InvertibleSheaf

include H in
/-- The degree of a line bundle on a smooth proper connected curve is unchanged by any
extension of the ground field. The curve need not have a rational point or be geometrically
connected. -/
theorem eulerDegree_pullback (L : InvertibleSheaf X) :
    ((pullback g).obj L).eulerDegree K = L.eulerDegree k := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  obtain ⟨U, V, hU, hV, hUV⟩ := X.exists_two_affine_opens_of_smooth (k := k)
  rw [eulerDegree_eq_finrank_sub, eulerDegree_eq_finrank_sub, pullback_obj_obj,
    finrank_cohomology_zero_pullback_eq_of_isPullback H L.obj hU hV (hU.inf hV) hUV,
    finrank_cohomology_one_pullback_eq_of_isPullback H L.obj hU hV (hU.inf hV) hUV,
    finrank_cohomology_zero_trivial_eq_of_isPullback H,
    finrank_cohomology_one_trivial_eq_of_isPullback H hU hV hUV]

end InvertibleSheaf

namespace LineBundleClass

include H in
/-- Pullback under a field extension preserves the Euler-characteristic degree of a
line-bundle class on a smooth proper connected curve. -/
theorem eulerDegree_pullback (a : LineBundleClass X) :
    eulerDegree K (pullback g a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk, InvertibleSheaf.eulerDegree_pullback H]

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
