/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.AffineCover

/-!
# The genus of a smooth proper curve under extension of the base field

Let `X` be a smooth proper connected curve over a field `k`, and let `X_K = X ×_k K` be its base
change to a field extension `K / k`. Then `X_K` has the same genus as `X`:
`dim_K H¹(X_K, 𝒪) = dim_k H¹(X, 𝒪)`.

Such a curve is covered by two affine opens (`Scheme.exists_two_affine_opens_of_smooth`), so this
is the flat base change of `H¹(X, 𝒪_X)` on a two-affine cover
(`TauCeti.AlgebraicGeometry.genus_eq_of_isPullback`). It is the invariance of the genus that
comparisons of curves and of their Jacobians across field extensions rely on.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Module

universe u

namespace TauCeti.AlgebraicGeometry

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- **The genus of a smooth proper connected curve is invariant under extension of the base
field**: `dim_K H¹(X_K, 𝒪) = dim_k H¹(X, 𝒪)`. -/
theorem finrank_cohomology_one_trivial_eq_of_isPullback_of_smooth
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [ConnectedSpace X] :
    finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1) =
      finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  obtain ⟨U, V, hU, hV, hUV⟩ := X.exists_two_affine_opens_of_smooth (k := k)
  exact finrank_cohomology_one_trivial_eq_of_isPullback H hU hV hUV

include H in
/-- **The genus of a smooth proper connected curve is invariant under extension of the base
field**, stated with `Scheme.genus`. -/
theorem genus_eq_of_isPullback_of_smooth
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [ConnectedSpace X]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    [FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)] :
    Y.genus K = X.genus k := by
  rw [Scheme.genus_def, Scheme.genus_def,
    finrank_cohomology_one_trivial_eq_of_isPullback_of_smooth H]

end TauCeti.AlgebraicGeometry
