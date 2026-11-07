/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.Curves.AffineCover
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# The genus of a proper curve under extension of the base field

Let `X` be a proper scheme over a field `k`, and let `X_K = X ×_k K` be its base change to a field
extension `K / k`. Then `X_K` has the same genus as `X`: `dim_K H¹(X_K, 𝒪) = dim_k H¹(X, 𝒪)`
(`TauCeti.AlgebraicGeometry.genus_eq_of_isPullback_of_isProper`). This is flat base change of
cohomology (`TauCeti.AlgebraicGeometry.finrank_cohomology_trivial_eq_of_isPullback`), and needs no
smoothness, reducedness, irreducibility or dimension hypothesis, which matters because `X_K` need
not be reduced or irreducible when `K / k` is inseparable. In degree zero, flat base change
(`TauCeti.AlgebraicGeometry.finrank_cohomology_zero_trivial_eq_of_isPullback`) shows that
`H⁰(X, 𝒪_X) = k` implies `H⁰(X_K, 𝒪) = K`. The hypothesis `H⁰(X, 𝒪_X) = k` cannot be dropped
there: for `X = ℙ¹_L` viewed as a `k`-scheme with `L / k` finite of degree `> 1`, the ring
`H⁰(X_L, 𝒪) = L ⊗_k L` has dimension `[L : k] > 1` over `L`.

For a smooth proper connected curve the finite-dimensionality of `H¹(X, 𝒪_X)` is automatic, so
there the invariance holds without finiteness hypotheses
(`TauCeti.AlgebraicGeometry.genus_eq_of_isPullback_of_smooth`); the dimension of `H¹` is also
computed on a cover by two affine opens (`Scheme.exists_two_affine_opens_of_smooth`). It is the
invariance of the genus that comparisons of curves and of their Jacobians across field extensions
rely on.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
* [The Stacks Project, Lemma 0BY9](https://stacks.math.columbia.edu/tag/0BY9).
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
  have := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  obtain ⟨U, V, hU, hV, hUV⟩ := X.exists_two_affine_opens_of_smooth (k := k)
  exact finrank_cohomology_one_trivial_eq_of_isPullback H hU hV hUV

include H in
/-- For a smooth proper connected curve, `H¹(X, 𝒪_X)` stays finite-dimensional under extension of
the base field. -/
theorem finiteDimensional_cohomology_one_trivial_of_isPullback_of_smooth
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [ConnectedSpace X] :
    FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1) := by
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  obtain ⟨U, V, hU, hV, hUV⟩ := X.exists_two_affine_opens_of_smooth (k := k)
  exact finiteDimensional_cohomology_one_trivial_of_isPullback H hU hV hUV

include H in
/-- **The genus of a proper scheme over a field is invariant under extension of the base field**:
`dim_K H¹(X_K, 𝒪) = dim_k H¹(X, 𝒪)`. The scheme need not be smooth, reduced, irreducible or of
dimension one. The finite-dimensionality of `H¹` after base change, needed to form the genus of
`Y`, follows from that before by `finiteDimensional_cohomology_trivial_of_isPullback`. -/
theorem genus_eq_of_isPullback_of_isProper [IsProper (X ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    [FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)] :
    Y.genus K = X.genus k := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  rw [Scheme.genus_def, Scheme.genus_def, finrank_cohomology_trivial_eq_of_isPullback H]

include H in
/-- **The genus of a smooth proper connected curve is invariant under extension of the base
field**, stated with `Scheme.genus`. The finite-dimensionality of `H¹` before and after base
change, needed to form both genera, follows from the geometric hypotheses. -/
theorem genus_eq_of_isPullback_of_smooth
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [ConnectedSpace X] :
    haveI : FiniteDimensional k
        (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) :=
      finiteDimensional_cohomology_one_trivial_of_smooth k X
    haveI := finiteDimensional_cohomology_one_trivial_of_isPullback_of_smooth H
    Y.genus K = X.genus k := by
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  have := finiteDimensional_cohomology_one_trivial_of_isPullback_of_smooth H
  exact genus_eq_of_isPullback_of_isProper H

end TauCeti.AlgebraicGeometry
