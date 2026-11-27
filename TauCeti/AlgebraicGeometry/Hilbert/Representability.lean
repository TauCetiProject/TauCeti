/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.AffineSpace
public import TauCeti.AlgebraicGeometry.Hilbert.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.OpenRepresentability

/-!
# The Hilbert scheme of points of affine space

The prescribed polynomial-basis charts cover the finite locally free Hilbert functor by
representable open subfunctors. Their gluing represents the functor on all test schemes.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert

/-- The degree-`d` Hilbert functor of affine space over an affine base is representable
on all test schemes. -/
theorem isRepresentable_hilbertFunctor_affineSpace (n : Type u) (S : Scheme.{u})
    [IsAffine S] (d : ℕ) : (hilbertFunctor (𝔸(n; S) ↘ S) d).IsRepresentable := by
  refine Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over_of_isAffine _
    (isSheaf_zariskiTopology_hilbertFunctor _ d)
    (fun w ↦ basisChart w) (fun w ↦ basisChartPoint w)
    (fun w T _ a b h ↦ basisChartPoint_injective w T h)
    (fun w T _ x ↦ exists_opens_basisChartPoint w T x)
    (fun T _ x t ↦ by
      obtain ⟨w, W, a, b, -, ht, hx⟩ := exists_basisChartPoint T x t
      exact ⟨w, W, a, b, ht, hx⟩)

end AlgebraicGeometry.Hilbert
