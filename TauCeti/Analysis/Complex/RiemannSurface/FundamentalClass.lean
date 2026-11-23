/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Fundamental classes of finite holomorphic maps

Let `f : X → Y` be a finite holomorphic map between compact Riemann surfaces, with `Y`
connected. This file proves that `f` carries the fundamental class of `X` to its degree times the
fundamental class of `Y`:

`f_*[X] = deg f • [Y]`  in `H₂(Y; ℤ)`

(`TauCeti.RiemannSurface.FiniteHolomorphicMap.mapFundamentalClass_complexHomologicalOrientation`).
Here `[X]` and `[Y]` are the fundamental classes of the canonical orientations of the complex
structures (`TauCeti.complexFundamentalClass`), and `deg f` is the analytic degree
`TauCeti.RiemannSurface.degree f`, the number of preimages of any point counted with local
multiplicities. Composing with any continuous map `u : Y → M` gives
`(u ∘ f)_*[X] = deg f • u_*[Y]`
(`FiniteHolomorphicMap.mapFundamentalClass_complexHomologicalOrientation_comp`).

In the theory of pseudoholomorphic curves in a symplectic four-manifold `M`, a closed curve that
is not simple factors as `u ∘ f` through a simple curve `u : Y → M` and a finite holomorphic map
`f` of degree at least two. The second statement says that its homology class is `deg f` times the
class of the simple curve. So the `m`-fold cover of an embedded curve `C` and an embedded curve
in the class `m [C]` have the same homology class; they are told apart by whether the map
factors through `C`, not by their classes.

The proof compares the topological degree of `f` with its analytic degree at one point. The
topological degree, defined through local homology, is the sum of the local indices of `f` over any
finite fibre (`TauCeti.HomologicalOrientation.degree_eq_sum_localIndex`). At a point of local
multiplicity one, `f` has a nonzero complex derivative, so it is a local biholomorphism by the
inverse function theorem
(`TauCeti.RiemannSurface.localMultiplicity_eq_one_iff_isLocalDiffeomorphAt`). A local
biholomorphism preserves the canonical orientations
(`IsLocalDiffeomorphAt.isOrientationPreservingAt_complexManifoldOrientation`), so its local index
there is `1` (`IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one`). Away from
the finitely many branch values every point of the fibre has local multiplicity one, so the
topological degree is the number of points of such a fibre, which is the analytic degree
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.card_fiber_eq_degree_iff`).

## Main results

* `IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one`: a local biholomorphism
  has local index `1` for the canonical orientations.
* `FiniteHolomorphicMap.degree_complexHomologicalOrientation`: the topological degree of a finite
  holomorphic map is its analytic degree.
* `FiniteHolomorphicMap.mapFundamentalClass_complexHomologicalOrientation`: `f_*[X] = deg f • [Y]`.
* `FiniteHolomorphicMap.mapFundamentalClass_complexHomologicalOrientation_comp`:
  `(u ∘ f)_*[X] = deg f • u_*[Y]`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52 (2012), Proposition 2.5.1 (every closed curve factors through a simple curve).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

noncomputable section

open Filter Module Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.RiemannSurface

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space X] [T2Space Y]

/-- **A local biholomorphism has local index one.** For the canonical orientations of the complex
structures, the local index of a local biholomorphism at `x` is `1`. -/
theorem _root_.IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one
    {f : C(X, Y)} {x : X} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 f x) :
    (complexHomologicalOrientation X).localIndex (complexHomologicalOrientation Y) f x = 1 := by
  have hR : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 f x := hf.restrictScalars ℝ
  obtain ⟨L, hL, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1
    (hf.isOrientationPreservingAt_complexManifoldOrientation 1)
  rw [complexHomologicalOrientation_def, complexHomologicalOrientation_def,
    Manifold.Orientation.localIndex_toHomologicalOrientation (f := f)
      (hf := hR.isInvertible_mfderiv one_ne_zero)]
  refine Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
    ((Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).2 ⟨L, hL, ?_⟩)
  rw [Manifold.Orientation.orientationAt_reindex, Manifold.Orientation.orientationAt_reindex,
    Orientation.map_reindex, hmap]

namespace FiniteHolomorphicMap

variable [CompactSpace X] [PreconnectedSpace Y]

/-- **The topological degree of a finite holomorphic map is its analytic degree.** For the
canonical orientations of compact Riemann surfaces `X` and `Y`, with `Y` connected, the degree of
a finite holomorphic map `f : X → Y` defined through local homology is the number
`TauCeti.RiemannSurface.degree f` of preimages of any point counted with local multiplicities. -/
theorem degree_complexHomologicalOrientation (f : FiniteHolomorphicMap X Y) :
    (complexHomologicalOrientation X).degree (complexHomologicalOrientation Y)
      Complex.finrank_real_complex ⟨f, f.holomorphic.continuous⟩ = degree f := by
  -- A value `y` off the finitely many branch values: `Y` has no isolated points, so it is
  -- infinite.
  have : PerfectSpace Y := ChartedSpace.perfectSpace (H := ℂ)
  have : ∀ y : Y, (𝓝[≠] y).NeBot := perfectSpace_iff_forall_not_isolated.1 this
  obtain ⟨x₀, -⟩ := f.nonconstant
  obtain ⟨y, -, hy⟩ := ((infinite_of_mem_nhds (f x₀) univ_mem).sdiff
    f.finite_branchValues).nonempty
  have hfin := f.finite_fiber y
  rw [HomologicalOrientation.degree_eq_sum_localIndex _ _ Complex.finrank_real_complex
    Complex.finrank_real_complex (f.holomorphic.continuous.isProperMap) hfin]
  -- Every point of the fibre has local multiplicity one, hence local index one.
  rw [Finset.sum_congr rfl fun x hx ↦
    IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one
      (f := ⟨f, f.holomorphic.continuous⟩) ((localMultiplicity_eq_one_iff_isLocalDiffeomorphAt
        (.of_forall fun z ↦ f.holomorphic z)).1
        ((f.notMem_branchValues_iff y).1 hy x (hfin.mem_toFinset.1 hx)))]
  simp [(f.card_fiber_eq_degree_iff y).2 hy]

variable [CompactSpace Y]

/-- **A finite holomorphic map multiplies the fundamental class by its degree.** For a finite
holomorphic map `f : X → Y` between compact Riemann surfaces, with `Y` connected,
`f_*[X] = deg f • [Y]` in `H₂(Y; ℤ)`. -/
theorem mapFundamentalClass_complexHomologicalOrientation (f : FiniteHolomorphicMap X Y) :
    (complexHomologicalOrientation X).mapFundamentalClass Complex.finrank_real_complex
      ⟨f, f.holomorphic.continuous⟩ = (degree f : ℤ) • complexFundamentalClass Y := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ (complexHomologicalOrientation Y)
    _ Complex.finrank_real_complex, degree_complexHomologicalOrientation,
    complexFundamentalClass_def]

/-- **The class of a multiple cover.** For a finite holomorphic map `f : X → Y` between compact
Riemann surfaces, with `Y` connected, and any continuous map `u : Y → M`,
`(u ∘ f)_*[X] = deg f • u_*[Y]`. When `u` is a pseudoholomorphic curve, `u ∘ f` is the
`deg f`-fold multiple cover of `u`. -/
theorem mapFundamentalClass_complexHomologicalOrientation_comp {M : Type} [TopologicalSpace M]
    (f : FiniteHolomorphicMap X Y) (u : C(Y, M)) :
    (complexHomologicalOrientation X).mapFundamentalClass Complex.finrank_real_complex
      (u.comp ⟨f, f.holomorphic.continuous⟩) = (degree f : ℤ) •
        (complexHomologicalOrientation Y).mapFundamentalClass Complex.finrank_real_complex u := by
  rw [HomologicalOrientation.mapFundamentalClass_comp_eq_degree_smul _
    (complexHomologicalOrientation Y) _ Complex.finrank_real_complex,
    degree_complexHomologicalOrientation]

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
