/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Analysis.Analytic.Order
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Chart
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
inverse function theorem. A local biholomorphism preserves the canonical orientations
(`IsLocalDiffeomorphAt.isOrientationPreservingAt_complexManifoldOrientation`), so its local index
there is `1` (`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_eq_one`). Away from
the finitely many branch values every point of the fibre has local multiplicity one, so the
topological degree is the number of points of such a fibre, which is the analytic degree
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.card_fiber_eq_degree_iff`).

## Main results

* `TauCeti.RiemannSurface.localMultiplicity_eq_one_iff_isRegularPoint`: a holomorphic map has
  local multiplicity one exactly at the points where its complex derivative is nonzero.
* `TauCeti.RiemannSurface.localMultiplicity_eq_one_iff_isLocalDiffeomorphAt`: a holomorphic map
  has local multiplicity one exactly at the points where it is a local biholomorphism.
* `TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_eq_one`: there its local index
  is `1`.
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
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

/-- **Multiplicity one means a regular point.** A map holomorphic near `x` has local multiplicity
`1` at `x` exactly when its complex derivative at `x` is surjective, that is, nonzero. -/
theorem localMultiplicity_eq_one_iff_isRegularPoint {f : X → Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity f x = 1 ↔ IsRegularPoint 𝓘(ℂ) 𝓘(ℂ) f x := by
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hFa : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z))) (c x) :=
    analyticAt_chartAt_comp_comp_chartAt_symm hf
  -- Both conditions say that the representative of `f` in the preferred charts has nonzero
  -- derivative.
  have h := hFa.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero
  rw [c.left_inv hcx] at h
  have hw : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = fun z ↦ c' (f (c.symm z)) := rfl
  rw [localMultiplicity_def, analyticOrderNatAt, ENat.toNat_eq_iff one_ne_zero, Nat.cast_one, h,
    isRegularPoint_iff, hf.self_of_nhds.mfderiv, ModelWithCorners.range_eq_univ,
    fderivWithin_univ, hw, extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq,
    hFa.differentiableAt.hasDerivAt.hasFDerivAt.fderiv]
  refine ⟨fun hd v ↦ ⟨(tangentSpaceCastModel 𝓘(ℂ) x).symm
    (tangentSpaceCastModel 𝓘(ℂ) (f x) v / deriv (fun z ↦ c' (f (c.symm z))) (c x)), ?_⟩,
    fun hs hd ↦ ?_⟩
  · simp [div_mul_cancel₀ _ hd]
  · obtain ⟨a, ha⟩ := hs ((tangentSpaceCastModel 𝓘(ℂ) (f x)).symm 1)
    simp only [hd, ContinuousLinearMap.toSpanSingleton_zero, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, zero_apply] at ha
    simpa using congrArg (tangentSpaceCastModel 𝓘(ℂ) (f x)) ha

/-- **Multiplicity one means a local biholomorphism.** A map holomorphic near `x` has local
multiplicity `1` at `x` exactly when it is a local biholomorphism at `x`. -/
theorem localMultiplicity_eq_one_iff_isLocalDiffeomorphAt {f : X → Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity f x = 1 ↔ IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 f x := by
  refine ⟨fun hx ↦ ?_, fun h ↦ (localMultiplicity_eq_one_iff_isRegularPoint hf).2
    ((isRegularPoint_iff_isInvertible_mfderiv rfl).2 (h.isInvertible_mfderiv one_ne_zero))⟩
  -- The inverse function theorem at a point of invertible derivative.
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 hf
  obtain ⟨e, he⟩ := (isRegularPoint_iff_isInvertible_mfderiv rfl).1
    ((localMultiplicity_eq_one_iff_isRegularPoint hf).1 hx)
  exact isLocalDiffeomorphAt_of_mfderiv_eq
    (MDifferentiableOn.contMDiffOn (fun y hy ↦ (hs y hy).mdifferentiableWithinAt) hso) hso hxs
    BoundarylessManifold.isInteriorPoint le_rfl he

variable [T2Space X] [T2Space Y]

/-- **A holomorphic map has local index one at a point of multiplicity one.** For the canonical
orientations of the complex structures, the local index of a map holomorphic near `x` with local
multiplicity `1` at `x` is `1`. -/
theorem localIndex_complexHomologicalOrientation_eq_one {f : C(X, Y)} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hx : localMultiplicity f x = 1) :
    (complexHomologicalOrientation X).localIndex (complexHomologicalOrientation Y) f x = 1 := by
  have hl := (localMultiplicity_eq_one_iff_isLocalDiffeomorphAt hf).1 hx
  have hR : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 f x := hl.restrictScalars ℝ
  obtain ⟨L, hL, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1
    (hl.isOrientationPreservingAt_complexManifoldOrientation 1)
  rw [complexHomologicalOrientation_def, complexHomologicalOrientation_def,
    Manifold.Orientation.localIndex_toHomologicalOrientation _ _ _ f
      (hR.isInvertible_mfderiv one_ne_zero)]
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
  rw [Finset.sum_congr rfl fun x hx ↦ localIndex_complexHomologicalOrientation_eq_one
    (f := ⟨f, f.holomorphic.continuous⟩) (.of_forall fun z ↦ f.holomorphic z)
    ((f.notMem_branchValues_iff y).1 hy x (hfin.mem_toFinset.1 hx))]
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
