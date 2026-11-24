/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.HomologicalDegree
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.Degree.Homological
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

The proof compares the topological degree of `f` with its analytic degree at one point. A finite
holomorphic map from a compact surface is proper, and holomorphic and constant near no point, so
its topological degree is the number of preimages of any point counted with local multiplicities
(`TauCeti.RiemannSurface.degree_complexHomologicalOrientation`), which is the analytic degree
(`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`). Since the degree is a natural number,
when `X` and `Y` are both compact and connected, `f_* : H₂(X; ℤ) → H₂(Y; ℤ)` is bijective
exactly when `deg f = 1`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.bijective_singularHomologyMap_iff_degree_eq_one`);
a finite holomorphic map of degree one is a biholomorphism
(`TauCeti.RiemannSurface.biholomorphOfDegreeEqOne`).

A local biholomorphism has local multiplicity one
(`TauCeti.RiemannSurface.localMultiplicity_eq_one_iff_isLocalDiffeomorphAt`), so its local index
for the canonical orientations, which is its local multiplicity
(`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation`), is `1`
(`IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one`).

## Main results

* `IsLocalDiffeomorphAt.localIndex_complexHomologicalOrientation_eq_one`: a local biholomorphism
  has local index `1` for the canonical orientations.
* `FiniteHolomorphicMap.degree_complexHomologicalOrientation`: the topological degree of a finite
  holomorphic map is its analytic degree.
* `FiniteHolomorphicMap.bijective_singularHomologyMap_iff_degree_eq_one`: for compact connected
  `X` and `Y`, `f_*` is bijective on `H₂(-; ℤ)` exactly when `deg f = 1`.
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
  have hd : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    hf.eventually.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  rw [localIndex_complexHomologicalOrientation f hd,
    (localMultiplicity_eq_one_iff_isLocalDiffeomorphAt hd).2 hf, Nat.cast_one]

namespace FiniteHolomorphicMap

variable [CompactSpace X] [PreconnectedSpace Y]

/-- **The topological degree of a finite holomorphic map is its analytic degree.** For the
canonical orientations of compact Riemann surfaces `X` and `Y`, with `Y` connected, the degree of
a finite holomorphic map `f : X → Y` defined through local homology is the number
`TauCeti.RiemannSurface.degree f` of preimages of any point counted with local multiplicities. -/
theorem degree_complexHomologicalOrientation (f : FiniteHolomorphicMap X Y) :
    (complexHomologicalOrientation X).degree (complexHomologicalOrientation Y)
      Complex.finrank_real_complex ⟨f, f.holomorphic.continuous⟩ = degree f := by
  obtain ⟨x₀, -⟩ := f.nonconstant
  rw [RiemannSurface.degree_complexHomologicalOrientation f.holomorphic.continuous.isProperMap
    (y := f x₀) (fun _ _ ↦ .of_forall fun z ↦ f.holomorphic z) fun x _ ↦ f.not_eventuallyConst x]
  exact_mod_cast fiberMultiplicitySum_eq_degree f.holomorphic f.not_eventuallyConst _

variable [CompactSpace Y]

omit [PreconnectedSpace Y] in
/-- **A finite holomorphic map is an isomorphism on top homology exactly in degree one.** For a
finite holomorphic map `f : X → Y` between compact connected Riemann surfaces,
`f_* : H₂(X; ℤ) → H₂(Y; ℤ)` is bijective exactly when `deg f = 1`. -/
theorem bijective_singularHomologyMap_iff_degree_eq_one [ConnectedSpace X] [ConnectedSpace Y]
    (f : FiniteHolomorphicMap X Y) :
    Function.Bijective (ContinuousMap.singularHomologyMap ℤ 2 ⟨f, f.holomorphic.continuous⟩) ↔
      degree f = 1 := by
  rw [HomologicalOrientation.bijective_singularHomologyMap_iff _ (complexHomologicalOrientation Y)
    Complex.finrank_real_complex Complex.finrank_real_complex,
    degree_complexHomologicalOrientation]
  omega

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
