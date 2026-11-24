/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.RepresentationTheory.GKModule.Basic

/-!
# Compatible `(𝔤, K)`-modules

Let `K` be a Lie group modelled on `I` over `ℝ`, let `𝔤` be a Lie algebra over a normed field
extension `k` of `ℝ` (in the analytic theory `k = ℂ` and `𝔤` is a complexified Lie algebra) and let
`ι : Lie K → 𝔤` be the differentiated inclusion: for a Lie group `G` containing `K` through
`j : K →* G`, this is `TauCeti.GKModule.lieInclusion j c`, the differential of `j` at `1` followed
by a linear map `c : Lie G → 𝔤` (in the analytic theory, the inclusion of `Lie G` into its
complexification). A `(𝔤, K)`-module `M` in the sense of harmonic
analysis is a `TauCeti.GKModule` whose `K`-action is smooth on each finite-dimensional `K`-stable
subspace, with differential the action of `Lie K` through `ι`.

Every vector lies in the finite-dimensional `K`-stable span of its orbit, and a map into a
finite-dimensional space is smooth exactly when its coordinates are, with derivative computed
coordinatewise. So the condition is stated on matrix coefficients: for every linear functional `f`
and vector `v`, the function `g ↦ f (ρ g v)` is smooth, and its differential at `1` sends
`X ∈ Lie K` to `f ⁅ι X, v⁆`. No topology on `V` is needed.

Admissibility and the Harish-Chandra condition of `TauCeti.GKModule` are properties of the
underlying algebraic module and use no compatibility: a Harish-Chandra module in the sense of
harmonic analysis is a `TauCeti.GKModule` `M` with `M.IsCompatible ι` and
`M.IsHarishChandraModule`.

## Main definitions

* `TauCeti.GKModule.lieInclusion j c`: the differentiated inclusion `Lie K → 𝔤` of a Lie group
  homomorphism `j : K →* G`, followed by `c : Lie G → 𝔤`.
* `TauCeti.GKModule.IsCompatible M ι`: the `K`-action of `M` is smooth on finite-dimensional
  `K`-stable subspaces, with differential the action of `Lie K` through `ι`.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §3.3.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.GKModule

variable {k 𝔤 : Type*} [NontriviallyNormedField k] [NormedAlgebra ℝ k] [LieRing 𝔤]
  [LieAlgebra k 𝔤] [Module ℝ 𝔤]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {K : Type*} [TopologicalSpace K] [ChartedSpace H K] [Group K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad] {V : Type*} [AddCommGroup V] [Module k V]
  [LieRingModule 𝔤 V] [LieModule k 𝔤 V]

/-- A `(𝔤, K)`-module `M` is **compatible** with a map `ι : Lie K → 𝔤` when its `K`-action is
smooth on every finite-dimensional `K`-stable subspace with differential the action of `Lie K`
through `ι`. This is stated on matrix coefficients: each `g ↦ f (M.ρ g v)` is smooth, with
differential at `1` sending `X` to `f ⁅ι X, v⁆`. -/
structure IsCompatible (M : GKModule Ad V) (ι : GroupLieAlgebra I K →ₗ[ℝ] 𝔤) : Prop where
  /-- Every matrix coefficient of the `K`-action is smooth. -/
  contMDiff (f : Module.Dual k V) (v : V) : ContMDiff I 𝓘(ℝ, k) ∞ fun g ↦ f (M.ρ g v)
  /-- The differential of the `K`-action at `1` is the action of `Lie K` through `ι`. -/
  mfderiv_apply (f : Module.Dual k V) (v : V) (X : GroupLieAlgebra I K) :
    mfderiv I 𝓘(ℝ, k) (fun g ↦ f (M.ρ g v)) 1 X = f ⁅ι X, v⁆

section LieInclusion

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G]

/-- The **differentiated inclusion** `Lie K → 𝔤` of a Lie group pair: the differential at `1` of
a homomorphism `j : K →* G` (the inclusion of `K` in the Lie group `G`), followed by a linear map
`c : Lie G → 𝔤`, such as the inclusion of `Lie G` into its complexification. A `(𝔤, K)`-module in
the sense of harmonic analysis for the pair `(G, K)` is one with
`M.IsCompatible (lieInclusion j c)`. -/
noncomputable def lieInclusion (j : K →* G) (c : GroupLieAlgebra I' G →ₗ[ℝ] 𝔤) :
    GroupLieAlgebra I K →ₗ[ℝ] 𝔤 :=
  c ∘ₗ (show E →L[ℝ] E' from mfderiv I I' j 1).toLinearMap

theorem lieInclusion_apply (j : K →* G) (c : GroupLieAlgebra I' G →ₗ[ℝ] 𝔤)
    (X : GroupLieAlgebra I K) : lieInclusion j c X = c (mfderiv I I' j 1 X) :=
  (rfl)

end LieInclusion

end TauCeti.GKModule
