/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Fréchet derivative rules on topological vector spaces

Mathlib defines `HasFDerivAtFilter` and `HasFDerivAt` on arbitrary topological vector spaces via
`Asymptotics.IsLittleOTVS`, while several standard differentiation rules in Mathlib still carry
`NormedAddCommGroup` and `NormedSpace` hypotheses:

* `HasFDerivAtFilter.comp` / `HasFDerivAt.comp` in `Mathlib.Analysis.Calculus.FDeriv.Comp` assume
  normed spaces on the domain and intermediate spaces (`E` and `F`, while `G` is already a TVS),
* `ContinuousAffineMap.hasFDerivAtFilter` / `ContinuousAffineMap.hasFDerivAt` in
  `Mathlib.Analysis.Calculus.FDeriv.Affine` assume normed spaces on both domain and codomain, and
* `hasFDerivAtFilter_pi'` / `hasFDerivAt_pi'` in `Mathlib.Analysis.Calculus.FDeriv.Prod` allow
  arbitrary index types `ι`, but assume normed spaces on `E` and each coordinate space `F i`.

This module provides the topological-vector-space versions directly via `Asymptotics.IsLittleOTVS`,
adapting the proofs from those Mathlib modules to drop the norm hypotheses—specifically, for
products, `HasFDerivAtFilter.proj` and `HasFDerivAt.proj` give the forward projection implication
for arbitrary (possibly infinite) index types without normed-space hypotheses, rather than the full
product equivalence. Where Mathlib already exposes a normed-space theorem under the unsuffixed
name, we use the `_tvs` suffix to avoid name collisions.

## Main results

* `ContinuousAffineMap.hasFDerivAtFilter_tvs`, `ContinuousAffineMap.hasFDerivAt_tvs`: a
  continuous affine map between topological vector spaces has derivative `f.contLinear`.
* `ContinuousLinearMap.comp_hasFDerivAtFilter_tvs`, `ContinuousLinearMap.comp_hasFDerivAt_tvs`:
  postcomposing a differentiable map with a continuous linear map composes the derivative, with no
  continuity hypotheses on addition or scalar multiplication.
* `HasFDerivAtFilter.proj`, `HasFDerivAt.proj`: TVS forward projection rule giving the
  coordinatewise Fréchet derivative for maps into arbitrary (possibly infinite) products
  `∀ i, F i`.
* `HasFDerivAtFilter.comp_tvs`, `HasFDerivAt.comp_tvs`: the chain rule on topological vector
  spaces.
-/

public section

open Filter Asymptotics

section AffineAndLinear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]

/-- A continuous affine map between topological vector spaces has Fréchet derivative `f.contLinear`
along any filter `L`. Generalizes Mathlib's normed-only `ContinuousAffineMap.hasFDerivAtFilter`. -/
theorem ContinuousAffineMap.hasFDerivAtFilter_tvs [IsTopologicalAddTorsor E]
    [IsTopologicalAddTorsor F] (f : E →ᴬ[𝕜] F) {L : Filter (E × E)} :
    HasFDerivAtFilter f f.contLinear L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun p => by
    rw [Pi.zero_apply, ← vsub_eq_sub p.1 p.2, f.contLinear_apply_vsub, vsub_eq_sub, sub_self]

/-- A continuous affine map between topological vector spaces has Fréchet derivative `f.contLinear`
at every point `x`. Generalizes Mathlib's normed-only `ContinuousAffineMap.hasFDerivAt`. -/
theorem ContinuousAffineMap.hasFDerivAt_tvs [IsTopologicalAddTorsor E] [IsTopologicalAddTorsor F]
    (f : E →ᴬ[𝕜] F) {x : E} :
    HasFDerivAt f f.contLinear x :=
  f.hasFDerivAtFilter_tvs

/-- Postcomposing a function with Fréchet derivative `f'` along `L` by a continuous linear map `A`
has Fréchet derivative `A.comp f'` along `L`, requiring no continuity assumptions on addition or
scalar multiplication. -/
theorem ContinuousLinearMap.comp_hasFDerivAtFilter_tvs (A : F →L[𝕜] G) {f : E → F}
    {f' : E →L[𝕜] F} {L : Filter (E × E)} (hf : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (A ∘ f) (A.comp f') L :=
  .of_isLittleOTVS <| (A.isBigOTVS_comp.trans_isLittleOTVS hf.isLittleOTVS).congr_left fun p => by
    simp only [Function.comp_apply, map_sub, ContinuousLinearMap.comp_apply]

/-- Postcomposing a function with Fréchet derivative `f'` at `x` by a continuous linear map `A` has
Fréchet derivative `A.comp f'` at `x`, requiring no continuity assumptions on addition or scalar
multiplication. -/
theorem ContinuousLinearMap.comp_hasFDerivAt_tvs (A : F →L[𝕜] G) {f : E → F} {f' : E →L[𝕜] F}
    {x : E} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (A ∘ f) (A.comp f') x :=
  A.comp_hasFDerivAtFilter_tvs hf

/-- If `g : E → ∀ i, F i` has Fréchet derivative `g'` along `L`, then its `j`-th coordinate has
Fréchet derivative `(ContinuousLinearMap.proj j).comp g'` along `L`, for arbitrary (possibly
infinite) index types `ι`. -/
theorem HasFDerivAtFilter.proj {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    {g : E → ∀ i, F i} {g' : E →L[𝕜] ∀ i, F i} {L : Filter (E × E)}
    (hg : HasFDerivAtFilter g g' L) (j : ι) :
    HasFDerivAtFilter (fun z => g z j) ((ContinuousLinearMap.proj (R := 𝕜) j).comp g') L := by
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
    (ContinuousLinearMap.proj (R := 𝕜) (φ := F) j).comp_hasFDerivAtFilter_tvs hg

/-- If `g : E → ∀ i, F i` has Fréchet derivative `g'` at `x`, then its `j`-th coordinate has
Fréchet derivative `(ContinuousLinearMap.proj j).comp g'` at `x`, for arbitrary (possibly infinite)
index types `ι`. -/
theorem HasFDerivAt.proj {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    {g : E → ∀ i, F i} {g' : E →L[𝕜] ∀ i, F i} {x : E}
    (hg : HasFDerivAt g g' x) (j : ι) :
    HasFDerivAt (fun z => g z j) ((ContinuousLinearMap.proj (R := 𝕜) j).comp g') x :=
  HasFDerivAtFilter.proj hg j

end AffineAndLinear

section Comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [ContinuousAdd G] [ContinuousSMul 𝕜 G]

/-- **Chain rule along filters on topological vector spaces.** If `g` has Fréchet derivative `g'`
along `L'`, `f` has Fréchet derivative `f'` along `L`, and `Prod.map f f` tends from `L` to `L'`,
then `g ∘ f` has Fréchet derivative `g'.comp f'` along `L`. Generalizes Mathlib's normed-only
`HasFDerivAtFilter.comp`. -/
theorem HasFDerivAtFilter.comp_tvs {g : F → G} {g' : F →L[𝕜] G} {f : E → F} {f' : E →L[𝕜] F}
    {L : Filter (E × E)} {L' : Filter (F × F)}
    (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L)
    (hL : Tendsto (Prod.map f f) L L') :
    HasFDerivAtFilter (g ∘ f) (g'.comp f') L := by
  refine .of_isLittleOTVS <| calc
    (fun p => (g ∘ f) p.1 - (g ∘ f) p.2 - (g'.comp f') (p.1 - p.2))
      = (fun p => g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          (fun p => g' (f p.1 - f p.2 - f' (p.1 - p.2))) := by
        ext p
        simp
    _ =o[𝕜; L] (fun p => p.1 - p.2) :=
      ((hg.isLittleOTVS.comp_tendsto hL).trans_isBigOTVS hf.isBigOTVS_sub).add
        (g'.isBigOTVS_comp.trans_isLittleOTVS hf.isLittleOTVS)

/-- **Chain rule at a point on topological vector spaces.** Generalizes Mathlib's normed-only
`HasFDerivAt.comp`. -/
theorem HasFDerivAt.comp_tvs [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {g : F → G} {g' : F →L[𝕜] G} {f : E → F} {f' : E →L[𝕜] F} {x : E}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (g ∘ f) (g'.comp f') x :=
  HasFDerivAtFilter.comp_tvs hg hf <| hf.continuousAt.tendsto.prodMap (tendsto_pure_pure _ _)

end Comp
