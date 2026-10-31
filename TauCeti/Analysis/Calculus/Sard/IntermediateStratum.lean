/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The intermediate strata in Sard's theorem

This file supplies the local dimension-reduction step for the intermediate strata in the
Morse--Sard proof. Suppose the `i`th iterated derivative of a smooth map vanishes at `a`, but the
derivative of order `i + 1` does not. A scalar component of the `i`th derivative then has a nonzero
differential at `a`. Its zero set is a regular hypersurface containing every nearby point where
the `i`th derivative vanishes.

`TauCeti.exists_parametrization_iteratedFDeriv_eq_zero` makes this reduction explicit. It gives a
`C^r` parametrization `θ` from the kernel of a nonzero scalar functional, whose dimension is one
less than that of the source. Locally, the zero set of the `i`th derivative is contained in the
image under `θ` of any prescribed neighbourhood of the origin, and `θ` itself lies in a regular
scalar level set containing that zero set. This is the induction-on-source-dimension input for
proving that the images of the intermediate strata `Σ_i \ Σ_{i+1}` are null.

The scalar component is `ℓ ∘ iteratedFDeriv 𝕜 i f` for a continuous linear functional `ℓ`,
supplied by Hahn--Banach through `SeparatingDual`, that does not vanish on a nonzero value of the
derivative of `iteratedFDeriv 𝕜 i f` at `a`. The parametrization is Mathlib's implicit function
for that scalar component. The statement holds over any `RCLike` field `𝕜`; Sard's theorem uses
the real case. This is the second stratification step following the flat-stratum estimate in
`TauCeti.Analysis.Calculus.Sard.FlatStratum`.

## Main result

* `TauCeti.exists_parametrization_iteratedFDeriv_eq_zero`: near a point of
  `Σ_i \ Σ_{i+1}`, the set `Σ_i` is contained in the image of a `C^r` map from a
  codimension-one space.

## References

The reduction is the intermediate-stratum step in the proof of Sard's theorem given in
J. Milnor, *Topology from the Differentiable Viewpoint*, Section 3, and M. Hirsch,
*Differential Topology*, Chapter 3.
-/

public section

open Filter Function Module Set

open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {a : E} {i : ℕ} {r : ℕ∞ω}

/-- **Local hypersurface reduction for an intermediate Sard stratum.** Suppose `f` is `C^{r+i}`
at `a`, with `r ≠ 0`, its `i`th iterated derivative vanishes at `a`, and its `(i+1)`st derivative
does not. Then there are a scalar component `g` of the `i`th derivative, its nonzero strict
derivative `g'`, and a `C^r` parametrization `θ` from `ker g'` such that:

* every zero of `iteratedFDeriv 𝕜 i f` is a zero of `g`;
* locally at `a`, every zero of `iteratedFDeriv 𝕜 i f` lies in the image under `θ` of any
  prescribed neighbourhood of the origin;
* locally at the origin, `θ` lies in the regular level set `g = 0`; and
* `ker g'` has dimension one less than `E`.

In particular, the intermediate stratum where all derivatives through order `i` vanish but the
next does not is locally carried by a `C^r` map from a strictly lower-dimensional source. -/
theorem exists_parametrization_iteratedFDeriv_eq_zero
    (hf : ContDiffAt 𝕜 (r + i) f a) (hr : r ≠ 0)
    (hi : iteratedFDeriv 𝕜 i f a = 0)
    (hnext : iteratedFDeriv 𝕜 (i + 1) f a ≠ 0) :
    ∃ (g : E → 𝕜) (g' : E →L[𝕜] 𝕜) (θ : ↥g'.ker → E),
      ContDiffAt 𝕜 r g a ∧
      HasStrictFDerivAt g g' a ∧
      g'.range = ⊤ ∧
      (∀ x, iteratedFDeriv 𝕜 i f x = 0 → g x = 0) ∧
      θ 0 = a ∧
      ContDiffAt 𝕜 r θ 0 ∧
      (∀ᶠ z in 𝓝 0, g (θ z) = 0) ∧
      (∀ V ∈ 𝓝 (0 : ↥g'.ker), ∀ᶠ x in 𝓝 a, iteratedFDeriv 𝕜 i f x = 0 → x ∈ θ '' V) ∧
      finrank 𝕜 ↥g'.ker + 1 = finrank 𝕜 E := by
  have := FiniteDimensional.complete 𝕜 E
  -- A scalar component `g = ℓ ∘ iteratedFDeriv 𝕜 i f` with nonzero derivative at `a`.
  have hD : fderiv 𝕜 (iteratedFDeriv 𝕜 i f) a ≠ 0 := by
    rw [← norm_ne_zero_iff (a := fderiv 𝕜 (iteratedFDeriv 𝕜 i f) a)]
    rwa [norm_fderiv_iteratedFDeriv, norm_ne_zero_iff]
  obtain ⟨v, hv⟩ := ContinuousLinearMap.exists_ne_zero hD
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hv
  let g : E → 𝕜 := fun x ↦ ℓ (iteratedFDeriv 𝕜 i f x)
  let g' : E →L[𝕜] 𝕜 := ℓ.comp (fderiv 𝕜 (iteratedFDeriv 𝕜 i f) a)
  have hg' : (g' : Module.Dual 𝕜 E) ≠ 0 := fun h ↦
    hℓ (by simpa [g'] using LinearMap.congr_fun h v)
  have hsurj : g'.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hg'
  have hiter : ContDiffAt 𝕜 r (iteratedFDeriv 𝕜 i f) a := hf.iteratedFDeriv_right le_rfl
  have hg : ContDiffAt 𝕜 r g a := ℓ.contDiff.contDiffAt.comp a hiter
  have hstrict : HasStrictFDerivAt g g' a :=
    hg.hasStrictFDerivAt' (ℓ.hasFDerivAt.comp a (hiter.differentiableAt hr).hasFDerivAt) hr
  have hzero : ∀ x, iteratedFDeriv 𝕜 i f x = 0 → g x = 0 := fun x hx ↦ by simp [g, hx]
  -- The implicit function theorem for `g`, with kernel coordinate `x ↦ π (x - a)` for a
  -- projection `π` onto `ker g'`; `θ` parametrizes the level set `g = 0` near `a`. This is the
  -- data of `HasStrictFDerivAt.implicitFunctionDataOfComplemented`, spelled out because that
  -- definition does not expose its fields, which the smoothness of `θ` needs.
  have hker : g'.ker.ClosedComplemented := g'.ker_closedComplemented_of_finiteDimensional_range
  let π : E →L[𝕜] ↥g'.ker := Classical.choose hker
  let φ : ImplicitFunctionData 𝕜 E 𝕜 ↥g'.ker :=
    { leftFun := g
      leftDeriv := g'
      rightFun x := π (x - a)
      rightDeriv := π
      pt := a
      hasStrictFDerivAt_leftFun := hstrict
      hasStrictFDerivAt_rightFun :=
        π.hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  let θ : ↥g'.ker → E := φ.implicitFunction 0
  -- The implicit-function API is stated for `φ.leftFun`; record that this field is `g`.
  have hleft : φ.leftFun = g := by simp only [φ]
  have hright : φ.rightFun φ.pt = 0 := by simp [φ]
  have hpt : φ.prodFun φ.pt = (0, 0) := by simp [φ, hzero a hi]
  have hθa : θ 0 = a := by
    have h := φ.implicitFunction_apply_image.self_of_nhds
    rwa [hright, hleft, hzero a hi] at h
  have hθ : ContDiffAt 𝕜 r θ 0 := by
    have hrightφ : ContDiffAt 𝕜 r φ.rightFun φ.pt := by
      simp only [φ]
      fun_prop
    have himplicit := φ.contDiffAt_implicitFunction hg hrightφ hr
    rw [hpt] at himplicit
    simpa only [comp_def, uncurry_apply_pair] using
      himplicit.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hθg : ∀ᶠ z in 𝓝 0, g (θ z) = 0 := by
    have h : Tendsto (fun z : ↥g'.ker ↦ ((0 : 𝕜), z)) (𝓝 0) (𝓝 (φ.prodFun φ.pt)) := by
      rw [hpt]
      exact tendsto_const_nhds.prodMk_nhds tendsto_id
    exact h.eventually φ.leftFun_implicitFunction
  have hcover : ∀ V ∈ 𝓝 (0 : ↥g'.ker),
      ∀ᶠ x in 𝓝 a, iteratedFDeriv 𝕜 i f x = 0 → x ∈ θ '' V := by
    intro V hV
    -- Near `a`, each `x` is `φ.implicitFunction (g x) (φ.rightFun x)`, and the kernel
    -- coordinate `φ.rightFun x` tends to `0` as `x` tends to `a`.
    have htend : Tendsto φ.rightFun (𝓝 a) (𝓝 0) :=
      hright ▸ φ.hasStrictFDerivAt_rightFun.continuousAt.tendsto
    filter_upwards [φ.implicitFunction_apply_image, htend hV] with x hx hxV hxi
    rw [hleft, hzero x hxi] at hx
    exact ⟨φ.rightFun x, hxV, hx⟩
  exact ⟨g, g', θ, hg, hstrict, hsurj, hzero, hθa, hθ, hθg, hcover,
    Module.Dual.finrank_ker_add_one_of_ne_zero hg'⟩

end TauCeti

end
