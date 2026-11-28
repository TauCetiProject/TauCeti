/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The differential vanishes along a slice

If a map `h : M → N` is constant on the image of `ι : S → M` near `s`, then the differential of `h`
at `ι s` vanishes on the tangent vectors `dι_s w` of the slice. This is the chain rule applied to
the locally constant composite `h ∘ ι`, and it needs no regularity: where `h` or `ι` is not
differentiable, the differential involved is zero by convention.

## Main declarations

* `TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const`: the statement for maps
  between manifolds.
* `TauCeti.mvfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_zero`: the case of a function with
  values in a normed space vanishing on the slice.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {E'' H'' N : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace N] [ChartedSpace H'' N]

/-- **The differential vanishes along a slice.** If a map `h` is constant on the image of
`ι : S → M` near `s`, then its differential at `ι s` vanishes on the range of `dι_s`. No regularity
is needed: where `h` or `ι` is not differentiable, the differential involved is zero. -/
theorem mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const {ι : S → M} {h : M → N} {s : S}
    {c : N} (h0 : h ∘ ι =ᶠ[𝓝 s] fun _ ↦ c) (w : TangentSpace J s) :
    mfderiv I K h (ι s) (mfderiv J I ι s w) = 0 := by
  by_cases hh : MDifferentiableAt I K h (ι s)
  · by_cases hιs : MDifferentiableAt J I ι s
    · rw [← mfderiv_comp_apply s hh hιs, h0.mfderiv_eq]
      simp
    · simp [mfderiv_zero_of_not_mdifferentiableAt hιs]
  · simp [mfderiv_zero_of_not_mdifferentiableAt hh]

/-- **The differential vanishes along a slice**, for a function `h` with values in a normed space
vanishing on the image of `ι : S → M` near `s`: its differential at `ι s` vanishes on the range of
`dι_s`. -/
theorem mvfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : S → M} {h : M → F} {s : S}
    (h0 : h ∘ ι =ᶠ[𝓝 s] 0) (w : TangentSpace J s) :
    mvfderiv I h (ι s) (mfderiv J I ι s w) = 0 :=
  mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const (K := 𝓘(𝕜, F)) h0 w

end TauCeti
