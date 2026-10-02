/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.RiemannSurface.Meromorphic

/-!
# Meromorphic functions on the upper half-plane

A function `f : ℍ → E` is meromorphic at `τ`, as a function on the Riemann surface `ℍ`
(`TauCeti.RiemannSurface.MeromorphicAt`), exactly when its extension `f ∘ ofComplex` to `ℂ` is
meromorphic at `τ` in the sense of Mathlib's `MeromorphicAt`, and the two orders at `τ` agree.
This is the form in which orders of modular functions, stated for `f ∘ ofComplex`, enter the
theory of Riemann surfaces, in the same way as `UpperHalfPlane.mdifferentiableAt_iff` does for
holomorphy.
-/

public section

open Filter Topology UpperHalfPlane

open scoped Manifold

namespace TauCeti.UpperHalfPlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℍ → E} {τ : ℍ}

/-- The representative of `f` in the chart of `ℍ` at `τ` agrees with `f ∘ ofComplex` near `τ`. -/
private theorem comp_chartAt_symm_eventuallyEq {α : Type*} (f : ℍ → α) (τ : ℍ) :
    f ∘ (chartAt ℂ τ).symm =ᶠ[𝓝 (τ : ℂ)] f ∘ ofComplex := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
  have hwt : w ∈ (chartAt ℂ τ).target := by simpa using hw
  rw [Function.comp_apply, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  congr 1
  ext
  simpa using (chartAt ℂ τ).right_inv hwt

/-- A function on the upper half-plane is meromorphic at `τ` exactly when its extension by
`ofComplex` is meromorphic at `τ`. -/
theorem meromorphicAt_iff_meromorphicAt_comp_ofComplex :
    RiemannSurface.MeromorphicAt f τ ↔ MeromorphicAt (f ∘ ofComplex) τ := by
  rw [RiemannSurface.meromorphicAt_def]
  exact MeromorphicAt.meromorphicAt_congr
    ((comp_chartAt_symm_eventuallyEq f τ).filter_mono nhdsWithin_le_nhds)

/-- The order of a function on the upper half-plane at `τ` is the meromorphic order of its
extension by `ofComplex` at `τ`. -/
theorem meromorphicOrderAt_eq_meromorphicOrderAt_comp_ofComplex :
    RiemannSurface.meromorphicOrderAt f τ = meromorphicOrderAt (f ∘ ofComplex) τ := by
  rw [RiemannSurface.meromorphicOrderAt_def]
  exact meromorphicOrderAt_congr
    ((comp_chartAt_symm_eventuallyEq f τ).filter_mono nhdsWithin_le_nhds)

end TauCeti.UpperHalfPlane
