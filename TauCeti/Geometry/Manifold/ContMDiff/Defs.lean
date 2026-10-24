/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# The set of points where a map is `C^n`

For `n ≠ ∞`, a map between manifolds is `C^n` at a point if and only if it is `C^n` on a
neighbourhood of that point (`contMDiffAt_iff_contMDiffAt_nhds`), so the set of points where it
is `C^n` is open. This file records that openness and that `C¹` regularity at a point implies
differentiability throughout a neighbourhood.

It also records that the regularity indices `∞` and `ω` are nonzero, as `NeZero` instances, so
that statements about `C^n` manifolds assuming `[NeZero n]` (that is, `1 ≤ n`) apply to smooth
and analytic manifolds.

## Main results

* `TauCeti.isOpen_setOfPred_contMDiffAt`: for `n ≠ ∞`, the set of points where a map is `C^n` is
  open.
* `TauCeti.ContMDiffAt.eventually_mdifferentiableAt`: `C^n` regularity at a point, with `1 ≤ n`,
  implies differentiability throughout a neighbourhood.
* The instances `NeZero (∞ : ℕ∞ω)` and `NeZero (ω : ℕ∞ω)`.
-/

public section

open scoped ContDiff

namespace TauCeti

/-- The smoothness index `∞` is nonzero, so smooth manifolds are differentiable. -/
instance : NeZero (∞ : ℕ∞ω) :=
  ⟨WithTop.coe_ne_zero.2 ENat.top_ne_zero⟩

/-- The analyticity index `ω` is nonzero, so analytic manifolds are differentiable. -/
instance : NeZero (ω : ℕ∞ω) :=
  ⟨WithTop.top_ne_zero⟩

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω} {f : M → M'}

/-- For `n ≠ ∞`, the set of points where a map is `C^n` is open.  This fails for `n = ∞`, where
the neighbourhood on which `f` is `C^k` may shrink with `k`. -/
theorem isOpen_setOfPred_contMDiffAt [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    IsOpen {x | ContMDiffAt I I' n f x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ (contMDiffAt_iff_contMDiffAt_nhds hn).1 hx

/-- A map between `C¹` manifolds that is `C^n` at a point, with `1 ≤ n`, is differentiable
throughout a neighbourhood of that point. -/
theorem ContMDiffAt.eventually_mdifferentiableAt [IsManifold I 1 M] [IsManifold I' 1 M']
    {x : M} (hf : ContMDiffAt I I' n f x) (hn : 1 ≤ n) :
    ∀ᶠ y in nhds x, MDifferentiableAt I I' f y := by
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).1
    (hf.of_le hn)] with y hy
  exact hy.mdifferentiableAt one_ne_zero

end TauCeti

end
