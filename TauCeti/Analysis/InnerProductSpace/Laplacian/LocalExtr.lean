/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Calculus.DerivativeTest
public import TauCeti.Topology.Order.LocalExtr

import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# The Laplacian at an interior local extremum

At an interior local maximum of a `C²` function the Laplacian is nonpositive, and at an interior
local minimum it is nonnegative; this is the second-derivative form of the maximum principle.
The Laplacian is the trace of the Hessian, and `TauCeti.Analysis.Calculus.DerivativeTest` signs
each diagonal Hessian entry at a local extremum.

## Main declarations

* `TauCeti.laplacian_nonpos_of_isLocalMax` / `TauCeti.laplacian_nonneg_of_isLocalMin`: the
  Laplacian is nonpositive at a local maximum and nonnegative at a local minimum.
* `TauCeti.not_isLocalMax_of_laplacian_pos` / `TauCeti.not_isLocalMin_of_laplacian_neg`: a
  strictly subharmonic function (`0 < Δ f x`) has no interior local maximum, the classical first
  step of the maximum principle; the superharmonic mirror image has no interior local minimum.
* `TauCeti.laplacian_nonneg_of_isMinOn_prod`: if `(x, s)` minimizes `q` over `K × S` with `x` in
  the interior of `K`, the Laplacian of `y ↦ q y (γ y)` is nonnegative at `x` for every local
  section `γ` of `S` through `s` along which this function is `C²` at `x`. This is the Laplacian
  test for a lower envelope `x ↦ min_{s ∈ S} q x s`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {x : E}

/-- **Maximum principle, second-derivative form.** At an interior local maximum of a `C²`
function the Laplacian is nonpositive. -/
theorem laplacian_nonpos_of_isLocalMax (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    Δ f x ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  exact Finset.sum_nonpos fun i _ => by
    simpa [iteratedFDeriv_two_apply] using fderiv_fderiv_self_nonpos_of_isLocalMax
      (hf.eventually_differentiableAt (by norm_num)) hmax _

/-- **Minimum principle, second-derivative form.** At an interior local minimum of a `C²`
function the Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) :
    0 ≤ Δ f x := by
  simpa [laplacian_neg] using laplacian_nonpos_of_isLocalMax (f := -f) hf.neg hmin.neg

/-- A strictly subharmonic `C²` function (`0 < Δ f x`) has no interior local maximum at `x`. This
is the classical opening move of the maximum principle. -/
theorem not_isLocalMax_of_laplacian_pos (hf : ContDiffAt ℝ 2 f x) (hlap : 0 < Δ f x) :
    ¬ IsLocalMax f x := fun hmax => (laplacian_nonpos_of_isLocalMax hf hmax).not_gt hlap

/-- A strictly superharmonic `C²` function (`Δ f x < 0`) has no interior local minimum at `x`. -/
theorem not_isLocalMin_of_laplacian_neg (hf : ContDiffAt ℝ 2 f x) (hlap : Δ f x < 0) :
    ¬ IsLocalMin f x := fun hmin => (laplacian_nonneg_of_isLocalMin hf hmin).not_gt hlap

open Topology in
/-- **The Laplacian test for a lower envelope.** If `(x, s)` minimizes `q` over `K × S` and `x`
lies in the interior of `K`, then for every local section `γ` of `S` through `s` such that
`y ↦ q y (γ y)` is `C²` at `x`, the Laplacian of `y ↦ q y (γ y)` is nonnegative at `x`. -/
theorem laplacian_nonneg_of_isMinOn_prod {ι : Type*} {K : Set E} {S : Set ι} {q : E → ι → ℝ}
    {s : ι} {γ : E → ι} (hx : x ∈ interior K)
    (hmin : IsMinOn (fun p : E × ι ↦ q p.1 p.2) (K ×ˢ S) (x, s)) (hγx : γ x = s)
    (hγ : ∀ᶠ y in 𝓝 x, γ y ∈ S) (hcd : ContDiffAt ℝ 2 (fun y ↦ q y (γ y)) x) :
    0 ≤ Δ (fun y ↦ q y (γ y)) x :=
  laplacian_nonneg_of_isLocalMin hcd (isLocalMin_of_isMinOn_prod hx hmin hγx hγ)

end TauCeti
