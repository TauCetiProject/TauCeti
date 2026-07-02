/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The Laplacian at an interior local extremum

The second-derivative test underlies the maximum principle for the Laplacian: at an interior
local maximum of a `C²` function the Laplacian is nonpositive, and at an interior local minimum
it is nonnegative. Mathlib already has the *sufficient* second-derivative test
(`isLocalMax_of_deriv_deriv_neg`: a negative second derivative forces a local maximum); this file
supplies the *necessary* direction and its multivariate Laplacian consequence, the first
building block of the Lane C maximum principle in the PDE roadmap.

The one-dimensional necessary test `deriv_deriv_nonpos_of_isLocalMax` says that at a local maximum
of a twice-differentiable `g : ℝ → ℝ` the second derivative is nonpositive. Restricting a function
`f : E → ℝ` to a line `t ↦ f (x + t • w)` turns each diagonal Hessian entry into such a second
derivative (`deriv_deriv_comp_line`), and summing over an orthonormal basis gives the Laplacian.

## Main declarations

* `TauCeti.deriv_deriv_nonpos_of_isLocalMax` / `TauCeti.deriv_deriv_nonneg_of_isLocalMin`: the
  necessary one-dimensional second-derivative test.
* `TauCeti.deriv_deriv_comp_line`: the second derivative of the restriction of `f` to a line is a
  diagonal entry of the Hessian `fderiv ℝ (fderiv ℝ f) x w w`.
* `TauCeti.fderiv_fderiv_self_nonpos_of_isLocalMax` /
  `TauCeti.fderiv_fderiv_self_nonneg_of_isLocalMin`: the Hessian is negative (resp. positive)
  semidefinite on the diagonal at a local extremum.
* `TauCeti.laplacian_nonpos_of_isLocalMax` / `TauCeti.laplacian_nonneg_of_isLocalMin`: the
  Laplacian is nonpositive at a local maximum and nonnegative at a local minimum.
* `TauCeti.not_isLocalMax_of_laplacian_pos` / `TauCeti.not_isLocalMin_of_laplacian_neg`: a
  strictly subharmonic function (`0 < Δ f x`) has no interior local maximum, the classical first
  step of the maximum principle; the superharmonic mirror image has no interior local minimum.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology

/-- **Necessary second-derivative test.** At a local maximum of a twice-differentiable function
`g : ℝ → ℝ`, the second derivative is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContDiffAt ℝ 2 g t₀) (hmax : IsLocalMax g t₀) :
    deriv (deriv g) t₀ ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have hd : deriv g t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g t₀ := isLocalMin_of_deriv_deriv_pos h hd hg.continuousAt
  -- Being both a local minimum and a local maximum, `g` is eventually constant near `t₀`.
  have hconst : g =ᶠ[𝓝 t₀] fun _ => g t₀ := by
    filter_upwards [hmax, hmin] with y hy hy' using le_antisymm hy hy'
  have hderiv : deriv g =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.deriv] with y hy
    simpa using hy
  have hzero : deriv (deriv g) t₀ = 0 := by
    rw [hderiv.deriv_eq]; simp
  linarith

/-- **Necessary second-derivative test, minimum version.** At a local minimum of a
twice-differentiable function `g : ℝ → ℝ`, the second derivative is nonnegative. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContDiffAt ℝ 2 g t₀) (hmin : IsLocalMin g t₀) :
    0 ≤ deriv (deriv g) t₀ := by
  have := deriv_deriv_nonpos_of_isLocalMax (g := -g) hg.neg hmin.neg
  simpa using this

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine line `t ↦ x + t • w` is smooth at `0`. -/
private theorem contDiffAt_line (x w : E) : ContDiffAt ℝ 2 (fun t : ℝ => x + t • w) 0 := by
  fun_prop

/-- The affine line `t ↦ x + t • w` tends to `x` as `t → 0`. -/
private theorem tendsto_line (x w : E) :
    Filter.Tendsto (fun t : ℝ => x + t • w) (𝓝 0) (𝓝 x) := by
  have : ContinuousAt (fun t : ℝ => x + t • w) 0 := by fun_prop
  simpa using this.tendsto

/-- The restriction of `f` to a line inherits a local maximum from `f`. -/
private theorem isLocalMax_comp_line {f : E → ℝ} {x : E} (hmax : IsLocalMax f x) (w : E) :
    IsLocalMax (fun t : ℝ => f (x + t • w)) 0 := by
  filter_upwards [(tendsto_line x w).eventually hmax] with t ht
  simpa using ht

/-- The restriction of `f` to a line inherits a local minimum from `f`. -/
private theorem isLocalMin_comp_line {f : E → ℝ} {x : E} (hmin : IsLocalMin f x) (w : E) :
    IsLocalMin (fun t : ℝ => f (x + t • w)) 0 := by
  filter_upwards [(tendsto_line x w).eventually hmin] with t ht
  simpa using ht

/-- The restriction of a `C²` function `f` to a line is `C²` at `0`. -/
private theorem contDiffAt_comp_line {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (w : E) :
    ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • w)) 0 :=
  (show ContDiffAt ℝ 2 f ((fun t : ℝ => x + t • w) 0) by simpa using hf).comp 0
    (contDiffAt_line x w)

/-- The second derivative of the restriction of `f` to the line `t ↦ x + t • w` is the diagonal
Hessian entry `fderiv ℝ (fderiv ℝ f) x w w`. -/
theorem deriv_deriv_comp_line {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (w : E) :
    deriv (deriv fun t : ℝ => f (x + t • w)) 0 = fderiv ℝ (fderiv ℝ f) x w w := by
  -- The line and its derivative.
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • w) w t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  -- `f` is differentiable on a neighbourhood of `x`, so the first derivative of the restriction is
  -- `t ↦ fderiv ℝ f (x + t • w) w` near `0`.
  have hfev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x + t • w) :=
    (tendsto_line x w).eventually hfev
  have hev : (deriv fun t : ℝ => f (x + t • w)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (x + t • w) w := by
    filter_upwards [hdiff] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlin t)).deriv
  -- `fderiv ℝ f` is differentiable at `x` since `f` is `C²`.
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDx : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • w) := by
    simpa using hD.hasFDerivAt
  -- Differentiate `t ↦ fderiv ℝ f (x + t • w) w` at `0` by the chain rule (staying with the
  -- `ℝ`-valued composition to avoid the two `AddCommGroup` structures on `E →L[ℝ] ℝ`).
  have h2 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp_hasDerivAt 0
    (hDx.comp_hasDerivAt 0 (hlin 0))
  have h2' : deriv (fun t : ℝ => fderiv ℝ f (x + t • w) w) 0 = fderiv ℝ (fderiv ℝ f) x w w := by
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using h2.deriv
  calc deriv (deriv fun t : ℝ => f (x + t • w)) 0
      = deriv (fun t : ℝ => fderiv ℝ f (x + t • w) w) 0 := hev.deriv_eq
    _ = fderiv ℝ (fderiv ℝ f) x w w := h2'

/-- At an interior local maximum of a `C²` function `f : E → ℝ`, every diagonal Hessian entry is
nonpositive. -/
theorem fderiv_fderiv_self_nonpos_of_isLocalMax {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) (w : E) :
    fderiv ℝ (fderiv ℝ f) x w w ≤ 0 := by
  rw [← deriv_deriv_comp_line hf w]
  exact deriv_deriv_nonpos_of_isLocalMax (contDiffAt_comp_line hf w) (isLocalMax_comp_line hmax w)

/-- At an interior local minimum of a `C²` function `f : E → ℝ`, every diagonal Hessian entry is
nonnegative. -/
theorem fderiv_fderiv_self_nonneg_of_isLocalMin {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) (w : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x w w := by
  rw [← deriv_deriv_comp_line hf w]
  exact deriv_deriv_nonneg_of_isLocalMin (contDiffAt_comp_line hf w) (isLocalMin_comp_line hmin w)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Maximum principle, second-derivative form.** At an interior local maximum of a `C²`
function the Laplacian is nonpositive. -/
theorem laplacian_nonpos_of_isLocalMax {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    Δ f x ≤ 0 := by
  have hL := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)) x
  rw [hL]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simpa using fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax (stdOrthonormalBasis ℝ E i)

/-- **Minimum principle, second-derivative form.** At an interior local minimum of a `C²`
function the Laplacian is nonnegative. -/
theorem laplacian_nonneg_of_isLocalMin {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) :
    0 ≤ Δ f x := by
  have := laplacian_nonpos_of_isLocalMax (f := -f) hf.neg hmin.neg
  rw [laplacian_neg] at this
  simpa using this

/-- A strictly subharmonic `C²` function (`0 < Δ f x`) has no interior local maximum at `x`. This
is the classical opening move of the maximum principle. -/
theorem not_isLocalMax_of_laplacian_pos {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hlap : 0 < Δ f x) :
    ¬ IsLocalMax f x := fun hmax => absurd (laplacian_nonpos_of_isLocalMax hf hmax) (not_le.2 hlap)

/-- A strictly superharmonic `C²` function (`Δ f x < 0`) has no interior local minimum at `x`. -/
theorem not_isLocalMin_of_laplacian_neg {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hlap : Δ f x < 0) :
    ¬ IsLocalMin f x := fun hmin => absurd (laplacian_nonneg_of_isLocalMin hf hmin) (not_le.2 hlap)

end FiniteDimensional

end TauCeti
