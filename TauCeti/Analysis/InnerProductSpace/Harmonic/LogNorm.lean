/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry

/-!
# Harmonicity of the logarithm of the norm in two dimensions

Mathlib's `AnalyticAt.harmonicAt_log_norm` shows that `z ↦ log ‖z‖` is harmonic away from `0` on
`ℂ`. Transporting along a linear isometry onto `ℂ`, this file shows that `x ↦ log ‖x - a‖` is
harmonic away from `a` in every two-dimensional real inner product space, such as
`EuclideanSpace ℝ (Fin 2)`.

In the plane, `x ↦ log ‖x - a‖` plays the role that the Newtonian kernel plays in higher
dimensions. These results supply the harmonicity behind the logarithmic exterior sphere barrier
`TauCeti.isBarrier_log_norm_sub` in `TauCeti.Analysis.PDE.Perron.Barrier`. That barrier handles
the two-dimensional case of Perron's method for the Dirichlet problem on domains satisfying the
exterior sphere condition.

## Main declarations

* `TauCeti.harmonicAt_log_norm_sub_of_finrank_eq_two`: harmonicity of `x ↦ log ‖x - a‖` away
  from `a` in a two-dimensional real inner product space.
* `TauCeti.harmonicOnNhd_log_norm_sub_of_finrank_eq_two`: the same on the complement of `a`.
-/

public section

namespace TauCeti

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a two-dimensional real inner product space, `x ↦ log ‖x - a‖` is harmonic at every point
other than `a`. -/
theorem harmonicAt_log_norm_sub_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) {x a : E}
    (hxa : x ≠ a) : HarmonicAt (fun y ↦ Real.log ‖y - a‖) x := by
  -- Transport to `ℂ`, where `log ‖z - l a‖` is the log-modulus of an analytic function.
  let l : E ≃ₗᵢ[ℝ] ℂ := ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr.trans
    Complex.orthonormalBasisOneI.repr.symm
  have hfun : (fun y ↦ Real.log ‖y - a‖) = (fun z : ℂ ↦ Real.log ‖z - l a‖) ∘ l := by
    ext y
    simp [← map_sub]
  rw [hfun, harmonicAt_comp_linearIsometryEquiv_right_iff]
  exact (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm
    (sub_ne_zero.2 (l.injective.ne hxa))

/-- In a two-dimensional real inner product space, `x ↦ log ‖x - a‖` is harmonic on the
complement of `a`. -/
theorem harmonicOnNhd_log_norm_sub_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) (a : E) :
    HarmonicOnNhd (fun y ↦ Real.log ‖y - a‖) ({a}ᶜ : Set E) :=
  fun _ hx ↦ harmonicAt_log_norm_sub_of_finrank_eq_two hE hx

end TauCeti
