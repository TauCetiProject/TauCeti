/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Mixed derivatives of a family with a `C¹` velocity

Let `G : ℝ × E → F` be a family of maps `G (u, ·)` whose velocity `∂ᵤ G = g` is a `C¹` map of
`(u, z)` near `(t, x)`, and whose slice `G (t, ·)` is differentiable at `x`. Then the spatial
derivative of `G` at `x` can be differentiated in the parameter at `t`, and the two partial
derivatives commute:

`∂ᵤ (D_z G (u, x)) = D_z (∂ᵤ G (u, x))` at `u = t`

(`TauCeti.hasDerivAt_fderiv_slice_of_contDiffAt_velocity`). No second derivative of `G` is
assumed. This is the form in which the variational equation of the flow of a `C¹` vector field is
obtained: such a flow is only `C¹`, but its velocity `v (G (u, z))` is again `C¹`, so the spatial
derivative of the flow solves `∂ᵤ D_z G = Dv (G) ∘ D_z G`.

The proof integrates the velocity: near the base point, `G (u, z) = G (t, z) + ∫ₜᵘ g (τ, z) dτ`.
Differentiating under the integral sign, which is allowed since `g` is `C¹` on a compact box,
gives `D_z G (u, x) = D_z G (t, x) + ∫ₜᵘ D_z g (τ, x) dτ`, and the fundamental theorem of calculus
differentiates the right-hand side in `u`.

## Main results

* `TauCeti.hasDerivAt_fderiv_slice_of_contDiffAt_velocity`: the parameter derivative of the
  spatial derivative of a family with a `C¹` velocity is the spatial derivative of the velocity.

## References

* P. Hartman, *Ordinary Differential Equations*, 2nd ed., SIAM, 2002, Chapter V, Theorem 3.1,
  for the variational equation of a `C¹` vector field.
-/

public section

open Filter Set Metric
open scoped Topology Interval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- **Mixed derivatives of a family with a `C¹` velocity.** Let `g : ℝ × E → F`, `C¹` at `(t, x)`,
be the velocity of `G : ℝ × E → F` near `(t, x)`: the curves `u ↦ G (u, z)` have velocity
`g (u, z)`. If the slice `G (t, ·)` is differentiable at `x`, then the spatial derivative
`u ↦ D_z G (u, x)` has derivative `D_z g (t, x)` at `t`. This applies to a `C¹` map `G` with a
`C¹` velocity. -/
theorem hasDerivAt_fderiv_slice_of_contDiffAt_velocity {G g : ℝ × E → F} {t : ℝ} {x : E}
    (hGt : DifferentiableAt ℝ (fun z ↦ G (t, z)) x) (hg : ContDiffAt ℝ 1 g (t, x))
    (hvel : ∀ᶠ p in 𝓝 (t, x), HasDerivAt (fun u ↦ G (u, p.2)) (g p) p.1) :
    HasDerivAt (fun u ↦ fderiv ℝ (fun z ↦ G (u, z)) x) (fderiv ℝ (fun z ↦ g (t, z)) x) t := by
  -- A ball about `(t, x)` on which `g` is `C¹` and `g` is the velocity of `G`.
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hV hvel)
  have hgC : ContDiffOn ℝ 1 g (ball (t, x) ε) := hgV.mono fun p hp ↦ (hball hp).1
  have hmem {τ : ℝ} {z : E} (hτ : τ ∈ ball t ε) (hz : z ∈ ball x ε) :
      (τ, z) ∈ ball (t, x) ε := by
    rw [← ball_prod_same]
    exact ⟨hτ, hz⟩
  have hsub {u : ℝ} (hu : u ∈ ball t ε) : [[t, u]] ⊆ ball t ε :=
    (convex_ball t ε).ordConnected.uIcc_subset (mem_ball_self hε) hu
  -- Integrating the velocity: `G (u, z) = G (t, z) + ∫ₜᵘ g (τ, z) dτ` on the box.
  have hint {u : ℝ} (hu : u ∈ ball t ε) {z : E} (hz : z ∈ ball x ε) :
      G (u, z) = G (t, z) + ∫ τ in t..u, g (τ, z) := by
    have hcont : ContinuousOn (fun τ ↦ g (τ, z)) [[t, u]] :=
      hgC.continuousOn.comp (by fun_prop) fun τ hτ ↦ hmem (hsub hu hτ) hz
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ ↦ G (τ, z))
      (fun τ hτ ↦ (hball (hmem (hsub hu hτ) hz)).2) hcont.intervalIntegrable]
    abel
  -- Differentiating under the integral sign.
  set φ : ℝ → E →L[ℝ] F := fun τ ↦ fderiv ℝ (fun z ↦ g (τ, z)) x
  have hfd {u : ℝ} (hu : u ∈ ball t ε) :
      fderiv ℝ (fun z ↦ G (u, z)) x = fderiv ℝ (fun z ↦ G (t, z)) x + ∫ τ in t..u, φ τ := by
    have hI : HasFDerivAt (fun z ↦ ∫ τ in t..u, g (τ, z)) (∫ τ in t..u, φ τ) x :=
      intervalIntegral.hasFDerivAt_integral_of_contDiffOn (f := fun z τ ↦ g (τ, z))
        (ball_mem_nhds x hε) (hgC.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
          fun p hp ↦ hmem (hsub hu hp.2) hp.1)
    refine ((hGt.hasFDerivAt.add hI).congr_of_eventuallyEq ?_).fderiv
    filter_upwards [ball_mem_nhds x hε] with z hz
    exact hint hu hz
  -- The partial derivative `φ` of the velocity is continuous near `t`.
  have hφ : ContinuousOn φ (ball t ε) := by
    have hfg : ContinuousOn (fun τ : ℝ ↦ fderiv ℝ g (τ, x)) (ball t ε) :=
      (hgC.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp (by fun_prop)
        fun τ hτ ↦ hmem hτ (mem_ball_self hε)
    refine (hfg.clm_comp (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))).congr
      fun τ hτ ↦ ?_
    exact fderiv_slice_right ((hgC.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (hmem hτ (mem_ball_self hε))))
  -- The fundamental theorem of calculus differentiates `u ↦ ∫ₜᵘ φ`.
  have hFTC : HasDerivAt (fun u ↦ ∫ τ in t..u, φ τ) (φ t) t :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hφ.stronglyMeasurableAtFilter isOpen_ball t (mem_ball_self hε))
      (hφ.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε)))
  refine (hFTC.const_add (fderiv ℝ (fun z ↦ G (t, z)) x)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t hε] with u hu
  exact hfd hu

end TauCeti
