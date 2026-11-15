/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Analysis.ODE.InitialCondition

/-!
# Local smooth flows on Banach spaces

A locally `C^(n+1)` vector field on a real Banach space admits a local flow of the same joint
regularity in time and initial condition. The flow has initial value the identity, satisfies
the flow law, and solves the original differential equation near the chosen initial point at
time zero.

The global flow used to totalize this local object comes from a Lipschitz extension of the
field by radial retraction. This extension agrees with the field on a ball, but need not be
smooth outside that ball. Local smooth parameter dependence of the Picard equation suffices;
no smooth bump functions on the Banach space are assumed.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The local flow of a smooth Banach-space vector field.** A field that is `C^(n+1)` near
`a` admits a flow jointly `C^(n+1)` near `(a, 0)`, solving the equation there. Its initial value
and flow law hold for all points and times. Away from this neighbourhood it is the global flow
of a Lipschitz extension, rather than necessarily a solution of the original field. -/
theorem exists_contDiffAt_localFlow {n : ℕ∞} (v : E → E) {a : E}
    {s : Set E} (hv : ContDiffOn ℝ (n + 1) v s) (hs : s ∈ nhds a) :
    ∃ Φ : E → ℝ → E, ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ Φ p.1 p.2) (a, 0) ∧
      (∀ x, Φ x 0 = x) ∧ (∀ x t u, Φ x (t + u) = Φ (Φ x t) u) ∧
      ∀ᶠ p in nhds ((a, 0) : E × ℝ), HasDerivAt (Φ p.1) (v (Φ p.1 p.2)) p.2 := by
  obtain ⟨K, t, ht, hvt⟩ := ((hv.contDiffAt hs).of_le (by simp)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp (inter_mem ht hs)
  let g := v ∘ TauCeti.centeredRadialRetraction a r
  have hgK : LipschitzWith (K * 2) g :=
    (hvt.mono (fun x hx ↦ (hrt hx).1)).comp_centeredRadialRetraction hr.le
  have hgv : EqOn g v (ball a r) := fun x hx ↦ by
    simp only [g, Function.comp_apply,
      TauCeti.centeredRadialRetraction_of_mem_closedBall (ball_subset_closedBall hx)]
  have hgs : ContDiffOn ℝ (n + 1) g (ball a r) :=
    (hv.mono (fun x hx ↦ (hrt (ball_subset_closedBall hx)).2)).congr hgv
  have hga : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ globalSolution g hgK p.1 p.2) (a, 0) :=
    contDiffAt_globalSolution g hgK hgs (ball_mem_nhds a hr)
  refine ⟨globalSolution g hgK, hga, fun x ↦ globalSolution_zero g hgK x,
    fun x t u ↦ globalSolution_add g hgK x t u, ?_⟩
  have htends : Tendsto (fun p : E × ℝ ↦ globalSolution g hgK p.1 p.2)
      (nhds ((a, 0) : E × ℝ)) (nhds a) := by
    simpa only [ContinuousAt, globalSolution_zero] using hga.continuousAt
  filter_upwards [htends.eventually (ball_mem_nhds a hr)] with p hp
  rw [← hgv hp]
  exact hasDerivAt_globalSolution g hgK p.1 p.2

end ODE
