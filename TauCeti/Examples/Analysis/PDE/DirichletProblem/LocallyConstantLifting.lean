/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem.Lifting
public import TauCeti.Examples.Analysis.PDE.Neumann.TwoIntervals
import TauCeti.Analysis.Sobolev.Poincare.W1p0
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.LocallyConstant.ConnectedComponents

/-!
# Locally constant boundary liftings of the Dirichlet problem

A boundary lifting `g ∈ H¹(Ω)` with vanishing gradient, constant on each connected component of
`Ω`, solves the Dirichlet problem `L u = 0` in `Ω`, `u - g ∈ H¹₀(Ω)` for every operator with no
mass term (`TauCeti.PDE.dirichletSolutionWithLiftingL_eq_self_of_gradient_eq_zero`). This file
checks two instances, which pin down how the boundary condition is formulated.

* **The constant lifting.** On a nonempty bounded open `Ω ⊆ ℝ^{n+1}` the solution with the
  lifting `g = 1` and zero forcing is the constant `1`, which does not lie in `H¹₀(Ω)`
  (`dirichletSolutionWithLiftingL_const_one`). A plausible wrong formulation that solves for the
  unknown itself in `H¹₀(Ω)` with the forcing `-a(g, ·)` returns `0`, since `a(1, ·) = 0`
  (`solutionOfFunctional_neg_energyFormH1L_const_one`), and `0` has the wrong boundary values.
  The correct reduction solves for the correction `u - g ∈ H¹₀(Ω)` and adds `g` back.
* **Two components.** On `Ω = (0, 1) ∪ (2, 3)` a lifting equal to `0` on the first interval and
  to `1` on the second exists, with vanishing gradient
  (`exists_gradient_eq_zero_and_value_ae_eq_indicator`), and for `-Δ` with zero forcing
  the unique solution with these boundary values is the lifting itself
  (`sub_mem_w1p0Submodule_and_forall_energyFormH1_eq_zero_iff`): the problem is solved
  componentwise, and no connectedness of `Ω` is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2 (boundary liftings and
  the Lax–Milgram solution of the Dirichlet problem).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE

namespace TauCeti.Examples.DirichletProblemLocallyConstantLifting

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

section Constant

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  [IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  (hcoeff : MemLp
    (fun x => energyIntegrand (a x) (b x) ((0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) ⊤
    (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

/-- **The constant lifting.** On a nonempty bounded open `Ω ⊆ ℝ^{n+1}`, for an operator with no
mass term whose energy form is coercive on `H¹₀(Ω)`, the Dirichlet problem with boundary lifting
`g = 1` and zero forcing has the solution `1`, which does not lie in `H¹₀(Ω)`: its boundary
values are those of `g`, not zero. -/
theorem dirichletSolutionWithLiftingL_const_one
    (hne : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty)
    (hbdd : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    dirichletSolutionWithLiftingL hcoeff hcoercive (W1p.const 1, 0) = W1p.const 1 ∧
      W1p.const 1 ∉ w1p0Submodule volume Omega 2 :=
  ⟨dirichletSolutionWithLiftingL_eq_self_of_gradient_eq_zero hcoeff hcoercive .rfl
    (W1p.gradient_const 1), W1p.const_notMem_w1p0Submodule hne hbdd one_ne_zero⟩

/-- **The wrong formulation of the constant lifting.** Solving for the unknown itself in `H¹₀(Ω)`
with the forcing `-a(g, ·)` for the lifting `g = 1`, instead of for the correction `u - g`,
returns `0`: with no mass term, `a(1, ·) = 0`. Unlike the solution `1` of
`dirichletSolutionWithLiftingL_const_one`, it has zero boundary values. -/
theorem solutionOfFunctional_neg_energyFormH1L_const_one :
    hcoercive.solutionOfFunctional (-(energyFormH1L hcoeff (W1p.const 1)).comp
      (w1p0Submodule volume Omega 2).toSubmodule.subtypeL) = 0 := by
  have h : (energyFormH1L hcoeff (W1p.const 1)).comp
      (w1p0Submodule volume Omega 2).toSubmodule.subtypeL = 0 := by
    ext v
    rw [ContinuousLinearMap.comp_apply, energyFormH1L_apply,
      energyFormH1_eq_zero_of_gradient_eq_zero a b (W1p.gradient_const 1),
      zero_apply]
  simp [h]

end Constant

section TwoIntervals

open NeumannTwoIntervals

/-- **A lifting constant on each component.** On `(0, 1) ∪ (2, 3)` there is `g ∈ H¹` with
vanishing gradient, equal to `0` on `(0, 1)` and to `1` on `(2, 3)`. -/
theorem exists_gradient_eq_zero_and_value_ae_eq_indicator :
    ∃ g : W1p volume twoIntervals 2, W1p.gradient g = 0 ∧
      W1p.value g =ᵐ[volume.restrict (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))]
        (intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))).indicator 1 := by
  classical
  let x₀ : (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) :=
    ⟨_, intervalDomain_two_three_subset fiveHalves_mem_intervalDomain⟩
  let φ : ConnectedComponents (twoIntervals : Set (EuclideanSpace ℝ (Fin 1))) → ℝ :=
    fun c => if c = ConnectedComponents.mk x₀ then 1 else 0
  let g := W1p.componentFunEquivKerGradientL (mu := volume) (p := 2) φ
  refine ⟨g, ?_, ?_⟩
  · have h := LinearMap.mem_ker.1 g.property
    rwa [ContinuousLinearMap.coe_coe, W1p.gradientL_apply] at h
  filter_upwards [W1p.coeFn_value_componentFunEquivKerGradientL_apply (mu := volume) (p := 2) φ,
    ae_restrict_mem twoIntervals.isOpen.measurableSet] with x hx hxΩ
  rw [hx, componentFun_of_mem φ hxΩ]
  by_cases hx₂ : x ∈ intervalDomain 2 3
  · have hmk : ConnectedComponents.mk ⟨x, hxΩ⟩ = ConnectedComponents.mk x₀ :=
      (isPreconnected_intervalDomain 2 3).connectedComponents_mk_eq
        intervalDomain_two_three_subset hx₂ fiveHalves_mem_intervalDomain
    simp [φ, hmk, indicator_of_mem hx₂]
  · have hmk : ConnectedComponents.mk ⟨x, hxΩ⟩ ≠ ConnectedComponents.mk x₀ := by
      rw [Ne, ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn,
        connectedComponentIn_twoIntervals_fiveHalves]
      exact hx₂
    simp [φ, hmk, indicator_of_notMem hx₂]

/-- **The Dirichlet problem for `-Δ` on `(0, 1) ∪ (2, 3)` with componentwise constant boundary
values.** For a lifting `g ∈ H¹((0, 1) ∪ (2, 3))` equal to `0` on `(0, 1)` and to `1` on
`(2, 3)`, an element `u` satisfies `u - g ∈ H¹₀` and `∫ ∇u · ∇v = 0` for every `v ∈ H¹₀` exactly
when `u = g`. -/
theorem sub_mem_w1p0Submodule_and_forall_energyFormH1_eq_zero_iff
    {g u : W1p volume twoIntervals 2}
    (hg : W1p.value g =ᵐ[volume.restrict (twoIntervals : Set (EuclideanSpace ℝ (Fin 1)))]
      (intervalDomain 2 3 : Set (EuclideanSpace ℝ (Fin 1))).indicator 1) :
    (u - g ∈ w1p0Submodule volume twoIntervals 2 ∧
      ∀ v ∈ w1p0Submodule volume twoIntervals 2, energyFormH1 (fun _ => 1) 0 0 u v = 0) ↔
      u = g := by
  obtain ⟨g₀, hg₀, hval₀⟩ := exists_gradient_eq_zero_and_value_ae_eq_indicator
  have hgrad : W1p.gradient g = 0 := by
    rwa [W1p.ext_value (Lp.ext (hg.trans hval₀.symm))]
  obtain ⟨hcoeff, hcoercive⟩ := exists_isCoercive_laplacian_of_isBounded (n := 0)
    (Omega := twoIntervals) isBounded_twoIntervals
  -- The solution with lifting `g` and zero forcing is `g` itself.
  have hsol : u = g ↔ dirichletSolutionWithLiftingL hcoeff hcoercive (g, 0) = u := by
    rw [dirichletSolutionWithLiftingL_eq_self_of_gradient_eq_zero hcoeff hcoercive .rfl hgrad,
      eq_comm]
  rw [hsol, dirichletSolutionWithLiftingL_eq_iff hcoeff hcoercive]
  exact and_congr_right fun _ => ⟨fun h v => by simpa using h v v.property,
    fun h v hv => by simpa using h ⟨v, hv⟩⟩

end TwoIntervals

end TauCeti.Examples.DirichletProblemLocallyConstantLifting
