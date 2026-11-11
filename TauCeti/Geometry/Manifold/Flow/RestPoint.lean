/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The flow of a vector field at a rest point

Let `v` be a `C¹` vector field on a boundaryless manifold `M` modelled on a finite-dimensional
real space, and let `p` be a rest point, `v p = 0`. Read in the extended chart `φ` at `p`, the
field is the map `g z = v (φ⁻¹ z)` written in the coordinates of that chart, and its derivative at
`φ p` is the linearization `L = TauCeti.chartLinearization I v p` of `v` at `p`.

The trajectory of `p` is constant, so every time map `Φ_{s,t}` of the flow of `v` fixes `p`, and
its derivative at `p` is the exponential of the linearization:

`dΦ_{s,t}(p) = exp ((t - s) L)`

(`TauCeti.mfderiv_timeDependentFlowOf_eq_exp`). Consequently `p` is a nondegenerate fixed point of
`Φ_{s,t}` exactly when `exp ((t - s) L)` fixes no nonzero vector
(`TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff`), and for short times, `t ≠ s` with
`|t - s| ‖L‖ < log 2`, exactly when `L` is injective
(`TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff_of_abs_mul_norm_lt`). Since the
linearization of `c • v` is `c • L` (`TauCeti.chartLinearization_smul`), the time-one map of the
field `ε v` has the nondegenerate fixed point `p` for all small `ε ≠ 0` exactly when `L` is
injective. For a Hamiltonian vector field `X_F` at a critical point this is the statement that the
constant orbits of a `C²`-small Morse Hamiltonian are nondegenerate.

The proof is local. In the chart the field is `C¹` near `φ p`, and the flow of the coordinate
field, cut off away from `φ p` (`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`),
has derivatives solving the variational equation `D' = Dg(ψ_τ z) ∘ D`. At the rest point this
equation has the constant coefficient `L`, so its solution is the exponential. Trajectories of `v`
starting near `p` stay in the chart up to time `t`, so by uniqueness of solutions they are the
trajectories of the coordinate flow read through the chart.

## Main definitions

* `TauCeti.chartLinearization I v p`: the derivative at `φ p` of the coordinate expression of `v`
  in the extended chart `φ` at `p`.

## Main results

* `TauCeti.mfderiv_timeDependentFlowOf_eq_exp`: at a rest point, the derivative of the time map of
  the flow from `s` to `t` is `exp ((t - s) L)`.
* `TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff`: the rest point is a nondegenerate fixed
  point of the time map exactly when `exp ((t - s) L)` fixes no nonzero vector.
* `TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff_of_abs_mul_norm_lt`: for short times,
  exactly when `L` is injective.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, 3rd ed., Academic Press, 2013, Chapter 8 (linearization at an
  equilibrium).
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2.
-/

public section

noncomputable section

open Function Set Filter NormedSpace
open scoped Manifold NNReal Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The **linearization of a vector field in a chart**: the derivative at `φ p` of the coordinate
expression `z ↦ v (φ⁻¹ z)` of `v` in the extended chart `φ` at `p`, where the vector at `φ⁻¹ z` is
written in the coordinates of the chart at `p`. At a rest point of `v` it is the coefficient of
the linearized equation along the constant trajectory. -/
def chartLinearization (v : (x : M) → TangentSpace I x) (p : M) : E →L[ℝ] E :=
  fderiv ℝ (fun z ↦ tangentCoordChange I ((extChartAt I p).symm z) p ((extChartAt I p).symm z)
    (v ((extChartAt I p).symm z))) (extChartAt I p p)

theorem chartLinearization_def (v : (x : M) → TangentSpace I x) (p : M) :
    chartLinearization I v p =
      fderiv ℝ (fun z ↦ tangentCoordChange I ((extChartAt I p).symm z) p ((extChartAt I p).symm z)
        (v ((extChartAt I p).symm z))) (extChartAt I p p) :=
  (rfl)

/-- The linearization of a constant multiple of a vector field is the same multiple of its
linearization. -/
@[simp]
theorem chartLinearization_smul (c : ℝ) (v : (x : M) → TangentSpace I x) (p : M) :
    chartLinearization I (c • v) p = c • chartLinearization I v p := by
  have hfun : (fun z ↦ tangentCoordChange I ((extChartAt I p).symm z) p ((extChartAt I p).symm z)
      ((c • v) ((extChartAt I p).symm z))) = c • fun z ↦ tangentCoordChange I
        ((extChartAt I p).symm z) p ((extChartAt I p).symm z) (v ((extChartAt I p).symm z)) := by
    funext z
    exact map_smul _ c _
  rw [chartLinearization_def, chartLinearization_def, hfun, fderiv_const_smul_field]
  rfl

variable {I} [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M]
  {v : (x : M) → TangentSpace I x} {p : M}

/-- **The derivative of the flow at a rest point.** Let `v` be a `C¹` vector field on a
boundaryless manifold modelled on a finite-dimensional space, and `p` a point with `v p = 0`.
Then the derivative at `p` of the time map of the flow of `v` from time `s` to time `t` is the
exponential `exp ((t - s) L)` of the linearization `L` of `v` at `p`. -/
theorem mfderiv_timeDependentFlowOf_eq_exp
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) (s t : ℝ) :
    mfderiv I I (timeDependentFlowOf (fun _ ↦ v) s t) p =
      exp ((t - s) • chartLinearization I v p) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun q : ℝ × M ↦ (⟨q.2, v q.2⟩ : TangentBundle I M)) := hv.comp contMDiff_snd
  set φ := extChartAt I p
  set x₀ := φ p
  set c := t - s
  set g : E → E := fun z ↦ tangentCoordChange I (φ.symm z) p (φ.symm z) (v (φ.symm z)) with hg
  have hrange : range I ∈ 𝓝 x₀ :=
    range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint
  have htarget : φ.target ∈ 𝓝 x₀ := by
    rw [← nhdsWithin_eq_nhds.2 hrange]
    exact extChartAt_target_mem_nhdsWithin p
  have hpφ : φ.symm x₀ = p := extChartAt_to_inv p
  -- At a chart point `φ q`, the coordinate field is `v q` in the coordinates of the chart at `p`.
  have hgφ {q : M} (hq : q ∈ φ.source) : g (φ q) = tangentCoordChange I q p q (v q) :=
    congrArg (fun q' : M ↦ (tangentCoordChange I q' p q' (v q') : E)) (φ.left_inv hq)
  have hg₀ : g x₀ = 0 := by
    rw [hgφ (mem_extChartAt_source p), hp]
    exact map_zero _
  -- The coordinate field is `C¹`, and Lipschitz, on a ball `B` around `φ p` inside the target.
  have hgc : ContDiffAt ℝ 1 g x₀ :=
    ((contMDiffAt_iff.mp (hv p)).2.contDiffAt hrange).snd
  obtain ⟨K, Z, hZ, hlip⟩ := hgc.exists_lipschitzOnWith
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem (hgc.eventually (by simp)) hZ) htarget)
  set B := Metric.ball x₀ r
  have hBo : IsOpen B := Metric.isOpen_ball
  have hx₀B : x₀ ∈ B := Metric.mem_ball_self hr
  have hgB : ContDiffOn ℝ 1 g B := fun z hz ↦ (hB hz).1.1.contDiffWithinAt
  -- The cut-off coordinate flow `ψ` of the field `c • g`.
  obtain ⟨ψ, -, -, -, -, -, hψ0, hψrest, hψ⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := fun _ z ↦ c • g z)
      (T := univ) (U := B) (x₀ := x₀) (r := 1) le_rfl isOpen_univ hBo (subset_univ _) hx₀B
      ((hgB.comp contDiffOn_snd fun q (hq : q ∈ (univ : Set ℝ) ×ˢ B) ↦ hq.2).const_smul c)
      (fun _ _ ↦ by simp [hg₀])
  have hψx₀ (τ : ℝ) : ψ τ x₀ = x₀ := hψrest x₀ (fun _ _ ↦ by simp [hg₀]) τ
  -- Trajectories of `v` starting near `p` stay in `N = φ⁻¹(B)` up to time `t`.
  set N := φ.source ∩ φ ⁻¹' B
  have hNo : IsOpen N := isOpen_extChartAt_preimage' p hBo
  have hpN : p ∈ N := ⟨mem_extChartAt_source p, hx₀B⟩
  have hdom : IsOpen (timeDependentFlowDomain (fun _ ↦ v)) := isOpen_timeDependentFlowDomain hX
  have hrest : ∀ u, (fun _ : ℝ ↦ v) u p = 0 := fun _ ↦ hp
  have htube : ∀ᶠ y in 𝓝 p, ∀ τ ∈ Icc (0 : ℝ) 1,
      ((s, s + c * τ), y) ∈ timeDependentFlowDomain (fun _ ↦ v) ∧
        timeDependentFlowOf (fun _ ↦ v) s (s + c * τ) y ∈ N := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun τ _ ↦ ?_
    have hι : Continuous fun q : M × ℝ ↦ ((s, s + c * q.2), q.1) := by fun_prop
    have hmem : ((s, s + c * τ), p) ∈ timeDependentFlowDomain (fun _ ↦ v) :=
      mem_timeDependentFlowDomain_of_forall_eq_zero hrest _ _
    have hcontΦ : ContinuousAt (fun q : (ℝ × ℝ) × M ↦ timeDependentFlowOf (fun _ ↦ v) q.1.1 q.1.2
        q.2) ((s, s + c * τ), p) :=
      ((contMDiffOn_timeDependentFlowOf le_rfl hX).continuousOn).continuousAt (hdom.mem_nhds hmem)
    have hΦp : timeDependentFlowOf (fun _ ↦ v) s (s + c * τ) p = p :=
      timeDependentFlowOf_eq_self_of_forall_eq_zero hX hrest _ _
    have h1 := (hι.continuousAt (x := (p, τ))).preimage_mem_nhds (hdom.mem_nhds hmem)
    have h2 := (hcontΦ.comp (x := (p, τ)) hι.continuousAt).preimage_mem_nhds
      (hNo.mem_nhds (by simpa only [comp_apply, hΦp] using hpN))
    filter_upwards [h1, h2] with q hq1 hq2 using ⟨hq1, hq2⟩
  -- Near `p`, the time map read in the chart is the time-one map of `ψ`.
  have heq : ∀ᶠ y in 𝓝 p, φ (timeDependentFlowOf (fun _ ↦ v) s t y) = ψ 1 (φ y) := by
    filter_upwards [htube, (continuousAt_extChartAt (I := I) p).eventually hψ] with y hy hyψ
    set f₁ : ℝ → E := fun τ ↦ φ (timeDependentFlowOf (fun _ ↦ v) s (s + c * τ) y)
    have hf₁ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : HasDerivAt f₁ (c • g (f₁ τ)) τ := by
      have hΦ := hasMFDerivAt_timeDependentFlowOf hX (hy τ hτ).1
      have hchart := hΦ.hasDerivAt_extChartAt_comp (x := p) (hy τ hτ).2.1
      have hval : g (f₁ τ) = _ := hgφ (hy τ hτ).2.1
      rw [hval]
      have hlin : HasDerivAt (fun τ : ℝ ↦ s + c * τ) c τ := by
        simpa using ((hasDerivAt_id τ).const_mul c).const_add s
      exact hchart.scomp τ hlin
    have hEq : EqOn f₁ (fun τ ↦ ψ τ (φ y)) (Icc 0 1) := by
      refine ODE_solution_unique_of_mem_Icc_right (v := fun _ z ↦ c • g z) (s := fun _ ↦ B)
        (K := ‖c‖₊ * K)
        (fun _ _ ↦ (lipschitzWith_smul c).comp_lipschitzOnWith (hlip.mono fun z hz ↦ (hB hz).1.2))
        (fun τ hτ ↦ (hf₁ τ hτ).continuousAt.continuousWithinAt)
        (fun τ hτ ↦ (hf₁ τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
        (fun τ hτ ↦ (hy τ (Ico_subset_Icc_self hτ)).2.2)
        (fun τ hτ ↦ (hyψ τ hτ).2.1.continuousAt.continuousWithinAt)
        (fun τ hτ ↦ (hyψ τ (Ico_subset_Icc_self hτ)).2.1.hasDerivWithinAt)
        (fun τ hτ ↦ (hyψ τ (Ico_subset_Icc_self hτ)).1) ?_
      simp only [f₁, mul_zero, add_zero, timeDependentFlowOf_self, hψ0, id]
    have h1 := hEq (right_mem_Icc.2 zero_le_one)
    simpa only [f₁, mul_one, c, add_sub_cancel] using h1
  -- The derivative of the time map is that of `ψ 1` at `φ p`.
  have hΦp : timeDependentFlowOf (fun _ ↦ v) s t p = p :=
    timeDependentFlowOf_eq_self_of_forall_eq_zero hX hrest _ _
  have hwritten : writtenInExtChartAt I I p (timeDependentFlowOf (fun _ ↦ v) s t) =ᶠ[𝓝 x₀]
      ψ 1 := by
    have hsymm : ∀ᶠ z in 𝓝 x₀, φ.symm z ∈ {y | φ (timeDependentFlowOf (fun _ ↦ v) s t y) =
        ψ 1 (φ y)} :=
      (continuousAt_extChartAt_symm p).preimage_mem_nhds (by rw [hpφ]; exact heq)
    filter_upwards [hsymm, htarget] with z hz hzt
    simp only [writtenInExtChartAt, hΦp, comp_apply] at hz ⊢
    rw [hz, φ.right_inv hzt]
  have hmd := mdifferentiableAt_timeDependentFlowOf hX
    (mem_timeDependentFlowDomain_of_forall_eq_zero hrest s t)
  rw [hmd.mfderiv, fderivWithin_of_mem_nhds hrange, hwritten.fderiv_eq]
  -- The derivative of `ψ τ` at the rest point solves `D' = (c • L) * D`.
  have hD : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun σ ↦ fderiv ℝ (ψ σ) x₀)
      ((c • chartLinearization I v p) * fderiv ℝ (ψ τ) x₀) τ := by
    intro τ hτ
    have h := (hψ.self_of_nhds τ hτ).2.2
    have hfd : fderiv ℝ (fun z ↦ c • g z) x₀ = c • chartLinearization I v p := by
      rw [show (fun z ↦ c • g z) = c • g from rfl, fderiv_const_smul_field, Pi.smul_apply,
        chartLinearization_def]
    rw [hψx₀, hfd] at h
    exact h
  have hexp : fderiv ℝ (ψ 1) x₀ = exp (c • chartLinearization I v p) := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    have hDw (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun σ ↦ fderiv ℝ (ψ σ) x₀ w)
        ((c • chartLinearization I v p) (fderiv ℝ (ψ τ) x₀ w)) τ :=
      ((hD τ hτ).clm_apply (hasDerivAt_const τ w)).congr_deriv (by simp)
    have h := ContinuousLinearMap.eq_exp_smul_apply_of_hasDerivWithinAt_Icc
      (z := fun τ ↦ fderiv ℝ (ψ τ) x₀ w)
      (fun τ hτ ↦ (hDw τ hτ).continuousAt.continuousWithinAt)
      (fun τ hτ ↦ (hDw τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) (right_mem_Icc.2 zero_le_one)
    simpa only [hψ0, fderiv_id, one_smul, ContinuousLinearMap.id_apply] using h
  -- The casts between `TangentSpace I p` and `E` are the identity.
  ext w
  exact congrArg (fun T : E →L[ℝ] E ↦ T w) hexp

/-- **Nondegeneracy of a rest point as a fixed point of the flow.** A rest point `p` of a `C¹`
vector field is a nondegenerate fixed point of the time map of the flow from `s` to `t` exactly
when `exp ((t - s) L)` fixes no nonzero vector, for the linearization `L` of the field at `p`. -/
theorem isNondegenerateFixedPt_timeDependentFlowOf_iff
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) (s t : ℝ) :
    IsNondegenerateFixedPt I (timeDependentFlowOf (fun _ ↦ v) s t) p ↔
      ∀ w : E, exp ((t - s) • chartLinearization I v p) w = w → w = 0 := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun q : ℝ × M ↦ (⟨q.2, v q.2⟩ : TangentBundle I M)) := hv.comp contMDiff_snd
  have hrest : ∀ u, (fun _ : ℝ ↦ v) u p = 0 := fun _ ↦ hp
  rw [isNondegenerateFixedPt_iff, mfderiv_timeDependentFlowOf_eq_exp hv hp s t]
  simp only [timeDependentFlowOf_eq_self_of_forall_eq_zero hX hrest s t, IsFixedPt,
    mdifferentiableAt_timeDependentFlowOf hX
      (mem_timeDependentFlowDomain_of_forall_eq_zero hrest s t), true_and]
  -- The tangent space `TangentSpace I p` is `E` by definition.
  exact Iff.rfl

/-- **Rest points with injective linearization are nondegenerate for short times.** Let `p` be a
rest point of a `C¹` vector field, with linearization `L`, and let `t ≠ s` with
`|t - s| ‖L‖ < log 2`. Then `p` is a nondegenerate fixed point of the time map of the flow from `s`
to `t` exactly when `L` is injective. -/
theorem isNondegenerateFixedPt_timeDependentFlowOf_iff_of_abs_mul_norm_lt
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) {s t : ℝ}
    (hst : t ≠ s) (hsmall : |t - s| * ‖chartLinearization I v p‖ < Real.log 2) :
    IsNondegenerateFixedPt I (timeDependentFlowOf (fun _ ↦ v) s t) p ↔
      ∀ w : E, chartLinearization I v p w = 0 → w = 0 := by
  have hB : ‖(t - s) • chartLinearization I v p‖ < Real.log 2 := by
    rwa [norm_smul, Real.norm_eq_abs]
  rw [isNondegenerateFixedPt_timeDependentFlowOf_iff hv hp s t]
  refine forall_congr' fun w ↦ ?_
  rw [ContinuousLinearMap.exp_apply_eq_self_iff hB, _root_.smul_apply, smul_eq_zero,
    or_iff_right (sub_ne_zero.2 hst)]

end TauCeti
