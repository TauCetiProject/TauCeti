/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The energy identity on the pair of pants

Let `S = ℂ ∖ {0, 1}` be the thrice-punctured sphere, with positive (input) cylindrical ends at `0`
and `1` and a negative (output) end at `∞`, parametrized by the end charts
`ThricePuncturedSphere.Puncture.endChart`. Let `K = K_s ds + K_t dt` be a Hamiltonian perturbation
on `S` which, on the part `±s ≥ T₀` of each end `q`, is `H_q(t) dt` for a period-one Hamiltonian
`H_q`. For a map `u` from `S` into a symplectic vector space, write `e` for the Floer energy
density and `R_K` for the curvature. Suppose that `e ≥ 0`, as for a solution of the Floer equation
with a tamed almost complex structure. Suppose also that the actions `A_{H_q}` of the loops
`t ↦ u(s, t)` of the end `q` tend to `a_q` as `±s → ∞`. Then the energy of `u` is

`E(u) = a₀ + a₁ - a_∞ - ∫_S R_K(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_endChart`). This
is the energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of the pair-of-pants product for a
vector space target. There every loop is capped by the cone of
`SymplecticForm.hamiltonianAction`, and the class `A` of the glued sphere has zero area.

The identity comes from Stokes' formula for the one-form `α = λ(u) + K(u)`, where
`λₓ(v) = ½ ω(x, v)`, whose exterior derivative is `e + R_K(u)`
(`SymplecticForm.floerEnergyDensity_eq`). It is applied to `χ_T α`, where the cutoff
`χ_T = 1 - ∑_q β(±s_q - T)` truncates the three ends at depth `T`. Then `χ_T α` has compact
support in `S`, and in the coordinates of the end `q` the boundary term `dχ_T ∧ α` is `∓β'(±s - T)`
times the action density of the loop at `s`. So `∫ χ_T (e + R_K(u))` is a signed sum of averages
of the loop actions against weights of total mass one supported in `±s ∈ [T, T + 1]`. Letting
`T → ∞` gives the identity, by monotone convergence for the energy and dominated convergence for
the curvature.

For the perturbation `Floer.pairOfPantsPerturbation H` of bounded Hamiltonians `|H_q| ≤ B_q`,
whose integrated curvature is at most `B₀ + B₁ + B_∞`
(`SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`), this gives
two bounds. The energy is at most `a₀ + a₁ - a_∞ + B₀ + B₁ + B_∞`. The output action satisfies
`a_∞ ≤ a₀ + a₁ + B₀ + B₁ + B_∞`. These are the energy bound and the action bound that a count of
pairs of pants needs for its coefficients to be supported.

## Main results

* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_endChart`: the
  energy identity for a perturbation that is `H_q(t) dt` far out on the ends.
* `SymplecticForm.integral_hamiltonianCurvature_le_of_tendsto_hamiltonianAction_endChart`: the
  integrated curvature is at most `a₀ + a₁ - a_∞`.
* `SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq_of_tendsto`: the energy
  identity for the pair-of-pants perturbation.
* `SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le_of_tendsto` and
  `SymplecticForm.action_inf_le_of_tendsto_pairOfPantsPerturbation`: the energy bound and the
  action bound for the pair-of-pants perturbation.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on the energy of
  inhomogeneous pseudoholomorphic maps on surfaces with strip-like ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy of solutions defining the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Cutoff

/-- The thrice-punctured sphere `ℂ ∖ {0, 1}` in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
private def pantsDomain : Set (ℝ × ℝ) := {(0, 0), (1, 0)}ᶜ

private theorem isOpen_pantsDomain : IsOpen pantsDomain :=
  (Set.toFinite _).isClosed.isOpen_compl

private theorem mem_pantsDomain_iff {z : ℝ × ℝ} :
    z ∈ pantsDomain ↔
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 := by
  rcases z with ⟨a, b⟩
  simp [pantsDomain, Complex.ext_iff, Complex.equivRealProdCLM_symm_apply, and_comm]

/-- The signed longitudinal coordinate `±s` of the end `q`, which tends to `∞` at the
puncture. -/
private noncomputable def signedCoord (q : Puncture) (z : ℝ × ℝ) : ℝ :=
  q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re

private theorem ne_endCenter_of_signedCoord_ne_zero {q : Puncture} {z : ℝ × ℝ}
    (h : signedCoord q z ≠ 0) : Complex.equivRealProdCLM.symm z ≠ q.endCenter :=
  q.ne_endCenter_of_re_endCoord_ne_zero fun h' => h (by simp [signedCoord, h'])

/-- The parts `±s > 0` of distinct ends are disjoint. -/
private theorem signedCoord_nonpos {q r : Puncture} (hqr : q ≠ r) {z : ℝ × ℝ}
    (hq : 0 < signedCoord q z) : signedCoord r z ≤ 0 := by
  by_contra! hr
  exact cylindricalEndLift_ne_cylindricalEndLift hqr hq hr
    ((q.cylindricalEndLift_endCoord (ne_endCenter_of_signedCoord_ne_zero hq.ne')).trans
      (r.cylindricalEndLift_endCoord (ne_endCenter_of_signedCoord_ne_zero hr.ne')).symm)

private theorem mem_pantsDomain_of_signedCoord_pos {q : Puncture} {z : ℝ × ℝ}
    (h : 0 < signedCoord q z) : z ∈ pantsDomain :=
  mem_pantsDomain_iff.2 (q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos h)

private theorem contDiffAt_signedCoord (q : Puncture) {z : ℝ × ℝ} (hz : z ∈ pantsDomain)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (signedCoord q) z :=
  contDiffAt_const.mul ((q.contDiffAt_re_endCoord (ne_endCenter (mem_pantsDomain_iff.1 hz) q)).comp
    z Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

/-- Close to the center of a positive end, its signed coordinate is large. -/
private theorem lt_signedCoord_of_norm_lt {q : Puncture} (hq : q ≠ inf) {z : ℝ × ℝ} {c : ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ < ‖q.endScale‖ * exp (-(2 * π * c))) :
    c < signedCoord q z := by
  have hb : 0 < ‖q.endScale‖ := norm_pos_iff.2 q.endScale_ne_zero
  have hpos : 0 < ‖(Complex.equivRealProdCLM.symm z - q.endCenter) / q.endScale‖ :=
    norm_pos_iff.2 (div_ne_zero (sub_ne_zero.2 hz) q.endScale_ne_zero)
  have hlt : ‖(Complex.equivRealProdCLM.symm z - q.endCenter) / q.endScale‖ <
      exp (-(2 * π * c)) := by
    rw [norm_div, div_lt_iff₀ hb]
    linarith
  have hlog := (Real.log_lt_iff_lt_exp hpos).2 hlt
  rw [signedCoord, endSign_eq_one hq, one_mul, re_endCoord, lt_div_iff₀ (by positivity)]
  linarith

/-- Far from the origin, the signed coordinate of the end at `∞` is large. -/
private theorem lt_signedCoord_inf {z : ℝ × ℝ} {c : ℝ}
    (h : 2 * exp (2 * π * c) < ‖Complex.equivRealProdCLM.symm z‖) : c < signedCoord inf z := by
  have hlt : exp (2 * π * c) < ‖Complex.equivRealProdCLM.symm z / 2‖ := by
    rw [norm_div]
    norm_num
    linarith
  have hlog := (Real.lt_log_iff_exp_lt ((exp_pos _).trans hlt)).2 hlt
  rw [signedCoord, endSign_inf, re_endCoord, endCenter_inf, endScale_inf, sub_zero, neg_div,
    neg_one_mul, neg_neg, lt_div_iff₀ (by positivity)]
  linarith

/-- Near each puncture, the signed coordinate of some end exceeds any given bound. -/
private theorem exists_eventually_lt_signedCoord {z₀ : ℝ × ℝ} (hz₀ : z₀ ∉ pantsDomain) (c : ℝ) :
    ∃ q : Puncture, ∀ᶠ z in 𝓝 z₀, z ∈ pantsDomain → c < signedCoord q z := by
  have key (q : Puncture) (hq : q ≠ inf) (h₀ : Complex.equivRealProdCLM.symm z₀ = q.endCenter) :
      ∀ᶠ z in 𝓝 z₀, z ∈ pantsDomain → c < signedCoord q z := by
    have hcont : Tendsto (fun z ↦ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖) (𝓝 z₀)
        (𝓝 0) := by
      have := ((Complex.equivRealProdCLM.symm.continuous.sub
        (continuous_const (y := q.endCenter))).norm).tendsto z₀
      simpa [h₀] using this
    filter_upwards [hcont.eventually (gt_mem_nhds
      (mul_pos (norm_pos_iff.2 q.endScale_ne_zero) (exp_pos (-(2 * π * c)))))] with z hz hzD
    exact lt_signedCoord_of_norm_lt hq (ne_endCenter (mem_pantsDomain_iff.1 hzD) q) hz
  simp only [pantsDomain, mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] at hz₀
  rcases hz₀ with rfl | rfl
  · exact ⟨zero, key zero (by decide) (by simp [Complex.equivRealProdCLM_symm_apply])⟩
  · exact ⟨one, key one (by decide) (by simp [Complex.equivRealProdCLM_symm_apply])⟩

/-- The cutoff `χ_T`, equal to `1 - ∑ q, β(±s_q - T)` on `ℂ ∖ {0, 1}` and to `0` at the
punctures, where `β` is the smooth transition function. It is `1` where every signed end
coordinate is at most `T`, and `0` where one of them is at least `T + 1`. -/
private noncomputable def cutoff (T : ℝ) : ℝ × ℝ → ℝ :=
  pantsDomain.indicator fun z ↦ 1 - ∑ q : Puncture, smoothTransition (signedCoord q z - T)

private theorem cutoff_of_mem {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ pantsDomain) :
    cutoff T z = 1 - ∑ q : Puncture, smoothTransition (signedCoord q z - T) :=
  indicator_of_mem hz _

private theorem cutoff_of_notMem {T : ℝ} {z : ℝ × ℝ} (hz : z ∉ pantsDomain) : cutoff T z = 0 :=
  indicator_of_notMem hz _

/-- On the part `±s > 0` of the end `q` only the cutoff of that end contributes. -/
private theorem cutoff_of_signedCoord_pos {T : ℝ} (hT : 0 ≤ T) {q : Puncture} {z : ℝ × ℝ}
    (hq : 0 < signedCoord q z) : cutoff T z = 1 - smoothTransition (signedCoord q z - T) := by
  rw [cutoff_of_mem (mem_pantsDomain_of_signedCoord_pos hq), Finset.sum_eq_single q]
  · intro r _ hr
    exact smoothTransition.zero_of_nonpos (by linarith [signedCoord_nonpos (Ne.symm hr) hq])
  · simp

private theorem cutoff_eq_one {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ pantsDomain)
    (h : ∀ q, signedCoord q z ≤ T) : cutoff T z = 1 := by
  rw [cutoff_of_mem hz, Finset.sum_eq_zero fun q _ ↦
    smoothTransition.zero_of_nonpos (by linarith [h q]), sub_zero]

private theorem cutoff_mem_Icc {T : ℝ} (hT : 0 ≤ T) (z : ℝ × ℝ) : cutoff T z ∈ Icc 0 1 := by
  by_cases hz : z ∈ pantsDomain
  · by_cases h : ∃ q, 0 < signedCoord q z
    · obtain ⟨q, hq⟩ := h
      rw [cutoff_of_signedCoord_pos hT hq]
      exact ⟨sub_nonneg.2 (smoothTransition.le_one _),
        sub_le_self _ (smoothTransition.nonneg _)⟩
    · push Not at h
      rw [cutoff_eq_one hz fun q ↦ (h q).trans hT]
      exact ⟨zero_le_one, le_rfl⟩
  · rw [cutoff_of_notMem hz]
    exact ⟨le_rfl, zero_le_one⟩

private theorem cutoff_mono {T T' : ℝ} (h : T ≤ T') (z : ℝ × ℝ) : cutoff T z ≤ cutoff T' z := by
  by_cases hz : z ∈ pantsDomain
  · rw [cutoff_of_mem hz, cutoff_of_mem hz]
    exact sub_le_sub_left (Finset.sum_le_sum fun q _ ↦ smoothTransition.monotone (by linarith)) _
  · simp [cutoff_of_notMem hz]

/-- At a point of `ℂ ∖ {0, 1}`, the cutoff is eventually `1`. -/
private theorem eventually_cutoff_eq_one {z : ℝ × ℝ} (hz : z ∈ pantsDomain) :
    ∀ᶠ T in atTop, cutoff T z = 1 := by
  filter_upwards [eventually_ge_atTop (∑ q : Puncture, |signedCoord q z|)] with T hT
  exact cutoff_eq_one hz fun q ↦ (le_abs_self _).trans
    ((Finset.single_le_sum (fun r _ ↦ abs_nonneg (signedCoord r z)) (Finset.mem_univ q)).trans hT)

/-- The cutoff vanishes near the punctures. -/
private theorem cutoff_eventuallyEq_zero {T : ℝ} (hT : 0 ≤ T) {z₀ : ℝ × ℝ}
    (hz₀ : z₀ ∉ pantsDomain) : cutoff T =ᶠ[𝓝 z₀] 0 := by
  obtain ⟨q, hq⟩ := exists_eventually_lt_signedCoord hz₀ (T + 1)
  filter_upwards [hq] with z hz
  by_cases hzD : z ∈ pantsDomain
  · have h := hz hzD
    rw [Pi.zero_apply, cutoff_of_signedCoord_pos hT (by linarith),
      smoothTransition.one_of_one_le (by linarith), sub_self]
  · exact cutoff_of_notMem hzD

private theorem contDiffAt_cutoff {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ pantsDomain) {n : ℕ∞} :
    ContDiffAt ℝ n (cutoff T) z := by
  refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const.sub (ContDiffAt.sum fun q _ ↦
    (smoothTransition.contDiff.contDiffAt).comp (f := fun z ↦ signedCoord q z - T) z
      ((contDiffAt_signedCoord q hz).sub contDiffAt_const)))
    (eventually_of_mem (isOpen_pantsDomain.mem_nhds hz) fun z hz ↦ cutoff_of_mem hz)

/-- The cutoff vanishes outside a compact set. -/
private theorem hasCompactSupport_cutoff {T : ℝ} (hT : 0 ≤ T) : HasCompactSupport (cutoff T) := by
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℂ) (2 * exp (2 * π * (T + 1)))).image
    Complex.equivRealProdCLM.continuous) fun z hz ↦ ?_
  have hR : 2 * exp (2 * π * (T + 1)) < ‖Complex.equivRealProdCLM.symm z‖ := by
    by_contra! h
    exact hz ⟨_, mem_closedBall_zero_iff.2 h, by simp⟩
  have h := lt_signedCoord_inf hR
  rw [cutoff_of_signedCoord_pos hT (by linarith), smoothTransition.one_of_one_le (by linarith),
    sub_self]

end Cutoff

section Primitive

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ}
  {u : ℝ × ℝ → V}

/-- A function vanishing near the punctures has topological support in `ℂ ∖ {0, 1}`. -/
private theorem tsupport_subset_pantsDomain {F : Type*} [Zero F]
    {f : ℝ × ℝ → F} (h0 : ∀ z ∉ pantsDomain, f =ᶠ[𝓝 z] 0) : tsupport f ⊆ pantsDomain :=
  fun z hz ↦ by_contra fun hzD ↦ (notMem_tsupport_iff_eventuallyEq.2 (h0 z hzD)) hz

/-- A function `C^n` on `ℂ ∖ {0, 1}` and vanishing near the punctures is `C^n`. -/
private theorem contDiff_of_contDiffOn_pantsDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f pantsDomain)
    (h0 : ∀ z ∉ pantsDomain, f =ᶠ[𝓝 z] 0) : ContDiff ℝ n f :=
  contMDiff_iff_contDiff.1 (contMDiff_of_tsupport fun _ hz ↦ (hf.contDiffAt
    (isOpen_pantsDomain.mem_nhds (tsupport_subset_pantsDomain h0 hz))).contMDiffAt)

/-- A function continuous on `ℂ ∖ {0, 1}` and vanishing near the punctures is continuous. -/
private theorem continuous_of_continuousOn_pantsDomain {F : Type*} [NormedAddCommGroup F]
    {f : ℝ × ℝ → F} (hf : ContinuousOn f pantsDomain) (h0 : ∀ z ∉ pantsDomain, f =ᶠ[𝓝 z] 0) :
    Continuous f :=
  continuous_of_tsupport fun _ hz ↦
    hf.continuousAt (isOpen_pantsDomain.mem_nhds (tsupport_subset_pantsDomain h0 hz))

/-- The product with the cutoff of any function vanishes near the punctures. -/
private theorem cutoff_mul_eventuallyEq_zero {T : ℝ} (hT : 0 ≤ T) (f : ℝ × ℝ → ℝ) {z : ℝ × ℝ}
    (hz : z ∉ pantsDomain) : (fun w ↦ cutoff T w * f w) =ᶠ[𝓝 z] 0 :=
  (cutoff_eventuallyEq_zero hT hz).mono fun w hw ↦ by simp [hw]

/-- The cutoff is smooth on the plane. -/
private theorem contDiff_cutoff {T : ℝ} (hT : 0 ≤ T) {n : ℕ∞} : ContDiff ℝ n (cutoff T) :=
  contDiff_of_contDiffOn_pantsDomain (fun _ hz ↦ (contDiffAt_cutoff hz).contDiffWithinAt)
    fun _ hz ↦ cutoff_eventuallyEq_zero hT hz

/-- The derivative of the cutoff vanishes near the punctures. -/
private theorem fderiv_cutoff_eventuallyEq_zero {T : ℝ} (hT : 0 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ pantsDomain) : fderiv ℝ (cutoff T) =ᶠ[𝓝 z] 0 :=
  (cutoff_eventuallyEq_zero hT hz).eventuallyEq_nhds.mono fun w hw ↦ by
    rw [hw.fderiv_eq]
    simp

omit [FiniteDimensional ℝ V] in
/-- The components `K_s`, `K_t` of a perturbation in the global coordinate inherit its
regularity. -/
private theorem contDiffAt_uncurry_perturbation {z : ℝ × ℝ} {x : V} {n : WithTop ℕ∞}
    (hK : ContDiffAt ℝ n (fun p : ℂ × V ↦ K p.1 p.2) (Complex.equivRealProdCLM.symm z, x))
    (v : ℂ) : ContDiffAt ℝ n (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x) :=
  (hK.comp (z, x) ((Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp _
    contDiffAt_fst).prodMk contDiffAt_snd)).clm_apply contDiffAt_const

/-- The one-form `α = λ(u) + K(u)` on the domain, where `λₓ(v) = ½ ω(x, v)` is the primitive of
`ω`: `α_z(v) = ½ ω(u z, du_z v) + K_z(u z)(v)`. Its exterior derivative is the Floer energy
density plus the curvature. -/
private noncomputable def primitive (ω : SymplecticForm V) (K : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ω.toBilinForm.toContinuousBilinearMap (u z)).comp (fderiv ℝ u z) +
    (K (Complex.equivRealProdCLM.symm z) (u z)).comp
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)

private theorem primitive_apply (z v : ℝ × ℝ) :
    primitive ω K u z v = (1 / 2 : ℝ) * ω (u z) (fderiv ℝ u z v) +
      K (Complex.equivRealProdCLM.symm z) (u z) (Complex.equivRealProdCLM.symm v) := by
  simp [primitive]

private theorem contDiffAt_primitive_apply {z : ℝ × ℝ} (hu : ContDiffAt ℝ 2 u z)
    (hK : ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (Complex.equivRealProdCLM.symm z, u z))
    (v : ℝ × ℝ) : ContDiffAt ℝ 1 (fun w ↦ primitive ω K u w v) z := by
  simp only [primitive_apply]
  have hDu : ContDiffAt ℝ 1 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hB := ω.toBilinForm.toContinuousBilinearMap.contDiff.contDiffAt (x := u z) (n := 1)
  refine (contDiffAt_const.mul ?_).add ?_
  · have h := (hB.comp z (hu.of_le one_le_two)).clm_apply
      (hDu.clm_apply (contDiffAt_const (c := v)))
    simpa using h
  · exact (hK.comp z (Complex.equivRealProdCLM.symm.contDiff.contDiffAt.prodMk
      (hu.of_le one_le_two))).clm_apply contDiffAt_const

/-- **The exterior derivative of the primitive.** At a point where `u` is `C²` and `K` is `C¹`,
`∂_s α_t - ∂_t α_s` is the Floer energy density plus the curvature. -/
private theorem fderiv_primitive_sub {z : ℝ × ℝ} (hu : ContDiffAt ℝ 2 u z)
    (hK : ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (Complex.equivRealProdCLM.symm z, u z)) :
    fderiv ℝ (fun w ↦ primitive ω K u w stdComplexLineImag) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ primitive ω K u w stdComplexLineReal) z stdComplexLineImag =
      ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
        ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  set B := ω.toBilinForm.toContinuousBilinearMap
  have hB (x y : V) : B x y = ω x y := by simp [B]
  have hu₁ : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm : fderiv ℝ (fderiv ℝ u) z stdComplexLineReal stdComplexLineImag =
      fderiv ℝ (fderiv ℝ u) z stdComplexLineImag stdComplexLineReal :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  have h1 : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  have hBdiff (v : ℝ × ℝ) : DifferentiableAt ℝ (fun w ↦ B (u w) (fderiv ℝ u w v)) z :=
    (B.hasFDerivAt_of_bilinear hu₁.hasFDerivAt
      (hDu.clm_apply (differentiableAt_const v)).hasFDerivAt).differentiableAt
  -- Differentiate the area part `½ B(u, ∂_v u)` by the product rule for `B`.
  have harea (v e : ℝ × ℝ) : fderiv ℝ (fun w ↦ (1 / 2 : ℝ) * B (u w) (fderiv ℝ u w v)) z e =
      (1 / 2 : ℝ) * (B (u z) (fderiv ℝ (fderiv ℝ u) z e v) +
        B (fderiv ℝ u z e) (fderiv ℝ u z v)) := by
    have hv : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w v) z :=
      hDu.clm_apply (differentiableAt_const v)
    rw [fderiv_const_mul (hBdiff v), smul_apply,
      B.fderiv_of_bilinear hu₁ hv, fderiv_clm_apply hDu (differentiableAt_const v)]
    simp
  have hKdiff (v : ℂ) :
      DifferentiableAt ℝ (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) v) z :=
    (DifferentiableAt.comp (g := fun p : ℂ × V ↦ K p.1 p.2) z (hK.differentiableAt one_ne_zero)
      (Complex.equivRealProdCLM.symm.differentiableAt.prodMk hu₁)).clm_apply
      (differentiableAt_const v)
  have hareadiff (v : ℝ × ℝ) :
      DifferentiableAt ℝ (fun w ↦ (1 / 2 : ℝ) * B (u w) (fderiv ℝ u w v)) z :=
    (hBdiff v).const_mul _
  have hprim (v : ℝ × ℝ) (c : ℂ) (hc : Complex.equivRealProdCLM.symm v = c) :
      (fun w ↦ primitive ω K u w v) = fun w ↦ (1 / 2 : ℝ) * B (u w) (fderiv ℝ u w v) +
        K (Complex.equivRealProdCLM.symm w) (u w) c := by
    funext w
    rw [primitive_apply, hB, hc]
  rw [hprim _ _ hI, hprim _ _ h1, fderiv_fun_add (hareadiff _) (hKdiff _),
    fderiv_fun_add (hareadiff _) (hKdiff _), add_apply,
    add_apply, harea, harea, hsymm,
    ω.floerEnergyDensity_eq hu₁
      ((contDiffAt_uncurry_perturbation hK 1).differentiableAt one_ne_zero)
      ((contDiffAt_uncurry_perturbation hK Complex.I).differentiableAt one_ne_zero)]
  simp only [hB, ← ω.neg_eq (fderiv ℝ u z stdComplexLineImag)]
  ring

end Primitive

section Stokes

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ}
  {u : ℝ × ℝ → V}

/-- The collar term `(dχ_T ∧ α)(∂_s, ∂_t)` of Stokes' formula for `χ_T α`. It is supported where
the cutoff is not locally constant, on the collars `T ≤ ±s ≤ T + 1` of the three ends. -/
private noncomputable def collarDensity (ω : SymplecticForm V) (K : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (cutoff T) z stdComplexLineReal * primitive ω K u z stdComplexLineImag -
    fderiv ℝ (cutoff T) z stdComplexLineImag * primitive ω K u z stdComplexLineReal

private theorem contDiffAt_primitive_apply_of_mem (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    {z : ℝ × ℝ} (hz : z ∈ pantsDomain)
    (v : ℝ × ℝ) : ContDiffAt ℝ 1 (fun w ↦ primitive ω K u w v) z :=
  contDiffAt_primitive_apply (hu.contDiffAt (isOpen_pantsDomain.mem_nhds hz))
    (hK _ (mem_pantsDomain_iff.1 hz).1 (mem_pantsDomain_iff.1 hz).2 _) v

private theorem continuous_collarDensity (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    {T : ℝ} (hT : 0 ≤ T) :
    Continuous (collarDensity ω K u T) := by
  have hc := (contDiff_cutoff (T := T) hT (n := 1)).continuous_fderiv one_ne_zero
  refine continuous_of_continuousOn_pantsDomain (fun z hz ↦ ?_) fun z hz ↦ ?_
  · exact (((hc.clm_apply continuous_const).continuousAt.mul
      (contDiffAt_primitive_apply_of_mem hu hK hz _).continuousAt).sub
      ((hc.clm_apply continuous_const).continuousAt.mul
      (contDiffAt_primitive_apply_of_mem hu hK hz _).continuousAt)).continuousWithinAt
  · filter_upwards [fderiv_cutoff_eventuallyEq_zero hT hz] with w hw
    simp [collarDensity, hw]

private theorem integrable_collarDensity (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (collarDensity ω K u T) :=
  (continuous_collarDensity hu hK hT).integrable_of_hasCompactSupport
    ((hasCompactSupport_cutoff hT).fderiv ℝ |>.mono fun z hz ↦ by
      by_contra h
      exact (mem_support.1 hz) (by simp [collarDensity, notMem_support.1 h]))

/-- **Stokes' formula with a cutoff.** The integral of `χ_T (e + R_K)`, where `e` is the Floer
energy density, is minus the integral of the collar term `dχ_T ∧ α`, since
`d(χ_T α) = χ_T dα + dχ_T ∧ α`, `dα = e + R_K`, and `χ_T α` has compact support in
`ℂ ∖ {0, 1}`. -/
private theorem integral_cutoff_mul_eq_neg (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ z, cutoff T z *
        (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
          ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) =
      -∫ z, collarDensity ω K u T z := by
  have hreg (v : ℝ × ℝ) : ContDiff ℝ 1 (fun z ↦ cutoff T z * primitive ω K u z v) :=
    contDiff_of_contDiffOn_pantsDomain
      (fun z hz ↦ ((contDiffAt_cutoff hz).mul
        (contDiffAt_primitive_apply_of_mem hu hK hz v)).contDiffWithinAt)
      fun z hz ↦ cutoff_mul_eventuallyEq_zero hT _ hz
  have hsupp (v : ℝ × ℝ) : HasCompactSupport (fun z ↦ cutoff T z * primitive ω K u z v) :=
    (hasCompactSupport_cutoff hT).mul_right
  have hint (v w : ℝ × ℝ) :
      Integrable (fun z ↦ fderiv ℝ (fun z ↦ cutoff T z * primitive ω K u z v) z w) :=
    ((hreg v).continuous_fderiv one_ne_zero |>.clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hsupp v).fderiv_apply (𝕜 := ℝ) w)
  -- Pointwise, `∂_s (χ_T α_t) - ∂_t (χ_T α_s) = χ_T (e + R_K) + dχ_T ∧ α`.
  have hpt (z : ℝ × ℝ) :
      fderiv ℝ (fun z ↦ cutoff T z * primitive ω K u z stdComplexLineImag) z stdComplexLineReal -
        fderiv ℝ (fun z ↦ cutoff T z * primitive ω K u z stdComplexLineReal) z stdComplexLineImag -
      collarDensity ω K u T z = cutoff T z *
        (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
          ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
    by_cases hz : z ∈ pantsDomain
    · have hc := (contDiffAt_cutoff (T := T) hz (n := 1)).differentiableAt one_ne_zero
      have hp (v : ℝ × ℝ) := (contDiffAt_primitive_apply_of_mem (ω := ω) hu hK hz
        v).differentiableAt one_ne_zero
      rw [fderiv_fun_mul hc (hp _), fderiv_fun_mul hc (hp _), ← fderiv_primitive_sub
          (hu.contDiffAt (isOpen_pantsDomain.mem_nhds hz))
          (hK _ (mem_pantsDomain_iff.1 hz).1 (mem_pantsDomain_iff.1 hz).2 _), collarDensity]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · rw [(cutoff_mul_eventuallyEq_zero hT _ hz).fderiv_eq,
        (cutoff_mul_eventuallyEq_zero hT _ hz).fderiv_eq, collarDensity,
        (fderiv_cutoff_eventuallyEq_zero hT hz).eq_of_nhds, cutoff_of_notMem hz]
      simp
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hsub : Integrable (fun z ↦
      fderiv ℝ (fun z ↦ cutoff T z * primitive ω K u z stdComplexLineImag) z stdComplexLineReal -
        fderiv ℝ (fun z ↦ cutoff T z * primitive ω K u z stdComplexLineReal) z
          stdComplexLineImag) :=
    (hint _ _).sub (hint _ _)
  rw [← integral_congr_ae (ae_of_all _ hpt), integral_sub hsub
    (integrable_collarDensity hu hK hT), integral_sub (hint _ _) (hint _ _),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (hreg _) (hsupp _),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (hreg _) (hsupp _)]
  ring

end Stokes

section Collar

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ}
  {u : ℝ × ℝ → V} {H : Puncture → ℝ → V → ℝ}

private theorem signedCoord_endChart (q : Puncture) (z : ℝ × ℝ) :
    signedCoord q (q.endChart z) = q.endSign * z.1 := by
  rw [signedCoord, equivRealProdCLM_symm_endChart, re_endCoord_cylindricalEndLift]
  simp [Complex.equivRealProdCLM_symm_apply]

private theorem endChart_mem_pantsDomain {q : Puncture} {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) :
    q.endChart z ∈ pantsDomain :=
  mem_pantsDomain_of_signedCoord_pos (by rwa [signedCoord_endChart])

/-- **The collar term in end coordinates.** On the part `±s > 0` of the end `q`, where the
cutoff is `1 - β(±s - T)` and, beyond `T₀ ≤ T`, the perturbation is `H_q(t) dt`, the collar term
`dχ_T ∧ α` times the Jacobian of the end chart is `∓β'(±s - T)` times the action density
`½ ω(x, x') + H_q(t, x)` of the loop `x = u(s, ·)`. -/
private theorem abs_det_mul_collarDensity_endChart (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hH : ∀ q, Periodic (H q) 1) {T₀ T : ℝ} (hT : 0 ≤ T) (hT₀ : T₀ ≤ T)
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) :
    |(fderiv ℝ q.endChart z).det| * collarDensity ω K u T (q.endChart z) =
      -(q.endSign * deriv smoothTransition (q.endSign * z.1 - T)) *
        ((1 / 2 : ℝ) * ω (u (q.endChart z)) (deriv (fun t ↦ u (q.endChart (z.1, t))) z.2) +
          H q z.2 (u (q.endChart z))) := by
  set L := fderiv ℝ q.endChart z
  have hw : q.endChart z ∈ pantsDomain := endChart_mem_pantsDomain hz
  have hφ : HasFDerivAt q.endChart L z := (q.hasFDerivAt_endChart z).differentiableAt.hasFDerivAt
  have hχ : DifferentiableAt ℝ (cutoff T) (q.endChart z) :=
    (contDiffAt_cutoff (n := 1) hw).differentiableAt one_ne_zero
  -- Near `z` the pulled-back cutoff is `1 - β(±s - T)`.
  have hloc : cutoff T ∘ q.endChart =ᶠ[𝓝 z]
      fun z' ↦ 1 - smoothTransition (q.endSign * z'.1 - T) := by
    have hev : ∀ᶠ z' in 𝓝 z, 0 < q.endSign * z'.1 :=
      (continuous_const.mul continuous_fst).continuousAt.eventually (lt_mem_nhds hz)
    filter_upwards [hev] with z' hz'
    rw [comp_apply, cutoff_of_signedCoord_pos hT (by rwa [signedCoord_endChart]),
      signedCoord_endChart]
  have hβ : HasFDerivAt (fun z' : ℝ × ℝ ↦ 1 - smoothTransition (q.endSign * z'.1 - T))
      (-(deriv smoothTransition (q.endSign * z.1 - T) •
        (q.endSign • ContinuousLinearMap.fst ℝ ℝ ℝ))) z :=
    (((hasFDerivAt_fst.const_smul q.endSign).sub_const T).smoothTransition).const_sub 1
  have hdχ (v : ℝ × ℝ) : fderiv ℝ (cutoff T) (q.endChart z) (L v) =
      -(q.endSign * deriv smoothTransition (q.endSign * z.1 - T)) * v.1 := by
    have h := congrArg (· v) (fderiv_comp z hχ hφ.differentiableAt)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h, hloc.fderiv_eq, hβ.fderiv]
    simp only [neg_apply, smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul]
    ring
  have hwedge := LinearMap.apply_mul_apply_sub_det (L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)
    (fderiv ℝ (cutoff T) (q.endChart z) : ℝ × ℝ →ₗ[ℝ] ℝ)
    (primitive ω K u (q.endChart z) : ℝ × ℝ →ₗ[ℝ] ℝ)
  simp only [ContinuousLinearMap.coe_coe] at hwedge
  rw [abs_of_nonneg (q.det_fderiv_endChart_nonneg z), collarDensity, stdComplexLineReal_eq,
    stdComplexLineImag_eq, ContinuousLinearMap.det, ← hwedge, hdχ, hdχ]
  simp only [mul_one, mul_zero, zero_mul, sub_zero]
  by_cases hβ0 : deriv smoothTransition (q.endSign * z.1 - T) = 0
  · simp [hβ0]
  congr 1
  -- Where the cutoff varies, `T ≤ ±s`, so the perturbation is `H_q(t) dt` there.
  have hTs : T ≤ q.endSign * z.1 := by
    by_contra! h
    exact hβ0 (smoothTransition.deriv_of_neg (by linarith))
  have hux : HasDerivAt (fun t ↦ u (q.endChart (z.1, t)))
      (fderiv ℝ u (q.endChart z) (L (0, 1))) z.2 := by
    have hu' : DifferentiableAt ℝ u (q.endChart z) :=
      (hu.contDiffAt (isOpen_pantsDomain.mem_nhds hw)).differentiableAt (by norm_num)
    have hφ' : HasFDerivAt q.endChart L (z.1, z.2) := hφ
    have h := (hu'.hasFDerivAt.comp (z.1, z.2) hφ').comp_hasDerivAt z.2
      (HasDerivAt.prodMk (hasDerivAt_const z.2 z.1) (hasDerivAt_id' z.2))
    exact h
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm z)
  have hKw := hKend q (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))
    (u (q.endChart z)) (by
      rw [re_endCoord_cylindricalEndLift]
      simpa [Complex.equivRealProdCLM_symm_apply] using hT₀.trans hTs)
  have hHk : H q (z.2 + k) (u (q.endChart z)) = H q z.2 (u (q.endChart z)) := by
    simpa using congrFun ((hH q).int_mul k z.2) (u (q.endChart z))
  have hI : Complex.equivRealProdCLM.symm ((0, 1) : ℝ × ℝ) = Complex.I := by
    simp [Complex.equivRealProdCLM_symm_apply]
  rw [primitive_apply, hux.deriv, equivRealProdCLM_symm_endChart, hKw, hk, fderiv_endChart_apply,
    ContinuousLinearEquiv.symm_apply_apply, hI, smul_apply, endAngularForm_cylindricalEndLift]
  simp [Complex.equivRealProdCLM_symm_apply, hHk]

/-- **The loop integral of the action density.** For `±s > 0`, the integral over one period of
the action density `½ ω(x, x') + H_q(t, x)` of the loop `x = u(s, ·)` on the end `q` is its
Hamiltonian action. -/
private theorem setIntegral_Ico_eq_hamiltonianAction (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) {q : Puncture}
    {s : ℝ} (hs : 0 < q.endSign * s) :
    ∫ t in Ico (-1 / 2 : ℝ) (1 / 2),
        ((1 / 2 : ℝ) * ω (u (q.endChart (s, t))) (deriv (fun t ↦ u (q.endChart (s, t))) t) +
          H q t (u (q.endChart (s, t)))) =
      ω.hamiltonianAction (H q) (fun t ↦ u (q.endChart (s, t))) := by
  set x : ℝ → V := fun t ↦ u (q.endChart (s, t))
  have hx : ContDiff ℝ 2 x := contDiff_iff_contDiffAt.2 fun t ↦
    (hu.contDiffAt (isOpen_pantsDomain.mem_nhds (endChart_mem_pantsDomain (z := (s, t)) hs))).comp
      t (q.contDiff_endChart.contDiffAt.comp t (contDiffAt_const.prodMk contDiffAt_id))
  have hxper : Periodic x 1 := fun t ↦ by simp only [x, q.periodic_endChart s t]
  have hdper : Periodic (deriv x) 1 := fun t ↦ by
    rw [← deriv_comp_add_const]
    exact congrArg (deriv · t) (funext hxper)
  set B := ω.toBilinForm.toContinuousBilinearMap
  have hB (v w : V) : B v w = ω v w := by simp [B]
  have hc₁ : Continuous fun t ↦ ω (x t) (deriv x t) := by
    simp only [← hB]
    exact B.continuous₂.comp (hx.continuous.prodMk (hx.continuous_deriv one_le_two))
  have hc₂ : Continuous fun t ↦ H q t (x t) :=
    (hHc q).comp (continuous_id.prodMk hx.continuous)
  set f : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ω (x t) (deriv x t) + H q t (x t)
  have hper : Periodic f 1 := fun t ↦ by
    simp only [f, hxper t, hdper t, (hH q) t]
  have hshift : ∫ t in (-1 / 2 : ℝ)..(1 / 2), f t = ∫ t in (0 : ℝ)..1, f t := by
    have h := hper.intervalIntegral_add_eq (-1 / 2) 0
    rwa [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at h
  -- `set` does not fold the integrand under the binder, so name it `f` explicitly.
  change ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), f t = _
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), hshift,
    intervalIntegral.integral_add ((hc₁.const_mul _).intervalIntegrable _ _)
      (hc₂.intervalIntegrable _ _), intervalIntegral.integral_const_mul, hamiltonianAction_def,
    loopArea_def]

/-- The action of the loop at signed longitudinal coordinate `σ` on the end `q`. -/
private noncomputable def endAction (ω : SymplecticForm V) (H : Puncture → ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (q : Puncture) (σ : ℝ) : ℝ :=
  ω.hamiltonianAction (H q) (fun t ↦ u (q.endChart (q.endSign * σ, t)))

omit [FiniteDimensional ℝ V] in
private theorem endAction_endSign_mul (q : Puncture) (s : ℝ) :
    endAction ω H u q (q.endSign * s) =
      ω.hamiltonianAction (H q) (fun t ↦ u (q.endChart (s, t))) := by
  rw [endAction, ← mul_assoc, endSign_mul_self, one_mul]

/-- **The collar term of one end.** Its integral is `∓` the average of the actions of the loops
of the end against the weight `β'(σ - T)`, of total mass one and supported in `[T, T + 1]`. -/
private theorem integral_image_endChart_collarDensity (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) {T₀ T : ℝ}
    (hT : 1 ≤ T) (hT₀ : T₀ ≤ T)
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w) (q : Puncture) :
    Integrable (fun σ ↦ deriv smoothTransition (σ - T) * endAction ω H u q σ) ∧
      ∫ z in q.endChart '' q.endStrip, collarDensity ω K u T z =
        -(q.endSign * ∫ σ, deriv smoothTransition (σ - T) * endAction ω H u q σ) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set A : Set ℝ := {s | 1 / 2 < q.endSign * s}
  set B : Set ℝ := Ico (-1 / 2) (1 / 2)
  have hstrip : q.endStrip = A ×ˢ B := q.endStrip_def
  have hmeasA : MeasurableSet A :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  have hmeas : MeasurableSet q.endStrip := hstrip ▸ hmeasA.prod measurableSet_Ico
  have hder : ∀ z ∈ q.endStrip,
      HasFDerivWithinAt q.endChart (fderiv ℝ q.endChart z) q.endStrip z :=
    fun z _ ↦ (q.hasFDerivAt_endChart z).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  -- In cylinder coordinates the collar term is `∓β'(±s - T)` times the action density.
  set F : ℝ × ℝ → ℝ := fun z ↦ -(q.endSign * deriv smoothTransition (q.endSign * z.1 - T)) *
    ((1 / 2 : ℝ) * ω (u (q.endChart z)) (deriv (fun t ↦ u (q.endChart (z.1, t))) z.2) +
      H q z.2 (u (q.endChart z)))
  have hF : EqOn (fun z ↦ |(fderiv ℝ q.endChart z).det| • collarDensity ω K u T (q.endChart z))
      F q.endStrip := fun z hz ↦ by
    simpa only [smul_eq_mul] using abs_det_mul_collarDensity_endChart hu hH hT0 hT₀ hKend
      (endSign_mul_pos_of_mem_endStrip hz)
  have hFint : IntegrableOn F (A ×ˢ B) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hstrip]
    exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas hder
      q.injOn_endChart _).1 (integrable_collarDensity hu hK hT0).integrableOn).congr_fun hF hmeas
  -- Integrating over the angular coordinate gives the action of the loop.
  set g : ℝ → ℝ := fun s ↦ deriv smoothTransition (q.endSign * s - T) *
    ω.hamiltonianAction (H q) (fun t ↦ u (q.endChart (s, t)))
  have hinner : ∀ s ∈ A, ∫ t in B, F (s, t) = -(q.endSign * g s) := by
    intro s hs
    simp only [F, g, integral_const_mul]
    by_cases hβ : deriv smoothTransition (q.endSign * s - T) = 0
    · simp [hβ]
    · have hs' : 0 < q.endSign * s := by
        have : 1 / 2 < q.endSign * s := hs
        linarith
      rw [setIntegral_Ico_eq_hamiltonianAction hu hH hHc hs']
      ring
  have hgA : IntegrableOn g A := by
    -- Integrability on `A ×ˢ B` is integrability for the product of the restricted measures.
    have h := (show Integrable F ((volume.restrict A).prod (volume.restrict B)) by
      rw [Measure.prod_restrict]; exact hFint).integral_prod_left
    have h' : IntegrableOn (fun s ↦ -(q.endSign * g s)) A :=
      h.congr ((ae_restrict_iff' hmeasA).2 (Eventually.of_forall hinner))
    refine IntegrableOn.congr_fun (h'.const_mul (-q.endSign)) (fun s _ ↦ ?_) hmeasA
    rw [neg_mul_neg, ← mul_assoc, endSign_mul_self, one_mul]
  have hg0 : ∀ s, s ∉ A → g s = 0 := by
    intro s hs
    have : q.endSign * s ≤ 1 / 2 := not_lt.1 hs
    simp only [g, smoothTransition.deriv_of_neg (by linarith : q.endSign * s - T < 0), zero_mul]
  have hg : Integrable g := hgA.integrable_of_forall_notMem_eq_zero hg0
  -- Substitute `σ = ±s`.
  have hgh : g = fun s ↦ deriv smoothTransition (q.endSign * s - T) *
      endAction ω H u q (q.endSign * s) := by
    funext s
    rw [endAction_endSign_mul]
  have hne : q.endSign ≠ 0 := by
    intro h
    simpa [h] using endSign_mul_self q
  refine ⟨?_, ?_⟩
  · have h := hg.comp_mul_left' hne
    refine h.congr (Eventually.of_forall fun σ ↦ ?_)
    rw [hgh]
    simp only [← mul_assoc, endSign_mul_self, one_mul]
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hder q.injOn_endChart,
      setIntegral_congr_fun hmeas hF, hstrip, Measure.volume_eq_prod, setIntegral_prod F hFint,
      setIntegral_congr_fun hmeasA hinner, integral_neg, integral_const_mul,
      setIntegral_eq_integral_of_forall_compl_eq_zero hg0, hgh,
      Measure.integral_comp_mul_left (fun σ ↦ deriv smoothTransition (σ - T) * endAction ω H u q σ),
      abs_inv, abs_endSign, inv_one, one_smul]

/-- **The collar term.** The integral of `dχ_T ∧ α` over the plane is `-∑ ±` the averages of the
actions of the loops of the three ends against the weight `β'(σ - T)`. -/
private theorem integral_collarDensity (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) {T₀ T : ℝ}
    (hT : 1 ≤ T) (hT₀ : T₀ ≤ T)
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w) :
    (∀ q, Integrable (fun σ ↦ deriv smoothTransition (σ - T) * endAction ω H u q σ)) ∧
      ∫ z, collarDensity ω K u T z =
        -∑ q, q.endSign * ∫ σ, deriv smoothTransition (σ - T) * endAction ω H u q σ := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hend := fun q ↦
    integral_image_endChart_collarDensity (ω := ω) hu hK hH hHc hT hT₀ hKend q
  refine ⟨fun q ↦ (hend q).1, ?_⟩
  -- The collar term vanishes off the strips of the ends.
  have hsupp : ∀ z, z ∉ ⋃ q : Puncture, q.endChart '' q.endStrip →
      collarDensity ω K u T z = 0 := by
    intro z hz
    by_cases hzD : z ∈ pantsDomain
    · by_cases h : ∃ q, T ≤ signedCoord q z
      · obtain ⟨q, hq⟩ := h
        exact absurd (mem_iUnion.2 ⟨q, mem_image_endChart (mem_pantsDomain_iff.1 hzD)
          (show 1 / 2 < signedCoord q z by linarith)⟩) hz
      · push Not at h
        have hev : ∀ᶠ w in 𝓝 z, w ∈ pantsDomain ∧ ∀ q, signedCoord q w < T :=
          Filter.Eventually.and (isOpen_pantsDomain.mem_nhds hzD) (eventually_all.2 fun q ↦
            (contDiffAt_signedCoord q hzD (n := 0)).continuousAt.eventually (gt_mem_nhds (h q)))
        have h1 : cutoff T =ᶠ[𝓝 z] fun _ ↦ 1 :=
          hev.mono fun w hw ↦ cutoff_eq_one hw.1 fun q ↦ (hw.2 q).le
        simp [collarDensity, h1.fderiv_eq]
    · simp [collarDensity, (fderiv_cutoff_eventuallyEq_zero hT0 hzD).eq_of_nhds]
  have hmeas (q : Puncture) : MeasurableSet (q.endChart '' q.endStrip) :=
    (q.endStrip_def ▸ (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod
      measurableSet_Ico).image_of_continuousOn_injOn
      (q.contDiff_endChart (n := 0)).continuous.continuousOn q.injOn_endChart
  have hdisj : Pairwise (Disjoint on fun q : Puncture ↦ q.endChart '' q.endStrip) := by
    intro q r hqr
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have h := congrArg Complex.equivRealProdCLM.symm hab
    rw [equivRealProdCLM_symm_endChart, equivRealProdCLM_symm_endChart] at h
    exact cylindricalEndLift_ne_cylindricalEndLift hqr
      (by simpa [Complex.equivRealProdCLM_symm_apply] using endSign_mul_pos_of_mem_endStrip ha)
      (by simpa [Complex.equivRealProdCLM_symm_apply] using endSign_mul_pos_of_mem_endStrip hb)
      h.symm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_iUnion_fintype hmeas hdisj fun q ↦ (integrable_collarDensity hu hK hT0).integrableOn,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ ↦ (hend q).2

end Collar

section Limit

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ}
  {u : ℝ × ℝ → V} {H : Puncture → ℝ → V → ℝ}

private theorem continuous_cutoff_mul {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h pantsDomain) {T : ℝ}
    (hT : 0 ≤ T) : Continuous fun z ↦ cutoff T z * h z :=
  continuous_of_continuousOn_pantsDomain (fun _ hz ↦
    ((contDiffAt_cutoff (n := 0) hz).continuousAt.mul
      (hh.continuousAt (isOpen_pantsDomain.mem_nhds hz))).continuousWithinAt)
    fun _ hz ↦ cutoff_mul_eventuallyEq_zero hT h hz

private theorem integrable_cutoff_mul {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h pantsDomain) {T : ℝ}
    (hT : 0 ≤ T) : Integrable fun z ↦ cutoff T z * h z :=
  (continuous_cutoff_mul hh hT).integrable_of_hasCompactSupport
    (hasCompactSupport_cutoff hT).mul_right

omit [FiniteDimensional ℝ V] in
private theorem contDiffOn_uncurry_perturbation
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
      (pantsDomain ×ˢ univ) := fun p hp ↦ (contDiffAt_uncurry_perturbation
    (hK _ (mem_pantsDomain_iff.1 hp.1).1 (mem_pantsDomain_iff.1 hp.1).2 p.2) v).contDiffWithinAt

private theorem continuousOn_floerEnergyDensity_pantsDomain (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x)) :
    ContinuousOn (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) pantsDomain :=
  ω.continuousOn_floerEnergyDensity isOpen_pantsDomain (hu.of_le one_le_two)
    (contDiffOn_uncurry_perturbation hK 1) (contDiffOn_uncurry_perturbation hK _)

private theorem continuousOn_hamiltonianCurvature_pantsDomain {u : ℝ × ℝ → V}
    (hu : ContinuousOn u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x)) :
    ContinuousOn (fun z ↦ ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) pantsDomain :=
  ω.continuousOn_hamiltonianCurvature_comp isOpen_pantsDomain hu
    (contDiffOn_uncurry_perturbation hK 1) (contDiffOn_uncurry_perturbation hK _)

private theorem ae_mem_pantsDomain : ∀ᵐ z : ℝ × ℝ, z ∈ pantsDomain := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  exact compl_mem_ae_iff.2 ((Set.toFinite _).measure_zero _)

/-- **The energy identity in the limit.** The integrals of `χ_T e`, over `T ∈ ℕ`, converge to
`∑ ±a_q - ∫ R_K`. -/
private theorem tendsto_integral_cutoff_mul_floerEnergyDensity (hu : ContDiffOn ℝ 2 u pantsDomain)
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) {T₀ : ℝ}
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (endAction ω H u q) atTop (𝓝 (a q))) :
    Tendsto (fun n : ℕ ↦ ∫ z, cutoff n z * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) atTop
      (𝓝 (∑ q, q.endSign * a q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))) := by
  set e := ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set R := fun z ↦ ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  have he : ContinuousOn e pantsDomain := continuousOn_floerEnergyDensity_pantsDomain hu hK
  have hRc : ContinuousOn R pantsDomain :=
    continuousOn_hamiltonianCurvature_pantsDomain hu.continuousOn hK
  -- The exact identity at every large level `T`.
  have hlarge : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ T₀ ≤ T :=
    (eventually_ge_atTop 1).and (eventually_ge_atTop T₀)
  have hid : ∀ᶠ T : ℝ in atTop,
      ∫ z, cutoff T z * e z = (∑ q, q.endSign * ∫ σ, deriv smoothTransition (σ - T) *
        endAction ω H u q σ) - ∫ z, cutoff T z * R z := by
    filter_upwards [hlarge] with T hT
    have h := integral_cutoff_mul_eq_neg (ω := ω) hu hK (by linarith : (0 : ℝ) ≤ T)
    rw [(integral_collarDensity hu hK hH hHc hT.1 hT.2 hKend).2, neg_neg] at h
    rw [← h, eq_sub_iff_add_eq, ← integral_add (integrable_cutoff_mul he (by linarith))
      (integrable_cutoff_mul hRc (by linarith))]
    simp only [e, R, mul_add]
  -- The averaged actions converge to the asymptotic actions.
  have hact : Tendsto (fun T : ℝ ↦ ∑ q, q.endSign * ∫ σ, deriv smoothTransition (σ - T) *
      endAction ω H u q σ) atTop (𝓝 (∑ q, q.endSign * a q)) :=
    tendsto_finsetSum _ fun q _ ↦ (smoothTransition.tendsto_integral_deriv_sub_smul (ha q)
      (hlarge.mono fun T hT ↦
        ((integral_collarDensity hu hK hH hHc hT.1 hT.2 hKend).1 q))).const_mul _
  -- The cut-off curvature integrals converge by dominated convergence.
  have hcurv : Tendsto (fun n : ℕ ↦ ∫ z, cutoff n z * R z) atTop (𝓝 (∫ z, R z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ ‖R z‖)
      (fun n ↦ (continuous_cutoff_mul hRc n.cast_nonneg).aestronglyMeasurable) hR.norm
      (fun n ↦ ae_of_all _ fun z ↦ ?_) ?_
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (by simpa [abs_of_nonneg (cutoff_mem_Icc n.cast_nonneg z).1] using
          (cutoff_mem_Icc n.cast_nonneg z).2)
    · filter_upwards [ae_mem_pantsDomain] with z hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_cutoff_eq_one hz)]
        with n hn
      rw [hn, one_mul]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  exact ((hact.comp hnat).sub hcurv).congr' (hnat.eventually hid |>.mono fun n hn ↦ hn.symm)

end Limit

section Main

variable [FiniteDimensional ℝ V] (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ}

private theorem sum_endSign_mul (a : Puncture → ℝ) :
    ∑ q, q.endSign * a q = a zero + a one - a inf := by
  rw [show (Finset.univ : Finset Puncture) = {zero, one, inf} from rfl]
  simp
  ring

/-- **The energy identity on the pair of pants.** Let `K` be a perturbation datum on
`S = ℂ ∖ {0, 1}`, `C¹` jointly with the target point, which on the part `±s ≥ T₀` of each end
`q` is `H_q(t) dt` for a continuous period-one Hamiltonian `H_q`. Let `u` be a `C²` map on `S`
into a symplectic vector space with nonnegative Floer energy density, as for a solution of the
Floer equation with a tamed almost complex structure (`SymplecticForm.floerEnergyDensity_nonneg`),
and with integrable curvature term `R_K(u)`. If the actions of the loops `t ↦ u(s, t)` of the end
`q` tend to `a_q` as `±s → ∞`, then the energy of `u` is `a₀ + a₁ - a_∞ - ∫ R_K(u)`.

The components of `K` in the global coordinate `z = s + i t` of `ℂ` are `K_s = K(·)(1)` and
`K_t = K(·)(i)`, and the loops of the ends are parametrized by the end charts
`ThricePuncturedSphere.Puncture.endChart`. -/
theorem lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_endChart
    {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {(0, 0), (1, 0)}ᶜ)
    (he : ∀ z ∉ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (q.endChart (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (a zero + a one - a inf - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  have hlim := tendsto_integral_cutoff_mul_floerEnergyDensity hu hK hH hHc hKend hR ha
  rw [sum_endSign_mul] at hlim
  have hec := continuousOn_floerEnergyDensity_pantsDomain (ω := ω) hu hK
  -- The cut-off energies increase to the energy, by monotone convergence.
  have hmono : Tendsto (fun n : ℕ ↦ ∫⁻ z, ENNReal.ofReal (cutoff n z * ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n ↦ (ENNReal.measurable_ofReal.comp
      (continuous_cutoff_mul hec n.cast_nonneg).measurable).aemeasurable) ?_ ?_
    · filter_upwards [ae_mem_pantsDomain] with z hz
      intro m n hmn
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (cutoff_mono (Nat.cast_le.2 hmn) z) (he z hz))
    · filter_upwards [ae_mem_pantsDomain] with z hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_cutoff_eq_one hz)]
        with n hn
      rw [hn, one_mul]
  refine tendsto_nhds_unique hmono
    (((ENNReal.continuous_ofReal.tendsto _).comp hlim).congr fun n ↦ ?_)
  rw [Function.comp_apply, ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoff_mul hec n.cast_nonneg)]
  filter_upwards [ae_mem_pantsDomain] with z hz
  exact mul_nonneg (cutoff_mem_Icc n.cast_nonneg z).1 (he z hz)

/-- **The action inequality on the pair of pants.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_endChart`, the
integrated curvature is at most `a₀ + a₁ - a_∞`, since the energy is nonnegative. -/
theorem integral_hamiltonianCurvature_le_of_tendsto_hamiltonianAction_endChart
    {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hK : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ K p.1 p.2) (w, x))
    (hKend : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {(0, 0), (1, 0)}ᶜ)
    (he : ∀ z ∉ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (q.endChart (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) ≤
      a zero + a one - a inf := by
  have hlim := tendsto_integral_cutoff_mul_floerEnergyDensity hu hK hH hHc hKend hR ha
  rw [sum_endSign_mul] at hlim
  have h := ge_of_tendsto' hlim fun n ↦ integral_nonneg_of_ae (by
    filter_upwards [ae_mem_pantsDomain] with z hz
    exact mul_nonneg (cutoff_mem_Icc n.cast_nonneg z).1 (he z hz))
  linarith

/-- The curvature of the pair-of-pants perturbation along a map continuous on `S` is integrable,
with integral at most `B₀ + B₁ + B_∞` in absolute value. -/
private theorem integrable_hamiltonianCurvature_pairOfPantsPerturbation
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V} (hu : ContinuousOn u pantsDomain) :
    Integrable (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) ∧
      |∫ z, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  have hbound := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH hHs hB u
  have hB0 (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  have hc := continuousOn_hamiltonianCurvature_pantsDomain (ω := ω) hu fun _ hw₀ hw₁ x ↦
    contDiffAt_pairOfPantsPerturbation_prod hH hHs ⟨hw₀, hw₁⟩ x
  have hmeas : AEStronglyMeasurable (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) := by
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_pantsDomain]
    exact hc.aestronglyMeasurable isOpen_pantsDomain.measurableSet
  have hfin : ∑ q, ENNReal.ofReal (B q) ≠ ⊤ := by
    simp [ENNReal.sum_eq_top]
  refine ⟨⟨hmeas, (hbound.trans_lt hfin.lt_top)⟩, ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  simp only [ofReal_norm]
  refine (ENNReal.toReal_mono hfin hbound).trans_eq ?_
  rw [ENNReal.toReal_sum fun q _ ↦ ENNReal.ofReal_ne_top]
  exact Finset.sum_congr rfl fun q _ ↦ ENNReal.toReal_ofReal (hB0 q)

/-- **The energy identity for the pair-of-pants perturbation.** For the perturbation
`Floer.pairOfPantsPerturbation H` of bounded period-one `C¹` Hamiltonians `H_q`, a `C²` map `u`
on `S = ℂ ∖ {0, 1}` with nonnegative Floer energy density whose end loops have actions tending to
`a_q` has energy `a₀ + a₁ - a_∞ - ∫ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq_of_tendsto
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {(0, 0), (1, 0)}ᶜ)
    (he : ∀ z ∉ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (q.endChart (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (a zero + a one - a inf - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) :=
  ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_endChart
    (fun _ hw₀ hw₁ x ↦ contDiffAt_pairOfPantsPerturbation_prod hH hHs ⟨hw₀, hw₁⟩ x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH
    (fun q ↦ (hHs q).continuous) hu he
    (integrable_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hB hu.continuousOn).1 ha

/-- **The energy bound for the pair-of-pants product.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq_of_tendsto`, with
`|H_q| ≤ B_q`, the energy of `u` is at most `a₀ + a₁ - a_∞ + B₀ + B₁ + B_∞`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_le_of_tendsto
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {(0, 0), (1, 0)}ᶜ)
    (he : ∀ z ∉ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (q.endChart (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal (a zero + a one - a inf + ∑ q, B q) := by
  rw [ω.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq_of_tendsto hH hHs hB hu he ha]
  have h := (integrable_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hB
    hu.continuousOn).2
  exact ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))])

/-- **The action bound for the pair-of-pants product.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq_of_tendsto`, with
`|H_q| ≤ B_q`, the asymptotic action at the output end is at most the sum of the asymptotic
actions at the input ends plus `B₀ + B₁ + B_∞`. -/
theorem action_inf_le_of_tendsto_pairOfPantsPerturbation
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u {(0, 0), (1, 0)}ᶜ)
    (he : ∀ z ∉ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {a : Puncture → ℝ} (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (q.endChart (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    a inf ≤ a zero + a one + ∑ q, B q := by
  have h := ω.integral_hamiltonianCurvature_le_of_tendsto_hamiltonianAction_endChart
    (fun _ hw₀ hw₁ x ↦ contDiffAt_pairOfPantsPerturbation_prod hH hHs ⟨hw₀, hw₁⟩ x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH
    (fun q ↦ (hHs q).continuous) hu he
    (integrable_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hB hu.continuousOn).1 ha
  have h' := (integrable_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hB
    hu.continuousOn).2
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))]

end Main

end SymplecticForm

end TauCeti
