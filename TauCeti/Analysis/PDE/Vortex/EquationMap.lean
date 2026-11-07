/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier

/-!
# The plane vortex equation on the affine Sobolev field space

In the real coordinates `x = (b₁, b₂, p, q)` of `TauCeti.Vortex.equation`, the vortex equation,
its linearization `d₁ = linearizedEquation x`, the infinitesimal gauge action
`d₀ = gaugeDirection x` and the gauge-fixed operator `L_x = d₀* ⊕ d₁` with its formal adjoint
are classical first-order differential expressions. This file proves that, for every natural
`k ≥ 1`, they act on the Sobolev scale of framed degree-`m` fields
`A_m^s = x_m + H^s(ℂ; ℝ⁴)` (`TauCeti.Vortex.framedFieldSpace`):

* the equation maps `A_m^(k+1)` to defects in `H^k(ℂ; ℝ ⊕ ℂ)`
  (`TauCeti.Vortex.equation_apply_mem_realSobolevFunctions`);
* at every field `x` of `A_m^(k+1)` the deformation complex has the orders
  `H^(k+2)(ℂ; ℝ) → H^(k+1)(ℂ; ℝ⁴) → H^k(ℂ; ℝ ⊕ ℂ)`
  (`TauCeti.Vortex.gaugeDirection_mem_sobolevFields`,
  `TauCeti.Vortex.linearizedEquation_apply_mem_realSobolevFunctions`), and `L_x` and `L_x*` map
  `H^(k+1)(ℂ; ℝ⁴)` to `H^k(ℂ; ℝ⁴)` (`TauCeti.Vortex.gaugeFixedOperator_mem_sobolevFields`,
  `TauCeti.Vortex.gaugeFixedAdjoint_mem_sobolevFields`).

The expressions differentiate the given representative of a field pointwise, so the statements
concern `C¹` representatives. That every field of sufficiently high order has a `C¹`
representative is not proved here.

The base point of the affine space is the smooth reference field `x_m`, equal to
`(-i m dθ, (z / |z|)^m)` outside a disc. There it is the gauge transform of the vacuum by the
winding phase `(z / |z|)^m`, so it solves the vortex equation
(`TauCeti.Vortex.equation_referenceField_eq_zero`), and its defect is smooth with compact
support. For `x = x_m + y` the equation expands exactly as
`equation x = equation x_m + d₁ y + quadraticTerm y` (`TauCeti.Vortex.equation_add_smul`). The
linear term involves the derivatives of `y` and the products of the coordinates of `x_m` with
those of `y`. These coordinates do not decay, but all their derivatives are bounded, so they
multiply `H^k` into itself. The products of two Sobolev coordinates are controlled by the algebra
property of `H^s(ℂ)`, `s > 1`; this is where `k ≥ 1` is used.

All statements are memberships. Boundedness and smoothness of the completed maps, the weak
equation and elliptic regularity are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric TemperedDistribution
open scoped ContDiff Topology

/-! ### The reference field outside its cutoff disc -/

/-- The unit phase `w / |w|` as a circle-valued map, with value `1` at the origin. -/
private def unitPhase (w : ℂ) : Circle := Circle.exp (arg w)

private theorem coe_unitPhase {w : ℂ} (hw : w ≠ 0) :
    (unitPhase w : ℂ) = w * ((‖w‖⁻¹ : ℝ) : ℂ) := by
  have h := norm_mul_exp_arg_mul_I w
  have hn : (‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw)
  rw [unitPhase, Circle.coe_exp, ofReal_inv]
  field_simp
  rw [mul_comm]
  exact h

private theorem contDiffAt_mul_inv_norm {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : ℂ ↦ v * ((‖v‖⁻¹ : ℝ) : ℂ)) w :=
  contDiffAt_id.mul (ofRealCLM.contDiff.contDiffAt.comp w
    ((contDiffAt_norm ℂ hw).inv (norm_ne_zero_iff.2 hw)))

private theorem eventuallyEq_unitPhase {w : ℂ} (hw : w ≠ 0) :
    (fun v ↦ (unitPhase v : ℂ)) =ᶠ[𝓝 w] fun v ↦ v * ((‖v‖⁻¹ : ℝ) : ℂ) :=
  Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hw) fun _ hv ↦ coe_unitPhase hv

private theorem contDiffAt_unitPhase_pow (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun v ↦ ((unitPhase ^ m) v : ℂ)) w := by
  simp only [Pi.pow_apply, Circle.coe_pow]
  exact ((contDiffAt_mul_inv_norm hw).congr_of_eventuallyEq (eventuallyEq_unitPhase hw)).pow m

/-- The logarithmic derivative of the unit phase is `dθ`, `dθ_w (v) = Im (v / w)`. -/
private theorem gaugeForm_unitPhase {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    gaugeForm unitPhase w v = (v / w).im := by
  have hr : DifferentiableAt ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w :=
    ((contDiffAt_norm ℂ (n := 1) hw).differentiableAt one_ne_zero).inv (norm_ne_zero_iff.2 hw)
  -- The factor `‖·‖⁻¹` is real, and so is its derivative.
  have hd : HasFDerivAt (fun v : ℂ ↦ ((‖v‖⁻¹ : ℝ) : ℂ))
      (ofRealCLM.comp (fderiv ℝ (fun v : ℂ ↦ ‖v‖⁻¹) w)) w :=
    ofRealCLM.hasFDerivAt.comp w hr.hasFDerivAt
  rw [gaugeForm_apply, (eventuallyEq_unitPhase hw).fderiv_eq, coe_unitPhase hw,
    fderiv_fun_mul differentiableAt_fun_id hd.differentiableAt, hd.fderiv]
  have hn : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [← normSq_apply, normSq_eq_norm_sq]
  have hn0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [ofReal_inv, map_mul, map_inv₀, conj_ofReal, fderiv_fun_id, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.id_apply,
    mul_im, mul_re, conj_re, inv_re, ofReal_re, normSq_apply, ofReal_im, mul_zero, add_zero,
    div_self_mul_self', conj_im, inv_im, neg_zero, zero_div, sub_zero, add_im, zero_add, zero_mul,
    neg_mul, add_re, div_im]
  rw [← hn]
  field_simp
  ring

private theorem gaugeForm_unitPhase_pow (m : ℕ) {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    gaugeForm (unitPhase ^ m) w v = m * (v / w).im := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hd (k : ℕ) : DifferentiableAt ℝ (fun v ↦ ((unitPhase ^ k) v : ℂ)) w :=
      (contDiffAt_unitPhase_pow k hw).differentiableAt (by simp)
    rw [pow_succ, gaugeForm_mul (hd n) (by simpa using hd 1)]
    simp only [FunLike.coe_add, Pi.add_apply, ih, gaugeForm_unitPhase hw]
    push_cast
    ring

/-- Outside its cutoff disc, the reference field is the gauge transform of the vacuum by the
winding phase `(z / |z|)^m`. -/
private theorem referenceField_eventuallyEq (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut < ‖z‖ ^ 2) :
    referenceField f m =ᶠ[𝓝 z] gaugeTransform (unitPhase ^ m) vacuumField := by
  have hopen : IsOpen {w : ℂ | f.rOut < ‖w‖ ^ 2} :=
    isOpen_lt continuous_const (continuous_norm.pow 2)
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hw
    linarith [f.rOut_pos]
  have hsec := referenceSection_eq_phase f m (le_of_lt hw)
  have hphase : (w * (‖w‖ : ℂ)⁻¹) ^ m = (unitPhase w : ℂ) ^ m := by
    rw [coe_unitPhase hw0, ofReal_inv]
  ext i
  fin_cases i
  · simp [referenceField_apply, gaugeTransform_apply, vacuumField_apply,
      referenceConnection_eq_angular f m (le_of_lt hw), gaugeForm_unitPhase_pow m hw0]
  · simp [referenceField_apply, gaugeTransform_apply, vacuumField_apply,
      referenceConnection_eq_angular f m (le_of_lt hw), gaugeForm_unitPhase_pow m hw0]
  · simp [-referenceSection_apply, referenceField_apply, gaugeTransform_apply, vacuumField_apply,
      hsec, hphase, div_eq_mul_inv]
  · simp [-referenceSection_apply, referenceField_apply, gaugeTransform_apply, vacuumField_apply,
      hsec, hphase, div_eq_mul_inv]

/-- **The reference field is a vortex outside its cutoff disc.** Where the cutoff is inactive,
the reference pair `(-i m dθ, (z / |z|)^m)` is a gauge transform of the vacuum. -/
theorem equation_referenceField_eq_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut < ‖z‖ ^ 2) : equation (referenceField f m) z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
    linarith [f.rOut_pos]
  rw [equation_eq_of_eventuallyEq (referenceField_eventuallyEq f m hz),
    equation_gaugeTransform_eq_zero_iff ((contDiffAt_unitPhase_pow m hz0).of_le (by simp))
      (fun i ↦ by simp [vacuumField_apply])]
  exact equation_vacuumField z

/-- The defect of the reference field vanishes outside a compact set. -/
theorem hasCompactSupport_equation_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (equation (referenceField f m)) := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 (f.rOut + 1)) fun z hz ↦
    equation_referenceField_eq_zero f m ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hz
  nlinarith [f.rOut_pos]

/-- Every coordinate of the defect of the reference field is a smooth compactly supported
function, hence lies in every Sobolev space. -/
theorem equation_referenceField_apply_mem_realSobolevFunctions (f : ContDiffBump (0 : ℝ))
    (m : ℕ) (i : Fin 3) (s : ℝ) :
    (fun z ↦ equation (referenceField f m) z i) ∈ realSobolevFunctions ℂ s 2 :=
  mem_realSobolevFunctions_of_hasCompactSupport
    (contDiff_euclidean.1 (contDiff_equation (contDiff_referenceField f m)) i)
    ((hasCompactSupport_equation_referenceField f m).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) rfl) s

/-! ### Mapping properties on the Sobolev scale -/

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Multiplication by a coordinate of a framed field.** For `k > 1`, the product of a real
`H^k` function with a coordinate of a field of `A_m^k` lies in `H^k`, although the coordinate
itself does not decay. -/
theorem mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (hk : 1 < k)
    (hx : x ∈ framedFieldSpace f m k) (i : Fin 4) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ k 2) :
    (fun z ↦ x z i * g z) ∈ realSobolevFunctions ℂ k 2 := by
  -- Split `x = x_m + (x - x_m)`: the reference coordinate is a bounded smooth multiplier and
  -- the Sobolev coordinate multiplies in the algebra `H^k`.
  have hy := mem_sobolevFields.1 (mem_framedFieldSpace.1 hx) i
  choose C hC using exists_norm_iteratedFDeriv_referenceField_apply_le f m i
  have hM : 0 ≤ ∑ j ∈ Finset.range (k + 1), |C j| := by positivity
  have h₁ := mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) k
    (contDiff_euclidean.1 (contDiff_referenceField f m) i) hM
    (fun j hj z ↦ (hC j z).trans ((le_abs_self _).trans (Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_range.2 (by omega))))) hg
  have h₂ := mul_mem_realSobolevFunctions
    (finrank_real_complex_lt_two_mul (by exact_mod_cast hk)) hy hg
  convert add_mem h₁ h₂ using 1
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, PiLp.sub_apply]
  ring

/-- The classical partial derivatives of the coordinates of a `C¹` field of order `s + 1` have
order `s`. -/
theorem fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields {s : ℝ} (hs : 0 ≤ s)
    (hy : y ∈ sobolevFields (s + 1)) (hy₁ : ContDiff ℝ 1 y) (i : Fin 4) (v : ℂ) :
    (fun z ↦ fderiv ℝ (fun w ↦ y w i) z v) ∈ realSobolevFunctions ℂ s 2 :=
  fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) hs
    (contDiff_euclidean.1 hy₁ i) (mem_sobolevFields.1 hy i) v

/-- The products `x_i y_j` of a framed field of order `k + 1` and a Sobolev field of order
`k + 1` have order `k + 1`, in particular order `k`. -/
private theorem mul_mem_realSobolevFunctions_of_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1)) (i j : Fin 4) :
    (fun z ↦ x z i * y z j) ∈ realSobolevFunctions ℂ k 2 := by
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [Nat.cast_add_one]
  have hyj : (fun z ↦ y z j) ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 := by
    rw [Nat.cast_add_one]
    exact mem_sobolevFields.1 hy j
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by exact_mod_cast Nat.le_succ k)
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' i hyj)

/-- **The linearized vortex equation on the Sobolev scale.** For `k ≥ 1`, at a field of
`A_m^(k+1)`, the linearization `d₁` maps `C¹` fields of order `k + 1` to defects of order `k`. -/
theorem linearizedEquation_apply_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) (i : Fin 3) :
    (fun z ↦ linearizedEquation x y z i) ∈ realSobolevFunctions ℂ k 2 := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hy hy₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hy
  fin_cases i
  · convert add_mem (add_mem (sub_mem (D 0 I) (D 1 1)) (P 2 2)) (P 3 3) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (D 2 1) (D 3 I)) (P 0 3)) (P 3 0))
      (P 1 2)) (P 2 1) using 1
    ext z
    simp only [Fin.mk_one, linearizedEquation_apply_one, Pi.sub_apply]
    ring
  · convert sub_mem (sub_mem (add_mem (add_mem (add_mem (D 3 1) (D 2 I)) (P 0 2)) (P 2 0))
      (P 1 3)) (P 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, linearizedEquation_apply_two, Pi.sub_apply, Pi.add_apply]
    ring

/-- The quadratic remainder of the vortex equation maps Sobolev fields of order `s > 1` to
defects of order `s`. -/
theorem quadraticTerm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s)
    (hy : y ∈ sobolevFields s) (i : Fin 3) :
    (fun z ↦ quadraticTerm y z i) ∈ realSobolevFunctions ℂ s 2 := by
  have P (a b : Fin 4) : (fun z ↦ y z a) * (fun z ↦ y z b) ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
      (mem_sobolevFields.1 hy a) (mem_sobolevFields.1 hy b)
  fin_cases i
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (P 2 2) (P 3 3)) using 1
    ext z
    simp only [Fin.zero_eta, quadraticTerm_apply_zero, Pi.smul_apply, Pi.add_apply,
      Pi.mul_apply, smul_eq_mul]
    ring
  · convert neg_mem (add_mem (P 0 3) (P 1 2)) using 1
    ext z
    simp only [Fin.mk_one, quadraticTerm_apply_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · convert sub_mem (P 0 2) (P 1 3) using 1
    ext z
    simp

/-- **The vortex equation on the Sobolev scale.** For `k ≥ 1`, the vortex equation maps the
`C¹` fields of the affine space `A_m^(k+1)` to defects of order `k`: each of its three
coordinates lies in `H^k(ℂ)`. -/
theorem equation_apply_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hx₁ : ContDiff ℝ 1 x) (i : Fin 3) :
    (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2 := by
  -- Expand `x = x_m + y` about the reference field: the defect of `x_m` is compactly supported,
  -- the linear term has order `k`, and the quadratic term has order `k + 1`.
  set y := x - referenceField f m with hy_def
  have hy : y ∈ sobolevFields (k + 1) := mem_framedFieldSpace.1 hx
  have href : ContDiff ℝ ∞ (referenceField f m) := contDiff_referenceField f m
  have hy₁ : ContDiff ℝ 1 y := hx₁.sub (href.of_le (by exact_mod_cast le_top))
  have hdiff {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 1 u) (z : ℂ) (j : Fin 4) :
      DifferentiableAt ℝ (fun w ↦ u w j) z :=
    (contDiff_euclidean.1 hu j).differentiable one_ne_zero z
  have hexp (z : ℂ) : equation x z = equation (referenceField f m) z +
      linearizedEquation (referenceField f m) y z + quadraticTerm y z := by
    have h := equation_add_smul (hdiff (href.of_le (by exact_mod_cast le_top)) z) (hdiff hy₁ z) 1
    rwa [one_smul, one_smul, one_pow, one_smul, hy_def, add_sub_cancel] at h
  have hQ := realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith)
    (quadraticTerm_apply_mem_realSobolevFunctions
      (by linarith [(by exact_mod_cast hk : (1 : ℝ) ≤ k)]) hy i)
  convert add_mem (add_mem (equation_referenceField_apply_mem_realSobolevFunctions f m i k)
    (linearizedEquation_apply_mem_realSobolevFunctions hk
      (referenceField_mem_framedFieldSpace f m _) hy hy₁ i)) hQ using 1
  ext z
  simp [hexp z]

/-- **The gauge-fixing row on the Sobolev scale.** For `k ≥ 1`, at a field of `A_m^(k+1)`, the
formal adjoint `d₀*` of the infinitesimal gauge action maps `C¹` fields of order `k + 1` to
functions of order `k`. -/
theorem gaugeAdjoint_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) :
    gaugeAdjoint x y ∈ realSobolevFunctions ℂ k 2 := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hy hy₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hy
  convert sub_mem (add_mem (add_mem (D 0 1) (D 1 I)) (P 2 3)) (P 3 2) using 1
  ext z
  simp

/-- **The gauge-fixed operator on the Sobolev scale.** For `k ≥ 1`, at a field of `A_m^(k+1)`,
`L_x = d₀* ⊕ d₁` maps `C¹` fields of order `k + 1` to fields of order `k`. -/
theorem gaugeFixedOperator_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) :
    gaugeFixedOperator x y ∈ sobolevFields k := by
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [-gaugeAdjoint_def] using gaugeAdjoint_mem_realSobolevFunctions hk hx hy hy₁
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 0
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 1
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 2

/-- **The formal adjoint of the gauge-fixed operator on the Sobolev scale.** For `k ≥ 1`, at a
field of `A_m^(k+1)`, `L_x*` maps `C¹` fields of order `k + 1` to fields of order `k`. -/
theorem gaugeFixedAdjoint_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : η ∈ sobolevFields (k + 1)) (hη₁ : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint x η ∈ sobolevFields k := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hη hη₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hη
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert sub_mem (add_mem (sub_mem (neg_mem (D 0 1)) (D 1 I)) (P 2 3)) (P 3 2) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (add_mem (neg_mem (D 0 I)) (D 1 1)) (P 2 2)) (P 3 3) using 1
    ext z
    simp
  · convert add_mem (sub_mem (add_mem (sub_mem (sub_mem (neg_mem (D 2 1)) (D 3 I)) (P 1 2))
      (P 0 3)) (P 3 0)) (P 2 1) using 1
    ext z
    simp
  · convert add_mem (add_mem (sub_mem (sub_mem (add_mem (neg_mem (D 3 1)) (D 2 I)) (P 0 2))
      (P 1 3)) (P 2 0)) (P 3 1) using 1
    ext z
    simp

/-- **The infinitesimal gauge action on the Sobolev scale.** For `k ≥ 1`, at a field of
`A_m^(k+1)`, the infinitesimal gauge action `d₀` maps `C¹` phases of order `k + 2` to fields of
order `k + 1`. -/
theorem gaugeDirection_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ (k + 2) 2) (hg₁ : ContDiff ℝ 1 g) :
    gaugeDirection x g ∈ sobolevFields (k + 1) := by
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [Nat.cast_add_one]
  have hg' : g ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by push_cast; linarith) hg
  have D (v : ℂ) : (fun z ↦ fderiv ℝ g z v) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by positivity) hg₁
      (by convert hg using 2; ring) v
  have P (i : Fin 4) : (fun z ↦ x z i * g z) ∈ realSobolevFunctions ℂ (k + 1) 2 := by
    simpa only [Nat.cast_add_one] using
      mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' i hg'
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert neg_mem (D 1) using 1
    ext z
    simp
  · convert neg_mem (D I) using 1
    ext z
    simp
  · convert neg_mem (P 3) using 1
    ext z
    simp [mul_comm]
  · convert P 2 using 1
    ext z
    simp [mul_comm]

end TauCeti.Vortex
