/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.PDE.YangMills.GaugeIdentities

/-!
# Examples of the gauge identities

Worked cases of the gauge calculus of `TauCeti.Analysis.PDE.YangMills.GaugeIdentities`.

* The structure group `U(1)`, with coefficients `ℂ`: the one-form `A = i x₁ dx₂` on `ℝ²` has
  curvature `F₁₂ = i` (`connectionCurvature_u1Connection`); the gauge transformation
  `O = exp (i φ)` acts by `O·A = A - i dφ` (`gaugeAction_expPhase`) and leaves the curvature
  unchanged (`connectionCurvature_gaugeAction_expPhase`).
* A constant `U(1)` gauge transformation is central, so it acts trivially
  (`gaugeAction_const_of_ne_zero`, from `TauCeti.gaugeAction_const_of_commute`).
* The structure group `SU(2)`, as the unit quaternions: for `O(t) = g exp (t i)` with `g = 1 + k`
  (a multiple of `exp (π k / 4)`, so with the same adjoint action) and the constant `B = j`, the
  derivative of `Ad(O)B` at `t = 0` is `[O;1, Ad(O)B] = 2k`
  (`fderiv_su2Gauge_mul_mul_ringInverse`), while `Ad(O)[O;1, B] = 0`
  (`su2Gauge_mul_lie_mul_ringInverse_zero`). So the second term of the Leibniz rule
  `TauCeti.fderiv_mul_mul_ringInverse_apply` cannot be replaced by `Ad(O)[O;1, B]`.

## References

* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Lemma 3.4.
-/

public section

noncomputable section

open Complex ContinuousLinearMap
open scoped ContDiff Quaternion Ring

namespace TauCeti.GaugeIdentitiesExample

/-! ### The structure group `U(1)` -/

/-- The `U(1)` connection `A = i x₁ dx₂` on `ℝ²`, as the linear map `x ↦ x₁ • (i dx₂)`. -/
def u1Connection : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℂ :=
  (fst ℝ ℝ ℝ).smulRight (I • (ofRealCLM.comp (snd ℝ ℝ ℝ)))

theorem u1Connection_apply (x v : ℝ × ℝ) : u1Connection x v = x.1 * (I * v.2) := by
  simp [u1Connection, Complex.real_smul]

/-- The curvature of `A = i x₁ dx₂` is `F₁₂ = i`. -/
theorem connectionCurvature_u1Connection (x : ℝ × ℝ) :
    connectionCurvature ℝ (⇑u1Connection) x (1, 0) (0, 1) = I := by
  rw [connectionCurvature_apply_of_comm, u1Connection.fderiv]
  simp [u1Connection_apply]

/-- The `U(1)` gauge transformation `O = exp (i φ)` of a real phase `φ`. -/
def expPhase (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  exp (φ x * I)

theorem isUnit_expPhase (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : IsUnit (expPhase φ x) :=
  (exp_ne_zero _).isUnit

/-- The Maurer–Cartan form of `O = exp (i φ)` is `O;x = i dφ`. -/
theorem rightMaurerCartan_expPhase {φ : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hφ : DifferentiableAt ℝ φ x)
    (v : ℝ × ℝ) : rightMaurerCartan ℝ (expPhase φ) x v = I * fderiv ℝ φ x v := by
  have h : HasFDerivAt (expPhase φ)
      (exp (φ x * I) • (I • (ofRealCLM.comp (fderiv ℝ φ x)))) x :=
    ((ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt).mul_const I).cexp.congr_fderiv (by
      ext <;> simp [mul_comm I])
  rw [rightMaurerCartan_apply, h.fderiv, Ring.inverse_eq_inv]
  simp only [smul_apply, comp_apply, ofRealCLM_apply, smul_eq_mul, expPhase]
  field_simp [exp_ne_zero]

/-- **The `U(1)` gauge action**: `O = exp (i φ)` acts by `O·A = A - i dφ`. -/
theorem gaugeAction_expPhase {φ : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hφ : DifferentiableAt ℝ φ x)
    (A : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ) (v : ℝ × ℝ) :
    gaugeAction ℝ (expPhase φ) A x v = A x v - I * fderiv ℝ φ x v := by
  rw [gaugeAction_eq_sub (isUnit_expPhase φ x), sub_apply, rightMaurerCartan_expPhase hφ]

/-- **The `U(1)` gauge action preserves curvature**: `F[exp (i φ)·A] = F[A]` for a twice
continuously differentiable phase `φ`. -/
theorem connectionCurvature_gaugeAction_expPhase {φ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) {A : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ} (hA : DifferentiableAt ℝ A x)
    (v w : ℝ × ℝ) :
    connectionCurvature ℝ (gaugeAction ℝ (expPhase φ) A) x v w =
      connectionCurvature ℝ A x v w := by
  have hO : ContDiffAt ℝ 2 (expPhase φ) x :=
    ((ofRealCLM.contDiff.contDiffAt.comp x hφ).mul contDiffAt_const).cexp
  rw [connectionCurvature_gaugeAction hO (by simp) (isUnit_expPhase φ x) hA,
    mul_comm _ (expPhase φ x)⁻¹ʳ, ← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_expPhase φ x),
    one_mul]

/-- A constant `U(1)` gauge transformation `c ≠ 0` is central, so it acts trivially. -/
theorem gaugeAction_const_of_ne_zero {c : ℂ} (hc : c ≠ 0) (A : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ) :
    gaugeAction ℝ (fun _ ↦ c) A = A :=
  gaugeAction_const_of_commute hc.isUnit fun _ _ ↦ Commute.all _ _

/-! ### The structure group `SU(2)` -/

/-- The quaternion `g = 1 + k`, a positive multiple of `exp (π k / 4)`. -/
def su2Element : ℍ[ℝ] := ⟨1, 0, 0, 1⟩

/-- The gauge transformation `O(t) = g exp (t i)` on `ℝ`, with `g = 1 + k`. -/
def su2Gauge (t : ℝ) : ℍ[ℝ] :=
  su2Element * NormedSpace.exp (t • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]))

theorem su2Gauge_zero : su2Gauge 0 = su2Element := by
  simp [su2Gauge]

theorem isUnit_su2Element : IsUnit su2Element :=
  isUnit_iff_ne_zero.mpr fun h ↦ by simpa [su2Element] using congrArg QuaternionAlgebra.re h

theorem su2Element_inv : su2Element⁻¹ = ⟨1 / 2, 0, 0, -1 / 2⟩ := by
  rw [inv_eq_of_mul_eq_one_right]
  ext <;> norm_num [su2Element]

theorem hasDerivAt_su2Gauge : HasDerivAt su2Gauge (su2Element * ⟨0, 1, 0, 0⟩) 0 := by
  have h := (hasDerivAt_exp_smul_const (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) (0 : ℝ)).const_mul su2Element
  rwa [zero_smul, NormedSpace.exp_zero, one_mul] at h

/-- The Maurer–Cartan form `O;1 = Ad(g) i = j`. -/
theorem rightMaurerCartan_su2Gauge : rightMaurerCartan ℝ su2Gauge 0 1 = ⟨0, 0, 1, 0⟩ := by
  rw [rightMaurerCartan_apply, fderiv_apply_one_eq_deriv, hasDerivAt_su2Gauge.deriv,
    su2Gauge_zero, Ring.inverse_eq_inv, su2Element_inv]
  ext <;> norm_num [su2Element]

/-- The derivative of `Ad(O) j` at `t = 0` is `[O;1, Ad(O) j] = [j, -i] = 2k`. -/
theorem fderiv_su2Gauge_mul_mul_ringInverse :
    fderiv ℝ (fun t ↦ su2Gauge t * ⟨0, 0, 1, 0⟩ * (su2Gauge t)⁻¹ʳ) 0 1 = ⟨0, 0, 0, 2⟩ := by
  rw [fderiv_mul_mul_ringInverse_apply hasDerivAt_su2Gauge.differentiableAt
      (su2Gauge_zero ▸ isUnit_su2Element) (differentiableAt_const _), fderiv_const_apply,
    rightMaurerCartan_su2Gauge, su2Gauge_zero, Ring.inverse_eq_inv, su2Element_inv]
  ext <;> norm_num [su2Element, Ring.lie_def]

/-- The uncorrected second term `Ad(O)[O;1, j] = Ad(g)[j, j]` vanishes. -/
theorem su2Gauge_mul_lie_mul_ringInverse_zero :
    su2Gauge 0 * ⁅rightMaurerCartan ℝ su2Gauge 0 1, ⟨0, 0, 1, 0⟩⁆ * (su2Gauge 0)⁻¹ʳ = 0 := by
  rw [rightMaurerCartan_su2Gauge, Ring.lie_def, sub_self, mul_zero, zero_mul]

end TauCeti.GaugeIdentitiesExample
