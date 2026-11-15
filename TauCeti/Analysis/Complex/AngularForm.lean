/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import TauCeti.Topology.Circle.Degree
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The planar angular `1`-form and its path integrals

The planar **angular `1`-form**
$$\omega_z(v) = \operatorname{Im}(v / z) = \frac{x\,dy - y\,dx}{x^2 + y^2}$$
is the real-valued covector field `TauCeti.angularForm : ℂ → ℂ →L[ℝ] ℝ` obtained by composing
`Complex.imCLM` with complex multiplication by `z⁻¹`.

On `Complex.slitPlane` it is the Fréchet derivative of `Complex.arg`, and on `-Complex.slitPlane` it
is the Fréchet derivative of `w ↦ Complex.arg (-w)`. Since those two open sets cover the punctured
plane `{0}ᶜ`, `angularForm` satisfies `TauCeti.HasLocalPotentials ({0} : Set ℂ)ᶜ angularForm`.

Pulling `angularForm` back along the universal covering `Circle.exp : ℝ → Circle` yields the
constant covector field `1` on `ℝ`. Consequently, for *every* continuous path `γ` in `Circle`, its
continuous path integral `TauCeti.localPotentialIntegral angularForm` equals the swept angle
`Circle.angleChange γ`, and for every continuous loop `γ` in `Circle` it equals
`Circle.degree γ * (2 * Real.pi)`. In particular:

* around `Circle.expLoop` (`t ↦ exp(2πit)`) the integral is `2π`;
* around `Circle.expLoop.trans Circle.expLoop` it is `4π`;
* around `Circle.expLoop.symm` it is `-2π`.

Because `2π ≠ 0`, `angularForm` admits no global potential on `{0}ᶜ`—separating
`TauCeti.HasLocalPotentials` from global exactness—and `z ↦ z⁻¹` admits no global complex primitive
on `{0}ᶜ`.

## Main definitions and results

* `TauCeti.angularForm`: the planar angular `1`-form `z ↦ (v ↦ Im (v / z))`.
* `TauCeti.angularForm_apply_re_im`: coordinate formula
  `(z.re * v.im - z.im * v.re) / Complex.normSq z`.
* `TauCeti.hasFDerivAt_arg_angularForm` and `TauCeti.hasLocalPotentials_angularForm_slitPlane`:
  `Complex.arg` is a global smooth potential on `Complex.slitPlane`.
* `TauCeti.hasLocalPotentials_angularForm`: `angularForm` has local potentials on `{0}ᶜ`.
* `TauCeti.localPotentialIntegral_angularForm_map_circle` and
  `TauCeti.localPotentialIntegral_angularForm_map_circle_loop`: path integral along any continuous
  path or loop in `Circle` in terms of `Circle.angleChange` and `Circle.degree`.
* `TauCeti.localPotentialIntegral_angularForm_expLoop`: the unit circle loop integrates to `2π`.
* `TauCeti.not_exists_hasFDerivAt_angularForm_compl_singleton_zero` and
  `TauCeti.not_isExactOn_inv_compl_singleton_zero`: non-existence of global real/complex primitives
  on the punctured plane `{0}ᶜ`.
-/

public section

noncomputable section

open Set Complex
open scoped unitInterval ContDiff

namespace TauCeti

/-- The planar angular `1`-form `z ↦ (v ↦ Im (v / z))`, equal in real coordinates `z = x + iy`,
`v = dx + i dy` to `(x dy - y dx) / (x² + y²)`, with junk value `0` at `z = 0`. -/
def angularForm (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM ∘L (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ

/-- Evaluating `angularForm z` at a tangent vector `v` takes the imaginary part of `v / z`. -/
@[simp]
theorem angularForm_apply (z v : ℂ) : angularForm z v = (v / z).im := by
  simp [angularForm, div_eq_mul_inv]

/-- Explicit real-coordinate formula `(x dy - y dx) / (x² + y²)` for `angularForm`. -/
theorem angularForm_apply_re_im (z v : ℂ) :
    angularForm z v = (z.re * v.im - z.im * v.re) / Complex.normSq z := by
  rw [angularForm_apply, Complex.div_im]
  ring

/-- At the origin `angularForm` takes the junk value `0`. -/
@[simp]
theorem angularForm_zero : angularForm 0 = 0 := by
  ext v
  simp

/-- Reflection through the origin negates `angularForm` at the reflected point. -/
@[simp]
theorem angularForm_neg (z : ℂ) : angularForm (-z) = -angularForm z := by
  ext v
  simp [div_neg]

/-! ### Local potentials via branches of `Complex.arg` -/

/-- On `Complex.slitPlane`, the principal argument `Complex.arg` has Fréchet derivative
`angularForm z` at `z`. -/
theorem hasFDerivAt_arg_angularForm {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasFDerivAt Complex.arg (angularForm z) z := by
  simpa [angularForm, one_div] using (hasDerivAt_id z).hasFDerivAt_arg hz

/-- On `-Complex.slitPlane`, the rotated branch `w ↦ Complex.arg (-w)` has Fréchet derivative
`angularForm z` at `z`. -/
theorem hasFDerivAt_arg_neg_angularForm {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    HasFDerivAt (fun w ↦ Complex.arg (-w)) (angularForm z) z := by
  have h := (hasDerivAt_id z).neg.hasFDerivAt_arg hz
  have hdiv : (-1 : ℂ) / -z = z⁻¹ := by rw [neg_div_neg_eq, one_div]
  simpa [angularForm, hdiv] using h

/-- On `Complex.slitPlane`, `angularForm` has local potentials (indeed the global smooth potential
`Complex.arg`). -/
theorem hasLocalPotentials_angularForm_slitPlane :
    HasLocalPotentials Complex.slitPlane angularForm :=
  hasLocalPotentials_of_hasFDerivAt Complex.isOpen_slitPlane
    (fun _ hz ↦ (Complex.contDiffAt_arg hz).contDiffWithinAt)
    fun _ hz ↦ hasFDerivAt_arg_angularForm hz

/-- On the punctured plane `{0}ᶜ`, `angularForm` has local `C¹` potentials. -/
theorem hasLocalPotentials_angularForm :
    HasLocalPotentials ({0} : Set ℂ)ᶜ angularForm := by
  have hneg : HasLocalPotentials {z : ℂ | -z ∈ Complex.slitPlane} angularForm :=
    hasLocalPotentials_of_hasFDerivAt (Complex.isOpen_slitPlane.preimage continuous_neg)
      (fun z hz ↦ ((Complex.contDiffAt_arg hz).comp z contDiff_neg.contDiffAt).contDiffWithinAt)
      fun _ hz ↦ hasFDerivAt_arg_neg_angularForm hz
  have hcover : Complex.slitPlane ∪ {z : ℂ | -z ∈ Complex.slitPlane} = ({0} : Set ℂ)ᶜ := by
    ext z
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun h ↦ h.elim Complex.slitPlane_ne_zero
        fun hnz hz0 ↦ Complex.slitPlane_ne_zero hnz (by simp [hz0]),
      Complex.mem_slitPlane_or_neg_mem_slitPlane⟩
  rw [← hcover]
  exact hasLocalPotentials_angularForm_slitPlane.union hneg

/-! ### Pullback to the universal cover of `Circle` and path integrals -/

/-- Pulling `angularForm` back along `θ ↦ (Circle.exp θ : ℂ)` gives the identity covector on `ℝ`. -/
theorem angularForm_comp_fderiv_circleExp (θ : ℝ) :
    (angularForm (Circle.exp θ)).comp (fderiv ℝ (fun s : ℝ ↦ (Circle.exp s : ℂ)) θ) =
      ContinuousLinearMap.id ℝ ℝ := by
  have hd : fderiv ℝ (fun s : ℝ ↦ (Circle.exp s : ℂ)) θ =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (Complex.I * Circle.exp θ) :=
    (hasDerivAt_coe_circleExp θ).hasFDerivAt.fderiv
  ext
  rw [ContinuousLinearMap.comp_apply, hd, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, angularForm_apply,
    mul_div_cancel_right₀ _ (Circle.coe_ne_zero _), Complex.I_im]

/-- Along *any* continuous path `γ` in the unit circle, the continuous path integral of
`angularForm` equals the swept angle `Circle.angleChange γ`. -/
theorem localPotentialIntegral_angularForm_map_circle {x y : Circle} (γ : Path x y) :
    localPotentialIntegral angularForm (γ.map continuous_subtype_val) =
      Circle.angleChange γ := by
  obtain ⟨θ, hθ⟩ := Circle.exists_lift γ
  let f : ℝ → ℂ := fun s ↦ (Circle.exp s : ℂ)
  have hfc : Continuous f := continuous_subtype_val.comp Circle.exp.continuous
  have hf_smooth : ContDiffOn ℝ 1 f univ := by
    have hfeq : f = fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I) := funext Circle.coe_exp
    rw [hfeq]
    exact (Complex.contDiff_exp.comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const)).contDiffOn
  let Θ : Path (θ 0) (θ 1) := ⟨θ, rfl, rfl⟩
  have hcongr : ∀ t, (γ.map continuous_subtype_val) t = (Θ.map hfc) t :=
    fun t ↦ congrArg Subtype.val (hθ t).symm
  rw [localPotentialIntegral_congr_path angularForm hcongr,
    localPotentialIntegral_map hasLocalPotentials_angularForm isOpen_univ hf_smooth
      (fun s _ ↦ Circle.coe_ne_zero _) hfc (fun _ ↦ mem_univ _)]
  simp only [f, angularForm_comp_fderiv_circleExp, localPotentialIntegral_const,
    ContinuousLinearMap.id_apply]
  exact (Circle.angleChange_eq_sub γ θ.continuous hθ).symm

/-- Along any continuous loop `γ` in the unit circle, the continuous path integral of `angularForm`
is `2π` times the winding degree `Circle.degree γ`. -/
theorem localPotentialIntegral_angularForm_map_circle_loop {x : Circle} (γ : Path x x) :
    localPotentialIntegral angularForm (γ.map continuous_subtype_val) =
      Circle.degree γ * (2 * Real.pi) := by
  rw [localPotentialIntegral_angularForm_map_circle, Circle.angleChange_eq_degree_mul]

/-- Around the counterclockwise unit circle loop `Circle.expLoop`, `angularForm` integrates to
`2π`. -/
@[simp]
theorem localPotentialIntegral_angularForm_expLoop :
    localPotentialIntegral angularForm (Circle.expLoop.map continuous_subtype_val) =
      2 * Real.pi := by
  rw [localPotentialIntegral_angularForm_map_circle_loop, Circle.degree_expLoop]
  simp

/-- Around the unit circle loop traversed twice counterclockwise, `angularForm` integrates to
`4π`. -/
theorem localPotentialIntegral_angularForm_expLoop_trans_expLoop :
    localPotentialIntegral angularForm
        ((Circle.expLoop.trans Circle.expLoop).map continuous_subtype_val) =
      4 * Real.pi := by
  rw [localPotentialIntegral_angularForm_map_circle_loop, Circle.degree_trans,
    Circle.degree_expLoop]
  norm_num
  ring

/-- Around the reversed (clockwise) unit circle loop, `angularForm` integrates to `-2π`. -/
theorem localPotentialIntegral_angularForm_expLoop_symm :
    localPotentialIntegral angularForm (Circle.expLoop.symm.map continuous_subtype_val) =
      -(2 * Real.pi) := by
  rw [localPotentialIntegral_angularForm_map_circle_loop, Circle.degree_symm,
    Circle.degree_expLoop]
  simp

/-! ### Non-exactness on the punctured plane -/

/-- Although `angularForm` has local `C¹` potentials on `{0}ᶜ`, no function on `ℂ` has Fréchet
derivative `angularForm z` at every `z ∈ {0}ᶜ`. -/
theorem not_exists_hasFDerivAt_angularForm_compl_singleton_zero :
    ¬ ∃ g : ℂ → ℝ, ∀ z ∈ ({0} : Set ℂ)ᶜ, HasFDerivAt g (angularForm z) z := by
  rintro ⟨g, hdg⟩
  have h0 : localPotentialIntegral angularForm (Circle.expLoop.map continuous_subtype_val) = 0 := by
    rw [localPotentialIntegral_of_hasFDerivAt isOpen_compl_singleton hdg
      (fun t ↦ Circle.coe_ne_zero _), sub_self]
  rw [localPotentialIntegral_angularForm_expLoop] at h0
  linarith [Real.pi_pos]

/-- The reciprocal `z ↦ z⁻¹` has no global complex primitive on the punctured plane `{0}ᶜ`. -/
theorem not_isExactOn_inv_compl_singleton_zero :
    ¬ Complex.IsExactOn Inv.inv ({0} : Set ℂ)ᶜ := by
  rintro ⟨G, hG⟩
  refine not_exists_hasFDerivAt_angularForm_compl_singleton_zero ⟨fun z ↦ (G z).im, fun z hz ↦ ?_⟩
  exact Complex.imCLM.hasFDerivAt.comp z ((hG z hz).hasFDerivAt.restrictScalars ℝ)

end TauCeti

end
