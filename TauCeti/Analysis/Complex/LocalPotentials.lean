/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Analysis.Calculus.LocalPotentials.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Local potentials, continuous path integrals, and primitives on the complex plane

Specializing `TauCeti.HasLocalPotentials` and `TauCeti.localPotentialIntegral` to `ℂ` connects the
real theory of locally potential continuous one-forms with complex primitives (`Complex.IsExactOn`)
and supplies the canonical planar examples and counterexamples separating the hypotheses.

1. **Holomorphic one-forms and primitives on simply connected domains.** For a map `f : ℂ → F` with
   values in a complete complex normed space `F`, the `ℂ`-linear covector field
   `z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ` (that is, `v ↦ v • f z`)
   has local potentials on an open set `s ⊆ ℂ` if and only if `f` is holomorphic on `s`
   (`TauCeti.hasLocalPotentials_toSpanSingleton_iff`), combining `DifferentiableOn.isExactOn_ball`
   with `Complex.IsExactOn.differentiableOn`. Applying
   `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected` therefore yields
   `DifferentiableOn.isExactOn_of_simplyConnected` (and Morera's counterpart
   `Complex.IsConservativeOn.isExactOn_of_simplyConnected`), extending Mathlib's disc primitive
   theorems to arbitrary simply connected open domains and open sets with simply connected
   components. Meanwhile `dx` (`Complex.reCLM`) is `ℝ`-linear rather than `ℂ`-linear
   (`TauCeti.ofRealCLM_comp_reCLM_ne_toSpanSingleton_restrictScalars`), so the real theory is
   strictly wider than the holomorphic case.
2. **The angular one-form and `dz / z` on the slit and punctured planes.** The planar angular form
   `TauCeti.angularForm` (`(x dy - y dx) / (x² + y²)`, equivalently `v ↦ Im (v / z)`) has the
   global potential `Complex.arg` on `Complex.slitPlane` and local potentials on `{0}ᶜ`, yet its
   continuous path integral around `TauCeti.unitCircleLoop` is `2π` (`4π` when traversed twice and
   `-2π` when reversed), obstructing any global potential on `{0}ᶜ`. Likewise `z ↦ z⁻¹` has loop
   integral `2πi` around `unitCircleLoop`, so `¬ Complex.IsExactOn (·⁻¹) {0}ᶜ`.
3. **Separating planar one-forms.** On every nonempty open set `s ⊆ ℂ`, the covector field
   `z ↦ z.re • Complex.imCLM` (`x dy`) fails to have local potentials
   (`TauCeti.not_hasLocalPotentials_re_smul_imCLM`), whereas `d(|Re z| ^ (3 / 2))` has a global `C¹`
   potential on `ℂ` despite not being `C¹` itself
   (`TauCeti.exists_hasLocalPotentials_not_contDiffOn`).

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, Sections 1.4 and 4.2 (primitives of
  holomorphic functions on simply connected domains and the period of `dz / z`).
* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, Section 2 (differential forms with local primitives, the angular form on `ℂ \ {0}`,
  and holomorphic primitives on simply connected domains).
-/

public section

open Set Metric Filter Complex
open scoped Topology ContDiff unitInterval

namespace TauCeti

/-! ### Holomorphic covector fields and primitives on simply connected domains -/

section Holomorphic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Having complex derivative `f'` at `z` is equivalent to having real Fréchet derivative
`(toSpanSingleton ℂ f').restrictScalars ℝ` (sending `v` to `v • f'`) at `z`. -/
theorem hasDerivAt_iff_hasFDerivAt_restrictScalars {g : ℂ → F} {z : ℂ} {f' : F} :
    HasDerivAt g f' z ↔
      HasFDerivAt g ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ) z :=
  ⟨fun h ↦ h.hasFDerivAt.restrictScalars ℝ,
    fun h ↦ hasDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_of_restrictScalars ℝ h rfl)⟩

/-- A holomorphic function `f : ℂ → F` into a complete complex normed space defines a covector field
`z ↦ (v ↦ v • f z)` carrying local potentials on every open set where `f` is holomorphic. -/
theorem _root_.DifferentiableOn.hasLocalPotentials [CompleteSpace F] {s : Set ℂ} {f : ℂ → F}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    HasLocalPotentials s
      (fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) := by
  rw [hasLocalPotentials_iff]
  intro z hz
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs z hz
  obtain ⟨g, hg⟩ := (hf.mono hrs).isExactOn_ball
  have hg_diff : DifferentiableOn ℂ g (ball z r) :=
    fun w hw ↦ (hg w hw).differentiableAt.differentiableWithinAt
  exact ⟨r, hr, hrs, g, (hg_diff.contDiffOn isOpen_ball).restrict_scalars ℝ,
    fun w hw ↦ (hg w hw).hasFDerivAt.restrictScalars ℝ⟩

/-- Conversely, if the `ℂ`-linear covector field `z ↦ (v ↦ v • f z)` has local potentials on `s`
and `F` is complete, then `f` is holomorphic on `s`. -/
theorem HasLocalPotentials.differentiableOn [CompleteSpace F] {s : Set ℂ} {f : ℂ → F}
    (h : HasLocalPotentials s
      (fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ)) :
    DifferentiableOn ℂ f s := by
  intro z hz
  obtain ⟨r, hr, -, g, -, hd⟩ := hasLocalPotentials_iff.mp h z hz
  have hex : Complex.IsExactOn f (ball z r) :=
    ⟨g, fun w hw ↦ hasDerivAt_iff_hasFDerivAt_restrictScalars.mpr (hd w hw)⟩
  exact ((hex.differentiableOn isOpen_ball).differentiableAt
    (ball_mem_nhds z hr)).differentiableWithinAt

/-- On an open subset `s ⊆ ℂ`, the `ℂ`-linear covector field `z ↦ (v ↦ v • f z)` into a complete
complex normed space has local potentials if and only if `f` is holomorphic on `s`. -/
theorem hasLocalPotentials_toSpanSingleton_iff [CompleteSpace F] {s : Set ℂ} {f : ℂ → F}
    (hs : IsOpen s) :
    HasLocalPotentials s
      (fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) ↔
    DifferentiableOn ℂ f s :=
  ⟨HasLocalPotentials.differentiableOn, fun hf ↦ hf.hasLocalPotentials hs⟩

/-- **Primitives of holomorphic functions on simply connected domains.** Every holomorphic function
`f : ℂ → F` on a simply connected open set `s ⊆ ℂ` with values in a complete complex normed space
admits a holomorphic primitive on `s` (`Complex.IsExactOn f s`). -/
theorem _root_.DifferentiableOn.isExactOn_of_simplyConnected [CompleteSpace F]
    {s : Set ℂ} [SimplyConnectedSpace s] {f : ℂ → F} (hf : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : Complex.IsExactOn f s := by
  obtain ⟨g, -, hd⟩ := (hf.hasLocalPotentials hs).exists_hasFDerivAt_of_simplyConnected
  exact ⟨g, fun z hz ↦ hasDerivAt_iff_hasFDerivAt_restrictScalars.mpr (hd z hz)⟩

/-- **Componentwise primitives of holomorphic functions.** Every holomorphic function `f : ℂ → F` on
an open set `s ⊆ ℂ` whose connected components are simply connected admits a complex primitive on
`s` when `F` is complete. -/
theorem _root_.DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    [CompleteSpace F] {s : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hcomp : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s := by
  obtain ⟨g, -, hd⟩ :=
    (hf.hasLocalPotentials hs).exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn hcomp
  exact ⟨g, fun z hz ↦ hasDerivAt_iff_hasFDerivAt_restrictScalars.mpr (hd z hz)⟩

/-- **Morera's theorem on simply connected domains.** A continuous function `f : ℂ → F` into a
complete complex normed space whose rectangle integrals vanish on a simply connected open set `s`
has a complex primitive on `s`. -/
theorem _root_.Complex.IsConservativeOn.isExactOn_of_simplyConnected [CompleteSpace F]
    {s : Set ℂ} [SimplyConnectedSpace s] {f : ℂ → F} (hcons : Complex.IsConservativeOn f s)
    (hs : IsOpen s) (hf : ContinuousOn f s) : Complex.IsExactOn f s := by
  have hdiff : DifferentiableOn ℂ f s := by
    intro z hz
    obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs z hz
    have hex : Complex.IsExactOn f (ball z r) :=
      (hcons.mono hrs).isExactOn_ball (hf.mono hrs)
    exact ((hex.differentiableOn isOpen_ball).differentiableAt
      (ball_mem_nhds z hr)).differentiableWithinAt
  exact hdiff.isExactOn_of_simplyConnected hs

/-- The real-part covector `dx` (viewed as `ℂ`-valued via `ofRealCLM ∘L reCLM`) is not of the
`ℂ`-linear form `(toSpanSingleton ℂ w).restrictScalars ℝ` for any `w : ℂ`. -/
theorem ofRealCLM_comp_reCLM_ne_toSpanSingleton_restrictScalars (w : ℂ) :
    Complex.ofRealCLM ∘L Complex.reCLM ≠
      (ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ := by
  intro h
  have h1 : (1 : ℂ) = w := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L 1) h
  have hI : (0 : ℂ) = Complex.I * w := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L Complex.I) h
  rw [← h1, mul_one] at hI
  exact Complex.I_ne_zero hI.symm

end Holomorphic

/-! ### The planar angular one-form, `dz / z`, and the unit circle loop -/

/-- The planar angular one-form `(x dy - y dx) / (x² + y²)` on `ℂ`, defined as the real-linear
covector `v ↦ Im (v / z)` (taking value `0` at `z = 0`). -/
noncomputable def angularForm (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM ∘L (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ

@[simp]
theorem angularForm_apply (z v : ℂ) : angularForm z v = (v / z).im := by
  simp [angularForm, div_eq_mul_inv]

@[simp]
theorem angularForm_zero : angularForm 0 = 0 := by
  ext v
  simp

/-- Real-coordinate expression `(x v_y - y v_x) / (x² + y²)` for `angularForm z v`. -/
theorem angularForm_apply_re_im (z v : ℂ) :
    angularForm z v = (z.re * v.im - z.im * v.re) / (z.re ^ 2 + z.im ^ 2) := by
  rw [angularForm_apply, Complex.div_im, Complex.normSq_apply]
  ring

/-- On `Complex.slitPlane`, the principal argument `Complex.arg` has Fréchet derivative
`angularForm z` at every `z`. -/
theorem hasFDerivAt_arg {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasFDerivAt Complex.arg (angularForm z) z := by
  have h := (hasDerivAt_id z).hasFDerivAt_arg hz
  simpa only [id_eq, one_div, angularForm] using HasFDerivAt.of_isLittleO h.isLittleO

/-- On `Complex.slitPlane`, `angularForm` has local potentials (witnessed globally by
`Complex.arg`). -/
theorem hasLocalPotentials_angularForm_slitPlane :
    HasLocalPotentials Complex.slitPlane angularForm :=
  hasLocalPotentials_of_hasFDerivAt Complex.isOpen_slitPlane
    (fun _ hz ↦ (Complex.contDiffAt_arg hz).contDiffWithinAt) fun _ hz ↦ hasFDerivAt_arg hz

/-- On the punctured plane `{0}ᶜ`, `angularForm` has local potentials, covered by the branches
`Complex.arg` on `slitPlane` and `z ↦ Complex.arg (-z)` on `-slitPlane`. -/
theorem hasLocalPotentials_angularForm_compl_zero :
    HasLocalPotentials ({0}ᶜ : Set ℂ) angularForm := by
  have hneg : HasLocalPotentials (Neg.neg ⁻¹' Complex.slitPlane) angularForm := by
    refine hasLocalPotentials_of_hasFDerivAt
      (Complex.isOpen_slitPlane.preimage continuous_neg)
      (fun z hz ↦ ((Complex.contDiffAt_arg hz).comp z contDiff_neg.contDiffAt).contDiffWithinAt)
      fun z hz ↦ ?_
    have hd := (hasFDerivAt_arg hz).comp z (hasFDerivAt_id z).neg
    have hclm : angularForm (-z) ∘L (-ContinuousLinearMap.id ℝ ℂ) = angularForm z := by
      ext v
      simp [div_neg]
    rwa [hclm] at hd
  have hcov : ({0}ᶜ : Set ℂ) = ⋃ b : Bool, cond b Complex.slitPlane
      (Neg.neg ⁻¹' Complex.slitPlane) := by
    ext z
    simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, Bool.exists_bool, Bool.cond_false,
      Bool.cond_true, mem_preimage]
    exact ⟨fun hz ↦ (Complex.mem_slitPlane_or_neg_mem_slitPlane hz).symm,
      by rintro (hz | hz); exacts [fun h ↦ Complex.slitPlane_ne_zero hz (by simp [h]),
        Complex.slitPlane_ne_zero hz]⟩
  rw [hcov]
  exact hasLocalPotentials_iUnion fun b ↦ by
    cases b <;> [exact hneg; exact hasLocalPotentials_angularForm_slitPlane]

/-- The standard counterclockwise unit circle loop `t ↦ exp (2πi t)` based at `1 : ℂ`. -/
noncomputable def unitCircleLoop : Path (1 : ℂ) 1 where
  toFun t := Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Icc.coe_one, mul_one, ofReal_mul, ofReal_ofNat]
    exact Complex.exp_two_pi_mul_I

@[simp]
theorem unitCircleLoop_apply (t : I) :
    unitCircleLoop t = Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I) := by
  rfl

theorem unitCircleLoop_ne_zero (t : I) : unitCircleLoop t ≠ 0 :=
  Complex.exp_ne_zero _

/-- Pulling a covector field `φ` with local potentials on `{0}ᶜ` back along the angular map
`θ ↦ exp (θ * I)` expresses its integral around `unitCircleLoop` as a continuous path integral
along `Path.segment (0 : ℝ) (2 * Real.pi)`. -/
theorem HasLocalPotentials.localPotentialIntegral_unitCircleLoop {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℂ → ℂ →L[ℝ] F}
    (hφ : HasLocalPotentials ({0}ᶜ : Set ℂ) φ) :
    localPotentialIntegral φ unitCircleLoop =
      localPotentialIntegral
        (fun θ : ℝ ↦ (φ (Complex.exp ((θ : ℂ) * Complex.I))).comp
          (ContinuousLinearMap.toSpanSingleton ℝ
            (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)))
        (Path.segment (0 : ℝ) (2 * Real.pi)) := by
  let f : ℝ → ℂ := fun θ ↦ Complex.exp (Complex.ofRealCLM θ * Complex.I)
  have hf_contDiff : ContDiff ℝ 1 f :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hf_fderiv : ∀ θ : ℝ,
      fderiv ℝ f θ = ContinuousLinearMap.toSpanSingleton ℝ (f θ * Complex.I) := fun θ ↦ by
    have hd : HasDerivAt f (f θ * Complex.I) θ := by
      simpa [f] using (((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp
    exact hd.hasFDerivAt.fderiv
  have h0 : (1 : ℂ) = f 0 := by simp [f]
  have h1 : (1 : ℂ) = f (2 * Real.pi) := by
    simp only [f, Complex.ofRealCLM_apply, ofReal_mul, ofReal_ofNat]
    exact Complex.exp_two_pi_mul_I.symm
  have hcast : ((Path.segment (0 : ℝ) (2 * Real.pi)).map hf_contDiff.continuous).cast h0 h1 =
      unitCircleLoop := by
    ext t
    have hlhs : (((Path.segment (0 : ℝ) (2 * Real.pi)).map hf_contDiff.continuous).cast h0 h1) t =
        f (Path.segment (0 : ℝ) (2 * Real.pi) t) := rfl
    rw [hlhs]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul,
      unitCircleLoop_apply, f, Complex.ofRealCLM_apply]
    congr 1
    push_cast
    ring
  rw [← hcast, localPotentialIntegral_cast,
    ← hφ.localPotentialIntegral_pullback_map hf_contDiff (fun _ ↦ Complex.exp_ne_zero _)]
  congr 1
  funext θ
  rw [hf_fderiv θ]
  simp [f]

/-- The continuous path integral of `angularForm` once around `unitCircleLoop` is `2π`. -/
theorem localPotentialIntegral_angularForm_unitCircleLoop :
    localPotentialIntegral angularForm unitCircleLoop = 2 * Real.pi := by
  rw [hasLocalPotentials_angularForm_compl_zero.localPotentialIntegral_unitCircleLoop]
  have hpull : (fun θ : ℝ ↦ (angularForm (Complex.exp ((θ : ℂ) * Complex.I))).comp
      (ContinuousLinearMap.toSpanSingleton ℝ
        (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) =
      fun _ ↦ ContinuousLinearMap.id ℝ ℝ := by
    funext θ
    apply ContinuousLinearMap.ext_ring
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      angularForm_apply, ContinuousLinearMap.id_apply]
    rw [mul_comm, mul_div_cancel_right₀ _ hne, Complex.I_im]
  rw [hpull, localPotentialIntegral_const]
  simp

/-- Traversing `unitCircleLoop` twice gives continuous path integral `4π`. -/
theorem localPotentialIntegral_angularForm_unitCircleLoop_trans :
    localPotentialIntegral angularForm (unitCircleLoop.trans unitCircleLoop) = 4 * Real.pi := by
  rw [hasLocalPotentials_angularForm_compl_zero.localPotentialIntegral_trans
    unitCircleLoop_ne_zero unitCircleLoop_ne_zero,
    localPotentialIntegral_angularForm_unitCircleLoop]
  ring

/-- Reversing `unitCircleLoop` negates the continuous path integral to `-2π`. -/
theorem localPotentialIntegral_angularForm_unitCircleLoop_symm :
    localPotentialIntegral angularForm unitCircleLoop.symm = -(2 * Real.pi) := by
  rw [localPotentialIntegral_symm, localPotentialIntegral_angularForm_unitCircleLoop]

/-- On the punctured plane `{0}ᶜ`, `angularForm` admits no global potential, because its integral
around `unitCircleLoop` is `2π ≠ 0`. -/
theorem not_exists_hasFDerivAt_angularForm_compl_zero :
    ¬ ∃ g : ℂ → ℝ, ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivAt g (angularForm z) z := by
  rintro ⟨g, hd⟩
  have h0 : localPotentialIntegral angularForm unitCircleLoop = 0 := by
    rw [hasLocalPotentials_angularForm_compl_zero.localPotentialIntegral_eq_sub_of_hasFDerivAt hd
      unitCircleLoop_ne_zero, sub_self]
  rw [localPotentialIntegral_angularForm_unitCircleLoop] at h0
  exact Real.two_pi_pos.ne' h0

/-- The holomorphic covector field `dz / z` (`v ↦ v * z⁻¹`) has local potentials on `{0}ᶜ`. -/
theorem hasLocalPotentials_inv_compl_zero :
    HasLocalPotentials ({0}ᶜ : Set ℂ)
      (fun z : ℂ ↦ (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ) :=
  (differentiableOn_inv.mono (subset_refl _)).hasLocalPotentials isOpen_compl_singleton

/-- The holomorphic covector field `dz / z` (`v ↦ v * z⁻¹`) has continuous path integral `2πi`
around `unitCircleLoop`. -/
theorem localPotentialIntegral_inv_unitCircleLoop :
    localPotentialIntegral
      (fun z : ℂ ↦ (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)
      unitCircleLoop = (2 * Real.pi : ℂ) * Complex.I := by
  rw [hasLocalPotentials_inv_compl_zero.localPotentialIntegral_unitCircleLoop]
  have hpull : (fun θ : ℝ ↦
      ((ContinuousLinearMap.toSpanSingleton ℂ
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹).restrictScalars ℝ).comp
        (ContinuousLinearMap.toSpanSingleton ℝ
          (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) =
      fun _ ↦ ContinuousLinearMap.toSpanSingleton ℝ Complex.I := by
    funext θ
    apply ContinuousLinearMap.ext_ring
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul]
    rw [mul_comm _ Complex.I, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [hpull, localPotentialIntegral_const]
  simp [Complex.real_smul]

/-- The reciprocal `z ↦ z⁻¹` has no holomorphic primitive on the punctured plane `{0}ᶜ`, because
`dz / z` has loop integral `2πi ≠ 0` around `unitCircleLoop`. -/
theorem _root_.Complex.not_isExactOn_inv_compl_zero :
    ¬ Complex.IsExactOn (·⁻¹ : ℂ → ℂ) ({0}ᶜ : Set ℂ) := by
  rintro ⟨g, hg⟩
  have hd : ∀ z ∈ ({0}ᶜ : Set ℂ),
      HasFDerivAt g ((ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ) z :=
    fun z hz ↦ (hg z hz).hasFDerivAt.restrictScalars ℝ
  have h0 : localPotentialIntegral
      (fun z : ℂ ↦ (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)
      unitCircleLoop = 0 := by
    rw [hasLocalPotentials_inv_compl_zero.localPotentialIntegral_eq_sub_of_hasFDerivAt hd
      unitCircleLoop_ne_zero, sub_self]
  rw [localPotentialIntegral_inv_unitCircleLoop] at h0
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero h0

/-! ### Separating witnesses for `HasLocalPotentials` on `ℂ` -/

/-- On any nonempty domain `s ⊆ ℂ`, the one-form `x dy` (`z ↦ z.re • Complex.imCLM`) has no local
potentials. -/
theorem not_hasLocalPotentials_re_smul_imCLM {s : Set ℂ} (hs : s.Nonempty) :
    ¬ HasLocalPotentials s (fun z : ℂ ↦ z.re • Complex.imCLM) := by
  -- Around a small axis-aligned square of side `δ` in a hypothetical potential ball, a potential
  -- has horizontal increments `0` and unequal vertical increments `z₀.re * δ` and
  -- `(z₀.re + δ) * δ`.
  obtain ⟨z₀, hz₀⟩ := hs
  intro hφ
  obtain ⟨r, hr, -, g, -, hd⟩ := hasLocalPotentials_iff.mp hφ z₀ hz₀
  let δ : ℝ := r / 4
  have hδ : 0 < δ := by positivity
  -- Helper evaluating `g (a + δ • u) - g a` along an axis-aligned segment in `ball z₀ r`.
  have hseg : ∀ (a u : ℂ), ‖a - z₀‖ ≤ δ → ‖u‖ = 1 →
      (∀ t : ℝ, ((a + (t : ℂ) * u).re • Complex.imCLM) u = (a.re * u.im : ℝ)) →
      g (a + (δ : ℂ) * u) - g a = a.re * u.im * δ := by
    intro a u ha hu hval
    let U : Set ℝ := Ioo (-δ) (2 * δ)
    have hmem_ball : ∀ t ∈ U, a + (t : ℂ) * u ∈ ball z₀ r := by
      intro t ht
      rw [mem_ball, dist_eq_norm, show a + (t : ℂ) * u - z₀ = (a - z₀) + (t : ℂ) * u by ring]
      have ht_abs : |t| < 2 * δ := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      calc
        ‖(a - z₀) + (t : ℂ) * u‖ ≤ ‖a - z₀‖ + ‖(t : ℂ) * u‖ := norm_add_le _ _
        _ = ‖a - z₀‖ + |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one]
        _ < δ + 2 * δ := by linarith
        _ < r := by dsimp [δ]; linarith
    have hd₁ : ∀ t ∈ U, HasFDerivAt (fun s : ℝ ↦ g (a + (s : ℂ) * u))
        (ContinuousLinearMap.toSpanSingleton ℝ (a.re * u.im)) t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ ↦ a + (s : ℂ) * u) u t := by
        simpa using (((hasDerivAt_id t).ofReal_comp).mul_const u).const_add a
      have hcomp := (hd _ (hmem_ball t ht)).comp_hasDerivAt t hlin
      rw [hval t] at hcomp
      simpa only [Function.comp_def] using hcomp.hasFDerivAt
    have hd₂ : ∀ t ∈ U, HasFDerivAt (fun s : ℝ ↦ a.re * u.im * s)
        (ContinuousLinearMap.toSpanSingleton ℝ (a.re * u.im)) t := fun t _ ↦ by
      have h := (hasDerivAt_id t).const_mul (a.re * u.im)
      rw [mul_one] at h
      exact h.hasFDerivAt
    have hsub := sub_eq_sub_of_hasFDerivAt_of_isPreconnected isOpen_Ioo
      (convex_Ioo _ _).isPreconnected hd₁ hd₂ (p := 0) (q := δ)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    simpa using hsub
  have h_bot : g (z₀ + (δ : ℂ) * 1) - g z₀ = 0 := by
    simpa using hseg z₀ 1 (by simp [hδ.le]) norm_one (fun t ↦ by simp)
  have h_top : g ((z₀ + (δ : ℂ) * Complex.I) + (δ : ℂ) * 1) - g (z₀ + (δ : ℂ) * Complex.I) = 0 := by
    refine (hseg (z₀ + (δ : ℂ) * Complex.I) 1 ?_ norm_one (fun t ↦ by simp)).trans (by simp)
    simp [Complex.norm_real, abs_of_pos hδ]
  have h_left : g (z₀ + (δ : ℂ) * Complex.I) - g z₀ = z₀.re * δ := by
    simpa using hseg z₀ Complex.I (by simp [hδ.le]) Complex.norm_I (fun t ↦ by simp)
  have h_right : g ((z₀ + (δ : ℂ) * 1) + (δ : ℂ) * Complex.I) - g (z₀ + (δ : ℂ) * 1) =
      (z₀.re + δ) * δ := by
    have := hseg (z₀ + (δ : ℂ) * 1) Complex.I
      (by simp [Complex.norm_real, abs_of_pos hδ]) Complex.norm_I (fun t ↦ by simp)
    simpa using this
  have hcorner : (z₀ + (δ : ℂ) * Complex.I) + (δ : ℂ) * 1 =
      (z₀ + (δ : ℂ) * 1) + (δ : ℂ) * Complex.I := by ring
  rw [hcorner] at h_top
  have hsq : δ * δ = 0 := by linarith
  exact (mul_ne_zero hδ.ne' hδ.ne') hsq

/-- **A continuous non-`C¹` one-form with local potentials.** The covector field
`φ = d(|Re z| ^ (3 / 2))` on `ℂ` has a global `C¹` potential (`z ↦ |Re z| ^ (3 / 2)`), hence
satisfies `HasLocalPotentials univ φ`, yet `φ` is not `C¹` on `ℂ` (it fails to be differentiable at
`0`). Thus `HasLocalPotentials` is strictly weaker than being a closed `C¹` one-form. -/
theorem exists_hasLocalPotentials_not_contDiffOn :
    ∃ φ : ℂ → ℂ →L[ℝ] ℝ, HasLocalPotentials univ φ ∧ ¬ ContDiffOn ℝ 1 φ univ := by
  -- Use `g₀ x = x ^ (3 / 2) + (-x) ^ (3 / 2) = |x| ^ (3 / 2)` on `ℝ` (`cos (3π/2) = 0`).
  let g₀ : ℝ → ℝ := fun x ↦ x ^ ((3 : ℝ) / 2) + (-x) ^ ((3 : ℝ) / 2)
  let g₀' : ℝ → ℝ := fun x ↦ (3 / 2 : ℝ) * (x ^ ((1 : ℝ) / 2) - (-x) ^ ((1 : ℝ) / 2))
  let φ : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ g₀' z.re • Complex.reCLM
  have hg₀_contDiff : ContDiff ℝ 1 g₀ :=
    (Real.contDiff_rpow_const_of_le (by norm_num)).add
      ((Real.contDiff_rpow_const_of_le (by norm_num)).comp contDiff_neg)
  have hg₀_deriv : ∀ x : ℝ, HasDerivAt g₀ (g₀' x) x := by
    intro x
    have h₁ : HasDerivAt (fun y : ℝ ↦ y ^ ((3 : ℝ) / 2))
        ((3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2)) x := by
      simpa [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num] using
        Real.hasDerivAt_rpow_const (x := x) (p := (3 : ℝ) / 2) (Or.inr (by norm_num))
    have h₂ : HasDerivAt (fun y : ℝ ↦ (-y) ^ ((3 : ℝ) / 2))
        (-((3 / 2 : ℝ) * (-x) ^ ((1 : ℝ) / 2))) x := by
      have h := HasDerivAt.comp x
        (Real.hasDerivAt_rpow_const (x := -x) (p := (3 : ℝ) / 2) (Or.inr (by norm_num)))
        (hasDerivAt_id x).neg
      simpa only [Function.comp_def, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num, mul_neg,
        mul_one] using h
    have hsum := h₁.add h₂
    have heq : (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2) + -((3 / 2 : ℝ) * (-x) ^ ((1 : ℝ) / 2)) =
        g₀' x := by dsimp [g₀']; ring
    rw [heq] at hsum
    exact hsum
  have hφ_pot : HasLocalPotentials univ φ := by
    refine hasLocalPotentials_of_hasFDerivAt isOpen_univ
      (hg₀_contDiff.comp Complex.reCLM.contDiff).contDiffOn fun z _ ↦ ?_
    have hcomp := (hg₀_deriv z.re).hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
    have hclm : ContinuousLinearMap.toSpanSingleton ℝ (g₀' z.re) ∘L Complex.reCLM = φ z := by
      ext v
      simp [φ, mul_comm]
    rwa [hclm] at hcomp
  refine ⟨φ, hφ_pot, fun hcont ↦ ?_⟩
  have hdiff_φ : DifferentiableAt ℝ φ 0 :=
    (hcont.differentiableOn one_ne_zero 0 (mem_univ 0)).differentiableAt Filter.univ_mem
  have hdiff_g₀' : DifferentiableAt ℝ g₀' 0 := by
    have hcomp : DifferentiableAt ℝ (φ ∘ Complex.ofRealCLM) 0 :=
      DifferentiableAt.comp 0 (by simpa using hdiff_φ) Complex.ofRealCLM.differentiableAt
    have heval : DifferentiableAt ℝ ((ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)) ∘
        (φ ∘ Complex.ofRealCLM)) 0 :=
      DifferentiableAt.comp 0 (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).differentiableAt hcomp
    simpa [Function.comp_def, φ] using heval
  -- Precomposing `g₀'` with `t ↦ t ^ 2` at `0` gives derivative `0`, yet on `Ici 0` it equals
  -- `(3 / 2) * t`.
  have hzero : HasDerivWithinAt (fun t : ℝ ↦ g₀' (t ^ 2)) 0 (Ici 0) 0 := by
    let sqFun : ℝ → ℝ := fun t ↦ t ^ 2
    have hsq : HasDerivAt sqFun 0 0 := by simpa [sqFun] using hasDerivAt_pow 2 (0 : ℝ)
    have hd0 : HasDerivAt g₀' (deriv g₀' 0) (sqFun 0) := by
      simpa [sqFun] using hdiff_g₀'.hasDerivAt
    simpa [Function.comp_def, sqFun] using (HasDerivAt.comp (0 : ℝ) hd0 hsq).hasDerivWithinAt
  have heq_Ici : EqOn (fun t : ℝ ↦ (3 / 2 : ℝ) * t) (fun t : ℝ ↦ g₀' (t ^ 2)) (Ici 0) := by
    intro t (ht : 0 ≤ t)
    dsimp [g₀']
    have hneg_zero : (-(t ^ 2)) ^ ((1 : ℝ) / 2) = 0 := by
      rcases ht.eq_or_lt with rfl | ht_pos
      · norm_num
      · have hneg : -(t ^ 2) < 0 := neg_lt_zero.mpr (sq_pos_of_pos ht_pos)
        rw [Real.rpow_def_of_neg hneg, show (1 : ℝ) / 2 * Real.pi = Real.pi / 2 by ring,
          Real.cos_pi_div_two, mul_zero]
    have hpos : (t ^ 2) ^ ((1 : ℝ) / 2) = t := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
      norm_num
    rw [hneg_zero, hpos, sub_zero]
  have hlin : HasDerivWithinAt (fun t : ℝ ↦ (3 / 2 : ℝ) * t) 0 (Ici 0) 0 :=
    hzero.congr heq_Ici (heq_Ici (le_rfl : (0 : ℝ) ≤ 0))
  have hlin' : HasDerivWithinAt (fun t : ℝ ↦ (3 / 2 : ℝ) * t) (3 / 2) (Ici 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (3 / 2 : ℝ)).hasDerivWithinAt
  have h032 : (0 : ℝ) = 3 / 2 :=
    UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici 0) hlin hlin'
  norm_num at h032

end TauCeti
