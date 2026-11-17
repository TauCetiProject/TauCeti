/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Complex.HasPrimitives
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ContinuousPath
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.XDy
public import TauCeti.Topology.Circle.Loop
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Planar examples and checks for local primitives and continuous path integrals

This file collects the canonical low-dimensional examples separating the classes of `1`-forms
with local primitives, closed `C¹` `1`-forms, exact `1`-forms, and holomorphic differentials:

* **Constant `dx` on `ℂ` (`TauCeti.complexDx`)**: nonzero with global primitive `Complex.re`,
  unique up to an additive constant (`TauCeti.isPrimitiveOn_complexDx_univ_iff`), integrating to
  `b.re - a.re` along every continuous path — including graphs of arbitrary continuous (possibly
  nowhere-differentiable) functions — and illustrated on an explicit subdivision with different
  local primitives (`TauCeti.continuousPathIntegral_complexDx_subdivision_example`).
* **Non-closed `x dy` on `ℝ × ℝ`**: admits no local primitive on any nonempty open set
  (`TauCeti.not_isPrimitiveOn_realPlaneXDy`), by symmetry of second derivatives.
* **Angular form `dθ = (x dy - y dx) / (x² + y²)` on `ℂ \ {0}`
  (`TauCeti.puncturedPlaneAngularForm`, `TauCeti.puncturedPlaneAngularFormRestricted`)**: smooth
  and closed, with global primitive `Complex.arg` on `Complex.slitPlane` and local primitives on
  `ℂ \ {0}`, pulling back to `TauCeti.circleAngularForm` on `Circle`. Its integral around the unit
  circle loop is `2π` — agreeing with Mathlib's `curveIntegral` and with `TauCeti.periodHom` —
  with double traversal `4π` and reversal `-2π`, showing that neither
  `TauCeti.puncturedPlaneAngularFormRestricted` on `ℂ \ {0}` nor `TauCeti.circleAngularForm` on
  `Circle` has a global primitive.
* **Holomorphic `dz / z`**: exact on `Complex.slitPlane` (`TauCeti.isExactOn_inv_slitPlane`), with
  loop integral `2πi` around the unit circle, hence not exact on `ℂ \ {0}`
  (`TauCeti.not_isExactOn_inv_compl_zero`).
* **Non-`C¹` form `d(|x|^(3/2))` on `ℝ × ℝ` (`TauCeti.absRpowThreeHalvesForm`)**: has global
  primitive `(x, y) ↦ |x|^(3/2)` (unique up to a constant), is not `C¹`, integrates to `1` along
  `(0, 0) → (1, 0)` and `0` along `(-1, 0) → (1, 0)`, while `TauCeti.pathClassIntegral` returns
  its default value `0` on `(0, 0) → (1, 0)`.
* **Discontinuous form `d(x² sin(1/x))` on `ℝ` (`TauCeti.xSqSinInvForm`)**: has global primitive
  `x ↦ x² sin(1/x)` (extended by `0` at `0`), yet is not continuous at `0`, and still integrates
  nontrivially via `TauCeti.continuousPathIntegral` while `TauCeti.pathClassIntegral` returns `0`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (line integrals and
  conservative covector fields) and Chapter 17 (the angular form on the punctured plane).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, Sections 2.1, 4.4, and 4.6 (the period
  and index of `dz / z` and primitives of holomorphic functions).
-/

public section

noncomputable section

open Set Filter Metric Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Constant `dx` on `ℂ` -/

section ComplexDx

/-- The constant real-valued `1`-form `dx` (`v ↦ v.re`) on the real manifold `ℂ`. -/
def complexDx : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  fun _ ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) Complex.reCLM

/-- Evaluating `complexDx` on a tangent vector reads off its real part. -/
@[simp]
theorem complexDx_apply (z : ℂ) (v : Fin 1 → ℂ) :
    complexDx z v = (v 0).re :=
  (rfl)

/-- The constant form `dx` on `ℂ` is nonzero. -/
theorem complexDx_ne_zero : complexDx ≠ 0 := by
  intro h
  have h1 : complexDx 0 ![(1 : ℂ)] = 0 :=
    RoughForm.mem_ker.mp ((RoughForm.ker_eq_top_iff.mpr (congrFun h 0)).symm ▸ Submodule.mem_top)
  have h2 := (complexDx_apply 0 ![(1 : ℂ)]).symm.trans h1
  simp at h2

/-- `Complex.re` is a global primitive of `complexDx` on `ℂ`. -/
theorem isPrimitiveOn_complexDx_re : IsPrimitiveOn complexDx Complex.re univ := by
  unfold complexDx
  rw [isPrimitiveOn_ofSubsingleton_iff]
  exact ⟨isOpen_univ, fun _ _ ↦ Complex.reCLM.hasFDerivAt⟩

/-- Every point of `ℂ` has a local primitive for `complexDx`. -/
theorem forall_exists_isPrimitiveOn_complexDx (z : ℂ) :
    ∃ (g : ℂ → ℝ) (U : Set ℂ), z ∈ U ∧ IsPrimitiveOn complexDx g U :=
  ⟨Complex.re, univ, mem_univ z, isPrimitiveOn_complexDx_re⟩

/-- The global primitives of `complexDx` on `ℂ` are precisely the translates `z ↦ z.re + c`. -/
theorem isPrimitiveOn_complexDx_univ_iff {g : ℂ → ℝ} :
    IsPrimitiveOn complexDx g univ ↔ ∃ c : ℝ, g = fun z ↦ z.re + c := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hg.exists_eq_add_const isPrimitiveOn_complexDx_re
    exact ⟨c, funext hc⟩
  · rintro ⟨c, rfl⟩
    exact isPrimitiveOn_complexDx_re.add_const c

/-- The continuous path integral of `dx` along any continuous path `γ` from `a` to `b` in `ℂ`
equals `b.re - a.re`. -/
theorem continuousPathIntegral_complexDx {a b : ℂ} (γ : Path a b) :
    continuousPathIntegral complexDx γ = b.re - a.re :=
  continuousPathIntegral_eq_sub_of_isPrimitiveOn forall_exists_isPrimitiveOn_complexDx
    isPrimitiveOn_complexDx_re γ (fun _ ↦ mem_univ _)

/-- The continuous path integral of `dx` along the graph `t ↦ t + i W(t)` of any continuous
function `W : ℝ → ℝ` with `W 0 = 0` and `W 1 = 0` equals `1`, even when `W` is nowhere
differentiable. -/
theorem continuousPathIntegral_complexDx_graph {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    continuousPathIntegral complexDx
        ({ toFun := fun t : unitInterval ↦ ((t : ℝ) : ℂ) + (W t : ℂ) * Complex.I
           continuous_toFun :=
             (Complex.continuous_ofReal.comp continuous_subtype_val).add
               ((Complex.continuous_ofReal.comp (hW.comp continuous_subtype_val)).mul
                 continuous_const)
           source' := by simp [hW0]
           target' := by simp [hW1] } : Path (0 : ℂ) 1) = 1 := by
  rw [continuousPathIntegral_complexDx]
  simp

/-- Subdivision check for `dx` along the segment from `0` to `3` in `ℂ`, split at `1` (`t = 1/3`)
with local primitives `Re` on the first piece and `Re + 7` on the second: both the subdivision
sum and the continuous path integral equal `3`. -/
theorem continuousPathIntegral_complexDx_subdivision_example :
    let γ : Path (0 : ℂ) 3 :=
      { toFun := fun t : unitInterval ↦ ((3 * (t : ℝ) : ℝ) : ℂ)
        continuous_toFun :=
          Complex.continuous_ofReal.comp (continuous_const.mul continuous_subtype_val)
        source' := by simp
        target' := by simp }
    let t : Fin 3 → unitInterval :=
      ![0, ⟨(1 : ℝ) / 3, by norm_num, by norm_num⟩, 1]
    let g : Fin 2 → ℂ → ℝ := ![Complex.re, fun z ↦ z.re + 7]
    continuousPathIntegral complexDx γ =
        ∑ i : Fin 2, (g i (γ (t i.succ)) - g i (γ (t i.castSucc))) ∧
      continuousPathIntegral complexDx γ = 3 := by
  intro γ t g
  have hsum : continuousPathIntegral complexDx γ =
      ∑ i : Fin 2, (g i (γ (t i.succ)) - g i (γ (t i.castSucc))) := by
    refine continuousPathIntegral_eq_sum_sub_of_subdivision forall_exists_isPrimitiveOn_complexDx γ
      (n := 2) (t := t) rfl rfl (g := g) (U := fun _ ↦ univ) (fun i ↦ ?_) (fun _ _ _ ↦ mem_univ _)
    fin_cases i
    · exact isPrimitiveOn_complexDx_re
    · exact isPrimitiveOn_complexDx_re.add_const 7
  refine ⟨hsum, ?_⟩
  rw [continuousPathIntegral_complexDx]
  norm_num

end ComplexDx

/-! ### `x dy` on `ℝ × ℝ` has no local primitives -/

section RealPlaneXDy

/-- The smooth `1`-form `x dy` on `ℝ × ℝ` has no primitive on any open set containing a point. -/
theorem not_isPrimitiveOn_realPlaneXDy {g : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ U) :
    ¬ IsPrimitiveOn (I := 𝓘(ℝ, ℝ × ℝ))
      ((fun q ↦ _root_.Prod.realPlaneXDy q) : RoughForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ℝ 1) g U := by
  intro hg
  let α : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q ↦ q.1 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hform : ((fun q ↦ _root_.Prod.realPlaneXDy q) : RoughForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ℝ 1) =
      fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1) (α q) := by
    funext q; ext v; simp [α]
  rw [hform] at hg
  have hα : HasFDerivAt α
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hsym := hg.hasFDerivAt_symm hp hα (1, 0) (0, 1)
  norm_num at hsym

end RealPlaneXDy

/-! ### The punctured-plane angular form and `dz / z` -/

section PuncturedPlane

attribute [local instance] finrank_real_complex_fact'

/-- The punctured plane `ℂ \ {0}` as an open submanifold of `ℂ`. -/
def puncturedPlane : TopologicalSpace.Opens ℂ :=
  ⟨({0} : Set ℂ)ᶜ, isOpen_compl_singleton⟩

@[simp]
theorem coe_puncturedPlane : (puncturedPlane : Set ℂ) = ({0} : Set ℂ)ᶜ :=
  (rfl)

@[simp]
theorem mem_puncturedPlane_iff {z : ℂ} : z ∈ puncturedPlane ↔ z ≠ 0 :=
  Iff.rfl

/-- The basepoint `1` in the punctured plane `ℂ \ {0}`. -/
def puncturedPlaneOne : puncturedPlane :=
  ⟨1, mem_puncturedPlane_iff.mpr one_ne_zero⟩

@[simp]
theorem coe_puncturedPlaneOne : (puncturedPlaneOne : ℂ) = 1 :=
  (rfl)

/-- The covector field `z ↦ (v ↦ Im (v / z))` on `ℂ`, representing `(x dy - y dx) / (x² + y²)`
away from `0` (and `0` at `0`). -/
def puncturedPlaneAngularCovector (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ (1 / z)).restrictScalars ℝ)

/-- Operator-level unfolding of `puncturedPlaneAngularCovector`. -/
theorem puncturedPlaneAngularCovector_def (z : ℂ) :
    puncturedPlaneAngularCovector z =
      Complex.imCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ (1 / z)).restrictScalars ℝ) :=
  (rfl)

@[simp]
theorem puncturedPlaneAngularCovector_apply (z v : ℂ) :
    puncturedPlaneAngularCovector z v = (v / z).im := by
  simp [puncturedPlaneAngularCovector, div_eq_mul_inv]

@[simp]
theorem puncturedPlaneAngularCovector_zero : puncturedPlaneAngularCovector 0 = 0 := by
  ext v
  simp

/-- In Cartesian coordinates, `puncturedPlaneAngularCovector z v = (x v_y - y v_x) / (x² + y²)`. -/
theorem puncturedPlaneAngularCovector_apply_re_im (z v : ℂ) :
    puncturedPlaneAngularCovector z v = (z.re * v.im - z.im * v.re) / (z.re ^ 2 + z.im ^ 2) := by
  simp only [puncturedPlaneAngularCovector_apply, Complex.div_im, Complex.normSq_apply, sq]
  ring

/-- The angular `1`-form `(x dy - y dx) / (x² + y²)` on `ℂ` (totalized to `0` at `0`). -/
def puncturedPlaneAngularForm : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
    (puncturedPlaneAngularCovector z)

@[simp]
theorem puncturedPlaneAngularForm_apply (z : ℂ) (v : Fin 1 → ℂ) :
    puncturedPlaneAngularForm z v = (v 0 / z).im :=
  puncturedPlaneAngularCovector_apply z (v 0)

@[simp]
theorem puncturedPlaneAngularForm_zero : puncturedPlaneAngularForm 0 = 0 := by
  rw [← RoughForm.ker_eq_top_iff, eq_top_iff]
  intro v _
  rw [RoughForm.mem_ker]
  let w : ℂ := v
  exact (puncturedPlaneAngularForm_apply 0 ![w]).trans (by simp)

/-- The angular `1`-form restricted to the punctured plane `ℂ \ {0}`. -/
def puncturedPlaneAngularFormRestricted : RoughForm 𝓘(ℝ, ℂ) puncturedPlane ℝ 1 :=
  mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) puncturedPlaneAngularForm

/-- On the slit plane `ℂ \ (-∞, 0]`, `Complex.arg` is a global primitive of the angular form. -/
theorem isPrimitiveOn_puncturedPlaneAngularForm_arg :
    IsPrimitiveOn puncturedPlaneAngularForm Complex.arg Complex.slitPlane := by
  unfold puncturedPlaneAngularForm
  rw [isPrimitiveOn_ofSubsingleton_iff]
  exact ⟨Complex.isOpen_slitPlane, fun z hz ↦ (hasDerivAt_id z).hasFDerivAt_arg hz⟩

/-- On the opposite slit plane `(- ·) ⁻¹' Complex.slitPlane`, `z ↦ Complex.arg (-z)` is a primitive
of the angular form. -/
theorem isPrimitiveOn_puncturedPlaneAngularForm_arg_neg :
    IsPrimitiveOn puncturedPlaneAngularForm (fun z ↦ Complex.arg (-z))
      (Neg.neg ⁻¹' Complex.slitPlane) := by
  unfold puncturedPlaneAngularForm
  rw [isPrimitiveOn_ofSubsingleton_iff]
  refine ⟨Complex.isOpen_slitPlane.preimage continuous_neg, fun z hz ↦ ?_⟩
  have h := (hasDerivAt_neg z).hasFDerivAt_arg hz
  simpa [puncturedPlaneAngularCovector] using h

/-- Away from `0`, the angular form has local primitives (branches of `arg`). -/
theorem forall_exists_isPrimitiveOn_puncturedPlaneAngularForm {z : ℂ} (hz : z ≠ 0) :
    ∃ (g : ℂ → ℝ) (U : Set ℂ), z ∈ U ∧ IsPrimitiveOn puncturedPlaneAngularForm g U := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · exact ⟨Complex.arg, Complex.slitPlane, h, isPrimitiveOn_puncturedPlaneAngularForm_arg⟩
  · exact ⟨fun w ↦ Complex.arg (-w), Neg.neg ⁻¹' Complex.slitPlane, h,
      isPrimitiveOn_puncturedPlaneAngularForm_arg_neg⟩

/-- The angular form on the punctured plane `ℂ \ {0}` has local primitives at every point. -/
theorem forall_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted (z : puncturedPlane) :
    ∃ (g : puncturedPlane → ℝ) (U : Set puncturedPlane),
      z ∈ U ∧ IsPrimitiveOn puncturedPlaneAngularFormRestricted g U :=
  ((forall_exists_isPrimitiveOn_mpullback_subtypeVal_iff (U := puncturedPlane)
    puncturedPlaneAngularForm).mpr fun _ hz ↦
      forall_exists_isPrimitiveOn_puncturedPlaneAngularForm hz) z

/-- On the punctured plane, `puncturedPlaneAngularFormRestricted` is the imaginary part of the
logarithmic derivative `dz / z = mlogDeriv Subtype.val`. -/
theorem puncturedPlaneAngularFormRestricted_eq_mapCoeff_mlogDeriv :
    puncturedPlaneAngularFormRestricted =
      RoughForm.mapCoeff Complex.imCLM
        (mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ)) := by
  funext z
  ext v
  rw [puncturedPlaneAngularFormRestricted, mpullback_apply, RoughForm.mapCoeff_apply,
    mlogDeriv_apply, mvfderiv_apply_eq_mfderiv_apply, Complex.imCLM_apply]
  let w : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) z (v 0)
  have hv : (fun i : Fin 1 ↦
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) z (v i)) = fun _ ↦ w :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hv, puncturedPlaneAngularForm_apply, div_eq_inv_mul]

/-- The angular form on the punctured plane is smooth. -/
theorem isSmoothForm_puncturedPlaneAngularFormRestricted :
    IsSmoothForm 𝓘(ℝ, ℂ) ∞ puncturedPlaneAngularFormRestricted := by
  rw [puncturedPlaneAngularFormRestricted_eq_mapCoeff_mlogDeriv]
  exact (isSmoothForm_mlogDeriv (n := ∞) contMDiff_subtype_val (fun z ↦ z.2)).mapCoeff
    Complex.imCLM

/-- The angular form on the punctured plane is closed. -/
theorem mextDeriv_puncturedPlaneAngularFormRestricted :
    mextDeriv puncturedPlaneAngularFormRestricted = 0 := by
  rw [puncturedPlaneAngularFormRestricted_eq_mapCoeff_mlogDeriv,
    mextDeriv_mapCoeff Complex.imCLM
      ((isSmoothForm_mlogDeriv (n := ∞) contMDiff_subtype_val (fun z ↦ z.2)).of_le (by simp)),
    mextDeriv_mlogDeriv (contMDiff_subtype_val (n := 2)) (fun z ↦ z.2), RoughForm.mapCoeff_zero]

/-- The inclusion of the unit circle into the punctured plane `ℂ \ {0}`. -/
def circleToPuncturedPlane (z : Circle) : puncturedPlane :=
  ⟨z, mem_puncturedPlane_iff.mpr (Circle.coe_ne_zero z)⟩

theorem contMDiff_circleToPuncturedPlane :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ circleToPuncturedPlane :=
  (ContMDiff.subtypeVal_comp_iff puncturedPlane circleToPuncturedPlane).mp contMDiff_coe_sphere

/-- Pulling `puncturedPlaneAngularFormRestricted` back to the unit circle yields
`TauCeti.circleAngularForm`. -/
theorem mpullback_circleToPuncturedPlane_puncturedPlaneAngularFormRestricted :
    mpullback (𝓡 1) 𝓘(ℝ, ℂ) circleToPuncturedPlane puncturedPlaneAngularFormRestricted =
      circleAngularForm := by
  have hcomp : mpullback (𝓡 1) 𝓘(ℝ, ℂ) circleToPuncturedPlane puncturedPlaneAngularFormRestricted =
      mpullback (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) puncturedPlaneAngularForm := by
    simpa [Function.comp_def, circleToPuncturedPlane, puncturedPlaneAngularFormRestricted] using
      (mpullback_comp (I := 𝓡 1) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
        (f := circleToPuncturedPlane) (g := (Subtype.val : puncturedPlane → ℂ))
        (contMDiff_circleToPuncturedPlane.mdifferentiable (by simp))
        (contMDiff_subtype_val.mdifferentiable one_ne_zero)
        puncturedPlaneAngularForm).symm
  rw [hcomp, circleAngularForm_def]
  funext z
  ext v
  rw [mpullback_apply, mpullback_apply]
  let w : ℂ := mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun y : Circle ↦ (y : ℂ)) z (v 0)
  have hv : (fun i : Fin 1 ↦
      mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun y : Circle ↦ (y : ℂ)) z (v i)) = fun _ ↦ w :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hv, puncturedPlaneAngularForm_apply, ← puncturedPlaneAngularCovector_apply,
    puncturedPlaneAngularCovector_apply_re_im, Circle.re_sq_add_im_sq z, div_one,
    planeAngularForm_apply]

/-- The standard counterclockwise loop around the unit circle, `t ↦ exp (2πit)`. -/
def circleUnitLoop : Path (1 : Circle) 1 :=
  (ContinuousMap.id Circle).toBasedLoop

@[simp]
theorem circleUnitLoop_apply (t : unitInterval) :
    circleUnitLoop t = Circle.exp (2 * Real.pi * t) :=
  (ContinuousMap.toBasedLoop_apply (ContinuousMap.id Circle) t).trans (by
    rw [ContinuousMap.id_apply, unitToCircle_apply])

/-- The standard counterclockwise unit circle loop inside the punctured plane `ℂ \ {0}`. -/
def puncturedPlaneUnitLoop : Path puncturedPlaneOne puncturedPlaneOne :=
  circleUnitLoop.map contMDiff_circleToPuncturedPlane.continuous

@[simp]
theorem puncturedPlaneUnitLoop_apply (t : unitInterval) :
    (puncturedPlaneUnitLoop t : ℂ) = Circle.exp (2 * Real.pi * t) := by
  have hmap : puncturedPlaneUnitLoop t = circleToPuncturedPlane (circleUnitLoop t) :=
    congrFun (circleUnitLoop.map_coe contMDiff_circleToPuncturedPlane.continuous) t
  rw [hmap, circleToPuncturedPlane, circleUnitLoop_apply]

/-- The angular form `circleAngularForm` has local primitives on `Circle`. -/
theorem forall_exists_isPrimitiveOn_circleAngularForm (z : Circle) :
    ∃ (g : Circle → ℝ) (U : Set Circle), z ∈ U ∧ IsPrimitiveOn circleAngularForm g U := by
  obtain ⟨g, U, hzU, hgU⟩ :=
    forall_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted (circleToPuncturedPlane z)
  refine ⟨g ∘ circleToPuncturedPlane, circleToPuncturedPlane ⁻¹' U, hzU, ?_⟩
  rw [← mpullback_circleToPuncturedPlane_puncturedPlaneAngularFormRestricted]
  exact hgU.mpullback (contMDiff_circleToPuncturedPlane.mdifferentiable (by simp))

/-- The continuous path integral of `circleAngularForm` around the unit circle loop is `2π`. -/
theorem continuousPathIntegral_circleAngularForm_circleUnitLoop :
    continuousPathIntegral circleAngularForm circleUnitLoop = 2 * Real.pi := by
  let c : ℝ → Circle := fun t ↦ Circle.exp (2 * Real.pi * t + 0)
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 1 c :=
    (contMDiff_circleExp (m := 1)).comp
      ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  rw [continuousPathIntegral_eq_pathIntegral forall_exists_isPrimitiveOn_circleAngularForm
    (isSmoothForm_circleAngularForm.of_le (by simp)) hc (fun t ↦ by simp [c]),
    pathIntegral_comp_mul_add (isSmoothForm_circleAngularForm.of_le (by simp))
      (contMDiff_circleExp (m := 1)) (2 * Real.pi) 0 0 1,
    pathIntegral_circleAngularForm_circleExp]
  ring

/-- The continuous path integral of the punctured-plane angular form around the unit circle loop
is `2π`. -/
theorem continuousPathIntegral_puncturedPlaneAngularForm_unitLoop :
    continuousPathIntegral puncturedPlaneAngularFormRestricted puncturedPlaneUnitLoop =
      2 * Real.pi := by
  rw [continuousPathIntegral_eq_of_apply_eq puncturedPlaneUnitLoop
        (circleUnitLoop.map contMDiff_circleToPuncturedPlane.continuous)
        (fun t ↦ Subtype.ext (by
          rw [puncturedPlaneUnitLoop_apply,
            congrFun (circleUnitLoop.map_coe contMDiff_circleToPuncturedPlane.continuous) t]
          simp [circleToPuncturedPlane])),
    ← continuousPathIntegral_mpullback
      forall_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted
      (contMDiff_circleToPuncturedPlane.mdifferentiable (by simp)),
    mpullback_circleToPuncturedPlane_puncturedPlaneAngularFormRestricted,
    continuousPathIntegral_circleAngularForm_circleUnitLoop]

/-- Traversing the unit circle loop twice integrates the angular form to `4π`. -/
theorem continuousPathIntegral_puncturedPlaneAngularForm_unitLoop_trans :
    continuousPathIntegral puncturedPlaneAngularFormRestricted
        (puncturedPlaneUnitLoop.trans puncturedPlaneUnitLoop) = 4 * Real.pi := by
  rw [continuousPathIntegral_trans, continuousPathIntegral_puncturedPlaneAngularForm_unitLoop]
  ring

/-- Reversing the unit circle loop negates the integral of the angular form to `-2π`. -/
theorem continuousPathIntegral_puncturedPlaneAngularForm_unitLoop_symm :
    continuousPathIntegral puncturedPlaneAngularFormRestricted puncturedPlaneUnitLoop.symm =
      -(2 * Real.pi) := by
  rw [continuousPathIntegral_symm, continuousPathIntegral_puncturedPlaneAngularForm_unitLoop]

/-- Along the unit circle loop, the continuous path integral of the punctured-plane angular form
agrees with Mathlib's `curveIntegral` of its covector field (both equal `2π`). -/
theorem curveIntegral_puncturedPlaneAngularCovector_unitLoop :
    curveIntegral puncturedPlaneAngularCovector
        (puncturedPlaneUnitLoop.map continuous_subtype_val) = 2 * Real.pi := by
  have hcov : puncturedPlaneAngularCovector = fun z : ℂ ↦
      (z.re / (z.re ^ 2 + z.im ^ 2)) • Complex.imCLM -
        (z.im / (z.re ^ 2 + z.im ^ 2)) • Complex.reCLM := by
    funext z; ext v
    simp only [puncturedPlaneAngularCovector_apply_re_im, sub_apply, smul_apply,
      Complex.imCLM_apply, Complex.reCLM_apply, smul_eq_mul]
    ring
  have hden (z : ℂ) (hz : z ∈ (puncturedPlane : Set ℂ)) : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    have hne : z ≠ 0 := hz
    simpa [Complex.normSq_apply, sq] using Complex.normSq_pos.mpr hne |>.ne'
  have hα : ContinuousOn puncturedPlaneAngularCovector puncturedPlane := by
    rw [hcov]
    have hsq : ContinuousOn (fun z : ℂ ↦ z.re ^ 2 + z.im ^ 2) puncturedPlane :=
      ((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2)).continuousOn
    exact ((Complex.continuous_re.continuousOn.div hsq hden).smul continuousOn_const).sub
      ((Complex.continuous_im.continuousOn.div hsq hden).smul continuousOn_const)
  let c : ℝ → puncturedPlane := fun t ↦ circleToPuncturedPlane (Circle.exp (2 * Real.pi * t))
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 c :=
    (contMDiff_circleToPuncturedPlane.of_le (by simp)).comp
      ((contMDiff_circleExp (m := 1)).comp (contDiff_const.mul contDiff_id).contMDiff)
  rw [← continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral hα
    forall_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted hc
    (fun t ↦ Subtype.ext (by simp [c, circleToPuncturedPlane]))]
  exact continuousPathIntegral_puncturedPlaneAngularForm_unitLoop

/-- Along the unit circle loop, `TauCeti.periodHom` of the smooth closed angular form on `ℂ \ {0}`
equals `2π`, agreeing with `continuousPathIntegral`. -/
theorem periodHom_puncturedPlaneAngularForm_unitLoop :
    periodHom puncturedPlaneAngularFormRestricted puncturedPlaneOne
        (Additive.ofMul (.of (.mk puncturedPlaneUnitLoop))) = 2 * Real.pi := by
  rw [← continuousPathIntegral_eq_periodHom
    (isSmoothForm_puncturedPlaneAngularFormRestricted.of_le (by simp))
    mextDeriv_puncturedPlaneAngularFormRestricted,
    continuousPathIntegral_puncturedPlaneAngularForm_unitLoop]

/-- The angular form on the punctured plane `ℂ \ {0}` has no global primitive. -/
theorem not_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted :
    ¬ ∃ g : puncturedPlane → ℝ, IsPrimitiveOn puncturedPlaneAngularFormRestricted g univ := by
  rintro ⟨g, hg⟩
  have h0 := continuousPathIntegral_eq_sub_of_isPrimitiveOn
    forall_exists_isPrimitiveOn_puncturedPlaneAngularFormRestricted hg puncturedPlaneUnitLoop
    (fun _ ↦ mem_univ _)
  rw [sub_self, continuousPathIntegral_puncturedPlaneAngularForm_unitLoop] at h0
  linarith [Real.pi_pos]

/-- The angular form `circleAngularForm` on `Circle` has no global primitive. -/
theorem not_exists_isPrimitiveOn_circleAngularForm :
    ¬ ∃ g : Circle → ℝ, IsPrimitiveOn circleAngularForm g univ := by
  rintro ⟨g, hg⟩
  have h0 := continuousPathIntegral_eq_sub_of_isPrimitiveOn
    forall_exists_isPrimitiveOn_circleAngularForm hg circleUnitLoop (fun _ ↦ mem_univ _)
  rw [sub_self, continuousPathIntegral_circleAngularForm_circleUnitLoop] at h0
  linarith [Real.pi_pos]

/-- The logarithmic derivative `dz / z` on the punctured plane has local primitives everywhere. -/
theorem forall_exists_isPrimitiveOn_mlogDeriv_puncturedPlane (z : puncturedPlane) :
    ∃ (g : puncturedPlane → ℂ) (U : Set puncturedPlane),
      z ∈ U ∧ IsPrimitiveOn (mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ)) g U := by
  obtain ⟨g, -, U, hzU, hgU⟩ := exists_contMDiff_isPrimitiveOn (r := 1) le_rfl
    ((isSmoothForm_mlogDeriv (n := ∞) contMDiff_subtype_val (fun w ↦ w.2)).of_le (by simp))
    (mextDeriv_mlogDeriv (contMDiff_subtype_val (n := 2)) (fun w ↦ w.2)) z
  exact ⟨g, U, hzU, hgU⟩

/-- The continuous path integral of `dz / z` around the unit circle loop in `ℂ \ {0}` is `2πi`. -/
theorem continuousPathIntegral_mlogDeriv_puncturedPlane_unitLoop :
    continuousPathIntegral (mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ))
        puncturedPlaneUnitLoop = 2 * Real.pi * Complex.I := by
  let c : ℝ → puncturedPlane := fun t ↦ circleToPuncturedPlane (Circle.exp (2 * Real.pi * t))
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 c :=
    (contMDiff_circleToPuncturedPlane.of_le (by simp)).comp
      ((contMDiff_circleExp (m := 1)).comp (contDiff_const.mul contDiff_id).contMDiff)
  rw [continuousPathIntegral_eq_pathIntegral forall_exists_isPrimitiveOn_mlogDeriv_puncturedPlane
    ((isSmoothForm_mlogDeriv (n := ∞) contMDiff_subtype_val (fun w ↦ w.2)).of_le (by simp))
    hc (fun t ↦ Subtype.ext (by simp [c, circleToPuncturedPlane])), pathIntegral_def]
  have hval (t : ℝ) :
      mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) (c t)
        (fun _ ↦ Manifold.curveVelocity 𝓘(ℝ, ℂ) c t) = 2 * Real.pi * Complex.I := by
    rw [mlogDeriv_apply, mvfderiv_apply_eq_mfderiv_apply]
    have hvel : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) (c t)
        (Manifold.curveVelocity 𝓘(ℝ, ℂ) c t) =
        deriv (fun s : ℝ ↦ (Circle.exp (2 * Real.pi * s) : ℂ)) t := by
      have hsub : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) (c t) :=
        contMDiff_subtype_val.mdifferentiable one_ne_zero _
      have hcv := Manifold.curveVelocityWithin_map (s := univ) hsub uniqueDiffWithinAt_univ
        ((hc t).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
      rw [Manifold.curveVelocityWithin_univ, Manifold.curveVelocityWithin_univ] at hcv
      rw [← hcv, Manifold.curveVelocity_eq_deriv]
      rfl
    rw [hvel]
    have hlin : HasDerivAt (fun s : ℝ ↦ 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    have hd : HasDerivAt (fun s : ℝ ↦ (Circle.exp (2 * Real.pi * s) : ℂ))
        ((2 * Real.pi) • (Complex.I * (Circle.exp (2 * Real.pi * t) : ℂ))) t :=
      (hasDerivAt_coe_circleExp (2 * Real.pi * t)).scomp t hlin
    rw [hd.deriv, Complex.real_smul]
    have hne : (Circle.exp (2 * Real.pi * t) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    simp only [c, circleToPuncturedPlane]
    push_cast
    field_simp [hne]
  simp_rw [hval]
  exact (intervalIntegral.integral_const (E := ℂ) (a := (0 : ℝ)) (b := 1)
    (2 * Real.pi * Complex.I)).trans (by simp)

/-- The holomorphic function `z ↦ z⁻¹` has no complex primitive on `ℂ \ {0}`. -/
theorem not_isExactOn_inv_compl_zero :
    ¬ Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) ({0} : Set ℂ)ᶜ := by
  rintro ⟨g, hg⟩
  let φ : RoughForm 𝓘(ℝ, ℂ) ℂ ℂ 1 :=
    fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1)
      ((ContinuousLinearMap.toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)
  have hgφ : IsPrimitiveOn φ g ({0} : Set ℂ)ᶜ :=
    isPrimitiveOn_toSpanSingleton_iff.mpr ⟨isOpen_compl_singleton, hg⟩
  have hpull : mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) φ =
      mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) := by
    funext z; ext v
    rw [mpullback_apply, mlogDeriv_apply, mvfderiv_apply_eq_mfderiv_apply]
    let w : ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) z (v 0)
    have hv : (fun i : Fin 1 ↦
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ) z (v i)) = fun _ ↦ w :=
      funext fun i ↦ by rw [Subsingleton.elim i 0]
    rw [hv]
    exact (ContinuousAlternatingMap.ofSubsingleton_apply_apply
      (f := (ContinuousLinearMap.toSpanSingleton ℂ (z : ℂ)⁻¹).restrictScalars ℝ)
      (i := (0 : Fin 1)) (x := fun _ ↦ w)).trans
      (by
        rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul, mul_comm])
  have hpre : ((Subtype.val : puncturedPlane → ℂ) ⁻¹' ({0} : Set ℂ)ᶜ) = univ :=
    eq_univ_iff_forall.mpr fun z ↦ z.2
  have hgp : IsPrimitiveOn (mlogDeriv 𝓘(ℝ, ℂ) (Subtype.val : puncturedPlane → ℂ))
      (g ∘ Subtype.val) univ := by
    rw [← hpull, ← hpre]
    exact hgφ.mpullback_subtypeVal (U := puncturedPlane)
  have h0 := continuousPathIntegral_eq_sub_of_isPrimitiveOn
    forall_exists_isPrimitiveOn_mlogDeriv_puncturedPlane hgp puncturedPlaneUnitLoop
    (fun _ ↦ mem_univ _)
  rw [sub_self, continuousPathIntegral_mlogDeriv_puncturedPlane_unitLoop] at h0
  have hne : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact hne h0

end PuncturedPlane

/-! ### Non-`C¹` form `d(|x|^(3/2))` on `ℝ × ℝ` -/

section AbsRpowThreeHalves

/-- The `C¹` (but not `C²`) real function `x ↦ |x|^(3/2)`. -/
def absRpowThreeHalves (x : ℝ) : ℝ :=
  |x| ^ ((3 : ℝ) / 2)

/-- The derivative of `x ↦ |x|^(3/2)`, given by `(3/2) (√x - √(-x))` (which is `C⁰` but not
differentiable at `0`). -/
def absRpowThreeHalvesDeriv (x : ℝ) : ℝ :=
  ((3 : ℝ) / 2) * (Real.sqrt x - Real.sqrt (-x))

/-- `x ↦ |x|^(3/2)` is differentiable everywhere on `ℝ` with derivative
`absRpowThreeHalvesDeriv`. -/
theorem hasDerivAt_absRpowThreeHalves (x : ℝ) :
    HasDerivAt absRpowThreeHalves (absRpowThreeHalvesDeriv x) x := by
  unfold absRpowThreeHalves
  refine (hasDerivAt_abs_rpow x (p := (3 : ℝ) / 2) (by norm_num)).congr_deriv ?_
  rw [absRpowThreeHalvesDeriv]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    rw [abs_of_neg hx, Real.sqrt_eq_zero_of_nonpos hx.le, zero_sub, Real.sqrt_eq_rpow]
    have hmul : (-x) ^ ((3 : ℝ) / 2 - 2) * (-x) = (-x) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add_one hpos.ne']
      norm_num
    linarith [congrArg (fun t ↦ (3 : ℝ) / 2 * t) hmul]
  · simp
  · rw [abs_of_pos hx, Real.sqrt_eq_zero_of_nonpos (x := -x) (by linarith), sub_zero,
      Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add_one hx.ne']
    norm_num

/-- `absRpowThreeHalvesDeriv` is not differentiable at `0`. -/
theorem not_differentiableAt_absRpowThreeHalvesDeriv_zero :
    ¬ DifferentiableAt ℝ absRpowThreeHalvesDeriv 0 := by
  intro hd
  obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hC
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right C 0
  let r : ℝ := min (Real.sqrt (δ / 2)) (1 / (M + 1))
  have hr_pos : 0 < r := lt_min (Real.sqrt_pos.mpr (half_pos hδ)) (by positivity)
  have ht_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have ht_lt : r ^ 2 < δ := by
    have h1 : r ^ 2 ≤ (Real.sqrt (δ / 2)) ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg (δ / 2)]) (min_le_left _ _)
    rw [Real.sq_sqrt (half_pos hδ).le] at h1
    linarith
  have hspec := hball (y := r ^ 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]; exact ht_lt)
  have hval : absRpowThreeHalvesDeriv (r ^ 2) = (3 / 2 : ℝ) * r := by
    rw [absRpowThreeHalvesDeriv, Real.sqrt_sq hr_pos.le,
      Real.sqrt_eq_zero_of_nonpos (by linarith), sub_zero]
  have h0 : absRpowThreeHalvesDeriv 0 = 0 := by simp [absRpowThreeHalvesDeriv]
  rw [hval, h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity), abs_of_pos ht_pos] at hspec
  have hrM : r ≤ 1 / (M + 1) := min_le_right _ _
  have hCM : C * r ^ 2 ≤ M * r ^ 2 := mul_le_mul_of_nonneg_right (le_max_left C 0) ht_pos.le
  have hstep : (3 / 2 : ℝ) ≤ M * r := by
    nlinarith [hspec, hCM]
  have hMr : M * r ≤ M / (M + 1) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrM hM
  have hlt1 : M / (M + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- The function `(x, y) ↦ |x|^(3/2)` on `ℝ × ℝ`. -/
def absRpowThreeHalvesPlane (p : ℝ × ℝ) : ℝ :=
  absRpowThreeHalves p.1

/-- The `1`-form `d(|x|^(3/2))` on `ℝ × ℝ`, which is continuous with a global primitive yet not
`C¹`. -/
def absRpowThreeHalvesForm : RoughForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ℝ 1 :=
  fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (absRpowThreeHalvesDeriv p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp]
theorem absRpowThreeHalvesForm_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    absRpowThreeHalvesForm p v = absRpowThreeHalvesDeriv p.1 * (v 0).1 :=
  (rfl)

/-- `absRpowThreeHalvesPlane` is a global primitive of `absRpowThreeHalvesForm` on `ℝ × ℝ`. -/
theorem isPrimitiveOn_absRpowThreeHalvesForm :
    IsPrimitiveOn absRpowThreeHalvesForm absRpowThreeHalvesPlane univ := by
  unfold absRpowThreeHalvesForm
  rw [isPrimitiveOn_ofSubsingleton_iff]
  refine ⟨isOpen_univ, fun p _ ↦ ?_⟩
  have h := (hasDerivAt_absRpowThreeHalves p.1).hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [mul_comm]

/-- Every point of `ℝ × ℝ` has a local primitive for `absRpowThreeHalvesForm`. -/
theorem forall_exists_isPrimitiveOn_absRpowThreeHalvesForm (p : ℝ × ℝ) :
    ∃ (g : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)), p ∈ U ∧ IsPrimitiveOn absRpowThreeHalvesForm g U :=
  ⟨absRpowThreeHalvesPlane, univ, mem_univ p, isPrimitiveOn_absRpowThreeHalvesForm⟩

/-- Every global primitive of `absRpowThreeHalvesForm` on `ℝ × ℝ` equals `|x|^(3/2) + c`. -/
theorem isPrimitiveOn_absRpowThreeHalvesForm_univ_iff {g : ℝ × ℝ → ℝ} :
    IsPrimitiveOn absRpowThreeHalvesForm g univ ↔
      ∃ c : ℝ, g = fun p ↦ absRpowThreeHalvesPlane p + c := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hg.exists_eq_add_const isPrimitiveOn_absRpowThreeHalvesForm
    exact ⟨c, funext hc⟩
  · rintro ⟨c, rfl⟩
    exact isPrimitiveOn_absRpowThreeHalvesForm.add_const c

/-- `absRpowThreeHalvesForm` is not a `C¹` form on `ℝ × ℝ`. -/
theorem not_isSmoothForm_one_absRpowThreeHalvesForm :
    ¬ IsSmoothForm 𝓘(ℝ, ℝ × ℝ) 1 absRpowThreeHalvesForm := by
  intro hsmooth
  have hcd : ContDiff ℝ (E := ℝ × ℝ) (F := (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ) 1 absRpowThreeHalvesForm :=
    isSmoothForm_modelSpace_iff.mp hsmooth
  have h1 : DifferentiableAt ℝ
      (fun p : ℝ × ℝ ↦
        ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ (fun _ ↦ ((1 : ℝ), (0 : ℝ)))
          (absRpowThreeHalvesForm p)) (0, 0) :=
    (differentiableAt_const _).clm_apply (hcd.differentiable one_ne_zero (0, 0))
  have h2 : DifferentiableAt ℝ (fun x : ℝ ↦ (x, (0 : ℝ))) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const (0 : ℝ))
  have hcomp : DifferentiableAt ℝ
      (fun x : ℝ ↦
        ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ (fun _ ↦ ((1 : ℝ), (0 : ℝ)))
          (absRpowThreeHalvesForm (x, 0))) 0 :=
    DifferentiableAt.comp (f := fun x : ℝ ↦ (x, (0 : ℝ))) 0 h1 h2
  have hdiff : DifferentiableAt ℝ absRpowThreeHalvesDeriv 0 :=
    hcomp.congr_of_eventuallyEq (.of_forall fun x ↦
      ((absRpowThreeHalvesForm_apply (x, 0) (fun _ ↦ (1, 0))).trans (mul_one _)).symm)
  exact not_differentiableAt_absRpowThreeHalvesDeriv_zero hdiff

/-- Along the segment `(0, 0) → (1, 0)` in `ℝ × ℝ`, `continuousPathIntegral` of `d(|x|^(3/2))`
is `1`, whereas `TauCeti.pathClassIntegral` returns its default value `0` because the form is not
`C¹`. -/
theorem continuousPathIntegral_absRpowThreeHalvesForm_seg01 :
    let γ : Path ((0 : ℝ), (0 : ℝ)) (1, 0) :=
      { toFun := fun t : unitInterval ↦ ((t : ℝ), 0)
        continuous_toFun := continuous_subtype_val.prodMk continuous_const
        source' := rfl
        target' := rfl }
    continuousPathIntegral absRpowThreeHalvesForm γ = 1 ∧
      pathClassIntegral absRpowThreeHalvesForm (.mk γ) = 0 := by
  intro γ
  refine ⟨?_, pathClassIntegral_undef (fun h ↦ not_isSmoothForm_one_absRpowThreeHalvesForm h.1) _⟩
  rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn
    forall_exists_isPrimitiveOn_absRpowThreeHalvesForm isPrimitiveOn_absRpowThreeHalvesForm γ
    (fun _ ↦ mem_univ _)]
  simp [absRpowThreeHalvesPlane, absRpowThreeHalves]

/-- Along the segment `(-1, 0) → (1, 0)` in `ℝ × ℝ`, `continuousPathIntegral` of `d(|x|^(3/2))`
is `0`. -/
theorem continuousPathIntegral_absRpowThreeHalvesForm_segNeg11 :
    let γ : Path ((-1 : ℝ), (0 : ℝ)) (1, 0) :=
      { toFun := fun t : unitInterval ↦ (2 * (t : ℝ) - 1, 0)
        continuous_toFun :=
          ((continuous_const.mul continuous_subtype_val).sub continuous_const).prodMk
            continuous_const
        source' := by ext <;> norm_num
        target' := by ext <;> norm_num }
    continuousPathIntegral absRpowThreeHalvesForm γ = 0 := by
  intro γ
  rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn
    forall_exists_isPrimitiveOn_absRpowThreeHalvesForm isPrimitiveOn_absRpowThreeHalvesForm γ
    (fun _ ↦ mem_univ _)]
  simp [absRpowThreeHalvesPlane, absRpowThreeHalves]

end AbsRpowThreeHalves

/-! ### Discontinuous form `d(x² sin(1/x))` on `ℝ` -/

section XSqSinInv

/-- The everywhere-differentiable function `x ↦ x² sin(1/x)` on `ℝ` (equal to `0` at `0`). -/
def xSqSinInv (x : ℝ) : ℝ :=
  x ^ 2 * Real.sin x⁻¹

/-- The derivative of `x ↦ x² sin(1/x)`: `0` at `0`, and `2x sin(1/x) - cos(1/x)` for `x ≠ 0`. -/
def xSqSinInvDeriv (x : ℝ) : ℝ :=
  if x = 0 then 0 else 2 * x * Real.sin x⁻¹ - Real.cos x⁻¹

/-- `x ↦ x² sin(1/x)` is differentiable everywhere on `ℝ` with derivative `xSqSinInvDeriv`. -/
theorem hasDerivAt_xSqSinInv (x : ℝ) : HasDerivAt xSqSinInv (xSqSinInvDeriv x) x := by
  by_cases hx : x = 0
  · subst hx
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h0 : xSqSinInv 0 = 0 := by simp [xSqSinInv]
    have hd0 : xSqSinInvDeriv 0 = 0 := by simp [xSqSinInvDeriv]
    rw [h0, hd0]
    refine squeeze_zero_norm' (a := fun t : ℝ ↦ |t|) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [xSqSinInv, zero_add, sub_zero, smul_eq_mul, Real.norm_eq_abs]
      rw [show t⁻¹ * (t ^ 2 * Real.sin t⁻¹) = t * Real.sin t⁻¹ by field_simp [ht], abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sin_le_one _)
    · simpa using
        (continuous_abs.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
  · have hmul := (hasDerivAt_pow 2 x).mul ((Real.hasDerivAt_sin x⁻¹).comp x (hasDerivAt_inv hx))
    refine hmul.congr_deriv ?_
    simp only [xSqSinInvDeriv, ite_eq_right hx, Function.comp_apply, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one]
    field_simp [hx]
    ring

/-- The `1`-form `d(x² sin(1/x))` on `ℝ`, which has a global primitive yet is discontinuous at
`0`. -/
def xSqSinInvForm : RoughForm 𝓘(ℝ, ℝ) ℝ ℝ 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1)
    (xSqSinInvDeriv x • ContinuousLinearMap.id ℝ ℝ)

@[simp]
theorem xSqSinInvForm_apply (x : ℝ) (v : Fin 1 → ℝ) :
    xSqSinInvForm x v = xSqSinInvDeriv x * v 0 :=
  (rfl)

/-- `xSqSinInv` is a global primitive of `xSqSinInvForm` on `ℝ`. -/
theorem isPrimitiveOn_xSqSinInvForm : IsPrimitiveOn xSqSinInvForm xSqSinInv univ := by
  unfold xSqSinInvForm
  rw [isPrimitiveOn_ofSubsingleton_iff]
  refine ⟨isOpen_univ, fun x _ ↦ ?_⟩
  refine (hasDerivAt_xSqSinInv x).hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [mul_comm]

/-- `xSqSinInvForm` is not even continuous (`C⁰`) on `ℝ`, because `xSqSinInvDeriv` oscillates
near `0`. -/
theorem not_isSmoothForm_zero_xSqSinInvForm :
    ¬ IsSmoothForm 𝓘(ℝ, ℝ) 0 xSqSinInvForm := by
  intro hsmooth
  have hcont : Continuous (fun x : ℝ ↦ xSqSinInvForm x fun _ ↦ (1 : ℝ)) :=
    (ContinuousAlternatingMap.apply ℝ ℝ ℝ (fun _ ↦ (1 : ℝ))).continuous.comp
      (isSmoothForm_modelSpace_iff.mp hsmooth).continuous
  have hcontD : Continuous xSqSinInvDeriv := hcont.congr fun x ↦ by simp
  let u : ℕ → ℝ := fun n ↦ (2 * Real.pi * ((n : ℝ) + 1))⁻¹
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ ↦ 2 * Real.pi * ((n : ℝ) + 1)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop Real.two_pi_pos
    exact tendsto_inv_atTop_zero.comp hmul
  have hval (n : ℕ) : xSqSinInvDeriv (u n) = -1 := by
    have hpos : (0 : ℝ) < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
    have hne : u n ≠ 0 := inv_ne_zero hpos.ne'
    have hinv : (u n)⁻¹ = ((2 * (n + 1) : ℕ) : ℝ) * Real.pi := by
      simp [u, inv_inv]; ring
    rw [xSqSinInvDeriv, ite_eq_right hne, hinv, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    simp [pow_mul]
  have hlim : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 0) := by
    have h := (hcontD.continuousAt (x := 0)).tendsto.comp hu_tendsto
    have h0 : xSqSinInvDeriv 0 = 0 := by simp [xSqSinInvDeriv]
    rw [h0] at h
    exact h.congr fun n ↦ hval n
  have hEq : (-1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at hEq

/-- Along the segment `0 → 2 / π` in `ℝ`, `continuousPathIntegral` of the discontinuous form
`d(x² sin(1/x))` equals `(2 / π)²` (nonzero), whereas `TauCeti.pathClassIntegral` returns its
default value `0`. -/
theorem continuousPathIntegral_xSqSinInvForm_seg :
    let γ : Path (0 : ℝ) (2 / Real.pi) :=
      { toFun := fun t : unitInterval ↦ (2 / Real.pi) * (t : ℝ)
        continuous_toFun := continuous_const.mul continuous_subtype_val
        source' := by simp
        target' := by simp }
    continuousPathIntegral xSqSinInvForm γ = (2 / Real.pi) ^ 2 ∧
      pathClassIntegral xSqSinInvForm (.mk γ) = 0 := by
  intro γ
  refine ⟨?_, pathClassIntegral_undef (fun h ↦
    not_isSmoothForm_zero_xSqSinInvForm (h.1.of_le (by simp))) _⟩
  rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ isPrimitiveOn_xSqSinInvForm γ]
  simp [xSqSinInv]

end XSqSinInv

end TauCeti
