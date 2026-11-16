/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The exact prequantum line

A real one-form `θ` defines the connection `d + iθ/ℏ` on the trivial complex line.
Its curvature is `i dθ/ℏ`, hence `-iω/ℏ` when `ω = -dθ`. The connection is encoded
by Mathlib's `CovariantDerivative` on the real smooth bundle with fibre `ℂ`;
complex linearity on sections is proved separately. The construction itself does
not require nondegeneracy of the two-form.

This is the trivial-line construction in Schottenloher, *Lecture Notes on
Geometric Quantization*, version 15.6, Example 7.3 and Remark 7.4, pp. 96–97,
with the conjugate line convention and curvature scale `1/ℏ`.
-/

public noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

section Basic

variable [IsManifold I 1 M]

/-- The connection `d + iθ/ℏ` on the trivial complex line, regarded as a real
smooth vector bundle. Prequantization uses `0 < ℏ`; the formula is defined at
all real scales, with Lean's totalized inverse. -/
def exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) :
    CovariantDerivative I ℂ (Trivial M ℂ) :=
  (CovariantDerivative.trivial (I := I) ℂ).addOneForm fun x ↦
    letI := (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x).isNormableSpace
    ((ContinuousLinearMap.smulRightL ℝ (TangentSpace I x) ℂ)
      (SmoothForm.degreeOneEquiv θ x)).comp
        (ℏ⁻¹ • ContinuousLinearMap.lsmul ℝ ℂ Complex.I)

/-- Evaluation of the exact-line connection in its global unit frame. -/
@[simp]
theorem exactPrequantumConnection_apply (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (v : TangentSpace I x) :
    exactPrequantumConnection θ ℏ s x v =
      mvfderiv I s x v + ((θ : RoughForm I M ℝ 1) x ![v] / ℏ) • (Complex.I * s x) := by
  simp [exactPrequantumConnection, CovariantDerivative.addOneForm,
    div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The zero primitive gives the ordinary derivative connection. -/
@[simp]
theorem exactPrequantumConnection_zero (ℏ : ℝ) :
    exactPrequantumConnection (0 : SmoothForm I M ℝ 1) ℏ =
      CovariantDerivative.trivial (I := I) ℂ := by
  ext s x v
  simp only [exactPrequantumConnection_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero, zero_div, zero_smul, CovariantDerivative.trivial_apply]
  exact add_zero _

/-- Changing the primitive adds precisely the corresponding imaginary one-form
to the line connection. No differentiability of the section is required. -/
theorem exactPrequantumConnection_add_apply (θ β : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (v : TangentSpace I x) :
    exactPrequantumConnection (θ + β) ℏ s x v =
      exactPrequantumConnection θ ℏ s x v +
        (β.1 x ![v] / ℏ) • (Complex.I * s x) := by
  simp only [exactPrequantumConnection_apply, AddMemClass.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, add_div, add_smul]
  abel

/-- The exact-line connection commutes with constant complex scalars. This also
holds for the totalized derivative on sections not differentiable at the point. -/
theorem exactPrequantumConnection_const_smul (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    (s : M → ℂ) (x : M) (c : ℂ) (v : TangentSpace I x) :
    exactPrequantumConnection θ ℏ (fun y ↦ c • s y) x v =
      c * exactPrequantumConnection θ ℏ s x v := by
  have hd : mvfderiv I (fun y ↦ c • s y) x = c • mvfderiv I s x := by
    by_cases hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x
    · exact mvfderiv_const_smul hs c
    by_cases hc : c = 0
    · subst c
      simp [mvfderiv_const]
    have hcs : ¬ MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ c • s y) x := by
      intro hcs
      have h := (ContinuousLinearMap.lsmul ℝ ℂ c⁻¹).mdifferentiableAt.comp x hcs
      apply hs
      simpa [Function.comp_def, smul_smul, ← mul_assoc, inv_mul_cancel₀ hc] using h
    rw [mvfderiv, mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hcs,
      mfderiv_zero_of_not_mdifferentiableAt hs]
    simp
  rw [exactPrequantumConnection_apply, hd, exactPrequantumConnection_apply]
  simp only [smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- The exact-line connection preserves the standard Hermitian metric on `ℂ`. -/
theorem exactPrequantumConnection_inner (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {s t : M → ℂ} {x : M}
    (hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x)
    (ht : MDifferentiableAt I 𝓘(ℝ, ℂ) t x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℂ (s y) (t y)) x v =
      inner ℂ (exactPrequantumConnection θ ℏ s x v) (t x) +
        inner ℂ (s x) (exactPrequantumConnection θ ℏ t x v) := by
  rw [mvfderiv_inner_apply hs ht]
  simp only [exactPrequantumConnection_apply, RCLike.inner_apply', Complex.real_smul,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

end Basic

section Smooth

variable [IsManifold I 2 M]

/-- The exact-line connection is smooth when the base has a C² smooth structure. -/
instance (θ : SmoothForm I M ℝ 1) (ℏ : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (exactPrequantumConnection θ ℏ) ∞ where
  contMDiff.contMDiff {s} hs := by
    rw [contMDiffOn_univ] at hs ⊢
    have hle : (∞ : ℕ∞ω) ≤ ∞ + 1 := by simp
    have hs' : ContMDiff I 𝓘(ℝ, ℂ) ∞ s := fun x ↦ by
      simpa only [contMDiffAt_section_iff, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] using (hs x).of_le hle
    have hC : ContMDiff I (I.prod 𝓘(ℝ, ℝ →L[ℝ] ℂ)) ∞
        (fun x ↦ TotalSpace.mk' (ℝ →L[ℝ] ℂ)
          (E := fun _ : M ↦ ℝ →L[ℝ] ℂ) x
          ((1 : ℝ →L[ℝ] ℝ).smulRight (ℏ⁻¹ • (Complex.I • s x)))) := by
      intro x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      simpa [ContinuousLinearMap.inCoordinates, Function.comp_def, smul_smul, mul_assoc] using
        ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1).contMDiff.comp
          ((ContinuousLinearMap.lsmul ℝ ℂ (ℏ⁻¹ • Complex.I)).contMDiff.comp hs')).contMDiffAt
    have hA := hC.clm_bundle_comp (SmoothForm.degreeOneEquiv θ).contMDiff
    have hd := hs'.contMDiff_totalSpaceMk_mvfderiv (n := (∞ : ℕ∞ω))
    convert hd.add_section hA using 1
    funext x
    congr 1
    ext v
    simp [exactPrequantumConnection_apply, div_eq_mul_inv, mul_comm, mul_assoc]

end Smooth

section Curvature

variable [CompleteSpace E] [IsManifold I 2 M]

/-- Curvature of the exact-line connection, evaluated on differentiable
vector fields and a twice differentiable section. -/
theorem curvatureOperator_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x =
      (mextDeriv (θ : RoughForm I M ℝ 1) x ![X x, Y x] / ℏ) • (Complex.I * s x) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := 2) (by simp)
  have hs' := hs.mdifferentiableAt (by simp)
  have hθX : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ (θ : RoughForm I M ℝ 1) y ![X y]) x :=
    by simpa only [Matrix.vec_single_eq_const] using
      θ.mdifferentiableAt_apply_vectorField (V := fun _ ↦ X) (fun _ ↦ hX)
  have hθY : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ (θ : RoughForm I M ℝ 1) y ![Y y]) x :=
    by simpa only [Matrix.vec_single_eq_const] using
      θ.mdifferentiableAt_apply_vectorField (V := fun _ ↦ Y) (fun _ ↦ hY)
  have hθX' : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ (θ : RoughForm I M ℝ 1) y ![X y] / ℏ) x := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      hθX.mul (mdifferentiableAt_const (c := ℏ⁻¹))
  have hθY' : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ (θ : RoughForm I M ℝ 1) y ![Y y] / ℏ) x := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      hθY.mul (mdifferentiableAt_const (c := ℏ⁻¹))
  have hIs : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ Complex.I * s y) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).mdifferentiableAt.comp x hs'
  have hdIs : mvfderiv I (fun y ↦ Complex.I * s y) x =
      Complex.I • mvfderiv I s x := by
    simpa only [smul_eq_mul] using mvfderiv_const_smul hs' Complex.I
  have hAX : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun y ↦ ((θ : RoughForm I M ℝ 1) y ![X y] / ℏ) • (Complex.I * s y)) x := by
    convert hθX'.smul hIs using 1
  have hAY : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun y ↦ ((θ : RoughForm I M ℝ 1) y ![Y y] / ℏ) • (Complex.I * s y)) x := by
    convert hθY'.smul hIs using 1
  have hXs := mdifferentiableAt_mvfderiv_apply hs le_rfl hX
  have hYs := mdifferentiableAt_mvfderiv_apply hs le_rfl hY
  rw [CovariantDerivative.curvatureOperator_apply]
  simp only [exactPrequantumConnection_apply]
  rw [mvfderiv_fun_add hYs hAY,
    mvfderiv_fun_add hXs hAX,
    mvfderiv_fun_smul hθY' hIs,
    mvfderiv_fun_smul hθX' hIs,
    hdIs,
    mvfderiv_mlieBracket hs (by simp) hX hY,
    θ.mextDeriv_apply_one hX hY]
  have hdscale (Z : Π y : M, TangentSpace I y)
      (hZ : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ θ.1 y ![Z y]) x) :
      mvfderiv I (fun y ↦ (θ : RoughForm I M ℝ 1) y ![Z y] / ℏ) x =
        ℏ⁻¹ • mvfderiv I (fun y ↦ (θ : RoughForm I M ℝ 1) y ![Z y]) x := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      mvfderiv_const_smul hZ ℏ⁻¹
  rw [hdscale X hθX, hdscale Y hθY]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.real_smul, smul_eq_mul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- With the convention `ω = -dθ`, the exact-line curvature is `-iω/ℏ`.
Nondegeneracy is not needed for this normalization identity. -/
theorem curvatureOperator_exactPrequantumConnection_of_mextDeriv_eq_neg
    (θ : SmoothForm I M ℝ 1) (σ : SmoothForm I M ℝ 2) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hθ : mextDeriv θ.1 x = -σ.1 x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x =
      -(σ.1 x ![X x, Y x] / ℏ) • (Complex.I * s x) := by
  rw [curvatureOperator_exactPrequantumConnection θ ℏ hX hY hs, hθ]
  simp
  ring

/-- Changing the primitive by a closed one-form leaves the curvature unchanged.
This does not assert that the two connections have the same holonomy. -/
theorem curvatureOperator_exactPrequantumConnection_add_of_closed
    (θ β : SmoothForm I M ℝ 1) (ℏ : ℝ)
    {X Y : Π x : M, TangentSpace I x} {s : M → ℂ} {x : M}
    (hβ : mextDeriv β.1 x = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(ℝ, ℂ) 2 s x) :
    (exactPrequantumConnection (θ + β) ℏ).curvatureOperator X Y s x =
      (exactPrequantumConnection θ ℏ).curvatureOperator X Y s x := by
  rw [curvatureOperator_exactPrequantumConnection (θ + β) ℏ hX hY hs,
    curvatureOperator_exactPrequantumConnection θ ℏ hX hY hs]
  have hd := congrArg (fun α : SmoothForm I M ℝ 2 ↦ α.1 x)
    ((mextDerivₗ I (F := ℝ) 1).map_add θ β)
  simp only [mextDerivₗ_apply, AddMemClass.coe_add, Pi.add_apply] at hd
  rw [AddMemClass.coe_add, hd, hβ, add_zero]

end Curvature

end TauCeti
