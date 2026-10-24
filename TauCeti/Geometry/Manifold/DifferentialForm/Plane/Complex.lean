/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff

/-!
# Complex coordinate one-forms and their pullback

The coordinate forms `dz` and `dbar z` on the real manifold `ℂ` take a tangent vector to
itself and to its conjugate. They use the existing `SmoothForm` carrier, with complex
coefficients and real tangent spaces. Pullback by a real-differentiable map has the usual
Wirtinger coefficients: `f⁎dz = f_z dz + f_barz dbar z`.

A covector is of type `(1,0)` precisely when it is a complex multiple of `dz`. We prove
that pullback preserves these covectors exactly when the map is complex differentiable;
the converse only needs to test `dz`. The pointwise test needs only real differentiability,
and also applies to the bundled pullback of a smooth map. The open-set version uses
ambient representatives, so it applies in planar charts without extending a map smoothly
outside its chart domain.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter I.
-/

public noncomputable section

open Complex Set
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

namespace SmoothForm

/-- The complex-valued coordinate one-form `dz` on the real manifold `ℂ`. -/
def complexDz : SmoothForm 𝓘(ℝ, ℂ) ℂ ℂ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1)
    (ContinuousLinearMap.id ℝ ℂ))

/-- The complex-valued coordinate one-form `dbar z` on the real manifold `ℂ`. -/
def complexDzBar : SmoothForm 𝓘(ℝ, ℂ) ℂ ℂ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1)
    (Complex.conjCLE : ℂ →L[ℝ] ℂ))

@[simp]
theorem complexDz_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDz.1 z v = NormedSpace.fromTangentSpace z (v 0) := by
  simp [complexDz]

@[simp]
theorem complexDzBar_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDzBar.1 z v = conj (NormedSpace.fromTangentSpace z (v 0)) := by
  simp [complexDzBar]

/-- Conjugating the coefficients exchanges the two complex coordinate forms. -/
@[simp]
theorem mapCoeff_conj_complexDz :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) complexDz = complexDzBar := by
  apply Subtype.ext
  ext z v
  simp

/-- Conjugating `dbar z` gives `dz`. -/
@[simp]
theorem mapCoeff_conj_complexDzBar :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) complexDzBar = complexDz := by
  apply Subtype.ext
  ext z v
  simp

end SmoothForm

/-- The pullback of `dz` has the two Wirtinger coefficients. No regularity assumption is
needed for this identity of totalized derivatives. -/
theorem mpullback_complexDz (f : ℂ → ℂ) (z : ℂ) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z =
      wirtingerDeriv f z 1 • SmoothForm.complexDz.1 z +
        conjWirtingerDeriv f z 1 • SmoothForm.complexDzBar.1 z := by
  ext v
  simp only [mpullback_apply, SmoothForm.complexDz_apply, mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.complexDzBar_apply, smul_eq_mul]
  simpa only [smul_eq_mul, mul_comm] using
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv
      (f := f) z (NormedSpace.fromTangentSpace z (v 0))

/-- Evaluation of the Wirtinger pullback formula for `dz` on a tangent vector. -/
theorem mpullback_complexDz_apply (f : ℂ → ℂ) (z : ℂ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z v =
      wirtingerDeriv f z 1 * NormedSpace.fromTangentSpace z (v 0) +
        conjWirtingerDeriv f z 1 * conj (NormedSpace.fromTangentSpace z (v 0)) := by
  simp only [mpullback_complexDz, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.complexDz_apply,
    SmoothForm.complexDzBar_apply, smul_eq_mul]

/-- Pullback of `dbar z` is the conjugate of the pullback of `dz`, including its coefficients. -/
theorem mpullback_complexDzBar (f : ℂ → ℂ) (z : ℂ) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDzBar.1 z =
      conj (conjWirtingerDeriv f z 1) • SmoothForm.complexDz.1 z +
        conj (wirtingerDeriv f z 1) • SmoothForm.complexDzBar.1 z := by
  conv_lhs =>
    rw [← SmoothForm.mapCoeff_conj_complexDz, SmoothForm.coe_mapCoeff, mpullback_mapCoeff]
  ext v
  simp only [RoughForm.mapCoeff_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    mpullback_complexDz_apply,
    map_add, map_mul, starRingEnd_self_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.complexDz_apply,
    SmoothForm.complexDzBar_apply, smul_eq_mul]
  rw [add_comm]

/-- Evaluation of the Wirtinger pullback formula for `dbar z` on a tangent vector. -/
theorem mpullback_complexDzBar_apply (f : ℂ → ℂ) (z : ℂ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDzBar.1 z v =
      conj (conjWirtingerDeriv f z 1) * NormedSpace.fromTangentSpace z (v 0) +
        conj (wirtingerDeriv f z 1) * conj (NormedSpace.fromTangentSpace z (v 0)) := by
  simp only [mpullback_complexDzBar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.complexDz_apply,
    SmoothForm.complexDzBar_apply, smul_eq_mul]

/-- The pullback of `dz` is of type `(1,0)` at a point exactly when the conjugate Wirtinger
coefficient vanishes there. Being of type `(1,0)` means being a multiple of `dz`. -/
theorem mpullback_complexDz_eq_smul_iff (f : ℂ → ℂ) (z : ℂ) :
    (∃ a : ℂ, mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z =
      a • SmoothForm.complexDz.1 z) ↔ conjWirtingerDeriv f z 1 = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrArg (fun η ↦ η (fun _ ↦ (NormedSpace.fromTangentSpace z).symm 1)) ha
    have hi := congrArg (fun η ↦ η (fun _ ↦ (NormedSpace.fromTangentSpace z).symm I)) ha
    simp only [mpullback_complexDz_apply, ContinuousAlternatingMap.smul_apply,
      SmoothForm.complexDz_apply, ContinuousLinearEquiv.apply_symm_apply,
      smul_eq_mul, map_one, mul_one] at h1
    simp only [mpullback_complexDz_apply, ContinuousAlternatingMap.smul_apply,
      SmoothForm.complexDz_apply, ContinuousLinearEquiv.apply_symm_apply,
      smul_eq_mul, conj_I, mul_neg] at hi
    have h := hi.trans (congrArg (fun c : ℂ ↦ c * I) h1).symm
    have hz : 2 * conjWirtingerDeriv f z 1 * I = 0 := by linear_combination -h
    simpa using (mul_eq_zero.mp hz).resolve_right I_ne_zero
  · intro h
    exact ⟨wirtingerDeriv f z 1, by rw [mpullback_complexDz, h, zero_smul, add_zero]⟩

/-- A real-differentiable map is holomorphic at a point exactly when its pullback of `dz`
is a `(1,0)` covector there. -/
theorem differentiableAt_iff_mpullback_complexDz_eq_smul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔
      ∃ a : ℂ, mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z =
        a • SmoothForm.complexDz.1 z := by
  rw [mpullback_complexDz_eq_smul_iff,
    differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hf]

/-- Preservation of all target `(1,0)` covectors characterizes holomorphy. The reverse
implication tests the single covector `dz`, by taking its coefficient to be `1`. -/
theorem differentiableAt_iff_forall_mpullback_smul_complexDz_eq_smul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔
      ∀ a : ℂ, ∃ b : ℂ,
        mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (a • SmoothForm.complexDz.1) z =
          b • SmoothForm.complexDz.1 z := by
  rw [differentiableAt_iff_mpullback_complexDz_eq_smul hf]
  constructor
  · rintro ⟨b, hb⟩ a
    exact ⟨a * b, by rw [mpullback_smul]; simp only [Pi.smul_apply, hb, smul_smul]⟩
  · intro h
    simpa using h 1

/-- The type-preservation criterion on an open planar chart domain, for a real-differentiable
ambient representative. No differentiability outside the domain is assumed. -/
theorem differentiableOn_iff_mpullback_complexDz_eq_smul {f : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℂ f s ↔
      ∀ z ∈ s, ∃ a : ℂ, mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z =
        a • SmoothForm.complexDz.1 z := by
  constructor
  · intro h z hz
    exact (differentiableAt_iff_mpullback_complexDz_eq_smul
      (hf.differentiableAt (hs.mem_nhds hz))).mp (h.differentiableAt (hs.mem_nhds hz))
  · intro h z hz
    exact ((differentiableAt_iff_mpullback_complexDz_eq_smul
      (hf.differentiableAt (hs.mem_nhds hz))).mpr (h z hz)).differentiableWithinAt

end TauCeti
