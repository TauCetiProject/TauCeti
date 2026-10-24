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
whereas the bundled smooth pullback is stated for smooth maps. The open-set version uses
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
def complexDbar : SmoothForm 𝓘(ℝ, ℂ) ℂ ℂ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1)
    (Complex.conjCLE : ℂ →L[ℝ] ℂ))

@[simp]
theorem complexDz_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDz.1 z v = NormedSpace.fromTangentSpace z (v 0) := by
  simp [complexDz]

@[simp]
theorem complexDbar_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDbar.1 z v = conj (NormedSpace.fromTangentSpace z (v 0)) := by
  simp [complexDbar]

/-- Conjugating the coefficients exchanges the two complex coordinate forms. -/
@[simp]
theorem mapCoeff_conj_complexDz :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) complexDz = complexDbar := by
  apply Subtype.ext
  ext z v
  simp

/-- Conjugating `dbar z` gives `dz`. -/
@[simp]
theorem mapCoeff_conj_complexDbar :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) complexDbar = complexDz := by
  apply Subtype.ext
  ext z v
  simp

end SmoothForm

/-- The pullback of `dz` has the two Wirtinger coefficients. No regularity assumption is
needed for this identity of totalized derivatives. -/
theorem mpullback_complexDz_apply (f : ℂ → ℂ) (z : ℂ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z v =
      wirtingerDeriv f z 1 * NormedSpace.fromTangentSpace z (v 0) +
        conjWirtingerDeriv f z 1 * conj (NormedSpace.fromTangentSpace z (v 0)) := by
  simp only [mpullback_apply, SmoothForm.complexDz_apply, mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  simpa only [smul_eq_mul, mul_comm] using
    fderiv_eq_wirtingerDeriv_smul_add (f := f) z (NormedSpace.fromTangentSpace z (v 0))

/-- Pullback of `dbar z` is the conjugate of the pullback of `dz`, including its coefficients. -/
theorem mpullback_complexDbar_apply (f : ℂ → ℂ) (z : ℂ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDbar.1 z v =
      conj (conjWirtingerDeriv f z 1) * NormedSpace.fromTangentSpace z (v 0) +
        conj (wirtingerDeriv f z 1) * conj (NormedSpace.fromTangentSpace z (v 0)) := by
  have h := congrArg conj (mpullback_complexDz_apply f z v)
  simpa [mpullback_apply, add_comm] using h

/-- The pullback of `dz` is of type `(1,0)` at a point exactly when the conjugate Wirtinger
coefficient vanishes there. Being of type `(1,0)` means being a multiple of `dz`. -/
theorem mpullback_complexDz_eq_mul_iff (f : ℂ → ℂ) (z : ℂ) :
    (∃ a : ℂ, ∀ v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z,
      mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z v =
        a * NormedSpace.fromTangentSpace z (v 0)) ↔
        conjWirtingerDeriv f z 1 = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have h1 := ha (fun _ ↦ (NormedSpace.fromTangentSpace z).symm 1)
    have hi := ha (fun _ ↦ (NormedSpace.fromTangentSpace z).symm I)
    simp only [mpullback_complexDz_apply, ContinuousLinearEquiv.apply_symm_apply,
      map_one, mul_one] at h1
    simp only [mpullback_complexDz_apply, ContinuousLinearEquiv.apply_symm_apply,
      conj_I, mul_neg] at hi
    have h := hi.trans (congrArg (fun c : ℂ ↦ c * I) h1).symm
    have hz : 2 * conjWirtingerDeriv f z 1 * I = 0 := by linear_combination -h
    simpa using (mul_eq_zero.mp hz).resolve_right I_ne_zero
  · intro h
    exact ⟨wirtingerDeriv f z 1, fun v ↦ by rw [mpullback_complexDz_apply, h]; simp⟩

/-- A real-differentiable map is holomorphic at a point exactly when its pullback of `dz`
is a `(1,0)` covector there. -/
theorem differentiableAt_iff_mpullback_complexDz_eq_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔
      ∃ a : ℂ, ∀ v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z,
        mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z v =
          a * NormedSpace.fromTangentSpace z (v 0) := by
  rw [mpullback_complexDz_eq_mul_iff,
    differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hf]

/-- Preservation of all target `(1,0)` covectors characterizes holomorphy. The reverse
implication tests the single covector `dz`, by taking its coefficient to be `1`. -/
theorem differentiableAt_iff_mpullback_forall_mul_complexDz {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔
      ∀ a : ℂ, ∃ b : ℂ, ∀ v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z,
        mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (a • SmoothForm.complexDz.1) z v =
          b * NormedSpace.fromTangentSpace z (v 0) := by
  rw [differentiableAt_iff_mpullback_complexDz_eq_mul hf]
  constructor
  · rintro ⟨b, hb⟩ a
    exact ⟨a * b, fun v ↦ by simp [mpullback_smul, hb v, mul_assoc]⟩
  · intro h
    simpa using h 1

/-- The type-preservation criterion on an open planar chart domain, for a real-differentiable
ambient representative. No differentiability outside the domain is assumed. -/
theorem differentiableOn_iff_mpullback_complexDz_eq_mul {f : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℂ f s ↔
      ∀ z ∈ s, ∃ a : ℂ, ∀ v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z,
        mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f SmoothForm.complexDz.1 z v =
          a * NormedSpace.fromTangentSpace z (v 0) := by
  constructor
  · intro h z hz
    exact (differentiableAt_iff_mpullback_complexDz_eq_mul
      (hf.differentiableAt (hs.mem_nhds hz))).mp (h.differentiableAt (hs.mem_nhds hz))
  · intro h z hz
    exact ((differentiableAt_iff_mpullback_complexDz_eq_mul
      (hf.differentiableAt (hs.mem_nhds hz))).mpr (h z hz)).differentiableWithinAt

namespace SmoothForm

/-- A smooth real map is holomorphic at a point exactly when the fibre of its bundled
pullback of `dz` is a complex multiple of `dz`. -/
theorem differentiableAt_iff_mpullback_complexDz_eq_smul (f : ℂ → ℂ)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (z : ℂ) :
    DifferentiableAt ℂ f z ↔
      ∃ a : ℂ, (mpullback f hf complexDz).1 z = a • complexDz.1 z := by
  have hfr : DifferentiableAt ℝ f z :=
    (contMDiff_iff_contDiff.mp hf).differentiable (by simp) z
  rw [TauCeti.differentiableAt_iff_mpullback_complexDz_eq_mul hfr]
  refine exists_congr fun a ↦ ?_
  constructor
  · intro h
    ext v
    simpa using h v
  · intro h v
    have hv := congrArg (fun η ↦ η v) h
    simpa using hv

end SmoothForm

end TauCeti
