/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

import Mathlib.Analysis.Normed.Algebra.GelfandMazur

/-!
# Rigidity of real-valued absolute values on the complex numbers

An absolute value `w : AbsoluteValue ℂ ℝ` bounded above by the ordinary absolute value on `ℝ`
(`∀ x : ℝ, w x ≤ |x|`) coincides with the Euclidean norm `‖·‖` on all of `ℂ`. In particular, an
absolute value on `ℂ` that restricts to `|·|` on `ℝ` is `‖·‖`
(`AbsoluteValue.eq_norm_of_apply_ofReal`).

This upgrades the `ℝ`-algebra isomorphism supplied by the real Gelfand–Mazur theorem
(`NormedAlgebra.Real.nonempty_algEquiv_or`) to an isometry: every `ℝ`-algebra equivalence from a
normed field `F` over `ℝ` to `ℝ` or `ℂ` preserves the norm
(`NormedAlgebra.Real.norm_algEquiv_real`, `NormedAlgebra.Real.norm_algEquiv_complex`), so every
normed field over `ℝ` — or more generally every normed field equipped with a norm-preserving ring
homomorphism from `ℝ` — admits a norm-preserving embedding into `ℂ`
(`NormedAlgebra.Real.exists_algHom_complex_norm_eq`,
`NormedField.exists_ringHom_complex_norm_eq`).

## Proof outline

From `Complex.I ^ 2 = -1` and `w (-1) = 1` one obtains `w Complex.I ≤ 1`, and decomposing
`u = u.re + u.im * Complex.I` gives the coarse linear bound `w u ≤ 2 * ‖u‖`. Applying this bound
to powers `z ^ n` yields `w z ^ n ≤ 2 * ‖z‖ ^ n` for every `n : ℕ`, which forces `w z ≤ ‖z‖` by
the Archimedean property of `ℝ`. Applying `w z⁻¹ ≤ ‖z⁻¹‖` to `z ≠ 0` gives the reverse inequality.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal_le`: if `w x ≤ |x|` for every `x : ℝ`, then `w z = ‖z‖`
  for every `z : ℂ`.
* `AbsoluteValue.eq_norm_of_apply_ofReal`: if `w x = |x|` for every `x : ℝ`, then `w z = ‖z‖`
  for every `z : ℂ`.
* `AbsoluteValue.eq_toAbsoluteValue_iff_forall_apply_ofReal`: `w = NormedField.toAbsoluteValue ℂ`
  if and only if `w x = |x|` for every `x : ℝ`.
* `NormedAlgebra.Real.norm_algEquiv_real`, `NormedAlgebra.Real.abs_algEquiv_real`, and
  `NormedAlgebra.Real.norm_algEquiv_complex`: for a normed field `F` that is a normed `ℝ`-algebra,
  any `ℝ`-algebra equivalence `F ≃ₐ[ℝ] ℝ` or `F ≃ₐ[ℝ] ℂ` preserves the norm (with the real case
  holding more generally for any seminormed ring `F` with `NormOneClass F` and
  `NormedAlgebra ℝ F`).
* `NormedAlgebra.Real.exists_algHom_complex_norm_eq` and
  `NormedField.exists_ringHom_complex_norm_eq`: every normed field over `ℝ` (or equipped with a
  norm-preserving ring homomorphism from `ℝ`) admits a norm-preserving homomorphism into `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2–1.3.
-/

public section

namespace AbsoluteValue

private theorem apply_le_norm_of_apply_ofReal_le {w : AbsoluteValue ℂ ℝ}
    (hw : ∀ x : ℝ, w x ≤ |x|) (z : ℂ) : w z ≤ ‖z‖ := by
  have hI : w Complex.I ≤ 1 := by
    have hI2 : w Complex.I ^ 2 ≤ 1 ^ 2 := by
      rw [← map_pow, Complex.I_sq]
      simp
    exact (sq_le_sq₀ (w.nonneg _) zero_le_one).mp hI2
  have h2 (u : ℂ) : w u ≤ 2 * ‖u‖ := by
    calc w u = w (u.re + u.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ w u.re + w (u.im * Complex.I) := w.add_le _ _
      _ = w u.re + w u.im * w Complex.I := by rw [map_mul]
      _ ≤ |u.re| + |u.im| * 1 :=
        add_le_add (hw u.re) (mul_le_mul (hw u.im) hI (w.nonneg _) (abs_nonneg _))
      _ ≤ ‖u‖ + ‖u‖ * 1 := by
        gcongr
        exacts [Complex.abs_re_le_norm u, Complex.abs_im_le_norm u]
      _ = 2 * ‖u‖ := by ring
  by_contra! hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) ((one_lt_div hz0).mpr hz)
  rw [div_pow, lt_div_iff₀ (pow_pos hz0 n), ← map_pow, ← norm_pow] at hn
  exact hn.not_ge (h2 (z ^ n))

/-- An absolute value on `ℂ` bounded above by `|·|` on `ℝ` coincides with the Euclidean norm `‖·‖`
on all of `ℂ`. -/
theorem eq_norm_of_apply_ofReal_le {w : AbsoluteValue ℂ ℝ}
    (hw : ∀ x : ℝ, w x ≤ |x|) (z : ℂ) : w z = ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · refine le_antisymm (apply_le_norm_of_apply_ofReal_le hw z) ?_
    have hinv := apply_le_norm_of_apply_ofReal_le hw z⁻¹
    rwa [map_inv₀, norm_inv, inv_le_inv₀ (w.pos hz) (norm_pos_iff.mpr hz)] at hinv

/-- An absolute value on `ℂ` that restricts to `|·|` on `ℝ` coincides with the Euclidean norm `‖·‖`
on all of `ℂ`. -/
theorem eq_norm_of_apply_ofReal {w : AbsoluteValue ℂ ℝ}
    (hw : ∀ x : ℝ, w x = |x|) (z : ℂ) : w z = ‖z‖ :=
  eq_norm_of_apply_ofReal_le (fun x ↦ (hw x).le) z

/-- An absolute value on `ℂ` is the Euclidean norm absolute value if and only if it restricts to
`|·|` on `ℝ`. -/
theorem eq_toAbsoluteValue_iff_forall_apply_ofReal {w : AbsoluteValue ℂ ℝ} :
    w = NormedField.toAbsoluteValue ℂ ↔ ∀ x : ℝ, w x = |x| := by
  refine ⟨?_, fun hw ↦ ext (eq_norm_of_apply_ofReal hw)⟩
  rintro rfl x
  simp [NormedField.toAbsoluteValue]

/-! Bounding `w` by `|·|` only on `ℤ` does not force `w` to be `‖·‖`: the trivial absolute value on
`ℂ` satisfies `w n ≤ |(n : ℝ)|` for every integer `n`, since `ℝ` contains no reciprocals in `ℤ` of
elements larger than `1`. -/

open scoped Classical in
example : (∀ n : ℤ, AbsoluteValue.trivial (n : ℂ) ≤ |(n : ℝ)|) ∧
    AbsoluteValue.trivial (2 : ℂ) ≠ ‖(2 : ℂ)‖ := by
  refine ⟨fun n ↦ ?_, by norm_num [AbsoluteValue.trivial_apply]⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [AbsoluteValue.trivial_apply (Int.cast_ne_zero.mpr hn)]
    exact_mod_cast Int.one_le_abs hn

end AbsoluteValue

namespace NormedAlgebra.Real

/-- Every `ℝ`-algebra equivalence from a seminormed `ℝ`-algebra `F` with `‖(1 : F)‖ = 1` to `ℝ`
preserves the norm. -/
theorem norm_algEquiv_real {F : Type*} [SeminormedRing F] [NormOneClass F] [NormedAlgebra ℝ F]
    (σ : F ≃ₐ[ℝ] ℝ) (x : F) : ‖σ x‖ = ‖x‖ := by
  have hx : algebraMap ℝ F (σ x) = x := by
    simpa using (σ.symm.commutes (σ x)).symm
  simpa [hx] using (norm_algebraMap' F (σ x)).symm

/-- Every `ℝ`-algebra equivalence from a seminormed `ℝ`-algebra `F` with `‖(1 : F)‖ = 1` to `ℝ`
sends each element to a real number whose absolute value equals its norm. -/
@[simp]
theorem abs_algEquiv_real {F : Type*} [SeminormedRing F] [NormOneClass F] [NormedAlgebra ℝ F]
    (σ : F ≃ₐ[ℝ] ℝ) (x : F) : |σ x| = ‖x‖ := by
  rw [← Real.norm_eq_abs, norm_algEquiv_real]

/-- Every `ℝ`-algebra equivalence from a normed field `F` over `ℝ` to `ℂ` preserves the norm. -/
@[simp]
theorem norm_algEquiv_complex {F : Type*} [NormedField F] [NormedAlgebra ℝ F]
    (σ : F ≃ₐ[ℝ] ℂ) (x : F) : ‖σ x‖ = ‖x‖ := by
  let u : AbsoluteValue ℂ ℝ :=
    (NormedField.toAbsoluteValue F).comp (f := σ.symm.toRingHom) σ.symm.injective
  have hu (r : ℝ) : u r = |r| := by
    have hr : σ.symm (r : ℂ) = algebraMap ℝ F r := σ.symm.commutes r
    simp [u, NormedField.toAbsoluteValue, hr, Real.norm_eq_abs]
  simpa [u, NormedField.toAbsoluteValue] using
    (AbsoluteValue.eq_norm_of_apply_ofReal hu (σ x)).symm

/-- **Isometric real Gelfand–Mazur embedding.** Every normed field `F` that is a normed
`ℝ`-algebra admits a norm-preserving `ℝ`-algebra homomorphism into `ℂ`. -/
theorem exists_algHom_complex_norm_eq (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →ₐ[ℝ] ℂ, ∀ x : F, ‖φ x‖ = ‖x‖ := by
  rcases nonempty_algEquiv_or F with ⟨⟨σ⟩⟩ | ⟨⟨σ⟩⟩
  · exact ⟨(Algebra.ofId ℝ ℂ).comp σ.toAlgHom, fun x ↦ by simp⟩
  · exact ⟨σ.toAlgHom, norm_algEquiv_complex σ⟩

end NormedAlgebra.Real

/-- Every normed field `E` equipped with a norm-preserving ring homomorphism from `ℝ` admits a
norm-preserving ring homomorphism into `ℂ`. -/
theorem NormedField.exists_ringHom_complex_norm_eq {E : Type*} [NormedField E]
    (f : ℝ →+* E) (hf : ∀ r : ℝ, ‖f r‖ = |r|) :
    ∃ φ : E →+* ℂ, ∀ x : E, ‖φ x‖ = ‖x‖ := by
  let : Algebra ℝ E := f.toAlgebra
  let : NormedAlgebra ℝ E :=
    ⟨fun r x ↦ by rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, norm_mul, hf,
      Real.norm_eq_abs]⟩
  obtain ⟨φ, hφ⟩ := NormedAlgebra.Real.exists_algHom_complex_norm_eq E
  exact ⟨φ.toRingHom, hφ⟩
