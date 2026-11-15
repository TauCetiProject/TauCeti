/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Fricke

/-!
# Self-dual newforms

The dual of a newform `f` of nebentypus `χ` is its conjugate newform `f_ρ`, whose
`q`-expansion coefficients are the complex conjugates of those of `f` and whose nebentypus is
`χ⁻¹`. A newform is **self-dual** when it equals its dual. Since a cusp form is determined by its
`q`-expansion, this happens exactly when every Fourier coefficient of `f` is real; the nebentypus
of a self-dual newform is then a real character, `χ⁻¹ = χ`. Every newform of trivial nebentypus
is self-dual.

Self-duality is the hypothesis under which the Fricke involution acts on `f` by a scalar. In
general `𝒲_N f = λ_N(f) • f_ρ` for the Fricke pseudo-eigenvalue `λ_N(f)`, so for a self-dual
newform `𝒲_N f = λ_N(f) • f`. Moreover `λ_N(f) λ_N(f_ρ) = (-1) ^ k`, so `λ_N(f) ^ 2 = (-1) ^ k`,
and the sign `i ^ k λ_N(f)` of the functional equation of `L(s, f)` is `1` or `-1`, in every
weight and for every real nebentypus.

## Main definitions

* `HeckeRing.GL2.Newform.IsSelfDual`: the newform equals its conjugate newform.

## Main results

* `HeckeRing.GL2.Newform.isSelfDual_iff_forall_im_coeff_eq_zero`: a newform is self-dual if and
  only if all of its Fourier coefficients are real.
* `HeckeRing.GL2.Newform.isSelfDual_of_χ_eq_one`: newforms of trivial nebentypus are self-dual.
* `HeckeRing.GL2.Newform.IsSelfDual.inv_χ`: a self-dual newform has a real nebentypus.
* `HeckeRing.GL2.Newform.IsSelfDual.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul`:
  `𝒲_N f = λ_N(f) • f` for a self-dual newform.
* `HeckeRing.GL2.Newform.isSelfDual_iff_exists_normalizedFrickeOperatorCusp_eq_smul`: conversely,
  a newform is an eigenvector of `𝒲_N` only if it is self-dual.
* `HeckeRing.GL2.Newform.IsSelfDual.I_zpow_mul_frickePseudoEigenvalue_eq_one_or_neg_one`: the
  sign `i ^ k λ_N(f)` of a self-dual newform is `1` or `-1`.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. **48** (1978), 221–243.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- A newform is **self-dual** when it equals its conjugate newform `f_ρ`, the newform with the
complex-conjugate Fourier coefficients and the inverse nebentypus. Equivalently, all of its
Fourier coefficients are real (`isSelfDual_iff_forall_im_coeff_eq_zero`). -/
def IsSelfDual (f : Newform N k) : Prop :=
  f.conj = f

/-- The defining equation of self-duality: `f_ρ = f`. -/
theorem isSelfDual_iff_conj_eq (f : Newform N k) : f.IsSelfDual ↔ f.conj = f :=
  Iff.rfl

/-- A newform is self-dual exactly when each of its Fourier coefficients is fixed by complex
conjugation. -/
theorem isSelfDual_iff_forall_conj_coeff_eq (f : Newform N k) :
    f.IsSelfDual ↔ ∀ n : ℕ, starRingEnd ℂ ((qExpansion 1 f.toCuspForm).coeff n) =
      (qExpansion 1 f.toCuspForm).coeff n := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Newform.ext <| CuspForm.qExpansion_injective one_pos
    (one_mem_strictPeriods_Gamma1_map N) ?_⟩
  · have hn := congrArg (fun g : Newform N k ↦ (qExpansion 1 g.toCuspForm).coeff n) h
    simpa only [qExpansion_conj, PowerSeries.coeff_map] using hn
  · ext n
    simp only [qExpansion_conj, PowerSeries.coeff_map, h]

/-- **A newform is self-dual if and only if all of its Fourier coefficients are real.** -/
theorem isSelfDual_iff_forall_im_coeff_eq_zero (f : Newform N k) :
    f.IsSelfDual ↔ ∀ n : ℕ, ((qExpansion 1 f.toCuspForm).coeff n).im = 0 := by
  simp only [isSelfDual_iff_forall_conj_coeff_eq, Complex.conj_eq_iff_im]

/-- **A newform of trivial nebentypus is self-dual.** -/
theorem isSelfDual_of_χ_eq_one (f : Newform N k) (hχ : f.χ = 1) : f.IsSelfDual :=
  f.conj_eq_self_of_χ_eq_one hχ

namespace IsSelfDual

variable {f : Newform N k}

/-- **The nebentypus of a self-dual newform is real**: it equals its inverse, the nebentypus of
the conjugate newform. -/
theorem inv_χ (hf : f.IsSelfDual) : f.χ⁻¹ = f.χ := by
  rw [← χ_conj, hf]

/-- **The Fricke involution acts on a self-dual newform by its pseudo-eigenvalue**:
`𝒲_N f = λ_N(f) • f`. -/
theorem normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul (hf : f.IsSelfDual) :
    normalizedFrickeOperatorCusp k f.toCuspForm = f.frickePseudoEigenvalue • f.toCuspForm := by
  rw [f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul, hf]

/-- **The square of the pseudo-eigenvalue of a self-dual newform** is `λ_N(f) ^ 2 = (-1) ^ k`. -/
theorem frickePseudoEigenvalue_sq (hf : f.IsSelfDual) :
    f.frickePseudoEigenvalue ^ 2 = (-1 : ℂ) ^ k := by
  have h := f.frickePseudoEigenvalue_mul_frickePseudoEigenvalue_conj
  rwa [hf, ← sq] at h

/-- **The sign `i ^ k λ_N(f)` of a self-dual newform is `1` or `-1`**, in every weight: its square
is `i ^ (2k) λ_N(f) ^ 2 = (-1) ^ k (-1) ^ k = 1`. -/
theorem I_zpow_mul_frickePseudoEigenvalue_eq_one_or_neg_one (hf : f.IsSelfDual) :
    Complex.I ^ k * f.frickePseudoEigenvalue = 1 ∨
      Complex.I ^ k * f.frickePseudoEigenvalue = -1 := by
  refine sq_eq_one_iff.mp ?_
  rw [mul_pow, hf.frickePseudoEigenvalue_sq, sq (Complex.I ^ k), ← mul_zpow, Complex.I_mul_I,
    ← mul_zpow, neg_one_mul, neg_neg, one_zpow]

end IsSelfDual

/-- **A newform is an eigenvector of the Fricke involution exactly when it is self-dual.** Since
`𝒲_N f = λ_N(f) • f_ρ`, an equation `𝒲_N f = c • f` makes `f_ρ` a multiple of `f`; comparing
the normalized first Fourier coefficients gives `c = λ_N(f)` and `f_ρ = f`. -/
theorem isSelfDual_iff_exists_normalizedFrickeOperatorCusp_eq_smul (f : Newform N k) :
    f.IsSelfDual ↔ ∃ c : ℂ, normalizedFrickeOperatorCusp k f.toCuspForm = c • f.toCuspForm := by
  refine ⟨fun hf ↦ ⟨_, hf.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul⟩, ?_⟩
  rintro ⟨c, hc⟩
  have h := f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul.symm.trans hc
  have h1 := congrArg (fun g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k ↦ (qExpansion 1 g).coeff 1) h
  simp only [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
    (one_mem_strictPeriods_Gamma1_map N), PowerSeries.coeff_smul, qExpansion_coeff_one,
    smul_eq_mul, mul_one] at h1
  have hne : f.frickePseudoEigenvalue ≠ 0 :=
    norm_ne_zero_iff.mp (f.norm_frickePseudoEigenvalue ▸ one_ne_zero)
  rw [← h1] at h
  exact Newform.ext (smul_right_injective _ hne h)

end HeckeRing.GL2.Newform
