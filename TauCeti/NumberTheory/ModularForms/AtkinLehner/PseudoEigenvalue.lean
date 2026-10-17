/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Newform
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Atkin–Li pseudo-eigenvalues of newforms

Let `f` be a newform of level `N` and let `Q` be an exact divisor of `N`. The normalized slash
by the Atkin–Li matrix for `Q` carries `f` to a scalar multiple of the normalized newform
`f.atkinLehnerTransform h`. This file names that scalar
`HeckeRing.GL2.Newform.atkinLehnerPseudoEigenvalue` and proves its characteristic equation,
uniqueness, and nonvanishing.

Applying the operator twice gives the precise product of the pseudo-eigenvalues of `f` and its
Atkin–Lehner transform. If the nebentypus splits as `χ = ψ * φ` along
`N = Q * (N / Q)`, the product is

`ψ(-1) * φ(Q)⁻¹`.

In particular the product of their complex norms is one.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  W-operators*, Invent. Math. **48** (1978), 221–243, §1.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace HeckeRing.GL2

open TauCeti

variable {N Q : ℕ} [NeZero N] {k : ℤ}

namespace Newform

/-- **The Atkin–Li pseudo-eigenvalue at an exact divisor `Q`**: the scalar in the normalized
Atkin–Lehner equation

`𝒲_Q f = λ_Q(f) * f.atkinLehnerTransform h`.

The operator uses `TauCeti.atkinLiMatrix`, whose upper-left and upper-right parameters are both
one. This pins the matrix-dependent scalar to Atkin and Li's convention. -/
def atkinLehnerPseudoEigenvalue (f : Newform N k) (h : Q ∥ N) : ℂ :=
  atkinLehnerNormalizer Q k *
    (qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd
      (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm)).coeff 1

/-- **The pseudo-eigenvalue equation.** The Petersson-normalized slash by the Atkin–Li matrix
sends a newform to its pseudo-eigenvalue times the canonical transported newform. -/
theorem atkinLehnerNormalizer_smul_atkinLiOperatorGamma1Cusp_eq_pseudoEigenvalue_smul
    (f : Newform N k) (h : Q ∥ N) :
    atkinLehnerNormalizer Q k •
        atkinLehnerOperatorGamma1Cusp h.pos h.dvd
          (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm =
      f.atkinLehnerPseudoEigenvalue h • (f.atkinLehnerTransform h).toCuspForm := by
  simpa [atkinLehnerPseudoEigenvalue] using
    f.atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp_eq_smul h
      (isAtkinLehnerMatrix_atkinLiMatrix h)

/-- A scalar satisfying the normalized Atkin–Li equation is the pseudo-eigenvalue. -/
theorem atkinLehnerPseudoEigenvalue_eq_of_smul_atkinLiOperatorGamma1Cusp_eq_smul
    (f : Newform N k) (h : Q ∥ N) {c : ℂ}
    (hc : atkinLehnerNormalizer Q k •
        atkinLehnerOperatorGamma1Cusp h.pos h.dvd
          (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm =
      c • (f.atkinLehnerTransform h).toCuspForm) :
    f.atkinLehnerPseudoEigenvalue h = c :=
  smul_left_injective ℂ (f.atkinLehnerTransform h).ne_zero
    ((f.atkinLehnerNormalizer_smul_atkinLiOperatorGamma1Cusp_eq_pseudoEigenvalue_smul h).symm
      |>.trans hc)

/-- The Atkin–Li pseudo-eigenvalue is nonzero. -/
theorem atkinLehnerPseudoEigenvalue_ne_zero (f : Newform N k) (h : Q ∥ N) :
    f.atkinLehnerPseudoEigenvalue h ≠ 0 := by
  intro hzero
  have hsmul : atkinLehnerNormalizer Q k •
      atkinLehnerOperatorGamma1Cusp h.pos h.dvd
        (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm = 0 := by
    rw [f.atkinLehnerNormalizer_smul_atkinLiOperatorGamma1Cusp_eq_pseudoEigenvalue_smul h,
      hzero, zero_smul]
  exact f.atkinLehnerOperatorGamma1Cusp_ne_zero h.pos h.dvd
    (isAtkinLehnerMatrix_atkinLiMatrix h)
    ((smul_eq_zero.mp hsmul).resolve_left (atkinLehnerNormalizer_ne_zero h.ne_zero k))

/-- **Double transport product formula.** Suppose the nebentypus splits along the exact-divisor
factorization as `χ = ψ * φ`. The pseudo-eigenvalues of `f` and its transported newform
multiply to `ψ(-1) * φ(Q)⁻¹`. This is the normalized form of Atkin and Li's square
formula for their matrix convention. -/
theorem atkinLehnerPseudoEigenvalue_mul_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)
    (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    f.atkinLehnerPseudoEigenvalue h *
        (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h =
      (ψ (-1) *
        (φ (ZMod.unitOfCoprime Q h.coprime))⁻¹ : ℂˣ) := by
  let W := atkinLehnerOperatorGamma1Cusp h.pos h.dvd
    (isAtkinLehnerMatrix_atkinLiMatrix h) k
  let A := atkinLehnerNormalizer Q k • W
  have hf : A f.toCuspForm =
      f.atkinLehnerPseudoEigenvalue h • (f.atkinLehnerTransform h).toCuspForm := by
    exact f.atkinLehnerNormalizer_smul_atkinLiOperatorGamma1Cusp_eq_pseudoEigenvalue_smul h
  have hg : A (f.atkinLehnerTransform h).toCuspForm =
      (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h • f.toCuspForm := by
    dsimp only [A, W, LinearMap.smul_apply]
    simpa using atkinLehnerNormalizer_smul_atkinLiOperatorGamma1Cusp_eq_pseudoEigenvalue_smul
      (f.atkinLehnerTransform h) h
  have hA2 : A (A f.toCuspForm) =
      (↑(ψ (-1) * (φ (ZMod.unitOfCoprime Q h.coprime))⁻¹) : ℂ) •
        f.toCuspForm := by
    simp only [A, W, LinearMap.smul_apply, map_smul, smul_smul]
    rw [atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp_of_mem_cuspFormCharSpace
      h.pos h.dvd (isAtkinLehnerMatrix_atkinLiMatrix h) (intCast_atkinLiMatrix_one_one h)
      ψ φ (hχ ▸ f.mem_charSpace), smul_smul]
    rw [← mul_assoc, ← pow_two, atkinLehnerNormalizer_sq_mul h.ne_zero, one_mul]
  apply smul_left_injective ℂ f.ne_zero
  calc
    (f.atkinLehnerPseudoEigenvalue h *
          (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h) • f.toCuspForm =
        f.atkinLehnerPseudoEigenvalue h •
          ((f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h • f.toCuspForm) := by
            rw [smul_smul]
    _ = f.atkinLehnerPseudoEigenvalue h • A (f.atkinLehnerTransform h).toCuspForm := by rw [hg]
    _ = A (f.atkinLehnerPseudoEigenvalue h •
          (f.atkinLehnerTransform h).toCuspForm) := by rw [map_smul]
    _ = A (A f.toCuspForm) := by rw [hf]
    _ = (↑(ψ (-1) * (φ (ZMod.unitOfCoprime Q h.coprime))⁻¹) : ℂ) •
          f.toCuspForm := hA2

/-- The norms of the two pseudo-eigenvalues exchanged by Atkin--Lehner transport multiply to
one. -/
theorem norm_atkinLehnerPseudoEigenvalue_mul_norm_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)
    (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    norm (f.atkinLehnerPseudoEigenvalue h) *
        norm ((f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h) = 1 := by
  have hψ := DirichletCharacter.unit_norm_eq_one (MulChar.ofUnitHom ψ) (-1)
  have hφ := DirichletCharacter.unit_norm_eq_one (MulChar.ofUnitHom φ)
    (ZMod.unitOfCoprime Q h.coprime)
  rw [MulChar.ofUnitHom_coe] at hψ hφ
  have hnorm := congrArg norm
    (f.atkinLehnerPseudoEigenvalue_mul_atkinLehnerTransform h ψ φ hχ)
  simpa [norm_mul, norm_inv, hψ, hφ] using hnorm

end Newform

end HeckeRing.GL2
