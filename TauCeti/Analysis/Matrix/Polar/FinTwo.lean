/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.SpecialLinear
public import TauCeti.Analysis.Matrix.PosSemidef.FinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The polar decomposition of `SL(2, 𝕜)` in closed form

In size two the square root of a positive semidefinite matrix `H` of determinant one is
`CFC.sqrt H = (H + 1) / √(tr H + 2)` (`Matrix.PosSemidef.sqrt_fin_two_of_det_eq_one`, a case of
`Matrix.PosSemidef.sqrt_fin_two`), since the Cayley–Hamilton identity `H ^ 2 = (tr H) H - 1` gives
`(H + 1) ^ 2 = (tr H + 2) H`. For a matrix `g` whose determinant has norm one, such as
`g ∈ SL(2, 𝕜)`, `H = g gᴴ` and `H = gᴴ g` have determinant one, so the two positive factors of the
polar decompositions `g = √(g gᴴ) U = U √(gᴴ g)` are

`√(g gᴴ) = (g gᴴ + 1) / √(tr (g gᴴ) + 2)`, `√(gᴴ g) = (gᴴ g + 1) / √(tr (gᴴ g) + 2)`

(`Matrix.sqrt_mul_star_fin_two_of_norm_det_eq_one`,
`Matrix.sqrt_star_mul_fin_two_of_norm_det_eq_one`).
These are the square roots of the continuous functional calculus, so the explicit formula computes
the positive factors of `TauCeti.Analysis.Matrix.Polar`, rather than giving another square root.
The two traces agree, `tr (g gᴴ) = tr (gᴴ g) = ∑ |gᵢⱼ| ^ 2`.

The unitary factor is then explicit as well. Multiplying the Cayley–Hamilton identity
`(g gᴴ) ^ 2 = t g gᴴ - 1` on the right by `(g⁻¹)ᴴ` gives `g gᴴ g = t g - (g⁻¹)ᴴ`, so
`(g gᴴ + 1) (g + (g⁻¹)ᴴ) = (t + 2) g`, and the polar retraction `SL(2, 𝕜) → SU(2)` of
`TauCeti.Analysis.Matrix.Polar.SpecialLinear` is

`U = (g + (g⁻¹)ᴴ) / √(tr (g gᴴ) + 2)`

(`Matrix.SpecialLinearGroup.coe_polarRetraction_fin_two`). For `g = [[a, b], [c, d]]` this is the
matrix `[[a + conj d, b - conj c], [c - conj b, d + conj a]]` divided by
`√(|a|² + |b|² + |c|² + |d|² + 2)`, in the standard form `[[α, β], [-conj β, conj α]]` of a matrix
of `SU(2)`. The formula is visibly continuous and odd in `g`, in accordance with
`Matrix.SpecialLinearGroup.coe_polarRetraction_neg`.

For example, for `g = diag(2, 1/2)` the trace of `g gᴴ = diag(4, 1/4)` is `17/4`, so
`√(tr (g gᴴ) + 2) = 5/2` and `√(g gᴴ) = (diag(4, 1/4) + 1) / (5/2) = diag(2, 1/2) = g`, a positive
matrix with unitary factor `1`.

## Main results

* `Matrix.sqrt_mul_star_fin_two_of_norm_det_eq_one`,
  `Matrix.sqrt_star_mul_fin_two_of_norm_det_eq_one`: the positive factors of the polar
  decompositions of a matrix whose determinant has norm one.
* `Matrix.SpecialLinearGroup.coe_polarRetraction_fin_two`: the unitary factor of `g ∈ SL(2, 𝕜)` is
  `(g + (g⁻¹)ᴴ) / √(tr (g gᴴ) + 2)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5 (the polar decomposition).
-/

public section

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The left positive factor of a matrix of determinant of norm one.** If `|det A| = 1`, as for
`A ∈ SL(2, 𝕜)`, then `√(A Aᴴ) = (A Aᴴ + 1) / √(tr (A Aᴴ) + 2)`. -/
theorem sqrt_mul_star_fin_two_of_norm_det_eq_one {A : Matrix (Fin 2) (Fin 2) 𝕜}
    (hA : ‖A.det‖ = 1) :
    CFC.sqrt (A * star A) = (√(RCLike.re (A * star A).trace + 2))⁻¹ • (A * star A + 1) :=
  (nonneg_iff_posSemidef.1 (mul_star_self_nonneg A)).sqrt_fin_two_of_det_eq_one
    (by rw [det_mul_star, hA, RCLike.ofReal_one, one_pow])

/-- **The right positive factor of a matrix of determinant of norm one.** If `|det A| = 1`, as for
`A ∈ SL(2, 𝕜)`, then `√(Aᴴ A) = (Aᴴ A + 1) / √(tr (Aᴴ A) + 2)`. -/
theorem sqrt_star_mul_fin_two_of_norm_det_eq_one {A : Matrix (Fin 2) (Fin 2) 𝕜}
    (hA : ‖A.det‖ = 1) :
    CFC.sqrt (star A * A) = (√(RCLike.re (star A * A).trace + 2))⁻¹ • (star A * A + 1) := by
  have h := sqrt_mul_star_fin_two_of_norm_det_eq_one (A := star A)
    (by rwa [star_eq_conjTranspose, det_conjTranspose, norm_star])
  rwa [star_star] at h

end Matrix

namespace Matrix.SpecialLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For `g ∈ SL(2, 𝕜)`, `(g gᴴ + 1) (g + (g⁻¹)ᴴ) = (tr (g gᴴ) + 2) g`: by Cayley–Hamilton,
`g gᴴ g = tr (g gᴴ) g - (g⁻¹)ᴴ`. -/
private theorem mul_star_add_one_mul_add_star_inv (g : SpecialLinearGroup (Fin 2) 𝕜) :
    ((g : Matrix (Fin 2) (Fin 2) 𝕜) * star (g : Matrix (Fin 2) (Fin 2) 𝕜) + 1) *
        ((g : Matrix (Fin 2) (Fin 2) 𝕜) +
          star ((g⁻¹ : SpecialLinearGroup (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)) =
      (((g : Matrix (Fin 2) (Fin 2) 𝕜) * star (g : Matrix (Fin 2) (Fin 2) 𝕜)).trace + 2) •
        (g : Matrix (Fin 2) (Fin 2) 𝕜) := by
  set A : Matrix (Fin 2) (Fin 2) 𝕜 := (g : Matrix (Fin 2) (Fin 2) 𝕜)
  set B : Matrix (Fin 2) (Fin 2) 𝕜 :=
    ((g⁻¹ : SpecialLinearGroup (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
  have hstar : star A * star B = 1 := by
    rw [← star_mul, ← coe_mul, inv_mul_cancel, coe_one, star_one]
  have h := sq_eq_trace_smul_sub_det_smul_one_fin_two (A * star A)
  rw [det_mul_star, g.norm_det_eq_one, RCLike.ofReal_one, one_pow, one_smul, sq] at h
  -- `A Aᴴ A = (A Aᴴ) (A Aᴴ) Bᴴ = tr (A Aᴴ) A - Bᴴ`.
  have hCH : A * (star A * A) = (A * star A).trace • A - star B := by
    calc A * (star A * A) = A * star A * (A * star A) * star B := by
          simp only [Matrix.mul_assoc, hstar, Matrix.mul_one]
      _ = (A * star A).trace • A - star B := by
        rw [h]
        simp only [Matrix.sub_mul, smul_mul_assoc, Matrix.mul_assoc, hstar, Matrix.mul_one,
          Matrix.one_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hCH, hstar, Matrix.mul_one,
    Matrix.one_mul]
  module

/-- **The unitary factor of `g ∈ SL(2, 𝕜)`.** The polar retraction `SL(2, 𝕜) → SU(2)` sends `g` to
`(g + (g⁻¹)ᴴ) / √(tr (g gᴴ) + 2)`. -/
theorem coe_polarRetraction_fin_two (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) =
      (√(RCLike.re ((g : Matrix (Fin 2) (Fin 2) 𝕜) * star (g : Matrix (Fin 2) (Fin 2) 𝕜)).trace +
          2))⁻¹ •
        ((g : Matrix (Fin 2) (Fin 2) 𝕜) + star ((g⁻¹ : SpecialLinearGroup (Fin 2) 𝕜) :
          Matrix (Fin 2) (Fin 2) 𝕜)) := by
  set A : Matrix (Fin 2) (Fin 2) 𝕜 := (g : Matrix (Fin 2) (Fin 2) 𝕜)
  have hP := Matrix.sqrt_mul_star_fin_two_of_norm_det_eq_one (A := A) g.norm_det_eq_one
  have hid := mul_star_add_one_mul_add_star_inv g
  obtain ⟨t, ht0, ht⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (nonneg_iff_posSemidef.1 (mul_star_self_nonneg A)).trace_nonneg
  rw [← ht, RCLike.ofReal_re] at hP ⊢
  rw [← ht, ← RCLike.ofReal_ofNat, ← RCLike.ofReal_add, ← RCLike.real_smul_eq_coe_smul] at hid
  set c := √(t + 2)
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hcc : c * c = t + 2 := Real.mul_self_sqrt (by linarith)
  have hc2 : c⁻¹ * c⁻¹ * (t + 2) = 1 := by
    rw [← hcc]
    field_simp
  -- The left polar decomposition `A = √(A Aᴴ) U`, and the same equation for the explicit matrix.
  have hPU : CFC.sqrt (A * star A) * (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) =
      A := by
    rw [coe_polarRetraction_apply]
    simpa only [coe_GL_coe_matrix] using Units.sqrt_mul_star_mul_polarUnitary (toGL g)
  have hPV : CFC.sqrt (A * star A) * (c⁻¹ • (A + star ((g⁻¹ : SpecialLinearGroup (Fin 2) 𝕜) :
      Matrix (Fin 2) (Fin 2) 𝕜))) = A := by
    rw [hP, smul_mul_smul_comm, hid, smul_smul, hc2, one_smul]
  -- The positive factor is invertible, so it can be cancelled.
  have hunit : IsUnit (CFC.sqrt (A * star A)) := by
    simpa only [coe_GL_coe_matrix] using
      (GeneralLinearGroup.posDef_sqrt_mul_star (toGL g)).isUnit
  exact hunit.mul_left_cancel (hPU.trans hPV.symm)

end Matrix.SpecialLinearGroup
