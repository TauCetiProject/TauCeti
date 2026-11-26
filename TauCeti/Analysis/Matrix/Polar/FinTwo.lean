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

**The normalized segment.** With `g = U P` the right polar decomposition, `P = √(gᴴ g)`, the
positive factor is contracted to `1` along the segment from `P` to `1`, rescaled to determinant
one:

`Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`, for `0 ≤ s ≤ 1`.

The matrix `(1 - s) P + s` is positive definite, so its determinant is a positive real number and
`Q_s` is a positive-definite matrix of determinant one, with `Q₀ = P` and `Q₁ = 1`. So `g_s = U Q_s`
stays in `SL(2, 𝕜)`; it is the polar decomposition of `g_s`, which keeps the unitary factor `U` of
`g` (`Matrix.SpecialLinearGroup.polarRetraction_polarSegmentHomotopy`) and has positive factor
`Q_s` (`Matrix.SpecialLinearGroup.sqrt_star_mul_self_polarSegmentHomotopy`). For `g ∈ SU(2)`,
`P = 1` and `g_s = g` throughout. This gives a strong deformation retraction
`Matrix.SpecialLinearGroup.polarSegmentHomotopy` of `SL(2, 𝕜)` onto `SU(2)` by explicit algebraic
formulas in the entries of `g`, continuous by inspection of the formula for `P`, with no matrix
powers `P ^ (1 - s)` as in the polar homotopy `Matrix.SpecialLinearGroup.polarHomotopy`.

Left multiplication by `k ∈ SU(2)` fixes `gᴴ g` and multiplies `U` by `k`, so the deformation
commutes with it, and in particular with the center `{±1}`. It therefore descends to the projective
special linear group (`Matrix.ProjectiveSpecialLinearGroup.descendHomotopyRel`), as a strong
deformation retraction `Matrix.ProjectiveSpecialLinearGroup.polarSegmentHomotopy` of `PSL(2, 𝕜)`
onto the projective special unitary group `PSU(2)`. For `𝕜 = ℂ` this is the Möbius group of the
Riemann sphere deformed onto its rotation group.

## Main results

* `Matrix.sqrt_mul_star_fin_two_of_norm_det_eq_one`,
  `Matrix.sqrt_star_mul_fin_two_of_norm_det_eq_one`: the positive factors of the polar
  decompositions of a matrix whose determinant has norm one.
* `Matrix.SpecialLinearGroup.coe_polarRetraction_fin_two`: the unitary factor of `g ∈ SL(2, 𝕜)` is
  `(g + (g⁻¹)ᴴ) / √(tr (g gᴴ) + 2)`.
* `Matrix.SpecialLinearGroup.polarSegmentHomotopy`: the normalized-segment deformation retraction
  of `SL(2, 𝕜)` onto `SU(2)`, with its formula `coe_polarSegmentHomotopy_apply`.
* `Matrix.ProjectiveSpecialLinearGroup.polarSegmentHomotopy`: its descent to `PSL(2, 𝕜)`.

## References

* Bernard W. Levinger, *The square root of a `2 × 2` matrix*, Mathematics Magazine **53** (1980),
  222–224.
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

/-! ### The normalized-segment deformation -/

open scoped unitInterval ContinuousMap Matrix.Norms.L2Operator

namespace Matrix.SpecialLinearGroup

open Matrix.specialUnitaryGroup

variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The trace `t` of `gᴴ g` is nonnegative, so `t + 2 > 0`. -/
private theorem re_trace_star_mul_self_add_two_pos (g : SpecialLinearGroup (Fin 2) 𝕜) :
    0 < RCLike.re (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).trace + 2 := by
  have h := (RCLike.nonneg_iff.1
    (nonneg_iff_posSemidef.1 (star_mul_self_nonneg (g : Matrix (Fin 2) (Fin 2) 𝕜))).trace_nonneg).1
  linarith

/-- For `0 ≤ s ≤ 1`, the point `(1 - s) • √(gᴴ g) + s • 1` of the segment from the positive factor
of `g` to `1` is positive definite. -/
private theorem posDef_segment (g : SpecialLinearGroup (Fin 2) 𝕜) (s : I) :
    ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
      (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).PosDef := by
  rcases (unitInterval.le_one s).lt_or_eq with hs | hs
  · exact ((GeneralLinearGroup.posDef_sqrt_star_mul (toGL g)).smul (sub_pos.2 hs)).add_posSemidef
      (PosSemidef.one.smul (unitInterval.nonneg s))
  · simpa [hs] using PosDef.one

/-- The determinant of the point at time `s` of the segment from `√(gᴴ g)` to `1` has positive real
part. -/
private theorem re_det_segment_pos (g : SpecialLinearGroup (Fin 2) 𝕜) (s : I) :
    0 < RCLike.re ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
      (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det :=
  (RCLike.pos_iff.1 (posDef_segment g s).det_pos).1

/-- The point at time `s` of the segment from the positive factor `√(gᴴ g)` to `1`, divided by the
square root of its determinant. -/
private def segmentFactor (g : SpecialLinearGroup (Fin 2) 𝕜) (s : ℝ) :
    Matrix (Fin 2) (Fin 2) 𝕜 :=
  (√(RCLike.re ((1 - s) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
      s • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det))⁻¹ •
    ((1 - s) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
      s • (1 : Matrix (Fin 2) (Fin 2) 𝕜))

private theorem posDef_segmentFactor (g : SpecialLinearGroup (Fin 2) 𝕜) (s : I) :
    (segmentFactor g s).PosDef :=
  (posDef_segment g s).smul (inv_pos.2 (Real.sqrt_pos.2 (re_det_segment_pos g s)))

private theorem det_segmentFactor (g : SpecialLinearGroup (Fin 2) 𝕜) (s : I) :
    (segmentFactor g s).det = 1 := by
  obtain ⟨d, hd0, hd⟩ := RCLike.pos_iff_exists_ofReal.mp (posDef_segment g s).det_pos
  rw [segmentFactor, RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← hd]
  simp [← RCLike.ofReal_pow, hd0.le, hd0.ne']

private theorem segmentFactor_zero (g : SpecialLinearGroup (Fin 2) 𝕜) :
    segmentFactor g 0 = CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) := by
  simp [segmentFactor, det_sqrt_star_mul_self]

private theorem segmentFactor_one (g : SpecialLinearGroup (Fin 2) 𝕜) : segmentFactor g 1 = 1 := by
  simp [segmentFactor]

/-- The segment factor is continuous in the time and the matrix: the positive factor is given by
the explicit formula `Matrix.sqrt_star_mul_fin_two_of_norm_det_eq_one`, and the determinant stays
positive. -/
private theorem continuous_segmentFactor :
    Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 => segmentFactor p.2 p.1 := by
  have hg : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 =>
      (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) :=
    continuous_subtypeVal.comp continuous_snd
  have hH : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 =>
      star (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * p.2 :=
    hg.star.mul hg
  have hP : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 =>
      CFC.sqrt (star (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * p.2) := by
    have h : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 =>
        (√(RCLike.re (star (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * p.2).trace + 2))⁻¹ •
          (star (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * p.2 + 1) :=
      (Continuous.inv₀ (Real.continuous_sqrt.comp
        ((RCLike.continuous_re.comp hH.matrix_trace).add continuous_const))
          fun p => (Real.sqrt_pos.2 (re_trace_star_mul_self_add_two_pos p.2)).ne').smul
            (hH.add continuous_const)
    exact h.congr fun p =>
      (Matrix.sqrt_star_mul_fin_two_of_norm_det_eq_one p.2.norm_det_eq_one).symm
  have hs : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 => (p.1 : ℝ) :=
    continuous_subtypeVal.comp continuous_fst
  have hM : Continuous fun p : I × SpecialLinearGroup (Fin 2) 𝕜 =>
      (1 - (p.1 : ℝ)) • CFC.sqrt (star (p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * p.2) +
        (p.1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) :=
    ((continuous_const.sub hs).smul hP).add (hs.smul continuous_const)
  refine (Continuous.inv₀ (Real.continuous_sqrt.comp (RCLike.continuous_re.comp hM.matrix_det))
    fun p => ?_).smul hM
  exact (Real.sqrt_pos.2 (re_det_segment_pos p.2 p.1)).ne'

/-- Left multiplication by a special unitary matrix fixes the positive factor `√(gᴴ g)`, hence the
segment factor. -/
private theorem segmentFactor_toSL_mul (k : specialUnitaryGroup (Fin 2) 𝕜)
    (g : SpecialLinearGroup (Fin 2) 𝕜) (s : ℝ) :
    segmentFactor (toSL k * g) s = segmentFactor g s := by
  simp only [segmentFactor, star_mul_self_toSL_mul]

/-- The positive factor of a special unitary matrix is `1`, hence so is its segment factor. -/
private theorem segmentFactor_toSL (k : specialUnitaryGroup (Fin 2) 𝕜) (s : ℝ) :
    segmentFactor (toSL k) s = 1 := by
  have h := star_mul_self_toSL_mul k 1
  rw [mul_one, coe_one, star_one, mul_one] at h
  simp only [segmentFactor, h, CFC.sqrt_one, ← add_smul, sub_add_cancel, one_smul, det_one,
    RCLike.one_re, Real.sqrt_one, inv_one]

variable (𝕜) in
/-- **`SL(2, 𝕜)` deformation retracts onto `SU(2)` along normalized segments.** Write
`g = U P` with `U` the polar retraction and `P = √(gᴴ g)`. At time `s` the homotopy is
`g_s = U Q_s` with `Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`, which runs from the identity
to the polar retraction followed by the inclusion `SU(2) → SL(2, 𝕜)`, and fixes `SU(2)`
throughout. -/
def polarSegmentHomotopy :
    (ContinuousMap.id (SpecialLinearGroup (Fin 2) 𝕜)).HomotopyRel
      ((⟨toSL, continuous_toSL⟩ :
        C(specialUnitaryGroup (Fin 2) 𝕜, SpecialLinearGroup (Fin 2) 𝕜)).comp
          (polarRetraction (Fin 2) 𝕜))
      (Set.range toSL) where
  toFun p := ⟨(polarRetraction (Fin 2) 𝕜 p.2 : Matrix (Fin 2) (Fin 2) 𝕜) * segmentFactor p.2 p.1,
    by rw [det_mul, (mem_specialUnitaryGroup_iff.1 (polarRetraction (Fin 2) 𝕜 p.2).property).2,
      det_segmentFactor, one_mul]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtypeVal.comp
      ((polarRetraction (Fin 2) 𝕜).continuous.comp continuous_snd)).mul continuous_segmentFactor
  map_zero_left g := Subtype.ext <| by
    simp only [ContinuousMap.id_apply]
    rw [Set.Icc.coe_zero, segmentFactor_zero, coe_polarRetraction_mul_sqrt_star_mul_self]
  map_one_left g := Subtype.ext <| by simp [segmentFactor_one]
  prop' s := by
    rintro _ ⟨k, rfl⟩
    refine Subtype.ext ((congrArg (· * segmentFactor (toSL k) s)
      (congrArg Subtype.val (polarRetraction_toSL k))).trans ?_)
    rw [segmentFactor_toSL, mul_one, ContinuousMap.id_apply, coe_toSL]

/-- The normalized-segment homotopy at time `s` is `U Q_s`, in terms of the segment factor. -/
private theorem coe_polarSegmentHomotopy_apply' (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (polarSegmentHomotopy 𝕜 (s, g) : Matrix (Fin 2) (Fin 2) 𝕜) =
      (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) * segmentFactor g s :=
  (rfl)

/-- The normalized-segment homotopy at time `s` is `U Q_s`, where `U` is the polar retraction,
`P = √(gᴴ g)` and `Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`. -/
@[simp]
theorem coe_polarSegmentHomotopy_apply (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (polarSegmentHomotopy 𝕜 (s, g) : Matrix (Fin 2) (Fin 2) 𝕜) =
      (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) *
        ((√(RCLike.re ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
            (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det))⁻¹ •
          ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
            (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜))) :=
  (rfl)

/-- The right polar decomposition of the normalized-segment homotopy at time `s`: `g_s = U Q_s`
has unitary factor `U` and positive factor `Q_s`. -/
private theorem polarUnitary_eq_and_sqrt_star_mul_eq_polarSegmentHomotopy (s : I)
    (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (toGL (polarSegmentHomotopy 𝕜 (s, g))).polarUnitary = (toGL g).polarUnitary ∧
      CFC.sqrt (star ((toGL (polarSegmentHomotopy 𝕜 (s, g)) : GL (Fin 2) 𝕜) :
          Matrix (Fin 2) (Fin 2) 𝕜) * (toGL (polarSegmentHomotopy 𝕜 (s, g)) : GL (Fin 2) 𝕜)) =
        segmentFactor g s :=
  ((toGL (polarSegmentHomotopy 𝕜 (s, g))).mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq
    (posDef_segmentFactor g s).posSemidef.nonneg).1
      (by rw [coe_GL_coe_matrix, coe_polarSegmentHomotopy_apply', coe_polarRetraction_apply])

/-- The normalized-segment homotopy keeps the unitary polar factor: `g_s = U Q_s` has unitary
factor `U`. -/
@[simp]
theorem polarRetraction_polarSegmentHomotopy (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    polarRetraction (Fin 2) 𝕜 (polarSegmentHomotopy 𝕜 (s, g)) = polarRetraction (Fin 2) 𝕜 g := by
  refine Subtype.ext ?_
  rw [coe_polarRetraction_apply, coe_polarRetraction_apply,
    (polarUnitary_eq_and_sqrt_star_mul_eq_polarSegmentHomotopy s g).1]

/-- The positive polar factor of the normalized-segment homotopy at time `s` is
`Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`, where `P = √(gᴴ g)`. -/
theorem sqrt_star_mul_self_polarSegmentHomotopy (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    CFC.sqrt (star (polarSegmentHomotopy 𝕜 (s, g) : Matrix (Fin 2) (Fin 2) 𝕜) *
        polarSegmentHomotopy 𝕜 (s, g)) =
      (√(RCLike.re ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
          (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det))⁻¹ •
        ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
          (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  have h := (polarUnitary_eq_and_sqrt_star_mul_eq_polarSegmentHomotopy s g).2
  rwa [coe_GL_coe_matrix] at h

/-- The normalized-segment homotopy commutes with left multiplication by `SU(2)`. -/
theorem polarSegmentHomotopy_toSL_mul (s : I) (k : specialUnitaryGroup (Fin 2) 𝕜)
    (g : SpecialLinearGroup (Fin 2) 𝕜) :
    polarSegmentHomotopy 𝕜 (s, toSL k * g) = toSL k * polarSegmentHomotopy 𝕜 (s, g) := by
  refine Subtype.ext ?_
  rw [coe_polarSegmentHomotopy_apply', coe_mul, coe_polarSegmentHomotopy_apply',
    polarRetraction_toSL_mul, segmentFactor_toSL_mul, Submonoid.coe_mul, coe_toSL, mul_assoc]

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

open Matrix.specialUnitaryGroup

variable {𝕜 : Type*} [RCLike 𝕜]

variable (𝕜) in
/-- **`PSL(2, 𝕜)` deformation retracts onto `PSU(2)` along normalized segments**: the homotopy
induced by the normalized-segment homotopy of `SL(2, 𝕜)`, which commutes with the center `{±1}`. It
runs from the identity to the polar retraction followed by the inclusion `PSU(2) → PSL(2, 𝕜)`, and
fixes `PSU(2)` throughout. -/
def polarSegmentHomotopy :
    (ContinuousMap.id (ProjectiveSpecialLinearGroup (Fin 2) 𝕜)).HomotopyRel
      ((⟨Subtype.val, continuous_subtypeVal⟩ :
        C((toPSL : specialUnitaryGroup (Fin 2) 𝕜 →* _).range,
          ProjectiveSpecialLinearGroup (Fin 2) 𝕜)).comp
          (polarRetraction (Fin 2) 𝕜))
      ((toPSL : specialUnitaryGroup (Fin 2) 𝕜 →* ProjectiveSpecialLinearGroup (Fin 2) 𝕜).range) :=
  descendHomotopyRel (SpecialLinearGroup.polarSegmentHomotopy 𝕜)
    fun s k g _ => SpecialLinearGroup.polarSegmentHomotopy_toSL_mul s k g

/-- The normalized-segment homotopy of `PSL(2, 𝕜)` is induced by that of `SL(2, 𝕜)`. -/
@[simp]
theorem polarSegmentHomotopy_mk (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    polarSegmentHomotopy 𝕜 (s, (g : ProjectiveSpecialLinearGroup (Fin 2) 𝕜)) =
      (SpecialLinearGroup.polarSegmentHomotopy 𝕜 (s, g) : SpecialLinearGroup (Fin 2) 𝕜) :=
  descendHomotopyRel_mk _ _ s g

end Matrix.ProjectiveSpecialLinearGroup
