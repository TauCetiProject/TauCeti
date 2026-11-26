/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.FinTwo
public import TauCeti.Analysis.Matrix.Polar.SpecialLinear
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The explicit polar decomposition of `SL(2, 𝕜)`

For `𝕜 = ℝ` or `ℂ` and `g ∈ SL(2, 𝕜)`, put `H = gᴴ g` and `t = tr H`, a real number. Since
`det H = 1`, the Cayley–Hamilton theorem `H² = t H - 1` makes the polar decomposition `g = U P` of
`g` explicit:

* the positive factor is `P = √H = (t + 2) ^ (-1/2) • (H + 1)`
  (`Matrix.SpecialLinearGroup.sqrt_star_mul_self_fin_two`), the continuous-functional-calculus
  square root `CFC.sqrt H`, of determinant one;
* its inverse is `P⁻¹ = (t + 2) ^ (-1/2) • ((t + 1) • 1 - H)`, so the unitary factor, the polar
  retraction `SL(2, 𝕜) → SU(2)` of `Matrix.SpecialLinearGroup.polarRetraction`, is
  `U = g P⁻¹ = (t + 2) ^ (-1/2) • ((t + 1) • g - g gᴴ g)`
  (`Matrix.SpecialLinearGroup.coe_polarRetraction_fin_two`). It changes sign with `g`, while `P`
  does not, so `-g = (-U) P` (`Matrix.SpecialLinearGroup.coe_polarRetraction_neg_fin_two`).

**The normalized segment.** The positive factor is contracted to `1` along the segment from `P` to
`1`, rescaled to determinant one:

`Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`, for `0 ≤ s ≤ 1`.

The matrix `(1 - s) P + s` is positive definite, so its determinant is a positive real number and
`Q_s` is a positive-definite matrix of determinant one, with `Q₀ = P` and `Q₁ = 1`. So `g_s = U Q_s`
stays in `SL(2, 𝕜)`; it is the polar decomposition of `g_s`, which keeps the unitary factor `U` of
`g` (`Matrix.SpecialLinearGroup.polarRetraction_polarSegmentHomotopy`) and has positive factor
`Q_s` (`Matrix.SpecialLinearGroup.sqrt_star_mul_self_polarSegmentHomotopy`). For `g ∈ SU(2)`,
`P = 1` and `g_s = g` throughout. This gives a strong deformation retraction
`Matrix.SpecialLinearGroup.polarSegmentHomotopy` of `SL(2, 𝕜)` onto `SU(2)` by explicit algebraic
formulas in the entries of `g`, continuous by inspection of the formulas, with no matrix powers
`P ^ (1 - s)` as in the polar homotopy `Matrix.SpecialLinearGroup.polarHomotopy`.

Left multiplication by `k ∈ SU(2)` fixes `H` and multiplies `U` by `k`, so the deformation commutes
with it, and in particular with the center `{±1}`. It therefore descends to the projective special
linear group (`Matrix.ProjectiveSpecialLinearGroup.descendHomotopyRel`), as a strong deformation
retraction `Matrix.ProjectiveSpecialLinearGroup.polarSegmentHomotopy` of `PSL(2, 𝕜)` onto the
projective special unitary group `PSU(2)`. For `𝕜 = ℂ` this is the Möbius group of the Riemann
sphere deformed onto its rotation group.

## Main results

* `Matrix.SpecialLinearGroup.sqrt_star_mul_self_fin_two`: `√(gᴴ g) = (t + 2) ^ (-1/2) • (gᴴ g + 1)`.
* `Matrix.SpecialLinearGroup.coe_polarRetraction_fin_two`: the explicit unitary factor.
* `Matrix.SpecialLinearGroup.coe_polarRetraction_neg_fin_two`: `-g = (-U) P`.
* `Matrix.SpecialLinearGroup.polarSegmentHomotopy`: the normalized-segment deformation retraction
  of `SL(2, 𝕜)` onto `SU(2)`, with its formula `coe_polarSegmentHomotopy_apply`.
* `Matrix.ProjectiveSpecialLinearGroup.polarSegmentHomotopy`: its descent to `PSL(2, 𝕜)`.

## References

* Bernard W. Levinger, *The square root of a `2 × 2` matrix*, Mathematics Magazine **53** (1980),
  222–224.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped unitInterval ContinuousMap MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.SpecialLinearGroup

open Matrix.specialUnitaryGroup

variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The matrix `gᴴ g` of `g ∈ SL(2, 𝕜)` is positive semidefinite of determinant one. -/
private theorem posSemidef_star_mul_self (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).PosSemidef ∧
      (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).det = 1 :=
  ⟨nonneg_iff_posSemidef.1 (star_mul_self_nonneg _), by
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose, det_coe, star_one, one_mul]⟩

/-- **The positive polar factor of `SL(2, 𝕜)`.** For `g ∈ SL(2, 𝕜)`, the positive factor `√(gᴴ g)`
of the polar decomposition `g = U √(gᴴ g)` is `(t + 2) ^ (-1/2) • (gᴴ g + 1)`, where `t` is the
trace of `gᴴ g`. -/
theorem sqrt_star_mul_self_fin_two (g : SpecialLinearGroup (Fin 2) 𝕜) :
    CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) =
      (√(RCLike.re (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).trace + 2))⁻¹ •
        (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g + 1) := by
  obtain ⟨hH, hdet⟩ := posSemidef_star_mul_self g
  rw [hH.sqrt_fin_two, hdet]
  simp

/-- **The unitary polar factor of `SL(2, 𝕜)`.** For `g ∈ SL(2, 𝕜)`, the polar retraction
`U = g √(gᴴ g)⁻¹` onto `SU(2)` is `(t + 2) ^ (-1/2) • ((t + 1) • g - g gᴴ g)`, where `t` is the
trace of `gᴴ g`. -/
theorem coe_polarRetraction_fin_two (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) =
      (√(RCLike.re (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).trace + 2))⁻¹ •
        ((RCLike.re (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).trace + 1) •
            (g : Matrix (Fin 2) (Fin 2) 𝕜) -
          g * star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) := by
  obtain ⟨hH, hdet⟩ := posSemidef_star_mul_self g
  obtain ⟨t, ht0, ht⟩ := RCLike.nonneg_iff_exists_ofReal.mp hH.trace_nonneg
  rw [← ht, RCLike.ofReal_re]
  set H := star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g with hHdef
  -- Cayley–Hamilton: `H² = t H - 1`, so `P⁻¹ = (t + 2) ^ (-1/2) • ((t + 1) • 1 - H)`.
  have hCH : H * H = t • H - 1 := by
    rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, ← ht, hdet, one_smul,
      ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hP : CFC.sqrt H * ((√(t + 2))⁻¹ • ((t + 1) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) - H)) = 1 := by
    have h : (H + 1) * ((t + 1) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) - H) =
        (t + 2) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
      rw [mul_sub, add_mul, add_mul, hCH, mul_smul_comm, mul_smul_comm, mul_one, one_mul, one_mul]
      module
    have ht2 : 0 < t + 2 := by linarith
    rw [hHdef, sqrt_star_mul_self_fin_two, ← hHdef, ← ht, RCLike.ofReal_re, smul_mul_smul, h,
      smul_smul, ← mul_inv, Real.mul_self_sqrt ht2.le, inv_mul_cancel₀ ht2.ne', one_smul]
  calc (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜)
      = (polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) * (CFC.sqrt H *
          ((√(t + 2))⁻¹ • ((t + 1) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) - H))) := by
        rw [hP, mul_one]
    _ = _ := by
      rw [← mul_assoc, hHdef, coe_polarRetraction_mul_sqrt_star_mul_self, mul_smul_comm, mul_sub,
        mul_smul_comm, mul_one, mul_assoc]

/-- **`-g = (-U) P`.** The unitary polar factor of `-g ∈ SL(2, 𝕜)` is the negative of that of `g`.
Since `(-g)ᴴ (-g) = gᴴ g`, the positive factor `P = √(gᴴ g)` is the same for `g` and `-g`. -/
theorem coe_polarRetraction_neg_fin_two (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (polarRetraction (Fin 2) 𝕜 (-g) : Matrix (Fin 2) (Fin 2) 𝕜) =
      -(polarRetraction (Fin 2) 𝕜 g : Matrix (Fin 2) (Fin 2) 𝕜) := by
  rw [coe_polarRetraction_fin_two, coe_polarRetraction_fin_two]
  simp only [coe_neg, star_neg, neg_mul, mul_neg, neg_neg]
  module

/-- The positive factor `√(gᴴ g)` of `g ∈ SL(2, 𝕜)` is positive definite. -/
private theorem posDef_sqrt_star_mul_self (g : SpecialLinearGroup (Fin 2) 𝕜) :
    (CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g)).PosDef := by
  simpa using GeneralLinearGroup.posDef_sqrt_mul_star (star (toGL g))

/-- For `0 ≤ s ≤ 1`, the point `(1 - s) • √(gᴴ g) + s • 1` of the segment from the positive factor
of `g` to `1` is positive definite. -/
private theorem posDef_segment (g : SpecialLinearGroup (Fin 2) 𝕜) (s : I) :
    ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
      (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).PosDef := by
  rcases (unitInterval.le_one s).lt_or_eq with hs | hs
  · exact ((posDef_sqrt_star_mul_self g).smul (sub_pos.2 hs)).add_posSemidef
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
  rw [segmentFactor, RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, Fintype.card_fin, ← hd,
    RCLike.ofReal_re, ← RCLike.ofReal_pow, inv_pow, Real.sq_sqrt hd0.le, ← RCLike.ofReal_mul,
    inv_mul_cancel₀ hd0.ne', RCLike.ofReal_one]

private theorem segmentFactor_zero (g : SpecialLinearGroup (Fin 2) 𝕜) :
    segmentFactor g 0 = CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) := by
  have h : (CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g)).det = 1 := by
    rw [← star_star (g : Matrix (Fin 2) (Fin 2) 𝕜), star_star (star _), det_sqrt_mul_star,
      star_eq_conjTranspose, det_conjTranspose, det_coe, star_one, norm_one, RCLike.ofReal_one]
  simp [segmentFactor, h]

private theorem segmentFactor_one (g : SpecialLinearGroup (Fin 2) 𝕜) : segmentFactor g 1 = 1 := by
  simp [segmentFactor]

private theorem sqrt_re_trace_star_mul_self_add_two_pos (g : SpecialLinearGroup (Fin 2) 𝕜) :
    0 < √(RCLike.re (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g).trace + 2) := by
  obtain ⟨t, ht0, ht⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (posSemidef_star_mul_self g).1.trace_nonneg
  rw [← ht, RCLike.ofReal_re]
  exact Real.sqrt_pos.2 (by linarith)

/-- The segment factor is continuous in the time and the matrix: the positive factor is given by
the explicit formula `sqrt_star_mul_self_fin_two`, and the determinant stays positive. -/
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
          fun p => (sqrt_re_trace_star_mul_self_add_two_pos p.2).ne').smul
            (hH.add continuous_const)
    exact h.congr fun p => (sqrt_star_mul_self_fin_two p.2).symm
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
  have h : star ((toSL k * g : SpecialLinearGroup (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) *
      (toSL k * g : SpecialLinearGroup (Fin 2) 𝕜) = star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g := by
    rw [coe_mul, coe_toSL, star_mul, mul_assoc, ← mul_assoc (star (k : Matrix (Fin 2) (Fin 2) 𝕜)),
      Unitary.star_mul_self_of_mem (specialUnitaryGroup_le_unitaryGroup k.property), one_mul]
  simp only [segmentFactor, h]

/-- The positive factor of a special unitary matrix is `1`, hence so is its segment factor. -/
private theorem segmentFactor_toSL (k : specialUnitaryGroup (Fin 2) 𝕜) (s : ℝ) :
    segmentFactor (toSL k) s = 1 := by
  have h : star ((toSL k : SpecialLinearGroup (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) * toSL k =
      1 := by
    rw [coe_toSL, Unitary.star_mul_self_of_mem (specialUnitaryGroup_le_unitaryGroup k.property)]
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

/-- The normalized-segment homotopy keeps the unitary polar factor: `g_s = U Q_s` has unitary
factor `U`. -/
@[simp]
theorem polarRetraction_polarSegmentHomotopy (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    polarRetraction (Fin 2) 𝕜 (polarSegmentHomotopy 𝕜 (s, g)) = polarRetraction (Fin 2) 𝕜 g := by
  refine Subtype.ext ?_
  rw [coe_polarRetraction_apply, coe_polarRetraction_apply,
    ((toGL (polarSegmentHomotopy 𝕜 (s, g))).mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq
      (posDef_segmentFactor g s).posSemidef.nonneg (v := (toGL g).polarUnitary)).1
        (by rw [coe_GL_coe_matrix, coe_polarSegmentHomotopy_apply', coe_polarRetraction_apply])
        |>.1]

/-- The positive polar factor of the normalized-segment homotopy at time `s` is
`Q_s = ((1 - s) P + s) / √(det ((1 - s) P + s))`, where `P = √(gᴴ g)`. -/
theorem sqrt_star_mul_self_polarSegmentHomotopy (s : I) (g : SpecialLinearGroup (Fin 2) 𝕜) :
    CFC.sqrt (star (polarSegmentHomotopy 𝕜 (s, g) : Matrix (Fin 2) (Fin 2) 𝕜) *
        polarSegmentHomotopy 𝕜 (s, g)) =
      (√(RCLike.re ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
          (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)).det))⁻¹ •
        ((1 - (s : ℝ)) • CFC.sqrt (star (g : Matrix (Fin 2) (Fin 2) 𝕜) * g) +
          (s : ℝ) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  have h := ((toGL (polarSegmentHomotopy 𝕜 (s, g))).mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq
      (posDef_segmentFactor g s).posSemidef.nonneg (v := (toGL g).polarUnitary)).1
        (by rw [coe_GL_coe_matrix, coe_polarSegmentHomotopy_apply', coe_polarRetraction_apply]) |>.2
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
