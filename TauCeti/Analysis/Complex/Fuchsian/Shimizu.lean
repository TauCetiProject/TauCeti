/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Shimizu's lemma

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup containing the translation `z ↦ z + w` with `w ≠ 0`.
Shimizu's lemma says that the lower-left entry `c` of any element of `Γ` satisfies `c = 0` or
`|c| ≥ |w|⁻¹`: the elements of `Γ` that do not fix `∞` are bounded away from the parabolic ones.
Equivalently, in geometric form, an element of `Γ` that does not fix `∞` satisfies
`(g • z).im * z.im ≤ w ^ 2` for every `z` in the upper half-plane, so it cannot map a point high
above the real axis to another such point. This is what makes sufficiently high horodiscs at a
cusp precisely invariant under the cusp stabilizer.

The proof is Jørgensen's: if `w * |c| < 1`, the iteration `A ↦ A T A⁻¹` starting from a lift `A`
of `g`, where `T = !![1, w; 0, 1]`, stays in `Γ`, its lower-left entries satisfy
`c_{n+1} = -w * c_n ^ 2` and hence tend to `0` very fast, and the whole sequence converges to `T`.
Discreteness forces the sequence to reach `T`, whose lower-left entry vanishes, while
`c_{n+1} = -w * c_n ^ 2` keeps every `c_n` nonzero.

## Main results

* `Subgroup.inv_le_abs_apply_one_zero_of_upperRightHom_mem`: Shimizu's lemma in coordinates.
* `Subgroup.im_smul_mul_im_le_sq_of_upperRightHom_mem`: its geometric form.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4.
* Hideo Shimizu, *On discontinuous groups operating on the product of the upper half planes*,
  Annals of Mathematics 77 (1963), 33–71.
-/

public section

open Filter Matrix MulAction OnePoint UpperHalfPlane
open scoped MatrixGroups Topology

namespace Subgroup

open Matrix.ProjectiveSpecialLinearGroup Matrix.SpecialLinearGroup

attribute [local simp] Matrix.adjugate_fin_two

/-- The transvection `!![1, w; 0, 1]`, the canonical lift of the translation `upperRightHom w`. -/
private noncomputable def transSL (w : ℝ) : SL(2, ℝ) :=
  SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) w

private theorem coe_transSL (w : ℝ) : ((transSL w : SL(2, ℝ)) : PSL(2, ℝ)) = upperRightHom w :=
  (upperRightHom_apply w).symm

@[simp] private theorem transSL_apply_zero_zero (w : ℝ) : transSL w 0 0 = 1 := by
  simp [transSL, SpecialLinearGroup.transvection_coe]

@[simp] private theorem transSL_apply_zero_one (w : ℝ) : transSL w 0 1 = w := by
  simp [transSL, SpecialLinearGroup.transvection_coe]

@[simp] private theorem transSL_apply_one_zero (w : ℝ) : transSL w 1 0 = 0 := by
  simp [transSL, SpecialLinearGroup.transvection_coe]

@[simp] private theorem transSL_apply_one_one (w : ℝ) : transSL w 1 1 = 1 := by
  simp [transSL, SpecialLinearGroup.transvection_coe]

/-! ### The entries of Jørgensen's iteration -/

private theorem conj_transSL_apply_zero_zero (w : ℝ) (A : SL(2, ℝ)) :
    (A * transSL w * A⁻¹) 0 0 = 1 - w * A 0 0 * A 1 0 := by
  have h := A.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two, transSL, SpecialLinearGroup.transvection_coe]
  linear_combination h

private theorem conj_transSL_apply_zero_one (w : ℝ) (A : SL(2, ℝ)) :
    (A * transSL w * A⁻¹) 0 1 = w * A 0 0 ^ 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, transSL, SpecialLinearGroup.transvection_coe]
  ring

private theorem conj_transSL_apply_one_zero (w : ℝ) (A : SL(2, ℝ)) :
    (A * transSL w * A⁻¹) 1 0 = -(w * A 1 0 ^ 2) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, transSL, SpecialLinearGroup.transvection_coe]
  ring

private theorem conj_transSL_apply_one_one (w : ℝ) (A : SL(2, ℝ)) :
    (A * transSL w * A⁻¹) 1 1 = 1 + w * A 0 0 * A 1 0 := by
  have h := A.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two, transSL, SpecialLinearGroup.transvection_coe]
  linear_combination h

/-- Jørgensen's iteration `A ↦ A T A⁻¹` starting from `A`, where `T` is the transvection of
parameter `w`. -/
private noncomputable def jorgensen (w : ℝ) (A : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => A
  | n + 1 => jorgensen w A n * transSL w * (jorgensen w A n)⁻¹

private theorem jorgensen_succ (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    jorgensen w A (n + 1) = jorgensen w A n * transSL w * (jorgensen w A n)⁻¹ := rfl

variable {Γ : Subgroup PSL(2, ℝ)} {w : ℝ} {A : SL(2, ℝ)}

private theorem jorgensen_mem (hT : upperRightHom w ∈ Γ) (hA : (A : PSL(2, ℝ)) ∈ Γ) (n : ℕ) :
    ((jorgensen w A n : SL(2, ℝ)) : PSL(2, ℝ)) ∈ Γ := by
  induction n with
  | zero => exact hA
  | succ n ih =>
      rw [jorgensen_succ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        coe_transSL]
      exact Γ.mul_mem (Γ.mul_mem ih hT) (Γ.inv_mem ih)

private theorem jorgensen_apply_one_zero_ne_zero (hw : w ≠ 0) (hA : A 1 0 ≠ 0) (n : ℕ) :
    jorgensen w A n 1 0 ≠ 0 := by
  induction n with
  | zero => exact hA
  | succ n ih =>
      rw [jorgensen_succ, conj_transSL_apply_one_zero]
      simpa using ⟨hw, ih⟩

private theorem abs_jorgensen_apply_one_zero (hw : 0 ≤ w) (n : ℕ) :
    w * |jorgensen w A n 1 0| = (w * |A 1 0|) ^ 2 ^ n := by
  induction n with
  | zero => simp [jorgensen]
  | succ n ih =>
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      rw [jorgensen_succ, conj_transSL_apply_one_zero, abs_neg, abs_mul, abs_of_nonneg hw,
        abs_pow, h2, pow_mul, ← ih]
      ring

/-! ### Convergence of the iteration -/

/-- If the lower-left entry of `A` is small enough, Jørgensen's iteration converges to the
transvection `T`. The lower-left entries are squared at each step, and the upper-left entries
stay bounded because they satisfy `a_{n+1} = 1 - w * a_n * c_n`. -/
private theorem tendsto_jorgensen (hw : 0 < w) (hlt : w * |A 1 0| < 1) :
    Tendsto (jorgensen w A) atTop (𝓝 (transSL w)) := by
  set ε := w * |A 1 0| with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεle : ∀ n, w * |jorgensen w A n 1 0| ≤ ε ^ n := fun n => by
    rw [abs_jorgensen_apply_one_zero hw.le, ← hεdef]
    exact pow_le_pow_of_le_one hε0 hlt.le Nat.lt_two_pow_self.le
  have hεle1 : ∀ n, w * |jorgensen w A n 1 0| ≤ ε := fun n => by
    have h := pow_le_pow_of_le_one hε0 hlt.le (Nat.one_le_two_pow (n := n))
    rw [pow_one] at h
    exact (abs_jorgensen_apply_one_zero hw.le n).trans_le (hεdef ▸ h)
  set C := max |A 0 0| (1 - ε)⁻¹ with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_right (by positivity)
  have hCε : 1 + C * ε ≤ C := by
    have h2 : 0 < 1 - ε := by linarith
    have h3 : 1 ≤ C * (1 - ε) :=
      calc (1 : ℝ) = (1 - ε)⁻¹ * (1 - ε) := (inv_mul_cancel₀ h2.ne').symm
        _ ≤ C * (1 - ε) := mul_le_mul_of_nonneg_right (le_max_right _ _) h2.le
    nlinarith
  have htri : ∀ t : ℝ, |1 - t| ≤ 1 + |t| := fun t => by
    simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-t)
  have habs : ∀ n, |jorgensen w A n 0 0| ≤ C := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
        rw [jorgensen_succ, conj_transSL_apply_zero_zero]
        calc |1 - w * jorgensen w A n 0 0 * jorgensen w A n 1 0|
            ≤ 1 + |w * jorgensen w A n 0 0 * jorgensen w A n 1 0| := htri _
          _ = 1 + |jorgensen w A n 0 0| * (w * |jorgensen w A n 1 0|) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hw.le]; ring
          _ ≤ 1 + C * ε := by
              have := mul_le_mul ih (hεle1 n) (by positivity) hC0
              linarith
          _ ≤ C := hCε
  have hprod : Tendsto
      (fun n => w * jorgensen w A n 0 0 * jorgensen w A n 1 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => C * ε ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.le]
      calc w * |jorgensen w A n 0 0| * |jorgensen w A n 1 0|
          = |jorgensen w A n 0 0| * (w * |jorgensen w A n 1 0|) := by ring
        _ ≤ C * ε ^ n := mul_le_mul (habs n) (hεle n) (by positivity) hC0
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hε0 hlt).const_mul C
  have ha : Tendsto (fun n => jorgensen w A n 0 0) atTop (𝓝 1) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [jorgensen_succ, conj_transSL_apply_zero_zero]
    simpa using tendsto_const_nhds.sub hprod
  have hb : Tendsto (fun n => jorgensen w A n 0 1) atTop (𝓝 w) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [jorgensen_succ, conj_transSL_apply_zero_one]
    simpa using (ha.pow 2).const_mul w
  have hc : Tendsto (fun n => jorgensen w A n 1 0) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => w⁻¹ * ε ^ n) (fun n => ?_) ?_
    · have hsplit : |jorgensen w A n 1 0| = w⁻¹ * (w * |jorgensen w A n 1 0|) := by
        field_simp
      rw [Real.norm_eq_abs, hsplit]
      exact mul_le_mul_of_nonneg_left (hεle n) (by positivity)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hε0 hlt).const_mul w⁻¹
  have hd : Tendsto (fun n => jorgensen w A n 1 1) atTop (𝓝 1) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [jorgensen_succ, conj_transSL_apply_one_one]
    simpa using tendsto_const_nhds.add hprod
  have hmat : Tendsto
      (fun n => ((jorgensen w A n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (𝓝 ((transSL w : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) := by
    refine tendsto_pi_nhds.mpr (Fin.forall_fin_two.mpr ⟨tendsto_pi_nhds.mpr
      (Fin.forall_fin_two.mpr ⟨?_, ?_⟩), tendsto_pi_nhds.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩)
    · simpa using ha
    · simpa using hb
    · simpa using hc
    · simpa using hd
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.tendsto_nhds_iff.mpr hmat

/-! ### Shimizu's lemma -/

private theorem inv_le_abs_apply_one_zero_of_upperRightHom_mem_of_pos [DiscreteTopology Γ]
    (hw : 0 < w)
    (hT : upperRightHom w ∈ Γ) (hA : (A : PSL(2, ℝ)) ∈ Γ) (hA0 : A 1 0 ≠ 0) :
    w⁻¹ ≤ |A 1 0| := by
  rw [inv_le_iff_one_le_mul₀ hw, mul_comm]
  by_contra hlt
  rw [not_le] at hlt
  -- the iterates converge to the transvection inside the discrete subgroup `Γ`
  have hmem := jorgensen_mem hT hA
  have hcont : Continuous (fun a : SL(2, ℝ) => (a : PSL(2, ℝ))) := continuous_quot_mk
  have hconv : Tendsto (fun n => (⟨((jorgensen w A n : SL(2, ℝ)) : PSL(2, ℝ)), hmem n⟩ : Γ)) atTop
      (𝓝 (⟨upperRightHom w, hT⟩ : Γ)) :=
    tendsto_subtype_rng.mpr <| by
      simpa only [Function.comp_def, coe_transSL] using
        (hcont.tendsto (transSL w)).comp (tendsto_jorgensen hw hlt)
  rw [nhds_discrete, tendsto_pure] at hconv
  obtain ⟨n, hn⟩ := hconv.exists
  -- but no iterate can equal the transvection: their lower-left entries never vanish
  refine jorgensen_apply_one_zero_ne_zero hw.ne' hA0 n ?_
  have hval : ((jorgensen w A n : SL(2, ℝ)) : PSL(2, ℝ)) = upperRightHom w := by
    simpa using congrArg Subtype.val hn
  have hinfty : ((jorgensen w A n : SL(2, ℝ)) : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
    rw [hval, upperRightHom_smul_infty]
  rwa [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    SpecialLinearGroup.coe_GL_coe_matrix] at hinfty

/-- **Shimizu's lemma.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup containing the translation
`z ↦ z + w` with `w ≠ 0`, and let `A ∈ SL(2, ℝ)` lift an element of `Γ`. If the lower-left entry
of `A` does not vanish, that is, if the element does not fix `∞`, then that entry has absolute
value at least `|w|⁻¹`. Both lifts of the element give the same absolute value. -/
theorem inv_le_abs_apply_one_zero_of_upperRightHom_mem [DiscreteTopology Γ] (hw : w ≠ 0)
    (hT : upperRightHom w ∈ Γ) (hA : (A : PSL(2, ℝ)) ∈ Γ) (hA0 : A 1 0 ≠ 0) :
    |w|⁻¹ ≤ |A 1 0| := by
  rcases lt_or_gt_of_ne hw with hwneg | hwpos
  · have hTneg : upperRightHom (-w) ∈ Γ := by
      rw [AddChar.map_neg_eq_inv]
      exact Γ.inv_mem hT
    simpa [abs_of_neg hwneg] using
      inv_le_abs_apply_one_zero_of_upperRightHom_mem_of_pos (neg_pos.mpr hwneg) hTneg hA hA0
  · simpa [abs_of_pos hwpos] using
      inv_le_abs_apply_one_zero_of_upperRightHom_mem_of_pos hwpos hT hA hA0

/-- **Shimizu's lemma, geometric form.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup containing
the translation `z ↦ z + w` with `w ≠ 0`. An element of `Γ` that does not fix `∞` moves every
point `z` of the upper half-plane to a point with `(g • z).im * z.im ≤ w ^ 2`; in particular it
cannot keep a point of imaginary part greater than `|w|` that high. -/
theorem im_smul_mul_im_le_sq_of_upperRightHom_mem [DiscreteTopology Γ] (hw : w ≠ 0)
    (hT : upperRightHom w ∈ Γ) {g : PSL(2, ℝ)} (hg : g ∈ Γ)
    (hginf : g • (∞ : OnePoint ℝ) ≠ ∞) (z : ℍ) :
    (g • z).im * z.im ≤ w ^ 2 := by
  induction g using QuotientGroup.induction_on with | H A => ?_
  have hA0 : A 1 0 ≠ 0 := fun h => hginf (by
    rw [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
      SpecialLinearGroup.coe_GL_coe_matrix]
    exact h)
  have hbound := inv_le_abs_apply_one_zero_of_upperRightHom_mem hw hT hg hA0
  have hone : 1 ≤ w ^ 2 * A 1 0 ^ 2 := by
    have h1 : |w|⁻¹ ^ 2 ≤ A 1 0 ^ 2 := by
      rw [← sq_abs (A 1 0)]
      exact pow_le_pow_left₀ (by positivity) hbound 2
    calc (1 : ℝ) = |w| ^ 2 * |w|⁻¹ ^ 2 := by field_simp
      _ = w ^ 2 * |w|⁻¹ ^ 2 := by rw [sq_abs]
      _ ≤ w ^ 2 * A 1 0 ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg w)
  -- the imaginary part of `g • z` is `z.im` divided by the squared automorphy factor
  have hdenom : (A 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom (mapGL ℝ A) z) := by
    simpa [Matrix.SpecialLinearGroup.coe_mapGL_fin_two] using
      UpperHalfPlane.c_mul_im_sq_le_normSq_denom (mapGL ℝ A) z
  have hpos : 0 < Complex.normSq (denom (mapGL ℝ A) z) :=
    UpperHalfPlane.normSq_denom_pos (mapGL ℝ A) z.im_ne_zero
  have him : ((A : PSL(2, ℝ)) • z).im = z.im / Complex.normSq (denom (mapGL ℝ A) z) := by
    rw [UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def,
      UpperHalfPlane.im_smul_eq_div_normSq, det_mapGL, Units.val_one, abs_one, one_mul]
  rw [him, div_mul_eq_mul_div, div_le_iff₀ hpos]
  calc z.im * z.im = z.im ^ 2 := by ring
    _ ≤ w ^ 2 * A 1 0 ^ 2 * z.im ^ 2 := le_mul_of_one_le_left (by positivity) hone
    _ = w ^ 2 * (A 1 0 * z.im) ^ 2 := by ring
    _ ≤ w ^ 2 * Complex.normSq (denom (mapGL ℝ A) z) :=
        mul_le_mul_of_nonneg_left hdenom (sq_nonneg w)

end Subgroup
