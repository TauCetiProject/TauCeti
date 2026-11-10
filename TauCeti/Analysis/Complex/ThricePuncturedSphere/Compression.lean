/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Compressing the thrice-punctured sphere into a truncation

The truncation `S_R` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}` is the part where the signed
longitudinal coordinate `±s_q` of every end `q` is at most `R`. This file constructs, for `R ≥ 0`
and `ε > 0`, a smooth map `TauCeti.ThricePuncturedSphere.truncationCompression R ε` of `S` into
the slightly larger truncation `S_{R + ε}` which is the identity wherever every `±s_q` is at most
`R + ε / 2`, in particular near `S_R`.

On each end it moves points radially about the center `c_q` of the end, changing the signed
longitudinal coordinate `h = ±s_q` to the compressed height
`TauCeti.ThricePuncturedSphere.compressedHeight R ε h`. This is `h` up to `R + ε / 2`, is less
than `R + ε` everywhere, and is the constant `R + 3ε/4` beyond `R + ε`. Since the radius
`‖w - c_q‖` is `‖b_q‖ exp (∓2π s_q)`, the map on the end `q` is
`w ↦ c_q + exp (±2π (h - compressedHeight R ε h)) • (w - c_q)`
(`TauCeti.ThricePuncturedSphere.Puncture.endCompression`), and the compression of `S` is the
composition of the compressions of the three ends.

Composing a map with the compression replaces it by one that only sees its values on `S_{R + ε}`,
without changing it near `S_R`. A map of class `Cⁿ` on a neighbourhood of `S_{R + ε}` thus
becomes one of class `Cⁿ` on all of `S`. This localizes results stated for maps on the whole
of `S`, such as integral identities over `S_R`, to maps defined only near `S_R`, for instance
maps on a domain with further punctures outside `S_R`.

## Main definitions

* `TauCeti.ThricePuncturedSphere.compressedHeight`: the compressed height profile.
* `TauCeti.ThricePuncturedSphere.Puncture.endCompression`: the radial compression of one end.
* `TauCeti.ThricePuncturedSphere.truncationCompression`: the compression of all three ends.

## Main results

* `TauCeti.ThricePuncturedSphere.truncationCompression_mem_truncation`: the compression maps `S`
  into `S_{R + ε}`.
* `TauCeti.ThricePuncturedSphere.truncationCompression_eventuallyEq`: it is the identity near
  every point of `S_R`.
* `TauCeti.ThricePuncturedSphere.contDiffOn_truncationCompression`: it is smooth on `S`.
* `TauCeti.ThricePuncturedSphere.exists_pos_truncation_add_subset`: every open neighbourhood of
  `S_R` contains some `S_{R + ε}`, so the compression applies to maps defined near `S_R`.
-/

public noncomputable section

open Set Real Topology

namespace TauCeti.ThricePuncturedSphere

/-- The compressed height profile: `h` for `h ≤ R + ε / 2`, the constant `R + 3ε/4` for
`h ≥ R + ε`, and a smooth interpolation in between, which stays below `R + ε`. -/
def compressedHeight (R ε h : ℝ) : ℝ :=
  h + smoothTransition (2 * (h - R - ε / 2) / ε) * (R + 3 * ε / 4 - h)

variable {R ε h : ℝ}

theorem compressedHeight_def (R ε h : ℝ) :
    compressedHeight R ε h = h + smoothTransition (2 * (h - R - ε / 2) / ε) * (R + 3 * ε / 4 - h) :=
  (rfl)

/-- Up to `R + ε / 2` the compressed height is the height. -/
theorem compressedHeight_of_le (hε : 0 < ε) (hh : h ≤ R + ε / 2) : compressedHeight R ε h = h := by
  rw [compressedHeight_def, smoothTransition.zero_of_nonpos, zero_mul, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

/-- The compressed height is less than `R + ε`. -/
theorem compressedHeight_lt (hε : 0 < ε) (h : ℝ) : compressedHeight R ε h < R + ε := by
  rw [compressedHeight_def]
  rcases le_or_gt (R + ε) h with hh | hh
  · rw [smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)]
    linarith
  · rcases le_or_gt 0 (R + 3 * ε / 4 - h) with hc | hc
    · nlinarith [mul_le_of_le_one_left hc (smoothTransition.le_one (2 * (h - R - ε / 2) / ε))]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos (smoothTransition.nonneg
        (2 * (h - R - ε / 2) / ε)) hc.le]

/-- Beyond `R + ε / 2` the compressed height stays beyond `R + ε / 2`. -/
theorem lt_compressedHeight (hε : 0 < ε) (hh : R + ε / 2 < h) :
    R + ε / 2 < compressedHeight R ε h := by
  rw [compressedHeight_def]
  have hb₀ := smoothTransition.nonneg (2 * (h - R - ε / 2) / ε)
  have hb₁ := smoothTransition.le_one (2 * (h - R - ε / 2) / ε)
  rcases le_or_gt 0 (R + 3 * ε / 4 - h) with hc | hc
  · nlinarith [mul_nonneg hb₀ hc]
  · nlinarith [mul_nonneg (sub_nonneg.2 hb₁) (neg_nonneg.2 hc.le)]

/-- The compressed height profile is smooth. -/
theorem contDiff_compressedHeight {n : ℕ∞} (R ε : ℝ) : ContDiff ℝ n (compressedHeight R ε) :=
  contDiff_id.add ((smoothTransition.contDiff.comp (by fun_prop)).mul (by fun_prop))

namespace Puncture

/-- **The radial compression of an end.** It moves a point `w` of the plane along the ray from the
center `c_q` of the end `q`, so that its signed longitudinal coordinate `h = ±s_q(w)` becomes the
compressed height `compressedHeight R ε h`: it multiplies `w - c_q` by
`exp (±2π (h - compressedHeight R ε h))`. -/
def endCompression (q : Puncture) (R ε : ℝ) (w : ℂ) : ℂ :=
  q.endCenter + Real.exp (q.endSign * (2 * π) * (q.endSign * (q.endCoord w).re -
    compressedHeight R ε (q.endSign * (q.endCoord w).re))) • (w - q.endCenter)

theorem endCompression_def (q : Puncture) (R ε : ℝ) (w : ℂ) :
    q.endCompression R ε w = q.endCenter + Real.exp (q.endSign * (2 * π) *
      (q.endSign * (q.endCoord w).re - compressedHeight R ε (q.endSign * (q.endCoord w).re))) •
        (w - q.endCenter) :=
  (rfl)

variable {q : Puncture} {w : ℂ}

/-- Up to height `R + ε / 2` on the end `q`, the compression of the end is the identity. -/
theorem endCompression_of_le (hε : 0 < ε) (hw : q.endSign * (q.endCoord w).re ≤ R + ε / 2) :
    q.endCompression R ε w = w := by
  rw [endCompression_def, compressedHeight_of_le hε hw, sub_self, mul_zero, Real.exp_zero,
    one_smul, add_sub_cancel]

/-- The radial rescaling `w ↦ c_q + a • (w - c_q)` by `a > 0` lowers the longitudinal coordinate of
the end `q` by `log a / (2π)`. -/
theorem re_endCoord_endCenter_add_smul (q : Puncture) {a : ℝ} (ha : 0 < a) (hw : w ≠ q.endCenter) :
    (q.endCoord (q.endCenter + a • (w - q.endCenter))).re =
      (q.endCoord w).re - Real.log a / (2 * π) := by
  have hw' : ‖(w - q.endCenter) / q.endScale‖ ≠ 0 :=
    norm_ne_zero_iff.2 (div_ne_zero (sub_ne_zero.2 hw) q.endScale_ne_zero)
  rw [re_endCoord, re_endCoord, add_sub_cancel_left, smul_div_assoc, norm_smul,
    Real.norm_of_nonneg ha.le, Real.log_mul ha.ne' hw']
  ring

/-- The compression of the end `q` changes the signed longitudinal coordinate `h` of the end `q`
at a point other than its center to the compressed height of `h`. -/
theorem endSign_mul_re_endCoord_endCompression (hw : w ≠ q.endCenter) :
    q.endSign * (q.endCoord (q.endCompression R ε w)).re =
      compressedHeight R ε (q.endSign * (q.endCoord w).re) := by
  rw [endCompression_def, re_endCoord_endCenter_add_smul q (Real.exp_pos _) hw, Real.log_exp]
  have hπ : (2 * π) ≠ 0 := by positivity
  rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] <;> field_simp <;> ring

/-- The compression of an end is smooth away from the center of the end. -/
theorem contDiffAt_endCompression {n : ℕ∞} (hw : w ≠ q.endCenter) :
    ContDiffAt ℝ n (q.endCompression R ε) w := by
  have hh : ContDiffAt ℝ n (fun w ↦ q.endSign * (q.endCoord w).re) w :=
    contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)
  exact contDiffAt_const.add (((contDiffAt_const.mul (hh.sub
    ((contDiff_compressedHeight R ε).contDiffAt.comp w hh))).exp).smul
    (contDiffAt_id.sub contDiffAt_const))

/-- The compression of an end maps the thrice-punctured sphere into itself: points that move lie
far out on the end `q`, and stay there. -/
theorem endCompression_ne_zero_and_ne_one (hR : 0 ≤ R) (hε : 0 < ε) (hw : w ≠ 0 ∧ w ≠ 1) :
    q.endCompression R ε w ≠ 0 ∧ q.endCompression R ε w ≠ 1 := by
  rcases le_or_gt (q.endSign * (q.endCoord w).re) (R + ε / 2) with hh | hh
  · rwa [endCompression_of_le hε hh]
  · refine q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_
    rw [endSign_mul_re_endCoord_endCompression (ne_endCenter hw q)]
    linarith [lt_compressedHeight hε hh]

/-- After compressing the end `q`, the signed longitudinal coordinate of the end `q` is less than
`R + ε`. -/
theorem endSign_mul_re_endCoord_endCompression_lt (hε : 0 < ε) (hw : w ≠ q.endCenter) :
    q.endSign * (q.endCoord (q.endCompression R ε w)).re < R + ε := by
  rw [endSign_mul_re_endCoord_endCompression hw]
  exact compressedHeight_lt hε _

/-- Compressing the end `q` does not push a point other than its center beyond height `max h 0`
on another end `p`, where `h` is its height there: points that move lie far out on the end `q`,
where every other signed longitudinal coordinate is nonpositive. -/
theorem endSign_mul_re_endCoord_endCompression_le_max (hR : 0 ≤ R) (hε : 0 < ε)
    (hw : w ≠ q.endCenter) {p : Puncture} (hp : p ≠ q) :
    p.endSign * (p.endCoord (q.endCompression R ε w)).re ≤
      max (p.endSign * (p.endCoord w).re) 0 := by
  rcases le_or_gt (q.endSign * (q.endCoord w).re) (R + ε / 2) with hh | hh
  · rw [endCompression_of_le hε hh]
    exact le_max_left _ _
  · refine (endSign_mul_re_endCoord_nonpos (Ne.symm hp) ?_).trans (le_max_right _ _)
    rw [endSign_mul_re_endCoord_endCompression hw]
    linarith [lt_compressedHeight hε hh]

end Puncture

open Puncture

/-- **The compression of the thrice-punctured sphere into a truncation.** The composition of the
compressions of the three ends: a smooth map of `S` into `S_{R + ε}` which is the identity
wherever every signed longitudinal coordinate is at most `R + ε / 2`. -/
def truncationCompression (R ε : ℝ) : ℂ → ℂ :=
  inf.endCompression R ε ∘ one.endCompression R ε ∘ zero.endCompression R ε

theorem truncationCompression_def (R ε : ℝ) :
    truncationCompression R ε =
      inf.endCompression R ε ∘ one.endCompression R ε ∘ zero.endCompression R ε :=
  (rfl)

variable {w : ℂ}

/-- The compression is the identity wherever every signed longitudinal coordinate is at most
`R + ε / 2`. -/
theorem truncationCompression_of_forall_le (hε : 0 < ε)
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ R + ε / 2) :
    truncationCompression R ε w = w := by
  simp only [truncationCompression_def, Function.comp_apply, endCompression_of_le hε (hw _)]

/-- **The compression maps the thrice-punctured sphere into the truncation `S_{R + ε}`.** -/
theorem truncationCompression_mem_truncation (hR : 0 ≤ R) (hε : 0 < ε) (hw : w ≠ 0 ∧ w ≠ 1) :
    truncationCompression R ε w ∈ truncation (R + ε) := by
  have hw₁ := endCompression_ne_zero_and_ne_one (q := zero) hR hε hw
  have hw₂ := endCompression_ne_zero_and_ne_one (q := one) hR hε hw₁
  have hRε : 0 ≤ R + ε := by linarith
  have hlt (q : Puncture) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) :=
    endSign_mul_re_endCoord_endCompression_lt (R := R) hε (ne_endCenter hw q)
  have hle (q : Puncture) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) {p : Puncture} (hp : p ≠ q) :=
    endSign_mul_re_endCoord_endCompression_le_max (q := q) hR hε (ne_endCenter hw q) hp
  refine mem_truncation.2 ⟨(endCompression_ne_zero_and_ne_one hR hε hw₂).1,
    (endCompression_ne_zero_and_ne_one hR hε hw₂).2, fun q ↦ ?_⟩
  simp only [truncationCompression_def, Function.comp_apply]
  cases q
  · exact (hle inf hw₂ (by decide)).trans (max_le ((hle one hw₁ (by decide)).trans
      (max_le (hlt zero hw).le hRε)) hRε)
  · exact (hle inf hw₂ (by decide)).trans (max_le (hlt one hw₁).le hRε)
  · exact (hlt inf hw₂).le

/-- **The compression is the identity near the truncation `S_R`.** -/
theorem truncationCompression_eventuallyEq (hε : 0 < ε) (hw : w ∈ truncation R) :
    truncationCompression R ε =ᶠ[𝓝 w] id := by
  have hw' := mem_truncation.1 hw
  have hev (q : Puncture) : ∀ᶠ w' in 𝓝 w, q.endSign * (q.endCoord w').re ≤ R + ε / 2 := by
    have hc : ContinuousAt (fun w' ↦ q.endSign * (q.endCoord w').re) w :=
      continuousAt_const.mul
        (q.contDiffAt_re_endCoord (ne_endCenter ⟨hw'.1, hw'.2.1⟩ q) (n := 0)).continuousAt
    exact (hc.eventually (gt_mem_nhds (by linarith [hw'.2.2 q]))).mono fun _ h ↦ h.le
  filter_upwards [hev zero, hev one, hev inf] with w' h₀ h₁ h₂
  exact truncationCompression_of_forall_le hε fun q ↦ by cases q <;> assumption

/-- **The compression is smooth on the thrice-punctured sphere.** -/
theorem contDiffOn_truncationCompression {n : ℕ∞} (hR : 0 ≤ R) (hε : 0 < ε) :
    ContDiffOn ℝ n (truncationCompression R ε) {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
  intro w hw
  have hw₁ := endCompression_ne_zero_and_ne_one (q := zero) hR hε hw
  have hw₂ := endCompression_ne_zero_and_ne_one (q := one) hR hε hw₁
  exact ((contDiffAt_endCompression (ne_endCenter hw₂ inf)).comp w
    ((contDiffAt_endCompression (ne_endCenter hw₁ one)).comp w
      (contDiffAt_endCompression (ne_endCenter hw zero)))).contDiffWithinAt

/-- An open neighbourhood of the truncation `S_R` contains a truncation `S_{R + ε}` with
`ε > 0`: the truncations are compact and decrease to `S_R`. -/
theorem exists_pos_truncation_add_subset {U : Set ℂ} (hU : IsOpen U) (hRU : truncation R ⊆ U) :
    ∃ ε > 0, truncation (R + ε) ⊆ U := by
  have hanti : Antitone fun n : ℕ ↦ truncation (R + 1 / (n + 1)) := fun m n hmn ↦
    truncation_mono (add_le_add_right (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hmn)) R)
  have hsub : (⋂ n : ℕ, truncation (R + 1 / (n + 1))) ⊆ U := by
    refine fun w hw ↦ hRU ?_
    simp only [mem_iInter, mem_truncation] at hw
    refine mem_truncation.2 ⟨(hw 0).1, (hw 0).2.1, fun q ↦ le_of_forall_pos_lt_add fun δ hδ ↦ ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    linarith [(hw n).2.2 q]
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hanti.directed_ge
    (fun n ↦ isCompact_truncation _) (hU.mem_nhdsSet.2 hsub)
  exact ⟨1 / (n + 1), by positivity, hn⟩

end TauCeti.ThricePuncturedSphere
