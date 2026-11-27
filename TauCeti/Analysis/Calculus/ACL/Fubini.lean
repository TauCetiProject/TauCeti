/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# `ACL` maps through the faces of a box

Let `Q = Π_j [a_j, b_j]` be a closed coordinate box in `ℝⁿ⁺¹` and `i` a coordinate. A property `P`
of points of `ℝⁿ⁺¹` that depends only on the coordinates other than the `i`-th holds at almost
every point of `Q` exactly when it holds at the points of `Q` over almost every point of the face
`Π_{j ≠ i} [a_j, b_j]`, for the `n`-dimensional measure, provided `aᵢ < bᵢ`
(`TauCeti.ae_restrict_coordinateBox_iff_ae_face`). The proof splits off the `i`-th coordinate
with Fubini's theorem (`MeasureTheory.volume_preserving_piFinSuccAbove`): the exceptional set in
`Q` is the product of `[aᵢ, bᵢ]` with the exceptional set in the face, and the product measure of
a product set is the product of the measures, with no measurability assumption.

The line function of `u` through `x` in the `i`-th direction is such a property of `x`, so the
condition of `TauCeti.IsACLOn` is equivalent to the classical one of Martio, Rickman and Väisälä:
for every box and every `i`, the line function is absolutely continuous on the segment through
almost every point of the face (`TauCeti.ae_absolutelyContinuousOnInterval_lineFunction_iff`,
`TauCeti.isACLOn_iff_ae_face`).

## References

* O. Martio, S. Rickman, J. Väisälä, *Definitions for quasiregular mappings*,
  Ann. Acad. Sci. Fenn. Ser. A I 448 (1969), Definition 2.16.
-/

public section

open MeasureTheory Set

noncomputable section

namespace TauCeti

variable {n : ℕ}

/-- The point with `i`-th coordinate `t` and other coordinates `y` is obtained from the point with
`i`-th coordinate `s` and the same other coordinates by moving along the `i`-th axis. -/
private theorem toLp_insertNth_eq_add_sub_smul_single (i : Fin (n + 1)) (s t : ℝ)
    (y : Fin n → ℝ) :
    (WithLp.toLp 2 (i.insertNth t y) : EuclideanSpace ℝ (Fin (n + 1))) =
      WithLp.toLp 2 (i.insertNth s y) +
        (t - (WithLp.toLp 2 (i.insertNth s y) : EuclideanSpace ℝ (Fin (n + 1))) i) •
          EuclideanSpace.single i 1 := by
  ext j
  rw [EuclideanSpace.add_sub_smul_single_apply]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simp

/-- The point of `ℝⁿ⁺¹` with `i`-th coordinate `t` and the other coordinates `y` lies in the box
`Π_j [a_j, b_j]` iff `t ∈ [aᵢ, bᵢ]` and `y` lies in the face `Π_{j ≠ i} [a_j, b_j]`. -/
private theorem toLp_insertNth_mem_coordinateBox_iff {a b : Fin (n + 1) → ℝ} (i : Fin (n + 1))
    (t : ℝ) (y : Fin n → ℝ) :
    (WithLp.toLp 2 (i.insertNth t y) : EuclideanSpace ℝ (Fin (n + 1))) ∈ coordinateBox a b ↔
      t ∈ Icc (a i) (b i) ∧ y ∈ Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k)) := by
  rw [mem_coordinateBox, Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mem_Icc,
    Pi.le_def, forall_and]

/-- **Fubini for the faces of a box.** Let `P` be a property of points of `ℝⁿ⁺¹` that depends
only on the coordinates other than the `i`-th. If `aᵢ < bᵢ`, then `P` holds at almost every point
of the box `Π_j [a_j, b_j]` iff, for almost every `y` in the face `Π_{j ≠ i} [a_j, b_j]`, it holds
at the point with `i`-th coordinate `t₀` and the other coordinates `y`, for any fixed `t₀`. -/
theorem ae_restrict_coordinateBox_iff_ae_face {a b : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hab : a i < b i) {P : EuclideanSpace ℝ (Fin (n + 1)) → Prop}
    (hP : ∀ x (t : ℝ), P (x + (t - x i) • EuclideanSpace.single i 1) ↔ P x) (t₀ : ℝ) :
    (∀ᵐ x ∂volume.restrict (coordinateBox a b), P x) ↔
      ∀ᵐ y ∂volume.restrict (Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k))),
        P (WithLp.toLp 2 (i.insertNth t₀ y)) := by
  set face : Set (Fin n → ℝ) := Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k))
  set B : Set (Fin n → ℝ) := {y | ¬P (WithLp.toLp 2 (i.insertNth t₀ y))} ∩ face
  let e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ ℝ × (Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i)
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ ↦ ℝ) i).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1)))
  have he_symm (p : ℝ × (Fin n → ℝ)) :
      e.symm p = (WithLp.toLp 2 (i.insertNth p.1 p.2) : EuclideanSpace ℝ (Fin (n + 1))) :=
    rfl
  -- The exceptional set in the box is the product of `[aᵢ, bᵢ]` with the one in the face.
  have hpre : e.symm ⁻¹' ({x | ¬P x} ∩ coordinateBox a b) = Icc (a i) (b i) ×ˢ B := by
    ext ⟨t, y⟩
    simp only [mem_preimage, he_symm, mem_inter_iff, mem_ofPred_eq,
      toLp_insertNth_mem_coordinateBox_iff, mem_prod, B, face]
    rw [toLp_insertNth_eq_add_sub_smul_single i t₀ t y, hP]
    tauto
  have hvol : volume ({x | ¬P x} ∩ coordinateBox a b) = ENNReal.ofReal (b i - a i) * volume B := by
    rw [← he.symm.measure_preimage_equiv, hpre, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc]
  rw [ae_iff, Measure.restrict_apply' (measurableSet_coordinateBox a b), ae_iff,
    Measure.restrict_apply' measurableSet_Icc, hvol, mul_eq_zero,
    ENNReal.ofReal_eq_zero, sub_nonpos, iff_false_intro (not_le.2 hab), false_or]

/-- **Line functions through the faces of a box.** If `aᵢ < bᵢ`, the line function of `u` in the
`i`-th direction is absolutely continuous on `[aᵢ, bᵢ]` through almost every point of the box
`Π_j [a_j, b_j]` iff it is so through almost every point of the face `Π_{j ≠ i} [a_j, b_j]`,
placed at any fixed `i`-th coordinate `t₀`. -/
theorem ae_absolutelyContinuousOnInterval_lineFunction_iff {F : Type*} [NormedAddCommGroup F]
    (u : EuclideanSpace ℝ (Fin (n + 1)) → F) {a b : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hab : a i < b i) (t₀ : ℝ) :
    (∀ᵐ x ∂volume.restrict (coordinateBox a b),
        AbsolutelyContinuousOnInterval (lineFunction u x i) (a i) (b i)) ↔
      ∀ᵐ y ∂volume.restrict (Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k))),
        AbsolutelyContinuousOnInterval (lineFunction u (WithLp.toLp 2 (i.insertNth t₀ y)) i)
          (a i) (b i) :=
  ae_restrict_coordinateBox_iff_ae_face hab
    (fun x t ↦ by rw [lineFunction_add_smul_single]) t₀

/-- **The classical form of `ACL`.** A map is `ACL` on `Ω ⊆ ℝⁿ⁺¹` iff it is continuous on `Ω` and,
for every closed coordinate box `Π_j [a_j, b_j] ⊆ Ω` with `a_j < b_j` and every `i`, its line
function in the `i`-th direction is absolutely continuous on `[aᵢ, bᵢ]` through almost every point
of the face `Π_{j ≠ i} [a_j, b_j]`, placed at `i`-th coordinate `aᵢ`. -/
theorem isACLOn_iff_ae_face {F : Type*} [NormedAddCommGroup F]
    {u : EuclideanSpace ℝ (Fin (n + 1)) → F} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} :
    IsACLOn u Ω ↔ ContinuousOn u Ω ∧ ∀ a b : Fin (n + 1) → ℝ, (∀ j, a j < b j) →
      coordinateBox a b ⊆ Ω → ∀ i,
        ∀ᵐ y ∂volume.restrict (Icc (fun k ↦ a (i.succAbove k)) (fun k ↦ b (i.succAbove k))),
          AbsolutelyContinuousOnInterval
            (lineFunction u (WithLp.toLp 2 (i.insertNth (a i) y)) i) (a i) (b i) := by
  refine ⟨fun hu ↦ ⟨hu.continuousOn, fun a b hab hQ i ↦
    (ae_absolutelyContinuousOnInterval_lineFunction_iff u (hab i) (a i)).1
      (hu.ae_absolutelyContinuousOnInterval a b hab hQ i)⟩, fun ⟨hc, h⟩ ↦ ⟨hc, fun a b hab hQ i ↦
    (ae_absolutelyContinuousOnInterval_lineFunction_iff u (hab i) (a i)).2 (h a b hab hQ i)⟩⟩

end TauCeti
