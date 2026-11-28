/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Measure.Haar.Matrix.LDU

/-!
# Examples of integration in complex LDU coordinates

The first three ranks give a unit mass, ordinary complex volume, and a single complex
coordinate on each triangular side, respectively. A norm ball tests the indicator integral.
-/

open Matrix MeasureTheory MeasureTheory.Measure
open scoped ENNReal

-- Rank zero: the empty product is one and the coordinate space has unit mass.
example (f : Matrix (Fin 0) (Fin 0) ℂ → ℝ≥0∞) :
    ∫⁻ M, f M = f 0 := by
  let I := {p : Fin 0 × Fin 0 // p.1 < p.2}
  have : IsEmpty I := ⟨fun p ↦ Fin.elim0 p.val.1⟩
  have hu : volume (Set.univ : Set ((I → ℂ) × (I → ℂ))) = 1 := by
    rw [volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_pi]
  have h (M : Matrix (Fin 0) (Fin 0) ℂ) : f M = f 0 := congrArg f (Subsingleton.elim _ _)
  rw [← lintegral_bruhat_coords (Subsingleton.measurable (f := f))]
  simp [h, hu, volume_pi]

-- Rank one: there are no strictly upper entries and the diagonal gives a complex scalar.
example {f : Matrix (Fin 1) (Fin 1) ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ M, f M = ∫⁻ z : ℂ, f (diagonal fun _ ↦ z) := by
  let I := {p : Fin 1 × Fin 1 // p.1 < p.2}
  let U : (I → ℂ) → Matrix (Fin 1) (Fin 1) ℂ :=
    TauCeti.unitDiagonalMatrixOfEntries (fun p : Fin 1 × Fin 1 ↦ p.1 < p.2)
  have : IsEmpty I := ⟨fun p ↦ p.prop.ne (Subsingleton.elim _ _)⟩
  have hU (x : I → ℂ) : U x = 1 := by
    ext i j
    have h : i = j := Subsingleton.elim _ _
    subst j
    simp [U]
  have hu : volume (Set.univ : Set ((I → ℂ) × (I → ℂ))) = 1 := by
    rw [volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_pi]
  have h := lintegral_bruhat_coords hf
  -- Match the theorem's local coordinate type and constructor to `I` and `U` for rewriting.
  change (∫⁻ c : Fin 1 → ℂ, (∏ i : Fin 1, ‖c i‖ₑ ^ (4 * i.rev.val)) *
    ∫⁻ q : (I → ℂ) × (I → ℂ), f ((U q.1)ᴴ * diagonal c * U q.2)) = _ at h
  simp only [Fin.isValue, Fin.val_rev, Nat.reduceSubDiff, Fin.prod_univ_one,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, tsub_self, mul_zero, pow_zero,
    hU, Matrix.conjTranspose_one, one_mul, mul_one, lintegral_const, hu] at h
  rw [← h]
  let e := MeasurableEquiv.funUnique (Fin 1) ℂ
  exact ((volume_preserving_funUnique (Fin 1) ℂ).symm e).lintegral_comp_emb
    e.symm.measurableEmbedding (fun c ↦ f (diagonal c)) |>.symm

-- Rank two: the final diagonal entry has exponent zero. The two triangular sides each use
-- their own single complex coordinate.
example {f : Matrix (Fin 2) (Fin 2) ℂ → ℝ≥0∞} (hf : Measurable f) :
    let U := TauCeti.unitDiagonalMatrixOfEntries (fun p : Fin 2 × Fin 2 ↦ p.1 < p.2) (R := ℂ)
    (∫⁻ c : Fin 2 → ℂ, ‖c 0‖ₑ ^ 4 * ∫⁻ q : ℂ × ℂ,
      f ((U (fun _ ↦ q.1))ᴴ * diagonal c * U (fun _ ↦ q.2))) = ∫⁻ M, f M := by
  intro U
  let I := {p : Fin 2 × Fin 2 // p.1 < p.2}
  let p : I := ⟨(0, 1), by decide⟩
  let : Unique I := ⟨⟨p⟩, fun ⟨⟨i, j⟩, hij⟩ ↦ by
    -- Expose the natural-number comparisons; `omega` then pins down the position.
    change i.val < j.val at hij
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 1 := Fin.ext (by
      change j.val = 1
      omega)
    subst i j
    rfl⟩
  let e := MeasurableEquiv.funUnique I ℂ
  have hpres := (volume_preserving_funUnique I ℂ).symm e
  have h := lintegral_bruhat_coords hf
  -- This form exposes the two copies of `I → ℂ` to the product equivalence below.
  change (∫⁻ c : Fin 2 → ℂ, (∏ i : Fin 2, ‖c i‖ₑ ^ (4 * i.rev.val)) *
    ∫⁻ q : (I → ℂ) × (I → ℂ), f ((U q.1)ᴴ * diagonal c * U q.2)) = _ at h
  rw [← h]
  refine lintegral_congr fun c ↦ ?_
  simp only [Fin.isValue, Fin.val_rev, Nat.reduceSubDiff, Fin.prod_univ_two,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero, mul_one, Nat.mod_succ, tsub_self, mul_zero,
    pow_zero]
  congr 1
  simp only [volume_eq_prod]
  exact (hpres.prod hpres).lintegral_comp_emb (e.symm.prodCongr e.symm).measurableEmbedding
    (fun q : (I → ℂ) × (I → ℂ) ↦ f ((U q.1)ᴴ * diagonal c * U q.2))

open scoped Matrix.Norms.Frobenius in
-- Indicator of a measurable matrix norm ball, with its volume as the right-hand side.
example (n : ℕ) (r : ℝ) :
    let B := Metric.ball (0 : Matrix (Fin n) (Fin n) ℂ) r
    let E := {p : Fin n × Fin n // p.1 < p.2} → ℂ
    let U := TauCeti.unitDiagonalMatrixOfEntries (fun p : Fin n × Fin n ↦ p.1 < p.2)
    (∫⁻ c : Fin n → ℂ, (∏ i : Fin n, ‖c i‖ₑ ^ (4 * i.rev.val)) *
      ∫⁻ q : E × E,
        B.indicator (fun _ ↦ (1 : ℝ≥0∞)) ((U q.1)ᴴ * diagonal c * U q.2)) = volume B := by
  dsimp only
  have hNorm : Measurable (fun M : Matrix (Fin n) (Fin n) ℂ ↦ ‖M‖) := by
    simp only [Matrix.frobenius_norm_def]
    fun_prop
  have hB : MeasurableSet (Metric.ball (0 : Matrix (Fin n) (Fin n) ℂ) r) := by
    simpa only [Metric.ball, dist_zero_right] using measurableSet_lt hNorm measurable_const
  rw [lintegral_bruhat_coords (measurable_const.indicator hB)]
  exact lintegral_indicator_one hB
