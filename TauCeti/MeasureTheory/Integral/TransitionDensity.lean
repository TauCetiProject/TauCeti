/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Iterating successive-difference density integrals

The deterministic zero and successor formulas peel coordinates from a density integral,
without any probability-space hypotheses. `TauCeti.transitionRectangleIntegral` records the
resulting iterated integral on a rectangle, starting at a deterministic initial value.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The empty density integral is evaluation at the unique empty tuple. -/
theorem lintegral_mul_prod_sub_cons_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (F : (Fin 0 → ℝ) → ℝ≥0∞) :
    (∫⁻ y : Fin 0 → ℝ, F y * ∏ i, p i (y i - (Fin.cons a y : Fin 1 → ℝ) i.castSucc)) =
      F Fin.elim0 := by
  rw [Measure.volume_pi_eq_dirac Fin.elim0]
  simp

/-- Peel the first coordinate from a successive-difference density integral. The result
can be applied again to the inner integral, with shifted densities and test function. -/
theorem lintegral_mul_prod_sub_cons_succ {n : ℕ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (a : ℝ) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ y : Fin (n + 1) → ℝ, F y * ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)) =
      ∫⁻ x : ℝ, p 0 (x - a) * ∫⁻ y : Fin n → ℝ,
        F (Fin.cons x y) * ∏ i : Fin n,
          p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc) := by
  let g (y : Fin (n + 1) → ℝ) := F y * ∏ i,
    p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)
  have hg : Measurable g :=
    hF.mul (Finset.measurable_prod _ fun i _ ↦ (hp i).comp (by fun_prop))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  calc
    _ = ∫⁻ z : ℝ × (Fin n → ℝ), g (e.symm z) :=
      (he.lintegral_comp hg).symm
    _ = ∫⁻ x : ℝ, ∫⁻ y : Fin n → ℝ, g (e.symm (x, y)) :=
      lintegral_prod _ (hg.comp e.symm.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr fun x ↦ ?_
      have hi : Measurable (fun y : Fin n → ℝ ↦ F (Fin.cons x y) * ∏ i : Fin n,
          p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc)) :=
        (hF.comp (by fun_prop)).mul
          (Finset.measurable_prod _ fun i _ ↦ (hp i.succ).comp (by fun_prop))
      rw [← lintegral_const_mul _ hi]
      apply lintegral_congr fun y ↦ ?_
      simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, mul_left_comm]

/-- The empty rectangle has density integral one. -/
theorem setLIntegral_prod_sub_cons_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (B : Fin 0 → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i, p i (y i - (Fin.cons a y : Fin 1 → ℝ) i.castSucc)) = 1 := by
  rw [Measure.volume_pi_eq_dirac Fin.elim0]
  simp

/-- Peel one coordinate from a rectangle density integral. No normalization of the
transition densities is assumed. -/
theorem setLIntegral_prod_sub_cons_succ {n : ℕ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (a : ℝ) (B : Fin (n + 1) → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)) =
      ∫⁻ x in B 0, p 0 (x - a) * ∫⁻ y in Set.pi univ (fun i : Fin n ↦ B i.succ),
        ∏ i : Fin n, p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc) := by
  let g (y : Fin (n + 1) → ℝ) := ∏ i,
    p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)
  have hg : Measurable g :=
    Finset.measurable_prod _ fun i _ ↦ (hp i).comp (by fun_prop)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  have hpre : e.symm ⁻¹' Set.pi univ B =
      B 0 ×ˢ Set.pi univ (fun i : Fin n ↦ B i.succ) := by
    ext z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.forall_fin_succ]
  rw [← he.setLIntegral_comp_preimage_emb e.symm.measurableEmbedding g, hpre]
  rw [Measure.volume_eq_prod,
    setLIntegral_prod (fun z : ℝ × (Fin n → ℝ) ↦ g (e.symm z))
      (hg.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr fun x ↦ ?_
  have hi : Measurable (fun y : Fin n → ℝ ↦ ∏ i : Fin n,
      p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc)) :=
    Finset.measurable_prod _ fun i _ ↦ (hp i.succ).comp (by fun_prop)
  rw [← lintegral_const_mul _ hi]
  apply lintegral_congr fun y ↦ ?_
  simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.prod_univ_succ]

/-- The iterated transition-density integral on a finite rectangle, based at `a`.
There is no time-zero density: each step integrates only the next coordinate. -/
noncomputable def transitionRectangleIntegral : {n : ℕ} →
    (Fin n → ℝ → ℝ≥0∞) → ℝ → (Fin n → Set ℝ) → ℝ≥0∞
  | 0, _, _, _ => 1
  | n + 1, p, a, B => ∫⁻ x in B 0, p 0 (x - a) *
      transitionRectangleIntegral (fun i : Fin n ↦ p i.succ) x (fun i ↦ B i.succ)

/-- An empty iterated rectangle integral equals one. -/
@[simp]
theorem transitionRectangleIntegral_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (B : Fin 0 → Set ℝ) : transitionRectangleIntegral p a B = 1 := (rfl)

/-- Unfold the first step of an iterated rectangle integral. -/
@[simp]
theorem transitionRectangleIntegral_succ {n : ℕ} (p : Fin (n + 1) → ℝ → ℝ≥0∞)
    (a : ℝ) (B : Fin (n + 1) → Set ℝ) :
    transitionRectangleIntegral p a B = ∫⁻ x in B 0, p 0 (x - a) *
      transitionRectangleIntegral (fun i : Fin n ↦ p i.succ) x (fun i ↦ B i.succ) := (rfl)

/-- The iterated transition-density integral is measurable in its initial value. -/
@[fun_prop]
theorem measurable_transitionRectangleIntegral {n : ℕ} {p : Fin n → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (B : Fin n → Set ℝ) :
    Measurable fun a ↦ transitionRectangleIntegral p a B := by
  induction n with
  | zero => simp only [transitionRectangleIntegral_zero]; exact measurable_const
  | succ n ih =>
    simp only [transitionRectangleIntegral_succ]
    have hf : Measurable (fun z : ℝ × ℝ ↦ p 0 (z.2 - z.1) *
        transitionRectangleIntegral (fun i : Fin n ↦ p i.succ) z.2
          (fun i ↦ B i.succ)) :=
      ((hp 0).comp (measurable_snd.sub measurable_fst)).mul
        ((ih (fun i ↦ hp i.succ) (fun i ↦ B i.succ)).comp measurable_snd)
    exact hf.lintegral_prod_right' (ν := volume.restrict (B 0))

/-- The joint successive-difference integral on a rectangle equals its fully iterated
transition integral, including the empty rectangle. -/
theorem setLIntegral_prod_sub_cons_eq_transitionRectangleIntegral {n : ℕ}
    {p : Fin n → ℝ → ℝ≥0∞} (hp : ∀ i, Measurable (p i)) (a : ℝ)
    (B : Fin n → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) =
      transitionRectangleIntegral p a B := by
  induction n generalizing a with
  | zero => rw [setLIntegral_prod_sub_cons_zero, transitionRectangleIntegral_zero]
  | succ n ih =>
    rw [setLIntegral_prod_sub_cons_succ hp a B, transitionRectangleIntegral_succ]
    exact lintegral_congr fun x ↦ congrArg (p 0 (x - a) * ·)
      (ih (fun i ↦ hp i.succ) x (fun i ↦ B i.succ))

end TauCeti
