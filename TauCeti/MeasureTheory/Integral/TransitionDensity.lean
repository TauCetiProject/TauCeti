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
without any probability-space hypotheses. `TauCeti.transitionRectangleLIntegral` records the
resulting iterated integral on a rectangle, starting at a deterministic initial value.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The weighted density integral on the zero-coordinate rectangle evaluates the unique
empty tuple. -/
theorem setLIntegral_mul_prod_sub_cons_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (F : (Fin 0 → ℝ) → ℝ≥0∞) (B : Fin 0 → Set ℝ) :
    (∫⁻ y in Set.pi univ B,
      F y * ∏ i, p i (y i - (Fin.cons a y : Fin 1 → ℝ) i.castSucc)) = F Fin.elim0 := by
  classical
  rw [Measure.volume_pi_eq_dirac Fin.elim0, setLIntegral_dirac]
  simp

/-- Peel the first coordinate from a weighted rectangle density integral. No measurability
of the rectangle or normalization of the transition densities is assumed. -/
theorem setLIntegral_mul_prod_sub_cons_succ {n : ℕ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (a : ℝ) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (B : Fin (n + 1) → Set ℝ) :
    (∫⁻ y in Set.pi univ B, F y * ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)) =
      ∫⁻ x in B 0, p 0 (x - a) * ∫⁻ y in Set.pi univ (fun i : Fin n ↦ B i.succ),
        F (Fin.cons x y) * ∏ i : Fin n,
          p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc) := by
  let g (y : Fin (n + 1) → ℝ) := F y * ∏ i,
    p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)
  have hg : Measurable g :=
    hF.mul (Finset.measurable_prod _ fun i _ ↦ (hp i).comp (by fun_prop))
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
  have hi : Measurable (fun y : Fin n → ℝ ↦ F (Fin.cons x y) * ∏ i : Fin n,
      p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc)) :=
    (hF.comp (by fun_prop)).mul
      (Finset.measurable_prod _ fun i _ ↦ (hp i.succ).comp (by fun_prop))
  rw [← lintegral_const_mul _ hi]
  apply lintegral_congr fun y ↦ ?_
  simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.prod_univ_succ, mul_left_comm]

/-- The zero-coordinate density integral is evaluation at the unique empty tuple. -/
theorem lintegral_mul_prod_sub_cons_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (F : (Fin 0 → ℝ) → ℝ≥0∞) :
    (∫⁻ y : Fin 0 → ℝ, F y * ∏ i, p i (y i - (Fin.cons a y : Fin 1 → ℝ) i.castSucc)) =
      F Fin.elim0 := by
  simpa only [Set.pi_univ, setLIntegral_univ] using
    setLIntegral_mul_prod_sub_cons_zero p a F (fun _ ↦ univ)

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
  simpa only [Set.pi_univ, setLIntegral_univ] using
    setLIntegral_mul_prod_sub_cons_succ hp a hF (fun _ ↦ univ)

/-- The zero-coordinate rectangle has density integral one. -/
theorem setLIntegral_prod_sub_cons_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (B : Fin 0 → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i, p i (y i - (Fin.cons a y : Fin 1 → ℝ) i.castSucc)) = 1 := by
  simpa only [one_mul] using setLIntegral_mul_prod_sub_cons_zero p a (fun _ ↦ 1) B

/-- Peel one coordinate from a rectangle density integral. No normalization of the
transition densities is assumed. -/
theorem setLIntegral_prod_sub_cons_succ {n : ℕ} {p : Fin (n + 1) → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (a : ℝ) (B : Fin (n + 1) → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 2) → ℝ) i.castSucc)) =
      ∫⁻ x in B 0, p 0 (x - a) * ∫⁻ y in Set.pi univ (fun i : Fin n ↦ B i.succ),
        ∏ i : Fin n, p i.succ (y i - (Fin.cons x y : Fin (n + 1) → ℝ) i.castSucc) := by
  simpa only [one_mul] using
    setLIntegral_mul_prod_sub_cons_succ hp a (F := fun _ ↦ 1) measurable_const B

/-- The iterated transition-density lower integral over the coordinate sets `B`, starting at `a`.
The functions `p` are increment densities: the first step uses `p 0 (x - a)`, then each step
uses the difference from the preceding coordinate. There is no time-zero density. -/
noncomputable def transitionRectangleLIntegral : {n : ℕ} →
    (p : Fin n → ℝ → ℝ≥0∞) → (a : ℝ) → (B : Fin n → Set ℝ) → ℝ≥0∞
  | 0, _, _, _ => 1
  | n + 1, p, a, B => ∫⁻ x in B 0, p 0 (x - a) *
      transitionRectangleLIntegral (fun i : Fin n ↦ p i.succ) x (fun i ↦ B i.succ)

/-- The iterated integral on the zero-coordinate rectangle equals one. -/
@[simp]
theorem transitionRectangleLIntegral_zero (p : Fin 0 → ℝ → ℝ≥0∞) (a : ℝ)
    (B : Fin 0 → Set ℝ) : transitionRectangleLIntegral p a B = 1 := (rfl)

/-- Unfold the first step of an iterated rectangle integral. -/
@[simp]
theorem transitionRectangleLIntegral_succ {n : ℕ} (p : Fin (n + 1) → ℝ → ℝ≥0∞)
    (a : ℝ) (B : Fin (n + 1) → Set ℝ) :
    transitionRectangleLIntegral p a B = ∫⁻ x in B 0, p 0 (x - a) *
      transitionRectangleLIntegral (fun i : Fin n ↦ p i.succ) x (fun i ↦ B i.succ) := (rfl)

/-- The iterated transition-density integral is measurable in its initial value. -/
@[fun_prop]
theorem measurable_transitionRectangleLIntegral {n : ℕ} {p : Fin n → ℝ → ℝ≥0∞}
    (hp : ∀ i, Measurable (p i)) (B : Fin n → Set ℝ) :
    Measurable fun a ↦ transitionRectangleLIntegral p a B := by
  induction n with
  | zero => simp only [transitionRectangleLIntegral_zero]; exact measurable_const
  | succ n ih =>
    simp only [transitionRectangleLIntegral_succ]
    have hf : Measurable (fun z : ℝ × ℝ ↦ p 0 (z.2 - z.1) *
        transitionRectangleLIntegral (fun i : Fin n ↦ p i.succ) z.2
          (fun i ↦ B i.succ)) :=
      ((hp 0).comp (measurable_snd.sub measurable_fst)).mul
        ((ih (fun i ↦ hp i.succ) (fun i ↦ B i.succ)).comp measurable_snd)
    exact hf.lintegral_prod_right' (ν := volume.restrict (B 0))

/-- The joint successive-difference integral on a rectangle equals its fully iterated
transition integral, including the zero-coordinate (`n = 0`) case. -/
theorem setLIntegral_prod_sub_cons_eq_transitionRectangleLIntegral {n : ℕ}
    {p : Fin n → ℝ → ℝ≥0∞} (hp : ∀ i, Measurable (p i)) (a : ℝ)
    (B : Fin n → Set ℝ) :
    (∫⁻ y in Set.pi univ B, ∏ i,
      p i (y i - (Fin.cons a y : Fin (n + 1) → ℝ) i.castSucc)) =
      transitionRectangleLIntegral p a B := by
  induction n generalizing a with
  | zero => rw [setLIntegral_prod_sub_cons_zero, transitionRectangleLIntegral_zero]
  | succ n ih =>
    rw [setLIntegral_prod_sub_cons_succ hp a B, transitionRectangleLIntegral_succ]
    exact lintegral_congr fun x ↦ congrArg (p 0 (x - a) * ·)
      (ih (fun i ↦ hp i.succ) x (fun i ↦ B i.succ))

end TauCeti
