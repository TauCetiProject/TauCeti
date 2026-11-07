/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Moments.Variance

/-!
# The Efron–Stein inequality

This file proves the Efron–Stein inequality for a square-integrable measurable function of
independent coordinates, stated on `Measure.pi` over an arbitrary finite index type. If `X` has law
`Measure.pi μ`, then `Var f(X) ≤ ∑ i, E[Var_i f(X)]`, where `Var_i f(x)` is the variance of
`y ↦ f (Function.update x i y)` under `μ i`, i.e. the variance of `f` in the `i`-th coordinate
with all other coordinates frozen.

The two-factor law of total variance `evariance_prod_eq` and Jensen bound
`evariance_integral_prod_le` yield the two-factor Efron–Stein inequality `evariance_prod_le`. The
finite-coordinate proof is by induction on the number of coordinates, followed by transport along
an equivalence `Fin n ≃ ι`.

## Main results

* `TauCeti.Probability.efronStein`: the Efron–Stein inequality on `Measure.pi` over a finite index
  type, with arbitrary (dependent) coordinate spaces.

## References

* B. Efron and C. Stein, *The jackknife estimate of variance*, Ann. Statist. 9 (1981), 586–596.
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), Theorem 3.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti.Probability

universe u

/-- The Efron–Stein inequality on `Measure.pi` over `Fin 0`. -/
private theorem efronStein_zero {α : Fin 0 → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {f : (∀ i, α i) → ℝ} :
    evariance f (Measure.pi μ) ≤
      ∑ i, ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ := by
  have hc : ∀ ω, ∫ x, f x ∂Measure.pi μ = f ω := fun ω => by
    have hconst : f = fun _ => f ω := funext fun x => by rw [Subsingleton.elim x ω]
    rw [hconst]
    simp
  have h0 : ∀ ω, ‖f ω - f default‖ₑ ^ 2 = 0 := fun ω => by
    rw [Subsingleton.elim ω default]
    simp
  rw [evariance, hc default]
  simp [h0]

/-- Freezing the `succAbove 0 j`-th coordinate after splitting off coordinate `0` agrees with
freezing it in the original product. -/
private theorem evariance_comp_piFinSuccAbove_symm_update_succAbove {n : ℕ}
    {α : Fin (n + 1) → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    (f : (∀ i, α i) → ℝ) (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)) :
    evariance (fun y => f ((MeasurableEquiv.piFinSuccAbove α 0).symm
        (a, Function.update w j y))) (μ (Fin.succAbove 0 j)) =
      evariance (fun y => f (Function.update
        ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w)) (Fin.succAbove 0 j) y))
        (μ (Fin.succAbove 0 j)) := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.insertNth_update]

/-- Freezing all coordinates except `0` after splitting off coordinate `0` agrees with freezing
them in the original product. -/
private theorem evariance_comp_piFinSuccAbove_symm_update_zero {n : ℕ}
    {α : Fin (n + 1) → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    (f : (∀ i, α i) → ℝ) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)) :
    evariance (fun a' => f ((MeasurableEquiv.piFinSuccAbove α 0).symm (a', w))) (μ 0) =
      evariance (fun y => f (Function.update
        ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w)) 0 y)) (μ 0) := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.update_insertNth]

/-- Transport of a lower integral along the splitting of coordinate `0` off a finite product. -/
private theorem lintegral_comp_piFinSuccAbove_symm {n : ℕ} {α : Fin (n + 1) → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (g : (∀ i, α i) → ℝ≥0∞) :
    ∫⁻ p, g ((MeasurableEquiv.piFinSuccAbove α 0).symm p)
        ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
      ∫⁻ x, g x ∂Measure.pi μ :=
  ((measurePreserving_piFinSuccAbove μ 0).symm _).lintegral_comp_emb
    (MeasurableEquiv.piFinSuccAbove α 0).symm.measurableEmbedding g

/-- The average, over the remaining coordinates, of the variance in coordinate `0` is the `i = 0`
term of the Efron–Stein sum. -/
private theorem lintegral_evariance_piFinSuccAbove_symm_zero {n : ℕ} {α : Fin (n + 1) → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (∀ i, α i) → ℝ} (hf : Measurable f) :
    ∫⁻ w, evariance (fun a => f ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, w))) (μ 0)
        ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) =
      ∫⁻ x, evariance (fun y => f (Function.update x 0 y)) (μ 0) ∂Measure.pi μ := by
  have hGp : Measurable fun p => evariance (fun y => f (Function.update
      ((MeasurableEquiv.piFinSuccAbove α 0).symm p) 0 y)) (μ 0) :=
    (measurable_evariance_update μ 0 hf).comp (MeasurableEquiv.piFinSuccAbove α 0).symm.measurable
  rw [← lintegral_comp_piFinSuccAbove_symm μ, lintegral_prod _ hGp.aemeasurable]
  simp_rw [← evariance_comp_piFinSuccAbove_symm_update_zero μ f]
  rw [lintegral_const, measure_univ, mul_one]

/-- The Efron–Stein inequality on `Measure.pi` over `Fin n`. -/
private theorem efronStein_fin : ∀ {n : ℕ} {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {f : (∀ i, α i) → ℝ},
    Measurable f → MemLp f 2 (Measure.pi μ) →
    evariance f (Measure.pi μ) ≤
      ∑ i, ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ
  | 0, _, _, μ, _, _, _, _ => efronStein_zero μ
  | n + 1, α, _, μ, _, f, hf, hL => by
    -- Split off coordinate `0`: `e` identifies `∀ i, α i` with
    -- `α 0 × ∀ j, α (succAbove 0 j)`.
    set e := MeasurableEquiv.piFinSuccAbove α 0 with he
    have mp : MeasurePreserving e (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      measurePreserving_piFinSuccAbove μ 0
    have mps := mp.symm e
    set F : α 0 × (∀ j, α (Fin.succAbove 0 j)) → ℝ := fun p => f (e.symm p) with hFdef
    have hFm : Measurable F := hf.comp e.symm.measurable
    have hFL : MemLp F 2 ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      hL.comp_measurePreserving mps
    set G : Fin (n + 1) → (∀ i, α i) → ℝ≥0∞ :=
      fun i x => evariance (fun y => f (Function.update x i y)) (μ i) with hGdef
    have hGm : ∀ i, Measurable (G i) := fun i => measurable_evariance_update μ i hf
    have hEv : evariance f (Measure.pi μ) =
        evariance F ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
      (mps.evariance_fun_comp e.symm.measurableEmbedding f).symm
    have hG : ∀ (j : Fin n) (a : α 0) (w : ∀ j, α (Fin.succAbove 0 j)),
        evariance (fun y => F (a, Function.update w j y)) (μ (Fin.succAbove 0 j)) =
          G (Fin.succAbove 0 j) (e.symm (a, w)) := fun j a w =>
      evariance_comp_piFinSuccAbove_symm_update_succAbove μ f j a w
    have hslice := hFL.ae_memLp_prod_right
    have hGp : ∀ j, Measurable fun p => G j (e.symm p) := fun j =>
      (hGm j).comp e.symm.measurable
    -- Step 2: the induction hypothesis handles the remaining coordinates, slice by slice.
    have h1 : ∫⁻ a, evariance (fun w => F (a, w)) (Measure.pi fun j => μ (Fin.succAbove 0 j))
          ∂(μ 0) ≤ ∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ := by
      calc _ ≤ ∫⁻ a, ∑ j : Fin n, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) ∂(μ 0) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hslice] with a ha
            have := efronStein_fin (α := fun j => α (Fin.succAbove 0 j))
              (fun j => μ (Fin.succAbove 0 j)) (f := fun w => F (a, w))
              (hFm.comp measurable_prodMk_left) ha
            simpa only [hG] using this
        _ = ∑ j : Fin n, ∫⁻ a, ∫⁻ w, G (Fin.succAbove 0 j) (e.symm (a, w))
              ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) ∂(μ 0) :=
            lintegral_finsetSum' _ fun j _ =>
              (Measurable.lintegral_prod_right' (hGp _)).aemeasurable
        _ = _ := Finset.sum_congr rfl fun j _ => by
            rw [← lintegral_comp_piFinSuccAbove_symm μ, lintegral_prod _ (hGp _).aemeasurable]
    -- Step 3: the first-coordinate term is the `i = 0` summand.
    have h2 := lintegral_evariance_piFinSuccAbove_symm_zero μ hf
    calc evariance f (Measure.pi μ) = evariance F _ := hEv
      _ ≤ _ := evariance_prod_le hFm hFL
      _ ≤ (∑ j : Fin n, ∫⁻ x, G (Fin.succAbove 0 j) x ∂Measure.pi μ) +
          ∫⁻ x, G 0 x ∂Measure.pi μ := add_le_add h1 h2.le
      _ = ∑ i, ∫⁻ x, G i x ∂Measure.pi μ := by rw [Fin.sum_univ_succAbove _ 0, add_comm]

/-- **The Efron–Stein inequality** on `Measure.pi` over a finite index type: for a square
integrable measurable function `f` of independent coordinates, the variance of `f` is at most the
sum over `i` of the average variance of `f` in coordinate `i` with the other coordinates frozen. -/
theorem efronStein {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type u}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (∀ i, α i) → ℝ} (hf : Measurable f) (hL : MemLp f 2 (Measure.pi μ)) :
    evariance f (Measure.pi μ) ≤
      ∑ i, ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Φ := MeasurableEquiv.piCongrLeft α e
  have mp : MeasurePreserving Φ (Measure.pi fun k => μ (e k)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hupd : ∀ (k : Fin (Fintype.card ι)) (y : ∀ k, α (e k)) (v : α (e k)),
      Φ (Function.update y k v) = Function.update (Φ y) (e k) v := by
    intro k y v
    simpa [Φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using
      Function.piCongrLeft'_symm_update α e.symm y k v
  have hEv : evariance (fun x => f (Φ x)) (Measure.pi fun k => μ (e k)) =
      evariance f (Measure.pi μ) := mp.evariance_fun_comp Φ.measurableEmbedding f
  have hterm : ∀ k : Fin (Fintype.card ι),
      ∫⁻ y, evariance (fun v => f (Φ (Function.update y k v))) (μ (e k))
          ∂Measure.pi (fun k => μ (e k)) =
        ∫⁻ x, evariance (fun v => f (Function.update x (e k) v)) (μ (e k)) ∂Measure.pi μ := by
    intro k
    simp_rw [hupd]
    exact mp.lintegral_comp_emb Φ.measurableEmbedding
      (fun x => evariance (fun v => f (Function.update x (e k) v)) (μ (e k)))
  calc evariance f (Measure.pi μ)
      = evariance (fun x => f (Φ x)) (Measure.pi fun k => μ (e k)) := hEv.symm
    _ ≤ ∑ k, ∫⁻ y, evariance (fun v => f (Φ (Function.update y k v))) (μ (e k))
          ∂Measure.pi (fun k => μ (e k)) :=
        efronStein_fin (α := fun k => α (e k)) (fun k => μ (e k)) (f := fun x => f (Φ x))
          (hf.comp Φ.measurable) (hL.comp_measurePreserving mp)
    _ = ∑ k, ∫⁻ x, evariance (fun v => f (Function.update x (e k) v)) (μ (e k)) ∂Measure.pi μ :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = ∑ i, ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ :=
        Equiv.sum_comp e fun i =>
          ∫⁻ x, evariance (fun y => f (Function.update x i y)) (μ i) ∂Measure.pi μ

end TauCeti.Probability
