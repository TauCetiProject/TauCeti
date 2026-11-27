/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Composition
import Mathlib.Algebra.BigOperators.Fin

/-!
# Parallel stacking and affine combinations of ReLU networks

Placing two ReLU networks of the same positive depth `L + 1` side by side adds their hidden and
output widths (`ReLUNetRealizes.finAppend`). Composing the stacked network with a two-input
continuous affine output layer yields arbitrary affine combinations
`fun x => a * f₁ x + b * f₂ x + c` at the same depth `L + 1` (`ReLUNetComputes.affineComb`).

## References

* Raman Arora, Amitabh Basu, Poorya Mianjy, and Anirbit Mukherjee, *Understanding deep neural
  networks with rectified linear units*, ICLR 2018;
  [arXiv:1611.01491v6](https://arxiv.org/abs/1611.01491v6), Theorem 2.1 and Appendix D.
-/

public section

open Matrix

namespace TauCeti

open Neuromanifold

/-! ### Parallel stacking and affine combinations -/

private abbrev finAppendWidths {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    Fin (L + 2) → ℕ :=
  fun i => if i = 0 then n else d₁ i + d₂ i

private theorem finAppendWidths_zero {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    (reluSpec (finAppendWidths n d₁ d₂)).width 0 = n := by
  simp [finAppendWidths]

private theorem finAppendWidths_succ {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ)
    (i : Fin (L + 1)) :
    (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
      (reluSpec d₁).width i.succ + (reluSpec d₂).width i.succ := by
  simp [finAppendWidths, Fin.succ_ne_zero]

private def finAppendParams {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (reluSpec (finAppendWidths n d₁ d₂)).Parameters := fun i =>
  if hi : i = 0 then
    have hr : (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
        (reluSpec d₁).width (0 : Fin (L + 1)).succ +
          (reluSpec d₂).width (0 : Fin (L + 1)).succ := by
      subst hi; exact finAppendWidths_succ n d₁ d₂ 0
    have hc : (reluSpec (finAppendWidths n d₁ d₂)).width i.castSucc = n := by
      subst hi; exact finAppendWidths_zero n d₁ d₂
    (fun r c => Fin.addCases
        (fun r₁ => (θ₁ 0).1 r₁ (Fin.cast h0₁.symm (Fin.cast hc c)))
        (fun r₂ => (θ₂ 0).1 r₂ (Fin.cast h0₂.symm (Fin.cast hc c)))
        (Fin.cast hr r),
     fun r => Fin.addCases (θ₁ 0).2 (θ₂ 0).2 (Fin.cast hr r))
  else
    let k : Fin L := ⟨i.val - 1, by have := Fin.pos_iff_ne_zero.mpr hi; omega⟩
    have hi_eq : i = k.succ := Fin.ext (by simp [k]; have := Fin.pos_iff_ne_zero.mpr hi; omega)
    have hr : (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.succ.succ + (reluSpec d₂).width k.succ.succ := by
      rw [hi_eq]; exact finAppendWidths_succ n d₁ d₂ k.succ
    have hc : (reluSpec (finAppendWidths n d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.succ + (reluSpec d₂).width k.castSucc.succ := by
      rw [hi_eq]; exact finAppendWidths_succ n d₁ d₂ k.castSucc
    (fun r c => Fin.addCases
        (fun r₁ => Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hc c))
        (fun r₂ => Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂) (Fin.cast hc c))
        (Fin.cast hr r),
     fun r => Fin.addCases (θ₁ k.succ).2 (θ₂ k.succ).2 (Fin.cast hr r))

private theorem finAppendParams_zero {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (∀ r c, (finAppendParams h0₁ h0₂ θ₁ θ₂ 0).1 r c =
      Fin.addCases
        (fun r₁ => (θ₁ 0).1 r₁ (Fin.cast h0₁.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (fun r₂ => (θ₂ 0).1 r₂ (Fin.cast h0₂.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r)) ∧
    (∀ r, (finAppendParams h0₁ h0₂ θ₁ θ₂ 0).2 r =
      Fin.addCases (θ₁ 0).2 (θ₂ 0).2 (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r)) :=
  ⟨fun r c => by simp only [finAppendParams, ↓reduceDIte]; rfl,
   fun r => by simp only [finAppendParams, ↓reduceDIte]⟩

private theorem finAppendParams_succ {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L) :
    (∀ r c, (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r c =
      Fin.addCases
        (fun r₁ => Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0)
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
        (fun r₂ => Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂)
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r)) ∧
    (∀ r, (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).2 r =
      Fin.addCases (θ₁ k.succ).2 (θ₂ k.succ).2
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r)) := by
  have hk_ne : k.succ ≠ 0 := Fin.succ_ne_zero k
  have hfn₁ : ∀ (k' : Fin L) (_ : k' = k)
      (hr' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ =
        (reluSpec d₁).width k'.succ.succ + (reluSpec d₂).width k'.succ.succ)
      (hc' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc =
        (reluSpec d₁).width k'.castSucc.succ + (reluSpec d₂).width k'.castSucc.succ)
      (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ))
      (c : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc)),
      Fin.addCases (motive := fun _ => ℝ)
          (fun r₁ => Fin.addCases (motive := fun _ => ℝ)
            (fun c₁ => (θ₁ k'.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hc' c))
          (fun r₂ => Fin.addCases (motive := fun _ => ℝ)
            (fun _ => 0) (fun c₂ => (θ₂ k'.succ).1 r₂ c₂) (Fin.cast hc' c))
          (Fin.cast hr' r) =
        Fin.addCases (motive := fun _ => ℝ)
          (fun r₁ => Fin.addCases (motive := fun _ => ℝ)
            (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (fun r₂ => Fin.addCases (motive := fun _ => ℝ)
            (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r) := by
    rintro _ rfl _ _ _ _
    rfl
  have hfn₂ : ∀ (k' : Fin L) (_ : k' = k)
      (hr' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ =
        (reluSpec d₁).width k'.succ.succ + (reluSpec d₂).width k'.succ.succ)
      (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ)),
      Fin.addCases (motive := fun _ => ℝ) (θ₁ k'.succ).2 (θ₂ k'.succ).2 (Fin.cast hr' r) =
        Fin.addCases (motive := fun _ => ℝ) (θ₁ k.succ).2 (θ₂ k.succ).2
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r) := by
    rintro _ rfl _ _
    rfl
  refine ⟨fun r c => ?_, fun r => ?_⟩
  · simp only [finAppendParams, hk_ne, ↓reduceDIte]
    exact hfn₁ ⟨k.succ.val - 1, _⟩ (Fin.ext (by simp)) _ _ r c
  · simp only [finAppendParams, hk_ne, ↓reduceDIte]
    exact hfn₂ ⟨k.succ.val - 1, _⟩ (Fin.ext (by simp)) _ r

private theorem finAppend_zero_step {n L : ℕ} {d dₐ : Fin (L + 2) → ℕ}
    (hd0 : (reluSpec d).width 0 = n) (h0ₐ : (reluSpec dₐ).width 0 = n)
    (θ : (reluSpec d).Parameters) (θₐ : (reluSpec dₐ).Parameters)
    (x : Fin n → ℝ) (r : Fin ((reluSpec d).width (0 : Fin (L + 1)).succ))
    (rₐ : Fin ((reluSpec dₐ).width (0 : Fin (L + 1)).succ))
    (hW : ∀ c, (θ 0).1 r c =
      (θₐ 0).1 rₐ (Fin.cast h0ₐ.symm (Fin.cast hd0 c)))
    (hb : (θ 0).2 r = (θₐ 0).2 rₐ) :
    (reluSpec d).evalPrefix θ (fun i => x (Fin.cast hd0 i)) (0 : Fin (L + 1)).succ r =
      (reluSpec dₐ).evalPrefix θₐ (fun i => x (Fin.cast h0ₐ i)) (0 : Fin (L + 1)).succ rₐ := by
  have h0 : (reluSpec d).evalPrefix θ (fun i => x (Fin.cast hd0 i)) (0 : Fin (L + 1)).castSucc =
      fun i => x (Fin.cast hd0 i) := by simp
  have h0ₐ' : (reluSpec dₐ).evalPrefix θₐ (fun i => x (Fin.cast h0ₐ i))
      (0 : Fin (L + 1)).castSucc = fun i => x (Fin.cast h0ₐ i) := by simp
  rw [MLPSpec.evalPrefix_succ_apply, MLPSpec.evalPrefix_succ_apply, h0, h0ₐ',
    layerActivation_reluSpec_eq d dₐ Iff.rfl]
  congr 1
  simp only [Matrix.mulVec, dotProduct, hW, hb]
  congr 1
  refine Fintype.sum_equiv ((finCongr hd0).trans (finCongr h0ₐ).symm) _ _ fun c => ?_
  simp [finCongr_apply]

private theorem dotProduct_cast_addCases {w₁ w₂ w : ℕ} (hw : w = w₁ + w₂)
    (f₁ : Fin w₁ → ℝ) (f₂ : Fin w₂ → ℝ) (v : Fin w → ℝ) :
    (fun c => Fin.addCases f₁ f₂ (Fin.cast hw c)) ⬝ᵥ v =
      (∑ c₁ : Fin w₁, f₁ c₁ * v (Fin.cast hw.symm (Fin.castAdd w₂ c₁))) +
      (∑ c₂ : Fin w₂, f₂ c₂ * v (Fin.cast hw.symm (Fin.natAdd w₁ c₂))) := by
  simp only [dotProduct]
  rw [← Equiv.sum_comp (finCongr hw).symm, Fin.sum_univ_add]
  simp [finCongr_apply]

private theorem finAppend_succ_step {L : ℕ} {d dₐ : Fin (L + 2) → ℕ}
    (k : Fin L) (θ : (reluSpec d).Parameters) (θₐ : (reluSpec dₐ).Parameters)
    (x₀ : Fin ((reluSpec d).width 0) → ℝ) (xₐ : Fin ((reluSpec dₐ).width 0) → ℝ)
    (r : Fin ((reluSpec d).width k.succ.succ)) (rₐ : Fin ((reluSpec dₐ).width k.succ.succ))
    (hdot : (θ k.succ).1 r ⬝ᵥ (reluSpec d).evalPrefix θ x₀ k.succ.castSucc =
      (θₐ k.succ).1 rₐ ⬝ᵥ (reluSpec dₐ).evalPrefix θₐ xₐ k.succ.castSucc)
    (hb : (θ k.succ).2 r = (θₐ k.succ).2 rₐ) :
    (reluSpec d).evalPrefix θ x₀ k.succ.succ r =
      (reluSpec dₐ).evalPrefix θₐ xₐ k.succ.succ rₐ := by
  rw [MLPSpec.evalPrefix_succ_apply, MLPSpec.evalPrefix_succ_apply,
    layerActivation_reluSpec_eq d dₐ Iff.rfl]
  congr 1
  simp only [Matrix.mulVec]
  rw [hdot, hb]

private theorem finAppendParams_evalPrefix {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (x : Fin n → ℝ)
    (k : Fin (L + 1)) (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ)) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (finAppendWidths_zero n d₁ d₂) i)) k.succ r =
      Fin.append
        ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ)
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k) r) := by
  have hd0 := finAppendWidths_zero n d₁ d₂
  have hd_succ := finAppendWidths_succ n d₁ d₂
  induction k using Fin.induction with
  | zero =>
    obtain ⟨hW0, hb0⟩ := finAppendParams_zero h0₁ h0₂ θ₁ θ₂
    cases hrc : Fin.cast (hd_succ 0) r using Fin.addCases with
    | left r₁ =>
      rw [Fin.append_left]
      exact finAppend_zero_step hd0 h0₁ (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₁ x r r₁
        (fun c => by rw [hW0, hrc, Fin.addCases_left])
        (by rw [hb0, hrc, Fin.addCases_left])
    | right r₂ =>
      rw [Fin.append_right]
      exact finAppend_zero_step hd0 h0₂ (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₂ x r r₂
        (fun c => by rw [hW0, hrc, Fin.addCases_right])
        (by rw [hb0, hrc, Fin.addCases_right])
  | succ k ih =>
    obtain ⟨hWk, hbk⟩ := finAppendParams_succ h0₁ h0₂ θ₁ θ₂ k
    have hcast_w : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc =
        (reluSpec d₁).width k.castSucc.succ + (reluSpec d₂).width k.castSucc.succ :=
      hd_succ k.castSucc
    have hk_cast : k.succ.castSucc = k.castSucc.succ := Fin.ext rfl
    cases hrc : Fin.cast (hd_succ k.succ) r using Fin.addCases with
    | left r₁ =>
      rw [Fin.append_left]
      refine finAppend_succ_step k (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₁
        (fun i => x (Fin.cast hd0 i)) (fun i => x (Fin.cast h0₁ i)) r r₁ ?_
        (by simp [hbk, hrc])
      have hrow : (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r = fun c =>
          Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hcast_w c) := by
        ext c
        simp [hWk, hrc]
      rw [hrow, dotProduct_cast_addCases hcast_w]
      simp only [zero_mul, Finset.sum_const_zero, add_zero, dotProduct]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      congr 1
      have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hk_cast)
          (Fin.cast hcast_w.symm (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁)) =
          Fin.cast (hd_succ k.castSucc).symm
            (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁) :=
        Fin.ext (by simp only [Fin.val_cast])
      rw [MLPSpec.evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) _ hk_cast, hidx_eq, ih,
        Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_left,
        MLPSpec.evalPrefix_cast (reluSpec d₁) θ₁ _ hk_cast]
      exact congrArg _ (Fin.ext (by simp only [Fin.val_cast]))
    | right r₂ =>
      rw [Fin.append_right]
      refine finAppend_succ_step k (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₂
        (fun i => x (Fin.cast hd0 i)) (fun i => x (Fin.cast h0₂ i)) r r₂ ?_
        (by simp [hbk, hrc])
      have hrow : (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r = fun c =>
          Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂) (Fin.cast hcast_w c) := by
        ext c
        simp [hWk, hrc]
      rw [hrow, dotProduct_cast_addCases hcast_w]
      simp only [zero_mul, Finset.sum_const_zero, zero_add, dotProduct]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      congr 1
      have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hk_cast)
          (Fin.cast hcast_w.symm (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂)) =
          Fin.cast (hd_succ k.castSucc).symm
            (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂) :=
        Fin.ext (by simp only [Fin.val_cast])
      rw [MLPSpec.evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) _ hk_cast, hidx_eq, ih,
        Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_right,
        MLPSpec.evalPrefix_cast (reluSpec d₂) θ₂ _ hk_cast]
      exact congrArg _ (Fin.ext (by simp only [Fin.val_cast]))

/-- Stacking two ReLU networks of the same positive depth `L + 1` in parallel yields a network of
depth `L + 1` with hidden widths `d₁ i + d₂ i` realizing
`fun x => Fin.append (f₁ x) (f₂ x)`. -/
theorem ReLUNetRealizes.finAppend {n m₁ m₂ L : ℕ}
    {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ : (Fin n → ℝ) → (Fin m₁ → ℝ)} {f₂ : (Fin n → ℝ) → (Fin m₂ → ℝ)}
    (hf₁ : ReLUNetRealizes d₁ f₁) (hf₂ : ReLUNetRealizes d₂ f₂) :
    ReLUNetRealizes (fun i : Fin (L + 2) => if i = 0 then n else d₁ i + d₂ i)
      (fun x => Fin.append (f₁ x) (f₂ x)) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hf₁
  obtain ⟨h0₂, hm₂, θ₂, hθ₂⟩ := hf₂
  have h0₁' : (reluSpec d₁).width 0 = n := (congrFun (reluSpec_width d₁) 0).trans h0₁
  have h0₂' : (reluSpec d₂).width 0 = n := (congrFun (reluSpec_width d₂) 0).trans h0₂
  have hm₁' : (reluSpec d₁).width (Fin.last L).succ = m₁ :=
    (congrFun (reluSpec_width d₁) (Fin.last (L + 1))).trans hm₁
  have hm₂' : (reluSpec d₂).width (Fin.last L).succ = m₂ :=
    (congrFun (reluSpec_width d₂) (Fin.last (L + 1))).trans hm₂
  have hd0' : finAppendWidths n d₁ d₂ 0 = n := by simp
  have hd0 := finAppendWidths_zero n d₁ d₂
  have hdL : finAppendWidths n d₁ d₂ (Fin.last (L + 1)) = m₁ + m₂ := by
    simp [finAppendWidths, hm₁, hm₂]
  have hdL' : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last (L + 1)) = m₁ + m₂ :=
    (congrFun (reluSpec_width _) _).trans hdL
  have hd_succ := finAppendWidths_succ n d₁ d₂
  refine ⟨hd0', hdL, finAppendParams h0₁' h0₂' θ₁ θ₂, fun x j => ?_⟩
  have hm_eq : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last L).succ = m₁ + m₂ := by
    simp [finAppendWidths, hm₁, hm₂]
  have hlast := finAppendParams_evalPrefix h0₁' h0₂' θ₁ θ₂ x (Fin.last L) (Fin.cast hm_eq.symm j)
  have hlast_eq : (Fin.last (L + 1) : Fin (L + 2)) = (Fin.last L).succ := Fin.ext rfl
  have hrealize_eq :
      (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0' i)) (Fin.last (L + 1)) (Fin.cast hdL.symm j) =
        (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0 i)) (Fin.last (L + 1)) (Fin.cast hdL'.symm j) :=
    rfl
  rw [MLPSpec.realize_def]
  refine hrealize_eq.trans ?_
  rw [MLPSpec.evalPrefix_cast _ _ _ hlast_eq]
  have hcast_j : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hlast_eq)
      (Fin.cast hdL'.symm j) = Fin.cast hm_eq.symm j :=
    Fin.ext (by simp only [Fin.val_cast])
  rw [hcast_j, hlast]
  dsimp only
  cases j using Fin.addCases with
  | left j₁ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.castAdd m₂ j₁)) =
        Fin.castAdd ((reluSpec d₂).width (Fin.last L).succ) (Fin.cast hm₁'.symm j₁) :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_castAdd])
    rw [hidx, Fin.append_left, Fin.append_left,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₁ x j₁
  | right j₂ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.natAdd m₁ j₂)) =
        Fin.natAdd ((reluSpec d₁).width (Fin.last L).succ) (Fin.cast hm₂'.symm j₂) :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, hm₁'])
    rw [hidx, Fin.append_right, Fin.append_right,
      MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₂ x j₂

/-- Parallel affine combination of two ReLU networks of the same positive depth `L + 1`: if `d₁`
computes `f₁` and `d₂` computes `f₂`, then a network of depth `L + 1` with hidden widths
`d₁ i + d₂ i` computes `fun x => a * f₁ x + b * f₂ x + c`. -/
theorem ReLUNetComputes.affineComb {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ f₂ : (Fin n → ℝ) → ℝ} (hf₁ : ReLUNetComputes d₁ f₁)
    (hf₂ : ReLUNetComputes d₂ f₂) (a b c : ℝ) :
    ReLUNetComputes
      (fun i : Fin (L + 2) =>
        if i = 0 then n else if i = Fin.last (L + 1) then 1 else d₁ i + d₂ i)
      (fun x => a * f₁ x + b * f₂ x + c) := by
  let g₁ := reluNetComputes_iff_reluNetRealizes.mp hf₁
  let g₂ := reluNetComputes_iff_reluNetRealizes.mp hf₂
  let A : (Fin 2 → ℝ) →ᴬ[ℝ] ℝ :=
    { toFun := fun y => a * y 0 + b * y 1 + c
      linear :=
        { toFun := fun y => a * y 0 + b * y 1
          map_add' := fun y z => by simp only [Pi.add_apply]; ring
          map_smul' := fun r y => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      map_vadd' := fun v y => by simp [vadd_eq_add]; ring
      cont := by fun_prop }
  have hcomp :=
    ReLUNetComputes.comp (g₁.finAppend g₂) (ReLUNetComputes.of_continuousAffineMap A)
  have heq : (A ∘ fun x => Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x)) =
      fun x => a * f₁ x + b * f₂ x + c := by
    funext x
    have h0 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 0 = f₁ x :=
      Fin.append_left _ _ 0
    have h1 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 1 = f₂ x :=
      Fin.append_right _ _ 0
    simp [A, h0, h1]
  rw [heq] at hcomp
  refine hcomp.of_width_eq ?_
  ext i
  by_cases hi0 : i = 0
  · subst hi0
    simp
  · by_cases hiL : i = Fin.last (L + 1)
    · subst hiL
      simp
    · have hle : i.val ≤ L := by
        have := i.isLt
        have : i.val ≠ L + 1 := fun h => hiL (Fin.ext h)
        omega
      simp only [compWidths, hle, ↓reduceDIte, hi0, ↓reduceIte, hiL]

end TauCeti
