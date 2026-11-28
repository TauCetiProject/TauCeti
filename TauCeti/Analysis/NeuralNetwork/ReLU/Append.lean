/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Composition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Parallel stacking and affine combinations of ReLU networks

Placing two ReLU networks of the same positive depth `L + 1` side by side adds their hidden and
output widths (`finAppendWidths`, `ReLUNetRealizes.finAppend`). Composing the stacked network with
a two-input continuous affine output layer yields arbitrary affine combinations
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

/-- The width tuple obtained by stacking two depth-`(L + 1)` networks in parallel on a common
input of width `n`: input width `n`, and at every layer `i + 1` the sum `d₁ i.succ + d₂ i.succ`. -/
def finAppendWidths {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) : Fin (L + 2) → ℕ :=
  Fin.cons n (fun i => d₁ i.succ + d₂ i.succ)

/-- `finAppendWidths n d₁ d₂` is `Fin.cons n (fun i => d₁ i.succ + d₂ i.succ)`. -/
theorem finAppendWidths_def {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    finAppendWidths n d₁ d₂ = Fin.cons n (fun i => d₁ i.succ + d₂ i.succ) := (rfl)

/-- The input width of `finAppendWidths n d₁ d₂` is `n`. -/
@[simp]
theorem finAppendWidths_zero {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    finAppendWidths n d₁ d₂ 0 = n :=
  Fin.cons_zero _ _

/-- Every layer `i.succ` of `finAppendWidths n d₁ d₂` has width `d₁ i.succ + d₂ i.succ`. -/
@[simp]
theorem finAppendWidths_succ {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) (i : Fin (L + 1)) :
    finAppendWidths n d₁ d₂ i.succ = d₁ i.succ + d₂ i.succ :=
  Fin.cons_succ _ _ i

/-- The output width of `finAppendWidths n d₁ d₂` is
`d₁ (Fin.last (L + 1)) + d₂ (Fin.last (L + 1))`. -/
@[simp]
theorem finAppendWidths_last {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    finAppendWidths n d₁ d₂ (Fin.last (L + 1)) =
      d₁ (Fin.last (L + 1)) + d₂ (Fin.last (L + 1)) :=
  finAppendWidths_succ n d₁ d₂ (Fin.last L)

/-- Every non-input layer (in particular every hidden layer) of `finAppendWidths n d₁ d₂` has
width `d₁ i + d₂ i`. -/
theorem finAppendWidths_of_ne_zero {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ)
    {i : Fin (L + 2)} (hi : i ≠ 0) :
    finAppendWidths n d₁ d₂ i = d₁ i + d₂ i := by
  rcases Fin.eq_succ_of_ne_zero hi with ⟨j, rfl⟩
  exact finAppendWidths_succ n d₁ d₂ j

private theorem reluSpec_finAppendWidths_zero {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    (reluSpec (finAppendWidths n d₁ d₂)).width 0 = n :=
  finAppendWidths_zero n d₁ d₂

private theorem reluSpec_finAppendWidths_succ {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ)
    (i : Fin (L + 1)) :
    (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
      (reluSpec d₁).width i.succ + (reluSpec d₂).width i.succ :=
  finAppendWidths_succ n d₁ d₂ i

private def finAppendParamZero {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    Matrix (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width (0 : Fin (L + 1)).succ))
        (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width (0 : Fin (L + 1)).castSucc)) ℝ ×
      (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width (0 : Fin (L + 1)).succ) → ℝ) :=
  let eRow := (finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ 0)).trans finSumFinEquiv.symm
  let hd0 : (reluSpec (finAppendWidths n d₁ d₂)).width (0 : Fin (L + 1)).castSucc = n :=
    reluSpec_finAppendWidths_zero n d₁ d₂
  let h0₁' : (reluSpec d₁).width (0 : Fin (L + 1)).castSucc = n := h0₁
  let h0₂' : (reluSpec d₂).width (0 : Fin (L + 1)).castSucc = n := h0₂
  let W₁' := (θ₁ 0).1.submatrix (Equiv.refl _) (finCongr h0₁').symm
  let W₂' := (θ₂ 0).1.submatrix (Equiv.refl _) (finCongr h0₂').symm
  ((Matrix.fromRows W₁' W₂').submatrix eRow (finCongr hd0),
    Sum.elim (θ₁ 0).2 (θ₂ 0).2 ∘ eRow)

private def finAppendParamSucc {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L) :
    Matrix (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ))
        (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc)) ℝ ×
      (Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ) → ℝ) :=
  let eRow := (finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ k.succ)).trans finSumFinEquiv.symm
  let eCol :=
    (finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ k.castSucc)).trans finSumFinEquiv.symm
  ((Matrix.fromBlocks (θ₁ k.succ).1 0 0 (θ₂ k.succ).1).submatrix eRow eCol,
    Sum.elim (θ₁ k.succ).2 (θ₂ k.succ).2 ∘ eRow)

private def finAppendParams {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (reluSpec (finAppendWidths n d₁ d₂)).Parameters :=
  Fin.cons (finAppendParamZero h0₁ h0₂ θ₁ θ₂) (finAppendParamSucc θ₁ θ₂)

private theorem finAppendParams_zero {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    finAppendParams h0₁ h0₂ θ₁ θ₂ 0 = finAppendParamZero h0₁ h0₂ θ₁ θ₂ :=
  Fin.cons_zero _ _

private theorem finAppendParams_succ {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L) :
    finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ = finAppendParamSucc θ₁ θ₂ k :=
  Fin.cons_succ _ _ k

private theorem finAppendParams_evalPrefix_zero {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (x : Fin n → ℝ) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) (0 : Fin (L + 1)).succ =
      Sum.elim
        ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) (0 : Fin (L + 1)).succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) (0 : Fin (L + 1)).succ) ∘
        ((finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ 0)).trans finSumFinEquiv.symm) := by
  have hd_succ := reluSpec_finAppendWidths_succ n d₁ d₂
  have hd0 : (reluSpec (finAppendWidths n d₁ d₂)).width (0 : Fin (L + 1)).castSucc = n :=
    reluSpec_finAppendWidths_zero n d₁ d₂
  have h0₁' : (reluSpec d₁).width (0 : Fin (L + 1)).castSucc = n := h0₁
  have h0₂' : (reluSpec d₂).width (0 : Fin (L + 1)).castSucc = n := h0₂
  have h0_eval : (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix
      (finAppendParams h0₁ h0₂ θ₁ θ₂)
      (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i))
      (0 : Fin (L + 1)).castSucc =
      fun i => x (Fin.cast hd0 i) := by
    ext i; simp [Fin.castSucc_zero]
  have hx₁ : (reluSpec d₁).evalPrefix θ₁
      (fun i => x (Fin.cast h0₁ i)) (0 : Fin (L + 1)).castSucc =
      fun i => x (Fin.cast h0₁' i) := by ext i; simp [Fin.castSucc_zero]
  have hx₂ : (reluSpec d₂).evalPrefix θ₂
      (fun i => x (Fin.cast h0₂ i)) (0 : Fin (L + 1)).castSucc =
      fun i => x (Fin.cast h0₂' i) := by ext i; simp [Fin.castSucc_zero]
  have hW : ((finAppendParams h0₁ h0₂ θ₁ θ₂ 0).1 *ᵥ (fun i => x (Fin.cast hd0 i)) +
        (finAppendParams h0₁ h0₂ θ₁ θ₂ 0).2) =
      Sum.elim ((θ₁ 0).1 *ᵥ (fun i => x (Fin.cast h0₁' i)) + (θ₁ 0).2)
        ((θ₂ 0).1 *ᵥ (fun i => x (Fin.cast h0₂' i)) + (θ₂ 0).2) ∘
        ((finCongr (hd_succ 0)).trans finSumFinEquiv.symm) := by
    rw [finAppendParams_zero]; dsimp only [finAppendParamZero]
    rw [Matrix.submatrix_mulVec_equiv _ _ ((finCongr (hd_succ 0)).trans finSumFinEquiv.symm)
      (finCongr hd0)]
    have hx_comp : (fun i => x (Fin.cast hd0 i)) ∘ ⇑(finCongr hd0).symm = x := rfl
    rw [hx_comp, Matrix.fromRows_mulVec,
      Matrix.submatrix_mulVec_equiv (θ₁ 0).1 x (Equiv.refl _) (finCongr h0₁').symm,
      Matrix.submatrix_mulVec_equiv (θ₂ 0).1 x (Equiv.refl _) (finCongr h0₂').symm]
    simp only [Equiv.symm_symm, Equiv.coe_refl, Function.comp_id]
    exact (congrArg (· ∘ ((finCongr (hd_succ 0)).trans finSumFinEquiv.symm))
      (Sum.elim_add_add ((θ₁ 0).1 *ᵥ (fun i => x (Fin.cast h0₁' i))) (θ₁ 0).2
        ((θ₂ 0).1 *ᵥ (fun i => x (Fin.cast h0₂' i))) (θ₂ 0).2)).symm
  have hs₁ : (reluSpec (finAppendWidths n d₁ d₂)).layerActivation 0 ∘
      ((θ₁ 0).1 *ᵥ (fun i => x (Fin.cast h0₁' i)) + (θ₁ 0).2) =
      (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) (0 : Fin (L + 1)).succ := by
    rw [layerActivation_reluSpec_eq (finAppendWidths n d₁ d₂) d₁ Iff.rfl, MLPSpec.evalPrefix_succ,
      hx₁]; rfl
  have hs₂ : (reluSpec (finAppendWidths n d₁ d₂)).layerActivation 0 ∘
      ((θ₂ 0).1 *ᵥ (fun i => x (Fin.cast h0₂' i)) + (θ₂ 0).2) =
      (reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) (0 : Fin (L + 1)).succ := by
    rw [layerActivation_reluSpec_eq (finAppendWidths n d₁ d₂) d₂ Iff.rfl, MLPSpec.evalPrefix_succ,
      hx₂]; rfl
  rw [MLPSpec.evalPrefix_succ, h0_eval]
  simp_rw [← Pi.add_apply]
  rw [hW]
  change ((reluSpec (finAppendWidths n d₁ d₂)).layerActivation 0 ∘ Sum.elim _ _) ∘ _ = _
  rw [Sum.comp_elim, hs₁, hs₂]

private theorem finAppendParams_evalPrefix_succ {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (x : Fin n → ℝ) (k : Fin L)
    (ih : (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix
          (finAppendParams h0₁ h0₂ θ₁ θ₂)
          (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.castSucc.succ =
        Sum.elim ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.castSucc.succ)
          ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.castSucc.succ) ∘
          ((finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ k.castSucc)).trans
            finSumFinEquiv.symm)) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.succ.succ =
      Sum.elim ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ.succ) ∘
        ((finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ k.succ)).trans finSumFinEquiv.symm) := by
  have hd_succ := reluSpec_finAppendWidths_succ n d₁ d₂
  have hih_cast : (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix
        (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.succ.castSucc =
      Sum.elim ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.castSucc.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.castSucc.succ) ∘
        ((finCongr (hd_succ k.castSucc)).trans finSumFinEquiv.symm) := by
    rw [MLPSpec.evalPrefix_cast_eq_comp _ _ _ (Fin.ext rfl : k.succ.castSucc = k.castSucc.succ),
      ih]; rfl
  have hW : ((finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 *ᵥ
        (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix
          (finAppendParams h0₁ h0₂ θ₁ θ₂)
          (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.succ.castSucc +
        (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).2) =
      Sum.elim ((θ₁ k.succ).1 *ᵥ (reluSpec d₁).evalPrefix θ₁
          (fun i => x (Fin.cast h0₁ i)) k.succ.castSucc + (θ₁ k.succ).2)
        ((θ₂ k.succ).1 *ᵥ (reluSpec d₂).evalPrefix θ₂
          (fun i => x (Fin.cast h0₂ i)) k.succ.castSucc + (θ₂ k.succ).2) ∘
        ((finCongr (hd_succ k.succ)).trans finSumFinEquiv.symm) := by
    rw [finAppendParams_succ, hih_cast]; dsimp only [finAppendParamSucc]
    rw [Matrix.submatrix_mulVec_equiv _ _ ((finCongr (hd_succ k.succ)).trans finSumFinEquiv.symm)
        ((finCongr (hd_succ k.castSucc)).trans finSumFinEquiv.symm),
      Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
    exact (congrArg (· ∘ ((finCongr (hd_succ k.succ)).trans finSumFinEquiv.symm))
      (Sum.elim_add_add
        ((θ₁ k.succ).1 *ᵥ (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ.castSucc)
        (θ₁ k.succ).2
        ((θ₂ k.succ).1 *ᵥ (reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ.castSucc)
        (θ₂ k.succ).2)).symm
  have hs₁ : (reluSpec (finAppendWidths n d₁ d₂)).layerActivation k.succ ∘
      ((θ₁ k.succ).1 *ᵥ (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ.castSucc +
        (θ₁ k.succ).2) =
      (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ.succ := by
    rw [layerActivation_reluSpec_eq (finAppendWidths n d₁ d₂) d₁ Iff.rfl, MLPSpec.evalPrefix_succ]
    rfl
  have hs₂ : (reluSpec (finAppendWidths n d₁ d₂)).layerActivation k.succ ∘
      ((θ₂ k.succ).1 *ᵥ (reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ.castSucc +
        (θ₂ k.succ).2) =
      (reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ.succ := by
    rw [layerActivation_reluSpec_eq (finAppendWidths n d₁ d₂) d₂ Iff.rfl, MLPSpec.evalPrefix_succ]
    rfl
  rw [MLPSpec.evalPrefix_succ]
  simp_rw [← Pi.add_apply]
  rw [hW]
  change ((reluSpec (finAppendWidths n d₁ d₂)).layerActivation k.succ ∘ Sum.elim _ _) ∘ _ = _
  rw [Sum.comp_elim, hs₁, hs₂]

private theorem finAppendParams_evalPrefix_sumElim {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (x : Fin n → ℝ)
    (k : Fin (L + 1)) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.succ =
      Sum.elim
        ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ) ∘
        ((finCongr (reluSpec_finAppendWidths_succ n d₁ d₂ k)).trans finSumFinEquiv.symm) := by
  induction k using Fin.induction with
  | zero => exact finAppendParams_evalPrefix_zero h0₁ h0₂ θ₁ θ₂ x
  | succ k ih => exact finAppendParams_evalPrefix_succ h0₁ h0₂ θ₁ θ₂ x k ih

private theorem finAppendParams_evalPrefix {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (x : Fin n → ℝ)
    (k : Fin (L + 1)) (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ)) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (reluSpec_finAppendWidths_zero n d₁ d₂) i)) k.succ r =
      Fin.append
        ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ)
        (Fin.cast (reluSpec_finAppendWidths_succ n d₁ d₂ k) r) := by
  rw [congrFun (finAppendParams_evalPrefix_sumElim h0₁ h0₂ θ₁ θ₂ x k) r]
  dsimp only [Function.comp_apply, Equiv.trans_apply, finCongr_apply]
  exact (congrFun (Fin.append_comp_sumElim :
    Fin.append ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
      ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ) ∘
        Sum.elim (Fin.castAdd _) (Fin.natAdd _) = _)
    (finSumFinEquiv.symm (Fin.cast (reluSpec_finAppendWidths_succ n d₁ d₂ k) r))).symm.trans
    (by
      change Fin.append ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ)
        (finSumFinEquiv (finSumFinEquiv.symm
          (Fin.cast (reluSpec_finAppendWidths_succ n d₁ d₂ k) r))) = _
      rw [Equiv.apply_symm_apply])

/-- Stacking two ReLU networks of the same positive depth `L + 1` in parallel yields a network of
depth `L + 1` with widths `finAppendWidths n d₁ d₂` realizing
`fun x => Fin.append (f₁ x) (f₂ x)`. -/
theorem ReLUNetRealizes.finAppend {n m₁ m₂ L : ℕ}
    {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ : (Fin n → ℝ) → (Fin m₁ → ℝ)} {f₂ : (Fin n → ℝ) → (Fin m₂ → ℝ)}
    (hf₁ : ReLUNetRealizes d₁ f₁) (hf₂ : ReLUNetRealizes d₂ f₂) :
    ReLUNetRealizes (finAppendWidths n d₁ d₂)
      (fun x => Fin.append (f₁ x) (f₂ x)) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := reluNetRealizes_iff.mp hf₁
  obtain ⟨h0₂, hm₂, θ₂, hθ₂⟩ := reluNetRealizes_iff.mp hf₂
  have h0₁' : (reluSpec d₁).width 0 = n := h0₁
  have h0₂' : (reluSpec d₂).width 0 = n := h0₂
  have hm₁' : (reluSpec d₁).width (Fin.last L).succ = m₁ := hm₁
  have hm₂' : (reluSpec d₂).width (Fin.last L).succ = m₂ := hm₂
  have hd0' : finAppendWidths n d₁ d₂ 0 = n := finAppendWidths_zero n d₁ d₂
  have hd0 := reluSpec_finAppendWidths_zero n d₁ d₂
  have hdL : finAppendWidths n d₁ d₂ (Fin.last (L + 1)) = m₁ + m₂ :=
    (finAppendWidths_succ n d₁ d₂ (Fin.last L)).trans (congrArg₂ (· + ·) hm₁' hm₂')
  have hdL' : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last (L + 1)) = m₁ + m₂ := hdL
  refine reluNetRealizes_iff.mpr ⟨hd0', hdL, finAppendParams h0₁' h0₂' θ₁ θ₂, fun x j => ?_⟩
  have hm_eq : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last L).succ = m₁ + m₂ := hdL
  have hlast := finAppendParams_evalPrefix h0₁' h0₂' θ₁ θ₂ x (Fin.last L) (Fin.cast hm_eq.symm j)
  have hlast_eq : (Fin.last (L + 1) : Fin (L + 2)) = (Fin.last L).succ := Fin.ext rfl
  have hrealize_eq :
      (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0' i)) (Fin.last (L + 1)) (Fin.cast hdL.symm j) =
        (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0 i)) (Fin.last (L + 1)) (Fin.cast hdL'.symm j) := rfl
  rw [MLPSpec.realize_def]
  refine hrealize_eq.trans ?_
  have hcast_j : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hlast_eq)
      (Fin.cast hdL'.symm j) = Fin.cast hm_eq.symm j := Fin.ext (by simp only [Fin.val_cast])
  rw [MLPSpec.evalPrefix_cast _ _ _ hlast_eq, hcast_j, hlast]
  let y₁ := (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁' i)) (Fin.last L).succ
  let y₂ := (reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂' i)) (Fin.last L).succ
  have hf₁' : y₁ ∘ Fin.cast hm₁'.symm = f₁ x := funext fun j₁ => by
    dsimp only [Function.comp_apply, y₁]
    rw [MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₁ x j₁
  have hf₂' : y₂ ∘ Fin.cast hm₂'.symm = f₂ x := funext fun j₂ => by
    dsimp only [Function.comp_apply, y₂]
    rw [MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₂ x j₂
  rw [← hf₁', ← hf₂', Fin.append_cast_left _ _ m₁ hm₁'.symm,
    Fin.append_cast_right _ _ m₂ hm₂'.symm]
  exact congrArg (Fin.append y₁ y₂) (Fin.ext rfl)

/-- Parallel affine combination of two ReLU networks of the same positive depth `L + 1`: if `d₁`
computes `f₁` and `d₂` computes `f₂`, then `compWidths (finAppendWidths n d₁ d₂) ![2, 1]`
computes `fun x => a * f₁ x + b * f₂ x + c`. -/
theorem ReLUNetComputes.affineComb {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ f₂ : (Fin n → ℝ) → ℝ} (hf₁ : ReLUNetComputes d₁ f₁)
    (hf₂ : ReLUNetComputes d₂ f₂) (a b c : ℝ) :
    ReLUNetComputes (compWidths (finAppendWidths n d₁ d₂) ![2, 1])
      (fun x => a * f₁ x + b * f₂ x + c) := by
  let g₁ := reluNetComputes_iff_reluNetRealizes.mp hf₁
  let g₂ := reluNetComputes_iff_reluNetRealizes.mp hf₂
  let A : (Fin 2 → ℝ) →ᴬ[ℝ] ℝ :=
    a • (ContinuousLinearMap.proj (R := ℝ) 0).toContinuousAffineMap +
      b • (ContinuousLinearMap.proj (R := ℝ) 1).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ _ c
  have hcomp :=
    ReLUNetComputes.comp (g₁.finAppend g₂) (ReLUNetComputes.of_continuousAffineMap A)
  have heq : (A ∘ fun x => Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x)) =
      fun x => a * f₁ x + b * f₂ x + c := by
    funext x
    have h0 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 0 = f₁ x :=
      Fin.append_left _ _ 0
    have h1 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 1 = f₂ x :=
      Fin.append_right _ _ 0
    simp [A, h0, h1, smul_eq_mul]
  rwa [heq] at hcomp

end TauCeti
