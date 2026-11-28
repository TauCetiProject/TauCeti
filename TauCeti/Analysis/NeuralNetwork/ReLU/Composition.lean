/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Basic

/-!
# Composition and depth padding for ReLU networks

Merging the affine output layer of a depth-`(L₁ + 1)` ReLU network with the affine input layer of
a depth-`(L₂ + 1)` ReLU network yields a depth-`(L₁ + L₂ + 1)` ReLU network realizing the
composite (`ReLUNetRealizes.comp`, `ReLUNetComputes.comp`) with widths `compWidths`.

Composing with the depth-2 identity network `ReLUNetRealizes.id_depth_two` appends a `2 * m`-unit
hidden layer (two units in the scalar case) without changing the realized function
(`ReLUNetRealizes.pad`, `ReLUNetComputes.pad`), showing that every continuous affine functional
and every ReLU-computable scalar function is computed at every larger depth
(`exists_reluNetComputes_of_continuousAffineMap`, `exists_reluNetComputes_of_le`).

## References

* Raman Arora, Amitabh Basu, Poorya Mianjy, and Anirbit Mukherjee, *Understanding deep neural
  networks with rectified linear units*, ICLR 2018;
  [arXiv:1611.01491v6](https://arxiv.org/abs/1611.01491v6), Theorem 2.1 and Appendix D.
* Christoph Hertrich, Amitabh Basu, Marco Di Summa, and Martin Skutella, *Towards lower bounds on
  the depth of ReLU neural networks*, Discrete & Computational Geometry (2024);
  [arXiv:2105.14835v5](https://arxiv.org/abs/2105.14835v5), §2 and Figure 1.
-/

public section

open Matrix

namespace TauCeti

open Neuromanifold

/-! ### Composition -/

/-- The width tuple obtained by merging the output affine layer of a depth-`(L₁ + 1)` network
with the input affine layer of a depth-`(L₂ + 1)` network, producing depth `L₁ + L₂ + 1`. -/
@[expose] def compWidths {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ) (d₂ : Fin (L₂ + 2) → ℕ) :
    Fin (L₁ + L₂ + 2) → ℕ :=
  fun i =>
    if _ : i.val ≤ L₁ then d₁ ⟨i.val, by omega⟩ else d₂ ⟨i.val - L₁, by omega⟩

/-- On indices `i : Fin (L₁ + 1)` below the merge layer, `compWidths` agrees with `d₁`. -/
@[simp]
theorem compWidths_left {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₁ + 1)) :
    compWidths d₁ d₂ ⟨i.val, by omega⟩ = d₁ i.castSucc := by
  have hi : i.val ≤ L₁ := Nat.le_of_lt_succ i.isLt
  simp only [compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext rfl)

/-- On shifted indices `L₁ + 1 + i` above the merge layer, `compWidths` agrees with `d₂ i.succ`. -/
@[simp]
theorem compWidths_right {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₂ + 1)) :
    compWidths d₁ d₂ ⟨L₁ + 1 + i.val, by omega⟩ = d₂ i.succ := by
  have hi : ¬ (L₁ + 1 + i.val ≤ L₁) := by omega
  simp only [compWidths, hi, ↓reduceDIte]
  exact congrArg d₂ (Fin.ext (by simp; omega))

/-- The input width of `compWidths d₁ d₂` is `d₁ 0`. -/
@[simp]
theorem compWidths_zero {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) :
    compWidths d₁ d₂ 0 = d₁ 0 :=
  compWidths_left d₁ d₂ 0

/-- The output width of `compWidths d₁ d₂` is `d₂ (Fin.last (L₂ + 1))`. -/
@[simp]
theorem compWidths_last {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) :
    compWidths d₁ d₂ (Fin.last (L₁ + L₂ + 1)) = d₂ (Fin.last (L₂ + 1)) := by
  have hlast : Fin.last (L₁ + L₂ + 1) = ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [hlast]
  exact compWidths_right d₁ d₂ (Fin.last L₂)

private theorem width_compWidths_of_le {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₁ + 2)}
    (hi : i.val ≤ L₁) (hij : i.val = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₁).width j := by
  simp only [reluSpec_width, compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext hij)

private theorem width_compWidths_of_lt {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₂ + 2)}
    (hi : L₁ < i.val) (hij : i.val - L₁ = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₂).width j := by
  have hnot : ¬ i.val ≤ L₁ := Nat.not_le_of_lt hi
  simp only [reluSpec_width, compWidths, hnot, ↓reduceDIte]
  exact congrArg d₂ (Fin.ext hij)

private def compParams {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (reluSpec (compWidths d₁ d₂)).Parameters := fun i =>
  if hi : i.val < L₁ then
    let k : Fin L₁ := ⟨i.val, hi⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.castSucc.succ :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [k])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [k])
    (fun r c => (θ₁ k.castSucc).1 (Fin.cast hr r) (Fin.cast hc c),
     fun r => (θ₁ k.castSucc).2 (Fin.cast hr r))
  else if heq : i.val = L₁ then
    let W₁ := (θ₁ (Fin.last L₁)).1
    let b₁ := (θ₁ (Fin.last L₁)).2
    let W₂ := (θ₂ 0).1
    let b₂ := (θ₂ 0).2
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ :=
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [heq])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width (Fin.last L₁).castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [heq])
    let W₂' := W₂.submatrix (finCongr hr) (finCongr hm₂).symm
    let W₁' := W₁.submatrix (finCongr hm₁).symm (finCongr hc)
    (W₂' * W₁', W₂' *ᵥ (b₁ ∘ (finCongr hm₁).symm) + b₂ ∘ finCongr hr)
  else
    let k : Fin L₂ := ⟨i.val - (L₁ + 1), by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k.succ.succ :=
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    (fun r c => (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c),
     fun r => (θ₂ k.succ).2 (Fin.cast hr r))

private theorem compParams_lt {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L₁) :
    let i : Fin (L₁ + L₂ + 1) := ⟨k.val, by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.castSucc.succ :=
      width_compWidths_of_le d₁ d₂ (by dsimp [i]; omega) (by dsimp [i])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by dsimp [i]; omega) (by dsimp [i])
    (∀ r c, (compParams hm₁ hm₂ θ₁ θ₂ i).1 r c =
        (θ₁ k.castSucc).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
      (∀ r, (compParams hm₁ hm₂ θ₁ θ₂ i).2 r =
        (θ₁ k.castSucc).2 (Fin.cast hr r)) := by
  intro i hr hc
  have hi : i.val < L₁ := k.isLt
  simp [compParams, hi, i]

private theorem compParams_eq {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (hr : (reluSpec (compWidths d₁ d₂)).width
        (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).succ =
        (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ)
    (hc : (reluSpec (compWidths d₁ d₂)).width
        (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).castSucc =
        (reluSpec d₁).width (Fin.last L₁).castSucc) :
    compParams hm₁ hm₂ θ₁ θ₂ ⟨L₁, by omega⟩ =
      let W₂' := (θ₂ 0).1.submatrix (finCongr hr) (finCongr hm₂).symm
      let W₁' := (θ₁ (Fin.last L₁)).1.submatrix (finCongr hm₁).symm (finCongr hc)
      (W₂' * W₁', W₂' *ᵥ ((θ₁ (Fin.last L₁)).2 ∘ (finCongr hm₁).symm) +
        (θ₂ 0).2 ∘ finCongr hr) := by
  simp [compParams]

private theorem compParams_gt {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L₂) :
    let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k.succ.succ :=
      width_compWidths_of_lt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
    (∀ r c, (compParams hm₁ hm₂ θ₁ θ₂ i).1 r c =
        (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
      (∀ r, (compParams hm₁ hm₂ θ₁ θ₂ i).2 r = (θ₂ k.succ).2 (Fin.cast hr r)) := by
  intro i hr hc
  have hi : ¬ (i.val < L₁) := by dsimp [i]; omega
  have heq : i.val ≠ L₁ := by dsimp [i]; omega
  have hfn : ∀ (k' : Fin L₂) (_ : k' = k)
      (hr' : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k'.succ.succ)
      (hc' : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k'.succ.castSucc),
      (∀ r c, (θ₂ k'.succ).1 (Fin.cast hr' r) (Fin.cast hc' c) =
          (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
        (∀ r, (θ₂ k'.succ).2 (Fin.cast hr' r) = (θ₂ k.succ).2 (Fin.cast hr r)) := by
    rintro _ rfl _ _
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  simp only [compParams, hi, ↓reduceDIte, heq]
  exact hfn ⟨i.val - (L₁ + 1), by dsimp [i]; omega⟩ (Fin.ext (by dsimp [i]; omega)) _ _

private theorem compParams_evalPrefix_lt {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (x : Fin n → ℝ) (k : Fin (L₁ + 1))
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨k.val, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨k.val, by omega⟩ r =
      (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.castSucc
        (Fin.cast (width_compWidths_of_le d₁ d₂ (Nat.le_of_lt_succ k.isLt) rfl) r) := by
  induction k using Fin.induction with
  | zero =>
    have hzero₁ : (⟨(0 : Fin (L₁ + 1)).val, by omega⟩ : Fin (L₁ + L₂ + 2)) = 0 := Fin.ext rfl
    rw [MLPSpec.evalPrefix_cast _ _ _ hzero₁, MLPSpec.evalPrefix_zero,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ (Fin.castSucc_zero :
        (0 : Fin (L₁ + 1)).castSucc = 0), MLPSpec.evalPrefix_zero]
    exact congrArg x (Fin.ext rfl)
  | succ k ih =>
    let i : Fin (L₁ + L₂ + 1) := ⟨k.val, by omega⟩
    have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
        (reluSpec d₁).layerActivation k.castSucc :=
      layerActivation_reluSpec_eq _ _ (by simp [i]; omega)
    have hsucc : (⟨k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ := Fin.ext rfl
    have hk_cast : k.succ.castSucc = k.castSucc.succ := Fin.ext rfl
    rw [MLPSpec.evalPrefix_cast _ _ _ hsucc, MLPSpec.evalPrefix_succ_apply, hlayer,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ hk_cast, MLPSpec.evalPrefix_succ_apply]
    apply congrArg ((reluSpec d₁).layerActivation k.castSucc)
    obtain ⟨hW, hb⟩ := compParams_lt hm₁ hm₂ θ₁ θ₂ k
    dsimp only [i]
    simp only [Matrix.mulVec, dotProduct, hW, hb]
    congr 1
    let hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp [i]) rfl
    refine Fintype.sum_equiv (finCongr hc) _ _ fun c => ?_
    simp only [finCongr_apply]
    congr 1
    exact ih c

private theorem compParams_evalPrefix_mid {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (g : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (hθ₁ : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁ i)) (Fin.cast hm₁.symm k) = g x k)
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨L₁ + 1, by omega⟩ r =
      (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u)) 1
        (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp) (by simp)) r) := by
  let i_mid : Fin (L₁ + L₂ + 1) := ⟨L₁, by omega⟩
  have hsucc_mid : (⟨L₁ + 1, by omega⟩ : Fin (L₁ + L₂ + 2)) = i_mid.succ := Fin.ext rfl
  have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i_mid =
      (reluSpec d₂).layerActivation 0 :=
    layerActivation_reluSpec_eq _ _ (by simp [i_mid]; omega)
  have h0₂ : (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u))
      (0 : Fin (L₂ + 1)).castSucc = fun u => g x (Fin.cast hm₂ u) := by simp
  rw [MLPSpec.evalPrefix_cast _ _ _ hsucc_mid, MLPSpec.evalPrefix_succ_apply, hlayer,
    MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ (Fin.ext rfl : (1 : Fin (L₂ + 2)) = (0 : Fin _).succ),
    MLPSpec.evalPrefix_succ_apply, h0₂]
  apply congrArg ((reluSpec d₂).layerActivation 0)
  have hr_mid : (reluSpec (compWidths d₁ d₂)).width i_mid.succ =
      (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ :=
    width_compWidths_of_lt d₁ d₂ (by simp [i_mid]) (by simp [i_mid])
  have hc_mid : (reluSpec (compWidths d₁ d₂)).width i_mid.castSucc =
      (reluSpec d₁).width (Fin.last L₁).castSucc :=
    width_compWidths_of_le d₁ d₂ (by simp [i_mid]) (by simp [i_mid])
  let v₁ := (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) (Fin.last L₁).castSucc
  have hv : (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
      (fun i => x (Fin.cast h0c i)) i_mid.castSucc = v₁ ∘ finCongr hc_mid :=
    funext fun c => compParams_evalPrefix_lt h0c h0₁ hm₁ hm₂ θ₁ θ₂ x (Fin.last L₁) c
  have hθ₁_vec : ((θ₁ (Fin.last L₁)).1 *ᵥ v₁) ∘ ⇑(finCongr hm₁).symm +
      (θ₁ (Fin.last L₁)).2 ∘ ⇑(finCongr hm₁).symm = g x :=
    funext fun k => by simpa [MLPSpec.realize_succ] using hθ₁ k
  have hm₁' : (reluSpec d₁).width (Fin.last L₁).succ = m := hm₁
  have hm₂' : (reluSpec d₂).width (0 : Fin (L₂ + 1)).castSucc = m := hm₂
  have hvec :
      let W₂' := (θ₂ 0).1.submatrix (finCongr hr_mid) (finCongr hm₂').symm
      let W₁' := (θ₁ (Fin.last L₁)).1.submatrix (finCongr hm₁').symm (finCongr hc_mid)
      (W₂' * W₁') *ᵥ (v₁ ∘ finCongr hc_mid) +
          (W₂' *ᵥ ((θ₁ (Fin.last L₁)).2 ∘ (finCongr hm₁').symm) + (θ₂ 0).2 ∘ finCongr hr_mid) =
        ((θ₂ 0).1 *ᵥ (fun u => g x (Fin.cast hm₂' u)) + (θ₂ 0).2) ∘ finCongr hr_mid := by
    intro W₂' W₁'
    have hW₁v :
        W₁' *ᵥ (v₁ ∘ finCongr hc_mid) = ((θ₁ (Fin.last L₁)).1 *ᵥ v₁) ∘ (finCongr hm₁').symm := by
      dsimp only [W₁']
      rw [Matrix.submatrix_mulVec_equiv (θ₁ (Fin.last L₁)).1 _ (finCongr hm₁').symm
          (finCongr hc_mid), Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
    have hW₂v : W₂' *ᵥ g x = ((θ₂ 0).1 *ᵥ (fun u => g x (Fin.cast hm₂' u))) ∘ finCongr hr_mid := by
      dsimp only [W₂']
      rw [Matrix.submatrix_mulVec_equiv (θ₂ 0).1 _ (finCongr hr_mid) (finCongr hm₂').symm]; rfl
    rw [← Matrix.mulVec_mulVec, hW₁v, ← add_assoc, ← Matrix.mulVec_add, hθ₁_vec, hW₂v]; rfl
  dsimp only [i_mid] at hv hr_mid hc_mid hvec ⊢
  rw [compParams_eq hm₁ hm₂ θ₁ θ₂ hr_mid hc_mid, hv]
  exact (congrFun hvec (Fin.cast (congrArg (reluSpec (compWidths d₁ d₂)).width hsucc_mid) r)).trans
    (congrArg (fun j => ((θ₂ 0).1 *ᵥ (fun u => g x (Fin.cast hm₂ u)) + (θ₂ 0).2) j)
      (Fin.ext (by simp only [Fin.val_cast, finCongr_apply])))

private theorem compParams_evalPrefix_gt {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (g : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (hθ₁ : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁ i)) (Fin.cast hm₁.symm k) = g x k)
    (k : Fin (L₂ + 1))
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + k.val, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨L₁ + 1 + k.val, by omega⟩ r =
      (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u)) k.succ
        (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega)) r) := by
  induction k using Fin.induction with
  | zero =>
    exact compParams_evalPrefix_mid h0c h0₁ hm₁ hm₂ θ₁ θ₂ g x hθ₁ r
  | succ k ih =>
    let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
    have hsucc : (⟨L₁ + 1 + k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ :=
      Fin.ext (by simp [i]; omega)
    have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
        (reluSpec d₂).layerActivation k.succ :=
      layerActivation_reluSpec_eq _ _ (by simp [i]; omega)
    rw [MLPSpec.evalPrefix_cast _ _ _ hsucc, MLPSpec.evalPrefix_succ_apply, hlayer,
      MLPSpec.evalPrefix_succ_apply]
    apply congrArg ((reluSpec d₂).layerActivation k.succ)
    obtain ⟨hW, hb⟩ := compParams_gt hm₁ hm₂ θ₁ θ₂ k
    dsimp only [i]
    simp only [Matrix.mulVec, dotProduct, hW, hb]
    congr 1
    have hcast_c : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by simp [i]; omega) (by simp [i]; omega)
    refine Fintype.sum_equiv (finCongr hcast_c) _ _ fun c => ?_
    simp only [finCongr_apply]
    congr 1
    exact ih c

/-- Merging the affine output layer of a depth-`(L₁ + 1)` network realizing `g` with the affine
input layer of a depth-`(L₂ + 1)` network realizing `h` gives a depth-`(L₁ + L₂ + 1)` network
realizing `h ∘ g`. -/
theorem ReLUNetRealizes.comp {n m p L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetRealizes d₂ h) :
    ReLUNetRealizes (compWidths d₁ d₂) (h ∘ g) := by
  -- Track `evalPrefix` in three stages: `compParams_evalPrefix_lt` below `L₁`,
  -- `compParams_evalPrefix_mid` at the merged affine layer `L₁ + 1`, and
  -- `compParams_evalPrefix_gt` from `L₁ + 1` to the output.
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hg
  obtain ⟨hm₂, hp₂, θ₂, hθ₂⟩ := hh
  have h0₁' : (reluSpec d₁).width 0 = n := (congrFun (reluSpec_width d₁) 0).trans h0₁
  have hm₁' : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m :=
    (congrFun (reluSpec_width d₁) (Fin.last (L₁ + 1))).trans hm₁
  have hm₂' : (reluSpec d₂).width 0 = m := (congrFun (reluSpec_width d₂) 0).trans hm₂
  have hp₂' : (reluSpec d₂).width (Fin.last (L₂ + 1)) = p :=
    (congrFun (reluSpec_width d₂) (Fin.last (L₂ + 1))).trans hp₂
  have h0c : compWidths d₁ d₂ 0 = n := by simp [h0₁]
  have h0c' : (reluSpec (compWidths d₁ d₂)).width 0 = n :=
    (congrFun (reluSpec_width _) 0).trans h0c
  have hpc : compWidths d₁ d₂ (Fin.last (L₁ + L₂ + 1)) = p := by simp [hp₂]
  have hpc' : (reluSpec (compWidths d₁ d₂)).width (Fin.last (L₁ + L₂ + 1)) = p :=
    (congrFun (reluSpec_width _) _).trans hpc
  refine ⟨h0c, hpc, compParams hm₁' hm₂' θ₁ θ₂, fun x j => ?_⟩
  have hθ₁' : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁' i)) (Fin.cast hm₁'.symm k) = g x k :=
    fun k => hθ₁ x k
  have hlast_idx : (Fin.last (L₁ + L₂ + 1) : Fin (L₁ + L₂ + 2)) =
      ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ := Fin.ext (by simp; omega)
  have hp_eq :
      (reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ = p :=
    (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega)).trans hp₂'
  have hlast := compParams_evalPrefix_gt h0c' h0₁' hm₁' hm₂' θ₁ θ₂ g x hθ₁' (Fin.last L₂)
    (Fin.cast hp_eq.symm j)
  have hrealize_eq :
      (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁' hm₂' θ₁ θ₂)
          (fun i => x (Fin.cast h0c i)) (Fin.last (L₁ + L₂ + 1)) (Fin.cast hpc.symm j) =
        (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁' hm₂' θ₁ θ₂)
          (fun i => x (Fin.cast h0c' i)) (Fin.last (L₁ + L₂ + 1)) (Fin.cast hpc'.symm j) := rfl
  rw [MLPSpec.realize_def]
  refine hrealize_eq.trans ?_
  rw [MLPSpec.evalPrefix_cast _ _ _ hlast_idx]
  have h_eq : Fin.cast (congrArg (reluSpec (compWidths d₁ d₂)).width hlast_idx)
      (Fin.cast hpc'.symm j) = Fin.cast hp_eq.symm j := Fin.ext (by simp only [Fin.val_cast])
  rw [h_eq, hlast, MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ (Fin.succ_last L₂),
    ← MLPSpec.realize_def]
  have hcast_p : Fin.cast (congrArg (reluSpec d₂).width (Fin.succ_last L₂))
      (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega))
        (Fin.cast hp_eq.symm j)) = Fin.cast hp₂'.symm j := Fin.ext (by simp only [Fin.val_cast])
  rw [hcast_p]
  exact hθ₂ (g x) j

/-- Merging a depth-`(L₁ + 1)` network realizing `g : ℝⁿ → ℝᵐ` with a depth-`(L₂ + 1)`
network computing `h : ℝᵐ → ℝ` yields a depth-`(L₁ + L₂ + 1)` network computing
`h ∘ g`. -/
theorem ReLUNetComputes.comp {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → ℝ}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetComputes d₂ h) :
    ReLUNetComputes (compWidths d₁ d₂) (h ∘ g) :=
  reluNetComputes_iff_reluNetRealizes.mpr
    (hg.comp (reluNetComputes_iff_reluNetRealizes.mp hh))

/-! ### Depth padding -/

/-- Appending a hidden layer of width `2 * m` preserves realization, increasing depth by one. -/
theorem ReLUNetRealizes.pad {n m L : ℕ} {d : Fin (L + 2) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) :
    ReLUNetRealizes
      (fun i : Fin (L + 3) =>
        if _ : i.val ≤ L then d ⟨i.val, by omega⟩
        else if i = Fin.last (L + 2) then m else 2 * m)
      f := by
  have hcomp := hf.comp (ReLUNetRealizes.id_depth_two m)
  refine hcomp.of_width_eq ?_
  ext i
  by_cases hi : i.val ≤ L
  · simp [compWidths, hi]
  · by_cases hiL : i = Fin.last (L + 2)
    · subst hiL
      have h1 : ¬ (L + 2 ≤ L) := by omega
      simp [compWidths, h1]
    · have hi1 : i.val = L + 1 := by
        have := i.isLt
        have : i.val ≠ L + 2 := fun h => hiL (Fin.ext h)
        omega
      simp [compWidths, hiL, hi1]

/-- Appending a two-unit hidden layer preserves scalar computation, increasing depth by one. -/
theorem ReLUNetComputes.pad {n L : ℕ} {d : Fin (L + 2) → ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ReLUNetComputes d f) :
    ReLUNetComputes
      (fun i : Fin (L + 3) =>
        if _ : i.val ≤ L then d ⟨i.val, by omega⟩
        else if i = Fin.last (L + 2) then 1 else 2)
      f :=
  reluNetComputes_iff_reluNetRealizes.mpr
    (reluNetComputes_iff_reluNetRealizes.mp hf).pad

private theorem ReLUNetComputes.pad_pos {n L : ℕ} (hL : 1 ≤ L) {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) :
    ∃ d' : Fin (L + 2) → ℕ, ReLUNetComputes d' f := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hL)
  subst hm
  exact ⟨_, hf.pad⟩

private theorem exists_reluNetComputes_of_le_pos {n L₁ L₂ : ℕ} (hL₁ : 1 ≤ L₁) (hL : L₁ ≤ L₂)
    {d₁ : Fin (L₁ + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d₁ f) :
    ∃ d₂ : Fin (L₂ + 1) → ℕ, ReLUNetComputes d₂ f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  induction k with
  | zero => exact ⟨d₁, hf⟩
  | succ k ih =>
    obtain ⟨d, hd⟩ := ih (by omega)
    rw [← Nat.add_assoc]
    exact hd.pad_pos (by omega)

/-- Every continuous affine functional `(Fin n → ℝ) →ᴬ[ℝ] ℝ` is computed by a ReLU
network of every positive depth `L ≥ 1`. -/
theorem exists_reluNetComputes_of_continuousAffineMap {n L : ℕ} (hL : 1 ≤ L)
    (A : (Fin n → ℝ) →ᴬ[ℝ] ℝ) :
    ∃ d : Fin (L + 1) → ℕ, ReLUNetComputes d A :=
  exists_reluNetComputes_of_le_pos (le_refl 1) hL (ReLUNetComputes.of_continuousAffineMap A)

/-- A scalar function computed at depth `L₁` is computed at every depth `L₂ ≥ L₁`. -/
theorem exists_reluNetComputes_of_le {n L₁ L₂ : ℕ} (hL : L₁ ≤ L₂)
    {d₁ : Fin (L₁ + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d₁ f) :
    ∃ d₂ : Fin (L₂ + 1) → ℕ, ReLUNetComputes d₂ f := by
  rcases Nat.eq_zero_or_pos L₁ with rfl | hL₁
  · rcases Nat.eq_zero_or_pos L₂ with rfl | hL₂
    · exact ⟨d₁, hf⟩
    · obtain ⟨h0, h1, θ, hθ⟩ := hf
      have hn : n = 1 := h0.symm.trans h1
      subst hn
      have haff : f =
          ⇑((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 1)).toContinuousAffineMap) := by
        ext x
        have hx := (hθ x).symm
        rw [MLPSpec.realize_depth_zero] at hx
        simpa [Fin.eq_zero] using hx
      rw [haff]
      exact exists_reluNetComputes_of_continuousAffineMap hL₂ _
  · exact exists_reluNetComputes_of_le_pos hL₁ hL hf

end TauCeti
