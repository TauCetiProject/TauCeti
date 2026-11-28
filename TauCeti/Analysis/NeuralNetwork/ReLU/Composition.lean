/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Basic
import TauCeti.Geometry.Neuromanifold.MLP.Composition
import TauCeti.Geometry.Neuromanifold.MLP.Congr

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
def compWidths {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ) (d₂ : Fin (L₂ + 2) → ℕ) :
    Fin (L₁ + L₂ + 2) → ℕ :=
  fun i =>
    if _ : i.val ≤ L₁ then d₁ ⟨i.val, by omega⟩ else d₂ ⟨i.val - L₁, by omega⟩

/-- On indices `i` with `i.val ≤ L₁`, `compWidths d₁ d₂ i` agrees with `d₁`. -/
theorem compWidths_of_le {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} (hi : i.val ≤ L₁) :
    compWidths d₁ d₂ i = d₁ ⟨i.val, by omega⟩ := by
  simp only [compWidths, hi, ↓reduceDIte]

/-- On indices `i` with `L₁ < i.val`, `compWidths d₁ d₂ i` agrees with `d₂` shifted by `L₁`. -/
theorem compWidths_of_lt {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} (hi : L₁ < i.val) :
    compWidths d₁ d₂ i = d₂ ⟨i.val - L₁, by omega⟩ := by
  have hnot : ¬ i.val ≤ L₁ := Nat.not_le_of_lt hi
  simp only [compWidths, hnot, ↓reduceDIte]

/-- On indices `i : Fin (L₁ + 1)` below the merge layer, `compWidths` agrees with `d₁`. -/
@[simp]
theorem compWidths_left {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₁ + 1)) :
    compWidths d₁ d₂ ⟨i.val, by omega⟩ = d₁ i.castSucc :=
  compWidths_of_le d₁ d₂ (Nat.le_of_lt_succ i.isLt)

/-- On shifted indices `L₁ + 1 + i` above the merge layer, `compWidths` agrees with `d₂ i.succ`. -/
@[simp]
theorem compWidths_right {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₂ + 1)) :
    compWidths d₁ d₂ ⟨L₁ + 1 + i.val, by omega⟩ = d₂ i.succ :=
  (compWidths_of_lt d₁ d₂ (by simp; omega)).trans (congrArg d₂ (Fin.ext (by simp; omega)))

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

private theorem reluNetRealizes_congr_depth {n m L L' : ℕ} (hL : L = L')
    {d : Fin (L + 1) → ℕ} {d' : Fin (L' + 1) → ℕ}
    (hd : ∀ i : Fin (L + 1), d i = d' (Fin.cast (congrArg (· + 1) hL) i))
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) :
    ReLUNetRealizes d' f := by
  subst hL
  exact hf.of_width_eq (funext hd)

private def reluConsParams {L : ℕ} (d : Fin (L + 2) → ℕ) {d' : Fin (L + 1) → ℕ}
    (ht : Fin.tail d = d')
    (θ₀ : Matrix (Fin ((reluSpec d).width 1)) (Fin ((reluSpec d).width 0)) ℝ ×
      (Fin ((reluSpec d).width 1) → ℝ))
    (θ' : (reluSpec d').Parameters) : (reluSpec d).Parameters :=
  Fin.cons θ₀
    (cast (congrArg MLPSpec.Parameters ((tail_reluSpec d).trans (congrArg reluSpec ht)).symm) θ')

private theorem reluSpec_cons_realize {L : ℕ} (d : Fin (L + 2) → ℕ) {d' : Fin (L + 1) → ℕ}
    (ht : Fin.tail d = d')
    (θ₀ : Matrix (Fin ((reluSpec d).width 1)) (Fin ((reluSpec d).width 0)) ℝ ×
      (Fin ((reluSpec d).width 1) → ℝ))
    (θ' : (reluSpec d').Parameters)
    (x : Fin ((reluSpec d).width 0) → ℝ)
    (j : Fin ((reluSpec d).width (Fin.last (L + 1)))) :
    (reluSpec d).realize (reluConsParams d ht θ₀ θ') x j =
      (reluSpec d').realize θ'
        (fun i => Neuromanifold.activation ((reluSpec d).layerActivation 0) ()
          (Neuromanifold.dense θ₀ x) (Fin.cast (congrArg (· 0) ht.symm) i))
        (Fin.cast (congrArg (fun f => f (Fin.last L)) ht) j) := by
  have htail : reluSpec d' = (reluSpec d).tail :=
    ((tail_reluSpec d).trans (congrArg reluSpec ht)).symm
  have hreal := congrFun (congrFun (MLPSpec.realize_cons (reluSpec d) θ₀
    (cast (congrArg MLPSpec.Parameters htail) θ')) x) j
  have hcast := MLPSpec.realize_cast htail θ'
    (Neuromanifold.activation ((reluSpec d).layerActivation 0) () (Neuromanifold.dense θ₀ x)) j
  exact (hreal.trans hcast).trans (congrArg₂ ((reluSpec d').realize θ')
    (funext fun _ => congrArg _ (Fin.ext rfl)) (Fin.ext rfl))

private theorem reluNetRealizes_comp_one {n m p L₂ : ℕ}
    {d₁ : Fin 2 → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetRealizes d₂ h) :
    ReLUNetRealizes (fun i : Fin (L₂ + 2) => if i = 0 then d₁ 0 else d₂ i) (h ∘ g) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := reluNetRealizes_iff.mp hg
  obtain ⟨hm₂, hp₂, θ₂, hθ₂⟩ := reluNetRealizes_iff.mp hh
  let d : Fin (L₂ + 2) → ℕ := fun i => if i = 0 then d₁ 0 else d₂ i
  have hd0 : d 0 = n := by simpa [d] using h0₁
  have hd0_w : (reluSpec d).width 0 = n := hd0
  have hdL : d (Fin.last (L₂ + 1)) = p := by simpa [d, Fin.succ_ne_zero] using hp₂
  have ht : Fin.tail d = Fin.tail d₂ := funext fun i => by simp [Fin.tail, d, Fin.succ_ne_zero]
  have h0₁' : (reluSpec d₁).width (0 : Fin 1).castSucc = n := h0₁
  have hm₁' : (reluSpec d₁).width (0 : Fin 1).succ = m := hm₁
  have hm₂' : (reluSpec d₂).width (0 : Fin (L₂ + 1)).castSucc = m := hm₂
  have hd1' : (reluSpec d).width 1 = (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ := by simp [d]
  have hd0' : (reluSpec d).width 0 = (reluSpec d₁).width (0 : Fin 1).castSucc := rfl
  let W₂' := (θ₂ 0).1.submatrix (finCongr hd1') (finCongr hm₂').symm
  let W₁' := (θ₁ 0).1.submatrix (finCongr hm₁').symm (finCongr hd0')
  let θ₀ :=
    (W₂' * W₁', W₂' *ᵥ ((θ₁ 0).2 ∘ (finCongr hm₁').symm) + (θ₂ 0).2 ∘ finCongr hd1')
  let θ₂_tail := cast (congrArg MLPSpec.Parameters (tail_reluSpec d₂)) (Fin.tail θ₂)
  refine reluNetRealizes_iff.mpr ⟨hd0, hdL, reluConsParams d ht θ₀ θ₂_tail, fun x j => ?_⟩
  have hlayer1 : (θ₁ 0).1 *ᵥ (fun i => x (Fin.cast h0₁' i)) + (θ₁ 0).2 =
      fun k => g x (Fin.cast hm₁' k) := funext fun k => by
    have h1 := hθ₁ x (Fin.cast hm₁' k); rw [MLPSpec.realize_depth_one] at h1; exact h1
  have hdense : Neuromanifold.dense θ₀ (fun i => x (Fin.cast hd0_w i)) =
      Neuromanifold.dense (θ₂ 0) (fun u => g x (Fin.cast hm₂' u)) ∘ finCongr hd1' := by
    rw [Neuromanifold.dense_apply, Neuromanifold.dense_apply]; dsimp only [θ₀, W₂', W₁']
    rw [← Matrix.mulVec_mulVec,
      Matrix.submatrix_mulVec_equiv (θ₁ 0).1 _ (finCongr hm₁').symm _]
    have hx : (fun i => x (Fin.cast hd0_w i)) ∘ (finCongr hd0').symm = _ := rfl
    rw [hx, ← add_assoc, ← Matrix.mulVec_add]
    change W₂' *ᵥ (((θ₁ 0).1 *ᵥ (fun i => x (Fin.cast h0₁' i)) + (θ₁ 0).2) ∘
      (finCongr hm₁').symm) + (θ₂ 0).2 ∘ finCongr hd1' = _
    rw [hlayer1, Matrix.submatrix_mulVec_equiv]; rfl
  have hreal := reluSpec_cons_realize d ht θ₀ θ₂_tail (fun i => x (Fin.cast hd0_w i))
    (Fin.cast hdL.symm j)
  have hcast₂ := MLPSpec.realize_cast (tail_reluSpec d₂) (Fin.tail θ₂)
    (fun i => Neuromanifold.activation ((reluSpec d).layerActivation 0) ()
      (Neuromanifold.dense θ₀ fun i => x (Fin.cast hd0_w i))
      (Fin.cast (congrArg (· 0) ht.symm) i))
    (Fin.cast (congrArg (fun f => f (Fin.last L₂)) ht) (Fin.cast hdL.symm j))
  have hreal₂ := congrFun (congrFun (MLPSpec.realize_eq_tail_comp (reluSpec d₂) θ₂)
    (fun u => g x (Fin.cast hm₂' u))) (Fin.cast hp₂.symm j)
  dsimp only [Function.comp_def] at hreal₂; refine (hreal.trans hcast₂).trans (Eq.trans ?_
    (hreal₂.symm.trans (hθ₂ (g x) j)))
  refine congrArg₂ ((reluSpec d₂).tail.realize (Fin.tail θ₂)) (funext fun u => ?_) (Fin.ext rfl)
  simp only [Function.comp_apply, hdense, Neuromanifold.activation_apply,
    layerActivation_reluSpec_eq d d₂ (i₁ := 0) (i₂ := 0) Iff.rfl]
  exact congrArg ((reluSpec d₂).layerActivation 0)
    (congrArg (Neuromanifold.dense (θ₂ 0) fun u => g x (Fin.cast hm₂' u)) (Fin.ext rfl))

private theorem reluNetRealizes_comp_succ {n m p L₁ L₂ : ℕ}
    {d₁ : Fin ((L₁ + 1) + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (ih : ∀ {g' : (Fin (d₁ 1) → ℝ) → (Fin m → ℝ)},
      ReLUNetRealizes (Fin.tail d₁) g' → ReLUNetRealizes (compWidths (Fin.tail d₁) d₂) (h ∘ g'))
    (hg : ReLUNetRealizes d₁ g) :
    ReLUNetRealizes (Fin.cons (d₁ 0) (compWidths (Fin.tail d₁) d₂)) (h ∘ g) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := reluNetRealizes_iff.mp hg
  let θ₁_tail : (reluSpec (Fin.tail d₁)).Parameters :=
    cast (congrArg MLPSpec.Parameters (tail_reluSpec d₁)) (Fin.tail θ₁)
  let g_tail : (Fin (d₁ 1) → ℝ) → (Fin m → ℝ) :=
    fun v j => (reluSpec (Fin.tail d₁)).realize θ₁_tail v (Fin.cast hm₁.symm j)
  obtain ⟨hd1, hp, θ', hθ'⟩ := reluNetRealizes_iff.mp
    (ih (reluNetRealizes_iff.mpr ⟨rfl, hm₁, θ₁_tail, fun _ _ => rfl⟩))
  let d : Fin (L₁ + L₂ + 3) → ℕ := Fin.cons (d₁ 0) (compWidths (Fin.tail d₁) d₂)
  have hd0_w : (reluSpec d).width 0 = n := h0₁
  have hd1' : (reluSpec d).width 1 = (reluSpec d₁).width (0 : Fin (L₁ + 2)).succ := hd1
  have hd0' : (reluSpec d).width 0 = (reluSpec d₁).width (0 : Fin (L₁ + 2)).castSucc := rfl
  let θ₀ : Matrix (Fin ((reluSpec d).width 1)) (Fin ((reluSpec d).width 0)) ℝ ×
      (Fin ((reluSpec d).width 1) → ℝ) :=
    ((θ₁ 0).1.submatrix (finCongr hd1') (finCongr hd0'), (θ₁ 0).2 ∘ finCongr hd1')
  refine reluNetRealizes_iff.mpr ⟨h0₁, hp, reluConsParams d rfl θ₀ θ', fun x j => ?_⟩
  let u₁ := Neuromanifold.activation ((reluSpec d₁).layerActivation 0) ()
    (Neuromanifold.dense (θ₁ 0) (fun i => x (Fin.cast h0₁ i)))
  have hu : Neuromanifold.activation ((reluSpec d).layerActivation 0) ()
      (Neuromanifold.dense θ₀ (fun i => x (Fin.cast hd0_w i))) = u₁ ∘ finCongr hd1' := by
    funext k
    simp only [u₁, Neuromanifold.activation_apply, Neuromanifold.dense_apply,
      layerActivation_reluSpec_eq d d₁ (i₁ := 0) (i₂ := 0) (by simp), θ₀]
    rw [Matrix.submatrix_mulVec_equiv (θ₁ 0).1 _ (finCongr hd1') (finCongr hd0')]
    have hx : (fun i => x (Fin.cast hd0_w i)) ∘ (finCongr hd0').symm =
        fun i => x (Fin.cast h0₁ i) := rfl
    rw [hx]
    simp only [Function.comp_apply, Neuromanifold.activation_apply, Pi.add_apply]; rfl
  have hg_eq : g_tail u₁ = g x := funext fun k => by
    have h1 := congrFun (congrFun (MLPSpec.realize_eq_tail_comp (reluSpec d₁) θ₁)
      (fun i => x (Fin.cast h0₁ i))) (Fin.cast hm₁.symm k)
    have h2 := MLPSpec.realize_cast (tail_reluSpec d₁) (Fin.tail θ₁) u₁ (Fin.cast hm₁.symm k)
    exact ((h2.trans (congrArg₂ ((reluSpec d₁).tail.realize (Fin.tail θ₁))
      (funext fun _ => congrArg u₁ (Fin.ext rfl)) (Fin.ext rfl))).trans h1.symm).trans
      (hθ₁ x k)
  have hreal := reluSpec_cons_realize d (ht := rfl) θ₀ θ' (fun i => x (Fin.cast hd0_w i))
    (Fin.cast (hp : d (Fin.last (L₁ + L₂ + 2)) = p).symm j)
  refine hreal.trans (Eq.trans ?_ ((hθ' u₁ j).trans (congrFun (congrArg h hg_eq) j)))
  exact congrArg₂ ((reluSpec (compWidths (Fin.tail d₁) d₂)).realize θ')
    (funext fun i => by rw [hu]; rfl) (Fin.ext rfl)

/-- Merging the affine output layer of a depth-`(L₁ + 1)` network realizing `g` with the affine
input layer of a depth-`(L₂ + 1)` network realizing `h` gives a depth-`(L₁ + L₂ + 1)` network
realizing `h ∘ g`. -/
theorem ReLUNetRealizes.comp {n m p L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetRealizes d₂ h) :
    ReLUNetRealizes (compWidths d₁ d₂) (h ∘ g) := by
  induction L₁ generalizing n with
  | zero =>
    refine reluNetRealizes_congr_depth (by omega) (fun i => ?_) (reluNetRealizes_comp_one hg hh)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · simp [compWidths_of_le]
    · simp only [Fin.succ_ne_zero, ↓reduceIte]
      rw [compWidths_of_lt _ _ (by simp)]
      exact congrArg d₂ (Fin.ext (by simp))
  | succ L₁ ih =>
    refine reluNetRealizes_congr_depth (by omega) (fun i => ?_)
      (reluNetRealizes_comp_succ (fun hg' => ih hg') hg)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · simp only [Fin.cons_zero, Fin.cast_zero, compWidths_zero]
    · simp only [Fin.cons_succ]
      by_cases hk : k.val ≤ L₁
      · rw [compWidths_of_le _ _ hk, compWidths_of_le _ _ (by simp; omega)]
        rfl
      · have hlt : L₁ < k.val := Nat.lt_of_not_le hk
        rw [compWidths_of_lt _ _ hlt, compWidths_of_lt _ _ (by simp; omega)]
        exact congrArg d₂ (Fin.ext (by simp))

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
  · simp [compWidths_of_le, hi]
  · have hlt : L < i.val := Nat.lt_of_not_le hi
    rw [compWidths_of_lt _ _ hlt]
    by_cases hiL : i = Fin.last (L + 2)
    · subst hiL
      simp
    · have hi1 : i.val = L + 1 := by
        have := i.isLt
        have : i.val ≠ L + 2 := fun h => hiL (Fin.ext h)
        omega
      simp [hiL, hi1]

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
    · obtain ⟨h0, h1, θ, hθ⟩ := reluNetComputes_iff.mp hf
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
