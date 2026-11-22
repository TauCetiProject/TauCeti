/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Prod
public import TauCeti.NumberTheory.NumberField.HermitianBundle.TensorProduct

/-!
# Examples of hermitian vector bundles over rings of integers

* `Ō_K` has rank one and the zero module with the zero form on every fibre has rank zero.
* `Ō_K` has `h_σ(1, 1) = 1`, and rescaling by `c` gives `‖1‖_σ = e^{-c}`.
* The hermitian line of the unit ideal `(1)` with all weights zero is isometric to `Ō_K`.
* A family of forms on `O_K` with `h_σ(1, 1) = 1` and `h_{conj σ}(1, 1) = 4` violates the
  conjugation condition, although each form could be positive definite: it is not a hermitian
  metric.
* In the line of a fractional ideal with weights `λ_v`, `‖x‖_v = e^{-λ_v} |x|_v`.
* `Ō_K ⊕ Ō_K` has rank two, its basis vectors are orthogonal, and `‖e₁ + e₂‖_σ² = 2`.
* `Ō_K ⊗ E ≅ E` isometrically, `Ō_K ⊗ Ō_K` has rank one, and `‖1 ⊗ 1‖_σ = 1`.
-/

public section

open scoped TensorProduct nonZeroDivisors

open NumberField NumberField.ComplexEmbedding TauCeti

variable {K : Type*} [Field K] [NumberField K]

example : (HermitianBundle.trivial K).rank = 1 ∧ (HermitianBundle.zero K).rank = 0 :=
  ⟨HermitianBundle.rank_trivial K, HermitianBundle.rank_zero K⟩

example (σ : K →+* ℂ) : (HermitianMetric.trivial K).form σ (1 ⊗ₜ 1) (1 ⊗ₜ 1) = 1 := by
  simp

-- Rescaling multiplies every norm by `e^{-c}`.
example (σ : K →+* ℂ) (c : ℝ) :
    ((HermitianMetric.trivial K).rescale c).norm σ (1 ⊗ₜ 1) = Real.exp (-c) := by
  simp

-- The unit ideal `(1)` with all weights zero is isometric to `Ō_K`.
example :
    Nonempty (HermitianMetric.IsometryEquiv (HermitianMetric.trivial K)
      (HermitianMetric.fractionalIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) one_ne_zero 0)) :=
  ⟨HermitianMetric.isometryEquivTrivialFractionalIdealOne K⟩

-- The conjugation condition excludes `h_σ(1, 1) = 1` together with `h_{conj σ}(1, 1) = 4`.
example (h : HermitianMetric K (𝓞 K)) (σ : K →+* ℂ)
    (h₁ : h.form σ (1 ⊗ₜ 1) (1 ⊗ₜ 1) = 1) :
    h.form (conjugate σ) (1 ⊗ₜ 1) (1 ⊗ₜ 1) ≠ 4 := by
  rw [h.form_conjugate_tmul, h₁, map_one]
  norm_num

example {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (w : InfinitePlace K → ℝ)
    (v : InfinitePlace K) (x : I) :
    (HermitianMetric.fractionalIdeal I hI w).placeNorm v x = Real.exp (-w v) * v x := by
  simp

-- `Ō_K ⊕ Ō_K` has rank two.
example : ((HermitianBundle.trivial K).prod (HermitianBundle.trivial K)).rank = 2 := by
  simp

-- The basis vectors `e₁, e₂` of `Ō_K ⊕ Ō_K` are orthogonal.
example (σ : K →+* ℂ) :
    ((HermitianMetric.trivial K).prod (HermitianMetric.trivial K)).form σ
      (1 ⊗ₜ ((1, 0) : 𝓞 K × 𝓞 K)) (1 ⊗ₜ ((0, 1) : 𝓞 K × 𝓞 K)) = 0 := by
  simp

-- In `Ō_K ⊕ Ō_K`, `‖e₁ + e₂‖_σ² = 2`.
example (σ : K →+* ℂ) :
    ((HermitianMetric.trivial K).prod (HermitianMetric.trivial K)).norm σ
      (1 ⊗ₜ ((1, 1) : 𝓞 K × 𝓞 K)) ^ 2 = 2 := by
  rw [HermitianMetric.norm_prod_tmul_sq]
  norm_num

-- `Ō_K ⊗ E ≅ E` isometrically.
example {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (h : HermitianMetric K E) :
    Nonempty (HermitianMetric.IsometryEquiv ((HermitianMetric.trivial K).tmul h) h) :=
  ⟨HermitianMetric.tensorLId h⟩

-- `Ō_K ⊗ Ō_K` has rank one.
example : ((HermitianBundle.trivial K).tmul (HermitianBundle.trivial K)).rank = 1 := by
  simp

-- In `Ō_K ⊗ Ō_K`, `‖1 ⊗ 1‖_σ = 1`.
example (σ : K →+* ℂ) :
    ((HermitianMetric.trivial K).tmul (HermitianMetric.trivial K)).norm σ
      (1 ⊗ₜ ((1 : 𝓞 K) ⊗ₜ (1 : 𝓞 K))) = 1 := by
  simp
