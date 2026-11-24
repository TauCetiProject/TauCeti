/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Submodule

/-!
# Examples of hermitian vector bundles over rings of integers

* `Ō_K` has rank one and the zero module with the zero form on every fibre has rank zero.
* `Ō_K` has `h_σ(1, 1) = 1`, and rescaling by `c` gives `‖1‖_σ = e^{-c}`.
* The hermitian line of the unit ideal `(1)` with all weights zero is isometric to `Ō_K`.
* A family of forms on `O_K` with `h_σ(1, 1) = 1` and `h_{conj σ}(1, 1) = 4` violates the
  conjugation condition, although each form could be positive definite: it is not a hermitian
  metric.
* In the line of a fractional ideal with weights `λ_v`, `‖x‖_v = e^{-λ_v} |x|_v`.
* If `e₁, e₂` are orthonormal at `σ` (as for `ℤ²` with the standard metric), the quotient metric
  on `E ⧸ 𝓞 K (e₁ + e₂)` gives `‖[e₁]‖_σ = 1/√2`, not 1: the quotient metric is not the metric of
  a complement lattice such as `𝓞 K e₁`.
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

-- The quotient metric of `E ⧸ 𝓞 K (e₁ + e₂)` for `e₁, e₂` orthonormal at `σ` has
-- `‖[e₁]‖_σ = 1/√2`, computed through the lift `(e₁ - e₂) / 2`, which is orthogonal to `e₁ + e₂`.
example {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    (h : HermitianMetric K E) (σ : K →+* ℂ) (e₁ e₂ : E)
    (h₁₁ : h.form σ (1 ⊗ₜ e₁) (1 ⊗ₜ e₁) = 1) (h₂₂ : h.form σ (1 ⊗ₜ e₂) (1 ⊗ₜ e₂) = 1)
    (h₁₂ : h.form σ (1 ⊗ₜ e₁) (1 ⊗ₜ e₂) = 0) :
    (h.quotient (Submodule.span (𝓞 K) {e₁ + e₂})).norm σ (1 ⊗ₜ Submodule.Quotient.mk e₁) =
      √2⁻¹ := by
  set F := Submodule.span (𝓞 K) {e₁ + e₂}
  have h₂₁ : h.form σ (1 ⊗ₜ e₂) (1 ⊗ₜ e₁) = 0 := h.form_eq_zero_symm.mp h₁₂
  have hF (w : Codomain σ ⊗[𝓞 K] F) :
      ∃ c : ℂ, F.subtype.baseChange (Codomain σ) w = c • (1 ⊗ₜ (e₁ + e₂)) := by
    induction w using TensorProduct.inductionOn with
    | tmul c x =>
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 x.property
      refine ⟨Codomain.equiv σ (r • c), ?_⟩
      rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, ← hr, ← TensorProduct.smul_tmul,
        Codomain.tmul_eq_smul]
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨a, ha⟩ := h₁
      obtain ⟨b, hb⟩ := h₂
      exact ⟨a + b, by rw [map_add, ha, hb, add_smul]⟩
  set v : Codomain σ ⊗[𝓞 K] E := (2⁻¹ : ℂ) • (1 ⊗ₜ e₁ - 1 ⊗ₜ e₂)
  have hv : h.IsOrthogonalFiber F σ v := h.isOrthogonalFiber_iff F |>.mpr fun w ↦ by
    obtain ⟨c, hc⟩ := hF w
    simp only [hc, v, TensorProduct.tmul_add, map_smul, map_sub, map_add, LinearMap.map_smulₛₗ₂,
      LinearMap.add_apply, h₁₁, h₂₂, h₁₂, h₂₁]
    ring
  have hmk : F.mkQ.baseChange (Codomain σ) v = 1 ⊗ₜ Submodule.Quotient.mk e₁ := by
    have h0 : F.mkQ.baseChange (Codomain σ) (1 ⊗ₜ (e₁ + e₂)) = 0 := by
      rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero F).2 (Submodule.mem_span_singleton_self _),
        TensorProduct.tmul_zero]
    have hv' : v = 1 ⊗ₜ e₁ - (2⁻¹ : ℂ) • (1 ⊗ₜ (e₁ + e₂)) := by
      simp only [v, TensorProduct.tmul_add]
      module
    rw [hv', map_sub, LinearMap.map_smul_of_tower, h0, smul_zero, sub_zero,
      LinearMap.baseChange_tmul, Submodule.mkQ_apply]
  rw [← hmk, h.norm_quotient_baseChange_mkQ F hv, HermitianMetric.norm_def]
  congr 1
  simp only [v, map_smul, map_sub, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply, h₁₁, h₂₂, h₁₂,
    h₂₁]
  norm_num
