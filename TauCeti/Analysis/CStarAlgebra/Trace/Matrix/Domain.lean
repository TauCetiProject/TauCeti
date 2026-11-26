/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Domain
public import TauCeti.Analysis.CStarAlgebra.Trace.Matrix.Basic

/-!
# The domain of the matrix amplification of a trace

For a trace `τ` on a C⋆-algebra `B` (`TauCeti.IsTrace`) and its matrix amplification
`τ_n(x) = Σᵢ τ(xᵢᵢ)` on `M_n(B) = CStarMatrix n n B` (`TauCeti.matrixTrace`), the domain of `τ_n`
consists of the matrices with all entries in the domain of `τ`: `𝔪_{τ_n} = M_n(𝔪_τ)`
(`TauCeti.IsTrace.mem_domain_matrixTrace_iff`, Thomsen [WTK], Lemma 3.1 (f)), and on it the linear
extension of `τ_n` is `x ↦ Σᵢ τ(xᵢᵢ)` for the linear extension of `τ`
(`TauCeti.IsTrace.linearMap_matrixTrace`).

Both domains are spanned by products `y⋆x` of square-integrable elements
(`TauCeti.IsTrace.domain_eq_span_star_mul`), and `𝔫_{τ_n} = M_n(𝔫_τ)`
(`TauCeti.IsTrace.mem_sqIntegrable_matrixTrace_iff`). The entries `Σₖ y⋆ₖᵢ xₖⱼ` of `y⋆x` then lie in
`𝔪_τ`; conversely the matrix unit `Eᵢⱼ(b⋆a)` is `Eᵢᵢ(b)⋆ Eᵢⱼ(a)`, and every matrix is the sum of
its entries placed at matrix units.

## Main results

* `TauCeti.IsTrace.mem_domain_matrixTrace_iff`: `𝔪_{τ_n} = M_n(𝔪_τ)`.
* `TauCeti.IsTrace.linearMap_matrixTrace`: `τ_n(x) = Σᵢ τ(xᵢᵢ)` on `𝔪_{τ_n}`.

## References

* Klaus Thomsen, *On weights, traces and K-theory*, arXiv:2211.03172, version of 15 March 2024:
  Lemma 3.1.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞} {n : Type*} [Fintype n]

namespace IsTrace

/-- The matrix with the single entry `z` at `(i, j)` is square-integrable for `τ_n` when `z` is
square-integrable for `τ`. -/
private theorem single_mem_sqIntegrable_matrixTrace [DecidableEq n] (hτ : IsTrace τ) (i j : n)
    {z : B} (hz : z ∈ sqIntegrable τ) :
    CStarMatrix.ofMatrix (Matrix.single i j z) ∈ sqIntegrable (matrixTrace τ n) := by
  refine hτ.mem_sqIntegrable_matrixTrace_iff.2 fun p q ↦ ?_
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    simpa [CStarMatrix.ofMatrix_apply] using hz
  · simpa [CStarMatrix.ofMatrix_apply, Matrix.single_apply, h] using hτ.zero_mem_sqIntegrable

/-- The matrix with the single entry `b` at `(i, j)` lies in the domain of `τ_n` when `b` lies in
the domain of `τ`. -/
private theorem single_mem_domain_matrixTrace [DecidableEq n] (hτ : IsTrace τ) (i j : n) {b : B}
    (hb : b ∈ domain τ) :
    CStarMatrix.ofMatrix (Matrix.single i j b) ∈ domain (matrixTrace τ n) := by
  rw [hτ.domain_eq_span_star_mul] at hb
  induction hb using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    -- `Eᵢⱼ(y⋆x) = Eᵢᵢ(y)⋆ Eᵢⱼ(x)`.
    rw [← CStarMatrix.ofMatrix_single_mul_ofMatrix_single_same i i j (star y) x,
      ← CStarMatrix.star_ofMatrix_single i i y]
    exact hτ.isTrace_matrixTrace.star_mul_mem_domain
      (hτ.single_mem_sqIntegrable_matrixTrace i j hx)
      (hτ.single_mem_sqIntegrable_matrixTrace i i hy)
  | zero => simp [Matrix.single_zero]
  | add x y _ _ hx hy =>
    simpa [Matrix.single_add] using (domain (matrixTrace τ n)).add_mem hx hy
  | smul c x _ hx =>
    simpa [Matrix.smul_single] using (domain (matrixTrace τ n)).smul_mem c hx

/-- **`𝔪_{τ_n} = M_n(𝔪_τ)`**: a matrix lies in the domain of the matrix amplification exactly
when all its entries lie in the domain of `τ` (Thomsen [WTK], Lemma 3.1 (f)). -/
theorem mem_domain_matrixTrace_iff (hτ : IsTrace τ) {x : CStarMatrix n n B} :
    x ∈ domain (matrixTrace τ n) ↔ ∀ i j, x i j ∈ domain τ := by
  constructor
  · intro hx
    rw [hτ.isTrace_matrixTrace.domain_eq_span_star_mul] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      intro i j
      rw [CStarMatrix.mul_apply]
      exact Submodule.sum_mem _ fun k _ ↦ by
        simpa [CStarMatrix.star_apply] using hτ.star_mul_mem_domain
          (hτ.mem_sqIntegrable_matrixTrace_iff.1 hx k j)
          (hτ.mem_sqIntegrable_matrixTrace_iff.1 hy k i)
    | zero => exact fun _ _ ↦ (domain τ).zero_mem
    | add x y _ _ hx hy => exact fun i j ↦ (domain τ).add_mem (hx i j) (hy i j)
    | smul c x _ hx => exact fun i j ↦ (domain τ).smul_mem c (hx i j)
  · intro hx
    classical
    rw [CStarMatrix.eq_sum_ofMatrix_single x]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
      hτ.single_mem_domain_matrixTrace i j (hx i j)

/-- **The linear extension of `τ_n`**: on `𝔪_{τ_n} = M_n(𝔪_τ)`, the linear extension of the
matrix amplification is `x ↦ Σᵢ τ(xᵢᵢ)`, for the linear extension of `τ`. -/
theorem linearMap_matrixTrace (hτ : IsTrace τ) (x : domain (matrixTrace τ n)) :
    hτ.isTrace_matrixTrace.linearMap x =
      ∑ i, hτ.linearMap ⟨(x : CStarMatrix n n B) i i,
        hτ.mem_domain_matrixTrace_iff.1 x.property i i⟩ := by
  -- The diagonal entry `x ↦ xᵢᵢ` as a linear map `𝔪_{τ_n} → 𝔪_τ`.
  let d (i : n) : domain (matrixTrace τ n) →ₗ[ℂ] domain τ :=
    LinearMap.codRestrict (domain τ)
      (Matrix.entryLinearMap ℂ B i i ∘ₗ CStarMatrix.ofMatrixₗ.symm.toLinearMap ∘ₗ
        (domain (matrixTrace τ n)).subtype)
      fun x ↦ by simpa using hτ.mem_domain_matrixTrace_iff.1 x.property i i
  have hd (i : n) (x : domain (matrixTrace τ n)) :
      d i x = ⟨(x : CStarMatrix n n B) i i, hτ.mem_domain_matrixTrace_iff.1 x.property i i⟩ :=
    Subtype.ext (by simp [d])
  -- The right side is linear in `x` and agrees with `τ_n` on `𝔪_{τ_n}⁺`.
  have hf : ∑ i, hτ.linearMap ∘ₗ d i = hτ.isTrace_matrixTrace.linearMap := by
    refine hτ.isTrace_matrixTrace.eq_linearMap fun y hy ↦ ?_
    have hdiag (i : n) : y i i ∈ finitePart τ := by
      refine mem_finitePart.2 ⟨CStarMatrix.diag_nonneg_of_nonneg (mem_finitePart.1 hy).1 i,
        lt_of_le_of_lt ?_ (mem_finitePart.1 hy).2⟩
      rw [matrixTrace_apply]
      exact Finset.single_le_sum (f := fun i ↦ τ (y i i)) (fun _ _ ↦ zero_le)
        (Finset.mem_univ i)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hd]
    rw [matrixTrace_apply, ENNReal.toReal_sum fun i _ ↦ (mem_finitePart.1 (hdiag i)).2.ne,
      Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hτ.linearMap_apply_of_mem_finitePart (hdiag i)
  rw [← hf, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, hd]

end IsTrace

end TauCeti
