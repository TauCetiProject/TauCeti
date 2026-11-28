/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Trace ideals, block-diagonal flattening determinants, and polynomial traces

This file collects four algebraic ingredients for the tied-row construction in Ribet's method:
1. `TauCeti.traceIdeal`: the two-sided ideal of elements `w` of an `R`-algebra `Λ` whose traces
   `(ρ (w * s)).trace` lie in an `R`-submodule `𝒥 ≤ L` for all `s : Λ`.
2. `TauCeti.det_blockFlatten_eq_mul_prod`: for a block-diagonal map `χ` decomposing as a block
   `ψ` plus diagonal characters `η e`, the determinant of the flattened block matrix `(χ (M i j))`
   factors as the product of the flattened `ψ`-determinant and `∏ e, (M.map (η e)).det`.
3. `TauCeti.map_mul_eq_zero_of_blocks`: vanishing of `χ (ρ₁ * ρ₀)` when `ρ₁` is supported only
   on the `0`-th character block and `ρ₀` vanishes there.
4. `TauCeti.trace_mul_aeval_apply`: where `ρ (ρ₁ * ρ₀)` vanishes at `x`, the trace of
   `ρ (ρ₁ * aeval ρ₀ P)` at `x` equals `P.coeff 0 * (ρ ρ₁).trace x`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/RibetMethod.lean` (`New.Selmer.traceIdeal`,
`New.Selmer.mem_traceIdeal`, `New.Selmer.det_comp_map_eq_mul_prod`,
`New.Selmer.map_mul_eq_zero_of_blocks`, `New.Selmer.trace_mul_aeval_apply`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Matrix Polynomial

/-- The two-sided ideal of `Λ` consisting of elements `w` such that `(ρ (w * s)).trace ∈ 𝒥` for
every `s : Λ`. -/
def traceIdeal {R L Λ σ : Type*} [CommRing R] [CommRing L] [Algebra R L] [Ring Λ] [Algebra R Λ]
    [Fintype σ] [DecidableEq σ] (ρ : Λ →ₐ[R] Matrix σ σ L) (𝒥 : Submodule R L) :
    TwoSidedIdeal Λ :=
  .mk' {w | ∀ s : Λ, (ρ (w * s)).trace ∈ 𝒥}
    (fun s ↦ by rw [zero_mul, map_zero, trace_zero]; exact zero_mem 𝒥)
    (fun hw hw' s ↦ by rw [add_mul, map_add, trace_add]; exact add_mem (hw s) (hw' s))
    (fun hw s ↦ by rw [neg_mul, map_neg, trace_neg]; exact neg_mem (hw s))
    (fun {w w'} hw' s ↦ by
      rw [mul_assoc, map_mul, trace_mul_comm, ← map_mul, mul_assoc]
      exact hw' (s * w))
    (fun {w w'} hw s ↦ by rw [mul_assoc]; exact hw (w' * s))

/-- Membership characterization for `TauCeti.traceIdeal`. -/
theorem mem_traceIdeal {R L Λ σ : Type*} [CommRing R] [CommRing L] [Algebra R L] [Ring Λ]
    [Algebra R Λ] [Fintype σ] [DecidableEq σ] {ρ : Λ →ₐ[R] Matrix σ σ L} {𝒥 : Submodule R L}
    {w : Λ} : w ∈ traceIdeal ρ 𝒥 ↔ ∀ s : Λ, (ρ (w * s)).trace ∈ 𝒥 := by
  rw [traceIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]

/-- If `χ` decomposes along `blockEquiv : r ⊕ Fin t ≃ σ` as a block `ψ` plus diagonal characters
`η e`, then the determinant of the flattened block matrix `(χ (M i j))` equals the product of the
flattened `ψ`-determinant and `∏ e, (M.map (η e)).det`. -/
theorem det_blockFlatten_eq_mul_prod {R A ι σ r : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype r] [DecidableEq r] {t : ℕ} (blockEquiv : r ⊕ Fin t ≃ σ)
    {χ : A → Matrix σ σ R} {ψ : A → Matrix r r R} {η : Fin t → A → R}
    (hχ : ∀ c : A, χ c = reindex blockEquiv blockEquiv
      (fromBlocks (ψ c) 0 0 (diagonal fun e : Fin t ↦ η e c)))
    (M : Matrix ι ι A) :
    (Matrix.of fun (p q : ι × σ) ↦ χ (M p.fst q.fst) p.snd q.snd).det =
      (Matrix.of fun (p q : ι × r) ↦ ψ (M p.fst q.fst) p.snd q.snd).det *
        ∏ e : Fin t, (M.map (η e)).det := by
  let blockEquiv' : ι × r ⊕ ι × Fin t ≃ ι × σ :=
    (Equiv.prodSumDistrib ι r (Fin t)).symm.trans (.prodCongr (.refl ι) blockEquiv)
  have h_blocks :
      (Matrix.of fun (p q : ι × σ) ↦ χ (M p.fst q.fst) p.snd q.snd).submatrix
        blockEquiv' blockEquiv' =
      fromBlocks (Matrix.of fun (p q : ι × r) ↦ ψ (M p.fst q.fst) p.snd q.snd) 0 0
        (blockDiagonal fun e : Fin t ↦ M.map (η e)) := by
    ext (a | a) (b | b) <;> simp [blockEquiv', hχ, blockDiagonal, diagonal]
  rw [← det_submatrix_equiv_self blockEquiv', h_blocks, det_fromBlocks_zero₂₁,
    det_blockDiagonal]

/-- If `χ` decomposes along `blockEquiv` as a block `ψ` plus diagonal characters `η e`, `ρ₁`
vanishes under `ψ` and every `η e` for `e ≠ 0`, and `η 0 ρ₀ = 0`, then `χ (ρ₁ * ρ₀) = 0`. -/
theorem map_mul_eq_zero_of_blocks {O A σ r : Type*} [CommSemiring O] [Semiring A] [Algebra O A]
    [Fintype σ] [DecidableEq σ] [Fintype r] [DecidableEq r] {t : ℕ} [NeZero t]
    (blockEquiv : r ⊕ Fin t ≃ σ) (χ : A →ₐ[O] Matrix σ σ O) (ψ : A →ₐ[O] Matrix r r O)
    (η : Fin t → A →ₐ[O] O)
    (hχ : ∀ w : A, χ w = reindex blockEquiv blockEquiv
      (fromBlocks (ψ w) 0 0 (diagonal fun e : Fin t ↦ η e w)))
    {ρ₀ ρ₁ : A} {μ₀ : O} (hψ₁ : ψ ρ₁ = 0)
    (hη₁ : ∀ e : Fin t, η e ρ₁ = if e = 0 then μ₀ else 0) (hη₀ : η 0 ρ₀ = 0) :
    χ (ρ₁ * ρ₀) = 0 := by
  have h_η (e : Fin t) : η e (ρ₁ * ρ₀) = 0 := by
    rw [map_mul, hη₁]
    split_ifs with he
    · rw [he, hη₀, mul_zero]
    · rw [zero_mul]
  have h_ψ : ψ (ρ₁ * ρ₀) = 0 := by rw [map_mul, hψ₁, zero_mul]
  simp only [hχ, h_ψ, h_η, diagonal_zero, fromBlocks_zero, reindex_apply, submatrix_zero,
    Pi.zero_apply]

/-- At a point `x : Y` where every entry of `ρ (ρ₁ * ρ₀)` vanishes, the trace of
`ρ (ρ₁ * aeval ρ₀ P)` at `x` equals `algebraMap A (Y → L) (P.coeff 0) x * (ρ ρ₁).trace x`. -/
theorem trace_mul_aeval_apply {A Λ Y L σ : Type*} [CommSemiring A] [Semiring Λ] [Algebra A Λ]
    [Semiring L] [Algebra A (Y → L)] [Fintype σ] [DecidableEq σ]
    (ρ : Λ →ₐ[A] Matrix σ σ (Y → L)) (ρ₀ ρ₁ : Λ) (P : A[X]) (x : Y)
    (h_zero : ∀ i j : σ, ρ (ρ₁ * ρ₀) i j x = 0) :
    (ρ (ρ₁ * aeval ρ₀ P)).trace x = algebraMap A (Y → L) (P.coeff 0) x * (ρ ρ₁).trace x := by
  have h_split : ρ₁ * aeval ρ₀ P =
      ρ₁ * ρ₀ * aeval ρ₀ P.divX + algebraMap A Λ (P.coeff 0) * ρ₁ := by
    conv_lhs => rw [← P.X_mul_divX_add]
    rw [aeval_add, aeval_mul, aeval_X, aeval_C, mul_add, mul_assoc, Algebra.commutes]
  have h_vanish : (ρ (ρ₁ * ρ₀) * ρ (aeval ρ₀ P.divX)).trace x = 0 := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, h_zero,
      zero_mul, sum_const_zero]
  rw [h_split, map_add, map_mul ρ (ρ₁ * ρ₀), map_mul ρ (algebraMap A Λ _), ρ.commutes,
    ← Algebra.smul_def, trace_add, trace_smul, Pi.add_apply, h_vanish, zero_add,
    Algebra.smul_def, Pi.mul_apply]

end TauCeti
