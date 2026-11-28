/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume
public import TauCeti.NumberTheory.Height.IndexOverPairs
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Covolume

/-!
# Comparing covolumes on a span of short forms

If the translates of short integral forms span nearly all the target, choose one independent
family from those translates. Its column lengths give an upper bound for its covolume, and
its index is bounded using all selected translates. A lower bound for the same family's
covolume plus twice its index then controls the weighted prime-sum remainder.

The comparison follows `New.star_inequality` in `grh/src/New/Reduction/MainInequality.lean`
of lsernau/grh-lean at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Matrix Module Real Set Submodule
open scoped ComplexOrder Matrix

namespace TauCeti.OneSidedBound

/-- Compare the upper and lower covolume bounds for short forms. `S` is the set of short
integral forms in the source, `P` the selected translates, `L` the target's local integral
submodules, and `coord` the coordinates of the distinguished lift in the rational metric `G`.
Here `A` is the number of infinite places times the derivative order, `H` the common main
amount, and `r` the remainder multiplied by the chain length. The lower estimate applies
to any independent family of the requisite size, with its actual covolume and index bounds. -/
theorem weightedRemainder_le_of_short_spanning_family
    {U V ι τ : Type*} [AddCommMonoid U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Fintype ι] (coord : V → (ι → ℂ)) {G : Matrix ι ι ℚ}
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    (L : (v : PrimePadicIso) → Submodule v.integers V)
    (t : Finset τ) (S : Set U) (P : τ → U →ₗ[ℂ] V)
    {A H r b : ℝ} (hb : 64 ≤ log b) (hd : 0 < finrank ℂ V) (hA : 0 ≤ A)
    (hH : 0 ≤ H + A * log b ^ 4) (hS : span ℂ S = ⊤)
    (hspan : (1 - 4 / b ^ 2) * (finrank ℂ V : ℝ) ≤
      finrank ℂ ↥(⨆ j ∈ t, LinearMap.range (P j)))
    (hcount : (t.card : ℝ) * finrank ℂ U ≤ 5 * log (1 + 2 * b ^ 2) * finrank ℂ V)
    (hshort : ∀ j ∈ t, ∀ u ∈ S, ∀ σ : ℂ ≃+* ℂ,
      let v := σ ∘ coord (P j u)
      ‖star v ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ v)‖ ≤ exp (H - r + A * log b ^ 4))
    (hindex : ∀ {n : ℕ} (y : Fin n → V), (∀ i, y i ∈ ⋃ j ∈ t, P j '' S) →
      PrimePadicIso.IndexLe L y (t.card * finrank ℂ U * (2 * (A * log b ^ 3))))
    (hlower : ∀ {n : ℕ} (y : Fin n → V), LinearIndependent ℂ y →
      (1 - 4 / b ^ 2) * (finrank ℂ V : ℝ) ≤ n → ∀ c δ : ℝ,
      (Matrix.of fun i j ↦ coord (y j) i).CovolumeLE G c → PrimePadicIso.IndexLe L y δ →
      (finrank ℂ V : ℝ) * (H - 3 * A * log b ^ 4) ≤ c + 2 * δ) :
    r ≤ A * log b ^ 5 := by
  classical
  have := Module.finite_of_finrank_pos hd
  let B := ⋃ j ∈ t, P j '' S
  have hrange : span ℂ B = ⨆ j ∈ t, LinearMap.range (P j) := by
    simp only [B, span_iUnion₂, ← map_span, hS, LinearMap.range_eq_map]
  let n := finrank ℂ (span ℂ B)
  obtain ⟨y, hy, _, hyind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ B
  have hn : n ≤ finrank ℂ V := (span ℂ B).finrank_le
  have hnear : (1 - 4 / b ^ 2) * (finrank ℂ V : ℝ) ≤ n := by
    exact (congrArg (fun W : Submodule ℂ V ↦ (finrank ℂ W : ℝ)) hrange).symm ▸ hspan
  -- Use the same selected columns for the Hadamard bound and the local index bound.
  let M : Matrix ι (Fin n) ℂ := Matrix.of fun i j ↦ coord (y j) i
  have hcov : M.CovolumeLE G (n * (H - r + A * log b ^ 4)) := by
    refine (covolumeLE_sum_of_forall_norm_diag_le (A := M) hG
      (b := fun _ ↦ H - r + A * log b ^ 4) ?_).mono (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl])
    intro σ i
    obtain ⟨j, hj, u, hu, e⟩ := Set.mem_iUnion₂.mp (hy i)
    have hv := hshort j hj u hu σ
    rw [e] at hv
    rw [Matrix.mul_assoc]
    simpa only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.mulVec, dotProduct, Pi.star_apply, Function.comp_apply] using hv
  have hδ : (t.card : ℝ) * finrank ℂ U * (2 * (A * log b ^ 3)) ≤
      (finrank ℂ V : ℝ) * (10 * log (1 + 2 * b ^ 2) * (A * log b ^ 3)) := by
    have hlog : 0 ≤ log b := by linarith
    have hcost := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hA (pow_nonneg hlog 3))
    nlinarith only [mul_le_mul_of_nonneg_right hcount hcost]
  exact weightedRemainder_le_of_covolume_bounds hb hd hn hnear hA hH le_rfl hδ
    (hlower y hyind hnear _ _ hcov (hindex y hy))

end TauCeti.OneSidedBound
