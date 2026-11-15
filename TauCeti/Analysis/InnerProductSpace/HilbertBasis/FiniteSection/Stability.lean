/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic
public import TauCeti.Analysis.Normed.Operator.StableSequence
import Mathlib.Data.Nat.Bitwise

/-!
# Stability of the finite-section method

Let `T` be a bounded operator on a Hilbert space with a Hilbert basis `b` indexed by `ℕ`, and let
`Aₙ = T.finiteSection b n` be its compression to the first `n + 1` coordinates. The finite-section
method approximates the solution of `T x = y` by the solutions `xₙ` of the finite linear systems
`Aₙ xₙ = Pₙ y`, where `Pₙ` keeps the first `n + 1` coordinates. The method applies when the
sequence `Aₙ` is *stable* in the sense of `TauCeti.IsStableSequence`.

This file proves the basic theory of this situation.

* Uniform lower bounds of the finite sections pass to `T`, and so do those of the adjoint
  sections. Hence stability of the finite sections forces `T` to be invertible, with
  `‖T⁻¹‖` bounded by any eventual bound for `‖Aₙ⁻¹‖`.
* Under stability, the zero-extended solutions `xₙ` converge to the solution `x` of `T x = y`.
  More precisely, when `‖Aₙ⁻¹‖ ≤ M` the error is quasi-optimal:
  `‖xₙ - x‖ ≤ (1 + M ‖T‖) ‖x - Pₙ x‖`.
* Invertibility of `T` alone does not give stability: the unitary exchanging the basis vectors
  `b (2k)` and `b (2k + 1)` has singular finite sections of every odd size.

Since `‖Aₙ‖ ≤ ‖T‖`, stability also bounds the condition numbers of the finite sections uniformly,
by `TauCeti.IsStableSequence.exists_conditionNumber_le`.

## Main results

* `ContinuousLinearMap.norm_le_mul_norm_apply_of_finiteSection`: an eventual uniform lower bound
  for the finite sections is a lower bound for `T`.
* `ContinuousLinearMap.isUnit_and_norm_ringInverse_le_of_finiteSection`: eventually invertible
  finite sections with `‖Aₙ⁻¹‖ ≤ M` make `T` invertible with `‖T⁻¹‖ ≤ M`.
* `ContinuousLinearMap.isUnit_of_isStableSequence_finiteSection`: stable finite sections make `T`
  invertible.
* `ContinuousLinearMap.norm_finiteSection_solution_sub_le`: the quasi-optimal error estimate.
* `ContinuousLinearMap.tendsto_finiteSection_solution`: convergence of the finite-section
  solutions under stability.
* `HilbertBasis.exists_mem_unitary_not_isStableSequence_finiteSection`: a unitary operator whose
  finite sections are not stable.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Sections 1.4 and 2.1.
* R. Hagen, S. Roch and B. Silbermann, *C*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter Topology TauCeti

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[𝕜] H} {b : HilbertBasis ℕ 𝕜 H}

/-- If the finite sections of `T` are eventually bounded below by `M⁻¹` uniformly, then so is
`T`. -/
theorem norm_le_mul_norm_apply_of_finiteSection {M : ℝ}
    (hM : ∀ᶠ n in atTop, ∀ y, ‖y‖ ≤ M * ‖T.finiteSection b n y‖) (x : H) :
    ‖x‖ ≤ M * ‖T x‖ := by
  refine le_of_tendsto_of_tendsto (b.tendsto_finiteProjection x).norm
    ((T.tendsto_zeroExtendedFiniteSection b x).norm.const_mul M) (hM.mono fun n h ↦ ?_)
  simpa [zeroExtendedFiniteSection_apply, ← HilbertBasis.finiteInclusion_coordinateCutoff] using
    h (b.coordinateCutoff n x)

/-- If the finite sections of `T` are eventually invertible with `‖Aₙ⁻¹‖ ≤ M`, then `T` is
invertible and `‖T⁻¹‖ ≤ M`. -/
theorem isUnit_and_norm_ringInverse_le_of_finiteSection {M : ℝ}
    (hM : ∀ᶠ n in atTop,
      IsUnit (T.finiteSection b n) ∧ ‖Ring.inverse (T.finiteSection b n)‖ ≤ M) :
    IsUnit T ∧ ‖Ring.inverse T‖ ≤ M := by
  have hM' : ∀ᶠ n in atTop,
      IsUnit ((adjoint T).finiteSection b n) ∧
        ‖Ring.inverse ((adjoint T).finiteSection b n)‖ ≤ M := by
    refine hM.mono fun n ⟨hu, hn⟩ ↦ ?_
    rw [← adjoint_finiteSection, isUnit_adjoint_iff, ringInverse_adjoint,
      LinearIsometryEquiv.norm_map]
    exact ⟨hu, hn⟩
  have lower {S : H →L[𝕜] H}
      (hS : ∀ᶠ n in atTop,
        IsUnit (S.finiteSection b n) ∧ ‖Ring.inverse (S.finiteSection b n)‖ ≤ M) (x : H) :
      ‖x‖ ≤ M * ‖S x‖ :=
    norm_le_mul_norm_apply_of_finiteSection (hS.mono fun _ ⟨hu, hn⟩ y ↦
      (norm_le_norm_ringInverse_mul_norm_apply hu y).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) x
  obtain ⟨n, -, hn⟩ := hM.exists
  exact isUnit_and_norm_ringInverse_le_of_forall_norm_le ((norm_nonneg _).trans hn) (lower hM)
    (injective_of_forall_norm_le (lower hM'))

/-- An operator whose finite sections form a stable sequence is invertible. -/
theorem isUnit_of_isStableSequence_finiteSection (h : IsStableSequence (T.finiteSection b)) :
    IsUnit T := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp h
  exact (isUnit_and_norm_ringInverse_le_of_finiteSection hM).1

/-- The quasi-optimal error estimate of the finite-section method: if the `n`-th finite section
`Aₙ` is invertible with `‖Aₙ⁻¹‖ ≤ M`, then the zero extension of the solution of
`Aₙ xₙ = Pₙ (T x)` is within `(1 + M ‖T‖) ‖x - Pₙ x‖` of `x`. -/
theorem norm_finiteSection_solution_sub_le {M : ℝ} {n : ℕ} (hu : IsUnit (T.finiteSection b n))
    (hn : ‖Ring.inverse (T.finiteSection b n)‖ ≤ M) (x : H) :
    ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) (b.coordinateCutoff n (T x))) - x‖ ≤
      (1 + M * ‖T‖) * ‖x - b.finiteProjection n x‖ := by
  set A := T.finiteSection b n
  set c := b.coordinateCutoff n
  set z := x - b.finiteProjection n x
  have hM : 0 ≤ M := (norm_nonneg _).trans hn
  -- The finite residual of the truncated exact solution `c x` is the truncation of `T z`.
  have hres : Ring.inverse A (c (T x)) - c x = Ring.inverse A (c (T z)) := by
    have hAc : A (c x) = c (T (b.finiteProjection n x)) := by
      simp [A, c, finiteSection_coordinateCutoff]
    simp only [z, map_sub, ← hAc, ringInverse_apply_apply hu]
  have hsplit : b.finiteInclusion n (Ring.inverse A (c (T x))) - x =
      b.finiteInclusion n (Ring.inverse A (c (T z))) - z := by
    rw [← hres, map_sub]
    simp [z, c]
  have hcut : ‖c (T z)‖ ≤ ‖T‖ * ‖z‖ :=
    calc
      ‖c (T z)‖ ≤ 1 * ‖T z‖ :=
        (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (b.norm_coordinateCutoff_le n)
          (norm_nonneg _))
      _ ≤ ‖T‖ * ‖z‖ := by rw [one_mul]; exact le_opNorm _ _
  calc
    _ = ‖b.finiteInclusion n (Ring.inverse A (c (T z))) - z‖ := by rw [hsplit]
    _ ≤ ‖Ring.inverse A (c (T z))‖ + ‖z‖ :=
      (norm_sub_le _ _).trans_eq (by rw [LinearIsometry.norm_map])
    _ ≤ M * (‖T‖ * ‖z‖) + ‖z‖ := by
      gcongr
      exact (le_opNorm _ _).trans (mul_le_mul hn hcut (norm_nonneg _) hM)
    _ = (1 + M * ‖T‖) * ‖z‖ := by ring

/-- Convergence of the finite-section method: if the finite sections of `T` are stable, then for
every `x` the zero extensions of the solutions of `Aₙ xₙ = Pₙ (T x)` converge to `x`. -/
theorem tendsto_finiteSection_solution (h : IsStableSequence (T.finiteSection b)) (x : H) :
    Tendsto
      (fun n ↦ b.finiteInclusion n
        (Ring.inverse (T.finiteSection b n) (b.coordinateCutoff n (T x))))
      atTop (𝓝 x) := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hP : Tendsto (fun n ↦ (1 + M * ‖T‖) * ‖x - b.finiteProjection n x‖) atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp (b.tendsto_finiteProjection x)).congr
      fun n ↦ norm_sub_rev _ _).const_mul (1 + M * ‖T‖)
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (hM.mono fun n ⟨hu, hn⟩ ↦ norm_finiteSection_solution_sub_le hu hn x) hP

/-- Convergence of the finite-section method, stated for the right-hand side: if the finite
sections of `T` are stable, then the zero extensions of the solutions of `Aₙ xₙ = Pₙ y` converge
to `T⁻¹ y`. -/
theorem tendsto_finiteSection_solution_ringInverse (h : IsStableSequence (T.finiteSection b))
    (y : H) :
    Tendsto
      (fun n ↦ b.finiteInclusion n (Ring.inverse (T.finiteSection b n) (b.coordinateCutoff n y)))
      atTop (𝓝 (Ring.inverse T y)) := by
  have hy : T (Ring.inverse T y) = y :=
    apply_ringInverse_apply (isUnit_of_isStableSequence_finiteSection h) y
  simpa only [hy] using tendsto_finiteSection_solution h (Ring.inverse T y)

end ContinuousLinearMap

namespace HilbertBasis

/-- The unitary operator exchanging the basis vectors `b (2k)` and `b (2k + 1)` for every `k`
has a singular finite section of every odd size `n + 1`: the last coordinate is sent outside the
section. -/
theorem exists_mem_unitary_forall_even_not_isUnit_finiteSection (b : HilbertBasis ℕ 𝕜 H) :
    ∃ U ∈ unitary (H →L[𝕜] H), (∀ k, U (b k) = b (k ^^^ 1)) ∧
      ∀ n, Even n → ¬IsUnit (U.finiteSection b n) := by
  have hσ : Function.Involutive (· ^^^ 1 : ℕ → ℕ) := fun k ↦ by simp [Nat.xor_assoc]
  let b' : HilbertBasis ℕ 𝕜 H := HilbertBasis.mk (b.orthonormal.comp _ hσ.injective)
    (by rw [hσ.surjective.range_comp, b.dense_span])
  let U : H ≃ₗᵢ[𝕜] H := b.repr.trans b'.repr.symm
  have hU : ∀ k, U (b k) = b (k ^^^ 1) := fun k ↦ by
    classical
    simp [U, b', HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  refine ⟨U, by simpa using (Unitary.linearIsometryEquiv.symm U).property, hU, fun n hn hu ↦ ?_⟩
  set A := (U : H →L[𝕜] H).finiteSection b n
  let e : EuclideanSpace 𝕜 (Fin (n + 1)) := PiLp.single 2 (Fin.last n) 1
  have hAe : A e = 0 := by
    ext i
    have hi : (i : ℕ) ≠ n + 1 := by omega
    classical
    simp [A, e, hU, Nat.xor_one_of_even hn, HilbertBasis.repr_self, lp.single_apply,
      Ne.symm hi]
  have he : e = 0 := by
    simpa [hAe] using (congrArg (fun S ↦ S e) (Ring.inverse_mul_cancel A hu)).symm
  simpa [e] using congrArg (fun v ↦ v (Fin.last n)) he

/-- Invertibility of an operator does not imply stability of its finite sections: there is a
unitary operator whose finite sections are not a stable sequence. -/
theorem exists_mem_unitary_not_isStableSequence_finiteSection (b : HilbertBasis ℕ 𝕜 H) :
    ∃ U ∈ unitary (H →L[𝕜] H), ¬IsStableSequence (U.finiteSection b) := by
  obtain ⟨U, hU, -, hsing⟩ := b.exists_mem_unitary_forall_even_not_isUnit_finiteSection
  refine ⟨U, hU, fun h ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h.eventually_isUnit
  exact hsing (2 * N) (even_two_mul N) (hN _ (by omega))

end HilbertBasis
