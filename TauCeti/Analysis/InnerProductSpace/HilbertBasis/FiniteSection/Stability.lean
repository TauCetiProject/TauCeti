/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Corner
public import TauCeti.Analysis.InnerProductSpace.StableSequence
public import TauCeti.Analysis.Normed.Lp.StableSequence
import Mathlib.Data.Nat.Bitwise
import TauCeti.Algebra.GroupWithZero.Action.Units
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Stability of the finite-section method

Let `T` be a bounded operator on a Hilbert space with a Hilbert basis `b` indexed by `ℕ`, and let
`Aₙ = T.finiteSection b n` be its compression to the first `n + 1` coordinates. The finite-section
method approximates the solution of `T x = y` by the solutions `xₙ` of the finite linear systems
`Aₙ xₙ = Pₙ y`, where `Pₙ` keeps the first `n + 1` coordinates. The method applies when the
sequence `Aₙ` is *stable* in the sense of `TauCeti.IsStableSequence`.

This file proves the basic theory of this situation.

* Bundled as `T.finiteSectionLp b` in the `ℓ^∞` product of finite Euclidean operator algebras, the
  finite sections are stable if and only if their class modulo the `c₀` ideal `lp.c0Ideal` is a
  unit, with quotient inverse norm `limsup ‖Aₙ⁻¹‖`.
* Uniform lower bounds of the finite sections pass to `T`, and so do those of the adjoint
  sections. Hence stability of the finite sections forces `T` to be invertible, with
  `‖T⁻¹‖` bounded by any eventual bound for `‖Aₙ⁻¹‖`.
* Under stability, the zero-extended finite inverses `Bₙ = T.finiteInverseExtension b n` converge
  strongly to `T⁻¹`, and their adjoints `Bₙ†` converge strongly to `(T⁻¹)†` (though not in operator
  norm, as `Bₙ = Pₙ` for `T = 1` satisfies `‖Bₙ - 1‖ = 1`).
* When `‖Aₙ⁻¹‖ ≤ M`, the exact-RHS error is quasi-optimal, `‖xₙ - x‖ ≤ (1 + M ‖T‖) ‖x - Pₙ x‖`,
  and perturbed finite right-hand sides `yₙ` add at most `M ‖Jₙ yₙ - Pₙ (T x)‖`.
* Invertibility of `T` alone does not give stability: the unitary exchanging the basis vectors
  `b (2k)` and `b (2k + 1)` has singular finite sections of every odd size.

Since `‖Aₙ‖ ≤ ‖T‖`, stability also bounds the condition numbers of the finite sections uniformly,
by `TauCeti.IsStableSequence.exists_conditionNumber_le`.

## Main definitions and results

* `ContinuousLinearMap.finiteInverseExtension`: zero extension `Jₙ Aₙ⁻¹ Jₙ†` of the totalized
  finite-section inverse, always of finite rank and commuting with `adjoint`.
* `ContinuousLinearMap.isUnit_mk_c0Ideal_finiteSectionLp_iff`: stability of `T.finiteSection b` is
  equivalent to invertibility of `T.finiteSectionLp b` modulo `lp.c0Ideal`.
* `ContinuousLinearMap.norm_le_mul_norm_apply_of_finiteSection`: an eventual uniform lower bound
  for the finite sections is a lower bound for `T`.
* `ContinuousLinearMap.isUnit_and_norm_ringInverse_le_of_finiteSection`: eventually invertible
  finite sections with `‖Aₙ⁻¹‖ ≤ M` make `T` invertible with `‖T⁻¹‖ ≤ M`.
* `ContinuousLinearMap.norm_finiteSection_solution_sub_le` and
  `ContinuousLinearMap.norm_finiteSection_solution_sub_le_of_rhs`: quasi-optimal error bounds for
  exact and perturbed finite right-hand sides.
* `ContinuousLinearMap.tendsto_finiteInverseExtension` and
  `ContinuousLinearMap.tendsto_adjoint_finiteInverseExtension`: strong convergence of `Bₙ` to `T⁻¹`
  and of `Bₙ†` to `(T⁻¹)†` under stability.
* `HilbertBasis.exists_mem_unitary_not_isStableSequence_finiteSection`: a unitary operator whose
  finite sections are not stable.

## References

* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Sections 1 and 7.
* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Sections 1.4 and 2.1.
* R. Hagen, S. Roch and B. Silbermann, *C*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter Topology TauCeti
open scoped ENNReal

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
    norm_le_mul_norm_apply_of_finiteSection (hS.mono fun _ ⟨hu, hn⟩ y ↦ by
      have hy := (isInvertible_iff_isUnit.mpr hu).norm_le_norm_inverse_mul_norm y
      rw [← ringInverse_eq_inverse] at hy
      exact hy.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) x
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

/-- Quantitative error estimate for perturbed finite right-hand sides: if `Aₙ` is invertible
with `‖Aₙ⁻¹‖ ≤ M`, then solving `Aₙ xₙ = y` instead of `Aₙ xₙ = Qₙ (T x)` adds at most
`M * ‖Jₙ y - Pₙ (T x)‖` to the quasi-optimal projection error. -/
theorem norm_finiteSection_solution_sub_le_of_rhs {M : ℝ} {n : ℕ}
    (hu : IsUnit (T.finiteSection b n)) (hn : ‖Ring.inverse (T.finiteSection b n)‖ ≤ M)
    (x : H) (y : EuclideanSpace 𝕜 (Fin (n + 1))) :
    ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x‖ ≤
      (1 + M * ‖T‖) * ‖x - b.finiteProjection n x‖ +
        M * ‖b.finiteInclusion n y - b.finiteProjection n (T x)‖ := by
  set x₀ := b.finiteInclusion n (Ring.inverse (T.finiteSection b n) (b.coordinateCutoff n (T x)))
  have hrhs :
      ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x₀‖ ≤
        M * ‖b.finiteInclusion n y - b.finiteProjection n (T x)‖ := by
    calc
      ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x₀‖ =
          ‖Ring.inverse (T.finiteSection b n) (y - b.coordinateCutoff n (T x))‖ := by
        rw [← map_sub (b.finiteInclusion n), ← map_sub, LinearIsometry.norm_map]
      _ ≤ M * ‖y - b.coordinateCutoff n (T x)‖ :=
        (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
      _ = M * ‖b.finiteInclusion n y - b.finiteProjection n (T x)‖ := by
        rw [← (b.finiteInclusion n).norm_map, map_sub,
          HilbertBasis.finiteInclusion_coordinateCutoff]
  calc
    ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x‖ =
        ‖(x₀ - x) + (b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x₀)‖ := by
      congr 1
      abel
    _ ≤ ‖x₀ - x‖ + ‖b.finiteInclusion n (Ring.inverse (T.finiteSection b n) y) - x₀‖ :=
      norm_add_le _ _
    _ ≤ (1 + M * ‖T‖) * ‖x - b.finiteProjection n x‖ +
          M * ‖b.finiteInclusion n y - b.finiteProjection n (T x)‖ :=
      add_le_add (norm_finiteSection_solution_sub_le hu hn x) hrhs

/-- Convergence of the finite-section method for approximated right-hand sides: if the finite
sections of `T` are stable and the included right-hand sides `b.finiteInclusion n (y n)` converge
to `z`, then the included solutions `b.finiteInclusion n (Aₙ⁻¹ (y n))` converge to
`Ring.inverse T z`. -/
theorem tendsto_finiteSection_solution_of_tendsto (h : IsStableSequence (T.finiteSection b))
    {y : ∀ n, EuclideanSpace 𝕜 (Fin (n + 1))} {z : H}
    (hy : Tendsto (fun n ↦ b.finiteInclusion n (y n)) atTop (𝓝 z)) :
    Tendsto (fun n ↦ b.finiteInclusion n (Ring.inverse (T.finiteSection b n) (y n))) atTop
      (𝓝 (Ring.inverse T z)) := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp h
  set x := Ring.inverse T z
  have hTx : T x = z := apply_ringInverse_apply (isUnit_of_isStableSequence_finiteSection h) z
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hP : Tendsto (fun n ↦ (1 + M * ‖T‖) * ‖x - b.finiteProjection n x‖) atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp (b.tendsto_finiteProjection x)).congr
      fun n ↦ norm_sub_rev _ _).const_mul (1 + M * ‖T‖)
  have hR : Tendsto (fun n ↦ M * ‖b.finiteInclusion n (y n) - b.finiteProjection n z‖) atTop
      (𝓝 0) := by
    simpa [sub_self] using (hy.sub (b.tendsto_finiteProjection z)).norm.const_mul M
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (hM.mono fun n ⟨hu, hn⟩ ↦ ?_) (by simpa using hP.add hR)
  simpa only [hTx] using norm_finiteSection_solution_sub_le_of_rhs hu hn x (y n)

/-- The finite sections of `T†` are stable if and only if those of `T` are. -/
@[simp]
theorem isStableSequence_finiteSection_adjoint_iff (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    IsStableSequence (T.adjoint.finiteSection b) ↔ IsStableSequence (T.finiteSection b) :=
  (isStableSequence_congr (Eventually.of_forall fun n ↦
    (T.adjoint_finiteSection b n).symm)).trans isStableSequence_adjoint_iff

/-- Stability of finite sections in a transported Hilbert basis is equivalent to stability of
the finite sections of the conjugated operator in the original basis. -/
@[simp]
theorem isStableSequence_finiteSection_mapₗᵢ_iff {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace 𝕜 H'] [CompleteSpace H'] (S : H' →L[𝕜] H') (b : HilbertBasis ℕ 𝕜 H)
    (e : H ≃ₗᵢ[𝕜] H') :
    IsStableSequence (S.finiteSection (b.mapₗᵢ e)) ↔
      IsStableSequence (((e.symm : H' →L[𝕜] H) ∘L S ∘L (e : H →L[𝕜] H')).finiteSection b) :=
  isStableSequence_congr (Eventually.of_forall (S.finiteSection_mapₗᵢ b e))

/-- **Quotient characterization of finite-section stability.** The bundled sequence
`T.finiteSectionLp b` is invertible modulo `lp.c0Ideal` if and only if `T.finiteSection b` is a
stable sequence. -/
theorem isUnit_mk_c0Ideal_finiteSectionLp_iff (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    IsUnit
      (TwoSidedIdeal.Quotient.mk
        (lp.c0Ideal fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
        (T.finiteSectionLp b)) ↔
      IsStableSequence (T.finiteSection b) := by
  rw [lp.isUnit_mk_c0Ideal_iff_isStableSequence, coeFn_finiteSectionLp]

/-- When the finite sections of `T` are stable, the quotient norm of the inverse of
`T.finiteSectionLp b` modulo `lp.c0Ideal` is the asymptotic supremum of the finite-section inverse
norms. -/
theorem norm_ringInverse_mk_c0Ideal_finiteSectionLp (h : IsStableSequence (T.finiteSection b)) :
    ‖Ring.inverse
        (TwoSidedIdeal.Quotient.mk
          (lp.c0Ideal fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
          (T.finiteSectionLp b))‖ =
      limsup (fun n ↦ ‖Ring.inverse (T.finiteSection b n)‖) atTop := by
  rw [lp.norm_ringInverse_mk_c0Ideal ((isUnit_mk_c0Ideal_finiteSectionLp_iff T b).mpr h),
    Nat.cofinite_eq_atTop]
  simp only [finiteSectionLp_apply]

/-- Extend the (totalized) inverse of the `n`-th finite section of `T` by zero outside the first
`n + 1` coordinates of `b`. On the invertible tail this is the inverse of the finite section on
its orthogonal corner. -/
noncomputable def finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    H →L[𝕜] H :=
  (b.finiteInclusion n).cornerEmbedding (Ring.inverse (T.finiteSection b n))

/-- `ContinuousLinearMap.finiteInverseExtension` is the corner embedding of the totalized inverse
of `T.finiteSection b n`. -/
theorem finiteInverseExtension_def (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.finiteInverseExtension b n =
      (b.finiteInclusion n).cornerEmbedding (Ring.inverse (T.finiteSection b n)) :=
  (rfl)

/-- Evaluating `T.finiteInverseExtension b n` restricts to the first `n + 1` coordinates, applies
`Ring.inverse (T.finiteSection b n)`, and includes the result back into `H`. -/
@[simp]
theorem finiteInverseExtension_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    T.finiteInverseExtension b n x =
      b.finiteInclusion n (Ring.inverse (T.finiteSection b n) (b.coordinateCutoff n x)) := by
  simp only [finiteInverseExtension, LinearIsometry.cornerEmbedding_apply_apply,
    HilbertBasis.adjoint_finiteInclusion]

/-- `T.finiteInverseExtension b n` factors as coordinate restriction, finite-section inversion, and
coordinate inclusion. -/
theorem finiteInverseExtension_eq_comp (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.finiteInverseExtension b n =
      (b.finiteInclusion n).toContinuousLinearMap ∘L
        Ring.inverse (T.finiteSection b n) ∘L b.coordinateCutoff n := by
  ext x
  simp

/-- The operator norm of `T.finiteInverseExtension b n` equals the operator norm of
`Ring.inverse (T.finiteSection b n)`. -/
@[simp]
theorem norm_finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖T.finiteInverseExtension b n‖ = ‖Ring.inverse (T.finiteSection b n)‖ :=
  (b.finiteInclusion n).cornerEmbedding.norm_map _

/-- Zero-extended finite-section inversion commutes with the Hilbert adjoint. -/
@[simp]
theorem adjoint_finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.finiteInverseExtension b n).adjoint = T.adjoint.finiteInverseExtension b n := by
  rw [finiteInverseExtension, LinearIsometry.adjoint_cornerEmbedding, ← ringInverse_adjoint,
    adjoint_finiteSection, finiteInverseExtension]

/-- Zero-extended finite-section inversion commutes with `star`. -/
@[simp]
theorem finiteInverseExtension_star (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (star T).finiteInverseExtension b n = star (T.finiteInverseExtension b n) := by
  simp only [star_eq_adjoint, adjoint_finiteInverseExtension]

/-- Compressing `T.finiteInverseExtension b n` back to the first `n + 1` coordinates recovers
`Ring.inverse (T.finiteSection b n)`. -/
@[simp]
theorem finiteSection_finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.finiteInverseExtension b n).finiteSection b n = Ring.inverse (T.finiteSection b n) :=
  b.finiteSection_cornerEmbedding n _

/-- `T.finiteInverseExtension b n` takes values in the range of `b.finiteProjection n`. -/
@[simp]
theorem finiteProjection_comp_finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H)
    (n : ℕ) :
    b.finiteProjection n ∘L T.finiteInverseExtension b n = T.finiteInverseExtension b n := by
  rw [← b.cornerEmbedding_finiteInclusion_id n, finiteInverseExtension,
    ← LinearIsometry.cornerEmbedding_comp, ContinuousLinearMap.id_comp]

/-- `T.finiteInverseExtension b n` vanishes on the orthogonal complement of the first `n + 1`
coordinates. -/
@[simp]
theorem finiteInverseExtension_comp_finiteProjection (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H)
    (n : ℕ) :
    T.finiteInverseExtension b n ∘L b.finiteProjection n = T.finiteInverseExtension b n := by
  rw [← b.cornerEmbedding_finiteInclusion_id n, finiteInverseExtension,
    ← LinearIsometry.cornerEmbedding_comp, ContinuousLinearMap.comp_id]

/-- When `T.finiteSection b n` is invertible, `T.finiteInverseExtension b n` is a right inverse of
`T.zeroExtendedFiniteSection b n` on the finite-coordinate corner. -/
@[simp]
theorem zeroExtendedFiniteSection_comp_finiteInverseExtension {n : ℕ}
    (hu : IsUnit (T.finiteSection b n)) :
    T.zeroExtendedFiniteSection b n ∘L T.finiteInverseExtension b n = b.finiteProjection n := by
  ext x
  simp [zeroExtendedFiniteSection_apply, apply_ringInverse_apply hu]

/-- When `T.finiteSection b n` is invertible, `T.finiteInverseExtension b n` is a left inverse of
`T.zeroExtendedFiniteSection b n` on the finite-coordinate corner. -/
@[simp]
theorem finiteInverseExtension_comp_zeroExtendedFiniteSection {n : ℕ}
    (hu : IsUnit (T.finiteSection b n)) :
    T.finiteInverseExtension b n ∘L T.zeroExtendedFiniteSection b n = b.finiteProjection n := by
  ext x
  simp [zeroExtendedFiniteSection_apply, ringInverse_apply_apply hu]

/-- The zero operator has zero extended finite-section inverse. -/
@[simp]
theorem finiteInverseExtension_zero (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (0 : H →L[𝕜] H).finiteInverseExtension b n = 0 := by
  simp [finiteInverseExtension]

/-- The unit operator has `b.finiteProjection n` as its extended finite-section inverse. -/
@[simp]
theorem finiteInverseExtension_one (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (1 : H →L[𝕜] H).finiteInverseExtension b n = b.finiteProjection n := by
  simp [finiteInverseExtension]

/-- Scaling an operator by `c` scales its extended finite-section inverse by `c⁻¹`. -/
@[simp]
theorem finiteInverseExtension_smul (c : 𝕜) (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (c • T).finiteInverseExtension b n = c⁻¹ • T.finiteInverseExtension b n := by
  simp only [finiteInverseExtension, finiteSection_smul, ringInverse_smul, map_smul]

/-- Transporting a Hilbert basis across a linear isometric equivalence conjugates
`ContinuousLinearMap.finiteInverseExtension`. -/
@[simp]
theorem finiteInverseExtension_mapₗᵢ {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace 𝕜 H'] [CompleteSpace H'] (S : H' →L[𝕜] H') (b : HilbertBasis ℕ 𝕜 H)
    (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    S.finiteInverseExtension (b.mapₗᵢ e) n =
      (e : H →L[𝕜] H') ∘L
        ((e.symm : H' →L[𝕜] H) ∘L S ∘L (e : H →L[𝕜] H')).finiteInverseExtension b n ∘L
        (e.symm : H' →L[𝕜] H) := by
  ext y
  simp

/-- Every zero-extended finite-section inverse has finite rank. -/
theorem hasFiniteRange_finiteInverseExtension (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.finiteInverseExtension b n : H →ₗ[𝕜] H).HasFiniteRange := by
  refine b.hasFiniteRange_of_apply_eq_zero (T.finiteInverseExtension b n)
    (Finset.range (n + 1)) fun i hi ↦ ?_
  have hi' : ¬ i < n + 1 := by simpa [Finset.mem_range] using hi
  rw [← T.finiteInverseExtension_comp_finiteProjection b n, comp_apply,
    b.finiteProjection_basis n i]
  simp [hi']

/-- On an invertible finite section, the error between the finite-section approximation of `x` and
its coordinate projection `b.finiteProjection n x` is the extended finite inverse applied to the
tail residual `T (x - b.finiteProjection n x)`. -/
theorem finiteInverseExtension_apply_sub_finiteProjection {n : ℕ}
    (hu : IsUnit (T.finiteSection b n)) (x : H) :
    T.finiteInverseExtension b n (T x) - b.finiteProjection n x =
      T.finiteInverseExtension b n (T (x - b.finiteProjection n x)) := by
  have hproj : b.finiteProjection n x =
      T.finiteInverseExtension b n (T (b.finiteProjection n x)) := by
    calc
      b.finiteProjection n x =
          (T.finiteInverseExtension b n ∘L T.zeroExtendedFiniteSection b n) x := by
        rw [finiteInverseExtension_comp_zeroExtendedFiniteSection hu]
      _ = T.finiteInverseExtension b n (T (b.finiteProjection n x)) := by
        rw [zeroExtendedFiniteSection_eq, ← comp_assoc, ← comp_assoc,
          finiteInverseExtension_comp_finiteProjection, comp_apply, comp_apply]
  exact (congrArg (T.finiteInverseExtension b n (T x) - ·) hproj).trans
    (by rw [← map_sub, ← map_sub])

/-- Quasi-optimal error bound in terms of the right-hand side `y`: when `T` and its `n`-th finite
section are invertible with `‖Aₙ⁻¹‖ ≤ M`, the extended inverse approximation is within
`(1 + M * ‖T‖) * ‖T⁻¹ y - Pₙ (T⁻¹ y)‖` of `T⁻¹ y`. -/
theorem norm_finiteInverseExtension_sub_ringInverse_le {M : ℝ} {n : ℕ} (hT : IsUnit T)
    (hu : IsUnit (T.finiteSection b n)) (hn : ‖Ring.inverse (T.finiteSection b n)‖ ≤ M) (y : H) :
    ‖T.finiteInverseExtension b n y - Ring.inverse T y‖ ≤
      (1 + M * ‖T‖) * ‖Ring.inverse T y - b.finiteProjection n (Ring.inverse T y)‖ := by
  have hy : T (Ring.inverse T y) = y := apply_ringInverse_apply hT y
  simpa only [← finiteInverseExtension_apply, hy] using
    norm_finiteSection_solution_sub_le hu hn (Ring.inverse T y)

/-- Under finite-section stability, the zero-extended finite inverses converge strongly to
`Ring.inverse T`. -/
theorem tendsto_finiteInverseExtension (h : IsStableSequence (T.finiteSection b)) (y : H) :
    Tendsto (fun n ↦ T.finiteInverseExtension b n y) atTop (𝓝 (Ring.inverse T y)) := by
  simpa only [finiteInverseExtension_apply] using tendsto_finiteSection_solution_ringInverse h y

/-- Under finite-section stability, the adjoints of the zero-extended finite inverses converge
strongly to `(Ring.inverse T).adjoint`. -/
theorem tendsto_adjoint_finiteInverseExtension (h : IsStableSequence (T.finiteSection b))
    (y : H) :
    Tendsto (fun n ↦ (T.finiteInverseExtension b n).adjoint y) atTop
      (𝓝 ((Ring.inverse T).adjoint y)) := by
  simpa only [adjoint_finiteInverseExtension, ← ringInverse_adjoint] using
    tendsto_finiteInverseExtension ((isStableSequence_finiteSection_adjoint_iff T b).mpr h) y

/-- For the identity operator, `finiteInverseExtension` is at constant operator-norm distance `1`
from `1`, so strong inverse convergence cannot be upgraded to operator-norm convergence. -/
theorem norm_finiteInverseExtension_one_sub_one (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖(1 : H →L[𝕜] H).finiteInverseExtension b n - 1‖ = 1 := by
  rw [finiteInverseExtension_one, b.norm_finiteProjection_sub_one n]

/-- The zero-extended finite inverses of `1 : H →L[𝕜] H` do not converge to `1` in the operator
norm topology. -/
theorem not_tendsto_finiteInverseExtension_one (b : HilbertBasis ℕ 𝕜 H) :
    ¬Tendsto (fun n ↦ (1 : H →L[𝕜] H).finiteInverseExtension b n) atTop (𝓝 1) := by
  intro h
  have h0 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [norm_finiteInverseExtension_one_sub_one] using
      tendsto_iff_norm_sub_tendsto_zero.mp h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

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
