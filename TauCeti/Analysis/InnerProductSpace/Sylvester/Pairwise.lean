/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester.Basic
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Fourier.HaagerupZsido.Fourier
import TauCeti.Analysis.Fourier.HaagerupZsido.Mass
import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily

/-!
# The pairwise Sylvester bound in operator norm, in every dimension

Let `A` and `B` be bounded self-adjoint operators on complex Hilbert spaces `E` and `F`, of any
dimension, and suppose that every point of the spectrum of `A` is at distance at least `δ` from
every point of the spectrum of `B`. No ordering or interval structure of the two spectra is
assumed. This file proves the theorem of Bhatia, Davis and McIntosh that every solution of the
Sylvester equation `A X - X B = C` satisfies

`δ ‖X‖ ≤ (π / 2) ‖C‖`.

In finite dimension, and for every unitarily invariant norm, this is
`TauCeti.UnitarilyInvariantSeminorm.mul_map_le_pi_div_two_mul_map_sylvester_apply`.

## The finite-spectrum case

The constant is the mass `∫ |r| = π / 2` of the real Haagerup–Zsidó kernel `r`, which inverts
the variable outside the unit interval: `∫ r(t) sin (a t / δ) dt = δ / a` for `|a| ≥ δ`
(`TauCeti.HaagerupZsido.integral_realKernel_mul_sin_mul_div`), so finite combinations of the
reciprocals `(αᵢ - βⱼ)⁻¹` are kernel integrals of sines
(`TauCeti.HaagerupZsido.sum_sum_inv_sub_mul_eq_inv_mul_integral_realKernel_mul`). For pairwise
orthogonal finite families `(uᵢ)` and `(vⱼ)` and real numbers with `|αᵢ - βⱼ| ≥ δ`, expanding
`sin (a - b) = sin a cos b - cos a sin b` and using `sin² + cos² = 1` gives the Hilbert-type
inequality

`δ ‖∑ᵢ ∑ⱼ (αᵢ - βⱼ)⁻¹ ⟪uᵢ, C vⱼ⟫‖ ≤ (π / 2) ‖C‖ ‖∑ᵢ uᵢ‖ ‖∑ⱼ vⱼ‖`

(`ContinuousLinearMap.mul_norm_sum_sum_inv_sub_mul_inner_le`). If `A = ∑ᵢ αᵢ Pᵢ` and
`B = ∑ⱼ βⱼ Qⱼ` are finite combinations of mutually orthogonal projections summing to the
identity, the coefficients of `X` are `⟪Pᵢ x, X Qⱼ y⟫ = (αᵢ - βⱼ)⁻¹ ⟪Pᵢ x, C Qⱼ y⟫`, so this
inequality with `uᵢ = Pᵢ x` and `vⱼ = Qⱼ y` bounds `⟪x, X y⟫`. This step works over `ℝ` or `ℂ`
and needs neither completeness nor finite dimension.

## Approximation

A self-adjoint operator `A` is the norm limit of finite sums `∑ c • P(B_c)` of its spectral
projections with each `c` in the spectrum of `A`
(`ContinuousLinearMap.exists_seq_tendsto_borelCalculus_ofSimpleFunc`). These approximants have
their spectra inside those of `A` and `B`, so they stay separated by `δ`, and the bound passes to
the limit.

## Main statements

* `ContinuousLinearMap.mul_norm_sum_sum_inv_sub_mul_inner_le`: the Hilbert-type inequality with
  constant `π / 2`.
* `ContinuousLinearMap.mul_norm_le_pi_div_two_mul_norm_sum_smul_sylvester_sum_smul_apply`: the
  pairwise Sylvester bound for finite combinations of orthogonal projections.
* `ContinuousLinearMap.mul_norm_le_pi_div_two_mul_norm_sylvester_apply`: the pairwise Sylvester
  bound `δ ‖X‖ ≤ (π / 2) ‖A X - X B‖` for bounded self-adjoint operators.

## References

* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
-/

public section

open MeasureTheory Finset Filter Topology TauCeti TauCeti.HaagerupZsido
open scoped InnerProductSpace Real

namespace ContinuousLinearMap

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι κ : Type*} {s : Finset ι} {t : Finset κ}

/-- Rotating each vector of a pairwise orthogonal family by an angle splits its squared norm
between the sine and cosine sums: `‖∑ sin aᵢ • uᵢ‖² + ‖∑ cos aᵢ • uᵢ‖² = ‖∑ uᵢ‖²`. -/
private theorem norm_sum_sin_smul_sq_add_norm_sum_cos_smul_sq {u : ι → E}
    (hu : (s : Set ι).Pairwise fun i j ↦ ⟪u i, u j⟫_𝕜 = 0) (a : ι → ℝ) :
    ‖∑ i ∈ s, (Real.sin (a i) : 𝕜) • u i‖ ^ 2 + ‖∑ i ∈ s, (Real.cos (a i) : 𝕜) • u i‖ ^ 2 =
      ‖∑ i ∈ s, u i‖ ^ 2 := by
  have h (c : ι → ℝ) : (s : Set ι).Pairwise fun i j ↦ ⟪(c i : 𝕜) • u i, (c j : 𝕜) • u j⟫_𝕜 = 0 :=
    fun i hi j hj hij ↦ by simp [inner_smul_left, inner_smul_right, hu hi hj hij]
  rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero (h _),
    TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero (h _),
    TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero hu, ← sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal, mul_pow, mul_pow, sq_abs,
    sq_abs, ← add_mul, Real.sin_sq_add_cos_sq, one_mul]

/-- The phase-twisted coefficient sum `∑ᵢ ∑ⱼ sin (aᵢ - bⱼ) ⟪uᵢ, C vⱼ⟫` of pairwise orthogonal
families is bounded by `‖C‖ ‖∑ uᵢ‖ ‖∑ vⱼ‖`, since `sin² + cos² = 1`. -/
private theorem norm_sum_sum_sin_sub_mul_inner_le {u : ι → E} {v : κ → F}
    (hu : (s : Set ι).Pairwise fun i j ↦ ⟪u i, u j⟫_𝕜 = 0)
    (hv : (t : Set κ).Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) (a : ι → ℝ) (b : κ → ℝ)
    (C : F →L[𝕜] E) :
    ‖∑ i ∈ s, ∑ j ∈ t, (Real.sin (a i - b j) : 𝕜) * ⟪u i, C (v j)⟫_𝕜‖ ≤
      ‖C‖ * (‖∑ i ∈ s, u i‖ * ‖∑ j ∈ t, v j‖) := by
  set p := ∑ i ∈ s, (Real.sin (a i) : 𝕜) • u i
  set q := ∑ i ∈ s, (Real.cos (a i) : 𝕜) • u i
  set p' := ∑ j ∈ t, (Real.cos (b j) : 𝕜) • v j
  set q' := ∑ j ∈ t, (Real.sin (b j) : 𝕜) • v j
  -- Expand `sin (aᵢ - bⱼ) = sin aᵢ cos bⱼ - cos aᵢ sin bⱼ`.
  have hexp : ∑ i ∈ s, ∑ j ∈ t, (Real.sin (a i - b j) : 𝕜) * ⟪u i, C (v j)⟫_𝕜 =
      ⟪p, C p'⟫_𝕜 - ⟪q, C q'⟫_𝕜 := by
    rw [Finset.sum_comm]
    simp only [p, q, p', q', map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal, mul_sum, ← sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Real.sin_sub]
    push_cast
    ring
  have hu' := norm_sum_sin_smul_sq_add_norm_sum_cos_smul_sq hu a
  have hv' := norm_sum_sin_smul_sq_add_norm_sum_cos_smul_sq hv b
  have hinner (x : E) (y : F) : ‖⟪x, C y⟫_𝕜‖ ≤ ‖C‖ * (‖x‖ * ‖y‖) :=
    (norm_inner_le_norm _ _).trans <| by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
  -- Cauchy–Schwarz for the pairs `(‖p‖, ‖q‖)` and `(‖p'‖, ‖q'‖)`.
  have hcs : ‖p‖ * ‖p'‖ + ‖q‖ * ‖q'‖ ≤ ‖∑ i ∈ s, u i‖ * ‖∑ j ∈ t, v j‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, ← hu', ← hv']
    nlinarith [sq_nonneg (‖p‖ * ‖q'‖ - ‖q‖ * ‖p'‖)]
  rw [hexp]
  calc ‖⟪p, C p'⟫_𝕜 - ⟪q, C q'⟫_𝕜‖ ≤ ‖C‖ * (‖p‖ * ‖p'‖) + ‖C‖ * (‖q‖ * ‖q'‖) :=
        (norm_sub_le _ _).trans (add_le_add (hinner _ _) (hinner _ _))
    _ = ‖C‖ * (‖p‖ * ‖p'‖ + ‖q‖ * ‖q'‖) := by ring
    _ ≤ ‖C‖ * (‖∑ i ∈ s, u i‖ * ‖∑ j ∈ t, v j‖) := by gcongr

/-- **A Hilbert-type inequality with constant `π / 2`.** Let `(uᵢ)` and `(vⱼ)` be finite
pairwise orthogonal families, and let the real numbers `αᵢ` and `βⱼ` satisfy `|αᵢ - βⱼ| ≥ δ`.
Then for every bounded operator `C`,

`δ ‖∑ᵢ ∑ⱼ (αᵢ - βⱼ)⁻¹ ⟪uᵢ, C vⱼ⟫‖ ≤ (π / 2) ‖C‖ ‖∑ᵢ uᵢ‖ ‖∑ⱼ vⱼ‖`.

The coefficients `⟪uᵢ, C vⱼ⟫ / (αᵢ - βⱼ)` are those of the solution of a Sylvester equation
`A X - X B = C` in which `A` acts on `uᵢ` by `αᵢ` and `B` acts on `vⱼ` by `βⱼ`. -/
theorem mul_norm_sum_sum_inv_sub_mul_inner_le {u : ι → E} {v : κ → F}
    (hu : (s : Set ι).Pairwise fun i j ↦ ⟪u i, u j⟫_𝕜 = 0)
    (hv : (t : Set κ).Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) {α : ι → ℝ} {β : κ → ℝ} {δ : ℝ}
    (h : ∀ i ∈ s, ∀ j ∈ t, δ ≤ |α i - β j|) (C : F →L[𝕜] E) :
    δ * ‖∑ i ∈ s, ∑ j ∈ t, ((α i - β j)⁻¹ : ℝ) * ⟪u i, C (v j)⟫_𝕜‖ ≤
      π / 2 * (‖C‖ * (‖∑ i ∈ s, u i‖ * ‖∑ j ∈ t, v j‖)) := by
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (norm_nonneg _)).trans (by positivity)
  set K := ‖C‖ * (‖∑ i ∈ s, u i‖ * ‖∑ j ∈ t, v j‖)
  -- Each reciprocal is `δ⁻¹` times a kernel integral of a sine.
  rw [sum_sum_inv_sub_mul_eq_inv_mul_integral_realKernel_mul hδ h, norm_mul, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hδ, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  calc _ ≤ ∫ τ, |realKernel τ| * K :=
        norm_integral_le_of_norm_le (integrable_realKernel.abs.mul_const _)
          (.of_forall fun τ ↦ by
            rw [norm_mul, RCLike.norm_ofReal]
            simp only [sub_mul]
            exact mul_le_mul_of_nonneg_left
              (norm_sum_sum_sin_sub_mul_inner_le hu hv _ _ C) (abs_nonneg _))
    _ = π / 2 * K := by rw [integral_mul_const, integral_abs_realKernel]

/-- **The pairwise Sylvester bound for finite spectral decompositions.** Let
`A = ∑ᵢ αᵢ Pᵢ` and `B = ∑ⱼ βⱼ Qⱼ` be finite real combinations of symmetric operators `Pᵢ` and `Qⱼ`
with pairwise zero products, each family summing to the identity, so that `Pᵢ` and `Qⱼ` are
orthogonal projections onto mutually orthogonal subspaces. If `|αᵢ - βⱼ| ≥ δ` for all `i` and
`j`, then every `X` satisfies `δ ‖X‖ ≤ (π / 2) ‖A X - X B‖`. The spaces need not be complete or
finite-dimensional. -/
theorem mul_norm_le_pi_div_two_mul_norm_sum_smul_sylvester_sum_smul_apply {P : ι → E →L[𝕜] E}
    {Q : κ → F →L[𝕜] F} (hP : ∀ i ∈ s, (P i : E →ₗ[𝕜] E).IsSymmetric)
    (hQ : ∀ j ∈ t, (Q j : F →ₗ[𝕜] F).IsSymmetric)
    (hPP : (s : Set ι).Pairwise fun i j ↦ P i * P j = 0)
    (hQQ : (t : Set κ).Pairwise fun i j ↦ Q i * Q j = 0) (hP1 : ∑ i ∈ s, P i = 1)
    (hQ1 : ∑ j ∈ t, Q j = 1) {α : ι → ℝ} {β : κ → ℝ} {δ : ℝ}
    (h : ∀ i ∈ s, ∀ j ∈ t, δ ≤ |α i - β j|) (X : F →L[𝕜] E) :
    δ * ‖X‖ ≤ π / 2 *
      ‖(∑ i ∈ s, (α i : 𝕜) • P i).sylvester (∑ j ∈ t, (β j : 𝕜) • Q j) X‖ := by
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (norm_nonneg _)).trans (by positivity)
  set A := ∑ i ∈ s, (α i : 𝕜) • P i
  set B := ∑ j ∈ t, (β j : 𝕜) • Q j
  set C := A.sylvester B X
  have hsym (i) (hi : i ∈ s) (x z : E) : ⟪P i x, z⟫_𝕜 = ⟪x, P i z⟫_𝕜 := hP i hi x z
  have hsym' (j) (hj : j ∈ t) (y w : F) : ⟪Q j y, w⟫_𝕜 = ⟪y, Q j w⟫_𝕜 := hQ j hj y w
  -- In the two decompositions, `C = A X - X B` has the coefficients `(αᵢ - βⱼ) Pᵢ X Qⱼ`.
  have hcoef (x : E) (y : F) (i) (hi : i ∈ s) (j) (hj : j ∈ t) :
      ⟪P i x, C (Q j y)⟫_𝕜 = ((α i - β j : ℝ) : 𝕜) * ⟪P i x, X (Q j y)⟫_𝕜 := by
    have hA : ⟪P i x, A (X (Q j y))⟫_𝕜 = (α i : 𝕜) * ⟪P i x, X (Q j y)⟫_𝕜 := by
      rw [hsym i hi, ← mul_apply_eq_comp,
        mul_sum_smul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one hPP hP1 (fun k ↦ (α k : 𝕜)) hi,
        smul_apply, inner_smul_right, hsym i hi]
    have hB : ⟪P i x, X (B (Q j y))⟫_𝕜 = (β j : 𝕜) * ⟪P i x, X (Q j y)⟫_𝕜 := by
      rw [← mul_apply_eq_comp B,
        sum_smul_mul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one hQQ hQ1 (fun k ↦ (β k : 𝕜)) hj,
        smul_apply, map_smul, inner_smul_right]
    rw [show C = A ∘L X - X ∘L B from sylvester_apply A B X, sub_apply, comp_apply, comp_apply,
      inner_sub_right, hA, hB]
    push_cast
    ring
  -- The weak form of the bound, from the Hilbert-type inequality.
  have hweak (x : E) (y : F) : δ * ‖⟪x, X y⟫_𝕜‖ ≤ π / 2 * (‖C‖ * (‖x‖ * ‖y‖)) := by
    have hx : ∑ i ∈ s, P i x = x := by rw [← sum_apply, hP1, one_apply_eq_self]
    have hy : ∑ j ∈ t, Q j y = y := by rw [← sum_apply, hQ1, one_apply_eq_self]
    have hu : (s : Set ι).Pairwise fun i j ↦ ⟪P i x, P j x⟫_𝕜 = 0 := fun i hi j hj hij ↦ by
      beta_reduce
      rw [hsym i hi, ← mul_apply_eq_comp, hPP hi hj hij, zero_apply, inner_zero_right]
    have hv : (t : Set κ).Pairwise fun i j ↦ ⟪Q i y, Q j y⟫_𝕜 = 0 := fun i hi j hj hij ↦ by
      beta_reduce
      rw [hsym' i hi, ← mul_apply_eq_comp, hQQ hi hj hij, zero_apply, inner_zero_right]
    have hsum : ⟪x, X y⟫_𝕜 =
        ∑ i ∈ s, ∑ j ∈ t, ((α i - β j)⁻¹ : ℝ) * ⟪P i x, C (Q j y)⟫_𝕜 := by
      conv_lhs => rw [← hx, ← hy, map_sum, sum_inner]
      simp_rw [inner_sum]
      refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
      have hne : α i - β j ≠ 0 := abs_pos.mp (hδ.trans_le (h i hi j hj))
      rw [hcoef x y i hi j hj, ← mul_assoc, ← RCLike.ofReal_mul, inv_mul_cancel₀ hne,
        RCLike.ofReal_one, one_mul]
    have := mul_norm_sum_sum_inv_sub_mul_inner_le hu hv h C
    rwa [hx, hy, ← hsum] at this
  -- Pass to the operator norm by testing against unit vectors.
  rw [mul_comm, ← le_div_iff₀ hδ]
  refine opNorm_le_of_re_inner_le (by positivity) fun y x hy hx ↦ ?_
  have hxy := hweak x y
  rw [hx, hy, mul_one, mul_one, ← norm_inner_symm] at hxy
  rw [le_div_iff₀ hδ, mul_comm]
  exact (mul_le_mul_of_nonneg_left (RCLike.re_le_norm _) hδ.le).trans hxy

end RCLike

section SelfAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- If a simple function `s` on the spectrum of a self-adjoint operator `a` takes its values in
the spectrum, then `s(a)` is the real combination `∑ c • P(s ⁻¹' {c})` of the spectral projections
of its fibres. -/
private theorem borelCalculus_ofSimpleFunc_eq_sum_re_smul {a : E →L[ℂ] E} [IsStarNormal a]
    (ha : IsSelfAdjoint a) {s : SimpleFunc (spectrum ℂ a) ℂ} (hs : ∀ z, s z ∈ spectrum ℂ a) :
    a.borelCalculus (BoundedBorelFunction.ofSimpleFunc s) = ∑ c ∈ s.range,
      ((c.re : ℝ) : ℂ) • a.spectralPVM.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) := by
  rw [← integral_spectralPVM, ProjValMeasure.integral_ofSimpleFunc]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  obtain ⟨z, rfl⟩ := SimpleFunc.mem_range.mp hc
  exact congrArg (· • _) (ha.mem_spectrum_eq_re (hs z))

/-- The pairwise Sylvester bound for finite real combinations of the spectral projections of the
fibres of simple functions on the two spectra, with values in the spectra. -/
private theorem mul_norm_le_pi_div_two_mul_norm_borelCalculus_sylvester_borelCalculus_apply
    {a : E →L[ℂ] E} {b : F →L[ℂ] F} [IsStarNormal a] [IsStarNormal b] (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) {δ : ℝ} (h : ∀ z ∈ spectrum ℂ a, ∀ w ∈ spectrum ℂ b, δ ≤ ‖z - w‖)
    {s : SimpleFunc (spectrum ℂ a) ℂ} {t : SimpleFunc (spectrum ℂ b) ℂ}
    (hs : ∀ z, s z ∈ spectrum ℂ a) (ht : ∀ w, t w ∈ spectrum ℂ b) (X : F →L[ℂ] E) :
    δ * ‖X‖ ≤ π / 2 * ‖(a.borelCalculus (BoundedBorelFunction.ofSimpleFunc s)).sylvester
      (b.borelCalculus (BoundedBorelFunction.ofSimpleFunc t)) X‖ := by
  rw [borelCalculus_ofSimpleFunc_eq_sum_re_smul ha hs,
    borelCalculus_ofSimpleFunc_eq_sum_re_smul hb ht]
  refine mul_norm_le_pi_div_two_mul_norm_sum_smul_sylvester_sum_smul_apply
    (fun c _ ↦ (a.spectralPVM.isSelfAdjoint_proj _ _).isSymmetric)
    (fun d _ ↦ (b.spectralPVM.isSelfAdjoint_proj _ _).isSymmetric)
    (fun c _ c' _ hcc' ↦ a.spectralPVM.proj_mul_eq_zero_of_disjoint _ _
      ((Set.disjoint_singleton.mpr hcc').preimage s))
    (fun d _ d' _ hdd' ↦ b.spectralPVM.proj_mul_eq_zero_of_disjoint _ _
      ((Set.disjoint_singleton.mpr hdd').preimage t))
    (a.spectralPVM.sum_proj_preimage_singleton s) (b.spectralPVM.sum_proj_preimage_singleton t)
    (fun c hc d hd ↦ ?_) X
  obtain ⟨z, rfl⟩ := SimpleFunc.mem_range.mp hc
  obtain ⟨w, rfl⟩ := SimpleFunc.mem_range.mp hd
  have hδ := h _ (hs z) _ (ht w)
  rwa [ha.mem_spectrum_eq_re (hs z), hb.mem_spectrum_eq_re (ht w), ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hδ

/-- **The pairwise Sylvester bound** of Bhatia, Davis and McIntosh. Let `A` and `B` be bounded
self-adjoint operators on complex Hilbert spaces of any dimension. If every point of the spectrum
of `A` is at distance at least `δ` from every point of the spectrum of `B`, then
`δ ‖X‖ ≤ (π / 2) ‖A X - X B‖` for every bounded `X`. In particular every solution of the Sylvester
equation `A X - X B = C` satisfies `δ ‖X‖ ≤ (π / 2) ‖C‖`. -/
theorem mul_norm_le_pi_div_two_mul_norm_sylvester_apply {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {δ : ℝ}
    (h : ∀ z ∈ spectrum ℂ A, ∀ w ∈ spectrum ℂ B, δ ≤ ‖z - w‖) (X : F →L[ℂ] E) :
    δ * ‖X‖ ≤ π / 2 * ‖A.sylvester B X‖ := by
  have := hA.isStarNormal
  have := hB.isStarNormal
  -- Approximate `A` and `B` by finite spectral sums with values in their spectra.
  obtain ⟨s, hs, hsA⟩ := A.exists_seq_tendsto_borelCalculus_ofSimpleFunc
  obtain ⟨t, ht, htB⟩ := B.exists_seq_tendsto_borelCalculus_ofSimpleFunc
  have hlim : Tendsto (fun n ↦ (A.borelCalculus (BoundedBorelFunction.ofSimpleFunc (s n))).sylvester
      (B.borelCalculus (BoundedBorelFunction.ofSimpleFunc (t n))) X) atTop
      (𝓝 (A.sylvester B X)) := by
    simp only [sylvester_apply]
    exact (((compL ℂ F E E).flip X).continuous.tendsto A |>.comp hsA).sub
      ((compL ℂ F F E X).continuous.tendsto B |>.comp htB)
  exact ge_of_tendsto' ((hlim.norm).const_mul _) fun n ↦
    mul_norm_le_pi_div_two_mul_norm_borelCalculus_sylvester_borelCalculus_apply hA hB h
      (hs n) (ht n) X

end SelfAdjoint

end ContinuousLinearMap
