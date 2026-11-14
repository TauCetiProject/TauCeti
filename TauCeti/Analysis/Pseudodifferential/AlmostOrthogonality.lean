/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Lp
public import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Algebra.Order.BigOperators.Sum.Filter

/-!
# Almost orthogonality of the Littlewood–Paley pieces of a pseudodifferential operator

Let `a` be a symbol of order `m` whose estimates are uniform in the position, and let
`aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)` be its Littlewood–Paley pieces (`TauCeti.Symbol.littlewoodPaleyPiece`),
cut off to frequencies of size `2^j`. Each piece vanishes at large frequencies, so its quantization
`Op(aⱼ)` is an integral operator with an integrable kernel and is bounded on every `Lᵖ`. This file
proves the following facts about these operators, which are the input from the frequency side to
the Cotlar–Stein almost-orthogonality lemma (`TauCeti.exists_hasSum_apply_of_almost_orthogonal`)
for the `L²` boundedness of `Op(a)` when `m = 0` (the Calderón–Vaillancourt theorem).

* **Dyadic bounds.** `‖Op(aⱼ)‖_{Lᵖ → Lᵖ} ≤ C (2^j)^m`, so for `m = 0` the pieces are bounded
  uniformly in `j`.
* **Frequency orthogonality.** On `L²`, `Op(a) Op(b)† = 0` as soon as `a(x, ξ) b(z, ξ)† = 0` for
  all `x`, `z`, `ξ` (`TauCeti.Symbol.quantizeLp_comp_adjoint_eq_zero`). Since the cutoffs
  `ψⱼ` and `ψₖ` have disjoint supports when `|j - k|` is large, `Op(aⱼ) Op(aₖ)† = 0` for such
  `j`, `k`, and for `m ≤ 0` the sums `∑ₖ √‖Op(aⱼ) Op(aₖ)†‖` are bounded uniformly in `j`.
* **Reconstruction.** On a Schwartz function `u`, the partial sums `∑_{j < N} Op(aⱼ) u (x)`
  converge to `Op(a) u (x)`.

The other hypothesis of the Cotlar–Stein lemma, the decay of `‖Op(aⱼ)† Op(aₖ)‖`, is not treated
here: it depends on the regularity of `a` in the position rather than on frequency supports.

## Main results

* `TauCeti.Symbol.quantizeLittlewoodPaleyPiece`: the operator `Op(aⱼ)` on `Lᵖ`.
* `TauCeti.Symbol.IsUniform.exists_norm_quantizeLittlewoodPaleyPiece_le`: the dyadic bounds.
* `TauCeti.Symbol.IsUniform.exists_quantizeLittlewoodPaleyPiece_comp_adjoint_eq_zero` and
  `TauCeti.Symbol.IsUniform.exists_sum_sqrt_norm_quantizeLittlewoodPaleyPiece_comp_adjoint_le`:
  orthogonality of distant pieces, and the corresponding Cotlar–Stein bound.
* `TauCeti.Symbol.tendsto_sum_quantizeSchwartzValue_littlewoodPaleyPiece`: the pieces sum to
  `Op(a)` on Schwartz functions.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Princeton University Press, 1993, Chapter VII, §2.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

open MeasureTheory ContinuousLinearMap Real FourierTransform Filter Topology
open scoped RealInnerProductSpace ComplexConjugate NNReal ENNReal SchwartzMap

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-! ### The Littlewood–Paley pieces -/

variable (φ : ContDiffBump (0 : CoordinateSpace n)) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The `j`-th Littlewood–Paley piece, which vanishes at large frequencies, as a symbol of
order `-(n + 1)`. -/
private def smoothingPiece (a : Symbol n V W m) (j : ℕ) : Symbol n V W (-(n + 1)) :=
  ofBoundedFrequencySupport (a.littlewoodPaleyPiece φ j).coefficient
    (a.littlewoodPaleyPiece φ j).contDiff_coefficient (2 ^ j * φ.rOut)
    fun x _ hξ ↦ a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ

private theorem coefficient_smoothingPiece (a : Symbol n V W m) (j : ℕ) :
    (smoothingPiece φ a j).coefficient = (a.littlewoodPaleyPiece φ j).coefficient :=
  coefficient_ofBoundedFrequencySupport _ _ _ _

private theorem isUniform_smoothingPiece {a : Symbol n V W m} (ha : a.IsUniform) (j : ℕ) :
    (smoothingPiece φ a j).IsUniform :=
  (ha.littlewoodPaleyPiece φ j).ofBoundedFrequencySupport _ _

/-- The quantization `Op(aⱼ)` of the `j`-th Littlewood–Paley piece `aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)` of a
uniform symbol `a` (`TauCeti.Symbol.littlewoodPaleyPiece`), as a bounded operator on `Lᵖ`. Since
`aⱼ` vanishes at frequencies of norm at least `2^j φ.rOut`, it is a uniform symbol of order
`-(n + 1)`, so its kernel is integrable (`TauCeti.Symbol.quantizeLp`). -/
def quantizeLittlewoodPaleyPiece (a : Symbol n V W m) (ha : a.IsUniform) (j : ℕ) :
    Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ]
      Lp W p (volume : Measure (CoordinateSpace n)) :=
  (smoothingPiece φ a j).quantizeLp p (by linarith) (isUniform_smoothingPiece φ ha j)

/-- `Op(aⱼ)` is the quantization of the piece, viewed as a symbol of order `-(n + 1)`. -/
private theorem quantizeLittlewoodPaleyPiece_eq (a : Symbol n V W m) (ha : a.IsUniform) (j : ℕ) :
    a.quantizeLittlewoodPaleyPiece φ p ha j =
      (smoothingPiece φ a j).quantizeLp p (by linarith) (isUniform_smoothingPiece φ ha j) :=
  rfl

variable {φ p}

/-- The operator `Op(aⱼ)` acts by `u ↦ (x ↦ ∫ K_{aⱼ}(x, y) u(y) dy)`. -/
theorem coeFn_quantizeLittlewoodPaleyPiece {a : Symbol n V W m} (ha : a.IsUniform) (j : ℕ)
    (u : Lp V p (volume : Measure (CoordinateSpace n))) :
    a.quantizeLittlewoodPaleyPiece φ p ha j u =ᵐ[volume]
      fun x ↦ ∫ y, quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y (u y) := by
  simpa only [quantizeLittlewoodPaleyPiece_eq, coefficient_smoothingPiece] using
    coeFn_quantizeLp (a := smoothingPiece φ a j) u

/-- On Schwartz functions, `Op(aⱼ)` is the quantization of the piece `aⱼ`. -/
theorem coeFn_quantizeLittlewoodPaleyPiece_toLp [CompleteSpace V] [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) (j : ℕ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeLittlewoodPaleyPiece φ p ha j (u.toLp p) =ᵐ[volume]
      quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u := by
  simpa only [quantizeLittlewoodPaleyPiece_eq, coefficient_smoothingPiece] using
    coeFn_quantizeLp_toLp (a := smoothingPiece φ a j) (p := p) u

omit [Fact (1 ≤ p)] in
/-- **The pieces sum to the quantization.** For a Schwartz function `u` and every position `x`, the
partial sums `∑_{j < N} Op(aⱼ) u (x)` converge to `Op(a) u (x)`: by the telescoping of the
Littlewood–Paley partition they are `Op(φ(2^{1-N} ξ) a) u (x)`, and dominated convergence
applies. -/
theorem tendsto_sum_quantizeSchwartzValue_littlewoodPaleyPiece
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N,
      quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x) atTop
      (𝓝 (quantizeSchwartzValue a.coefficient u x)) := by
  set g : CoordinateSpace n → W := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  have hg : Integrable g := integrable_quantizeSchwartzValue_integrand
    (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x rfl) (𝓕 u)
  -- Multiplying `g` by a continuous function with values in `[-1, 1]` keeps it integrable.
  have hmul {ψ : CoordinateSpace n → ℝ} (hψ : Continuous ψ) (hψ₁ : ∀ ξ, |ψ ξ| ≤ 1) :
      Integrable fun ζ ↦ ψ ((2 * π) • ζ) • g ζ :=
    hg.norm.mono' ((hψ.comp (continuous_const_smul _)).aestronglyMeasurable.smul hg.1)
      (.of_forall fun ζ ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hψ₁ _))
  have hpiece (j : ℕ) : quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x =
      ∫ ζ, φ.inhomogeneousLittlewoodPaley j ((2 * π) • ζ) • g ζ := by
    simp only [quantizeSchwartzValue_def, coefficient_littlewoodPaleyPiece, g,
      smul_apply, smul_comm (𝐞 _)]
  have hsum (N : ℕ) : ∑ j ∈ Finset.range (N + 1),
      quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x =
        ∫ ζ, φ (((2 : ℝ) ^ N)⁻¹ • (2 * π) • ζ) • g ζ := by
    simp_rw [hpiece]
    rw [← integral_finsetSum (Finset.range (N + 1)) fun j _ ↦
      hmul (φ.contDiff_inhomogeneousLittlewoodPaley (n := 0) j).continuous
        (φ.abs_inhomogeneousLittlewoodPaley_le_one j)]
    simp_rw [← Finset.sum_smul, φ.sum_inhomogeneousLittlewoodPaley_range]
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  simp_rw [hsum]
  rw [quantizeSchwartzValue_def]
  refine tendsto_integral_of_dominated_convergence (fun ζ ↦ ‖g ζ‖)
    (fun N ↦ (hmul (φ.continuous.comp (continuous_const_smul _)) fun ξ ↦
      abs_le.2 ⟨(neg_nonpos.2 zero_le_one).trans φ.nonneg, φ.le_one⟩).1) hg.norm
    (fun N ↦ .of_forall fun ζ ↦ ?_) (.of_forall fun ζ ↦ ?_)
  · rw [norm_smul, Real.norm_of_nonneg φ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
  · -- `φ (2^{-N} ξ) → φ 0 = 1`.
    have h0 : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹ • (2 * π) • ζ) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).smul_const ((2 * π) • ζ)
      rwa [zero_smul] at h
    have h1 := ((φ.continuous.tendsto 0).comp h0).smul_const (g ζ)
    rwa [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_smul] at h1

variable (φ p) in
/-- **Dyadic `Lᵖ` bounds.** The quantizations of the Littlewood–Paley pieces of a uniform symbol
of order `m` satisfy `‖Op(aⱼ)‖ ≤ C (2^j)^m`. In particular, for a uniform symbol of order `0`,
they are bounded on `Lᵖ` uniformly in `j`. -/
theorem IsUniform.exists_norm_quantizeLittlewoodPaleyPiece_le {a : Symbol n V W m}
    (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ j, ‖a.quantizeLittlewoodPaleyPiece φ p ha j‖ ≤ C * ((2 : ℝ) ^ j) ^ m := by
  obtain ⟨C₀, hC₀, h₀⟩ := ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] []
  choose C₁ hC₁ h₁ using fun i : Fin n ↦
    ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] (List.replicate (n + 1) i)
  set C := C₀ + ∑ i, C₁ i
  have hC : 0 ≤ C := add_nonneg hC₀ (Finset.sum_nonneg fun i _ ↦ hC₁ i)
  set D := 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ *
    ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹
  have hD : 0 ≤ D := by
    have : 0 ≤ ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹ :=
      integral_nonneg fun w ↦ by positivity
    positivity
  refine ⟨D * C, mul_nonneg hD hC, fun j ↦ ?_⟩
  set t : ℝ := 2 ^ j
  have ht : 0 < t := by positivity
  -- The integrated dyadic estimates with `A = C t ^ (m + n)` and `R = t⁻¹`.
  have hA (x : CoordinateSpace n) :
      ∫ ξ, ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ ≤ C * t ^ (m + n) := by
    have h := h₀ j x
    simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hC₁ i)
  have hR (x : CoordinateSpace n) (i : Fin n) :
      ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) i) (a.littlewoodPaleyPiece φ j).coefficient x ξ‖
        ≤ C * t ^ (m + n) * t⁻¹ ^ (n + 1) := by
    have hexp : t ^ (m - ((List.replicate (n + 1) i).length : ℝ) + n) =
        t ^ (m + n) * t⁻¹ ^ (n + 1) := by
      rw [List.length_replicate, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg ht.le,
        ← Real.rpow_add ht]
      push_cast
      ring_nf
    refine (h₁ i j x).trans ?_
    rw [hexp, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (by positivity)
    exact (Finset.single_le_sum (fun i _ ↦ hC₁ i) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hC₀)
  rw [quantizeLittlewoodPaleyPiece_eq]
  refine (norm_quantizeLp_le (a := smoothingPiece φ a j) (inv_pos.2 ht)
    (by simpa only [coefficient_smoothingPiece] using hA)
    (by simpa only [coefficient_smoothingPiece] using hR)).trans_eq ?_
  have htn : t ^ n * t⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
  have htm : t ^ (m + n) * t⁻¹ ^ n = t ^ m := by
    rw [Real.rpow_add ht, Real.rpow_natCast, mul_assoc, htn, mul_one]
  rw [← htm]
  simp only [D]
  ring

end NormedSpace

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### Almost orthogonality of the Littlewood–Paley pieces -/

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- **Orthogonality of distant pieces.** There is `L` such that `Op(aⱼ) Op(aₖ)† = 0` on `L²`
whenever `j + L ≤ k` or `k + L ≤ j`: the cutoffs `ψⱼ` and `ψₖ` then have disjoint supports. -/
theorem IsUniform.exists_quantizeLittlewoodPaleyPiece_comp_adjoint_eq_zero {a : Symbol n V W m}
    (ha : a.IsUniform) :
    ∃ L : ℕ, ∀ j k, j + L ≤ k ∨ k + L ≤ j →
      a.quantizeLittlewoodPaleyPiece φ 2 ha j ∘L
        adjoint (a.quantizeLittlewoodPaleyPiece φ 2 ha k) = 0 := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  refine ⟨L, fun j k hjk ↦ ?_⟩
  have hψ (ξ : CoordinateSpace n) :
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0 := by
    rcases hjk with h | h
    · exact hL j k h ξ
    · rw [mul_comm]
      exact hL k j h ξ
  rw [quantizeLittlewoodPaleyPiece_eq, quantizeLittlewoodPaleyPiece_eq]
  refine quantizeLp_comp_adjoint_eq_zero _ _ _ _ fun x z ξ ↦ ?_
  simp only [coefficient_smoothingPiece, coefficient_littlewoodPaleyPiece]
  rcases mul_eq_zero.1 (hψ ξ) with h | h <;> simp [h]

/-- **Cotlar–Stein bound for `Op(aⱼ) Op(aₖ)†`.** For a uniform symbol of order `m ≤ 0`, the
quantizations of its Littlewood–Paley pieces satisfy `∑ₖ √‖Op(aⱼ) Op(aₖ)†‖ ≤ A` for every `j`,
the sum being over an arbitrary finite set of indices `k`: only the boundedly many `k` near `j`
contribute, each by at most the uniform bound on `‖Op(aₖ)‖`. This is one of the two hypotheses
of the Cotlar–Stein lemma `TauCeti.exists_hasSum_apply_of_almost_orthogonal`. -/
theorem IsUniform.exists_sum_sqrt_norm_quantizeLittlewoodPaleyPiece_comp_adjoint_le
    {a : Symbol n V W m} (ha : a.IsUniform) (hm : m ≤ 0) :
    ∃ A, 0 ≤ A ∧ ∀ j (s : Finset ℕ), ∑ k ∈ s,
      √‖a.quantizeLittlewoodPaleyPiece φ 2 ha j ∘L
        adjoint (a.quantizeLittlewoodPaleyPiece φ 2 ha k)‖ ≤ A := by
  obtain ⟨C, hC, hT⟩ := ha.exists_norm_quantizeLittlewoodPaleyPiece_le φ 2
  obtain ⟨L, hL⟩ := ha.exists_quantizeLittlewoodPaleyPiece_comp_adjoint_eq_zero φ
  generalize a.quantizeLittlewoodPaleyPiece φ 2 ha = T at hT hL ⊢
  have hT' (j : ℕ) : ‖T j‖ ≤ C := (hT j).trans (mul_le_of_le_one_right hC
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ one_le_two) hm))
  refine ⟨(2 * L) • C, nsmul_nonneg hC _, fun j s ↦ ?_⟩
  have hle (k : ℕ) : √‖T j ∘L adjoint (T k)‖ ≤ C := by
    rw [Real.sqrt_le_left hC]
    calc ‖T j ∘L adjoint (T k)‖ ≤ ‖T j‖ * ‖adjoint (T k)‖ := opNorm_comp_le _ _
      _ ≤ C * C := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul (hT' j) (hT' k) (norm_nonneg _) hC
      _ = C ^ 2 := (sq C).symm
  refine Finset.sum_le_of_eq_zero_of_dist_ge (j := j) (fun _ ↦ Real.sqrt_nonneg _) hle
    (fun k hk ↦ ?_) s
  rw [hL j k hk, norm_zero, Real.sqrt_zero]

end InnerProductSpace

end Symbol

end TauCeti
