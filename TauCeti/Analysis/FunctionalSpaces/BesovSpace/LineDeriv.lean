/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein

/-!
# Besov regularity from the first derivatives

Let `b` be an orthonormal basis of `E`, let `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`. If `f ∈ Lᵖ` and each
directional derivative `∂_{bᵢ} f` lies in the inhomogeneous Besov space `B^s_{p,q}`, then `f` lies
in `B^{s+1}_{p,q}`, with

`‖f‖_{B^{s+1}_{p,q}} ≤ C (‖f‖_p + ∑ᵢ ‖∂_{bᵢ} f‖_{B^s_{p,q}})`,

where `C` depends only on the bump function and on `b`, not on `s`, `p` or `q`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq`). One derivative more in
every direction is one order more on the Besov scale. Applied repeatedly, this recognises the
Besov regularity of a function of class `C^k` from that of its derivatives of order `k`.

## The argument

The low-frequency block `Δ₀ f` is bounded on `Lᵖ` by `‖f‖_p`. For `j ≥ 0` the block `Δ_{j+1} f`
has Fourier transform carried by the annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`, where the reverse
Bernstein inequality (`OrthonormalBasis.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq`) bounds
it by `2^{-j}` times its first derivatives:

`‖Δ_{j+1} f‖_p ≤ C 2^{-j} ∑ᵢ ‖∂_{bᵢ} Δ_{j+1} f‖_p = C 2^{-j} ∑ᵢ ‖Δ_{j+1} ∂_{bᵢ} f‖_p`.

Multiplying by `2^{(j+1)(s+1)}` bounds the weighted blocks of `f` of order `s + 1` by those of the
`∂_{bᵢ} f` of order `s`, so the `ℓ^q` norm of the former is controlled by the Besov norms of the
latter.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.3.8 (lifting property).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Lemma 2.1 (Bernstein's inequalities).
-/

public section

noncomputable section

open MeasureTheory Metric FourierTransform TemperedDistribution Distribution
open scoped ENNReal SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

/-- **One block from the first derivatives.** There is `c`, depending only on `φ` and the
orthonormal basis `b`, with the following property. If the block `Δ_{j+1} f` of `f ∈ Lᵖ` is the
`Lᵖ` function `g`, whose derivatives `∂_{bᵢ} g` are the `Lᵖ` functions `hᵢ`, then for every
`s ∈ ℝ` the weighted block `2^{(j+1)(s+1)} ‖g‖_p` is at most `c ∑ᵢ 2^{(j+1)s} ‖hᵢ‖_p`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le (φ : ContDiffBump (0 : E))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (s : ℝ) (f : Lp F p (volume : Measure E))
      (j : ℕ) (g : Lp F p (volume : Measure E)) (h : ι → Lp F p (volume : Measure E)),
      littlewoodPaleyBlock F φ (j + 1) (f : 𝓢'(E, F)) = g →
      (∀ i, ∂_{b i} (g : 𝓢'(E, F)) = h i) →
      2 ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) * ‖g‖ ≤
        c * ∑ i, 2 ^ (s * ((j + 1 : ℕ) : ℝ)) * ‖h i‖ := by
  obtain ⟨Cr, hCr, hrev⟩ :=
    b.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq (F := F) (2 * φ.rOut / φ.rIn)
  have hrIn := φ.rIn_pos
  refine ⟨2 * Cr / φ.rIn, by positivity, fun {p} _ s f j g h hg hh ↦ ?_⟩
  -- The block `g` has Fourier transform carried by the annulus
  -- `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`, where the reverse Bernstein inequality applies.
  have hR : (0 : ℝ) < 2 ^ j * φ.rIn := by positivity
  have hvan : IsVanishingOn (𝓕 (g : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 (2 ^ j * φ.rIn) ∪ (closedBall 0 (2 * φ.rOut / φ.rIn * (2 ^ j * φ.rIn)))ᶜ) := by
    have heq : 2 * φ.rOut / φ.rIn * (2 ^ j * φ.rIn) = 2 ^ (j + 1) * φ.rOut := by
      field_simp
      ring
    rw [heq, ← hg]
    simpa only [Set.compl_sdiff, Set.union_comm] using
      isVanishingOn_fourier_littlewoodPaleyBlock_succ φ j (f : 𝓢'(E, F))
  have h2 : (2 : ℝ) ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) =
      2 ^ (s * ((j + 1 : ℕ) : ℝ)) * (2 * 2 ^ j) := by
    rw [add_mul, one_mul, Real.rpow_add two_pos, Real.rpow_natCast, pow_succ, mul_comm 2]
  calc (2 : ℝ) ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) * ‖g‖
      ≤ 2 ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) * (Cr / (2 ^ j * φ.rIn) * ∑ i, ‖h i‖) := by
        gcongr
        exact hrev hR g h hvan hh
    _ = 2 * Cr / φ.rIn * ∑ i, 2 ^ (s * ((j + 1 : ℕ) : ℝ)) * ‖h i‖ := by
        rw [h2, ← Finset.mul_sum]
        field_simp

/-- **Besov regularity from the first derivatives.** Let `b` be an orthonormal basis of `E`. There
is `C`, depending only on `φ` and `b`, with the following property. Let `s ∈ ℝ`,
`1 ≤ p, q ≤ ∞` and `f ∈ Lᵖ`. If every directional derivative `∂_{bᵢ} f` is an element `vᵢ` of
`B^s_{p,q}`, then `f` is an element of `B^{s+1}_{p,q}` of norm at most
`C (‖f‖_p + ∑ᵢ ‖vᵢ‖)`. -/
theorem exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq (φ : ContDiffBump (0 : E)) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (f : Lp F p (volume : Measure E)) (v : ι → BesovSpace F φ s p q),
      (∀ i, ∂_{b i} (f : 𝓢'(E, F)) = (v i).toDistr) →
      ∃ w : BesovSpace F φ (s + 1) p q, w.toDistr = f ∧ ‖w‖ ≤ C * (‖f‖ + ∑ i, ‖v i‖) := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨c, hc, hblock⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le (F := F) φ b
  refine ⟨max CΔ 0 + c, by positivity, fun {s p q} _ _ f v hv ↦ ?_⟩
  -- The blocks of `f` are `Lᵖ` functions, and their derivatives are the blocks of the `vᵢ`.
  choose g hg hgn using fun j ↦ hΔ j f
  have hder (j : ℕ) (i : ι) : ∂_{b i} (g j : 𝓢'(E, F)) = (v i).block j := by
    rw [← hg, ← littlewoodPaleyBlock_lineDerivOp, hv i, coe_block]
  -- The majorant `B` of the weighted blocks of `f` of order `s + 1`, built from the weighted
  -- block norms of the `vᵢ`.
  set e : lp (fun _ : ℕ ↦ ℝ) q := lp.single q 0 (1 : ℝ)
  set B : lp (fun _ : ℕ ↦ ℝ) q := (max CΔ 0 * ‖f‖) • e + c • ∑ i, (v i).weightedBlockNorms
  have hB (j : ℕ) : B j = (max CΔ 0 * ‖f‖) * (if j = 0 then 1 else 0) +
      c * ∑ i, 2 ^ (s * j) * ‖(v i).block j‖ := by
    simp only [B, e, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sum, Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, weightedBlockNorms_apply]
  obtain ⟨w, hw, hwn⟩ :=
    exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq (s := s + 1) g B hg fun j ↦ by
      rw [hB]
      rcases j with _ | j
      · -- The low-frequency block is bounded by `‖f‖_p`.
        simp only [↓reduceIte, Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul, mul_one]
        exact ((hgn 0).trans (by gcongr; exact le_max_left _ _)).trans
          (le_add_of_nonneg_right (by positivity))
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, mul_zero, zero_add]
        exact hblock s f j _ _ (hg (j + 1)) (hder (j + 1))
  refine ⟨w, hw, hwn.trans ?_⟩
  have he : ‖e‖ = 1 := by rw [lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one]
  calc ‖B‖ ≤ ‖(max CΔ 0 * ‖f‖) • e‖ + ‖c • ∑ i, (v i).weightedBlockNorms‖ := norm_add_le _ _
    _ ≤ max CΔ 0 * ‖f‖ + c * ∑ i, ‖v i‖ := by
      rw [norm_smul, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg hc]
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (norm_weightedBlockNorms _).le)
    _ ≤ (max CΔ 0 + c) * (‖f‖ + ∑ i, ‖v i‖) := by
      have : 0 ≤ ∑ i, ‖v i‖ := by positivity
      nlinarith [le_max_right CΔ 0, norm_nonneg f]

end TauCeti.BesovSpace
