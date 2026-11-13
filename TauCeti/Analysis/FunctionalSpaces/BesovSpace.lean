/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`Δⱼ` (`j ≥ 0`) be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). For `s : ℝ` and `1 ≤ p, q ≤ ∞`, the
**inhomogeneous Besov space** `B^s_{p,q}` consists of the tempered distributions `u` whose blocks
`Δⱼ u` are `Lᵖ` functions with

`‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)ⱼ‖_{ℓ^q} < ∞`.

The parameter `s` measures smoothness, `p` integrability and `q` is a fine index; for
`p = q = ∞` this is the Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}`. The definition is relative to the
chosen bump function `φ`, but the space is not: the Besov spaces built from two bump functions
contain the same tempered distributions, with equivalent norms. Indeed the blocks `Δ'ⱼ` of a
second bump function `φ'` interact only with the blocks `Δₖ` of nearby index,
`Δ'ⱼ u = ∑_{j - L ≤ k < j + L} Δ'ⱼ Δₖ u`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`), and the blocks are uniformly
bounded on `Lᵖ`, so `2^{js} ‖Δ'ⱼ u‖_p` is at most a constant times a window sum of the
`2^{ks} ‖Δₖ u‖_p`, whose `ℓ^q` norm is at most `2 L` times theirs.

We encode the norm through the sequence of weighted blocks `(2^{js} Δⱼ u)ⱼ`, an element of the
normed space `ℓ^q(ℕ, Lᵖ)`. A tempered distribution is determined by its blocks
(`TemperedDistribution.eq_of_forall_littlewoodPaleyBlock_eq`) and an `Lᵖ` function by its
tempered distribution, so this sequence is an injective linear image of `u`; the Besov norm is the
norm it induces. As in Mathlib's `BesselPotentialSpace`, an element of the bundled space stores
both its tempered distribution and this `Lᵖ` data.

## Main declarations

* `TemperedDistribution.MemBesov φ s p q u`: the unbundled predicate `u ∈ B^s_{p,q}`, and its
  characterisation `TemperedDistribution.memBesov_iff` by `Lᵖ` blocks with weighted `ℓ^q` norms;
  `TemperedDistribution.memBesov_iff_memℓp` is the same test for blocks already known to be `Lᵖ`
  functions.
* `TauCeti.BesovSpace F φ s p q`: the bundled space, a complex normed space whose elements carry
  their tempered distribution `toDistr` and weighted blocks `weightedBlocks`.
* `TauCeti.BesovSpace.block`: the block `Δⱼ u` as an `Lᵖ` function, with
  `TauCeti.BesovSpace.norm_eq_tsum_rpow` and `TauCeti.BesovSpace.hasSum_norm` (`q < ∞`) and
  `TauCeti.BesovSpace.norm_eq_ciSup` (`q = ∞`) expressing the norm through the blocks, and the
  single-block bound `TauCeti.BesovSpace.rpow_mul_norm_block_le`; conversely
  `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq` bounds the norm of a
  distribution by any `ℓ^q` majorant of its weighted block norms.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_block`: a tempered distribution whose
  blocks are `L^{p'}` functions with weighted norms `2^{js'} ‖Δⱼ w‖_{p'} ≤ B 2^{js} ‖Δⱼ u‖_p` for
  some `u ∈ B^s_{p,q}` lies in `B^{s'}_{p',q}`, with norm at most `B ‖u‖`.
* `TauCeti.BesovSpace.toDistrCLM`: for `1 ≤ q`, the continuous inclusion of `B^s_{p,q}` in the
  tempered distributions, and the instance `CompleteSpace (TauCeti.BesovSpace F φ s p q)`:
  `B^s_{p,q}` is a Banach space.
* `TauCeti.BesovSpace.inclusion`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` with norm at most `1` for
  `s' ≤ s` and `q ≤ q'`.
* `TauCeti.BesovSpace.inclusionOfLT`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s` and arbitrary
  `q, q'`, with norm at most `(1 - 2^{s' - s})⁻¹`. At the level of the predicate these inclusions
  are `TemperedDistribution.MemBesov.mono` and `TemperedDistribution.MemBesov.of_lt`.
* `TemperedDistribution.MemBesov.of_bump` and `TauCeti.BesovSpace.bumpEquiv`: the Besov space does
  not depend on the bump function; the identity on tempered distributions is an isomorphism of
  normed spaces between the Besov spaces built from two bump functions.
* `TauCeti.BesovSpace.inclusionOfExponentLE`: the Bernstein embedding
  `B^s_{p,q} ⊆ B^{s - n (1/p - 1/r)}_{r,q}` for `p ≤ r` in dimension `n`, bounded uniformly in `s`
  and `q` (`TauCeti.BesovSpace.exists_norm_inclusionOfExponentLE_le`); at the level of the
  predicate it is `TemperedDistribution.MemBesov.mono_exponent`. The Fourier transform of each
  block `Δⱼ u` is carried by the ball of radius `2^j φ.rOut`, so Bernstein's inequality bounds its
  `Lʳ` norm by `C 2^{j n (1/p - 1/r)}` times its `Lᵖ` norm, with `C` independent of `j` and `u`.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_eq`: a Schwartz function whose Fourier transform
  is carried by the region where `ψⱼ = 1` lies in every Besov space, with norm `2^{js} ‖u‖_p`;
  `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_eq_of_norm_le` is the low-frequency case `j = 0`,
  where the norm is `‖u‖_p` for every `s`.
* `TauCeti.two_rpow_mul_norm_sum_Ico_le`: the weighted estimate
  `2^{ks} ‖∑_{k - L ≤ j < k + L} gⱼ‖ ≤ max C 0 2^{|s| L} ∑_{k - L ≤ j < k + L} 2^{js} ‖xⱼ‖` when
  `‖gⱼ‖ ≤ C ‖xⱼ‖`, by which a block that is a sum of boundedly many pieces of nearby index is
  controlled by the weighted pieces.
* `TauCeti.two_rpow_mul_norm_tsum_le`: the weighted estimate
  `2^{ks} ‖∑ⱼ gⱼ‖ ≤ K 2^{|s| N} ∑_{k - N ≤ j < k + N} aⱼ + K ∑_{d ≥ 0} (2^{-s})^d a_{d + k}` when
  `gⱼ = 0` for `j + N ≤ k`, `‖gⱼ‖ ≤ K xⱼ` and `2^{js} xⱼ ≤ aⱼ`, by which a block meeting all pieces
  of higher index is controlled by a window sum and a geometric tail sum.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Proposition 2.71.
* H. Triebel, *Theory of Function Spaces*, Section 2.3; completeness and the embedding in the
  tempered distributions are in Section 2.3.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Weighted window sums.** If `‖gⱼ‖ ≤ C ‖xⱼ‖` for every `j`, then
`2^{ks} ‖∑_{k - L ≤ j < k + L} gⱼ‖ ≤ max C 0 2^{|s| L} ∑_{k - L ≤ j < k + L} 2^{js} ‖xⱼ‖`. -/
theorem TauCeti.two_rpow_mul_norm_sum_Ico_le {G H : Type*} [SeminormedAddCommGroup G]
    [SeminormedAddCommGroup H] (s : ℝ) {C : ℝ} {g : ℕ → G} {x : ℕ → H}
    (hg : ∀ j, ‖g j‖ ≤ C * ‖x j‖) (k L : ℕ) :
    (2 : ℝ) ^ (s * k) * ‖∑ j ∈ Finset.Ico (k - L) (k + L), g j‖ ≤
      max C 0 * 2 ^ (|s| * L) * ∑ j ∈ Finset.Ico (k - L) (k + L), 2 ^ (s * j) * ‖x j‖ := by
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  calc 2 ^ (s * k) * ‖g j‖ ≤ 2 ^ (|s| * L) * 2 ^ (s * j) * (max C 0 * ‖x j‖) := by
        gcongr
        · exact Real.rpow_mul_natCast_le_of_mem_Ico' one_le_two s hj
        · exact (hg j).trans (by gcongr; exact le_max_left C 0)
    _ = _ := by ring

/-- **Weighted tail sums.** Let `gⱼ` be vectors that vanish for `j + N ≤ k`, with `‖gⱼ‖ ≤ K xⱼ`
and `2^{js} xⱼ ≤ aⱼ`. Splitting `∑ⱼ gⱼ` at `j = k`, the contributing terms below `k` lie within
`N` of `k`, and each term above `k` carries the weight `2^{(k - j)s} = (2^{-s})^{j - k}`, so
`2^{ks} ‖∑ⱼ gⱼ‖ ≤ K 2^{|s| N} ∑_{k - N ≤ j < k + N} aⱼ + K ∑_{d ≥ 0} (2^{-s})^d a_{d + k}`. -/
theorem TauCeti.two_rpow_mul_norm_tsum_le {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    {s K T : ℝ} (hK : 0 ≤ K) {k N : ℕ} {g : ℕ → G} {x a : ℕ → ℝ}
    (hg0 : ∀ j, j + N ≤ k → g j = 0) (hgx : ∀ j, ‖g j‖ ≤ K * x j)
    (hx0 : ∀ j, 0 ≤ x j) (hxa : ∀ j : ℕ, 2 ^ (s * j) * x j ≤ a j)
    (hsum : Summable fun j ↦ ‖g j‖)
    (hT : HasSum (fun d ↦ ((2 : ℝ) ^ (-s)) ^ d • a (d + k)) T) :
    2 ^ (s * k) * ‖∑' j, g j‖ ≤
      K * 2 ^ (|s| * N) * ∑ j ∈ Finset.Ico (k - N) (k + N), a j + K * T := by
  -- The terms below `k`, a window sum around `k`.
  have hlow : 2 ^ (s * k) * ‖∑ j ∈ Finset.range k, g j‖ ≤
      K * 2 ^ (|s| * N) * ∑ j ∈ Finset.Ico (k - N) (k + N), a j := by
    have hwin : ∑ j ∈ Finset.range k, g j =
        ∑ j ∈ Finset.Ico (k - N) (k + N), if j < k then g j else 0 := by
      rw [← Finset.sum_filter]
      refine (Finset.sum_subset (fun j hj ↦ ?_) fun j hj hj' ↦ hg0 j ?_).symm
      · simp only [Finset.mem_filter, Finset.mem_Ico] at hj
        exact Finset.mem_range.2 hj.2
      · simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hj hj'
        omega
    have hg' (j : ℕ) : ‖if j < k then g j else 0‖ ≤ K * ‖x j‖ := by
      rw [Real.norm_of_nonneg (hx0 j)]
      split_ifs
      · exact hgx j
      · rw [norm_zero]
        exact mul_nonneg hK (hx0 j)
    rw [hwin]
    refine (TauCeti.two_rpow_mul_norm_sum_Ico_le s hg' k N).trans ?_
    rw [max_eq_left hK]
    gcongr with j
    rw [Real.norm_of_nonneg (hx0 j)]
    exact hxa j
  -- The terms above `k`.
  have hhigh : 2 ^ (s * k) * ‖∑' d, g (d + k)‖ ≤ K * T := by
    have hsum' : Summable fun d ↦ ‖g (d + k)‖ := (summable_nat_add_iff k).2 hsum
    refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum') (by positivity)).trans ?_
    refine hasSum_le (fun d ↦ ?_) (hsum'.hasSum.mul_left _) (hT.mul_left K)
    calc 2 ^ (s * k) * ‖g (d + k)‖
        ≤ ((2 : ℝ) ^ (-s)) ^ d * 2 ^ (s * (d + k : ℕ)) * (K * x (d + k)) := by
          rw [Real.rpow_neg_pow_mul_rpow_mul_natCast_add two_pos]
          exact mul_le_mul_of_nonneg_left (hgx _) (by positivity)
      _ = K * (((2 : ℝ) ^ (-s)) ^ d * (2 ^ (s * (d + k : ℕ)) * x (d + k))) := by ring
      _ ≤ K * (((2 : ℝ) ^ (-s)) ^ d • a (d + k)) := by rw [smul_eq_mul]; gcongr; exact hxa _
  calc 2 ^ (s * k) * ‖∑' j, g j‖
      = 2 ^ (s * k) * ‖∑ j ∈ Finset.range k, g j + ∑' d, g (d + k)‖ := by
        rw [hsum.of_norm.sum_add_tsum_nat_add k]
    _ ≤ 2 ^ (s * k) * ‖∑ j ∈ Finset.range k, g j‖ + 2 ^ (s * k) * ‖∑' d, g (d + k)‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ _ := add_le_add hlow hhigh

namespace TemperedDistribution

section MemBesov

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **inhomogeneous Besov space** `B^s_{p,q}` built from the
Littlewood–Paley partition of `φ` if its weighted blocks `2^{js} Δⱼ u` are `Lᵖ` functions forming
an `ℓ^q` sequence. See `TemperedDistribution.memBesov_iff` for the formulation with the unweighted
blocks. -/
def MemBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ v : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q,
    ∀ j : ℕ, (v j : 𝓢'(E, F)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlock F φ j u

variable {φ s p q}

/-- `u ∈ B^s_{p,q}` exactly when every Littlewood–Paley block `Δⱼ u` is an `Lᵖ` function `fⱼ` and
the sequence `2^{js} ‖fⱼ‖_p` lies in `ℓ^q`. -/
theorem memBesov_iff {u : 𝓢'(E, F)} :
    u.MemBesov φ s p q ↔ ∃ f : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) q := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • v j, fun j ↦ ?_,
      (lp.memℓp v).norm.mono fun j ↦ le_of_eq ?_⟩
    · rw [Lp.toTemperedDistribution_smul, hv,
        inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]
    · rw [Real.norm_of_nonneg (by positivity), norm_smul, norm_inv,
        Complex.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ (by positivity)]
  · rintro ⟨f, hf, hmem⟩
    refine ⟨⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f j, hmem.mono fun j ↦ le_of_eq ?_⟩,
      fun j ↦ ?_⟩
    · rw [norm_smul, Complex.norm_of_nonneg (by positivity)]
    · -- The `j`-th entry of the anonymous `lp` element is `2^{js} • f j` by definition: `lp`
      -- coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
      rw [hf j]
      exact Lp.toTemperedDistribution_smul _ (f j)

/-- If the Littlewood–Paley blocks `Δⱼ u` are the `Lᵖ` functions `fⱼ`, then `u ∈ B^s_{p,q}` exactly
when the sequence `2^{js} ‖fⱼ‖_p` lies in `ℓ^q`. -/
theorem memBesov_iff_memℓp {u : 𝓢'(E, F)} {f : ℕ → Lp F p (volume : Measure E)}
    (hf : ∀ j, littlewoodPaleyBlock F φ j u = f j) :
    u.MemBesov φ s p q ↔ Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) q := by
  refine ⟨fun hu ↦ ?_, fun h ↦ memBesov_iff.2 ⟨f, hf, h⟩⟩
  obtain ⟨g, hg, hmem⟩ := memBesov_iff.1 hu
  -- An `Lᵖ` function is determined by its tempered distribution, so `g = f`.
  have hgf : g = f := funext fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ← hg, hf]
  rwa [hgf] at hmem

theorem MemBesov.zero : (0 : 𝓢'(E, F)).MemBesov φ s p q :=
  ⟨0, fun j ↦ by simp⟩

theorem MemBesov.add {u v : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (hv : v.MemBesov φ s p q) :
    (u + v).MemBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  refine ⟨a + b, fun j ↦ ?_⟩
  rw [lp.coeFn_add, Pi.add_apply, Lp.toTemperedDistribution_add, ha, hb, map_add, smul_add]

theorem MemBesov.smul {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (c : ℂ) :
    (c • u).MemBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨c • a, fun j ↦ ?_⟩
  rw [lp.coeFn_smul, Pi.smul_apply, Lp.toTemperedDistribution_smul, ha, map_smul, smul_comm]

/-- **Monotonicity of the Besov scale.** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' ≤ s` and `q ≤ q'`. -/
theorem MemBesov.mono {u : 𝓢'(E, F)} {s' : ℝ} {q' : ℝ≥0∞} (hu : u.MemBesov φ s p q)
    (hs : s' ≤ s) (hq : q ≤ q') : u.MemBesov φ s' p q' := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨f, hf, (hmem.of_exponent_ge hq).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  exact one_le_two

/-- Lowering the order from `s` to `s'` multiplies the `j`-th weight `2^{js}` by
`(2^{s' - s})^j`. -/
private theorem two_rpow_mul_natCast_eq (s s' : ℝ) (j : ℕ) :
    (2 : ℝ) ^ (s' * j) = (2 ^ (s' - s)) ^ j * 2 ^ (s * j) := by
  rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_add two_pos, ← add_mul, sub_add_cancel]

/-- **Strict monotonicity of the Besov scale.** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s`, every
`q` and every `q' ≠ 0`: the weighted blocks for `s'` decay geometrically. -/
theorem MemBesov.of_lt {u : 𝓢'(E, F)} {s' : ℝ} {q' : ℝ≥0∞} (hu : u.MemBesov φ s p q)
    (hs : s' < s) (hq' : q' ≠ 0) : u.MemBesov φ s' p q' := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  obtain ⟨C, hC⟩ := memℓp_infty_iff.1 (hmem.of_exponent_ge le_top)
  refine memBesov_iff.2 ⟨f, hf, Memℓp.of_norm_le_geometric (C := C) (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hs)) (fun j ↦ ?_) hq'⟩
  have hj : ‖(2 : ℝ) ^ (s * j) * ‖f j‖‖ ≤ C := hC ⟨j, rfl⟩
  rw [Real.norm_of_nonneg (by positivity)] at hj ⊢
  rw [two_rpow_mul_natCast_eq s s' j, mul_assoc, mul_comm C]
  exact mul_le_mul_of_nonneg_left hj (by positivity)

theorem MemBesov.neg {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) : (-u).MemBesov φ s p q := by
  simpa using hu.smul (-1)

theorem MemBesov.sub {u v : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (hv : v.MemBesov φ s p q) :
    (u - v).MemBesov φ s p q := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- **The blocks of another bump function.** If the blocks `Δₖ u` built from `φ` are `Lᵖ`
functions `fₖ`, then the blocks `Δ'ⱼ u` built from `φ'` are `Lᵖ` functions `f'ⱼ`, with
`2^{js} ‖f'ⱼ‖_p ≤ K ∑_{j - L ≤ k < j + L} 2^{ks} ‖fₖ‖_p`. The constants `K` and `L` depend only on
`φ`, `φ'` and `s`. -/
private theorem exists_littlewoodPaleyBlock_eq_and_le (φ φ' : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (f : ℕ → Lp F p (volume : Measure E)), (∀ k, littlewoodPaleyBlock F φ k u = f k) →
      ∃ f' : ℕ → Lp F p (volume : Measure E), (∀ j, littlewoodPaleyBlock F φ' j u = f' j) ∧
        ∀ j : ℕ, 2 ^ (s * j) * ‖f' j‖ ≤
          K * ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (s * k) * ‖f k‖ := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ'
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ'
  refine ⟨max C 0 * 2 ^ (|s| * L), L, by positivity, fun {p} _ {u} f hf ↦ ?_⟩
  choose g hg hgC using fun j k ↦ hC (p := p) j (f k)
  refine ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), g j k, fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [hL j u]
    simp_rw [hf, hg]
    exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm
  · exact TauCeti.two_rpow_mul_norm_sum_Ico_le s (hgC j) j L

/-- **Independence of the bump function.** A tempered distribution in the Besov space `B^s_{p,q}`
built from the Littlewood–Paley partition of `φ` lies in the Besov space `B^s_{p,q}` built from any
other bump function `φ'`. -/
theorem MemBesov.of_bump {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (φ' : ContDiffBump (0 : E)) :
    u.MemBesov φ' s p q := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  obtain ⟨K, L, _, hKL⟩ := exists_littlewoodPaleyBlock_eq_and_le (F := F) φ φ' s
  obtain ⟨f', hf', hle⟩ := hKL f hf
  refine memBesov_iff.2 ⟨f', hf', ((hmem.sum_Ico_sub_add L).const_mul K).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hle j

/-- **The Bernstein embedding.** For `p ≤ r`, `B^s_{p,q} ⊆ B^{s - n (1/p - 1/r)}_{r,q}`, where `n`
is the dimension of `E` and `1/∞ = 0`: raising the integrability exponent of the blocks from `p`
to `r` costs `n (1/p - 1/r)` orders of smoothness. -/
theorem MemBesov.mono_exponent {u : 𝓢'(E, F)} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hu : u.MemBesov φ s p q) (hpr : p ≤ r) :
    u.MemBesov φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q := by
  obtain ⟨C, _, hB⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le_of_le (F := F) φ hpr
  set a : ℝ := Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  choose g hg hgf using fun j ↦ hB j u (f j) (hf j)
  refine memBesov_iff.2 ⟨g, hg, (hmem.const_mul C).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_sub_mul_mul_rpow_mul two_pos s a j]
  exact (mul_le_mul_of_nonneg_left (hgf j) (by positivity)).trans_eq (by ring)

end MemBesov

end TemperedDistribution

namespace TauCeti

open TemperedDistribution

variable (F) in
/-- The **inhomogeneous Besov space** `B^s_{p,q}` built from the Littlewood–Paley partition of the
bump function `φ`: the tempered distributions `u` whose weighted Littlewood–Paley blocks
`2^{js} Δⱼ u` are `Lᵖ` functions forming an `ℓ^q` sequence. An element stores both `u` and this
sequence, which determine each other. For `1 ≤ q` it is a normed space with
`‖u‖ = ‖(2^{js} ‖Δⱼ u‖_p)ⱼ‖_{ℓ^q}`. -/
structure BesovSpace (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] where
  /-- The underlying tempered distribution. -/
  toDistr : 𝓢'(E, F)
  /-- The weighted Littlewood–Paley blocks `(2^{js} Δⱼ u)ⱼ`, an `ℓ^q` sequence of `Lᵖ`
  functions. -/
  weightedBlocks : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q
  /-- The `j`-th weighted block is the `j`-th Littlewood–Paley block of `toDistr`, multiplied
  by `2^{js}`. -/
  coe_weightedBlocks_apply : ∀ j : ℕ, (weightedBlocks j : 𝓢'(E, F)) =
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • littlewoodPaleyBlock F φ j toDistr

namespace BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tempered distribution of an element of `B^s_{p,q}` lies in `B^s_{p,q}`. -/
theorem memBesov_toDistr (u : BesovSpace F φ s p q) : u.toDistr.MemBesov φ s p q :=
  ⟨u.weightedBlocks, u.coe_weightedBlocks_apply⟩

/-- An element of a Besov space is determined by its tempered distribution. -/
@[ext]
theorem ext {u v : BesovSpace F φ s p q} (h : u.toDistr = v.toDistr) : u = v := by
  obtain ⟨u, a, ha⟩ := u
  obtain ⟨v, b, hb⟩ := v
  obtain rfl : u = v := h
  obtain rfl : a = b := lp.ext <| funext fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ha, hb]
  rfl

/-- An element of a Besov space is determined by its weighted Littlewood–Paley blocks. -/
theorem weightedBlocks_injective :
    Function.Injective (weightedBlocks : BesovSpace F φ s p q → _) := by
  intro u v h
  ext1
  refine eq_of_forall_littlewoodPaleyBlock_eq φ fun j ↦ smul_right_injective _
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos two_pos (s * j)).ne') ?_
  simp only [← coe_weightedBlocks_apply, h]

instance : Zero (BesovSpace F φ s p q) where
  zero := ⟨0, 0, fun j ↦ by simp⟩

instance : Add (BesovSpace F φ s p q) where
  add u v := ⟨u.toDistr + v.toDistr, u.weightedBlocks + v.weightedBlocks, fun j ↦ by
    simp [smul_add, ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : Neg (BesovSpace F φ s p q) where
  neg u := ⟨-u.toDistr, -u.weightedBlocks, fun j ↦ by
    simp [← u.coe_weightedBlocks_apply]⟩

instance : Sub (BesovSpace F φ s p q) where
  sub u v := ⟨u.toDistr - v.toDistr, u.weightedBlocks - v.weightedBlocks, fun j ↦ by
    simp [smul_sub, ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : SMul ℂ (BesovSpace F φ s p q) where
  smul c u := ⟨c • u.toDistr, c • u.weightedBlocks, fun j ↦ by
    rw [lp.coeFn_smul, Pi.smul_apply, Lp.toTemperedDistribution_smul, u.coe_weightedBlocks_apply,
      map_smul, smul_comm]⟩

instance : SMul ℕ (BesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

instance : SMul ℤ (BesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

@[simp]
theorem toDistr_zero : (0 : BesovSpace F φ s p q).toDistr = 0 := (rfl)

@[simp]
theorem weightedBlocks_zero : (0 : BesovSpace F φ s p q).weightedBlocks = 0 := (rfl)

@[simp]
theorem toDistr_add (u v : BesovSpace F φ s p q) : (u + v).toDistr = u.toDistr + v.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_add (u v : BesovSpace F φ s p q) :
    (u + v).weightedBlocks = u.weightedBlocks + v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_neg (u : BesovSpace F φ s p q) : (-u).toDistr = -u.toDistr := (rfl)

@[simp]
theorem weightedBlocks_neg (u : BesovSpace F φ s p q) :
    (-u).weightedBlocks = -u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_sub (u v : BesovSpace F φ s p q) : (u - v).toDistr = u.toDistr - v.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_sub (u v : BesovSpace F φ s p q) :
    (u - v).weightedBlocks = u.weightedBlocks - v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_smul (c : ℂ) (u : BesovSpace F φ s p q) : (c • u).toDistr = c • u.toDistr :=
  (rfl)

@[simp]
theorem weightedBlocks_smul (c : ℂ) (u : BesovSpace F φ s p q) :
    (c • u).weightedBlocks = c • u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_nsmul (n : ℕ) (u : BesovSpace F φ s p q) : (n • u).toDistr = n • u.toDistr :=
  Nat.cast_smul_eq_nsmul ℂ n u.toDistr

@[simp]
theorem toDistr_zsmul (n : ℤ) (u : BesovSpace F φ s p q) : (n • u).toDistr = n • u.toDistr :=
  Int.cast_smul_eq_zsmul ℂ n u.toDistr

instance : AddCommGroup (BesovSpace F φ s p q) :=
  fast_instance% Function.Injective.addCommGroup toDistr (fun _ _ ↦ ext) toDistr_zero
    toDistr_add toDistr_neg toDistr_sub (fun u n ↦ toDistr_nsmul n u) fun u n ↦ toDistr_zsmul n u

instance : Module ℂ (BesovSpace F φ s p q) :=
  fast_instance% Function.Injective.module ℂ
    (⟨⟨toDistr, toDistr_zero⟩, toDistr_add⟩ : BesovSpace F φ s p q →+ 𝓢'(E, F))
    (fun _ _ ↦ ext) toDistr_smul

variable (F φ s p q) in
/-- The weighted Littlewood–Paley blocks `u ↦ (2^{js} Δⱼ u)ⱼ`, as an injective linear map into
`ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksₗ :
    BesovSpace F φ s p q →ₗ[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q where
  toFun := weightedBlocks
  map_add' := weightedBlocks_add
  map_smul' := weightedBlocks_smul

@[simp]
theorem weightedBlocksₗ_apply (u : BesovSpace F φ s p q) :
    weightedBlocksₗ F φ s p q u = u.weightedBlocks := (rfl)

/-- The Littlewood–Paley block `Δⱼ u` of an element of a Besov space, as an `Lᵖ` function. -/
def block (u : BesovSpace F φ s p q) (j : ℕ) : Lp F p (volume : Measure E) :=
  (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • u.weightedBlocks j

/-- The `Lᵖ` function `u.block j` is the Littlewood–Paley block `Δⱼ u`. -/
@[simp]
theorem coe_block (u : BesovSpace F φ s p q) (j : ℕ) :
    (u.block j : 𝓢'(E, F)) = littlewoodPaleyBlock F φ j u.toDistr := by
  rw [block, Lp.toTemperedDistribution_smul, coe_weightedBlocks_apply,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

theorem weightedBlocks_apply (u : BesovSpace F φ s p q) (j : ℕ) :
    u.weightedBlocks j = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • u.block j := by
  rw [block, smul_inv_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

theorem norm_weightedBlocks_apply (u : BesovSpace F φ s p q) (j : ℕ) :
    ‖u.weightedBlocks j‖ = 2 ^ (s * j) * ‖u.block j‖ := by
  rw [weightedBlocks_apply, norm_smul, Complex.norm_of_nonneg (by positivity)]

@[simp]
theorem block_zero (j : ℕ) : (0 : BesovSpace F φ s p q).block j = 0 := by
  simp [block]

@[simp]
theorem block_add (u v : BesovSpace F φ s p q) (j : ℕ) :
    (u + v).block j = u.block j + v.block j := by
  simp [block, smul_add]

@[simp]
theorem block_neg (u : BesovSpace F φ s p q) (j : ℕ) : (-u).block j = -u.block j := by
  simp [block]

@[simp]
theorem block_sub (u v : BesovSpace F φ s p q) (j : ℕ) :
    (u - v).block j = u.block j - v.block j := by
  simp [block, smul_sub]

@[simp]
theorem block_smul (c : ℂ) (u : BesovSpace F φ s p q) (j : ℕ) :
    (c • u).block j = c • u.block j := by
  rw [block, block, weightedBlocks_smul, lp.coeFn_smul, Pi.smul_apply, smul_comm]

/-- Elements of two Besov spaces with the same tempered distribution have the same blocks. -/
theorem block_eq_of_toDistr_eq {s' : ℝ} {q' : ℝ≥0∞} {u : BesovSpace F φ s p q}
    {v : BesovSpace F φ s' p q'} (h : u.toDistr = v.toDistr) (j : ℕ) : u.block j = v.block j :=
  LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block, h]

/-- A tempered distribution in `B^s_{p,q}`, as an element of the bundled Besov space. -/
def _root_.TemperedDistribution.MemBesov.toBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) : BesovSpace F φ s p q :=
  ⟨u, hu.choose, hu.choose_spec⟩

@[simp]
theorem _root_.TemperedDistribution.MemBesov.toDistr_toBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) : hu.toBesovSpace.toDistr = u := (rfl)

section Normed

variable [Fact (1 ≤ q)]

instance : NormedAddCommGroup (BesovSpace F φ s p q) :=
  fast_instance% NormedAddCommGroup.induced _ _ (weightedBlocksₗ F φ s p q)
    (by exact weightedBlocks_injective)

/-- The Besov norm of `u` is the `ℓ^q(ℕ, Lᵖ)` norm of its weighted blocks. -/
@[simp]
theorem norm_weightedBlocks (u : BesovSpace F φ s p q) : ‖u.weightedBlocks‖ = ‖u‖ := by rfl

instance : NormedSpace ℂ (BesovSpace F φ s p q) where
  norm_smul_le c u := by simp [← norm_weightedBlocks, norm_smul]

/-- **The single-block bound.** Each weighted block `2^{js} ‖Δⱼ u‖_p` is at most `‖u‖`. -/
theorem rpow_mul_norm_block_le (u : BesovSpace F φ s p q) (j : ℕ) :
    2 ^ (s * j) * ‖u.block j‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks_apply, ← norm_weightedBlocks]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j

/-- For `q < ∞` the Besov norm is `(∑ⱼ (2^{js} ‖Δⱼ u‖_p)^q)^{1/q}`. -/
theorem norm_eq_tsum_rpow (hq : q ≠ ∞) (u : BesovSpace F φ s p q) :
    ‖u‖ = (∑' j : ℕ, (2 ^ (s * j) * ‖u.block j‖) ^ q.toReal) ^ (1 / q.toReal) := by
  rw [← norm_weightedBlocks,
    lp.norm_eq_tsum_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)]
  simp_rw [norm_weightedBlocks_apply]

/-- For `q < ∞` the `q`-th power of the Besov norm is the sum `∑ⱼ (2^{js} ‖Δⱼ u‖_p)^q`. -/
theorem hasSum_norm (hq : q ≠ ∞) (u : BesovSpace F φ s p q) :
    HasSum (fun j : ℕ ↦ (2 ^ (s * j) * ‖u.block j‖) ^ q.toReal) (‖u‖ ^ q.toReal) := by
  have h := lp.hasSum_norm (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)
    u.weightedBlocks
  simpa only [norm_weightedBlocks_apply, norm_weightedBlocks] using h

/-- For `q = 2` the squared Besov norm is the sum `∑ⱼ (2^{js} ‖Δⱼ u‖_p)²`. -/
theorem hasSum_norm_sq (u : BesovSpace F φ s p 2) :
    HasSum (fun j : ℕ ↦ (2 ^ (s * j) * ‖u.block j‖) ^ 2) (‖u‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hasSum_norm (by simp) u

/-- For `q = ∞` the Besov norm is `supⱼ 2^{js} ‖Δⱼ u‖_p`. -/
theorem norm_eq_ciSup (u : BesovSpace F φ s p ∞) :
    ‖u‖ = ⨆ j : ℕ, 2 ^ (s * j) * ‖u.block j‖ := by
  rw [← norm_weightedBlocks, lp.norm_eq_ciSup]
  simp_rw [norm_weightedBlocks_apply]

/-- **Membership from a bound on the blocks.** If the blocks `Δⱼ u` of a tempered distribution
are `Lᵖ` functions `gⱼ` with `2^{js} ‖gⱼ‖_p ≤ bⱼ` for a sequence `b ∈ ℓ^q`, then `u` is an element
of `B^s_{p,q}` of norm at most `‖b‖`. -/
theorem exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq {u : 𝓢'(E, F)}
    (g : ℕ → Lp F p (volume : Measure E)) (b : lp (fun _ : ℕ ↦ ℝ) q)
    (hg : ∀ j, littlewoodPaleyBlock F φ j u = g j) (hb : ∀ j : ℕ, 2 ^ (s * j) * ‖g j‖ ≤ b j) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = u ∧ ‖v‖ ≤ ‖b‖ := by
  have hu : u.MemBesov φ s p q := memBesov_iff.2 ⟨g, hg, (lp.memℓp b).mono fun j ↦
    (Real.norm_of_nonneg (by positivity)).trans_le (hb j)⟩
  refine ⟨hu.toBesovSpace, hu.toDistr_toBesovSpace, ?_⟩
  rw [← norm_weightedBlocks]
  refine lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ ?_
  have hj : hu.toBesovSpace.block j = g j :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block,
        MemBesov.toDistr_toBesovSpace, hg j]
  rw [norm_weightedBlocks_apply, hj]
  exact (hb j).trans (Real.le_norm_self _)

/-- **A blockwise criterion for Besov membership.** Let `u ∈ B^s_{p,q}` and `B ≥ 0`. If every
block `Δ'ⱼ w`, for a bump function `φ'`, of a tempered distribution `w` with values in `F'` is an
`L^{p'}` function `gⱼ` with `2^{js'} ‖gⱼ‖_{p'} ≤ B 2^{js} ‖Δⱼ u‖_p`, then `w ∈ B^{s'}_{p',q}`
(for `φ'`) with `‖w‖_{B^{s'}_{p',q}} ≤ B ‖u‖_{B^s_{p,q}}`. -/
theorem exists_toDistr_eq_and_norm_le_of_block {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [CompleteSpace F'] {φ' : ContDiffBump (0 : E)} {p' : ℝ≥0∞}
    [Fact (1 ≤ p')] {s' B : ℝ} (hB : 0 ≤ B)
    (u : BesovSpace F φ s p q) {w : 𝓢'(E, F')} (g : ℕ → Lp F' p' (volume : Measure E))
    (hg : ∀ j, littlewoodPaleyBlock F' φ' j w = g j)
    (hgn : ∀ j : ℕ, 2 ^ (s' * j) * ‖g j‖ ≤ B * (2 ^ (s * j) * ‖u.block j‖)) :
    ∃ v : BesovSpace F' φ' s' p' q, v.toDistr = w ∧ ‖v‖ ≤ B * ‖u‖ := by
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq g
    (B • lp.toNorm u.weightedBlocks) hg fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.toNorm_coe, norm_weightedBlocks_apply]
      exact hgn j
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  rw [norm_smul, Real.norm_of_nonneg hB, lp.norm_toNorm, norm_weightedBlocks]

end Normed

section Complete

/-!
### Completeness and the embedding in the tempered distributions

The Bessel potential `J^{s-1}` maps `B^s_{p,q}` boundedly into `Lᵖ`. On the `j`-th block it acts
with norm `O(2^{j(s-1)})`, by
`TemperedDistribution.exists_besselPotential_compL_littlewoodPaleyBlock_eq`, so the series
`∑ⱼ J^{s-1} Δⱼ u` converges absolutely in `Lᵖ`. Hence `u = J^{1-s} (J^{s-1} u)` depends
continuously on `u`, and the limit of a Cauchy sequence `uₙ` in `B^s_{p,q}` is `J^{1-s}` of the
`Lᵖ` limit of the `J^{s-1} uₙ`.
-/

open Filter Topology

variable [Fact (1 ≤ q)]

/-- The Bessel potential `J^{s-1}` of an element of `B^s_{p,q}` is an `Lᵖ` function, with norm at
most a constant multiple of the Besov norm: `J^{s-1} Δⱼ u` has `Lᵖ` norm `O(2^{-j} ‖u‖)`, so the
series `∑ⱼ J^{s-1} Δⱼ u` converges absolutely in `Lᵖ`. -/
private theorem exists_besselPotential_toDistr_eq_and_norm_le :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ g : Lp F p (volume : Measure E),
      besselPotential E F (s - 1) u.toDistr = g ∧ ‖g‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ (s - 1)
  choose σ hσ hσC using hC
  refine ⟨2 * max C 0, fun u ↦ ?_⟩
  -- `J^{s-1} Δⱼ u = T_{σⱼ} Δⱼ u` is the `Lᵖ` function `h j`.
  choose h hh hhn using fun j ↦ exists_fourierMultiplierCLM_eq_and_norm_le (σ j) (u.block j)
  have hbound (j : ℕ) : ‖h j‖ ≤ max C 0 * ‖u‖ * (1 / 2) ^ j := by
    have h2 : ((2 : ℝ) ^ j) ^ (s - 1) = 2 ^ (s * j) * (1 / 2) ^ j := by
      rw [Real.rpow_sub_one (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
      field_simp
      simp
    calc ‖h j‖ ≤ (∫ x, ‖𝓕⁻ (σ j : E → ℂ) x‖) * ‖u.block j‖ := hhn j
      _ ≤ max C 0 * ((2 : ℝ) ^ j) ^ (s - 1) * ‖u.block j‖ := by
        gcongr
        exact (hσC j).trans (by gcongr; exact le_max_left _ _)
      _ = max C 0 * (1 / 2) ^ j * (2 ^ (s * j) * ‖u.block j‖) := by rw [h2]; ring
      _ ≤ max C 0 * (1 / 2) ^ j * ‖u‖ := by gcongr; exact rpow_mul_norm_block_le u j
      _ = _ := by ring
  have hsum : Summable fun j ↦ ‖h j‖ :=
    (summable_geometric_two.mul_left (max C 0 * ‖u‖)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      hbound
  refine ⟨∑' j, h j, ?_, ?_⟩
  · -- Both sides are limits of `J^{s-1} ∑_{j < N} Δⱼ u = ∑_{j < N} h j` in `𝓢'(E, F)`.
    refine tendsto_nhds_unique (((besselPotential E F (s - 1)).continuous.tendsto _).comp
      (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)) ?_
    have hlim := (hsum.of_norm.hasSum.map (Lp.toTemperedDistributionCLM F volume p)
      (Lp.toTemperedDistributionCLM F volume p).continuous).tendsto_sum_nat
    convert hlim using 2 with N
    · simp only [Function.comp_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Lp.toTemperedDistributionCLM_apply, ← hh, ← ContinuousLinearMap.comp_apply, hσ,
        ContinuousLinearMap.comp_apply, coe_block]
    · rw [Lp.toTemperedDistributionCLM_apply]
  · calc ‖∑' j, h j‖ ≤ ∑' j, ‖h j‖ := norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' j : ℕ, max C 0 * ‖u‖ * (1 / 2) ^ j :=
        hsum.tsum_le_tsum hbound (summable_geometric_two.mul_left _)
      _ = 2 * max C 0 * ‖u‖ := by rw [tsum_mul_left, tsum_geometric_two]; ring

variable (F φ s p q) in
/-- The Bessel potential `u ↦ J^{s-1} u` from `B^s_{p,q}` to `Lᵖ`, an auxiliary continuous linear
map: `B^s_{p,q}` lies in the tempered distributions as `J^{1-s}` of its image. -/
private def besselPotentialLp : BesovSpace F φ s p q →L[ℂ] Lp F p (volume : Measure E) :=
  have hC := (exists_besselPotential_toDistr_eq_and_norm_le (F := F) (φ := φ) (s := s) (p := p)
    (q := q)).choose_spec
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM F volume p) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  have key (u : BesovSpace F φ s p q) : Lp.toTemperedDistributionCLM F volume p (hC u).choose =
      besselPotential E F (s - 1) u.toDistr := (hC u).choose_spec.1.symm
  LinearMap.mkContinuous
    { toFun u := (hC u).choose
      map_add' u v := hinj <| (key (u + v)).trans <| by simp only [map_add, key, toDistr_add]
      map_smul' c u := hinj <| (key (c • u)).trans <| by
        simp only [map_smul, key, toDistr_smul, RingHom.id_apply] }
    _ fun u ↦ (hC u).choose_spec.2

/-- `besselPotentialLp` computes the Bessel potential `J^{s-1}`. -/
private theorem besselPotential_toDistr_eq (u : BesovSpace F φ s p q) :
    besselPotential E F (s - 1) u.toDistr = besselPotentialLp F φ s p q u :=
  (exists_besselPotential_toDistr_eq_and_norm_le.choose_spec u).choose_spec.1

/-- The tempered distribution of `u` is `J^{1-s}` applied to the `Lᵖ` function `J^{s-1} u`. -/
private theorem toDistr_eq_besselPotential (u : BesovSpace F φ s p q) :
    u.toDistr = besselPotential E F (1 - s) (besselPotentialLp F φ s p q u) := by
  rw [← besselPotential_toDistr_eq, besselPotential_besselPotential_apply,
    show s - 1 + (1 - s) = 0 by ring, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- **Besov spaces embed continuously in the tempered distributions.** The map
`B^s_{p,q} → 𝓢'(E, F)` sending `u` to its tempered distribution is continuous. -/
theorem continuous_toDistr : Continuous (toDistr : BesovSpace F φ s p q → 𝓢'(E, F)) := by
  have h : (toDistr : BesovSpace F φ s p q → 𝓢'(E, F)) = besselPotential E F (1 - s) ∘L
      Lp.toTemperedDistributionCLM F volume p ∘L besselPotentialLp F φ s p q := by
    ext1 u
    simp [toDistr_eq_besselPotential u]
  rw [h]
  exact ContinuousLinearMap.continuous _

variable (F φ s p q) in
/-- The inclusion `B^s_{p,q} ⊆ 𝓢'(E, F)`, as a continuous linear map. -/
def toDistrCLM : BesovSpace F φ s p q →L[ℂ] 𝓢'(E, F) where
  toFun := toDistr
  map_add' := toDistr_add
  map_smul' := toDistr_smul
  cont := continuous_toDistr

@[simp]
theorem toDistrCLM_apply (u : BesovSpace F φ s p q) : toDistrCLM F φ s p q u = u.toDistr :=
  (rfl)

/-- The weighted blocks form an isometry from `B^s_{p,q}` into `ℓ^q(ℕ, Lᵖ)`. -/
theorem isometry_weightedBlocks :
    Isometry (weightedBlocks : BesovSpace F φ s p q → _) :=
  AddMonoidHomClass.isometry_of_norm (weightedBlocksₗ F φ s p q) norm_weightedBlocks

/-- **Besov spaces are complete.** For `1 ≤ q`, the Besov space `B^s_{p,q}` is a Banach space. -/
instance : CompleteSpace (BesovSpace F φ s p q) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- The weighted blocks converge in `ℓ^q(ℕ, Lᵖ)` to some `w`, and `J^{s-1} u` converges in `Lᵖ`
  -- to some `g`; then `J^{1-s} g` is a tempered distribution whose weighted blocks are `w`.
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (isometry_weightedBlocks.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    ((besselPotentialLp F φ s p q).uniformContinuous.comp_cauchySeq hu)
  have hv : Tendsto (fun n ↦ (u n).toDistr) atTop
      (𝓝 (besselPotential E F (1 - s) g)) := by
    have := ((besselPotential E F (1 - s) ∘L
      Lp.toTemperedDistributionCLM F volume p).continuous.tendsto g).comp hg
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      Lp.toTemperedDistributionCLM_apply]
    exact (toDistr_eq_besselPotential (u n)).symm
  have hwv (j : ℕ) : (w j : 𝓢'(E, F)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) •
      littlewoodPaleyBlock F φ j (besselPotential E F (1 - s) g) := by
    refine tendsto_nhds_unique ?_ ((((((2 : ℝ) ^ (s * j) : ℝ) : ℂ) •
      littlewoodPaleyBlock F φ j).continuous.tendsto _).comp hv)
    have := ((Lp.toTemperedDistributionCLM F volume p).continuous.tendsto _).comp
      ((tendsto_pi_nhds.1 ((lp.uniformContinuous_coe.continuous.tendsto w).comp hw)) j)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, Lp.toTemperedDistributionCLM_apply,
      FunLike.coe_smul, Pi.smul_apply]
    exact (u n).coe_weightedBlocks_apply j
  refine ⟨⟨_, w, hwv⟩, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  refine (tendsto_iff_norm_sub_tendsto_zero.1 hw).congr fun n ↦ ?_
  rw [← norm_weightedBlocks, weightedBlocks_sub, Function.comp_apply]

end Complete

section Inclusion

variable {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')]

/-- For `s' ≤ s` and `q ≤ q'`, the `B^{s'}_{p,q'}` norm of a distribution is at most its
`B^s_{p,q}` norm. -/
private theorem norm_le_of_toDistr_eq_of_le (hs : s' ≤ s) (hq : q ≤ q')
    {u : BesovSpace F φ s p q} {v : BesovSpace F φ s' p q'} (h : u.toDistr = v.toDistr) :
    ‖v‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  set w : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q' :=
    ⟨u.weightedBlocks, (lp.memℓp u.weightedBlocks).of_exponent_ge hq⟩
  -- The entries of the anonymous `lp` element `w` are those of `u.weightedBlocks` by definition:
  -- `lp` coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
  have hw : ∀ j, w j = u.weightedBlocks j := fun _ ↦ rfl
  calc _ ≤ ‖w‖ := lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ by
          rw [hw j, norm_weightedBlocks_apply, norm_weightedBlocks_apply,
            block_eq_of_toDistr_eq h j]
          gcongr
          exact one_le_two
    _ ≤ _ := lp.norm_le_norm_of_exponent_le (zero_lt_one.trans_le Fact.out).ne' hq hw

/-- For `s' < s`, the `B^{s'}_{p,q'}` norm of a distribution is at most `(1 - 2^{s' - s})⁻¹` times
its `B^s_{p,q}` norm: the weighted blocks for `s'` decay geometrically. -/
private theorem norm_le_of_toDistr_eq_of_lt (hs : s' < s) {u : BesovSpace F φ s p q}
    {v : BesovSpace F φ s' p q'} (h : u.toDistr = v.toDistr) :
    ‖v‖ ≤ (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ := by
  rw [← norm_weightedBlocks, mul_comm]
  refine lp.norm_le_of_norm_le_geometric (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hs)) fun j ↦ ?_
  rw [norm_weightedBlocks_apply, ← block_eq_of_toDistr_eq h, two_rpow_mul_natCast_eq s s' j,
    mul_assoc, mul_comm ‖u‖]
  exact mul_le_mul_of_nonneg_left (rpow_mul_norm_block_le u j) (by positivity)

variable (F φ p) in
/-- **Monotonicity of the Besov scale.** For `s' ≤ s` and `q ≤ q'`, `B^s_{p,q} ⊆ B^{s'}_{p,q'}`
with `‖u‖_{B^{s'}_{p,q'}} ≤ ‖u‖_{B^s_{p,q}}`. -/
def inclusion (hs : s' ≤ s) (hq : q ≤ q') : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := (u.memBesov_toDistr.mono hs hq).toBesovSpace
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    1 fun _ ↦ (norm_le_of_toDistr_eq_of_le hs hq rfl).trans_eq (one_mul _).symm

@[simp]
theorem toDistr_inclusion (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    (inclusion F φ p hs hq u).toDistr = u.toDistr := by rfl

@[simp]
theorem block_inclusion (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) (j : ℕ) :
    (inclusion F φ p hs hq u).block j = u.block j :=
  block_eq_of_toDistr_eq (toDistr_inclusion hs hq u) j

theorem norm_inclusion_le (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace F φ s p q) :
    ‖inclusion F φ p hs hq u‖ ≤ ‖u‖ :=
  norm_le_of_toDistr_eq_of_le hs hq (toDistr_inclusion hs hq u).symm

variable (F φ p q q') in
/-- **Strict monotonicity of the Besov scale.** For `s' < s` and arbitrary fine indices `q, q'`,
`B^s_{p,q} ⊆ B^{s'}_{p,q'}` with `‖u‖_{B^{s'}_{p,q'}} ≤ (1 - 2^{s' - s})⁻¹ ‖u‖_{B^s_{p,q}}`: a
loss of smoothness absorbs every change of the fine index. -/
def inclusionOfLT (hs : s' < s) : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q' :=
  LinearMap.mkContinuous
    { toFun u := (u.memBesov_toDistr.of_lt hs (zero_lt_one.trans_le Fact.out).ne').toBesovSpace
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl }
    (1 - 2 ^ (s' - s))⁻¹ fun _ ↦ norm_le_of_toDistr_eq_of_lt hs rfl

@[simp]
theorem toDistr_inclusionOfLT (hs : s' < s) (u : BesovSpace F φ s p q) :
    (inclusionOfLT F φ p q q' hs u).toDistr = u.toDistr := by rfl

@[simp]
theorem block_inclusionOfLT (hs : s' < s) (u : BesovSpace F φ s p q) (j : ℕ) :
    (inclusionOfLT F φ p q q' hs u).block j = u.block j :=
  block_eq_of_toDistr_eq (toDistr_inclusionOfLT hs u) j

theorem norm_inclusionOfLT_le (hs : s' < s) (u : BesovSpace F φ s p q) :
    ‖inclusionOfLT F φ p q q' hs u‖ ≤ (1 - 2 ^ (s' - s))⁻¹ * ‖u‖ :=
  norm_le_of_toDistr_eq_of_lt hs (toDistr_inclusionOfLT hs u).symm

end Inclusion

section Bernstein

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- For `p ≤ r` there is `C`, independent of `s` and `q`, such that the
`B^{s - n (1/p - 1/r)}_{r,q}` norm of a distribution is at most `C` times its `B^s_{p,q}` norm. -/
private theorem exists_norm_le_of_toDistr_eq_of_exponent_le (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] {u : BesovSpace F φ s p q}
      {v : BesovSpace F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q},
      u.toDistr = v.toDistr → ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hB⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le_of_le (F := F) φ hpr
  refine ⟨C, hC, ?_⟩
  intro s q _ u v h
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  calc ‖v.weightedBlocks‖ ≤ ‖(C : ℂ) • u.weightedBlocks‖ :=
        lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ ?_
    _ = C * ‖u.weightedBlocks‖ := by
        rw [lp.norm_const_smul (zero_lt_one.trans_le Fact.out).ne', Complex.norm_of_nonneg hC]
  -- The block `Δⱼ v = Δⱼ u` is the `Lʳ` function given by Bernstein's inequality.
  obtain ⟨g, hg, hgf⟩ := hB j u.toDistr (u.block j) (coe_block u j).symm
  have hvg : v.block j = g := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block, ← h, hg]
  rw [norm_weightedBlocks_apply, hvg, lp.coeFn_smul, Pi.smul_apply, norm_smul,
    Complex.norm_of_nonneg hC, norm_weightedBlocks_apply,
    ← Real.rpow_sub_mul_mul_rpow_mul two_pos s (Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) j]
  exact (mul_le_mul_of_nonneg_left hgf (by positivity)).trans_eq (by ring)

variable [Fact (1 ≤ q)]

variable (F φ q) in
/-- **The Bernstein embedding.** For `p ≤ r`, `B^s_{p,q} ⊆ B^{s - n (1/p - 1/r)}_{r,q}`
continuously, where `n` is the dimension of `E` and `1/∞ = 0`. The norm of the inclusion is
bounded independently of `s` and `q` (`TauCeti.BesovSpace.exists_norm_inclusionOfExponentLE_le`).
At the level of the predicate this is `TemperedDistribution.MemBesov.mono_exponent`. -/
def inclusionOfExponentLE (hpr : p ≤ r) :
    BesovSpace F φ s p q →L[ℂ]
      BesovSpace F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.mono_exponent hpr).toBesovSpace
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl } <| by
    obtain ⟨C, -, hC⟩ := exists_norm_le_of_toDistr_eq_of_exponent_le (F := F) (φ := φ) hpr
    exact ⟨C, fun _ ↦ hC rfl⟩

@[simp]
theorem toDistr_inclusionOfExponentLE (hpr : p ≤ r) (u : BesovSpace F φ s p q) :
    (inclusionOfExponentLE F φ q hpr u).toDistr = u.toDistr := by rfl

variable (F φ) in
/-- **The Bernstein embedding is bounded uniformly in `s` and `q`.** For `p ≤ r` there is `C`,
depending only on `E`, `F`, `p`, `r` and `φ`, with
`‖u‖_{B^{s - n (1/p - 1/r)}_{r,q}} ≤ C ‖u‖_{B^s_{p,q}}` for every `s`, every `q ≥ 1` and every
`u ∈ B^s_{p,q}`. -/
theorem exists_norm_inclusionOfExponentLE_le (hpr : p ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : BesovSpace F φ s p q),
      ‖inclusionOfExponentLE F φ q hpr u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_le_of_toDistr_eq_of_exponent_le (F := F) (φ := φ) hpr
  exact ⟨C, hC, fun u ↦ h (toDistr_inclusionOfExponentLE hpr u).symm⟩

end Bernstein

section SingleBlock

variable [Fact (1 ≤ q)]

/-- **A Schwartz function carried by one block.** If on the support of the Fourier transform of a
Schwartz function `f` the piece `ψⱼ` equals `1` and every other piece vanishes, then `f` lies in
every Besov space `B^s_{p,q}`, with norm `2^{js} ‖f‖_p`. -/
theorem exists_toDistr_eq_and_norm_eq (j : ℕ) (f : 𝓢(E, F))
    (hf : ∀ k ξ, 𝓕 f ξ ≠ 0 → φ.inhomogeneousLittlewoodPaley k ξ = if k = j then 1 else 0) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = f ∧ ‖v‖ = 2 ^ (s * j) * ‖f.toLp p‖ := by
  refine ⟨⟨f, lp.single q j ((((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f.toLp p), fun k ↦ ?_⟩, rfl, ?_⟩
  · rw [littlewoodPaleyBlock_toTemperedDistributionCLM_eq_ite φ hf]
    split_ifs with hk
    · subst hk
      rw [lp.single_apply_self, Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_toLp_eq]
    · rw [lp.single_apply_ne _ _ _ hk, smul_zero, Lp.toTemperedDistribution_zero]
  · rw [← norm_weightedBlocks, lp.norm_single (zero_lt_one.trans_le Fact.out), norm_smul,
      Complex.norm_of_nonneg (by positivity)]

/-- **Low frequencies.** A Schwartz function whose Fourier transform vanishes outside the ball of
radius `φ.rIn`, where `φ = 1`, lies in every Besov space `B^s_{p,q}` with norm `‖f‖_p`,
independently of `s`. -/
theorem exists_toDistr_eq_and_norm_eq_of_norm_le (f : 𝓢(E, F))
    (hf : ∀ ξ, 𝓕 f ξ ≠ 0 → ‖ξ‖ ≤ φ.rIn) :
    ∃ v : BesovSpace F φ s p q, v.toDistr = f ∧ ‖v‖ = ‖f.toLp p‖ := by
  have hf' : ∀ k ξ, 𝓕 f ξ ≠ 0 → φ.inhomogeneousLittlewoodPaley k ξ = if k = 0 then 1 else 0 := by
    rintro (_ | k) ξ hξ
    · simpa using φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (hf ξ hξ))
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      exact φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le <| (hf ξ hξ).trans <|
        le_mul_of_one_le_left φ.rIn_pos.le (one_le_pow₀ one_le_two)
  simpa using exists_toDistr_eq_and_norm_eq (s := s) (q := q) 0 f hf'

end SingleBlock

section ChangeOfBump

variable [Fact (1 ≤ q)]

/-- The Besov norms built from two bump functions are comparable: there is `C`, depending only on
`φ`, `φ'` and `s`, with `‖u‖_{B'} ≤ C ‖u‖_B`. -/
private theorem exists_norm_toBesovSpace_of_bump_le (φ' : ContDiffBump (0 : E)) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q,
      ‖(u.memBesov_toDistr.of_bump φ').toBesovSpace‖ ≤ C * ‖u‖ := by
  obtain ⟨K, L, hK, hKL⟩ := exists_littlewoodPaleyBlock_eq_and_le (F := F) φ φ' s
  refine ⟨K * (2 * L), fun u ↦ ?_⟩
  obtain ⟨f', hf', hle⟩ := hKL u.block fun k ↦ (coe_block u k).symm
  -- The weighted block norms of `u`, and their window sums, as elements of `ℓ^q`.
  set b : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun k ↦ ‖u.weightedBlocks k‖, (lp.memℓp _).norm⟩
  set w : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), b k, (lp.memℓp b).sum_Ico_sub_add L⟩
  -- The entries of the anonymous `lp` elements `b` and `w` are their defining sequences by
  -- definition: `lp` coerces through `Subtype.val` and has no lemma evaluating an anonymous
  -- constructor.
  have hw (j : ℕ) : w j = ∑ k ∈ Finset.Ico (j - L) (j + L), ‖u.weightedBlocks k‖ := rfl
  have hp : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hb : ‖b‖ ≤ ‖u‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hp fun k ↦ (norm_norm _).le
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq f' (K • w) hf'
    fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hw]
      simpa only [norm_weightedBlocks_apply] using hle j
  rw [← ext (hv.trans (MemBesov.toDistr_toBesovSpace _).symm)]
  calc ‖v‖ ≤ ‖K • w‖ := hvn
    _ = K * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hK]
    _ ≤ K * (2 * L * ‖b‖) := by
        gcongr
        exact lp.norm_le_of_forall_eq_sum_Ico_sub_add L fun _ ↦ rfl
    _ ≤ K * (2 * L) * ‖u‖ := by rw [mul_assoc K]; gcongr

variable (F) in
/-- **Independence of the bump function.** The Besov spaces `B^s_{p,q}` built from the
Littlewood–Paley partitions of two bump functions `φ` and `φ'` consist of the same tempered
distributions, with equivalent norms: the identity on tempered distributions is an isomorphism of
normed spaces between them (Triebel, *Theory of Function Spaces*, Section 2.3.2). -/
def bumpEquiv (φ φ' : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ' s p q :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun u := (u.memBesov_toDistr.of_bump φ').toBesovSpace
      invFun v := (v.memBesov_toDistr.of_bump φ).toBesovSpace
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl
      left_inv _ := ext rfl
      right_inv _ := ext rfl }
    _ _ (exists_norm_toBesovSpace_of_bump_le φ').choose_spec
    (exists_norm_toBesovSpace_of_bump_le φ).choose_spec

@[simp]
theorem toDistr_bumpEquiv (φ' : ContDiffBump (0 : E)) (u : BesovSpace F φ s p q) :
    (bumpEquiv F φ φ' s p q u).toDistr = u.toDistr := by rfl

@[simp]
theorem bumpEquiv_symm (φ' : ContDiffBump (0 : E)) :
    (bumpEquiv F φ φ' s p q).symm = bumpEquiv F φ' φ s p q := by
  ext u
  rfl

end ChangeOfBump

end BesovSpace

end TauCeti
