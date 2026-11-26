/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The periodic little Besov spaces

Trigonometric polynomials, the formal Fourier series `c : ℤᵈ → ℂ` with finitely many nonzero
coefficients, lie in every periodic Besov space (`TauCeti.UnitAddTorus.memBesov_of_finite_support`).
Their closure in `B^s_{p,∞}(𝕋ᵈ)` is the **periodic little Besov space** `b^s_{p,∞}(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.BesovSpace.littleBesov`); at `p = ∞` it is the periodic little
Hölder–Zygmund space `c^s(𝕋ᵈ)`, the closure of the trigonometric polynomials in
`𝒞^s(𝕋ᵈ) = B^s_{∞,∞}(𝕋ᵈ)`. It is a Banach space, and it is the space on which the heat
semigroup is strongly continuous
(`TauCeti.UnitAddTorus.BesovSpace.tendsto_heatSemigroup_iff_mem_littleBesov`).

For every `1 ≤ p ≤ ∞`, the elements of `b^s_{p,∞}(𝕋ᵈ)` are exactly those whose weighted blocks
vanish at high frequency (`TauCeti.UnitAddTorus.BesovSpace.mem_littleBesov_iff_tendsto`):

`u ∈ b^s_{p,∞}(𝕋ᵈ)` if and only if `2^{js} ‖Δⱼ u‖_p → 0`.

On `ℝᵈ` the same holds for `p < ∞` (`TauCeti.BesovSpace.mem_littleBesov_iff_tendsto`), while at
`p = ∞` the blocks must in addition be uniform limits of Schwartz functions. On the torus every
block is a trigonometric polynomial, so no such condition arises and the characterization holds
at `p = ∞` as well.

## The argument

The decay of the weighted blocks is a closed condition
(`TauCeti.UnitAddTorus.BesovSpace.isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp`,
proved as `TauCeti.BesovSpace.isClosed_setOf_tendsto_rpow_mul_norm_block` is on `ℝᵈ`), since each
weighted block is at most the norm, and it holds for trigonometric polynomials, which
have only finitely many nonzero blocks. Conversely, let `S_N c = ∑_{i ≤ N} ψᵢ c` be the smooth
truncation of the coefficients, a trigonometric polynomial. Since `∑ᵢ ψᵢ = 1` and `ψₖ ψᵢ = 0` for
`|i - k| ≥ L`, the block `Δₖ (c - S_N c)` is the finite sum `∑_{N < i < k + L} Δₖ (ψᵢ c)`, whose
nonzero terms have `|i - k| < L` and are bounded in `Lᵖ` by `‖Δᵢ c‖_p`, uniformly in the indices.
So `‖c - S_N c‖_{B^s_{p,∞}}` is at most a constant times `sup_{i > N} 2^{is} ‖Δᵢ c‖_p`, which tends
to `0` when the weighted blocks of `c` do.

## Main declarations

* `TauCeti.UnitAddTorus.BesovSpace.isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp`:
  the decay of the weighted blocks is a closed condition in `B^s_{p,q}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.BesovSpace.littleBesov`: the periodic little Besov space, a closed
  subspace of `B^s_{p,∞}(𝕋ᵈ)` containing every trigonometric polynomial
  (`TauCeti.UnitAddTorus.BesovSpace.mem_littleBesov_of_finite_support`).
* `TauCeti.UnitAddTorus.BesovSpace.littleBesov_le`: it is the smallest closed subspace containing
  the trigonometric polynomials, which are dense in it
  (`TauCeti.UnitAddTorus.BesovSpace.dense_setOf_finite_support_coeff`).
* `TauCeti.UnitAddTorus.BesovSpace.bumpEquiv_mem_littleBesov_iff` and
  `TauCeti.UnitAddTorus.BesovSpace.littleBesovBumpEquiv`: it does not depend on the bump `φ`.
* `TauCeti.UnitAddTorus.BesovSpace.exists_norm_sub_le_of_forall_lt_rpow_mul_norm_le`: the
  approximation by trigonometric polynomials, `‖u - v‖_{B^s_{p,∞}} ≤ K ε` for some trigonometric
  polynomial `v` whenever `2^{is} ‖Δᵢ u‖_p ≤ ε` for all `i > N`.
* `TauCeti.UnitAddTorus.BesovSpace.mem_littleBesov_iff_tendsto`: the characterization by the decay
  of the weighted blocks, for every `1 ≤ p ≤ ∞`.

## References

* H. Triebel, *Theory of Function Spaces*, Section 2.3.3 (the closure of the smooth functions in
  `B^s_{p,∞}`) and Chapter 9 (periodic spaces).
* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (periodic distributions and the periodic Besov spaces).
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Besov spaces are built on `Lᵖ` for the product of the Haar probability measures on
-- the circle factors, given by this instance; use it here so that the blocks below live on the
-- same spaces.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {φ : ContDiffBump (0 : EuclideanSpace ℝ d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Blocks of truncated coefficients -/

/-- The block `Δₖ (ψᵢ c)` vanishes when the pieces `ψᵢ` and `ψₖ` have disjoint supports. -/
private theorem littlewoodPaleyBlockLp_mul_eq_zero {i k : ℕ}
    (h : ∀ ξ, φ.inhomogeneousLittlewoodPaley k ξ * φ.inhomogeneousLittlewoodPaley i ξ = 0)
    (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p k
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n) = 0 := by
  rw [← map_zero (littlewoodPaleyBlockLp φ p k)]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  rw [Pi.zero_apply, mul_zero, ← mul_assoc, ← Complex.ofReal_mul, h, Complex.ofReal_zero,
    zero_mul]

variable (φ) in
/-- The **smooth truncation** `S_N c = ∑_{i ≤ N} ψᵢ c` of a formal Fourier series, with
coefficients `(∑_{i ≤ N} ψᵢ(n)) c(n) = φ(2^{-N} n) c(n)`: a trigonometric polynomial. -/
private def truncation (N : ℕ) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ :=
  fun n ↦ (∑ i ∈ Finset.range (N + 1), φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n

/-- The smooth truncation has finitely many nonzero coefficients. -/
private theorem finite_support_truncation (N : ℕ) (c : (d → ℤ) → ℂ) :
    (Function.support (truncation φ N c)).Finite := by
  refine (finite_setOf_norm_latticePoint_le (2 ^ N * φ.rOut)).subset fun n hn ↦ ?_
  by_contra hlt
  simp only [Set.mem_ofPred_eq, not_le] at hlt
  refine hn ?_
  simp only [truncation]
  rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range, φ.zero_of_le_dist,
    Complex.ofReal_zero, zero_mul]
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
    le_inv_mul_iff₀ (by positivity)]
  exact hlt.le

/-- The blocks of the remainder `c - S_N c` of the smooth truncation are the finite sums
`Δₖ (c - S_N c) = ∑_{N < i < k + L} Δₖ (ψᵢ c)`, when `ψₖ ψᵢ = 0` for `i ≥ k + L`. -/
private theorem littlewoodPaleyBlockLp_sub_truncation {L k : ℕ}
    (hL : ∀ i, k + L ≤ i → ∀ ξ,
      φ.inhomogeneousLittlewoodPaley k ξ * φ.inhomogeneousLittlewoodPaley i ξ = 0)
    (N : ℕ) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p k (c - truncation φ N c) =
      ∑ i ∈ Finset.Ico (N + 1) (k + L), littlewoodPaleyBlockLp φ p k
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n) := by
  rw [← map_sum]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  have h := congrArg (fun x : ℝ ↦ (x : ℂ) * c n)
    (φ.inhomogeneousLittlewoodPaley_mul_one_sub_sum_range (ξ := latticePoint n)
      (fun i hi ↦ hL i hi _) N)
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum]
    at h
  simp only [truncation, Pi.sub_apply, Finset.sum_apply, ← Finset.sum_mul]
  linear_combination h

/-- **A near-diagonal term of the remainder.** If `ψᵢ ψₖ = 0` for `|i - k| ≥ L` and
`‖Δₖ (ψᵢ c)‖_p ≤ C ‖Δᵢ c‖_p` for all indices, then the term `Δₖ (ψᵢ c)`, weighted at `k`, vanishes
unless `k < i + L`, and is then at most `C 2^{|s| L} 2^{is} ‖Δᵢ c‖_p` when `i < k + L`. -/
private theorem rpow_mul_norm_littlewoodPaleyBlockLp_mul_le {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {C : ℝ} (hC : ∀ (j k : ℕ) (c : (d → ℤ) → ℂ), ‖littlewoodPaleyBlockLp φ p j
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n)‖ ≤
        C * ‖littlewoodPaleyBlockLp φ p k c‖)
    {i k : ℕ} (hik : i < k + L) (c : (d → ℤ) → ℂ) :
    2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n)‖ ≤
      if k < i + L then C * 2 ^ (|s| * L) * (2 ^ (s * i) * ‖littlewoodPaleyBlockLp φ p i c‖)
      else 0 := by
  split_ifs with hki
  · -- `|k - i| ≤ L`, so the weight at `k` is at most `2^{|s| L}` times the weight at `i`.
    have hw : (2 : ℝ) ^ (s * k) ≤ 2 ^ (|s| * L) * 2 ^ (s * i) := by
      rw [← Real.rpow_add two_pos]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      have h₁ : (i : ℝ) ≤ k + L := by exact_mod_cast hik.le
      have h₂ : (k : ℝ) ≤ i + L := by exact_mod_cast hki.le
      have hd : |(k : ℝ) - i| ≤ L := abs_le.2 ⟨by linarith, by linarith⟩
      have := abs_mul s ((k : ℝ) - i) ▸ le_abs_self (s * ((k : ℝ) - i))
      nlinarith [abs_nonneg s, abs_nonneg ((k : ℝ) - i)]
    calc 2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n)‖
        ≤ 2 ^ (|s| * L) * 2 ^ (s * i) * (C * ‖littlewoodPaleyBlockLp φ p i c‖) := by
          gcongr
          exact hC k i c
      _ = C * 2 ^ (|s| * L) * (2 ^ (s * i) * ‖littlewoodPaleyBlockLp φ p i c‖) := by ring
  · rw [littlewoodPaleyBlockLp_mul_eq_zero (fun ξ ↦ by
      rw [mul_comm]; exact hL i k (by omega) ξ), norm_zero, mul_zero]

variable (φ s) in
/-- **The truncation estimate.** There is `K ≥ 0`, depending only on `φ` and `s`, such that for
every `1 ≤ p ≤ ∞`, every `N`, every `ε ≥ 0` and every formal Fourier series `c` whose weighted
blocks beyond `N` are at most `ε`, `2^{is} ‖Δᵢ c‖_p ≤ ε` for `i > N`, every weighted block of the
remainder `c - S_N c` of the smooth truncation is at most `K ε`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_sub_truncation_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) {ε : ℝ} (c : (d → ℤ) → ℂ),
      0 ≤ ε → (∀ i, N < i → 2 ^ (s * i) * ‖littlewoodPaleyBlockLp φ p i c‖ ≤ ε) →
      ∀ k : ℕ, 2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k (c - truncation φ N c)‖ ≤ K * ε := by
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  obtain ⟨C, hC0, hC⟩ := exists_norm_littlewoodPaleyBlockLp_mul_le φ
  refine ⟨2 * L * (C * 2 ^ (|s| * L)), by positivity, fun p _ N ε c hε hc k ↦ ?_⟩
  rw [littlewoodPaleyBlockLp_sub_truncation (fun i hi ξ ↦ hL k i hi ξ)]
  -- Only the indices `N < i < k + L` with `k < i + L` contribute, each with at most
  -- `C 2^{|s| L} ε`; there are at most `2 L` of them.
  set S := (Finset.Ico (N + 1) (k + L)).filter fun i ↦ k < i + L
  have hterm : ∀ i ∈ Finset.Ico (N + 1) (k + L),
      2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n)‖ ≤
        if k < i + L then C * 2 ^ (|s| * L) * ε else 0 := fun i hi ↦ by
    rw [Finset.mem_Ico] at hi
    refine (rpow_mul_norm_littlewoodPaleyBlockLp_mul_le hL (fun j k c ↦ hC φ p j k c) hi.2
      c).trans ?_
    split_ifs
    exacts [by gcongr; exact hc i (by omega), le_rfl]
  have hcard : (S.card : ℝ) ≤ 2 * L := by
    have hsub : S ⊆ Finset.Ico (k + 1 - L) (k + L) := fun i hi ↦ by
      simp only [S, Finset.mem_filter, Finset.mem_Ico] at hi ⊢
      omega
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico] at h
    exact_mod_cast h.trans (by omega : k + L - (k + 1 - L) ≤ 2 * L)
  calc 2 ^ (s * k) * ‖∑ i ∈ Finset.Ico (N + 1) (k + L), littlewoodPaleyBlockLp φ p k
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n)‖
      ≤ ∑ i ∈ Finset.Ico (N + 1) (k + L), 2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n)‖ := by
        rw [← Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Ico (N + 1) (k + L), if k < i + L then C * 2 ^ (|s| * L) * ε else 0 :=
        Finset.sum_le_sum hterm
    _ = S.card * (C * 2 ^ (|s| * L) * ε) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * L * (C * 2 ^ (|s| * L) * ε) := by gcongr
    _ = 2 * L * (C * 2 ^ (|s| * L)) * ε := by ring

namespace BesovSpace

/-! ### Decay of the weighted blocks -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The set of `u ∈ B^s_{p,q}(𝕋ᵈ)` whose weighted blocks `2^{js} ‖Δⱼ u‖_p` vanish at high frequency
is closed in `B^s_{p,q}(𝕋ᵈ)`: each weighted block is at most the norm. -/
theorem isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp :
    IsClosed {u : BesovSpace φ s p q |
      Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖) atTop
        (𝓝 0)} := by
  refine closure_subset_iff_isClosed.mp fun u hu ↦ Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨v, hv, hvu⟩ := Metric.mem_closure_iff.1 hu (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hvu
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hv (ε / 2) (half_pos hε)
  refine ⟨J, fun j hj ↦ ?_⟩
  have hvj := hJ j hj
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hvj ⊢
  have hsub := rpow_mul_norm_littlewoodPaleyBlockLp_le (u - v) j
  rw [coeff_sub, map_sub] at hsub
  calc (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖
      ≤ 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff -
          littlewoodPaleyBlockLp φ p j v.coeff‖ +
        2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j v.coeff‖ := by
        rw [← mul_add]; gcongr; exact norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hsub.trans hvu.le) hvj
    _ = ε := add_halves ε

/-! ### The periodic little Besov space -/

variable (φ s p) in
/-- The **periodic little Besov space** `b^s_{p,∞}(𝕋ᵈ)`: the closure of the trigonometric
polynomials, the formal Fourier series with finitely many nonzero coefficients, in
`B^s_{p,∞}(𝕋ᵈ)`. At `p = ∞` it is the periodic little Hölder–Zygmund space `c^s(𝕋ᵈ)`. Its elements
are those whose weighted blocks `2^{js} ‖Δⱼ u‖_p` vanish at high frequency
(`TauCeti.UnitAddTorus.BesovSpace.mem_littleBesov_iff_tendsto`). -/
def littleBesov : Submodule ℂ (BesovSpace φ s p ∞) :=
  Submodule.topologicalClosure
    { carrier := {u | (Function.support u.coeff).Finite}
      add_mem' hu hv := (hu.union hv).subset (Function.support_add _ _)
      zero_mem' := by simp
      smul_mem' a _ hu := hu.subset (Function.support_const_smul_subset a _) }

/-- The periodic little Besov space is closed in `B^s_{p,∞}(𝕋ᵈ)`. -/
instance isClosed_littleBesov : IsClosed (littleBesov φ s p : Set (BesovSpace φ s p ∞)) :=
  Submodule.isClosed_topologicalClosure _

/-- The periodic little Besov space is complete, as a closed subspace of `B^s_{p,∞}(𝕋ᵈ)`. -/
instance : CompleteSpace (littleBesov φ s p) :=
  isClosed_littleBesov.completeSpace_coe

/-- As a set, the periodic little Besov space is the closure of the trigonometric polynomials. -/
theorem coe_littleBesov : (littleBesov φ s p : Set (BesovSpace φ s p ∞)) =
    closure {u | (Function.support u.coeff).Finite} :=
  Submodule.topologicalClosure_coe _

/-- **Trigonometric polynomials lie in the periodic little Besov space.** -/
theorem mem_littleBesov_of_finite_support {u : BesovSpace φ s p ∞}
    (hu : (Function.support u.coeff).Finite) : u ∈ littleBesov φ s p :=
  Submodule.le_topologicalClosure _ hu

/-- **Minimality.** The periodic little Besov space is contained in every closed subspace of
`B^s_{p,∞}(𝕋ᵈ)` containing the trigonometric polynomials. -/
theorem littleBesov_le {S : Submodule ℂ (BesovSpace φ s p ∞)}
    (hS : IsClosed (S : Set (BesovSpace φ s p ∞)))
    (h : ∀ u : BesovSpace φ s p ∞, (Function.support u.coeff).Finite → u ∈ S) :
    littleBesov φ s p ≤ S :=
  Submodule.topologicalClosure_minimal _ (fun u hu ↦ h u hu) hS

/-- **Density of the trigonometric polynomials.** The trigonometric polynomials are dense in the
periodic little Besov space. -/
theorem dense_setOf_finite_support_coeff :
    Dense {v : littleBesov φ s p | (Function.support (v : BesovSpace φ s p ∞).coeff).Finite} := by
  refine Topology.IsInducing.subtypeVal.dense_iff.2 fun v ↦ ?_
  have hv : (v : BesovSpace φ s p ∞) ∈
      closure {u : BesovSpace φ s p ∞ | (Function.support u.coeff).Finite} := by
    rw [← coe_littleBesov]
    exact v.property
  refine closure_mono (fun u hu ↦ ?_) hv
  exact ⟨⟨u, mem_littleBesov_of_finite_support hu⟩, hu, rfl⟩

/-- The weighted blocks of an element of the periodic little Besov space vanish at high
frequency. -/
theorem tendsto_rpow_mul_norm_littlewoodPaleyBlockLp_of_mem_littleBesov {u : BesovSpace φ s p ∞}
    (hu : u ∈ littleBesov φ s p) :
    Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖) atTop
      (𝓝 0) := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu
  -- A trigonometric polynomial lies in `B^s_{p,1}(𝕋ᵈ)`, so its weighted blocks are summable.
  exact closure_minimal (fun v hv ↦
      (memBesov_def.1 (memBesov_of_finite_support (q := 1) hv)).summable_of_one.tendsto_atTop_zero)
    isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp hu

variable (φ s) in
/-- **Approximation by trigonometric polynomials.** There is `K ≥ 0`, depending only on `φ` and
`s`, such that for every `1 ≤ p ≤ ∞`, every `N`, every `ε ≥ 0` and every `u ∈ B^s_{p,∞}(𝕋ᵈ)`
whose weighted blocks beyond `N` are at most `ε`, `2^{is} ‖Δᵢ u‖_p ≤ ε` for `i > N`, some
trigonometric polynomial `v` has `‖u - v‖ ≤ K ε`. One can take for `v` the smooth truncation
`∑_{i ≤ N} ψᵢ u`. -/
theorem exists_norm_sub_le_of_forall_lt_rpow_mul_norm_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) {ε : ℝ} (u : BesovSpace φ s p ∞),
      0 ≤ ε → (∀ i, N < i → 2 ^ (s * i) * ‖littlewoodPaleyBlockLp φ p i u.coeff‖ ≤ ε) →
      ∃ v : BesovSpace φ s p ∞, (Function.support v.coeff).Finite ∧ ‖u - v‖ ≤ K * ε := by
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_sub_truncation_le φ s
  refine ⟨K, hK0, fun p _ N ε u hε hu ↦ ?_⟩
  set v : BesovSpace φ s p ∞ :=
    ⟨truncation φ N u.coeff, memBesov_of_finite_support (finite_support_truncation N u.coeff)⟩
  refine ⟨v, finite_support_truncation N u.coeff, ?_⟩
  rw [norm_eq_ciSup]
  exact ciSup_le fun k ↦ hK p N u.coeff hε hu k

/-- **The periodic little Besov space is cut out by the decay of the weighted blocks.** For every
`1 ≤ p ≤ ∞`, `u ∈ b^s_{p,∞}(𝕋ᵈ)` if and only if `2^{js} ‖Δⱼ u‖_p → 0`. At `p = ∞` this
characterizes the periodic little Hölder–Zygmund space `c^s(𝕋ᵈ)` inside `𝒞^s(𝕋ᵈ)`. -/
theorem mem_littleBesov_iff_tendsto (u : BesovSpace φ s p ∞) :
    u ∈ littleBesov φ s p ↔
      Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖) atTop
        (𝓝 0) := by
  refine ⟨tendsto_rpow_mul_norm_littlewoodPaleyBlockLp_of_mem_littleBesov, fun hu ↦ ?_⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_sub_le_of_forall_lt_rpow_mul_norm_le φ s
  rw [← SetLike.mem_coe, coe_littleBesov, Metric.mem_closure_iff]
  intro ε hε
  -- Beyond some `N` the weighted blocks are at most `ε / (K + 1)`.
  have hδ : 0 < ε / (K + 1) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu _ hδ
  obtain ⟨v, hv, hvu⟩ := hK p N u hδ.le fun i hi ↦ by
    have := hN i hi.le
    rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.le
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm]
  calc ‖u - v‖ ≤ K * (ε / (K + 1)) := hvu
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-! ### Independence of the bump function -/

/-- `bumpEquiv` maps `b^s_{p,∞}(𝕋ᵈ)` into `b^s_{p,∞}(𝕋ᵈ)` for any other bump `φ'`: it is
continuous and keeps the coefficients, hence the trigonometric polynomials. -/
theorem bumpEquiv_mem_littleBesov (φ' : ContDiffBump (0 : EuclideanSpace ℝ d))
    {u : BesovSpace φ s p ∞} (hu : u ∈ littleBesov φ s p) :
    bumpEquiv φ φ' s p ∞ u ∈ littleBesov φ' s p := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu ⊢
  exact map_mem_closure (bumpEquiv φ φ' s p ∞).continuous hu fun v hv ↦ by
    simpa only [Set.mem_ofPred_eq, coeff_bumpEquiv] using hv

/-- **The periodic little Besov space does not depend on the bump function.** -/
@[simp]
theorem bumpEquiv_mem_littleBesov_iff (φ' : ContDiffBump (0 : EuclideanSpace ℝ d))
    {u : BesovSpace φ s p ∞} :
    bumpEquiv φ φ' s p ∞ u ∈ littleBesov φ' s p ↔ u ∈ littleBesov φ s p := by
  refine ⟨fun h ↦ ?_, bumpEquiv_mem_littleBesov φ'⟩
  have h' := bumpEquiv_mem_littleBesov φ h
  rwa [← bumpEquiv_symm, ContinuousLinearEquiv.symm_apply_apply] at h'

/-- **Equivalence of periodic little Besov norms across Littlewood–Paley partitions.** Two smooth
bump functions `φ` and `φ'` define canonically isomorphic Banach spaces `b^s_{p,∞}(𝕋ᵈ)`. -/
def littleBesovBumpEquiv (φ φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : littleBesov φ s p ≃L[ℂ] littleBesov φ' s p :=
  (bumpEquiv φ φ' s p ∞).ofSubmodules _ _ <| by
    ext v
    simp [Submodule.mem_map_equiv]

@[simp]
theorem coe_littleBesovBumpEquiv_apply (φ' : ContDiffBump (0 : EuclideanSpace ℝ d))
    (u : littleBesov φ s p) :
    (littleBesovBumpEquiv φ φ' s p u : BesovSpace φ' s p ∞) = bumpEquiv φ φ' s p ∞ u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem littleBesovBumpEquiv_symm (φ' : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    (littleBesovBumpEquiv φ φ' s p).symm = littleBesovBumpEquiv φ' φ s p :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ Subtype.ext <| by simp [littleBesovBumpEquiv]

end BesovSpace

end TauCeti.UnitAddTorus
