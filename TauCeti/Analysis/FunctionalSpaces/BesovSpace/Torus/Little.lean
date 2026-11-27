/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic

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
(`TauCeti.UnitAddTorus.BesovSpace.isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp`):
each weighted block is at most the norm, so that the weighted blocks are equicontinuous. It holds
for trigonometric polynomials, which have only finitely many nonzero blocks. Conversely, let
`S_N c = ∑_{i ≤ N} ψᵢ c` be the smooth truncation of the coefficients, a trigonometric polynomial.
Since `∑ᵢ ψᵢ = 1` and `ψₖ ψᵢ = 0` for `|i - k| ≥ L`, the block `Δₖ (c - S_N c)` is the finite sum
`∑_{N < i < k + L} Δₖ (ψᵢ c)`, whose nonzero terms have `|i - k| < L` and are bounded in `Lᵖ` by
`‖Δᵢ c‖_p`, uniformly in the indices. So `‖c - S_N c‖_{B^s_{p,∞}}` is at most a constant times
`sup_{i > N} 2^{is} ‖Δᵢ c‖_p`, which tends to `0` when the weighted blocks of `c` do.

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
  rw [← Complex.ofReal_sum, φ.sum_inhomogeneousLittlewoodPaley_range_eq_zero_of_le_norm hlt.le,
    Complex.ofReal_zero, zero_mul]

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
  obtain ⟨C, -, hC⟩ := exists_norm_littlewoodPaleyBlockLp_mul_le φ
  refine ⟨max C 0 * 2 ^ (|s| * L) * (2 * L), by positivity, fun p _ N ε c hε hc k ↦ ?_⟩
  -- The remainder block is the sum over the window `k - L ≤ i < k + L` of the terms `Δₖ (ψᵢ c)`
  -- with `N < i`: the terms with `i < k - L` vanish, as then `ψᵢ ψₖ = 0`.
  have hsum : littlewoodPaleyBlockLp φ p k (c - truncation φ N c) =
      ∑ i ∈ Finset.Ico (k - L) (k + L), if N < i then littlewoodPaleyBlockLp φ p k
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley i (latticePoint n) : ℂ) * c n) else 0 := by
    rw [littlewoodPaleyBlockLp_sub_truncation (fun i hi ξ ↦ hL k i hi ξ), ← Finset.sum_filter]
    refine (Finset.sum_subset (fun i hi ↦ ?_) fun i hi hi' ↦ ?_).symm
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
      omega
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hi hi'
      exact littlewoodPaleyBlockLp_mul_eq_zero (fun ξ ↦ by
        rw [mul_comm]; exact hL i k (by omega) ξ) c
  rw [hsum]
  refine (TauCeti.two_rpow_mul_norm_sum_Ico_le s (C := C)
    (x := fun i ↦ if N < i then littlewoodPaleyBlockLp φ p i c else 0) (fun i ↦ ?_) k L).trans ?_
  · split_ifs
    exacts [hC φ p k i c, by rw [norm_zero, mul_zero]]
  -- Each weighted term is at most `ε`, and the window has at most `2 L` indices.
  rw [mul_assoc _ (2 * (L : ℝ))]
  gcongr
  calc ∑ i ∈ Finset.Ico (k - L) (k + L),
        2 ^ (s * i) * ‖if N < i then littlewoodPaleyBlockLp φ p i c else 0‖
      ≤ ∑ _i ∈ Finset.Ico (k - L) (k + L), ε := Finset.sum_le_sum fun i _ ↦ by
        split_ifs with hi
        exacts [hc i hi, by rwa [norm_zero, mul_zero]]
    _ ≤ 2 * L * ε := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        gcongr
        exact_mod_cast (by omega : k + L - (k - L) ≤ 2 * L)

namespace BesovSpace

/-! ### Decay of the weighted blocks -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The set of `u ∈ B^s_{p,q}(𝕋ᵈ)` whose weighted blocks `2^{js} ‖Δⱼ u‖_p` vanish at high frequency
is closed in `B^s_{p,q}(𝕋ᵈ)`: each weighted block is at most the norm. -/
theorem isClosed_setOf_tendsto_rpow_mul_norm_littlewoodPaleyBlockLp :
    IsClosed {u : BesovSpace φ s p q |
      Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖) atTop
        (𝓝 0)} := by
  -- Each weighted block is `1`-Lipschitz, being at most the norm, so they are equicontinuous.
  refine (Metric.equicontinuous_of_continuity_modulus id tendsto_id
    (fun (j : ℕ) (u : BesovSpace φ s p q) ↦
      (2 : ℝ) ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j u.coeff‖)
    fun u v j ↦ ?_).isClosed_setOfPred_tendsto continuous_const
  have h := rpow_mul_norm_littlewoodPaleyBlockLp_le (u - v) j
  rw [coeff_sub, map_sub] at h
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity), id, dist_eq_norm]
  exact (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by positivity)).trans h

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
  have hv : v.coeff = truncation φ N u.coeff := rfl
  refine ⟨v, finite_support_truncation N u.coeff, ?_⟩
  rw [norm_eq_ciSup, coeff_sub, hv]
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
