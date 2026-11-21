/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Analysis.Complex.Runge.Operator
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Runge.Rational
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Normed.Module.FilledIn
import TauCeti.LinearAlgebra.HermiteInterpolation
import TauCeti.Topology.ConnectedComponents

/-!
# Runge's approximation theorem and holomorphic hulls

This file proves Runge's approximation theorem in its domain-relative form on open subsets
`Ω ⊆ ℂ`: a compact subset `K ⊆ Ω` admits uniform approximation of neighbourhood-holomorphic
functions by `Ω`-holomorphic functions if and only if `(Ω, K)` is a Runge compact pair, i.e. no
connected component of `Ω \ K` is relatively compact in `Ω`
(`TauCeti.isRungeCompactPair_iff_approximation`). Together with the explicit filled compact
exhaustions `TauCeti.filledExhaustion Ω` (`TauCeti.Analysis.Normed.Module.Exhaustion`), these
equivalences provide the compact-to-global patching step for constructing global holomorphic
functions on arbitrary open plane sets.

Building on the finite-rank Runge operator (`TauCeti.IsFilledIn.exists_norm_sub_sum_smul_le` in
`TauCeti.Analysis.Complex.Runge.Operator`) and rational Runge approximation
(`TauCeti.Analysis.Complex.Runge.Rational`), the file also provides vector-valued Runge
approximation (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`) without requiring openness
of `Ω`, simple-fraction converse and equivalence without requiring compactness of `K` for the
converse, and finite-jet Hermite interpolation Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`).

From scalar Runge approximation we identify `TauCeti.holomorphicHull Ω K` with
`TauCeti.fillIn K Ω`, the union of `K` and all relatively compact connected components of `Ω \ K` in
`Ω` (`TauCeti.holomorphicHull_eq_fill`), establishing `holomorphicHull Ω K = K ↔ IsFilledIn K Ω`.
Specializing to `Ω = Set.univ` links `TauCeti.holomorphicHull Set.univ K = TauCeti.filledHull K`,
polynomial convexity in dimension one, and uniform polynomial approximation on compact sets with
connected complement.

## Main results

* `IsOpen.isRungeCompactPair_holomorphicHull`, `IsOpen.isRungeCompactPair_filledExhaustion`, and
  `IsOpen.exists_subset_interior_and_isRungeCompactPair`: holomorphic hulls of compact subsets and
  stages of `TauCeti.filledExhaustion` form Runge compact pairs with `Ω`, which absorb every compact
  subset of `Ω` into their interior.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`,
  `TauCeti.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`, and
  `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt`:
  vector-valued uniform Runge approximation without requiring `Ω` to be open, plus simple-fraction
  converse and equivalence.
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt` and
  `TauCeti.isRungeCompactPair_iff_approximation`: forward uniform Runge approximation and the full
  domain-relative Runge equivalence.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`: Runge
  approximation matching prescribed finite jets at finitely many points of `Ω`.
* `TauCeti.holomorphicHull_eq_fill` and `TauCeti.holomorphicHull_eq_self_iff_isFilledIn`:
  topological characterization of `TauCeti.holomorphicHull Ω K` for open `Ω` and compact `K ⊆ Ω`.
* `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq` and
  `TauCeti.isRungeCompactPair_iff_forall_mem_sdiff_exists_differentiableOn_one_lt_norm_le`:
  holomorphic-hull and point-separation criteria for Runge compact pairs.
* `TauCeti.holomorphicHull_univ_eq_filledHull`,
  `TauCeti.isPolynomiallyConvex_image_const_iff_isConnected_compl`, and
  `IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt`:
  specialization to `Ω = Set.univ` and the polynomial Runge theorem on `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, §11 (Theorem 11.1, Lemma 11.3, Theorem 11.7).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorems 1.3.1 and 1.3.9.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.5.
-/

public section

open Filter Metric Polynomial Set
open scoped NNReal Topology

namespace TauCeti

/-- For an open set `Ω ⊆ ℂ` and compact `K ⊆ Ω`, `holomorphicHull Ω K` forms a Runge compact pair
with `Ω`. -/
theorem _root_.IsOpen.isRungeCompactPair_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω (holomorphicHull Ω K) :=
  isRungeCompactPair_iff.mpr
    ⟨hΩ, hK.holomorphicHull hKΩ, holomorphicHull_subset_left Ω K, hΩ.isFilledIn_holomorphicHull K⟩

/-- Every stage of `TauCeti.filledExhaustion Ω` forms a Runge compact pair with an open
`Ω ⊆ ℂ`. -/
theorem _root_.IsOpen.isRungeCompactPair_filledExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    IsRungeCompactPair Ω (filledExhaustion Ω n) :=
  isRungeCompactPair_iff.mpr
    ⟨hΩ, isCompact_filledExhaustion Ω n, filledExhaustion_subset Ω n,
      hΩ.isFilledIn_filledExhaustion n⟩

/-- Every compact subset `K` of an open plane set `Ω` lies inside the interior of a compact `L`
forming a Runge compact pair `(Ω, L)`. -/
theorem _root_.IsOpen.exists_subset_interior_and_isRungeCompactPair {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ L, K ⊆ interior L ∧ IsRungeCompactPair Ω L := by
  obtain ⟨n, hn⟩ := hΩ.exists_subset_interior_filledExhaustion hK hKΩ
  exact ⟨filledExhaustion Ω n, hn, hΩ.isRungeCompactPair_filledExhaustion n⟩

/-! ### Vector-valued Runge approximation and simple-fraction converse -/

/-- **Runge's approximation theorem (vector-valued, arbitrary `Ω`).** Let `K` be a compact set
filled in `Ω ⊆ ℂ` (without requiring `Ω` to be open), and let `f : ℂ → F` be holomorphic on an
open neighbourhood `U` of `K` with values in a complex normed space `F`. For every `ε > 0` there is
a function `g : ℂ → F` holomorphic on `Ω` such that `‖f z - g z‖ < ε` for all `z ∈ K`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K Ω U : Set ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.bddAbove_image (hf.continuousOn.mono hLU).norm
  set M : ℝ := max M₀ 0
  have hM : ∀ z ∈ interior L, ‖f z‖ ≤ M := fun z hz ↦
    (hM₀ ⟨z, interior_subset hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, ζ, g, -, hg, happrox⟩ := hfill.exists_norm_sub_sum_smul_le hK hKΩ isOpen_interior
    hKL (ε := ε / (2 * (M + 1))) (by positivity)
  refine ⟨fun w ↦ ∑ i, g i w • f (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ (hg i).smul_const (f (ζ i)), fun w hw ↦ ?_⟩
  have hle := happrox f M (hf.mono (interior_subset.trans hLU)) hM w hw
  have hlt : ε / (2 * (M + 1)) * M < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [le_max_right M₀ 0]
  exact hle.trans_lt hlt

/-- **Converse of Runge's theorem.** If `Ω ⊆ ℂ` is open and every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` can be uniformly approximated on `K` by functions holomorphic on `Ω`, then `K` is
filled in `Ω`. No compactness or closedness of `K` is needed. -/
theorem isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (h : ∀ a ∈ Ω \ K, ∀ ε > 0,
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    IsFilledIn K Ω := by
  rw [isFilledIn_iff]
  rintro a ha ⟨hcpt, hsub⟩
  set C := connectedComponentIn (Ω \ K) a
  have hfr : frontier C ⊆ closure K := hΩ.frontier_connectedComponentIn_sdiff_subset_closure hsub
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall a
  set M : ℝ := max R 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨g, hg, hga⟩ := h a ha (2 * M)⁻¹ (by positivity)
  set f : ℂ → ℂ := fun z ↦ 1 - (z - a) * g z
  have hf_diff : DifferentiableOn ℂ f Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  have hf_cl : DiffContOnCl ℂ f C :=
    ⟨hf_diff.mono ((connectedComponentIn_subset _ _).trans sdiff_subset),
      hf_diff.continuousOn.mono hsub⟩
  have hf_fr : ∀ y ∈ frontier C, ‖f y‖ ≤ 1 / 2 := by
    intro y hy
    have hcont : ContinuousAt (fun z ↦ ‖f z‖ - ‖z - a‖ * (2 * M)⁻¹) y :=
      ((hf_diff.continuousOn.continuousAt (hΩ.mem_nhds (hsub hy.1))).norm).sub
        (((continuous_id.sub continuous_const).norm.mul continuous_const).continuousAt)
    have hle_K : ∀ z ∈ K, ‖f z‖ - ‖z - a‖ * (2 * M)⁻¹ ≤ 0 := by
      intro z hz
      have hza : z - a ≠ 0 := sub_ne_zero.mpr fun hza ↦ ha.2 (hza ▸ hz)
      have hfz : f z = (z - a) * ((z - a)⁻¹ - g z) := by
        simp only [f]; field_simp [hza]
      rw [hfz, norm_mul]
      linarith [mul_le_mul_of_nonneg_left (hga z hz).le (norm_nonneg (z - a))]
    have hy_le : ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ := by
      have hnb : (𝓝[K] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hfr hy)
      have h0 := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall hle_K)
      linarith
    have hyM : ‖y - a‖ ≤ M :=
      (dist_eq_norm y a ▸ mem_closedBall.mp (hR hy.1)).trans (le_max_left _ _)
    calc ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ := hy_le
      _ ≤ M * (2 * M)⁻¹ := mul_le_mul_of_nonneg_right hyM (by positivity)
      _ = 1 / 2 := by field_simp [hM.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcpt.isBounded.subset subset_closure) hf_cl hf_fr
    (subset_closure (mem_connectedComponentIn ha))
  simp only [f, sub_self, zero_mul, sub_zero, norm_one] at hmax
  norm_num at hmax

/-- **Runge's theorem (equivalence with simple-fraction approximation).** A compact subset `K` of
an open set `Ω ⊆ ℂ` is filled in `Ω` if and only if every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` is uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∀ ε > 0,
        ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε :=
  ⟨fun hfill _ ha _ hε ↦ hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ ha.2 hε,
    isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ⟩

/-! ### Domain-relative Runge theorem and holomorphic hulls -/

/-- Forward Runge approximation for a `IsRungeCompactPair`: every function holomorphic on an open
neighbourhood `U` of `K` can be approximated uniformly on `K` by functions holomorphic on `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε :=
  hRunge.isFilledIn.exists_differentiableOn_norm_sub_lt hRunge.isCompact hRunge.subset hU hKU hf hε

/-- **Runge's approximation theorem** (domain-relative form): for compact `K ⊆ Ω` with `Ω ⊆ ℂ`
open, `IsRungeCompactPair Ω K` holds if and only if every function holomorphic on an open
neighbourhood `U ⊇ K` can be uniformly approximated on `K` by functions holomorphic on `Ω`. -/
theorem isRungeCompactPair_iff_approximation {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
          ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hRunge U hU hKU f hf ε hε =>
    hRunge.exists_differentiableOn_norm_sub_lt hU hKU hf hε, fun happrox => ?_⟩
  refine isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ,
    isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ fun a ha ε hε => ?_⟩
  exact happrox {a}ᶜ isOpen_compl_singleton (fun z hz hza => ha.2 (hza ▸ hz))
    (fun z => (z - a)⁻¹)
    ((differentiableOn_id.sub (differentiableOn_const a)).inv fun _ hz => sub_ne_zero.mpr hz) ε hε

/-- For an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω`, `holomorphicHull Ω K` coincides with
`TauCeti.fillIn K Ω`, the union of `K` and all connected components of `Ω \ K` whose closures are
compact subsets of `Ω`. -/
theorem holomorphicHull_eq_fill {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = fillIn K Ω := by
  refine Subset.antisymm (fun z hz => ?_)
    (hΩ.fillIn_subset_holomorphicHull hKΩ)
  set Ktilde : Set ℂ := fillIn K Ω
  by_contra hzKt
  -- Step 1: Adjoin `z ∉ Ktilde` to the filled compact set `Ktilde`, preserving Runge's condition.
  have hKt_cpt : IsCompact Ktilde := hK.fillIn hΩ
  have hRunge₁ : IsRungeCompactPair Ω (insert z Ktilde) :=
    isRungeCompactPair_iff.mpr ⟨hΩ, hKt_cpt.insert z,
      insert_subset_iff.mpr ⟨holomorphicHull_subset_left _ _ hz, fillIn_subset hKΩ⟩,
      (isFilledIn_fillIn K Ω).insert (by simp [Complex.rank_real_complex])
        (hΩ.sdiff hKt_cpt.isClosed) z⟩
  -- Step 2: Separate `z` from `Ktilde` by a `0`/`1` function on disjoint open sets.
  obtain ⟨r, hr, hr_ball⟩ := Metric.isOpen_iff.mp hKt_cpt.isClosed.isOpen_compl z hzKt
  set r' : ℝ := r / 2
  have hr' : 0 < r' := half_pos hr
  let U₁ : Set ℂ := (closedBall z r')ᶜ
  let U₂ : Set ℂ := ball z r'
  have hU₁ : IsOpen U₁ := isClosed_closedBall.isOpen_compl
  have hKtU₁ : Ktilde ⊆ U₁ := fun w hwK hw_cb =>
    hr_ball (closedBall_subset_ball (half_lt_self hr) hw_cb) hwK
  have hdisj : Disjoint U₁ U₂ :=
    disjoint_left.mpr fun _ hw1 hw2 => hw1 (ball_subset_closedBall hw2)
  classical
  let f : ℂ → ℂ := fun w => if w ∈ U₁ then 0 else 1
  have hf_diff : DifferentiableOn ℂ f (U₁ ∪ U₂) :=
    ((differentiableOn_const 0).congr fun _ hw => by simp [f, hw]).union_of_isOpen
      ((differentiableOn_const 1).congr fun _ hw => by simp [f, hdisj.notMem_of_mem_right hw])
      hU₁ isOpen_ball
  -- Step 3: Approximate `f` on `insert z Ktilde` via Runge and contradict the hull bound at `z`.
  obtain ⟨g, hg_diff, hg_lt⟩ :=
    hRunge₁.exists_differentiableOn_norm_sub_lt (hU₁.union isOpen_ball)
      (insert_subset_iff.mpr ⟨Or.inr (mem_ball_self hr'), hKtU₁.trans subset_union_left⟩)
      hf_diff (by norm_num : (0 : ℝ) < 1 / 3)
  have hgK : ∀ w ∈ K, ‖g w‖ ≤ (1 / 3 : ℝ) := fun w hwK => by
    have hwKt : w ∈ Ktilde := subset_fillIn hwK
    have hlt := hg_lt w (mem_insert_of_mem z hwKt)
    have hfw : f w = 0 := by simp [f, hKtU₁ hwKt]
    rw [hfw, zero_sub, norm_neg] at hlt
    exact hlt.le
  have hgz := norm_le_of_mem_holomorphicHull hz hg_diff hgK
  have hgz1 := hg_lt z (mem_insert z Ktilde)
  have hfz : f z = 1 := by simp [f, hdisj.notMem_of_mem_right (mem_ball_self hr')]
  rw [hfz] at hgz1
  have htri : (1 : ℝ) ≤ ‖(1 : ℂ) - g z‖ + ‖g z‖ := by
    simpa only [sub_add_cancel, norm_one] using norm_add_le ((1 : ℂ) - g z) (g z)
  linarith

/-- For compact `K ⊆ Ω` with `Ω` open, `holomorphicHull Ω K = K` if and only if `K` is filled in
`Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  rw [holomorphicHull_eq_fill hΩ hK hKΩ, fillIn_eq_self_iff_isFilledIn]

/-- For an open set `Ω ⊆ ℂ` and a compact set `K ⊆ ℂ`, `IsRungeCompactPair Ω K` holds if and only
if `holomorphicHull Ω K = K`. -/
theorem isRungeCompactPair_iff_holomorphicHull_eq {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) :
    IsRungeCompactPair Ω K ↔ holomorphicHull Ω K = K := by
  refine ⟨fun h => (holomorphicHull_eq_self_iff_isFilledIn hΩ hK h.subset).mpr h.isFilledIn,
    fun h => ?_⟩
  have hKΩ : K ⊆ Ω := h ▸ holomorphicHull_subset_left Ω K
  exact isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ,
    (holomorphicHull_eq_self_iff_isFilledIn hΩ hK hKΩ).mp h⟩

/-- Point-separation criterion for Runge compact pairs: for an open set `Ω ⊆ ℂ` and a compact
subset `K ⊆ Ω`, `IsRungeCompactPair Ω K` holds if and only if every `z ∈ Ω \ K` is separated from
`K` by an `Ω`-holomorphic function bounded by `1` on `K` and exceeding `1` in norm at `z`. -/
theorem isRungeCompactPair_iff_forall_mem_sdiff_exists_differentiableOn_one_lt_norm_le
    {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ z ∈ Ω \ K, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ 1 < ‖f z‖ ∧ ∀ w ∈ K, ‖f w‖ ≤ 1 := by
  rw [isRungeCompactPair_iff_holomorphicHull_eq hΩ hK]
  refine ⟨fun h z hz => ?_, fun hsep => Subset.antisymm (fun z hz => by_contra fun hzK => ?_)
    (subset_holomorphicHull hKΩ)⟩
  · obtain ⟨f, hf, hKlt, hfz⟩ :=
      (holomorphicHull_eq_self_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt hKΩ).mp
        h z hz
    exact ⟨f, hf, hfz, fun w hw => (hKlt w hw).le⟩
  · obtain ⟨f, hf, hfz, hKB⟩ := hsep z ⟨holomorphicHull_subset_left _ _ hz, hzK⟩
    exact hfz.not_ge (norm_le_of_mem_holomorphicHull hz hf hKB)

/-- Every stage of `TauCeti.filledExhaustion Ω` equals its own holomorphic hull in `Ω`. -/
@[simp]
theorem holomorphicHull_filledExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    holomorphicHull Ω (filledExhaustion Ω n) = filledExhaustion Ω n :=
  (isRungeCompactPair_iff_holomorphicHull_eq hΩ (isCompact_filledExhaustion Ω n)).mp
    (hΩ.isRungeCompactPair_filledExhaustion n)

/-- For compact `K ⊆ ℂ`, the entire holomorphic hull `holomorphicHull Set.univ K` equals the
topological filled hull `TauCeti.filledHull K`. -/
theorem holomorphicHull_univ_eq_filledHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Set.univ K = filledHull K := by
  rw [holomorphicHull_eq_fill isOpen_univ hK (subset_univ K), fillIn_univ]

/-- For compact `K ⊆ ℂ` and any nonempty index type `ι`, `Function.const ι '' K` is polynomially
convex if and only if `Kᶜ` is connected. -/
theorem isPolynomiallyConvex_image_const_iff_isConnected_compl {ι : Type*} [Nonempty ι]
    {K : Set ℂ} (hK : IsCompact K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ IsConnected Kᶜ := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  rw [← hK.isBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex,
    holomorphicHull_univ_eq_filledHull hK,
    filledHull_eq_self_iff_isConnected_compl hrank hK.isBounded]

/-- **Polynomial Runge theorem (for filled compact sets).** If `K ⊆ ℂ` is compact and filled in
`ℂ`, every function holomorphic on an open neighbourhood `U` of `K` can be uniformly approximated on
`K` by complex polynomials. -/
theorem IsFilledIn.exists_polynomial_norm_sub_lt {K U : Set ℂ} (hfill : IsFilledIn K univ)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨g, hg, hfg⟩ := hfill.exists_differentiableOn_norm_sub_lt hK (subset_univ K)
    hU hKU hf (half_pos hε)
  obtain ⟨p, hgp⟩ := (differentiableOn_univ.mp hg).exists_polynomial_norm_sub_lt hK.isBounded
    (half_pos hε)
  refine ⟨p, fun z hz ↦ ?_⟩
  calc ‖f z - p.eval z‖ = ‖(f z - g z) + (g z - p.eval z)‖ := by ring_nf
    _ ≤ ‖f z - g z‖ + ‖g z - p.eval z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgp z hz)
    _ = ε := add_halves ε

/-- **Polynomial Runge theorem**: a compact set `K ⊆ ℂ` has connected complement `Kᶜ` if and only
if every holomorphic function on an open neighbourhood `U ⊇ K` can be approximated uniformly on `K`
by polynomials `p : Polynomial ℂ`. -/
theorem _root_.IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt
    {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  rw [← filledHull_eq_self_iff_isConnected_compl hrank hK.isBounded,
    ← fillIn_univ K, fillIn_eq_self_iff_isFilledIn]
  refine ⟨fun hfill U hU hKU f hf ε hε =>
    hfill.exists_polynomial_norm_sub_lt hK hU hKU hf hε, fun h => ?_⟩
  exact ((isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)).mpr
    fun U hU hKU f hf ε hε =>
      let ⟨p, hp⟩ := h U hU hKU f hf ε hε
      ⟨fun z => p.eval z, p.differentiable.differentiableOn, hp⟩).isFilledIn

/-! ### Finite-jet interpolation refinement -/

/-- Multiplying a function analytic at `a ∈ S` by `∏_{b ∈ S} (z - b)^{m b}` annihilates all
derivatives of order `< m a` at `a`. -/
private theorem iteratedDeriv_prod_pow_sub_mul_eq_zero (S : Finset ℂ) (m : ℂ → ℕ) {r : ℂ → ℂ}
    {a : ℂ} (ha : a ∈ S) (hra : AnalyticAt ℂ r a) {k : ℕ} (hk : k < m a) :
    iteratedDeriv k (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a = 0 := by
  classical
  have hQ_an : AnalyticAt ℂ (fun z : ℂ ↦ ∏ b ∈ S, (z - b) ^ m b) a := by fun_prop
  have hQa : AnalyticAt ℂ (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a := hQ_an.mul hra
  have hord : ((m a : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a := by
    refine hQa.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
      (u := fun z ↦ (∏ b ∈ S.erase a, (z - b) ^ m b) * r z)
      ((by fun_prop : Continuous fun z : ℂ ↦ ∏ b ∈ S.erase a, (z - b) ^ m b).continuousAt.mul
        hra.continuousAt) (Eventually.of_forall fun z ↦ ?_)
    simp only [smul_eq_mul, ← mul_assoc]
    rw [Finset.mul_prod_erase S (fun b ↦ (z - b) ^ m b) ha]
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQa).mp hord k hk

private theorem exists_hermite_quotient {K U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (S : Finset ℂ) (m : ℂ → ℕ) :
    ∃ (P : ℂ[X]) (U' : Set ℂ) (q : ℂ → ℂ), IsOpen U' ∧ K ⊆ U' ∧ DifferentiableOn ℂ q U' ∧
      (∀ z ∈ K, f z - P.eval z = (∏ a ∈ S, (z - a) ^ m a) * q z) ∧
      (∀ a ∈ S, ∀ k < m a, iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a) := by
  classical
  have hbij := (Polynomial.eval_iterate_derivative_bijective_iff_of_charZero
    (K := ℂ) (a := fun i : S ↦ (i : ℂ)) (m := fun i : S ↦ m i)).mpr
    fun _ _ hij _ _ h ↦ hij (Subtype.ext h)
  obtain ⟨P, hP_eq⟩ := hbij.2 fun (i : S) (k : Fin (m i)) ↦ iteratedDeriv k f i
  have hP : ∀ a ∈ S, ∀ k < m a, iteratedDeriv k (fun z ↦ (P : ℂ[X]).eval z) a =
      iteratedDeriv k f a := fun a ha k hk ↦ by
    rw [Polynomial.iteratedDeriv]; exact congrFun (congrFun hP_eq ⟨a, ha⟩) ⟨k, hk⟩
  set Sin := S.filter (· ∈ K); set Sout := S.filter (· ∉ K); set U' := U \ (Sout : Set ℂ)
  have hU' : IsOpen U' := hU.sdiff Sout.finite_toSet.isClosed
  have hKU' : K ⊆ U' := fun z hz ↦ ⟨hKU hz, fun hz' ↦ (Finset.mem_filter.mp hz').2 hz⟩
  have hfP_an : AnalyticOnNhd ℂ (fun z ↦ f z - (P : ℂ[X]).eval z) U' :=
    ((hf.fun_sub (P : ℂ[X]).differentiable.differentiableOn).mono sdiff_subset).analyticOnNhd hU'
  have hord_in : ∀ a ∈ Sin, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ f z - (P : ℂ[X]).eval z) a := by
    intro a ha; obtain ⟨haS, haK⟩ := Finset.mem_filter.mp ha
    have hfa := hf.analyticAt (hU.mem_nhds (hKU haK))
    have hPa := (P : ℂ[X]).differentiable.analyticAt a
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hfa.fun_sub hPa)]
    intro k hk; rw [iteratedDeriv_fun_sub hfa.contDiffAt hPa.contDiffAt, hP a haS k hk, sub_self]
  obtain ⟨q₁, hq₁_an, hq₁_eq⟩ := hfP_an.exists_eq_prod_pow_smul Sin m hord_in
  set Qout : ℂ → ℂ := fun z ↦ ∏ b ∈ Sout, (z - b) ^ m b
  have hQout_ne : ∀ z ∈ U', Qout z ≠ 0 := fun z hz ↦
    Finset.prod_ne_zero_iff.mpr fun b hb ↦ pow_ne_zero _ (sub_ne_zero.mpr fun hzb ↦ hz.2 (hzb ▸ hb))
  refine ⟨P, U', fun z ↦ q₁ z / Qout z, hU', hKU',
    hq₁_an.differentiableOn.div (by fun_prop : Differentiable ℂ Qout).differentiableOn hQout_ne,
    fun z hz ↦ ?_, hP⟩
  have hsplit : (∏ a ∈ S, (z - a) ^ m a) = (∏ a ∈ Sin, (z - a) ^ m a) * Qout z :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ K) fun a ↦ (z - a) ^ m a).symm
  have h1 := hq₁_eq z; simp only [smul_eq_mul] at h1
  rw [h1, hsplit, mul_assoc, mul_div_cancel₀ _ (hQout_ne z (hKU' hz))]

/-- **Runge approximation with finite-jet interpolation.** Let `K` be a compact set filled in
`Ω ⊆ ℂ` (without requiring `Ω` to be open), let `f : ℂ → ℂ` be holomorphic on an open neighbourhood
`U` of `K`, and let `S ⊆ Ω` be a finite set with orders `m : ℂ → ℕ`. For every `ε > 0` there is a
function `g : ℂ → ℂ` holomorphic on `Ω` such that `‖f z - g z‖ < ε` on `K` and
`iteratedDeriv k g a = iteratedDeriv k f a` for all `a ∈ S` and `k < m a`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq
    {K Ω U : Set ℂ} (hfill : IsFilledIn K Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (S : Finset ℂ) (hSΩ : (S : Set ℂ) ⊆ Ω) (m : ℂ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖f z - g z‖ < ε) ∧
      ∀ a ∈ S, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a := by
  obtain ⟨P, U', q, hU', hKU', hq, hq_eq, hP⟩ := exists_hermite_quotient hU hKU hf S m
  set Q : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (z - a) ^ m a
  have hQ_diff : Differentiable ℂ Q := by fun_prop
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image hQ_diff.continuous.norm.continuousOn
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  obtain ⟨p_r, q_r, -, hqrΩ, hqr⟩ := exists_rational_norm_sub_lt hK hU' hKU'
    (fun _ hx => hfill.compl_inter_connectedComponentIn_nonempty hK.isClosed hKΩ hx) hq
    (ε := ε / (M + 1)) (by positivity)
  set r : ℂ → ℂ := fun z ↦ p_r.eval z / q_r.eval z
  set W : Set ℂ := {z : ℂ | q_r.eval z ≠ 0}
  have hW_open : IsOpen W := isOpen_ne_fun q_r.differentiable.continuous continuous_const
  have hΩW : Ω ⊆ W := fun z hz h0 ↦ (hqrΩ z h0).1 hz
  have hrW : DifferentiableOn ℂ r W :=
    p_r.differentiable.differentiableOn.div q_r.differentiable.differentiableOn fun _ hz ↦ hz
  refine ⟨fun z ↦ P.eval z + Q z * r z,
    P.differentiable.differentiableOn.add (hQ_diff.differentiableOn.mul (hrW.mono hΩW)),
    fun z hz ↦ ?_, fun a ha k hk ↦ ?_⟩
  · have hfg : f z - (P.eval z + Q z * r z) = Q z * (q z - r z) := by
      linear_combination hq_eq z hz
    have hQz : ‖Q z‖ ≤ M := (hM₀ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    rw [hfg, norm_mul]
    calc ‖Q z‖ * ‖q z - r z‖ ≤ M * (ε / (M + 1)) :=
          mul_le_mul hQz (hqr z hz).le (norm_nonneg _) hM0
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  · have hra : AnalyticAt ℂ r a := hrW.analyticAt (hW_open.mem_nhds (hΩW (hSΩ ha)))
    rw [iteratedDeriv_fun_add (P.differentiable.analyticAt a).contDiffAt
      ((hQ_diff.analyticAt a).fun_mul hra).contDiffAt,
      iteratedDeriv_prod_pow_sub_mul_eq_zero S m ha hra hk, add_zero, hP a ha k hk]

end TauCeti
