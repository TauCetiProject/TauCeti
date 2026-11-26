/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Analysis.Complex.Runge.Operator
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Analysis.Analytic.HermiteInterpolation
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Normed.Module.FilledIn
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.Compactification.OnePoint.FilledHull
import TauCeti.Topology.Perfect

/-!
# Runge's approximation theorem, finite-jet interpolation, and prescribed-pole rational Runge

This file proves Runge's approximation theorem in its domain-relative, finite-jet, polynomial, and
prescribed-pole rational forms on open subsets `Ω ⊆ ℂ`: a compact subset `K ⊆ Ω` admits uniform
approximation of neighbourhood-holomorphic functions by `Ω`-holomorphic functions if and only if
`(Ω, K)` is a Runge compact pair, i.e. no connected component of `Ω \ K` is relatively compact in
`Ω` (`TauCeti.isRungeCompactPair_iff_approximation`). Together with the explicit filled compact
exhaustions `TauCeti.filledExhaustion Ω` (`TauCeti.Analysis.Normed.Module.Exhaustion`), these
equivalences provide the compact-to-global patching step for constructing global holomorphic
functions on arbitrary open plane sets. Combining analytic Hermite interpolation
(`AnalyticOnNhd.exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul`) with scalar Runge approximation
yields `Ω`-holomorphic approximants matching prescribed finite jets at finitely many points of `K`
(`TauCeti.IsRungeCompactPair.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt`).

From scalar Runge approximation we identify `TauCeti.holomorphicHull Ω K` with
`TauCeti.fillIn K Ω`, the union of `K` and all relatively compact connected components of `Ω \ K` in
`Ω` (`TauCeti.holomorphicHull_eq_fill`), establishing `holomorphicHull Ω K = K ↔ IsFilledIn K Ω`.
Specializing to `Ω = Set.univ` links `TauCeti.holomorphicHull Set.univ K = TauCeti.filledHull K`,
polynomial convexity in dimension one, and uniform polynomial approximation on compact sets with
connected complement. More generally, given any pole set `A ⊆ OnePoint ℂ` meeting every connected
component of `(((↑) : ℂ → OnePoint ℂ) '' K)ᶜ` in the Riemann sphere, pole pushing across
complementary components yields uniform rational approximation by `P(z) + ∑ a ∈ s, Q_a((z - a)⁻¹)`
with poles in `A` (`IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`).

## Main results

* `IsOpen.isRungeCompactPair_holomorphicHull`, `IsOpen.isRungeCompactPair_filledExhaustion`, and
  `IsOpen.exists_subset_interior_and_isRungeCompactPair`: holomorphic hulls of compact subsets and
  stages of `TauCeti.filledExhaustion` form Runge compact pairs with `Ω`, which absorb every compact
  subset of `Ω` into their interior.
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt` and
  `TauCeti.isRungeCompactPair_iff_approximation`: forward uniform Runge approximation of functions
  with values in a complex normed space, and the full domain-relative Runge equivalence.
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt`: scalar
  Runge approximation matching prescribed finite jets at finitely many points of `K`.
* `TauCeti.differentiableOn_tsum_of_forall_norm_le_filledExhaustion`: a series of holomorphic
  functions whose `k`-th term is bounded on the `k`-th stage by a summable sequence has a
  holomorphic sum.
* `TauCeti.holomorphicHull_eq_fill` and `TauCeti.holomorphicHull_eq_self_iff_isFilledIn`:
  topological characterization of `TauCeti.holomorphicHull Ω K` for open `Ω` and compact `K ⊆ Ω`.
* `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq` and
  `TauCeti.isRungeCompactPair_iff_forall_mem_sdiff_exists_differentiableOn_one_lt_norm_le`:
  holomorphic-hull and point-separation criteria for Runge compact pairs.
* `TauCeti.holomorphicHull_univ_eq_filledHull`,
  `IsCompact.isConnected_compl_iff_isPolynomiallyConvex`, and
  `IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt`:
  specialization to `Ω = Set.univ` and the polynomial Runge theorem on `ℂ`.
* `IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt` and
  `IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`: pole pushing across a
  complementary component and rational Runge approximation with poles restricted to a set
  `A : Set (OnePoint ℂ)` meeting each complementary component in the Riemann sphere.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1, Lemma 11.3, Corollary 11.4, and
  Theorem 11.7.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorems 1.3.1 and 1.3.9.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.5–13.9.
-/

public section

open Bornology Metric Polynomial Set
open scoped NNReal OnePoint Topology

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

/-- Forward Runge approximation for a `IsRungeCompactPair`: every function with values in a complex
normed space that is holomorphic on an open neighbourhood `U` of `K` can be approximated uniformly
on `K` by functions holomorphic on `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {Ω K U : Set ℂ} (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → W} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → W, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUO, hop⟩ := exists_finite_rank_runge_operator hRunge hU hKU
  obtain ⟨M, hM⟩ :=
    hL.bddAbove_image (hf.continuousOn.mono (hLUO.trans inter_subset_left)).norm
  set B : ℝ := max M 1
  have hB1 : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hLB : ∀ z ∈ L, ‖f z‖ ≤ B := fun z hz =>
    (hM ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, ζ, w, g, -, hg_diff, hbound⟩ := hop (ε / 2 / B) (by positivity)
  refine ⟨fun z => ∑ j : Fin N, (w j * g j z) • f (ζ j), ?_, fun z hz => ?_⟩
  · exact DifferentiableOn.fun_sum fun j _ => ((hg_diff j).const_mul (w j)).smul_const (f (ζ j))
  -- The scalar estimate for `φ ∘ f`, for every continuous linear functional `φ`, bounds the norm.
  refine (NormedSpace.norm_le_dual_bound ℂ _ (by positivity) fun φ => ?_).trans_lt
    ((div_mul_cancel₀ _ hB1.ne').trans_lt (half_lt_self hε))
  have hφ := hbound (fun z => φ (f z)) (φ.differentiable.comp_differentiableOn hf)
    (‖φ‖ * B) (by positivity) (fun z hz => (φ.le_opNorm _).trans (by gcongr; exact hLB z hz)) z hz
  calc ‖φ (f z - ∑ j : Fin N, (w j * g j z) • f (ζ j))‖
      = ‖φ (f z) - ∑ j : Fin N, w j * φ (f (ζ j)) * g j z‖ := by
        simp only [map_sub, map_sum, map_smul, smul_eq_mul]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ε / 2 / B * (‖φ‖ * B) := hφ
    _ = ε / 2 / B * B * ‖φ‖ := by ring

/-- A series of functions holomorphic on an open set `Y ⊆ Ω`, whose `k`-th term is bounded by
`u k` on the stage `filledExhaustion Ω k` for a summable `u`, has a holomorphic sum on `Y`: each
compact subset of `Y` lies in all but finitely many stages, so the series converges locally
uniformly on `Y`. This is how Runge corrections chosen stage by stage sum to a holomorphic
function. -/
theorem differentiableOn_tsum_of_forall_norm_le_filledExhaustion {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {Ω Y : Set ℂ} (hY : IsOpen Y)
    (hYΩ : Y ⊆ Ω) {t : ℕ → ℂ → F} {u : ℕ → ℝ} (hu : Summable u)
    (ht : ∀ k, DifferentiableOn ℂ (t k) Y)
    (hb : ∀ k, ∀ z ∈ filledExhaustion Ω k, ‖t k z‖ ≤ u k) :
    DifferentiableOn ℂ (fun z ↦ ∑' k, t k z) Y := by
  refine SummableLocallyUniformlyOn.differentiableOn hY
    (.of_locally_bounded_eventually hY fun K hKY hK ↦ ?_)
    fun k z hz ↦ (ht k).differentiableAt (hY.mem_nhds hz)
  obtain ⟨j, hj⟩ := hK.exists_subset_interior_filledExhaustion
    (hKY.trans (hY.subset_interior_iff.2 hYΩ))
  refine ⟨u, hu, ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop j] with k hk z hz
  exact hb k z (filledExhaustion_mono hk (interior_subset (hj hz)))

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
    isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ fun a ha ↦
      happrox {a}ᶜ isOpen_compl_singleton (fun z hz hza ↦ ha.2 (hza ▸ hz)) _
        ((differentiableOn_id.sub_const a).inv fun _ hz ↦ sub_ne_zero.2 hz)⟩

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
  constructor
  · intro hhull z hz
    rcases K.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
    · exact ⟨fun _ => 2, differentiableOn_const 2, by norm_num, fun _ h => h.elim⟩
    have hz' : z ∉ holomorphicHull Ω K := by
      rw [hhull]
      exact hz.2
    rw [mem_holomorphicHull_iff] at hz'
    push Not at hz'
    obtain ⟨f, hf, B, hKB, hfz⟩ := hz' hz.1
    have hB0 : 0 ≤ B := (norm_nonneg (f w₀)).trans (hKB w₀ hw₀)
    let t : ℝ := (B + ‖f z‖) / 2
    have ht0 : 0 < t := by dsimp only [t]; linarith [norm_nonneg (f z)]
    have hBt : B < t := by dsimp only [t]; linarith
    refine ⟨fun w => (t⁻¹ : ℂ) * f w, hf.const_mul _, ?_, fun w hw => ?_⟩
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, inv_mul_eq_div,
        lt_div_iff₀ ht0]
      dsimp only [t]
      linarith
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, inv_mul_eq_div,
        div_le_one ht0]
      exact (hKB w hw).trans hBt.le
  · intro hsep
    refine Subset.antisymm (fun z hz => ?_) (subset_holomorphicHull hKΩ)
    by_contra hzK
    obtain ⟨f, hf, hfz, hKB⟩ := hsep z ⟨holomorphicHull_subset_left _ _ hz, hzK⟩
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

/-- For compact `K ⊆ ℂ`, the complement `Kᶜ` is connected if and only if the image of `K` in
`Fin 1 → ℂ` under the diagonal embedding is polynomially convex. -/
theorem _root_.IsCompact.isConnected_compl_iff_isPolynomiallyConvex {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsPolynomiallyConvex (Function.const (Fin 1) '' K) := by
  rw [← hK.isBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex,
    holomorphicHull_univ_eq_filledHull hK]
  refine ⟨fun hconn => filledHull_eq_self hconn.isPreconnected fun hb =>
    NormedSpace.unbounded_univ ℝ ℂ (by simpa using hb.union hK.isBounded), fun hfill => ?_⟩
  simpa only [hfill] using
    isConnected_compl_filledHull (by simp [Complex.rank_real_complex]) hK.isBounded

/-- **Polynomial Runge theorem**: a compact set `K ⊆ ℂ` has connected complement `Kᶜ` if and only
if every holomorphic function on an open neighbourhood `U ⊇ K` can be approximated uniformly on `K`
by polynomials `p : Polynomial ℂ`. -/
theorem _root_.IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt
    {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  rw [hK.isConnected_compl_iff_isPolynomiallyConvex,
    ← hK.isBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex,
    ← isRungeCompactPair_iff_holomorphicHull_eq isOpen_univ hK,
    isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)]
  constructor
  · intro h U hU hKU f hf ε hε
    obtain ⟨g, hg_diff, hg_lt⟩ := h U hU hKU f hf (ε / 2) (half_pos hε)
    obtain ⟨p, hp_lt⟩ := (differentiableOn_univ.mp hg_diff).exists_polynomial_norm_sub_lt
      hK.isBounded (half_pos hε)
    refine ⟨p, fun z hz => ?_⟩
    calc ‖f z - p.eval z‖
        ≤ ‖f z - g z‖ + ‖g z - p.eval z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hg_lt z hz) (hp_lt z hz)
      _ = ε := add_halves ε
  · intro h U hU hKU f hf ε hε
    obtain ⟨p, hp_lt⟩ := h U hU hKU f hf ε hε
    exact ⟨fun z => p.eval z, p.differentiable.differentiableOn, hp_lt⟩

/-- **Scalar Runge approximation with exact finite-jet interpolation.** Let `(Ω, K)` be a Runge
compact pair, let `s ⊆ K` be finite with prescribed jet orders `m : ℂ → ℕ`, and let `f : ℂ → ℂ` be
holomorphic on an open neighbourhood `U` of `K`. For every `ε > 0`, there exists `g : ℂ → ℂ`
holomorphic on `Ω` matching the iterated derivatives of `f` up to order `m a` at every `a ∈ s`
(`iteratedDeriv k g a = iteratedDeriv k f a` for `k < m a`) while satisfying `‖f z - g z‖ < ε` on
`K`. -/
theorem IsRungeCompactPair.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt
    {Ω K U s : Set ℂ} (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hs : s.Finite) (hsK : s ⊆ K) (m : ℂ → ℕ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      (∀ a ∈ s, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a) ∧
      ∀ z ∈ K, ‖f z - g z‖ < ε := by
  classical
  set t : Finset ℂ := hs.toFinset
  have htU : (t : Set ℂ) ⊆ U := by rw [hs.coe_toFinset]; exact hsK.trans hKU
  have hf_an : AnalyticOnNhd ℂ f U := (Complex.analyticOnNhd_iff_differentiableOn hU).mpr hf
  obtain ⟨P, F, -, hF, hP_jet, hfactor⟩ :=
    hf_an.exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul htU m
  set Qp : ℂ[X] := ∏ x ∈ t, (X - C x) ^ m x
  -- Approximate `F` on `K` by `G` holomorphic on `Ω`, scaled by `max (sup_K ‖Qp‖) 1`.
  obtain ⟨M, hM⟩ :=
    hRunge.isCompact.exists_bound_of_continuousOn Qp.differentiable.continuous.continuousOn
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos (le_max_right M 1)
  obtain ⟨G, hG, hFG⟩ := hRunge.exists_differentiableOn_norm_sub_lt hU hKU
    hF.differentiableOn (div_pos hε hB_pos)
  refine ⟨fun z ↦ P.eval z + Qp.eval z * G z,
    P.differentiableOn.add (Qp.differentiableOn.mul hG), fun a ha k hk ↦ ?_, fun z hz ↦ ?_⟩
  · have hat : a ∈ t := hs.mem_toFinset.mpr ha
    have haΩ : a ∈ Ω := hRunge.subset (hsK ha)
    have hQp_an : AnalyticAt ℂ (fun z ↦ Qp.eval z) a := Qp.differentiable.analyticAt a
    have hG_an : AnalyticAt ℂ G a := hG.analyticAt (hRunge.isOpen.mem_nhds haΩ)
    have hQG_an : AnalyticAt ℂ (fun z ↦ Qp.eval z * G z) a := hQp_an.mul hG_an
    have hQp_eq : (fun z ↦ Qp.eval z) = ∏ x ∈ t, (· - x) ^ m x := by
      ext z
      simp [Qp, eval_prod]
    have hQG_ord : (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ Qp.eval z * G z) a := by
      rw [analyticOrderAt_fun_mul hQp_an hG_an, hQp_eq, analyticOrderAt_prod_sub_pow,
        ite_eq_left hat]
      exact le_self_add
    have hQG_zero : iteratedDeriv k (fun z ↦ Qp.eval z * G z) a = 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQG_an).mp hQG_ord k hk
    change iteratedDeriv k ((fun z ↦ P.eval z) + fun z ↦ Qp.eval z * G z) a = _
    rw [iteratedDeriv_add (P.differentiable.analyticAt a).contDiffAt hQG_an.contDiffAt,
      hP_jet a hat k hk, hQG_zero, add_zero]
  · have hsub : f z - (P.eval z + Qp.eval z * G z) = Qp.eval z * (F z - G z) := by
      linear_combination hfactor z
    rw [hsub, norm_mul]
    calc ‖Qp.eval z‖ * ‖F z - G z‖
        ≤ B * ‖F z - G z‖ :=
          mul_le_mul_of_nonneg_right ((hM z hz).trans (le_max_left M 1)) (norm_nonneg _)
      _ < B * (ε / B) := mul_lt_mul_of_pos_left (hFG z hz) hB_pos
      _ = ε := mul_div_cancel₀ ε hB_pos.ne'

section RationalRunge

private theorem sub_inv_notMem_filledHull_image {K : Set ℂ} (hK : IsClosed K) {ζ b : ℂ}
    (hζK : ζ ∉ K) (hb : b ∈ connectedComponentIn Kᶜ ζ) (hζb : ζ ≠ b) :
    (ζ - b)⁻¹ ∉ filledHull ((fun z ↦ (z - b)⁻¹) '' K) := by
  intro hζ'_hull
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  set D : Set ℂ := connectedComponentIn Kᶜ ζ
  have hD_open : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hDb_pre : IsPreconnected (D \ {b}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hrank hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (finite_singleton b).isDiscrete
  have hφD_pre : IsPreconnected ((fun z ↦ (z - b)⁻¹) '' (D \ {b})) := hDb_pre.image _
    ((continuous_id.sub continuous_const).continuousOn.inv₀ fun _ hz ↦ sub_ne_zero.mpr hz.right)
  have hφD_compl : (fun z ↦ (z - b)⁻¹) '' (D \ {b}) ⊆ ((fun z ↦ (z - b)⁻¹) '' K)ᶜ := by
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
    have h12 : z₁ = z₂ := by simpa using heq.symm
    exact connectedComponentIn_subset Kᶜ ζ hz₁.left (h12 ▸ hz₂)
  have hsub := hφD_pre.subset_connectedComponentIn
    ⟨ζ, ⟨mem_connectedComponentIn hζK, hζb⟩, rfl⟩ hφD_compl
  have hnot_cl : b ∉ closure (D \ {b}) :=
    (isBounded_image_inv_sub_iff (q := b) (U := D \ {b}) fun h ↦ h.right rfl).mp
      ((mem_filledHull_iff.mp hζ'_hull).subset hsub)
  exact hnot_cl (hD_open.subset_closure_sdiff_of_isDiscrete
    ((finite_singleton b).subset inter_subset_right).isDiscrete hb)

/-- **Single-pole pole pushing across a complementary component.** If `K ⊆ ℂ` is compact and
`ζ ∉ K` lies in the same connected component of `Kᶜ` as `b`, then for every `η > 0` the simple
fraction `z ↦ (z - ζ)⁻¹` is uniformly approximated on `K` within `η` by `z ↦ R.eval (z - b)⁻¹` for
a polynomial `R : ℂ[X]` with `R.coeff 0 = 0`. -/
theorem _root_.IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt {K : Set ℂ} (hK : IsCompact K)
    {ζ b : ℂ} (hζK : ζ ∉ K) (hb : b ∈ connectedComponentIn Kᶜ ζ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℂ[X], R.coeff 0 = 0 ∧ ∀ z ∈ K, ‖(z - ζ)⁻¹ - R.eval (z - b)⁻¹‖ < η := by
  by_cases hζb : ζ = b
  · subst hζb
    exact ⟨X, coeff_X_zero, fun z _ ↦ by simpa using hη⟩
  have hbK : b ∉ K := connectedComponentIn_subset Kᶜ ζ hb
  set φ : ℂ → ℂ := fun z ↦ (z - b)⁻¹
  set K' : Set ℂ := φ '' K
  set ζ' : ℂ := φ ζ
  have hK' : IsCompact K' := hK.image_of_continuousOn
    ((continuous_id.sub continuous_const).continuousOn.inv₀ fun z hz ↦
      sub_ne_zero.mpr fun (h : z = b) ↦ hbK (h ▸ hz))
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  have hζ'_not_hull : ζ' ∉ filledHull K' := sub_inv_notMem_filledHull_image hK.isClosed hζK hb hζb
  -- Approximate `w ↦ -ζ' * (w - ζ')⁻¹` by `Q₀` on `filledHull K'`, then set `R = X * Q₀`.
  have hL' : IsCompact (filledHull K') :=
    Metric.isCompact_of_isClosed_isBounded hK'.isClosed.isClosed_filledHull
      (isBounded_filledHull.mpr hK'.isBounded)
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn continuous_id.continuousOn
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hf' : DifferentiableOn ℂ (fun w : ℂ ↦ -ζ' * (w - ζ')⁻¹) {ζ'}ᶜ :=
    (differentiableOn_const (-ζ')).mul
      ((differentiableOn_id.sub (differentiableOn_const ζ')).inv fun _ hw ↦ sub_ne_zero.mpr hw)
  obtain ⟨Q₀, hQ₀⟩ :=
    (hL'.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt.mp
      (isConnected_compl_filledHull hrank hK'.isBounded)) {ζ'}ᶜ isOpen_compl_singleton
      (fun _ hw (h : _ = ζ') ↦ hζ'_not_hull (h ▸ hw)) _ hf' (η / B) (div_pos hη hB_pos)
  refine ⟨X * Q₀, by simp, fun z hz ↦ ?_⟩
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun (h : z = b) ↦ hbK (h ▸ hz)
  have hζb' : ζ - b ≠ 0 := sub_ne_zero.mpr hζb
  have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr fun (h : z = ζ) ↦ hζK (h ▸ hz)
  have hmobius : φ z * (-ζ' * (φ z - ζ')⁻¹) = (z - ζ)⁻¹ := by
    have hdiff : φ z - ζ' = -(z - ζ) / ((z - b) * (ζ - b)) := by
      dsimp only [φ, ζ']; field_simp [hzb, hζb']; ring
    rw [hdiff, inv_div]; dsimp only [φ, ζ']; field_simp [hzb, hζb', hzζ]
  have hid : (z - ζ)⁻¹ - (X * Q₀).eval (φ z) = φ z * (-ζ' * (φ z - ζ')⁻¹ - Q₀.eval (φ z)) := by
    simp only [eval_mul, eval_X, mul_sub, hmobius]
  rw [hid, norm_mul]
  calc ‖φ z‖ * ‖-ζ' * (φ z - ζ')⁻¹ - Q₀.eval (φ z)‖
      ≤ B * ‖-ζ' * (φ z - ζ')⁻¹ - Q₀.eval (φ z)‖ :=
        mul_le_mul_of_nonneg_right
          ((hM (φ z) (mem_image_of_mem φ hz)).trans (le_max_left M 1)) (norm_nonneg _)
    _ < B * (η / B) :=
        mul_lt_mul_of_pos_left (hQ₀ (φ z) (subset_filledHull (mem_image_of_mem φ hz))) hB_pos
    _ = η := mul_div_cancel₀ η hB_pos.ne'

private theorem exists_polynomial_or_eval_sub_inv_norm_sub_lt {K : Set ℂ} {A : Set (OnePoint ℂ)}
    (hK : IsCompact K)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {ζ : ℂ} (hζK : ζ ∉ K) {η : ℝ} (hη : 0 < η) :
    ((∞ : OnePoint ℂ) ∈ A ∧ ∃ P : ℂ[X], ∀ z ∈ K, ‖(z - ζ)⁻¹ - P.eval z‖ < η) ∨
      ∃ (b : ℂ) (R : ℂ[X]), (b : OnePoint ℂ) ∈ A ∧ b ∉ K ∧ R.coeff 0 = 0 ∧
        ∀ z ∈ K, ‖(z - ζ)⁻¹ - R.eval (z - b)⁻¹‖ < η := by
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  set S : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' K
  have hζS : (ζ : OnePoint ℂ) ∈ Sᶜ := fun ⟨_, hy, hyζ⟩ ↦ hζK (OnePoint.coe_injective hyζ ▸ hy)
  obtain ⟨p, hpA, hpC⟩ := hA (ζ : OnePoint ℂ) hζS
  rcases p with _ | b
  · -- The component of `ζ` in `Sᶜ` contains `∞`, so `ζ` lies outside `filledHull K`.
    have hζ_not_hull : ζ ∉ filledHull K := by
      intro hζ_hull
      rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hζ_hull, hζK⟩] at hpC
      obtain ⟨_, -, h_eq⟩ := hpC
      exact OnePoint.coe_ne_infty _ h_eq
    have hL : IsCompact (filledHull K) :=
      Metric.isCompact_of_isClosed_isBounded hK.isClosed.isClosed_filledHull
        (isBounded_filledHull.mpr hK.isBounded)
    have hf_inv : DifferentiableOn ℂ (fun z : ℂ ↦ (z - ζ)⁻¹) {ζ}ᶜ :=
      (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun _ hz ↦ sub_ne_zero.mpr hz
    obtain ⟨P, hP⟩ :=
      (hL.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt.mp
        (isConnected_compl_filledHull hrank hK.isBounded)) {ζ}ᶜ isOpen_compl_singleton
        (fun _ hz (h : _ = ζ) ↦ hζ_not_hull (h ▸ hz)) _ hf_inv η hη
    exact Or.inl ⟨hpA, P, fun z hz ↦ hP z (subset_filledHull hz)⟩
  · -- A finite allowed pole `b` lies in the same component of `Kᶜ` as `ζ`.
    have hbK : b ∉ K := fun hbK ↦ connectedComponentIn_subset Sᶜ _ hpC (mem_image_of_mem _ hbK)
    have hb_comp : b ∈ connectedComponentIn Kᶜ ζ := by
      by_cases hζ_hull : ζ ∈ filledHull K
      · rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hζ_hull, hζK⟩] at hpC
        obtain ⟨y, hy, hyb⟩ := hpC
        exact OnePoint.coe_injective hyb ▸ hy
      · have hb_not_hull : b ∉ filledHull K := by
          intro hb_hull
          have hζ_in : (ζ : OnePoint ℂ) ∈ connectedComponentIn Sᶜ (b : OnePoint ℂ) :=
            connectedComponentIn_eq hpC ▸ mem_connectedComponentIn hζS
          rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hb_hull, hbK⟩] at hζ_in
          obtain ⟨y, hy, hyζ⟩ := hζ_in
          exact hζ_hull ((mem_filledHull_iff_of_mem_connectedComponentIn
            (OnePoint.coe_injective hyζ ▸ hy)).mpr hb_hull)
        rwa [← compl_filledHull_eq_connectedComponentIn hrank hK.isBounded hζ_hull]
    obtain ⟨R, hR0, hR⟩ := hK.exists_polynomial_eval_sub_inv_norm_sub_lt hζK hb_comp hη
    exact Or.inr ⟨b, R, hpA, hbK, hR0, hR⟩

private theorem exists_polynomial_add_sum_eval_sub_inv_of_sum {K : Set ℂ} {A : Set (OnePoint ℂ)}
    (hK : IsCompact K)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {N : ℕ} (c ζ : Fin N → ℂ) (hζ : ∀ j, ζ j ∉ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : ℂ[X]) (s : Finset ℂ) (Q : ℂ → ℂ[X]),
      (∀ a ∈ s, (a : OnePoint ℂ) ∈ A ∧ a ∉ K) ∧
      ((∞ : OnePoint ℂ) ∉ A → P = 0) ∧
      (∀ a ∈ s, (Q a).coeff 0 = 0) ∧
      ∀ z ∈ K, ‖(∑ j, c j * (z - ζ j)⁻¹) - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ ≤ δ := by
  classical
  set Sc : ℝ := ∑ j : Fin N, ‖c j‖
  have hSc_pos : 0 < Sc + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) one_pos
  set η : ℝ := δ / (Sc + 1)
  have hη : 0 < η := div_pos hδ hSc_pos
  set isInf : Fin N → Prop := fun j ↦
    (∞ : OnePoint ℂ) ∈ A ∧ ∃ P : ℂ[X], ∀ z ∈ K, ‖(z - ζ j)⁻¹ - P.eval z‖ < η
  choose Pj hPj using fun (j : {j : Fin N // isInf j}) ↦ j.property.right
  choose bj Rj hbjA hbjK hRj0 hRj using fun (j : {j : Fin N // ¬ isInf j}) ↦
    (exists_polynomial_or_eval_sub_inv_norm_sub_lt hK hA (hζ j.val) hη).resolve_left j.property
  set J_inf : Finset (Fin N) := Finset.univ.filter isInf
  set J_fin : Finset (Fin N) := Finset.univ.filter (fun j ↦ ¬ isInf j)
  set b_fn : Fin N → ℂ := fun j ↦ if hj : ¬ isInf j then bj ⟨j, hj⟩ else 0
  set R_fn : Fin N → ℂ[X] := fun j ↦ if hj : ¬ isInf j then Rj ⟨j, hj⟩ else 0
  set P_fn : Fin N → ℂ[X] := fun j ↦ if hj : isInf j then Pj ⟨j, hj⟩ else 0
  set P : ℂ[X] := ∑ j ∈ J_inf, C (c j) * P_fn j
  set s : Finset ℂ := J_fin.image b_fn
  set Q : ℂ → ℂ[X] := fun a ↦ ∑ j ∈ J_fin with b_fn j = a, C (c j) * R_fn j
  refine ⟨P, s, Q, fun a ha ↦ ?_, fun hinfA ↦ Finset.sum_eq_zero fun j hj ↦
    (hinfA (Finset.mem_filter.mp hj).right.left).elim, fun a _ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    have hj' : ¬ isInf j := (Finset.mem_filter.mp hj).right
    simpa only [b_fn, dite_eq_left hj'] using And.intro (hbjA ⟨j, hj'⟩) (hbjK ⟨j, hj'⟩)
  · simp only [Q, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' : ¬ isInf j := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).left).right
    dsimp only [R_fn]; rw [dite_eq_left hj', hRj0 ⟨j, hj'⟩, mul_zero]
  · set approx : Fin N → ℂ := fun j ↦
      if isInf j then (P_fn j).eval z else (R_fn j).eval (z - b_fn j)⁻¹
    have hsum_Q : ∑ a ∈ s, (Q a).eval (z - a)⁻¹ = ∑ j ∈ J_fin, c j * approx j :=
      (Finset.sum_image' (fun j ↦ (C (c j) * R_fn j).eval (z - b_fn j)⁻¹) fun j _ ↦ by
        rw [eval_finsetSum]
        exact Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).right]).trans <|
        Finset.sum_congr rfl fun j hj ↦ by
          simp [approx, ite_eq_right (Finset.mem_filter.mp hj).right]
    have hsum_P : P.eval z = ∑ j ∈ J_inf, c j * approx j := by
      simp only [P, eval_finsetSum, eval_mul, eval_C]
      exact Finset.sum_congr rfl fun j hj ↦ by
        simp [approx, ite_eq_left (Finset.mem_filter.mp hj).right]
    have herr_j (j : Fin N) : ‖(z - ζ j)⁻¹ - approx j‖ ≤ η := by
      by_cases hj : isInf j
      · simpa only [approx, ite_eq_left hj, P_fn, dite_eq_left hj] using (hPj ⟨j, hj⟩ z hz).le
      · simpa only [approx, ite_eq_right hj, R_fn, b_fn, dite_eq_left hj] using
          (hRj ⟨j, hj⟩ z hz).le
    rw [hsum_P, hsum_Q, Finset.sum_filter_add_sum_filter_not, ← Finset.sum_sub_distrib]
    calc ‖∑ j, (c j * (z - ζ j)⁻¹ - c j * approx j)‖
        ≤ ∑ j, ‖c j‖ * η := (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j _ ↦ by
            rw [← mul_sub, norm_mul]; exact mul_le_mul_of_nonneg_left (herr_j j) (norm_nonneg _)
      _ = Sc * η := by simp only [Sc, Finset.sum_mul]
      _ ≤ (Sc + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ = δ := mul_div_cancel₀ _ hSc_pos.ne'

/-- **Rational Runge theorem with prescribed pole set in the Riemann sphere.** Let `K ⊆ ℂ` be
compact, let `f : ℂ → ℂ` be holomorphic on an open neighbourhood `U` of `K`, and let
`A : Set (OnePoint ℂ)` meet every connected component of the complement of `K` in `OnePoint ℂ`. For
every `ε > 0`, `f` can be uniformly approximated on `K` within `ε` by a rational function
`z ↦ P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹` whose finite poles `a ∈ s` lie in `A` outside `K`,
with `(Q a).coeff 0 = 0` for each `a ∈ s` and `P = 0` whenever `∞ ∉ A`. -/
theorem _root_.IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt
    {K U : Set ℂ} {A : Set (OnePoint ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ℂ[X]) (s : Finset ℂ) (Q : ℂ → ℂ[X]),
      (∀ a ∈ s, (a : OnePoint ℂ) ∈ A ∧ a ∉ K) ∧
      ((∞ : OnePoint ℂ) ∉ A → P = 0) ∧
      (∀ a ∈ s, (Q a).coeff 0 = 0) ∧
      ∀ z ∈ K, ‖f z - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn (hf.continuousOn.mono hLU)
  set B : ℝ := max M₀ 0
  have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos (le_max_right M₀ 0) one_pos
  obtain ⟨N, ζ, w, hζ, hrat⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{0} isOpen_interior hKL (div_pos (half_pos hε) hB1)
  set c : Fin N → ℂ := fun j ↦ w j * f (ζ j)
  obtain ⟨P, s, Q, hsA, hP0, hQ0, hpush⟩ := exists_polynomial_add_sum_eval_sub_inv_of_sum hK hA
    c ζ (fun j ↦ (hζ j).right) (half_pos hε)
  refine ⟨P, s, Q, hsA, hP0, hQ0, fun z hz ↦ ?_⟩
  have herr_rat : ‖f z - ∑ j, c j * (z - ζ j)⁻¹‖ < ε / 2 := by
    have h1 := hrat f B (hf.mono (interior_subset.trans hLU))
      (fun u hu ↦ (hM₀ u (interior_subset hu)).trans (le_max_left M₀ 0)) z hz
    have heq : (∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)) = ∑ j, c j * (z - ζ j)⁻¹ :=
      Finset.sum_congr rfl fun j _ ↦ by dsimp only [c]; rw [smul_eq_mul]; ring
    rw [heq] at h1
    calc ‖f z - ∑ j, c j * (z - ζ j)⁻¹‖
        ≤ ε / 2 / (B + 1) * B := h1
      _ < ε / 2 / (B + 1) * (B + 1) := by gcongr; linarith
      _ = ε / 2 := div_mul_cancel₀ _ hB1.ne'
  calc ‖f z - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖
      ≤ ‖f z - ∑ j, c j * (z - ζ j)⁻¹‖ +
          ‖(∑ j, c j * (z - ζ j)⁻¹) - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by linarith [hpush z hz]
    _ = ε := add_halves ε

end RationalRunge

end TauCeti
