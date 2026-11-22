/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Analysis.Complex.Runge.CompactPair
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Runge.Rational.Basic
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Normed.Module.FilledIn
import TauCeti.LinearAlgebra.Complex.Finrank

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

Building on rational-kernel Runge approximation (`IsCompact.exists_rational_norm_sub_sum_smul_lt` in
`TauCeti.Analysis.Complex.Runge.Rational.Basic`), the file provides vector-valued Runge
approximation (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`) without requiring openness
of `Ω`.

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
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: vector-valued uniform Runge
  approximation without requiring `Ω` to be open.
* `TauCeti.differentiableOn_tsum_of_forall_norm_le_filledExhaustion`: a series of holomorphic
  functions whose `k`-th term is bounded on the `k`-th stage by a summable sequence has a
  holomorphic sum.
* `TauCeti.isRungeCompactPair_iff_approximation`: the full domain-relative Runge equivalence.
* `TauCeti.holomorphicHull_eq_fill` and `TauCeti.holomorphicHull_eq_self_iff_isFilledIn`:
  topological characterization of `TauCeti.holomorphicHull Ω K` for open `Ω` and compact `K ⊆ Ω`.
* `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq`: holomorphic-hull criterion for Runge compact
  pairs.
* `TauCeti.holomorphicHull_univ_eq_filledHull`,
  `IsCompact.isPolynomiallyConvex_image_const_iff_isConnected_compl`, and
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

/-! ### Vector-valued Runge approximation -/

/-- **Runge's approximation theorem (vector-valued, arbitrary `Ω`).** Let `K` be a compact set
filled in `Ω ⊆ ℂ` (without requiring `Ω` to be open), and let `f : ℂ → F` be holomorphic on an
open neighbourhood `U` of `K` with values in a complex normed space `F`. For every `ε > 0` there is
a function `g : ℂ → F` holomorphic on `Ω` such that `‖f z - g z‖ < ε` for all `z ∈ K`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K Ω U : Set ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨N, ζ, p, q, -, -, hqΩ, happrox⟩ := hK.exists_rational_norm_sub_sum_smul_lt hU hKU
    (fun _ hx ↦ hfill.compl_inter_connectedComponentIn_nonempty hKΩ hx) hf hε
  refine ⟨fun w ↦ ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ ?_, happrox⟩
  exact ((p i).differentiable.differentiableOn.div (q i).differentiable.differentiableOn
    fun z hz h0 ↦ (hqΩ i z h0).1 hz).smul_const (f (ζ i))

/-! ### Domain-relative Runge theorem and holomorphic hulls -/

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
    hRunge.isFilledIn.exists_differentiableOn_norm_sub_lt
      hRunge.isCompact hRunge.subset hU hKU hf hε,
    fun happrox => ?_⟩
  refine isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ,
    hΩ.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt fun a ha ε hε => ?_⟩
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
      (isFilledIn_fillIn K Ω).insert Complex.one_lt_rank_real (hΩ.sdiff hKt_cpt.isClosed) z⟩
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
    hRunge₁.isFilledIn.exists_differentiableOn_norm_sub_lt hRunge₁.isCompact hRunge₁.subset
      (hU₁.union isOpen_ball)
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
theorem _root_.IsCompact.isPolynomiallyConvex_image_const_iff_isConnected_compl
    {ι : Type*} [Nonempty ι] {K : Set ℂ} (hK : IsCompact K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ IsConnected Kᶜ := by
  rw [← hK.isBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex,
    holomorphicHull_univ_eq_filledHull hK,
    filledHull_eq_self_iff_isConnected_compl Complex.one_lt_rank_real hK.isBounded]

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
  exact ⟨p, fun z hz ↦ (norm_sub_le_norm_sub_add_norm_sub (f z) (g z) (p.eval z)).trans_lt
    (by linarith [hfg z hz, hgp z hz])⟩

/-- **Polynomial Runge theorem**: a compact set `K ⊆ ℂ` has connected complement `Kᶜ` if and only
if every holomorphic function on an open neighbourhood `U ⊇ K` can be approximated uniformly on `K`
by polynomials `p : Polynomial ℂ`. -/
theorem _root_.IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt
    {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  rw [← filledHull_eq_self_iff_isConnected_compl Complex.one_lt_rank_real hK.isBounded,
    ← fillIn_univ K, fillIn_eq_self_iff_isFilledIn]
  refine ⟨fun hfill U hU hKU f hf ε hε =>
    hfill.exists_polynomial_norm_sub_lt hK hU hKU hf hε, fun h => ?_⟩
  exact ((isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)).mpr
    fun U hU hKU f hf ε hε =>
      let ⟨p, hp⟩ := h U hU hKU f hf ε hε
      ⟨fun z => p.eval z, p.differentiable.differentiableOn, hp⟩).isFilledIn

end TauCeti
