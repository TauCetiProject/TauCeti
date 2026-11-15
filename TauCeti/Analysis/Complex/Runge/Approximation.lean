/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Analysis.Complex.Runge.Operator
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Normed.Module.FilledIn

/-!
# Runge's approximation theorem and holomorphic hulls

This file proves Runge's approximation theorem in its domain-relative form on open subsets
`Ω ⊆ ℂ`: a compact subset `K ⊆ Ω` admits uniform approximation of neighbourhood-holomorphic
functions by `Ω`-holomorphic functions if and only if `(Ω, K)` is a Runge compact pair, i.e. no
connected component of `Ω \ K` is relatively compact in `Ω`
(`TauCeti.isRungeCompactPair_iff_approximation`). Together with the explicit filled compact
exhaustions `TauCeti.rungeExhaustion Ω` (`TauCeti.Analysis.Normed.Module.Exhaustion`), these
equivalences provide the compact-to-global patching step for constructing global holomorphic
functions on arbitrary open plane sets.

From scalar Runge approximation we identify `TauCeti.holomorphicHull Ω K` with the union of `K`
and all relatively compact connected components of `Ω \ K` in `Ω`
(`TauCeti.holomorphicHull_eq_fill`), establishing `holomorphicHull Ω K = K ↔ IsFilledIn K Ω`.
Specializing to `Ω = Set.univ` links `TauCeti.holomorphicHull Set.univ K = TauCeti.filledHull K`,
polynomial convexity in dimension one, and uniform polynomial approximation on compact sets with
connected complement.

## Main results

* `IsOpen.isRungeCompactPair_holomorphicHull` and `IsOpen.isRungeCompactPair_rungeExhaustion`:
  holomorphic hulls of compact subsets and stages of `TauCeti.rungeExhaustion` form Runge compact
  pairs with `Ω`.
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt` and
  `TauCeti.isRungeCompactPair_iff_approximation`: forward uniform Runge approximation and the full
  domain-relative Runge equivalence.
* `TauCeti.holomorphicHull_eq_fill` and `TauCeti.holomorphicHull_eq_self_iff_isFilledIn`:
  topological characterization of `TauCeti.holomorphicHull Ω K` for open `Ω` and compact `K ⊆ Ω`.
* `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq` and
  `TauCeti.isRungeCompactPair_iff_forall_mem_sdiff_exists_differentiableOn_one_lt_norm_le`:
  holomorphic-hull and point-separation criteria for Runge compact pairs.
* `TauCeti.holomorphicHull_univ_eq_filledHull`,
  `IsCompact.isConnected_compl_iff_isPolynomiallyConvex`, and
  `IsCompact.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt`:
  specialization to `Ω = Set.univ` and the polynomial Runge theorem on `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorems 1.3.1 and 1.3.9.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.5.
-/

public section

open Metric Set
open scoped NNReal Topology

namespace TauCeti

/-- For an open set `Ω ⊆ ℂ` and compact `K ⊆ Ω`, `holomorphicHull Ω K` forms a Runge compact pair
with `Ω`. -/
theorem _root_.IsOpen.isRungeCompactPair_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω (holomorphicHull Ω K) :=
  isRungeCompactPair_iff.mpr
    ⟨hΩ, isCompact_holomorphicHull hK hKΩ, holomorphicHull_subset, isFilledIn_holomorphicHull hΩ⟩

/-- Every stage of `TauCeti.rungeExhaustion Ω` forms a Runge compact pair with an open `Ω ⊆ ℂ`. -/
theorem _root_.IsOpen.isRungeCompactPair_rungeExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    IsRungeCompactPair Ω (rungeExhaustion Ω n) :=
  isRungeCompactPair_iff.mpr
    ⟨hΩ, isCompact_rungeExhaustion Ω n, rungeExhaustion_subset Ω n, isFilledIn_rungeExhaustion hΩ n⟩

/-- Forward Runge approximation for a `IsRungeCompactPair`: every function holomorphic on an open
neighbourhood `U` of `K` can be approximated uniformly on `K` by functions holomorphic on `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUO, hop⟩ := exists_finite_rank_runge_operator hRunge hU hKU
  obtain ⟨M, hM⟩ :=
    hL.bddAbove_image (hf.continuousOn.mono (hLUO.trans inter_subset_left)).norm
  set B : ℝ := max M 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hLB : ∀ z ∈ L, ‖f z‖ ≤ B := fun z hz =>
    (hM ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  set ε' : ℝ := ε / (2 * (B + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨N, ζ, w, g, -, hg_diff, hbound⟩ := hop ε' hε'
  refine ⟨fun z => ∑ j : Fin N, w j * f (ζ j) * g j z, ?_, fun z hz => ?_⟩
  · exact DifferentiableOn.fun_sum fun j _ => (hg_diff j).const_mul (w j * f (ζ j))
  · calc ‖f z - ∑ j : Fin N, w j * f (ζ j) * g j z‖
        ≤ ε' * B := hbound f hf B hB0 hLB z hz
      _ = (ε / 2) * (B / (B + 1)) := by
          simp only [ε']
          field_simp
      _ ≤ (ε / 2) * 1 := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = ε / 2 := mul_one _
      _ < ε := half_lt_self hε

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
  refine isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ, isFilledIn_iff.mpr fun x hx ⟨hCc, hCΩ⟩ => ?_⟩
  set C : Set ℂ := connectedComponentIn (Ω \ K) x
  have hKU : K ⊆ {x}ᶜ := fun w hw hwx => hx.2 (hwx ▸ hw)
  have hf_diff : DifferentiableOn ℂ (fun z : ℂ => (z - x)⁻¹) {x}ᶜ :=
    (differentiableOn_id.sub_const x).inv fun _ hz => sub_ne_zero.mpr hz
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_id.sub continuous_const).norm.continuousOn
  set B : ℝ := max M 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hKB : ∀ w ∈ K, ‖w - x‖ ≤ B := fun w hw =>
    (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  set ε : ℝ := (2 * (B + 1))⁻¹
  have hε : 0 < ε := by positivity
  obtain ⟨g, hg_diff, hg_lt⟩ := happrox {x}ᶜ isOpen_ne hKU (fun z => (z - x)⁻¹) hf_diff ε hε
  let h : ℂ → ℂ := fun z => 1 - (z - x) * g z
  have hh_diff : DifferentiableOn ℂ h (closure C) :=
    ((differentiableOn_id.sub_const x).mul (hg_diff.mono hCΩ)).const_sub 1
  have hh_cl : DiffContOnCl ℂ h C :=
    ⟨hh_diff.mono subset_closure, hh_diff.continuousOn⟩
  have hh_fr : ∀ w ∈ frontier C, ‖h w‖ ≤ (1 / 2 : ℝ) := fun w hw => by
    have hwK : w ∈ K := frontier_connectedComponentIn_sdiff_subset (hΩ.sdiff hK.isClosed) hCΩ hw
    have hwx : w - x ≠ 0 := sub_ne_zero.mpr fun heq => hx.2 (heq ▸ hwK)
    have hfactor : h w = (w - x) * ((w - x)⁻¹ - g w) := by
      simp only [h]
      rw [mul_sub, mul_inv_cancel₀ hwx]
    rw [hfactor, norm_mul]
    calc ‖w - x‖ * ‖(w - x)⁻¹ - g w‖
        ≤ B * ε := mul_le_mul (hKB w hwK) (hg_lt w hwK).le (norm_nonneg _) hB0
      _ = (1 / 2 : ℝ) * (B / (B + 1)) := by
          simp only [ε]
          field_simp
      _ ≤ (1 / 2 : ℝ) * 1 := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = 1 / 2 := mul_one _
  have hhx : ‖h x‖ ≤ (1 / 2 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (hCc.isBounded.subset subset_closure) hh_cl
      hh_fr (subset_closure (mem_connectedComponentIn hx))
  have hhx1 : h x = 1 := by simp [h]
  rw [hhx1, norm_one] at hhx
  linarith

/-- For an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω`, `holomorphicHull Ω K` is compact and
coincides with `TauCeti.fillIn K Ω`, the union of `K` and all connected components of `Ω \ K`
whose closures are compact subsets of `Ω`. -/
theorem holomorphicHull_eq_fill {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) ∧
      holomorphicHull Ω K = K ∪ {z | z ∈ Ω \ K ∧
        IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  rw [← fillIn_def]
  refine ⟨isCompact_holomorphicHull hK hKΩ, Subset.antisymm (fun z hz => ?_)
    (fillIn_subset_holomorphicHull (hΩ.sdiff hK.isClosed) hKΩ)⟩
  set Ktilde : Set ℂ := fillIn K Ω
  by_contra hzKt
  have hKt_cpt : IsCompact Ktilde := hK.fillIn hΩ
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hRunge₁ : IsRungeCompactPair Ω (insert z Ktilde) :=
    isRungeCompactPair_iff.mpr ⟨hΩ, hKt_cpt.insert z,
      insert_subset_iff.mpr ⟨holomorphicHull_subset hz, fillIn_subset hKΩ⟩,
      (isFilledIn_fillIn K Ω).insert hrank (hΩ.sdiff hKt_cpt.isClosed) z⟩
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
  have hf_diff : DifferentiableOn ℂ f (U₁ ∪ U₂) := fun w hw => by
    rcases hw with hw1 | hw2
    · have heq : f =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
        Filter.eventually_of_mem (hU₁.mem_nhds hw1) fun y hy => by simp [f, hy]
      exact (differentiableAt_const 0).congr_of_eventuallyEq heq |>.differentiableWithinAt
    · have heq : f =ᶠ[𝓝 w] fun _ => (1 : ℂ) :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hw2) fun y hy => by
          simp [f, hdisj.notMem_of_mem_right hy]
      exact (differentiableAt_const 1).congr_of_eventuallyEq heq |>.differentiableWithinAt
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
    calc (1 : ℝ) = ‖(1 : ℂ) - g z + g z‖ := by simp
      _ ≤ ‖(1 : ℂ) - g z‖ + ‖g z‖ := norm_add_le _ _
  linarith

/-- For compact `K ⊆ Ω` with `Ω` open, `holomorphicHull Ω K = K` if and only if `K` is filled in
`Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  rw [(holomorphicHull_eq_fill hΩ hK hKΩ).2, ← fillIn_def, fillIn_eq_self_iff_isFilledIn]

/-- For an open set `Ω ⊆ ℂ` and a compact set `K ⊆ ℂ`, `IsRungeCompactPair Ω K` holds if and only
if `holomorphicHull Ω K = K`. -/
theorem isRungeCompactPair_iff_holomorphicHull_eq {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) :
    IsRungeCompactPair Ω K ↔ holomorphicHull Ω K = K := by
  refine ⟨fun h => (holomorphicHull_eq_self_iff_isFilledIn hΩ hK h.subset).mpr h.isFilledIn,
    fun h => ?_⟩
  have hKΩ : K ⊆ Ω := h ▸ holomorphicHull_subset
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
    obtain ⟨f, hf, hfz, hKB⟩ := hsep z ⟨holomorphicHull_subset hz, hzK⟩
    exact hfz.not_ge (norm_le_of_mem_holomorphicHull hz hf hKB)

/-- Every stage of `TauCeti.rungeExhaustion Ω` equals its own holomorphic hull in `Ω`. -/
@[simp]
theorem holomorphicHull_rungeExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    holomorphicHull Ω (rungeExhaustion Ω n) = rungeExhaustion Ω n :=
  (isRungeCompactPair_iff_holomorphicHull_eq hΩ (isCompact_rungeExhaustion Ω n)).mp
    (hΩ.isRungeCompactPair_rungeExhaustion n)

/-- For compact `K ⊆ ℂ`, the entire holomorphic hull `holomorphicHull Set.univ K` equals the
topological filled hull `TauCeti.filledHull K`. -/
theorem holomorphicHull_univ_eq_filledHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Set.univ K = filledHull K := by
  rw [(holomorphicHull_eq_fill isOpen_univ hK (subset_univ K)).2, ← fillIn_def, fillIn_univ]

/-- For compact `K ⊆ ℂ`, the complement `Kᶜ` is connected if and only if the image of `K` in
`Fin 1 → ℂ` is polynomially convex. -/
theorem _root_.IsCompact.isConnected_compl_iff_isPolynomiallyConvex {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsPolynomiallyConvex ((fun z (_ : Fin 1) => z) '' K) := by
  rw [← holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex hK.isBounded,
    holomorphicHull_univ_eq_filledHull hK]
  refine ⟨fun hconn => filledHull_eq_self hconn.isPreconnected fun hb =>
    NormedSpace.unbounded_univ ℝ ℂ (by simpa using hb.union hK.isBounded), fun hfill => ?_⟩
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  simpa only [hfill] using isConnected_compl_filledHull hrank hK.isBounded

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
    ← holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex hK.isBounded,
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

end TauCeti
