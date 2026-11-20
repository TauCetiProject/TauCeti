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
import Mathlib.Analysis.Normed.Module.DoubleDual
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
exhaustions `TauCeti.filledExhaustion Ω` (`TauCeti.Analysis.Normed.Module.Exhaustion`), these
equivalences provide the compact-to-global patching step for constructing global holomorphic
functions on arbitrary open plane sets.

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
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt` and
  `TauCeti.isRungeCompactPair_iff_approximation`: forward uniform Runge approximation of functions
  with values in a complex normed space, and the full domain-relative Runge equivalence.
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
  set B : ℝ := max M 1
  have hB1 : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hKB : ∀ w ∈ K, ‖w - x‖ ≤ B := fun w hw =>
    (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  obtain ⟨g, hg_diff, hg_lt⟩ :=
    happrox {x}ᶜ isOpen_ne hKU (fun z => (z - x)⁻¹) hf_diff (1 / 2 / B) (by positivity)
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
    exact (mul_le_mul (hKB w hwK) (hg_lt w hwK).le (norm_nonneg _) hB1.le).trans_eq
      (mul_div_cancel₀ _ hB1.ne')
  have hhx : ‖h x‖ ≤ (1 / 2 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (hCc.isBounded.subset subset_closure) hh_cl
      hh_fr (subset_closure (mem_connectedComponentIn hx))
  have hhx1 : h x = 1 := by simp [h]
  rw [hhx1, norm_one] at hhx
  linarith

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

end TauCeti
