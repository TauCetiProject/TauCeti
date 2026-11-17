/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Complex.HolomorphicHull.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Runge's approximation theorem, finite-rank operators, and holomorphic hulls

This file proves Runge's approximation theorem on arbitrary open subsets `Ω ⊆ ℂ` (neither `Ω`
nor `K` need be connected), together with its finite-rank operator form, the topological
characterization of holomorphic hulls, polynomial Runge approximation, and finite-jet Runge
interpolation.

## Overview

* **Finite-rank Runge operator (`TauCeti.IsFilledIn.exists_norm_sub_sum_smul_le`).**
  Combining the discretized Cauchy–Pompeiu formula
  (`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`) with simple-fraction Runge approximation
  (`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`), for any compact `K ⊆ Ω` filled
  in `Ω`, any open `V ⊇ K`, and any `ε > 0`, there are finitely many evaluation points
  `ζ i ∈ V \ K` and functions `g i` holomorphic on `Ω`, depending only on `Ω`, `K`, `V`, and
  `ε`, such that every `f : ℂ → F` into a complex normed space `F`, holomorphic on `V` and
  bounded by `M` there, satisfies `‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` on `K`. Specializing
  `V = interior L` for a compact collar `L` with `K ⊆ interior L` and `L ⊆ U` (for instance
  obtained from `exists_compact_between`) gives a fixed finite-rank linear approximation operator
  controlled by `sup_L ‖f‖`, which commutes with differentiation and holomorphic dependence on
  external parameters.

* **Runge's theorem and equivalences.**
  Applying the finite-rank operator on a compact collar gives vector-valued Runge approximation
  (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`). Conversely, if a compact `K ⊆ Ω`
  admits uniform approximation by `Ω`-holomorphic functions of every simple fraction `(z - a)⁻¹`
  with `a ∈ Ω \ K`, the maximum modulus principle applied to `(z - a) * g z - 1` on a relatively
  compact component of `Ω \ K` yields a contradiction, establishing the scalar equivalences
  `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt` and
  `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`.

* **Holomorphic hull characterization (`TauCeti.holomorphicHull_eq_union`).**
  Inserting a single point into a filled compact subset of `ℂ` preserves filledness
  (`TauCeti.IsFilledIn.insert` and `TauCeti.isConnected_ball_sdiff_singleton`), so Runge
  approximation applied to a locally constant function separating `K` from `a ∈ Ω \ K` yields a
  holomorphic function on `Ω` with `‖g‖ < 1` on `K` and `1 < ‖g a‖`
  (`TauCeti.IsFilledIn.exists_differentiableOn_norm_lt_one_lt`). Hence `K` is filled in `Ω` iff
  `holomorphicHull Ω K = K` (`TauCeti.isFilledIn_iff_holomorphicHull_eq`), and for every compact
  `K ⊆ Ω`, `holomorphicHull Ω K` equals `K` together with the relatively compact components of
  `Ω \ K`.

* **Polynomial Runge (`Ω = univ`).**
  Specializing to `Ω = univ` and combining with Taylor polynomial approximation of entire
  functions (`Differentiable.exists_polynomial_norm_sub_lt`) shows that for compact `K ⊆ ℂ`,
  connectedness of `Kᶜ` is equivalent to polynomial convexity of `K`
  (`TauCeti.isConnected_compl_iff_isPolynomiallyConvex`) and to uniform polynomial approximation of
  every function holomorphic on a neighbourhood of `K`
  (`TauCeti.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`).

* **Finite-jet Runge interpolation
  (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`).**
  For a Banach-space-valued function `f : ℂ → F` holomorphic near `K`, a finite set `s ⊆ K`,
  and prescribed jet orders `m : ℂ → ℕ`, constructing an entire Hermite interpolant `P` via
  `TauCeti.exists_analyticOnNhd_iteratedDeriv_eq`, factoring `f - P = Q • q` with
  `Q z = ∏ a ∈ s, (z - a) ^ m a` via `AnalyticOnNhd.exists_eq_prod_pow_smul`, and applying Runge
  approximation to `q` yields an `Ω`-holomorphic approximant matching all derivatives of order
  `< m a` at every `a ∈ s`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1 and Theorem 1.3.9.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6 and Theorem 13.9.
-/

public section

open Bornology Filter Metric Set
open scoped Polynomial Topology

universe u

namespace TauCeti

variable {K Ω : Set ℂ}

/-! ### Finite-rank Runge operator and vector-valued Runge approximation -/

/-- **Finite-rank Runge operator.** Let `K` be a compact set filled in an open set `Ω ⊆ ℂ`, and
let `V` be any open neighbourhood of `K`. For every `ε > 0` there exist finitely many evaluation
points `ζ i ∈ V \ K` and functions `g i : ℂ → ℂ` holomorphic on `Ω`, depending only on `Ω`, `K`,
`V`, and `ε`, such that every function `f : ℂ → F` into a complex normed space that is
holomorphic on `V` and bounded in norm by `M` there satisfies
`‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

Applying this with `V = interior L` for a compact collar `L` with `K ⊆ interior L` and `L ⊆ U`
yields a finite-rank approximation operator controlled by `sup_L ‖f‖` for every `f` holomorphic
on `U`. -/
theorem IsFilledIn.exists_norm_sub_sum_smul_le (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {V : Set ℂ} (hV : IsOpen V)
    (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨N, ζ, c, hζ, hrat⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (half_pos hε)
  set C := ∑ i, ‖c i‖
  have : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  set δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by positivity
  have hh_ex : ∀ i, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧
      ∀ w ∈ K, ‖(w - ζ i)⁻¹ - h w‖ < δ := fun i ↦
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 hδ
  choose h hh_diff hh_lt using hh_ex
  refine ⟨N, ζ, fun i w ↦ c i * h i w, hζ,
    fun i ↦ (differentiableOn_const (c i)).mul (hh_diff i), fun {F} _ _ f M hf hM w hw ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w (hKV hw))
  have hsplit : f w - ∑ i, (c i * h i w) • f (ζ i) =
      (f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - h i w)) • f (ζ i) := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, sub_add_sub_cancel]
  have hsum_err : ‖∑ i, (c i * ((w - ζ i)⁻¹ - h i w)) • f (ζ i)‖ ≤ ε / 2 * M := by
    calc ‖∑ i, (c i * ((w - ζ i)⁻¹ - h i w)) • f (ζ i)‖
        ≤ ∑ i, ‖(c i * ((w - ζ i)⁻¹ - h i w)) • f (ζ i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖(w - ζ i)⁻¹ - h i w‖ * ‖f (ζ i)‖ := by
          simp only [norm_smul, norm_mul]
      _ ≤ ∑ i, ‖c i‖ * δ * M := Finset.sum_le_sum fun i _ ↦ by
          have h1 : ‖c i‖ * ‖(w - ζ i)⁻¹ - h i w‖ ≤ ‖c i‖ * δ :=
            mul_le_mul_of_nonneg_left (hh_lt i w hw).le (norm_nonneg _)
          exact mul_le_mul h1 (hM (ζ i) (hζ i).1) (norm_nonneg _) (by positivity)
      _ = C * δ * M := by simp only [C, Finset.sum_mul]
      _ ≤ (C + 1) * δ * M := by gcongr; linarith
      _ = ε / 2 * M := by
          have hC1 : C + 1 ≠ 0 := by positivity
          dsimp only [δ]
          field_simp
  calc ‖f w - ∑ i, (c i * h i w) • f (ζ i)‖
      ≤ ‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - h i w)) • f (ζ i)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε / 2 * M + ε / 2 * M := add_le_add (hrat f M hf hM w hw) hsum_err
    _ = ε * M := by ring

/-- **Runge's approximation theorem** for functions with values in a complex normed space. If `K`
is compact and filled in an open set `Ω ⊆ ℂ`, every function `f : ℂ → F` holomorphic on an open
neighbourhood `U` of `K` can be uniformly approximated on `K` by functions holomorphic on `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn (hf.continuousOn.mono hLU)
  set M := max M₀ 0 + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨N, ζ, g, -, hg, hbound⟩ := hfill.exists_norm_sub_sum_smul_le.{u} hΩ hK hKΩ
    isOpen_interior hKL (div_pos hε (mul_pos two_pos hMpos))
  refine ⟨fun w ↦ ∑ i, g i w • f (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ (hg i).smul_const (f (ζ i)), fun w hw ↦ ?_⟩
  have hle := hbound f M (hf.mono (interior_subset.trans hLU))
    (fun z hz ↦ (hM₀ z (interior_subset hz)).trans (by linarith [le_max_left M₀ 0])) w hw
  have heq : ε / (2 * M) * M = ε / 2 := by field_simp
  linarith

/-! ### Scalar Runge equivalences -/

/-- **Simple-fraction Runge equivalence.** A compact subset `K` of an open set `Ω ⊆ ℂ` is
filled in `Ω` if and only if every simple fraction `(z - a)⁻¹` with `a ∈ Ω \ K` is uniformly
approximable on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
        ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε := by
  refine ⟨fun h a ha ε hε ↦ h.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ ha.2 hε,
    fun h ↦ ?_⟩
  rw [isFilledIn_iff]
  rintro a ha ⟨hcpt, hsub⟩
  set C := connectedComponentIn (Ω \ K) a
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall a
  set M := max R 0 + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨g, hg, hgK⟩ := h a ha (1 / (2 * M)) (by positivity)
  set F : ℂ → ℂ := fun z ↦ (z - a) * g z - 1
  have hF_diff : DifferentiableOn ℂ F Ω :=
    ((differentiableOn_id.sub (differentiableOn_const a)).mul hg).sub (differentiableOn_const 1)
  have hfr : frontier C ⊆ K := fun y hy ↦ by
    by_contra hyK
    exact frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) a hy
      ⟨hsub hy.1, hyK⟩
  have hF_bound : ∀ z ∈ frontier C, ‖F z‖ ≤ 1 / 2 := fun z hz ↦ by
    have hzK : z ∈ K := hfr hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun hEq ↦ ha.2 (hEq ▸ hzK)
    have hFz : F z = (z - a) * (g z - (z - a)⁻¹) := by
      dsimp only [F]
      rw [mul_sub, mul_inv_cancel₀ hza]
    have hdist : ‖z - a‖ ≤ M := by
      have h1 : ‖z - a‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hzK
      linarith [le_max_left R 0]
    calc ‖F z‖ = ‖z - a‖ * ‖(z - a)⁻¹ - g z‖ := by
          rw [hFz, norm_mul, norm_sub_rev (g z)]
      _ ≤ M * (1 / (2 * M)) :=
          mul_le_mul hdist (hgK z hzK).le (norm_nonneg _) hMpos.le
      _ = 1 / 2 := by field_simp
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcpt.isBounded.subset subset_closure)
    ⟨hF_diff.mono (subset_closure.trans hsub), hF_diff.continuousOn.mono hsub⟩
    hF_bound (subset_closure (mem_connectedComponentIn ha))
  simp only [F, sub_self, zero_mul, zero_sub, norm_neg, norm_one] at hle
  norm_num at hle

/-- **Universal scalar Runge equivalence.** A compact subset `K` of an open set `Ω ⊆ ℂ` is
filled in `Ω` if and only if every function holomorphic on an open neighbourhood of `K` can be
uniformly approximated on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
          ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
            ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun h U hU hKU f hf ε hε ↦
      h.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU hf hε,
    fun h ↦ (isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ).2
      fun a ha ε hε ↦ h {a}ᶜ isClosed_singleton.isOpen_compl
        (fun z hz hza ↦ ha.2 (hza ▸ hz)) (fun z ↦ (z - a)⁻¹)
        ((differentiableOn_id.sub (differentiableOn_const a)).inv fun z hz hza ↦
          hz (sub_eq_zero.1 hza))
        ε hε⟩

/-! ### Point separation and characterization of the holomorphic hull -/

/-- **Holomorphic separation from a filled compact set.** If `K` is compact and filled in an
open set `Ω ⊆ ℂ`, every point `a ∈ Ω \ K` is separated from `K` by a function holomorphic on `Ω`
of modulus `< 1` on `K` and `> 1` at `a`. -/
theorem IsFilledIn.exists_differentiableOn_norm_lt_one_lt (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∈ Ω \ K) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      (∀ z ∈ K, ‖g z‖ < 1) ∧ 1 < ‖g a‖ := by
  classical
  -- Adjoining `a` preserves filledness because punctured open discs in `ℂ` are connected.
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hins : IsFilledIn (insert a K) Ω :=
    hfill.insert (hΩ.sdiff hK.isClosed) fun U hU ↦ by
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
      exact ⟨ball a r, ball_mem_nhds a hr, hball, isConnected_ball_sdiff_singleton hrank a hr⟩
  obtain ⟨U₁, U₂, hU₁, hU₂, hKU₁, haU₂, hdisj⟩ := hK.separation_of_notMem ha.2
  -- Approximate the locally constant function equal to `0` on `U₁` and `2` on `U₂`.
  set f : ℂ → ℂ := fun z ↦ if z ∈ U₂ then 2 else 0
  have hf : DifferentiableOn ℂ f (U₁ ∪ U₂) := fun z hz ↦ by
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases hz with hz₁ | hz₂
    · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hU₁.mem_nhds hz₁] with w hw
      simp [f, hdisj.notMem_of_mem_left hw]
    · refine (differentiableAt_const (2 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hU₂.mem_nhds hz₂] with w hw
      simp [f, hw]
  obtain ⟨g, hg, hfg⟩ := hins.exists_differentiableOn_norm_sub_lt hΩ (hK.insert a)
    (insert_subset ha.1 hKΩ) (hU₁.union hU₂)
    (insert_subset (Or.inr haU₂) (hKU₁.trans subset_union_left)) hf
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨g, hg, fun z hz ↦ ?_, ?_⟩
  · have hz_lt := hfg z (Or.inr hz)
    have hfz : f z = 0 := by simp [f, hdisj.notMem_of_mem_left (hKU₁ hz)]
    rw [hfz, zero_sub, norm_neg] at hz_lt
    linarith
  · have ha_lt := hfg a (Or.inl rfl)
    have hfa : f a = 2 := by simp [f, haU₂]
    rw [hfa] at ha_lt
    have htri : (2 : ℝ) ≤ ‖(2 : ℂ) - g a‖ + ‖g a‖ := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [← h2]
      simpa [sub_add_cancel] using norm_add_le ((2 : ℂ) - g a) (g a)
    linarith

/-- A compact subset `K` of an open set `Ω ⊆ ℂ` is filled in `Ω` if and only if it equals its
holomorphic hull in `Ω`. -/
theorem isFilledIn_iff_holomorphicHull_eq
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ holomorphicHull Ω K = K :=
  ⟨fun hfill ↦ (holomorphicHull_eq_self_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt
      hKΩ).2 fun _ ha ↦ hfill.exists_differentiableOn_norm_lt_one_lt hΩ hK hKΩ ha,
    fun heq ↦ heq ▸ isFilledIn_holomorphicHull hΩ K⟩

/-- **Point-separation Runge equivalence.** A compact subset `K` of an open set `Ω ⊆ ℂ` is
filled in `Ω` if and only if every point of `Ω \ K` is separated from `K` by a function
holomorphic on `Ω` of modulus `< 1` on `K` and `> 1` at the point. -/
theorem isFilledIn_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ z ∈ Ω \ K, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
        (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  rw [isFilledIn_iff_holomorphicHull_eq hΩ hK hKΩ,
    holomorphicHull_eq_self_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt hKΩ]

/-- **Topological characterization of the holomorphic hull.** For a compact subset `K` of an open
set `Ω ⊆ ℂ`, the holomorphic hull `holomorphicHull Ω K` is the union of `K` with all connected
components of `Ω \ K` that are relatively compact in `Ω`. -/
theorem holomorphicHull_eq_union (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K =
      K ∪ {z | z ∈ Ω \ K ∧
        IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  set K' := K ∪ {z | z ∈ Ω \ K ∧
    IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
  have hΩK : IsOpen (Ω \ K) := hΩ.sdiff hK.isClosed
  have hK'sub : K' ⊆ holomorphicHull Ω K := by
    refine union_subset (subset_holomorphicHull hKΩ) ?_
    rintro z ⟨hz, hcpt, hsub⟩
    exact connectedComponentIn_subset_holomorphicHull hΩK
      (hcpt.isBounded.subset subset_closure) hsub (mem_connectedComponentIn hz)
  -- Each component of `Ω \ K` through a point of `Ω \ K'` stays inside `Ω \ K'`.
  have hcomp_sub : ∀ x ∈ Ω \ K', connectedComponentIn (Ω \ K) x ⊆ Ω \ K' := by
    intro x hx y hy
    have hyΩK : y ∈ Ω \ K := connectedComponentIn_subset _ _ hy
    refine ⟨hyΩK.1, fun hyK' ↦ ?_⟩
    rcases hyK' with hyK | ⟨-, hcpt, hsub⟩
    · exact hyΩK.2 hyK
    · rw [← connectedComponentIn_eq hy] at hcpt hsub
      exact hx.2 (Or.inr ⟨⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩, hcpt, hsub⟩)
  have hOpen : IsOpen (Ω \ K') := isOpen_iff_mem_nhds.2 fun x hx ↦
    Filter.mem_of_superset
      (hΩK.connectedComponentIn.mem_nhds
        (mem_connectedComponentIn ⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩))
      (hcomp_sub x hx)
  have hK'eq : K' = holomorphicHull Ω K \ (Ω \ K') := by
    ext z
    simp only [Set.mem_sdiff, not_and, not_not]
    exact ⟨fun hz ↦ ⟨hK'sub hz, fun _ ↦ hz⟩,
      fun ⟨hzH, hz⟩ ↦ hz (holomorphicHull_subset Ω K hzH)⟩
  have hK'cpt : IsCompact K' := hK'eq ▸ (hK.holomorphicHull hΩ hKΩ).diff hOpen
  have hK'fill : IsFilledIn K' Ω := by
    rw [isFilledIn_iff]
    intro x hx
    have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩
    have hcomp_eq : connectedComponentIn (Ω \ K') x = connectedComponentIn (Ω \ K) x :=
      Subset.antisymm
        (connectedComponentIn_mono x (sdiff_subset_sdiff_right subset_union_left))
        (isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hxΩK) (hcomp_sub x hx))
    rw [hcomp_eq]
    rintro ⟨hcpt, hsub⟩
    exact hx.2 (Or.inr ⟨hxΩK, hcpt, hsub⟩)
  refine Subset.antisymm ?_ hK'sub
  calc holomorphicHull Ω K
      ⊆ holomorphicHull Ω K' := holomorphicHull_mono subset_union_left
    _ = K' := (isFilledIn_iff_holomorphicHull_eq hΩ hK'cpt
        (hK'sub.trans (holomorphicHull_subset Ω K))).1 hK'fill

/-! ### Polynomial Runge theorem -/

/-- A compact subset `K ⊆ ℂ` has connected complement if and only if its image in `Fin 1 → ℂ`
is polynomially convex. -/
theorem isConnected_compl_iff_isPolynomiallyConvex (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsPolynomiallyConvex (Function.const (Fin 1) '' K) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  rw [isConnected_compl_iff_filledHull_eq hrank hK.isBounded,
    ← isFilledIn_univ_iff hK.isClosed,
    isFilledIn_iff_holomorphicHull_eq isOpen_univ hK (subset_univ K),
    holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex hK.isBounded]

/-- **Polynomial Runge theorem.** If `K ⊆ ℂ` is compact with connected complement, every
function holomorphic on an open neighbourhood of `K` can be uniformly approximated on `K` by
complex polynomials. -/
theorem exists_polynomial_norm_sub_lt_of_isConnected_compl (hK : IsCompact K)
    (hconn : IsConnected Kᶜ) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hfill : IsFilledIn K univ :=
    (isFilledIn_univ_iff hK.isClosed).2
      ((isConnected_compl_iff_filledHull_eq hrank hK.isBounded).1 hconn)
  obtain ⟨g, hg, hfg⟩ := hfill.exists_differentiableOn_norm_sub_lt isOpen_univ hK
    (subset_univ K) hU hKU hf (half_pos hε)
  obtain ⟨p, hgp⟩ := (differentiableOn_univ.1 hg).exists_polynomial_norm_sub_lt hK.isBounded
    (half_pos hε)
  refine ⟨p, fun z hz ↦ ?_⟩
  calc ‖f z - p.eval z‖
      = ‖(f z - g z) + (g z - p.eval z)‖ := by ring_nf
    _ ≤ ‖f z - g z‖ + ‖g z - p.eval z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgp z hz)
    _ = ε := add_halves ε

/-- **Polynomial Runge equivalence.** A compact subset `K ⊆ ℂ` has connected complement if and
only if every function holomorphic on an open neighbourhood of `K` is uniformly approximable on
`K` by complex polynomials. -/
theorem isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
          ∀ ε > 0, ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  refine ⟨fun hconn U hU hKU f hf ε hε ↦
      exists_polynomial_norm_sub_lt_of_isConnected_compl hK hconn hU hKU hf hε, fun h ↦ ?_⟩
  rw [isConnected_compl_iff_filledHull_eq hrank hK.isBounded, ← isFilledIn_univ_iff hK.isClosed,
    isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt isOpen_univ hK (subset_univ K)]
  intro U hU hKU f hf ε hε
  obtain ⟨p, hp⟩ := h U hU hKU f hf ε hε
  exact ⟨fun z ↦ p.eval z, p.differentiable.differentiableOn, hp⟩

/-! ### Finite-jet Runge interpolation -/

/-- **Finite-jet Runge interpolation.** Let `K` be compact and filled in an open set `Ω ⊆ ℂ`,
let `f : ℂ → F` be holomorphic on an open neighbourhood `U` of `K` with values in a complex
Banach space `F`, and let `s ⊆ K` be a finite set with prescribed jet orders `m : ℂ → ℕ`. For
every `ε > 0`, there is a function `g : ℂ → F` holomorphic on `Ω` such that `‖f z - g z‖ < ε` on
`K` and `iteratedDeriv k g a = iteratedDeriv k f a` for all `a ∈ s` and `k < m a`.

The jet matching holds regardless of whether `K` has interior or points of `s` lie on `frontier K`.
-/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (hfill : IsFilledIn K Ω)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (s : Finset ℂ) (hs : (s : Set ℂ) ⊆ K)
    (m : ℂ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧
      (∀ z ∈ K, ‖f z - g z‖ < ε) ∧
      ∀ a ∈ s, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a := by
  classical
  -- Step 1: interpolate the prescribed jets by an entire map `P`, then factor `f - P = Q • q`.
  obtain ⟨P, hP_an, hP_deriv⟩ :=
    exists_analyticOnNhd_iteratedDeriv_eq s m fun a k ↦ iteratedDeriv k f a
  have hf_an : AnalyticOnNhd ℂ f U := (Complex.analyticOnNhd_iff_differentiableOn hU).2 hf
  have hfP_an : AnalyticOnNhd ℂ (f - P) U := hf_an.sub (hP_an.mono (subset_univ U))
  have hord : ∀ a ∈ s, (m a : ℕ∞) ≤ analyticOrderAt (f - P) a := fun a ha ↦ by
    have haU : a ∈ U := hKU (hs ha)
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hfP_an a haU)]
    intro k hk
    rw [iteratedDeriv_sub ((hf_an a haU).contDiffAt.of_le le_top)
      ((hP_an a trivial).contDiffAt.of_le le_top), hP_deriv a ha k hk, sub_self]
  obtain ⟨q, hq_an, hq_eq⟩ := hfP_an.exists_eq_prod_pow_smul s m hord
  -- Step 2: approximate the quotient `q` by `g₀` holomorphic on `Ω`, setting `g = P + Q • g₀`.
  set Q : ℂ → ℂ := fun z ↦ ∏ a ∈ s, (z - a) ^ m a
  have hQ_an : AnalyticOnNhd ℂ Q univ :=
    Finset.analyticOnNhd_fun_prod s fun a _ ↦
      (analyticOnNhd_id.sub analyticOnNhd_const).pow (m a)
  obtain ⟨M₀, hM₀⟩ :=
    hK.exists_bound_of_continuousOn (hQ_an.continuousOn.mono (subset_univ K))
  set M := max M₀ 0 + 1
  have hMpos : 0 < M := by positivity
  obtain ⟨g₀, hg₀, hqg₀⟩ := hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU
    hq_an.differentiableOn (div_pos hε hMpos)
  refine ⟨fun z ↦ P z + Q z • g₀ z,
    (hP_an.differentiableOn.mono (subset_univ Ω)).add
      ((hQ_an.differentiableOn.mono (subset_univ Ω)).smul hg₀),
    fun z hz ↦ ?_, fun a ha k hk ↦ ?_⟩
  · have hsub : f z - (P z + Q z • g₀ z) = Q z • (q z - g₀ z) := by
      have h1 : f z - P z = Q z • q z := hq_eq z
      rw [← sub_sub, h1, smul_sub]
    have hQz : ‖Q z‖ ≤ M := (hM₀ z hz).trans (by linarith [le_max_left M₀ 0])
    calc ‖f z - (P z + Q z • g₀ z)‖
        = ‖Q z‖ * ‖q z - g₀ z‖ := by rw [hsub, norm_smul]
      _ ≤ M * ‖q z - g₀ z‖ := mul_le_mul_of_nonneg_right hQz (norm_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left (hqg₀ z hz) hMpos
      _ = ε := mul_div_cancel₀ ε hMpos.ne'
  · have haΩ : a ∈ Ω := hKΩ (hs ha)
    have hg₀_an : AnalyticAt ℂ g₀ a :=
      (Complex.analyticOnNhd_iff_differentiableOn hΩ).2 hg₀ a haΩ
    have hQg₀_an : AnalyticAt ℂ (fun z ↦ Q z • g₀ z) a := (hQ_an a trivial).smul hg₀_an
    have hrest_an : AnalyticOnNhd ℂ (fun z ↦ ∏ x ∈ s.erase a, (z - x) ^ m x) univ :=
      Finset.analyticOnNhd_fun_prod (s.erase a) fun x _ ↦
        (analyticOnNhd_id.sub analyticOnNhd_const).pow (m x)
    have hQg₀_ord : (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ Q z • g₀ z) a :=
      hQg₀_an.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
        ((hrest_an a trivial).continuousAt.smul hg₀_an.continuousAt)
        (Eventually.of_forall fun z ↦ by
          dsimp only [Q]
          rw [← Finset.mul_prod_erase s (fun x ↦ (z - x) ^ m x) ha, mul_smul]
          rfl)
    have hzero : iteratedDeriv k (fun z ↦ Q z • g₀ z) a = 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQg₀_an).1 hQg₀_ord k hk
    rw [iteratedDeriv_fun_add ((hP_an a trivial).contDiffAt.of_le le_top)
      (hQg₀_an.contDiffAt.of_le le_top), hzero, add_zero, hP_deriv a ha k hk]

end TauCeti
