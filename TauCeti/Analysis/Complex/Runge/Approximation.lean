/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Polynomial.Approximation
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.Manifold.FilledIn
import TauCeti.RingTheory.Polynomial.HermiteInterpolation
import TauCeti.Topology.Compactification.OnePoint.FilledHull
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Perfect

/-!
# Runge's approximation theorem and characterization of holomorphic hulls in the plane

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` (neither assumed connected). This file proves
Runge's approximation theorem together with its operator-theoretic, finite-jet, and prescribed-pole
rational refinements, its converse, and the resulting topological description of the holomorphic
hull `TauCeti.holomorphicHull Ω K`:

1. **Universal linear finite-rank operators and finite-jet interpolation**
   (`TauCeti.IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le` and
   `TauCeti.IsFilledIn.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt`):
   - When `K` is filled in `Ω` (`TauCeti.IsFilledIn K Ω`), choosing a compact collar `L ⊆ U ∩ Ω`
     with `K ⊆ interior L` (`IsCompact.exists_subset_interior_closedBall_sdiff_thickening`),
     discretizing the Cauchy–Pompeiu formula on `(K, interior L)` via
     `IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`, and replacing each simple fraction
     `z ↦ (z - ζ j)⁻¹` (`ζ j ∉ K`) by a function `g j` holomorphic on `Ω` via
     `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt` yields universal linear
     finite-rank holomorphic approximation operators

     `‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B`

     uniformly over all normed-space-valued maps `f : ℂ → F` holomorphic on `U` with `‖f‖ ≤ B` on
     `L`.
   - Combining scalar Runge approximation with Hermite polynomial interpolation
     (`TauCeti.ordinaryHermiteJet_bijective`) and analytic zero extraction
     (`AnalyticOnNhd.exists_eq_prod_pow_smul`) yields approximants on `Ω` that match prescribed
     finite jets of `f` at finitely many marked points of `K` while staying uniformly within `ε` on
     `K`.

2. **Runge equivalence and point separation**
   (`TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`,
   `TauCeti.isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_lt`): for compact `K ⊆ Ω`,
   `IsFilledIn K Ω` holds if and only if every function holomorphic near `K` is uniformly
   approximable on `K` by functions holomorphic on `Ω`, and if and only if every `a ∈ Ω \ K` is
   strictly separated from `K` in modulus by a function holomorphic on `Ω`.
3. **Topological identification of `holomorphicHull Ω K`**
   (`IsCompact.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn`,
   `TauCeti.isFilledIn_iff_holomorphicHull_eq`): for compact `K ⊆ Ω`, `holomorphicHull Ω K` equals
   `K` together with the connected components of `Ω \ K` whose closures are compact and contained in
   `Ω` (equivalently, the bounded components of `Kᶜ` contained in `Ω`), so `K` is filled in `Ω` if
   and only if `holomorphicHull Ω K = K`.
4. **Polynomial and prescribed-pole rational Runge theorems**
   (`IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`,
   `IsCompact.isConnected_compl_iff_isPolynomiallyConvex_image_const`,
   `IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`): for compact `K ⊆ ℂ`, `Kᶜ` is
   connected if and only if `K` is polynomially convex, if and only if every function holomorphic
   near `K` is uniformly approximable on `K` by polynomials; more generally, given any pole set
   `A ⊆ OnePoint ℂ` meeting every connected component of the complement of `K` in the Riemann
   sphere `OnePoint ℂ`, every function holomorphic near `K` is uniformly approximable on `K` by
   rational functions `P(z) + ∑ a ∈ s, Q_a((z - a)⁻¹)` with poles in `A` (and `P = 0` when
   `∞ ∉ A`).

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le`: universal holomorphic
  finite-rank approximation with uniform collar bound `ε * B` for normed-space-valued maps
  `f : ℂ → F`.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: normed-space-valued Runge approximation
  on a filled compact set `K ⊆ Ω`.
* `TauCeti.IsFilledIn.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt`: scalar Runge
  approximation matching prescribed finite jets at finitely many points of `K`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`: equivalence between
  `IsFilledIn K Ω` and Runge approximation.
* `TauCeti.isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_lt`: equivalence between
  `IsFilledIn K Ω` and holomorphic point separation.
* `IsCompact.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn` and
  `TauCeti.isFilledIn_iff_holomorphicHull_eq`: topological formula for `\widehat{K}_Ω` and hull
  characterization of `IsFilledIn K Ω`.
* `IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt` and
  `IsCompact.isConnected_compl_iff_isPolynomiallyConvex_image_const`: polynomial Runge theorem.
* `IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt` and
  `IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`: pole-pushing into a single finite
  pole and rational Runge approximation with poles restricted to a set `A : Set (OnePoint ℂ)`
  meeting each complementary component in the sphere.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1, Lemma 11.3, Corollary 11.4, and
  Theorem 11.7.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.5–13.9.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1
  and Theorem 1.3.4.
-/

public section

open Bornology Complex Metric Polynomial Set
open scoped OnePoint Topology

universe u

namespace TauCeti

section FiniteRank

/-- **Universal holomorphic finite-rank approximation operator.** Let `K ⊆ Ω` be a compact set
filled in an open set `Ω ⊆ ℂ`, and let `U` be an open neighbourhood of `K`. There exists a compact
collar `L ⊆ U ∩ Ω` with `K ⊆ interior L` such that for every `ε > 0`, there exist sample nodes
`ζ : Fin N → ℂ` in `interior L \ K`, scalar weights `w : Fin N → ℂ`, and functions
`g : Fin N → ℂ → ℂ` holomorphic on `Ω` satisfying

`‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B`

for all `z ∈ K` and every normed-space-valued function `f : ℂ → F` holomorphic on `U` with
`‖f‖ ≤ B` on `L`. -/
theorem IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le {K Ω U : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
          (∀ j, ζ j ∈ interior L \ K) ∧
          (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
          ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {B : ℝ},
            DifferentiableOn ℂ f U → (∀ z ∈ L, ‖f z‖ ≤ B) →
            ∀ z ∈ K, ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B := by
  obtain ⟨n, hKL⟩ :=
    hK.exists_subset_interior_closedBall_sdiff_thickening (hU.inter hΩ) (subset_inter hKU hKΩ)
  set L : Set ℂ := closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (U ∩ Ω)ᶜ
  have hL : IsCompact L := (isCompact_closedBall 0 (n + 1)).diff isOpen_thickening
  have hLUΩ : L ⊆ U ∩ Ω := fun z hz ↦
    by_contra fun hz' ↦ hz.2 (self_subset_thickening (by positivity) _ hz')
  refine ⟨L, hL, hKL, hLUΩ, fun {ε} hε ↦ ?_⟩
  obtain ⟨N, ζ, w, hζ, hrat⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} isOpen_interior hKL (half_pos hε)
  set S : ℝ := ∑ j : Fin N, ‖w j‖
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hS1_pos : 0 < S + 1 := add_pos_of_nonneg_of_pos hS_nonneg one_pos
  set η : ℝ := ε / (2 * (S + 1))
  have hη : 0 < η := by positivity
  have hpole (j : Fin N) :
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ ξ ∈ K, ‖(ξ - ζ j)⁻¹ - g ξ‖ < η :=
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ j).2 hη
  choose g hg_diff hg_err using hpole
  refine ⟨N, ζ, w, g, hζ, hg_diff, fun {F} _ _ {f B} hf hBL ξ hξ ↦ ?_⟩
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hBL ξ (interior_subset (hKL hξ)))
  have hf_intL : DifferentiableOn ℂ f (interior L) :=
    hf.mono (interior_subset.trans (hLUΩ.trans inter_subset_left))
  have hB_intL : ∀ z ∈ interior L, ‖f z‖ ≤ B := fun z hz ↦ hBL z (interior_subset hz)
  have hpole_err :
      ‖(∑ j, (w j * (ξ - ζ j)⁻¹) • f (ζ j)) - ∑ j, (w j * g j ξ) • f (ζ j)‖ ≤ ε / 2 * B := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ j, ((w j * (ξ - ζ j)⁻¹) • f (ζ j) - (w j * g j ξ) • f (ζ j))‖
        ≤ ∑ j, ‖(w j * (ξ - ζ j)⁻¹) • f (ζ j) - (w j * g j ξ) • f (ζ j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖w j‖ * η * B := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [← sub_smul, ← mul_sub, norm_smul, norm_mul]
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hg_err j ξ hξ).le (norm_nonneg _))
            (hBL (ζ j) (interior_subset (hζ j).1)) (norm_nonneg _) (by positivity)
      _ = S * η * B := by simp only [S, Finset.sum_mul]
      _ ≤ (S + 1) * η * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hη.le) hB₀
      _ = ε / 2 * B := by
          dsimp only [η]
          field_simp [hS1_pos.ne']
  calc ‖f ξ - ∑ j, (w j * g j ξ) • f (ζ j)‖
      ≤ ‖f ξ - ∑ j, (w j * (ξ - ζ j)⁻¹) • f (ζ j)‖ +
          ‖(∑ j, (w j * (ξ - ζ j)⁻¹) • f (ζ j)) - ∑ j, (w j * g j ξ) • f (ζ j)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 * B + ε / 2 * B := add_le_add (hrat f B hf_intL hB_intL ξ hξ) hpole_err
    _ = ε * B := by ring

/-- **Normed-space-valued Runge approximation.** If `K` is a compact subset filled in an open set
`Ω ⊆ ℂ`, then every normed-space-valued function `f : ℂ → F` holomorphic on an open neighbourhood
`U` of `K` is uniformly approximable on `K` by functions holomorphic on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {K Ω U : Set ℂ} (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUΩ, hFR⟩ :=
    hfill.exists_differentiableOn_sum_smul_norm_sub_le.{u} hΩ hK hKΩ hU hKU
  obtain ⟨M₀, hM₀⟩ :=
    hL.exists_bound_of_continuousOn (hf.continuousOn.mono (hLUΩ.trans inter_subset_left))
  set B : ℝ := max M₀ 0
  have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos (le_max_right M₀ 0) one_pos
  have hBL : ∀ z ∈ L, ‖f z‖ ≤ B := fun z hz ↦ (hM₀ z hz).trans (le_max_left M₀ 0)
  set ε' : ℝ := ε / (B + 1)
  have hε' : 0 < ε' := div_pos hε hB1
  obtain ⟨N, ζ, w, g, -, hg, happrox⟩ := hFR hε'
  refine ⟨fun z ↦ ∑ j, (w j * g j z) • f (ζ j),
    DifferentiableOn.fun_sum fun j _ ↦ ((hg j).const_mul (w j)).smul_const (f (ζ j)),
    fun z hz ↦ ?_⟩
  calc ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖
      ≤ ε' * B := happrox hf hBL z hz
    _ < ε' * (B + 1) := by gcongr; linarith
    _ = ε := div_mul_cancel₀ ε hB1.ne'

private theorem exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul {U : Set ℂ} (hU : IsOpen U)
    {t : Finset ℂ} (htU : (t : Set ℂ) ⊆ U) (m : ℂ → ℕ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ (P : ℂ[X]) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U ∧
      (∀ a ∈ t, ∀ k < m a, iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a) ∧
      ∀ z, f z - P.eval z = (∏ x ∈ t, (X - C x) ^ m x).eval z * F z := by
  classical
  obtain ⟨P₀, hP₀⟩ := (ordinaryHermiteJet_bijective
    (Subtype.val_injective : Function.Injective ((↑) : t → ℂ)) (fun x : t ↦ m x)
    fun _ k _ ↦ Ne.isUnit (Nat.cast_ne_zero.2 k.factorial_ne_zero)).surjective
      fun (x : t) (k : Fin (m x)) ↦ iteratedDeriv k f x
  set P : ℂ[X] := P₀.1
  have hP_jet {a : ℂ} (ha : a ∈ t) {k : ℕ} (hk : k < m a) :
      iteratedDeriv k (fun z ↦ P.eval z) a = iteratedDeriv k f a := by
    have h1 := congr_fun (congr_fun hP₀ ⟨a, ha⟩) ⟨k, hk⟩
    rw [ordinaryHermiteJet_apply] at h1
    simpa [P, Polynomial.iteratedDeriv] using h1
  have hh_an : AnalyticOnNhd ℂ (fun z ↦ f z - P.eval z) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).2 (hf.sub P.differentiableOn)
  have hord : ∀ a ∈ t, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ f z - P.eval z) a := by
    intro a ha
    have haU : a ∈ U := htU ha
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hh_an a haU)]
    intro k hk
    change iteratedDeriv k (f - fun z ↦ P.eval z) a = 0
    rw [iteratedDeriv_sub ((hf.analyticAt (hU.mem_nhds haU)).contDiffAt)
      ((P.differentiable.analyticAt a).contDiffAt), hP_jet ha hk, sub_self]
  obtain ⟨F, hF, hfactor⟩ := hh_an.exists_eq_prod_pow_smul t m hord
  refine ⟨P, F, hF, fun a ha k hk ↦ hP_jet ha hk, fun z ↦ ?_⟩
  simpa [eval_prod, smul_eq_mul] using hfactor z

/-- **Scalar Runge approximation with exact finite-jet interpolation.** Let `K` be a compact subset
filled in an open set `Ω ⊆ ℂ`, let `s ⊆ K` be finite with prescribed jet orders `m : ℂ → ℕ`, and
let `f : ℂ → ℂ` be holomorphic on an open neighbourhood `U` of `K`. For every `ε > 0`, there exists
`g : ℂ → ℂ` holomorphic on `Ω` matching the iterated derivatives of `f` up to order `m a` at every
`a ∈ s` (`iteratedDeriv k g a = iteratedDeriv k f a` for `k < m a`) while satisfying
`‖f z - g z‖ < ε` on `K`. -/
theorem IsFilledIn.exists_differentiableOn_iteratedDeriv_eq_and_norm_sub_lt
    {K Ω U s : Set ℂ} (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) (hs : s.Finite) (hsK : s ⊆ K)
    (m : ℂ → ℕ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      (∀ a ∈ s, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a) ∧
      ∀ z ∈ K, ‖f z - g z‖ < ε := by
  classical
  set t : Finset ℂ := hs.toFinset
  have htU : (t : Set ℂ) ⊆ U := by rw [hs.coe_toFinset]; exact hsK.trans hKU
  obtain ⟨P, F, hF, hP_jet, hfactor⟩ :=
    exists_polynomial_iteratedDeriv_eq_and_sub_eq_mul hU htU m hf
  set Qp : ℂ[X] := ∏ x ∈ t, (X - C x) ^ m x
  -- Approximate `F` on `K` by `G` holomorphic on `Ω`, scaled by `max (sup_K ‖Qp‖) 1`.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn Qp.differentiable.continuous.continuousOn
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos (le_max_right M 1)
  obtain ⟨G, hG, hFG⟩ := hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU
    hF.differentiableOn (div_pos hε hB_pos)
  refine ⟨fun z ↦ P.eval z + Qp.eval z * G z,
    P.differentiableOn.add (Qp.differentiableOn.mul hG), fun a ha k hk ↦ ?_, fun z hz ↦ ?_⟩
  · have hat : a ∈ t := hs.mem_toFinset.2 ha
    have haΩ : a ∈ Ω := hKΩ (hsK ha)
    have hQG_an : AnalyticAt ℂ (fun z ↦ Qp.eval z * G z) a :=
      (Qp.differentiable.analyticAt a).mul (hG.analyticAt (hΩ.mem_nhds haΩ))
    have hQG_ord : (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ Qp.eval z * G z) a := by
      refine hQG_an.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
        (((∏ x ∈ t.erase a, (X - C x) ^ m x).differentiable.continuous.continuousAt).mul
          (hG.analyticAt (hΩ.mem_nhds haΩ)).continuousAt) (.of_forall fun z ↦ ?_)
      simp only [Qp, eval_prod, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul, Pi.mul_apply]
      rw [← Finset.mul_prod_erase t _ hat, mul_assoc]
    have hQG_zero : iteratedDeriv k (fun z ↦ Qp.eval z * G z) a = 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQG_an).1 hQG_ord k hk
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

end FiniteRank

section Characterizations

/-- **Runge's approximation theorem (equivalence form).** A compact subset `K` of an open set
`Ω ⊆ ℂ` is filled in `Ω` if and only if every complex-valued function holomorphic on an open
neighbourhood of `K` can be approximated uniformly on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt {K Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ U, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hfill U hU hKU f hf ε hε ↦
    hfill.exists_differentiableOn_norm_sub_lt hΩ hK hKΩ hU hKU hf hε, fun happrox ↦ ?_⟩
  rw [isFilledIn_iff]
  rintro a ha ⟨hcpt, hsub⟩
  have haHull : a ∈ holomorphicHull Ω K :=
    hK.isClosed.union_setOf_isCompact_closure_connectedComponentIn_subset_holomorphicHull
      hΩ hKΩ (Or.inr ⟨ha, hcpt, hsub⟩)
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image
    (continuous_id.sub continuous_const : Continuous fun z : ℂ ↦ z - a).norm.continuousOn
  set M : ℝ := max M₀ 0
  have hM₀_le : 0 ≤ M := le_max_right M₀ 0
  have hM1 : 0 < M + 1 := add_pos_of_nonneg_of_pos hM₀_le one_pos
  have hMK : ∀ z ∈ K, ‖z - a‖ ≤ M :=
    fun z hz ↦ (hM₀ (mem_image_of_mem _ hz)).trans (le_max_left M₀ 0)
  have hf_inv : DifferentiableOn ℂ (fun z : ℂ ↦ (z - a)⁻¹) {a}ᶜ :=
    (differentiableOn_id.sub (differentiableOn_const a)).inv fun z hz h0 ↦
      hz ((sub_eq_zero.1 h0 : z = a))
  obtain ⟨g, hg, hgK⟩ := happrox {a}ᶜ isOpen_compl_singleton
    (fun z hz (hza : z = a) ↦ ha.2 (hza ▸ hz)) (fun z ↦ (z - a)⁻¹) hf_inv (M + 1)⁻¹ (by positivity)
  set h : ℂ → ℂ := fun z ↦ 1 - (z - a) * g z
  have hh : DifferentiableOn ℂ h Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  refine hK.notMem_holomorphicHull_of_forall_norm_lt hKΩ hh (fun z hz ↦ ?_) haHull
  have hza : z - a ≠ 0 := sub_ne_zero.2 fun h0 ↦ ha.2 (h0 ▸ hz)
  have hrew : h z = (z - a) * ((z - a)⁻¹ - g z) := by
    dsimp only [h]
    rw [mul_sub, mul_inv_cancel₀ hza]
  have hha : ‖h a‖ = 1 := by simp [h]
  rw [hha, hrew, norm_mul]
  calc ‖z - a‖ * ‖(z - a)⁻¹ - g z‖
      ≤ M * (M + 1)⁻¹ :=
        mul_le_mul (hMK z hz) (hgK z hz).le (norm_nonneg _) hM₀_le
    _ < (M + 1) * (M + 1)⁻¹ := by gcongr; linarith
    _ = 1 := mul_inv_cancel₀ hM1.ne'

/-- **Point-separation characterization of `IsFilledIn` in `ℂ`.** For a compact subset `K` of an
open set `Ω ⊆ ℂ`, `IsFilledIn K Ω` holds if and only if for every `a ∈ Ω \ K` there exists `g`
holomorphic on `Ω` with `‖g z‖ < ‖g a‖` for all `z ∈ K`. -/
theorem isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_lt {K Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖g z‖ < ‖g a‖ := by
  constructor
  · intro hfill a ha
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    have hfill' : IsFilledIn (insert a K) Ω := hfill.insert hrank hK.isClosed hΩ a
    obtain ⟨r, hr, hballK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl a ha.2
    set V₀ : Set ℂ := ball a (r / 2)
    set U₀ : Set ℂ := (closedBall a (r / 2))ᶜ
    have hdisj : Disjoint V₀ U₀ :=
      disjoint_left.2 fun _ hzV hzU ↦ hzU (ball_subset_closedBall hzV)
    have haV₀ : a ∈ V₀ := mem_ball_self (half_pos hr)
    have hKU₀ : K ⊆ U₀ := fun z hz hzcb ↦
      hballK (closedBall_subset_ball (half_lt_self hr) hzcb) hz
    classical
    set f : ℂ → ℂ := V₀.indicator fun _ ↦ 1
    have hf : DifferentiableOn ℂ f (V₀ ∪ U₀) := by
      rintro z (hzV | hzU)
      · have heq : f =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) :=
          Filter.eventually_of_mem (isOpen_ball.mem_nhds hzV) fun w hw ↦ indicator_of_mem hw _
        exact (heq.differentiableAt_iff.2 (differentiableAt_const 1)).differentiableWithinAt
      · have heq : f =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) :=
          Filter.eventually_of_mem (isClosed_closedBall.isOpen_compl.mem_nhds hzU) fun w hw ↦
            indicator_of_notMem (disjoint_right.1 hdisj hw) _
        exact (heq.differentiableAt_iff.2 (differentiableAt_const 0)).differentiableWithinAt
    obtain ⟨g, hg, hg_err⟩ := hfill'.exists_differentiableOn_norm_sub_lt hΩ (hK.insert a)
      (insert_subset ha.1 hKΩ) (isOpen_ball.union isClosed_closedBall.isOpen_compl)
      (insert_subset (Or.inl haV₀) (hKU₀.trans subset_union_right)) hf (ε := 1 / 3) (by norm_num)
    refine ⟨g, hg, fun z hz ↦ ?_⟩
    have hga : ‖1 - g a‖ < 1 / 3 := by
      simpa only [f, indicator_of_mem haV₀] using hg_err a (mem_insert a K)
    have hgz : ‖g z‖ < 1 / 3 := by
      have hz0 : f z = 0 := indicator_of_notMem (disjoint_right.1 hdisj (hKU₀ hz)) _
      simpa only [hz0, zero_sub, norm_neg] using hg_err z (mem_insert_of_mem a hz)
    have hga_lower : 2 / 3 < ‖g a‖ := by
      have h1 : (1 : ℝ) ≤ ‖1 - g a‖ + ‖g a‖ := by
        simpa using norm_add_le (1 - g a) (g a)
      linarith
    linarith
  · intro hsep
    rw [isFilledIn_iff]
    rintro a ha ⟨hcpt, hsub⟩
    obtain ⟨g, hg, hlt⟩ := hsep a ha
    exact hK.notMem_holomorphicHull_of_forall_norm_lt hKΩ hg hlt
      (hK.isClosed.union_setOf_isCompact_closure_connectedComponentIn_subset_holomorphicHull
        hΩ hKΩ (Or.inr ⟨ha, hcpt, hsub⟩))

/-- **Topological formula for the holomorphic hull in `ℂ`.** For a compact subset `K` of an open set
`Ω ⊆ ℂ`, `holomorphicHull Ω K` equals `K` together with the connected components of `Ω \ K` whose
closures are compact and contained in `Ω`. -/
theorem _root_.IsCompact.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn
    {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ∪ {z ∈ Ω \ K |
      IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  set S := K ∪ {z ∈ Ω \ K |
    IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
  refine Subset.antisymm (fun a ha ↦ by_contra fun haS ↦ ?_)
    (hK.isClosed.union_setOf_isCompact_closure_connectedComponentIn_subset_holomorphicHull hΩ hKΩ)
  have hfillS : IsFilledIn S Ω := isFilledIn_union_setOf_isCompact_closure_connectedComponentIn K Ω
  have hS : IsCompact S :=
    hK.isCompact_union_setOf_isCompact_closure_connectedComponentIn hΩ hKΩ
      not_isCompact_connectedComponent
  have hSΩ : S ⊆ Ω := union_subset hKΩ fun _ hz ↦ hz.1.1
  obtain ⟨g, hg, hlt⟩ :=
    (isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_lt hΩ hS hSΩ).1 hfillS a
      ⟨holomorphicHull_subset Ω K ha, haS⟩
  exact hK.notMem_holomorphicHull_of_forall_norm_lt hKΩ hg
    (fun z hz ↦ hlt z (subset_union_left hz)) ha

/-- **Filled-hull formula for `holomorphicHull Ω K` in `ℂ`.** For compact `K ⊆ Ω` (`Ω` open),
`holomorphicHull Ω K` is `K` together with those bounded complementary components of `K` that lie in
`Ω`. -/
theorem _root_.IsCompact.holomorphicHull_eq_union_filledHull {K Ω : Set ℂ} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ∪ {z ∈ filledHull K \ K | connectedComponentIn Kᶜ z ⊆ Ω} := by
  rw [hK.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn hΩ hKΩ,
    setOf_isCompact_closure_connectedComponentIn_eq_filledHull hK.isClosed hΩ hKΩ]

/-- On `Ω = univ`, the holomorphic hull of a compact set `K ⊆ ℂ` equals its topological filled hull
`TauCeti.filledHull K`. -/
theorem _root_.IsCompact.holomorphicHull_univ_eq_filledHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull univ K = filledHull K := by
  rw [hK.holomorphicHull_eq_union_filledHull isOpen_univ (subset_univ K)]
  ext z
  simp only [mem_union, mem_ofPred_eq, mem_sdiff, subset_univ, and_true]
  exact ⟨fun h ↦ h.elim (fun hz ↦ subset_filledHull hz) And.left,
    fun hz ↦ by_cases Or.inl fun hzK ↦ Or.inr ⟨hz, hzK⟩⟩

/-- **Hull characterization of `IsFilledIn` in `ℂ`.** For a compact subset `K` of an open set
`Ω ⊆ ℂ`, `IsFilledIn K Ω` holds if and only if `holomorphicHull Ω K = K`. -/
theorem isFilledIn_iff_holomorphicHull_eq {K Ω : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsFilledIn K Ω ↔ holomorphicHull Ω K = K := by
  refine ⟨fun hfill ↦ Subset.antisymm ?_ (subset_holomorphicHull hKΩ),
    fun h ↦ h ▸ hΩ.isFilledIn_holomorphicHull K⟩
  rw [hK.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn hΩ hKΩ]
  exact union_subset Subset.rfl fun z hz ↦ (isFilledIn_iff.1 hfill z hz.1 hz.2).elim

end Characterizations

section PolynomialRunge

/-- **Polynomial Runge theorem.** A compact set `K ⊆ ℂ` has connected complement if and only if
every complex-valued function holomorphic on an open neighbourhood of `K` can be uniformly
approximated on `K` by complex polynomials `P : ℂ[X]`. -/
theorem _root_.IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ P : ℂ[X], ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  rw [isConnected_compl_iff_filledHull_eq hrank hK.isBounded, ← isFilledIn_univ_iff hK.isClosed,
    isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt isOpen_univ hK (subset_univ K)]
  refine ⟨fun h U hU hKU f hf ε hε ↦ ?_,
    fun h U hU hKU f hf ε hε ↦
      let ⟨P, hP⟩ := h U hU hKU f hf ε hε; ⟨fun z ↦ P.eval z, P.differentiableOn, hP⟩⟩
  obtain ⟨g, hg, hfg⟩ := h U hU hKU f hf (ε / 2) (half_pos hε)
  obtain ⟨P, hgP⟩ := (differentiableOn_univ.1 hg).exists_polynomial_norm_sub_lt hK (half_pos hε)
  refine ⟨P, fun z hz ↦ ?_⟩
  calc ‖f z - P.eval z‖
      ≤ ‖f z - g z‖ + ‖g z - P.eval z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgP z hz)
    _ = ε := add_halves ε

/-- For a one-element index type `ι`, a compact set `K ⊆ ℂ` has connected complement if and only if
its image in `ι → ℂ` is polynomially convex (`TauCeti.IsPolynomiallyConvex`). -/
theorem _root_.IsCompact.isConnected_compl_iff_isPolynomiallyConvex_image_const {ι : Type*}
    [Unique ι] {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsPolynomiallyConvex (Function.const ι '' K) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  rw [isConnected_compl_iff_filledHull_eq hrank hK.isBounded, ← isFilledIn_univ_iff hK.isClosed,
    isFilledIn_iff_holomorphicHull_eq isOpen_univ hK (subset_univ K),
    (hK.isPolynomiallyConvex_image_const_iff (ι := ι)).symm]

end PolynomialRunge

section RationalRunge

private theorem sub_inv_notMem_filledHull_image {K : Set ℂ} (hK : IsClosed K) {ζ b : ℂ}
    (hζK : ζ ∉ K) (hb : b ∈ connectedComponentIn Kᶜ ζ) (hζb : ζ ≠ b) :
    (ζ - b)⁻¹ ∉ filledHull ((fun z ↦ (z - b)⁻¹) '' K) := by
  intro hζ'_hull
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two
  set D : Set ℂ := connectedComponentIn Kᶜ ζ
  have hD_open : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hDb_pre : IsPreconnected (D \ {b}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hrank hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (finite_singleton b).isDiscrete
  have hφD_pre : IsPreconnected ((fun z ↦ (z - b)⁻¹) '' (D \ {b})) := hDb_pre.image _
    ((continuous_id.sub continuous_const).continuousOn.inv₀ fun _ hz ↦ sub_ne_zero.2 hz.2)
  have hφD_compl : (fun z ↦ (z - b)⁻¹) '' (D \ {b}) ⊆ ((fun z ↦ (z - b)⁻¹) '' K)ᶜ := by
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
    have h12 : z₁ = z₂ := by simpa using heq.symm
    exact connectedComponentIn_subset Kᶜ ζ hz₁.1 (h12 ▸ hz₂)
  have hsub := hφD_pre.subset_connectedComponentIn
    ⟨ζ, ⟨mem_connectedComponentIn hζK, hζb⟩, rfl⟩ hφD_compl
  exact not_isBounded_image_sub_inv_of_mem_closure
    (hD_open.subset_closure_sdiff_of_isDiscrete
      ((finite_singleton b).subset inter_subset_right).isDiscrete hb)
    (fun h ↦ h.2 rfl) ((mem_filledHull_iff.1 hζ'_hull).subset hsub)

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
      sub_ne_zero.2 fun (h : z = b) ↦ hbK (h ▸ hz))
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two
  have hζ'_not_hull : ζ' ∉ filledHull K' := sub_inv_notMem_filledHull_image hK.isClosed hζK hb hζb
  -- Approximate `w ↦ -ζ' * (w - ζ')⁻¹` by `Q₀` on `filledHull K'`, then set `R = X * Q₀`.
  have hL' : IsCompact (filledHull K') :=
    Metric.isCompact_of_isClosed_isBounded hK'.isClosed.isClosed_filledHull
      (isBounded_filledHull.2 hK'.isBounded)
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn continuous_id.continuousOn
  set B : ℝ := max M 1
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hf' : DifferentiableOn ℂ (fun w : ℂ ↦ -ζ' * (w - ζ')⁻¹) {ζ'}ᶜ :=
    (differentiableOn_const (-ζ')).mul
      ((differentiableOn_id.sub (differentiableOn_const ζ')).inv fun _ hw ↦ sub_ne_zero.2 hw)
  obtain ⟨Q₀, hQ₀⟩ := (hL'.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt.1
    (isConnected_compl_filledHull hrank hK'.isBounded)) {ζ'}ᶜ isOpen_compl_singleton
    (fun _ hw (h : _ = ζ') ↦ hζ'_not_hull (h ▸ hw)) _ hf' (η / B) (div_pos hη hB_pos)
  refine ⟨X * Q₀, by simp, fun z hz ↦ ?_⟩
  have hzb : z - b ≠ 0 := sub_ne_zero.2 fun (h : z = b) ↦ hbK (h ▸ hz)
  have hζb' : ζ - b ≠ 0 := sub_ne_zero.2 hζb
  have hzζ : z - ζ ≠ 0 := sub_ne_zero.2 fun (h : z = ζ) ↦ hζK (h ▸ hz)
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
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two
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
        (isBounded_filledHull.2 hK.isBounded)
    have hf_inv : DifferentiableOn ℂ (fun z : ℂ ↦ (z - ζ)⁻¹) {ζ}ᶜ :=
      (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun _ hz ↦ sub_ne_zero.2 hz
    obtain ⟨P, hP⟩ := (hL.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt.1
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
            (OnePoint.coe_injective hyζ ▸ hy)).2 hb_hull)
        rwa [← compl_filledHull_eq_connectedComponentIn hrank hK.isBounded hζ_hull]
    obtain ⟨R, hR0, hR⟩ := hK.exists_polynomial_eval_sub_inv_norm_sub_lt hζK hb_comp hη
    exact Or.inr ⟨b, R, hpA, hbK, hR0, hR⟩

private theorem sum_eval_filter_image {α : Type*} [DecidableEq ℂ] (J : Finset α) (b c : α → ℂ)
    (R : α → ℂ[X]) (z : ℂ) :
    (∑ a ∈ J.image b, (∑ j ∈ J with b j = a, C (c j) * R j).eval (z - a)⁻¹) =
      ∑ j ∈ J, c j * (R j).eval (z - b j)⁻¹ := by
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans
    (Finset.sum_fiberwise_of_maps_to (fun _ ↦ Finset.mem_image_of_mem b) _)
  simp only [eval_finsetSum, eval_mul, eval_C]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.1 hj).2]

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
  choose Pj hPj using fun (j : {j : Fin N // isInf j}) ↦ j.2.2
  choose bj Rj hbjA hbjK hRj0 hRj using fun (j : {j : Fin N // ¬ isInf j}) ↦
    (exists_polynomial_or_eval_sub_inv_norm_sub_lt hK hA (hζ j.1) hη).resolve_left j.2
  set J_inf : Finset (Fin N) := Finset.univ.filter isInf
  set J_fin : Finset (Fin N) := Finset.univ.filter (fun j ↦ ¬ isInf j)
  set b_fn : Fin N → ℂ := fun j ↦ if hj : ¬ isInf j then bj ⟨j, hj⟩ else 0
  set R_fn : Fin N → ℂ[X] := fun j ↦ if hj : ¬ isInf j then Rj ⟨j, hj⟩ else 0
  set P_fn : Fin N → ℂ[X] := fun j ↦ if hj : isInf j then Pj ⟨j, hj⟩ else 0
  set P : ℂ[X] := ∑ j ∈ J_inf, C (c j) * P_fn j
  set s : Finset ℂ := J_fin.image b_fn
  set Q : ℂ → ℂ[X] := fun a ↦ ∑ j ∈ J_fin with b_fn j = a, C (c j) * R_fn j
  refine ⟨P, s, Q, fun a ha ↦ ?_, fun hinfA ↦ Finset.sum_eq_zero fun j hj ↦
    (hinfA (Finset.mem_filter.1 hj).2.1).elim, fun a _ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
    have hj' : ¬ isInf j := (Finset.mem_filter.1 hj).2
    simpa only [b_fn, dite_eq_left hj'] using And.intro (hbjA ⟨j, hj'⟩) (hbjK ⟨j, hj'⟩)
  · simp only [Q, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' : ¬ isInf j := (Finset.mem_filter.1 (Finset.mem_filter.1 hj).1).2
    dsimp only [R_fn]; rw [dite_eq_left hj', hRj0 ⟨j, hj'⟩, mul_zero]
  · set approx : Fin N → ℂ := fun j ↦
      if isInf j then (P_fn j).eval z else (R_fn j).eval (z - b_fn j)⁻¹
    have hsum_Q : ∑ a ∈ s, (Q a).eval (z - a)⁻¹ = ∑ j ∈ J_fin, c j * approx j :=
      (sum_eval_filter_image J_fin b_fn c R_fn z).trans <|
        Finset.sum_congr rfl fun j hj ↦ by simp [approx, ite_eq_right (Finset.mem_filter.1 hj).2]
    have hsum_P : P.eval z = ∑ j ∈ J_inf, c j * approx j := by
      simp only [P, eval_finsetSum, eval_mul, eval_C]
      exact Finset.sum_congr rfl fun j hj ↦ by simp [approx, ite_eq_left (Finset.mem_filter.1 hj).2]
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
    c ζ (fun j ↦ (hζ j).2) (half_pos hε)
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
