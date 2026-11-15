/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.Analysis.Complex.Polynomial.Approximation
import TauCeti.Analysis.Complex.Pompeiu.Cutoff
import TauCeti.Analysis.Complex.Quadrature
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.FilledIn
import TauCeti.Topology.Compactness.Compact

/-!
# Runge's approximation theorem and characterization of holomorphic hulls in the plane

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` (neither assumed connected). This file proves
Runge's approximation theorem together with its operator-theoretic refinement, its converse, and the
resulting topological description of the holomorphic hull `TauCeti.holomorphicHull Ω K`:

1. **Universal linear finite-rank operators**
   (`IsCompact.exists_sum_sub_inv_smul_norm_sub_le` and
   `TauCeti.IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le`):
   - First, for any compact pair `K ⊆ interior L` inside an open set `U ⊆ ℂ`, discretizing the
     cutoff Cauchy–Pompeiu representation on `interior L` via
     `IsCompact.exists_sum_smul_norm_setIntegral_sub_le` and controlling integrand oscillation
     uniformly by Cauchy's derivative estimate
     (`TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le`) produces finitely many nodes
     `ζ j ∈ interior L \ K` and scalar weights `w j : ℂ` such that
     `‖f z - ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)‖ ≤ ε * B` for all `z ∈ K` and every Banach-valued
     holomorphic map `f : ℂ → F` on `U` with `‖f‖ ≤ B` on `L`.
   - When `K` is filled in `Ω` (`TauCeti.IsFilledIn K Ω`), choosing a compact collar `L ⊆ U ∩ Ω`
     with `K ⊆ interior L` and replacing each simple fraction `z ↦ (z - ζ j)⁻¹` (`ζ j ∉ K`) by a
     function `g j` holomorphic on `Ω` via
     `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt` yields universal linear
     finite-rank holomorphic approximation operators

     `‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B`.

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
4. **Polynomial Runge theorem on `ℂ`**
   (`IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`,
   `IsCompact.isConnected_compl_iff_isPolynomiallyConvex_image_const`): for compact `K ⊆ ℂ`, `Kᶜ` is
   connected if and only if `K` is polynomially convex, if and only if every function holomorphic
   near `K` is uniformly approximable on `K` by polynomials.

## Main results

* `IsCompact.exists_sum_sub_inv_smul_norm_sub_le`: universal rational-kernel finite-rank
  approximation on a compact collar `K ⊆ interior L ⊆ L ⊆ U`.
* `TauCeti.IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le`: universal holomorphic
  finite-rank approximation with uniform collar bound `ε * B` for Banach-valued maps `f : ℂ → F`.
* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: Banach-valued Runge approximation on a
  filled compact set `K ⊆ Ω`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`: equivalence between
  `IsFilledIn K Ω` and Runge approximation.
* `TauCeti.isFilledIn_iff_forall_sdiff_exists_differentiableOn_norm_lt`: equivalence between
  `IsFilledIn K Ω` and holomorphic point separation.
* `IsCompact.holomorphicHull_eq_union_setOf_isCompact_closure_connectedComponentIn` and
  `TauCeti.isFilledIn_iff_holomorphicHull_eq`: topological formula for `\widehat{K}_Ω` and hull
  characterization of `IsFilledIn K Ω`.
* `IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt` and
  `IsCompact.isConnected_compl_iff_isPolynomiallyConvex_image_const`: polynomial Runge theorem.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Corollary 11.4.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.5–13.9.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1
  and Theorem 1.3.4.
-/

public section

open Bornology Complex MeasureTheory Metric Polynomial Set
open scoped ContDiff Topology

namespace TauCeti

section FiniteRank

/-- **Universal rational-kernel finite-rank approximation on a collar.** Let `K ⊆ ℂ` be compact and
let `L, U ⊆ ℂ` satisfy `K ⊆ interior L` and `L ⊆ U`. For every `ε > 0`, there exist sample nodes
`ζ : Fin N → ℂ` in `interior L \ K` and scalar weights `w : Fin N → ℂ` such that for every
Banach-valued function `f : ℂ → F` holomorphic on `U` with `‖f‖ ≤ B` on `L` (`0 ≤ B`),

`‖f z - ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)‖ ≤ ε * B`

for all `z ∈ K`. -/
theorem _root_.IsCompact.exists_sum_sub_inv_smul_norm_sub_le {K L U : Set ℂ} (hK : IsCompact K)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hKL : K ⊆ interior L) (hLU : L ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      ∀ {f : ℂ → F} {B : ℝ}, DifferentiableOn ℂ f U → 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
        ∀ z ∈ K, ‖f z - ∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)‖ ≤ ε * B := by
  -- Cutoff Cauchy–Pompeiu representation on `(K, interior L)`.
  obtain ⟨α, hα, -, hαL, hKα1, hK₁, hdisj, hrep⟩ :=
    hK.exists_contDiff_setIntegral_sub_inv_smul_conjWirtingerDeriv_eq (F := F) isOpen_interior hKL
  set K₁ : Set ℂ := tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)
  have hK₁L : K₁ ⊆ interior L := (tsupport_conjWirtingerDeriv_subset α 1).trans hαL
  have hK₁notK {ζ : ℂ} (hζ : ζ ∈ K₁) : ζ ∉ K :=
    fun hζK ↦ disjoint_left.1 hdisj hζ (hKα1 hζK)
  -- Uniform radius `r` around `K₁` inside `interior L` for Cauchy's derivative estimate.
  obtain ⟨r₀, hr₀, hr₀L⟩ := hK₁.exists_cthickening_subset_open isOpen_interior hK₁L
  set r : ℝ := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hballL {ζ : ℂ} (hζ : ζ ∈ K₁) : closedBall ζ (2 * r) ⊆ interior L := by
    have h2r : 2 * r = r₀ := by dsimp only [r]; ring
    rw [h2r]
    exact (closedBall_subset_cthickening hζ r₀).trans hr₀L
  -- Smooth scalar kernel `Φ (ζ, ξ) = π⁻¹ * (ξ - ζ)⁻¹ * bar∂ α (ζ)` on `K₁ ×ˢ K`.
  set Φ : ℂ × ℂ → ℂ := fun p ↦ (Real.pi : ℂ)⁻¹ * (p.2 - p.1)⁻¹ * conjWirtingerDeriv α p.1 1
  have hΦ_cont : ContinuousOn Φ (K₁ ×ˢ K) := by
    have hsub_ne : ∀ p ∈ K₁ ×ˢ K, p.2 - p.1 ≠ 0 := fun p hp h0 ↦
      hK₁notK hp.1 ((sub_eq_zero.1 h0 : p.2 = p.1) ▸ hp.2)
    have hbar_cont : Continuous (fun p : ℂ × ℂ ↦ conjWirtingerDeriv α p.1 1) :=
      ((hα.of_le (by simp)).continuous_conjWirtingerDeriv_apply 1).comp continuous_fst
    exact (continuousOn_const.mul
      ((continuous_snd.sub continuous_fst).continuousOn.inv₀ hsub_ne)).mul hbar_cont.continuousOn
  obtain ⟨M₀, hM₀⟩ := (hK₁.prod hK).bddAbove_image hΦ_cont.norm
  set M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hΦ_le {ζ ξ : ℂ} (hζ : ζ ∈ K₁) (hξ : ξ ∈ K) : ‖Φ (ζ, ξ)‖ ≤ M :=
    (hM₀ (mem_image_of_mem _ ⟨hζ, hξ⟩)).trans (le_max_left M₀ 0)
  -- Choose quadrature mesh `δ > 0` controlling both kernel oscillation and Cauchy Lipschitz bound.
  set V₁ : ℝ := volume.real K₁
  have hV₁_nonneg : 0 ≤ V₁ := measureReal_nonneg
  have hV₁_pos : 0 < V₁ + 1 := add_pos_of_nonneg_of_pos hV₁_nonneg one_pos
  have hM1_pos : 0 < M + 1 := add_pos_of_nonneg_of_pos hM_nonneg one_pos
  set ω₁ : ℝ := ε / (2 * (V₁ + 1))
  have hω₁ : 0 < ω₁ := by positivity
  obtain ⟨r₁, hr₁, hr₁Φ⟩ := Metric.uniformContinuousOn_iff.1
    ((hK₁.prod hK).uniformContinuousOn_of_continuous hΦ_cont) ω₁ hω₁
  set δ : ℝ := min (r / 3) (min (r₁ / 3) (ε * r / (4 * (M + 1) * (V₁ + 1))))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h2δ_r : 2 * δ < r := by
    have : δ ≤ r / 3 := min_le_left _ _
    linarith
  have h2δ_r₁ : 2 * δ < r₁ := by
    have : δ ≤ r₁ / 3 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have h2δ_M : M * (2 * δ) / r ≤ ω₁ := by
    have hδ₃ : δ ≤ ε * r / (4 * (M + 1) * (V₁ + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmul : M * (2 * δ) ≤ (M + 1) * (2 * (ε * r / (4 * (M + 1) * (V₁ + 1)))) := by
      gcongr; linarith
    rw [div_le_iff₀ hr]
    refine hmul.trans_eq ?_
    dsimp only [ω₁]
    field_simp [hM1_pos.ne', hV₁_pos.ne']
    ring
  obtain ⟨N, ζ, a, hζK₁, -, -, hquad⟩ := hK₁.exists_sum_smul_norm_setIntegral_sub_le (E := F) hδ
  set w : Fin N → ℂ := fun j ↦ (a j : ℂ) * (Real.pi : ℂ)⁻¹ * conjWirtingerDeriv α (ζ j) 1
  refine ⟨N, ζ, w, fun j ↦ ⟨hK₁L (hζK₁ j), hK₁notK (hζK₁ j)⟩, fun {f B} hf hB₀ hBL ξ hξ ↦ ?_⟩
  have hf_intL : DifferentiableOn ℂ f (interior L) := hf.mono (interior_subset.trans hLU)
  have hf_rep : f ξ = ∫ z in K₁, Φ (z, ξ) • f z := by
    rw [← hrep hf_intL ξ (hKα1 hξ), ← integral_smul]
    refine setIntegral_congr_fun hK₁.isClosed.measurableSet fun z _ ↦ ?_
    simp [Φ, smul_smul, mul_assoc]
  have hg_cont : ContinuousOn (fun z ↦ Φ (z, ξ) • f z) K₁ :=
    (hΦ_cont.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz ↦ ⟨hz, hξ⟩).smul
      (hf_intL.continuousOn.mono hK₁L)
  have hg_osc : ∀ z ∈ K₁, ∀ z' ∈ K₁, dist z z' ≤ 2 * δ →
      ‖Φ (z, ξ) • f z - Φ (z', ξ) • f z'‖ ≤ 2 * ω₁ * B := by
    intro z hz z' hz' hzz'
    have hΦ_diff : ‖Φ (z, ξ) - Φ (z', ξ)‖ ≤ ω₁ := by
      rw [← dist_eq_norm]
      refine (hr₁Φ (z, ξ) ⟨hz, hξ⟩ (z', ξ) ⟨hz', hξ⟩ ?_).le
      have hp : dist (z, ξ) (z', ξ) = dist z z' := by simp [Prod.dist_eq]
      linarith
    have hf_diff : ‖f z - f z'‖ ≤ B / r * dist z z' := by
      rw [← dist_eq_norm]
      exact dist_le_of_forall_mem_closedBall_two_mul_norm_le isOpen_interior hf_intL hr
        (hballL hz) (fun u hu ↦ hBL u (interior_subset (hballL hz hu)))
        (mem_ball_self hr) (mem_ball.2 (by rw [dist_comm]; exact hzz'.trans_lt h2δ_r))
    have hsplit : Φ (z, ξ) • f z - Φ (z', ξ) • f z' =
        (Φ (z, ξ) - Φ (z', ξ)) • f z + Φ (z', ξ) • (f z - f z') := by
      rw [sub_smul, smul_sub, sub_add_sub_cancel]
    rw [hsplit]
    calc ‖(Φ (z, ξ) - Φ (z', ξ)) • f z + Φ (z', ξ) • (f z - f z')‖
        ≤ ‖(Φ (z, ξ) - Φ (z', ξ)) • f z‖ + ‖Φ (z', ξ) • (f z - f z')‖ := norm_add_le _ _
      _ = ‖Φ (z, ξ) - Φ (z', ξ)‖ * ‖f z‖ + ‖Φ (z', ξ)‖ * ‖f z - f z'‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ ω₁ * B + M * (B / r * (2 * δ)) := by
          refine add_le_add (mul_le_mul hΦ_diff (hBL z (interior_subset (hK₁L hz)))
            (norm_nonneg _) hω₁.le) (mul_le_mul (hΦ_le hz' hξ) ?_ (norm_nonneg _) hM_nonneg)
          exact hf_diff.trans (mul_le_mul_of_nonneg_left hzz' (div_nonneg hB₀ hr.le))
      _ = ω₁ * B + (M * (2 * δ) / r) * B := by ring
      _ ≤ ω₁ * B + ω₁ * B := add_le_add le_rfl (mul_le_mul_of_nonneg_right h2δ_M hB₀)
      _ = 2 * ω₁ * B := by ring
  have hsum_eq : (∑ j, a j • (Φ (ζ j, ξ) • f (ζ j))) =
      ∑ j, (w j * (ξ - ζ j)⁻¹) • f (ζ j) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← smul_assoc, Complex.real_smul]
    exact congrArg (· • f (ζ j)) (by dsimp only [w, Φ]; ring)
  rw [hf_rep, ← hsum_eq]
  calc ‖(∫ z in K₁, Φ (z, ξ) • f z) - ∑ j, a j • (Φ (ζ j, ξ) • f (ζ j))‖
      ≤ (2 * ω₁ * B) * V₁ := hquad hg_cont hg_osc
    _ ≤ (2 * ω₁ * B) * (V₁ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε * B := by
        dsimp only [ω₁]
        field_simp [hV₁_pos.ne']

/-- **Universal holomorphic finite-rank approximation operator.** Let `K ⊆ Ω` be a compact set
filled in an open set `Ω ⊆ ℂ`, and let `U` be an open neighbourhood of `K`. There exists a compact
collar `L ⊆ U ∩ Ω` with `K ⊆ interior L` such that for every `ε > 0`, there exist sample nodes
`ζ : Fin N → ℂ` in `interior L \ K`, scalar weights `w : Fin N → ℂ`, and functions
`g : Fin N → ℂ → ℂ` holomorphic on `Ω` satisfying

`‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B`

for all `z ∈ K` and every Banach-valued function `f : ℂ → F` holomorphic on `U` with `‖f‖ ≤ B` on
`L` (`0 ≤ B`). -/
theorem IsFilledIn.exists_differentiableOn_sum_smul_norm_sub_le {K Ω U : Set ℂ}
    (hfill : IsFilledIn K Ω) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
          (∀ j, ζ j ∈ interior L \ K) ∧
          (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
          ∀ {f : ℂ → F} {B : ℝ}, DifferentiableOn ℂ f U → 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
            ∀ z ∈ K, ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B := by
  obtain ⟨n, hKL⟩ :=
    hK.exists_subset_interior_closedBall_sdiff_thickening (hU.inter hΩ) (subset_inter hKU hKΩ)
  set L : Set ℂ := closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (U ∩ Ω)ᶜ
  have hL : IsCompact L := (isCompact_closedBall 0 (n + 1)).diff isOpen_thickening
  have hLUΩ : L ⊆ U ∩ Ω := fun z hz ↦
    by_contra fun hz' ↦ hz.2 (self_subset_thickening (by positivity) _ hz')
  refine ⟨L, hL, hKL, hLUΩ, fun {ε} hε ↦ ?_⟩
  obtain ⟨N, ζ, w, hζ, hrat⟩ :=
    hK.exists_sum_sub_inv_smul_norm_sub_le F hKL (hLUΩ.trans inter_subset_left) (half_pos hε)
  set S : ℝ := ∑ j : Fin N, ‖w j‖
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hS1_pos : 0 < S + 1 := add_pos_of_nonneg_of_pos hS_nonneg one_pos
  set η : ℝ := ε / (2 * (S + 1))
  have hη : 0 < η := by positivity
  have hpole (j : Fin N) :
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ ξ ∈ K, ‖(ξ - ζ j)⁻¹ - g ξ‖ < η :=
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ j).2 hη
  choose g hg_diff hg_err using hpole
  refine ⟨N, ζ, w, g, hζ, hg_diff, fun {f B} hf hB₀ hBL ξ hξ ↦ ?_⟩
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
    _ ≤ ε / 2 * B + ε / 2 * B := add_le_add (hrat hf hB₀ hBL ξ hξ) hpole_err
    _ = ε * B := by ring

/-- **Banach-valued Runge approximation.** If `K` is a compact subset filled in an open set
`Ω ⊆ ℂ`, then every Banach-valued function `f : ℂ → F` holomorphic on an open neighbourhood `U` of
`K` is uniformly approximable on `K` by functions holomorphic on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {K Ω U : Set ℂ} (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUΩ, hFR⟩ :=
    hfill.exists_differentiableOn_sum_smul_norm_sub_le F hΩ hK hKΩ hU hKU
  obtain ⟨M₀, hM₀⟩ :=
    hL.bddAbove_image (hf.continuousOn.mono (hLUΩ.trans inter_subset_left)).norm
  set B : ℝ := max M₀ 0
  have hB₀ : 0 ≤ B := le_max_right M₀ 0
  have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos hB₀ one_pos
  have hBL : ∀ z ∈ L, ‖f z‖ ≤ B :=
    fun z hz ↦ (hM₀ (mem_image_of_mem _ hz)).trans (le_max_left M₀ 0)
  set ε' : ℝ := ε / (B + 1)
  have hε' : 0 < ε' := div_pos hε hB1
  obtain ⟨N, ζ, w, g, -, hg, happrox⟩ := hFR hε'
  refine ⟨fun z ↦ ∑ j, (w j * g j z) • f (ζ j),
    DifferentiableOn.fun_sum fun j _ ↦ ((hg j).const_mul (w j)).smul_const (f (ζ j)),
    fun z hz ↦ ?_⟩
  calc ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖
      ≤ ε' * B := happrox hf hB₀ hBL z hz
    _ < ε' * (B + 1) := by gcongr; linarith
    _ = ε := div_mul_cancel₀ ε hB1.ne'

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

end TauCeti
