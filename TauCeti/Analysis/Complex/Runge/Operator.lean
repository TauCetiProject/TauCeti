/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Runge.Hull
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.Analysis.Complex.Pompeiu.Cutoff
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.MeasureTheory.Integral.Bochner.PlanarQuadrature
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Finite-rank Runge approximation operators

Given a Runge compact pair `(Ω, K)` and an open neighborhood `U ⊇ K`, this file constructs a
compact collar `L ⊆ U ∩ Ω` with `K ⊆ interior L` and, for every `ε > 0`, a finite evaluation-and-sum
operator
`f ↦ z ↦ ∑ j : Fin N, w j * f (ζ j) * g j z`
with nodes `ζ j ∈ interior L` and functions `g j` holomorphic on `Ω`, independent of `f`, satisfying
the uniform operator norm bound
`‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B`
for every `U`-holomorphic `f` bounded in norm by `B ≥ 0` on `L` and every `z ∈ K`. Because the
nodes `ζ j`, weights `w j`, and basis functions `g j` depend only on `(Ω, K, U, ε)` and not on `f`,
this operator commutes with differentiation and preserves smooth or holomorphic dependence on
external parameters.

The construction splits cleanly into two steps:

1. `IsCompact.exists_finite_rank_cauchy_quadrature`: for *any* compact `K` and set `L ⊆ ℂ` with
   `K ⊆ interior L` (no compactness on `L` and no filledness assumption), a smooth cutoff `α` equal
   to `1` near `K` and supported in `interior L` represents every `(interior L)`-holomorphic `f` on
   `K` as a Cauchy–Green integral over the compact transition band
   `S = tsupport α \ interior (α ⁻¹' {1})`. Combining uniform equicontinuity of the smooth kernel
   `(ζ, z) ↦ π⁻¹ * bar∂ α(ζ) * (z - ζ)⁻¹` on `S ×ˢ K`, Cauchy's interior Lipschitz bound
   `(B / r₀) * ‖ζ₁ - ζ₂‖` on `f`, and planar square Riemann quadrature yields universal nodes
   `ζ j ∈ interior L \ K` and weights `w j` approximating `f` within `ε * B` by simple fractions
   `∑ j, w j * f (ζ j) * (z - ζ j)⁻¹`.
2. `TauCeti.exists_finite_rank_runge_operator`: when `(Ω, K)` is a Runge compact pair, each simple
   fraction `z ↦ (z - ζ j)⁻¹` (whose pole `ζ j` lies outside `K`) is uniformly approximated on `K`
   by an `Ω`-holomorphic function `g j` via
   `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`.

## Main results

* `IsCompact.exists_finite_rank_cauchy_quadrature`: universal finite-rank rational Cauchy–Green
  quadrature on any compact `K` inside `interior L`.
* `TauCeti.exists_finite_rank_runge_operator`: universal finite-rank holomorphic Runge operator
  with operator bound `ε * B` on a compact collar `L ⊆ U ∩ Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and §11.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1.
-/

public section

open Bornology Filter MeasureTheory Metric Set TauCeti Topology
open scoped ContDiff

/-- **Universal finite-rank rational Cauchy–Green quadrature.** Given a compact set `K ⊆ ℂ`, a set
`L ⊆ ℂ` with `K ⊆ interior L`, and `ε > 0`, there exist finitely many nodes `ζ j ∈ interior L \ K`
and complex weights `w j`—independent of `f`—such that every function `f` holomorphic on
`interior L` and bounded in norm by `B ≥ 0` on `L` satisfies
`‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * B` for all `z ∈ K`. -/
theorem IsCompact.exists_finite_rank_cauchy_quadrature {K L : Set ℂ} (hK : IsCompact K)
    (hKL : K ⊆ interior L) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
      (∀ j, ζ j ∈ interior L \ K) ∧
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (interior L) →
        ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
          ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * B := by
  -- Step 1: Smooth cutoff `α` equal to `1` on an open `V ⊇ K`, supported in `interior L`.
  obtain ⟨ψ, hψ_smooth, -, hKV, hψ_cpt, hψ_supp⟩ :=
    hK.exists_contDiff_cutoff isOpen_interior hKL
  let α : ℂ → ℂ := fun z ↦ ψ z
  have hα_smooth : ContDiff ℝ ∞ α := Complex.ofRealCLM.contDiff.comp hψ_smooth
  have hα_c1 : ContDiff ℝ 1 α := hα_smooth.of_le (by simp)
  have hα_cpt : HasCompactSupport α := hψ_cpt.comp_left Complex.ofReal_zero
  have hα_supp : tsupport α ⊆ interior L :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψ_supp
  let V : Set ℂ := interior (ψ ⁻¹' {1})
  have hV_open : IsOpen V := isOpen_interior
  have hαV : ∀ z ∈ V, α z = 1 := fun z hz ↦ by
    have hz1 : ψ z = 1 := interior_subset hz
    simp [α, hz1]
  -- Step 2: Compact transition band `S = tsupport α \ V` inside `interior L \ K` and clearance.
  let S : Set ℂ := tsupport α \ V
  have hS_cpt : IsCompact S := hα_cpt.isCompact.diff hV_open
  have hS_sub : S ⊆ interior L := sdiff_subset.trans hα_supp
  obtain ⟨δ₀, hδ₀, hS_thick⟩ := hS_cpt.exists_cthickening_subset_open isOpen_interior hS_sub
  set r₀ : ℝ := δ₀ / 2
  have hr₀ : 0 < r₀ := half_pos hδ₀
  have hball_sub {c : ℂ} (hc : c ∈ S) : closedBall c (2 * r₀) ⊆ interior L := by
    have h2 : 2 * r₀ = δ₀ := by ring
    rw [h2]
    exact (closedBall_subset_cthickening hc δ₀).trans hS_thick
  -- Step 3: Smooth off-diagonal Cauchy–Green kernel `Φ` on `S ×ˢ K`, sup bound, and oscillation.
  let Φ : ℂ → ℂ → ℂ := fun ζ z ↦ (Real.pi : ℂ)⁻¹ * conjWirtingerDeriv α ζ 1 * (z - ζ)⁻¹
  have hΦ_cont : ContinuousOn (Function.uncurry Φ) (S ×ˢ K) := by
    have hdα : Continuous (fun ζ ↦ conjWirtingerDeriv α ζ 1) :=
      hα_c1.continuous_conjWirtingerDeriv_apply 1
    have hinv : ContinuousOn (fun p : ℂ × ℂ ↦ (p.2 - p.1)⁻¹) (S ×ˢ K) :=
      (continuous_snd.sub continuous_fst).continuousOn.inv₀ fun p hp ↦
        sub_ne_zero.mpr fun h ↦ hp.1.2 (h ▸ hKV hp.2)
    exact (continuous_const.mul (hdα.comp continuous_fst)).continuousOn.mul hinv
  obtain ⟨M₁, hM₁⟩ := ((hS_cpt.prod hK).image_of_continuousOn hΦ_cont).isBounded.subset_closedBall 0
  set M₀ : ℝ := max M₁ 1
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hΦ_le {ζ z : ℂ} (hζ : ζ ∈ S) (hz : z ∈ K) : ‖Φ ζ z‖ ≤ M₀ :=
    (mem_closedBall_zero_iff.mp (hM₁ ⟨(ζ, z), ⟨hζ, hz⟩, rfl⟩)).trans (le_max_left _ _)
  set V_area : ℝ := max (volume.real S) 1
  have hV_pos : 0 < V_area := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set η₁ : ℝ := ε / V_area
  have hη₁ : 0 < η₁ := by positivity
  have hueq : UniformEquicontinuousOn (fun (z : K) ζ ↦ Φ ζ z) S :=
    hS_cpt.uniformEquicontinuousOn_of_continuousOn_prod hK hΦ_cont
  rw [(Metric.uniformity_basis_dist_le.inf_principal (S ×ˢ S)).uniformEquicontinuousOn_iff
    Metric.uniformity_basis_dist_le] at hueq
  obtain ⟨ρ, hρ, hρ_osc⟩ := hueq (η₁ / 2) (half_pos hη₁)
  -- Step 4: Mesh `δ > 0` controlling kernel oscillation and Cauchy interior Lipschitz error.
  set δ : ℝ := min (ρ / √2) (min (r₀ / (2 * √2)) (η₁ * r₀ / (2 * M₀ * √2)))
  have hδ : 0 < δ := by positivity
  have hδ_ρ : √2 * δ ≤ ρ := by
    have h1 : δ ≤ ρ / √2 := min_le_left _ _
    calc √2 * δ ≤ √2 * (ρ / √2) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
      _ = ρ := mul_div_cancel₀ ρ (by positivity)
  have hδ_r₀ : √2 * δ < r₀ := by
    have h1 : δ ≤ r₀ / (2 * √2) := (min_le_right _ _).trans (min_le_left _ _)
    calc √2 * δ ≤ √2 * (r₀ / (2 * √2)) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
      _ = r₀ / 2 := by
        have hsq : (√2 : ℝ) ≠ 0 := by positivity
        field_simp [hsq]
      _ < r₀ := half_lt_self hr₀
  have hδ_lip : M₀ * (√2 * δ / r₀) ≤ η₁ / 2 := by
    have h1 : δ ≤ η₁ * r₀ / (2 * M₀ * √2) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : √2 * δ ≤ √2 * (η₁ * r₀ / (2 * M₀ * √2)) :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
    have h3 : M₀ * (√2 * δ / r₀) ≤ M₀ * (√2 * (η₁ * r₀ / (2 * M₀ * √2)) / r₀) := by
      gcongr
    refine h3.trans_eq ?_
    have hsq : (√2 : ℝ) ≠ 0 := by positivity
    have hr₀_ne : r₀ ≠ 0 := hr₀.ne'
    have hM₀_ne : M₀ ≠ 0 := hM₀_pos.ne'
    field_simp [hsq, hr₀_ne, hM₀_ne]
  -- Step 5: Planar square quadrature on `S`, reindexed by `Fin A.card`.
  obtain ⟨z₀, n, A, ζ₀, -, -, hζ₀, hquad⟩ :=
    TauCeti.exists_planarSquare_quadrature_of_isCompact hS_cpt hδ
  let e : Fin A.card ≃ A := A.equivFin.symm
  let ζ : Fin A.card → ℂ := fun j ↦ ζ₀ (e j)
  let w : Fin A.card → ℂ := fun j ↦
    (volume.real (TauCeti.planarSquare z₀ δ (e j) ∩ S) : ℂ) * (Real.pi : ℂ)⁻¹ *
      conjWirtingerDeriv α (ζ j) 1
  refine ⟨A.card, ζ, w, fun j ↦ ?_, fun f hf B hB0 hfB z hz ↦ ?_⟩
  · have hmemS : ζ j ∈ S := (hζ₀ (e j) (e j).2).2
    exact ⟨hS_sub hmemS, fun hzK ↦ hmemS.2 (hKV hzK)⟩
  · -- Cutoff Cauchy–Green representation at `z ∈ K ⊆ V`.
    have hrep : f z = ∫ ζ' in S, Φ ζ' z * f ζ' := by
      rw [hf.eq_pi_inv_mul_setIntegral_conjWirtingerDeriv_mul isOpen_interior hV_open
        hα_c1.contDiffOn hα_cpt hα_supp hαV (hKV hz), ← integral_const_mul]
      refine setIntegral_congr_fun hS_cpt.measurableSet fun ζ' _ ↦ ?_
      dsimp [Φ]
      ring
    -- Integrability of `ζ' ↦ Φ ζ' z * f ζ'` on compact `S`.
    have hint : IntegrableOn (fun ζ' ↦ Φ ζ' z * f ζ') S volume := by
      have hcont_Φz : ContinuousOn (fun ζ' ↦ Φ ζ' z) S :=
        hΦ_cont.comp (Continuous.prodMk_left z).continuousOn fun ζ' hζ' ↦ ⟨hζ', hz⟩
      exact (hcont_Φz.mul (hf.continuousOn.mono hS_sub)).integrableOn_compact hS_cpt
    -- Cellwise oscillation bound `η₁ * B` on `S`.
    have hosc_f (c : ℕ × ℕ) (hc : c ∈ A) (ζ' : ℂ)
        (hζ' : ζ' ∈ TauCeti.planarSquare z₀ δ c ∩ S) :
        ‖Φ (ζ₀ c) z * f (ζ₀ c) - Φ ζ' z * f ζ'‖ ≤ η₁ * B := by
      have hc₀ := hζ₀ c hc
      have hdist : ‖ζ₀ c - ζ'‖ ≤ √2 * δ :=
        TauCeti.norm_sub_le_sqrt_two_mul_of_mem_planarSquare hδ.le hc₀.1 hζ'.1
      have hΦ_diff : ‖Φ (ζ₀ c) z - Φ ζ' z‖ ≤ η₁ / 2 := by
        have hmod := hρ_osc (ζ₀ c) ζ'
          ⟨(dist_eq_norm (ζ₀ c) ζ').trans_le (hdist.trans hδ_ρ), hc₀.2, hζ'.2⟩ ⟨z, hz⟩
        simpa [dist_eq_norm] using hmod
      have hfc₀ : ‖f (ζ₀ c)‖ ≤ B := hfB (ζ₀ c) (interior_subset (hS_sub hc₀.2))
      have hball_B : ∀ u ∈ closedBall (ζ₀ c) (2 * r₀), ‖f u‖ ≤ B :=
        fun u hu ↦ hfB u (interior_subset (hball_sub hc₀.2 hu))
      have hζ'_ball : ζ' ∈ ball (ζ₀ c) r₀ := by
        rw [mem_ball, dist_comm, dist_eq_norm]
        exact hdist.trans_lt hδ_r₀
      have hf_diff : ‖f (ζ₀ c) - f ζ'‖ ≤ B * (√2 * δ / r₀) := by
        have hlip := TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le isOpen_interior hf
          hr₀ (hball_sub hc₀.2) hball_B (mem_ball_self hr₀) hζ'_ball
        rw [dist_eq_norm, dist_eq_norm] at hlip
        calc ‖f (ζ₀ c) - f ζ'‖
          _ ≤ B / r₀ * ‖ζ₀ c - ζ'‖ := hlip
          _ ≤ B / r₀ * (√2 * δ) := mul_le_mul_of_nonneg_left hdist (div_nonneg hB0 hr₀.le)
          _ = B * (√2 * δ / r₀) := by ring
      calc ‖Φ (ζ₀ c) z * f (ζ₀ c) - Φ ζ' z * f ζ'‖
        _ = ‖(Φ (ζ₀ c) z - Φ ζ' z) * f (ζ₀ c) + Φ ζ' z * (f (ζ₀ c) - f ζ')‖ := by
            congr 1; ring
        _ ≤ ‖(Φ (ζ₀ c) z - Φ ζ' z) * f (ζ₀ c)‖ + ‖Φ ζ' z * (f (ζ₀ c) - f ζ')‖ := norm_add_le _ _
        _ = ‖Φ (ζ₀ c) z - Φ ζ' z‖ * ‖f (ζ₀ c)‖ + ‖Φ ζ' z‖ * ‖f (ζ₀ c) - f ζ'‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ η₁ / 2 * B + M₀ * (B * (√2 * δ / r₀)) :=
            add_le_add (mul_le_mul hΦ_diff hfc₀ (norm_nonneg _) (by positivity))
              (mul_le_mul (hΦ_le hζ'.2 hz) hf_diff (norm_nonneg _) hM₀_pos.le)
        _ = (η₁ / 2 + M₀ * (√2 * δ / r₀)) * B := by ring
        _ ≤ (η₁ / 2 + η₁ / 2) * B := mul_le_mul_of_nonneg_right (add_le_add_right hδ_lip _) hB0
        _ = η₁ * B := by ring
    -- Assemble the reindexed sum and apply the quadrature bound.
    have hsum_eq : (∑ j : Fin A.card, w j * f (ζ j) * (z - ζ j)⁻¹) =
        ∑ c ∈ A, volume.real (TauCeti.planarSquare z₀ δ c ∩ S) • (Φ (ζ₀ c) z * f (ζ₀ c)) := by
      rw [← A.sum_attach]
      refine Eq.trans ?_ (e.sum_comp fun x : A ↦
        volume.real (TauCeti.planarSquare z₀ δ x.1 ∩ S) • (Φ (ζ₀ x.1) z * f (ζ₀ x.1)))
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [w, ζ, Φ, Complex.real_smul]
      ring
    rw [hsum_eq, hrep, norm_sub_rev]
    calc ‖(∑ c ∈ A, volume.real (TauCeti.planarSquare z₀ δ c ∩ S) • (Φ (ζ₀ c) z * f (ζ₀ c))) -
            ∫ ζ' in S, Φ ζ' z * f ζ'‖
      _ ≤ volume.real S * (η₁ * B) := (hquad (fun ζ' ↦ Φ ζ' z * f ζ')).2 hint hosc_f
      _ ≤ V_area * (η₁ * B) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hη₁.le hB0)
      _ = ε * B := by
          dsimp [η₁]
          have hV_ne : V_area ≠ 0 := hV_pos.ne'
          field_simp [hV_ne]

namespace TauCeti

/-- **Finite-rank Runge approximation operator.** For every Runge compact pair `(Ω, K)` and every
open set `U ⊇ K`, there exists a compact collar `L ⊆ U ∩ Ω` with `K ⊆ interior L` such that for
each `ε > 0` one can choose finitely many evaluation nodes `ζ j ∈ interior L`, complex weights
`w j`, and `Ω`-holomorphic functions `g j`—all independent of `f`—satisfying
`‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B`
for every `U`-holomorphic `f`, every uniform bound `B ≥ 0` on `L`, and every `z ∈ K`. -/
theorem exists_finite_rank_runge_operator {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
          ∃ g : Fin N → ℂ → ℂ,
            (∀ j, ζ j ∈ interior L) ∧
            (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
            ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
              ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
                ∀ z ∈ K,
                  ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨L, hL_cpt, -, hKL, hLUΩ⟩ :=
    exists_compact_closed_between hRunge.isCompact (hU.inter hRunge.isOpen)
      (subset_inter hKU hRunge.subset)
  refine ⟨L, hL_cpt, hKL, hLUΩ, fun ε hε ↦ ?_⟩
  obtain ⟨N, ζ, w, hζ, hquad⟩ :=
    hRunge.isCompact.exists_finite_rank_cauchy_quadrature hKL (half_pos hε)
  set W : ℝ := (∑ j : Fin N, ‖w j‖) + 1
  have hW_pos : 0 < W := by positivity
  set η₂ : ℝ := ε / (2 * W)
  have hη₂ : 0 < η₂ := by positivity
  choose g hg_holo hg_approx using fun j : Fin N ↦
    hRunge.isFilledIn.exists_differentiableOn_norm_inv_sub_lt hRunge.isOpen hRunge.isCompact
      hRunge.subset (hζ j).2 hη₂
  refine ⟨N, ζ, w, g, fun j ↦ (hζ j).1, hg_holo, fun f hf B hB0 hfB z hz ↦ ?_⟩
  have hf_int : DifferentiableOn ℂ f (interior L) :=
    hf.mono (interior_subset.trans (hLUΩ.trans inter_subset_left))
  have herr₁ : ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε / 2 * B :=
    hquad f hf_int B hB0 hfB z hz
  have herr₂ :
      ‖(∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε / 2 * B := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm (j : Fin N) :
        ‖w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z‖ ≤ ‖w j‖ * (B * η₂) := by
      rw [← mul_sub, norm_mul, norm_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact mul_le_mul (hfB (ζ j) (interior_subset (hζ j).1))
        (hg_approx j z hz).le (norm_nonneg _) hB0
    calc ∑ j : Fin N, ‖w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z‖
      _ ≤ ∑ j : Fin N, ‖w j‖ * (B * η₂) := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (∑ j : Fin N, ‖w j‖) * (B * η₂) := (Finset.sum_mul _ _ _).symm
      _ ≤ W * (B * η₂) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hB0 hη₂.le)
      _ = ε / 2 * B := by
          dsimp [η₂]
          have hW_ne : W ≠ 0 := hW_pos.ne'
          field_simp [hW_ne]
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
    _ = ‖(f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) +
          ((∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) - ∑ j, w j * f (ζ j) * g j z)‖ := by
        congr 1; abel
    _ ≤ ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ +
          ‖(∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) - ∑ j, w j * f (ζ j) * g j z‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 * B + ε / 2 * B := add_le_add herr₁ herr₂
    _ = ε * B := by ring

end TauCeti
