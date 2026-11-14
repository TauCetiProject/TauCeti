/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.MeasureTheory.MeasurableSpace.Metric
import TauCeti.Topology.ConnectedComponents

/-!
# The finite-rank Runge approximation operator

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

For any Runge compact pair `(Ω, K)` and any open neighbourhood `U ⊇ K`, this file constructs a
compact collar `L` with `K ⊆ interior L ⊆ L ⊆ U ∩ Ω` and, for every `ε > 0`, a fixed finite-rank
linear operator `f ↦ ∑ j, w j * f (ζ j) * g j` with nodes `ζ j ∈ interior L` and functions
`g j` holomorphic on `Ω` satisfying

`sup_K ‖f - ∑ j, w j * f (ζ j) * g j‖ ≤ ε * B`

for every `f` holomorphic on `U` bounded by `B ≥ 0` on `L`
(`TauCeti.exists_finite_rank_runge_operator`).

The proof combines:
1. A fixed smooth cutoff `α` equal to `1` near `K` and supported inside `interior L`, giving the
   Cauchy–Pompeiu representation `f w = π⁻¹ ∫_{K₁} (w - z)⁻¹ (dbar α z) f z dA(z)` for `w ∈ K`
   on the compact collar `K₁ = tsupport α \ V` disjoint from `K`.
2. A finite measurable small-diameter partition of `K₁`
   (`TotallyBounded.exists_measurable_partition_ball`) together with uniform continuity of the
   kernel `(w, z) ↦ (w - z)⁻¹ dbar α z` and Cauchy's gradient bound
   (`TauCeti.norm_fderiv_le_of_forall_mem_ball_norm_le`) for `f` on `L`.
3. Simple-fraction Runge approximation
   (`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`) at each fixed sample point
   `ζ j ∈ K₁` outside `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Complex MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti

/-- A **Runge compact pair**: an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω` that is filled in
`Ω` (no connected component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

/-- Unfolding `TauCeti.IsRungeCompactPair`. -/
theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  Iff.rfl

/-- The empty set forms a Runge compact pair with every open `Ω ⊆ ℂ`. -/
theorem IsRungeCompactPair.empty {Ω : Set ℂ} (hΩ : IsOpen Ω) : IsRungeCompactPair Ω ∅ := by
  refine ⟨hΩ, isCompact_empty, empty_subset Ω, isFilledIn_iff.mpr fun x hx ⟨hcpt, hsub⟩ => ?_⟩
  simp only [sdiff_empty] at hx hcpt hsub
  set C := connectedComponentIn Ω x
  have hfr : frontier C = ∅ := eq_empty_of_forall_notMem fun y hy =>
    frontier_connectedComponentIn_subset_compl hΩ x hy (hsub (frontier_subset_closure hy))
  have hclo : IsClopen C := isClopen_iff_frontier_eq_empty.mpr hfr
  have hCuniv : C = Set.univ := hclo.eq_univ ⟨x, mem_connectedComponentIn hx⟩
  have huniv : IsCompact (Set.univ : Set ℂ) := by
    simpa only [hCuniv, closure_univ] using hcpt
  exact not_compactSpace_iff.mpr inferInstance (isCompact_univ_iff.mp huniv)

/-- **Cutoff Cauchy–Pompeiu representation.** For a compact set `K` inside an open set `V`, a
smooth compactly supported cutoff `α : ℂ → ℝ` equal to `1` near `V` and supported inside an open
set `U`, and any function `f` holomorphic on `U`, the values of `f` on `K` are given by the
area integral over `K₁ = tsupport α \ V` of `(w - z)⁻¹ (dbar α z) f(z)`. -/
private theorem eq_pi_inv_smul_setIntegral_of_differentiableOn {K V U : Set ℂ}
    {α : ℂ → ℝ} (hKV : K ⊆ V) (hV : IsOpen V) (hU : IsOpen U) (hα : ContDiff ℝ ∞ α)
    (hα_cpt : HasCompactSupport α) (hα_one : V ⊆ interior (α ⁻¹' {1}))
    (hα_U : tsupport α ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ K) :
    f w = (Real.pi : ℂ)⁻¹ • ∫ z in (tsupport α \ V),
      (w - z)⁻¹ * (conjWirtingerDeriv (fun y => (α y : ℂ)) z 1 * f z) := by
  let u : ℂ → ℂ := fun z => α z • f z
  have hfc : ContDiffOn ℝ ∞ f U := (hf.contDiffOn hU).restrict_scalars ℝ
  have hu_cd : ContDiff ℝ ∞ u := hfc.contDiff_smul_of_tsupport_subset hU hα.contDiffOn hα_U
  have hu_cpt : HasCompactSupport u := hα_cpt.smul_right
  have hu_1 : ContDiff ℝ 1 u := hu_cd.of_le (by simp)
  have huw : u w = f w := by
    have h1 : α w = 1 := by
      have := interior_subset (hα_one (hKV hw))
      simpa using this
    simp [u, h1]
  have hcp := hu_cpt.cauchyTransform_conjWirtingerDeriv hu_1 w
  rw [huw, cauchyTransform_apply] at hcp
  rw [← hcp]
  congr 1
  have hmeas : MeasurableSet (tsupport α \ V) :=
    (isClosed_tsupport α).measurableSet.diff hV.measurableSet
  rw [← integral_indicator hmeas]
  congr 1 with z
  simp only [smul_eq_mul]
  by_cases hz : z ∈ tsupport α \ V
  · rw [indicator_of_mem hz]
    have hzU : z ∈ U := hα_U hz.1
    have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hzU)
    have hαd : DifferentiableAt ℝ (fun y => (α y : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z (hα.differentiable (by simp) z)
    have hud := conjWirtingerDeriv_smul_apply hαd (hfd.restrictScalars ℝ) 1
    have hfz : conjWirtingerDeriv f z 1 = 0 := by simp [hfd.conjWirtingerDeriv_eq_zero]
    have hu_eq : (fun y => (α y : ℂ) • f y) = u := by
      ext y; simp [u, Complex.real_smul]
    rw [hu_eq] at hud
    rw [hud, hfz, smul_zero, zero_add, smul_eq_mul]
  · rw [indicator_of_notMem hz]
    suffices conjWirtingerDeriv u z 1 = 0 by simp [this]
    by_cases hzV : z ∈ V
    · have hne : u =ᶠ[𝓝 z] f := by
        filter_upwards [isOpen_interior.mem_nhds (hα_one hzV)] with y hy
        have hy1 : α y = 1 := by simpa using interior_subset hy
        simp [u, hy1]
      have hVsub : V ⊆ U := fun y hy => by
        have hy1 : α y = 1 := by simpa using interior_subset (hα_one hy)
        have hys : y ∈ Function.support α := by simp [hy1]
        exact hα_U (subset_tsupport α hys)
      have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds (hVsub hzV))
      rw [hne.conjWirtingerDeriv_eq, hfd.conjWirtingerDeriv_eq_zero]
      simp
    · have hnt : z ∉ tsupport α := fun h => hz ⟨h, hzV⟩
      have hne : u =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnt] with y hy
        simp [u, hy]
      rw [hne.conjWirtingerDeriv_eq, (differentiableAt_const (0 : ℂ)).conjWirtingerDeriv_eq_zero]
      simp

/-- **GH0, finite-rank Runge operator.** Fix a compact collar `L` inside the holomorphy
neighbourhood and the ambient domain. For every `ε > 0`, one finite evaluation formula, independent
of `f`, approximates every `U`-holomorphic `f` with an explicit operator bound in terms of
`sup_L ‖f‖`. -/
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
  obtain ⟨hΩ, hK, hKΩ, hfill⟩ := hRunge
  rcases K.eq_empty_or_nonempty with rfl | _
  · exact ⟨∅, isCompact_empty, by simp, empty_subset _, fun _ _ =>
      ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
        fun _ _ _ _ _ _ hz => hz.elim⟩⟩
  -- Build a compact collar `L = closure W₂` and a smooth cutoff `α` supported in `W₂`.
  obtain ⟨W₂, hW₂, hKW₂, hW₂UO, hW₂c⟩ :=
    exists_open_between_and_isCompact_closure hK (hU.inter hΩ) (subset_inter hKU hKΩ)
  let L : Set ℂ := closure W₂
  have hL : IsCompact L := hW₂c
  have hKL : K ⊆ interior L := hKW₂.trans (hW₂.subset_interior_iff.mpr subset_closure)
  have hLUO : L ⊆ U ∩ Ω := hW₂UO
  obtain ⟨V, hV, hKV, hVW₂, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hW₂ hKW₂
  obtain ⟨α, hα, -, hα_one, hα_cpt, hα_W₂⟩ :=
    hVc.exists_contDiff_cutoff hW₂ hVW₂
  let K₁ : Set ℂ := tsupport α \ V
  have hK₁ : IsCompact K₁ := hα_cpt.isCompact.diff hV
  have hK₁L : K₁ ⊆ interior L :=
    sdiff_subset.trans (hα_W₂.trans (hW₂.subset_interior_iff.mpr subset_closure))
  have hK₁U : tsupport α ⊆ U := hα_W₂.trans (subset_closure.trans (hLUO.trans inter_subset_left))
  have hV_one : V ⊆ interior (α ⁻¹' {1}) :=
    (subset_closure.trans hα_one).trans subset_rfl
  have hdisj : Disjoint K K₁ :=
    disjoint_left.mpr fun z hzK hzK₁ => hzK₁.2 (hKV hzK)
  -- Uniform radius `δ₀` for Cauchy gradient estimates on `K₁` inside `L`.
  obtain ⟨r₀, hr₀, hthick₀⟩ := hK₁.exists_thickening_subset_open isOpen_interior hK₁L
  let δ₀ : ℝ := r₀ / 2
  have hδ₀ : 0 < δ₀ := half_pos hr₀
  have hball₀ : ∀ z ∈ K₁, ball z (2 * δ₀) ⊆ interior L := fun z hz => by
    rw [show 2 * δ₀ = r₀ by dsimp only [δ₀]; ring]
    exact (ball_subset_thickening hz r₀).trans hthick₀
  -- Continuous kernel `κ w z = π⁻¹ * (w - z)⁻¹ * dbar α z` on `K ×ˢ K₁`.
  let β : ℂ → ℂ := fun z => conjWirtingerDeriv (fun y => (α y : ℂ)) z 1
  let κ : ℂ → ℂ → ℂ := fun w z => (Real.pi : ℂ)⁻¹ * (w - z)⁻¹ * β z
  have hβ_cont : Continuous β :=
    ((Complex.ofRealCLM.contDiff.comp hα).of_le (by simp)).continuous_conjWirtingerDeriv_apply 1
  have hκ_cont : ContinuousOn (fun p : ℂ × ℂ => κ p.1 p.2) (K ×ˢ K₁) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_)
      (hβ_cont.comp continuous_snd).continuousOn
    refine ContinuousOn.inv₀ (continuous_fst.sub continuous_snd).continuousOn ?_
    rintro ⟨w, z⟩ ⟨hw, hz⟩
    exact sub_ne_zero.mpr (hdisj.ne_of_mem hw hz)
  have hκ_uc : UniformContinuousOn (fun p : ℂ × ℂ => κ p.1 p.2) (K ×ˢ K₁) :=
    (hK.prod hK₁).uniformContinuousOn_of_continuous hκ_cont
  -- Find a uniform norm bound `Mκ` for `κ` on `K ×ˢ K₁`.
  have hκ_bdd : ∃ Mκ : ℝ, 0 ≤ Mκ ∧ ∀ w ∈ K, ∀ z ∈ K₁, ‖κ w z‖ ≤ Mκ := by
    obtain ⟨Mκ, hMκ⟩ := (hK.prod hK₁).bddAbove_image hκ_cont.norm
    refine ⟨max Mκ 0, le_max_right _ _, fun w hw z hz => ?_⟩
    exact (hMκ ⟨(w, z), ⟨hw, hz⟩, rfl⟩).trans (le_max_left _ _)
  obtain ⟨Mκ, hMκ0, hMκ⟩ := hκ_bdd
  -- Now build the finite-rank operator for any `ε > 0`.
  refine ⟨L, hL, hKL, hLUO, fun ε hε => ?_⟩
  let η : ℝ := ε / (2 * max 1 (volume.real K₁))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, huc₁⟩ := Metric.uniformContinuousOn_iff.mp hκ_uc (η / 2) (half_pos hη)
  let δ : ℝ := min δ₀ (min δ₁ (η * δ₀ / (4 * (Mκ + 1))))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hδ₁ (by positivity))
  obtain ⟨n, c, P, -, hPm, hPs, hPd, hPU⟩ :=
    hK₁.totallyBounded.exists_measurable_partition_ball hK₁.isClosed.measurableSet (half_pos hδ)
  classical
  let kept : Finset (Fin n) := Finset.univ.filter fun i => (P i).Nonempty
  let e : Fin kept.card ≃ kept := kept.equivFin.symm
  let N : ℕ := kept.card
  let A : Fin N → Set ℂ := fun j => P (e j).1
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hPm (e j).1
  have hAK₁ : ∀ j, A j ⊆ K₁ := fun j => (hPs (e j).1).trans inter_subset_left
  have hAne : ∀ j, (A j).Nonempty := fun j => (Finset.mem_filter.mp (e j).2).2
  let ζ : Fin N → ℂ := fun j => (hAne j).some
  have hζA : ∀ j, ζ j ∈ A j := fun j => (hAne j).some_mem
  have hAball : ∀ j, A j ⊆ ball (ζ j) δ := fun j y hy => by
    have hyc : dist y (c (e j).1) < δ / 2 := (hPs (e j).1 hy).2
    have hζc : dist (ζ j) (c (e j).1) < δ / 2 := (hPs (e j).1 (hζA j)).2
    rw [mem_ball]
    linarith [dist_triangle_right y (ζ j) (c (e j).1)]
  have hAdisj : Pairwise (Function.onFun Disjoint A) := fun j₁ j₂ hj =>
    hPd fun heq => hj (e.injective (Subtype.ext heq))
  have hAunion : ⋃ j, A j = K₁ := by
    refine Subset.antisymm (iUnion_subset hAK₁) fun x hx => ?_
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hPU.symm ▸ hx)
    have hi : i ∈ kept := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxi⟩⟩
    exact mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, by simpa [A] using hxi⟩
  let w : Fin N → ℂ := fun j => (volume.real (A j) : ℂ) * (Real.pi : ℂ)⁻¹ * β (ζ j)
  have hζ_notMem : ∀ j, ζ j ∉ K := fun j hj => hdisj.le_bot ⟨hj, hAK₁ j (hζA j)⟩
  have happrox : ∀ j : Fin N, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - ζ j)⁻¹ - g z‖ < ε / (2 * (∑ i, ‖w i‖ + 1)) := fun j =>
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ_notMem j) (by positivity)
  choose g hg_diff hg_lt using happrox
  refine ⟨N, ζ, w, g, fun j => hK₁L (hAK₁ j (hζA j)), hg_diff, fun f hf B hB hLf z hz => ?_⟩
  -- Express `f z` as `∫ y in K₁, κ z y * f y`.
  have hrep : f z = ∫ y in K₁, κ z y * f y := by
    have hcp := eq_pi_inv_smul_setIntegral_of_differentiableOn hKV hV hU hα hα_cpt
      hV_one hK₁U hf hz
    rw [hcp, ← integral_smul]
    refine setIntegral_congr_fun ((isClosed_tsupport α).measurableSet.diff hV.measurableSet)
      fun y _ => ?_
    simp only [κ, β, smul_eq_mul]
    ring
  -- Continuity and integrability of `y ↦ κ z y * f y` on `K₁`.
  have hκf_cont : ContinuousOn (fun y => κ z y * f y) K₁ := by
    have hz_cont : ContinuousOn (fun y => κ z y) K₁ :=
      hκ_cont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun y hy => ⟨hz, hy⟩
    have hf_cont : ContinuousOn f K₁ :=
      hf.continuousOn.mono (hK₁L.trans (interior_subset.trans (hLUO.trans inter_subset_left)))
    exact hz_cont.mul hf_cont
  have hκf_int : IntegrableOn (fun y => κ z y * f y) K₁ := hκf_cont.integrableOn_compact hK₁
  -- Split the integral over the partition `A`.
  have hsplit : ∫ y in K₁, κ z y * f y = ∑ j, ∫ y in A j, κ z y * f y := by
    rw [← hAunion, integral_iUnion_fintype hAm hAdisj fun j => hκf_int.mono_set (hAK₁ j)]
  -- Bound the Riemann-sum error on each cell `A j`.
  have hcell : ∀ j : Fin N,
      ‖(∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j)‖ ≤
        volume.real (A j) * (η * B) := fun j => by
    have hconst : (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j) =
        ∫ _ in A j, κ z (ζ j) * f (ζ j) := by
      rw [setIntegral_const, Complex.real_smul]
      ring
    have hA_lt : volume (A j) < ⊤ :=
      (measure_mono (hAK₁ j)).trans_lt hK₁.measure_lt_top
    have hint₁ : IntegrableOn (fun y => κ z y * f y) (A j) := hκf_int.mono_set (hAK₁ j)
    have hint₂ : IntegrableOn (fun _ => κ z (ζ j) * f (ζ j)) (A j) :=
      integrableOn_const hA_lt.ne
    rw [hconst, ← integral_sub hint₁ hint₂, mul_comm (volume.real (A j))]
    refine norm_setIntegral_le_of_norm_le_const hA_lt (C := η * B) fun y hy => ?_
    have hyK₁ : y ∈ K₁ := hAK₁ j hy
    have hζK₁ : ζ j ∈ K₁ := hAK₁ j (hζA j)
    have hydist : dist y (ζ j) < δ := mem_ball.mp (hAball j hy)
    -- Bound `‖κ z y - κ z (ζ j)‖` by uniform continuity on `K ×ˢ K₁`.
    have hκ_err : ‖κ z y - κ z (ζ j)‖ < η / 2 := by
      have hpd : dist (z, y) (z, ζ j) < δ₁ := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact hydist.trans_le (min_le_of_right_le (min_le_left _ _))
      simpa only [dist_eq_norm] using huc₁ (z, y) ⟨hz, hyK₁⟩ (z, ζ j) ⟨hz, hζK₁⟩ hpd
    -- Bound `‖f y - f (ζ j)‖` using Cauchy's derivative bound on `ball (ζ j) δ₀`.
    have hf_deriv : ∀ u ∈ ball (ζ j) δ₀, ‖fderiv ℂ f u‖ ≤ 2 * B / δ₀ := fun u hu => by
      have hsub : ball u δ₀ ⊆ L := fun v hv => by
        refine interior_subset (hball₀ (ζ j) hζK₁ ?_)
        rw [mem_ball] at hu hv ⊢
        linarith [dist_triangle v u (ζ j)]
      have hfball : DifferentiableOn ℂ f (ball u δ₀) :=
        hf.mono (hsub.trans (hLUO.trans inter_subset_left))
      exact norm_fderiv_le_of_forall_mem_ball_norm_le hfball hδ₀ fun v hv => hLf v (hsub hv)
    have hf_diff : ‖f y - f (ζ j)‖ ≤ (2 * B / δ₀) * ‖y - ζ j‖ := by
      have hf_at : ∀ u ∈ ball (ζ j) δ₀, DifferentiableAt ℂ f u := fun u hu =>
        hf.differentiableAt (hU.mem_nhds ((hLUO.trans inter_subset_left)
          (interior_subset (hball₀ (ζ j) hζK₁ (ball_subset_ball (by linarith) hu)))))
      refine (convex_ball (ζ j) δ₀).norm_image_sub_le_of_norm_fderiv_le hf_at hf_deriv
        (mem_ball_self hδ₀) (ball_subset_ball (min_le_left _ _) (hAball j hy))
    have hMκζ : ‖κ z (ζ j)‖ ≤ Mκ := hMκ z hz (ζ j) hζK₁
    have hsplit_err' : κ z y * f y - κ z (ζ j) * f (ζ j) =
        (κ z y - κ z (ζ j)) * f y + κ z (ζ j) * (f y - f (ζ j)) := by ring
    have hfyB : ‖f y‖ ≤ B := hLf y (interior_subset (hK₁L hyK₁))
    have hterm₁ : ‖(κ z y - κ z (ζ j)) * f y‖ ≤ (η / 2) * B := by
      rw [norm_mul]
      exact mul_le_mul hκ_err.le hfyB (norm_nonneg _) (by positivity)
    have hterm₂ : ‖κ z (ζ j) * (f y - f (ζ j))‖ ≤ (η / 2) * B := by
      rw [norm_mul]
      calc ‖κ z (ζ j)‖ * ‖f y - f (ζ j)‖
          ≤ Mκ * ((2 * B / δ₀) * ‖y - ζ j‖) :=
            mul_le_mul hMκζ hf_diff (norm_nonneg _) hMκ0
        _ ≤ Mκ * ((2 * B / δ₀) * (η * δ₀ / (4 * (Mκ + 1)))) := by
            gcongr
            rw [← dist_eq_norm]
            exact hydist.le.trans ((min_le_right _ _).trans (min_le_right _ _))
        _ = (Mκ / (Mκ + 1)) * ((η / 2) * B) := by field_simp; ring
        _ ≤ 1 * ((η / 2) * B) := by
            gcongr
            exact (div_le_one (by linarith)).mpr (by linarith)
        _ = (η / 2) * B := one_mul _
    calc ‖κ z y * f y - κ z (ζ j) * f (ζ j)‖
        = ‖(κ z y - κ z (ζ j)) * f y + κ z (ζ j) * (f y - f (ζ j))‖ := by rw [hsplit_err']
      _ ≤ ‖(κ z y - κ z (ζ j)) * f y‖ + ‖κ z (ζ j) * (f y - f (ζ j))‖ := norm_add_le _ _
      _ ≤ (η / 2) * B + (η / 2) * B := add_le_add hterm₁ hterm₂
      _ = η * B := by ring
  -- Combine the Riemann-sum bound with the simple-fraction approximation bound.
  have hsum_vol : ∑ j : Fin N, volume.real (A j) = volume.real K₁ := by
    rw [← hAunion, measureReal_iUnion_fintype hAdisj hAm
      (fun j => ((measure_mono (hAK₁ j)).trans_lt hK₁.measure_lt_top).ne)]
  have herr₁ : ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ (ε / 2) * B := by
    have hsum_eq : ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ =
        ∑ j, (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w, κ]
      ring
    rw [hrep, hsplit, hsum_eq, ← Finset.sum_sub_distrib]
    calc ‖∑ j, ((∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j))‖
        ≤ ∑ j, ‖(∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, volume.real (A j) * (η * B) := Finset.sum_le_sum fun j _ => hcell j
      _ = volume.real K₁ * (η * B) := by rw [← Finset.sum_mul, hsum_vol]
      _ = (volume.real K₁ / max 1 (volume.real K₁)) * ((ε / 2) * B) := by
          simp only [η]; ring
      _ ≤ 1 * ((ε / 2) * B) := by
          gcongr
          exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)
      _ = (ε / 2) * B := one_mul _
  have herr₂ : ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ ≤ (ε / 2) * B := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ j : Fin N, ‖w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z‖ ≤
        ‖w j‖ * B * (ε / (2 * (∑ i, ‖w i‖ + 1))) := fun j => by
      have heq : w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z =
          w j * f (ζ j) * ((z - ζ j)⁻¹ - g j z) := by ring
      rw [heq, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hLf (ζ j) (interior_subset (hK₁L (hAK₁ j (hζA j))))) (norm_nonneg _))
        (hg_lt j z hz).le (norm_nonneg _) (by positivity)
    calc ‖∑ j, (w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z)‖
        ≤ ∑ j, ‖w j * f (ζ j) * (z - ζ j)⁻¹ - w j * f (ζ j) * g j z‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖w j‖ * B * (ε / (2 * (∑ i, ‖w i‖ + 1))) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = ((∑ j, ‖w j‖) / (∑ i, ‖w i‖ + 1)) * ((ε / 2) * B) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have hden : ∑ i, ‖w i‖ + 1 ≠ 0 := by
            linarith [Finset.sum_nonneg (s := Finset.univ) fun j _ => norm_nonneg (w j)]
          field_simp
      _ ≤ 1 * ((ε / 2) * B) := by
          gcongr
          have hsum_nn : 0 ≤ ∑ j : Fin N, ‖w j‖ :=
            Finset.sum_nonneg fun j _ => norm_nonneg (w j)
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = (ε / 2) * B := one_mul _
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
      = ‖(f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) +
          (∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z)‖ := by ring_nf
    _ ≤ ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ +
        ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ := norm_add_le _ _
    _ ≤ (ε / 2) * B + (ε / 2) * B := add_le_add herr₁ herr₂
    _ = ε * B := by ring

end TauCeti
