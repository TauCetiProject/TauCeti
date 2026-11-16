/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.MetricSpace.Holder

/-!
# Precompactness of bounded maps with `\bar∂` bounded in `Lᵖ`, `p > 2`

Let `2 < p < ∞` and let `U ⊆ ℂ` be open. This file proves that a family of smooth maps
`u : ℂ → F` into a complex Hilbert space which is uniformly bounded on `U`, and whose
conjugate Wirtinger derivatives `\bar∂u` are, up to a uniformly bounded error, uniformly
bounded in `Lᵖ(U)`, is bounded in `W^{1,p}` on every compact subset of `U`
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le`, which only needs
`1 < p < ∞`) and uniformly Hölder continuous of exponent `1 - 2 / p` there
(`TauCeti.exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le`). For a finite-dimensional
target every sequence in such a family therefore has a subsequence converging locally uniformly
on `U`, and the limit inherits the Hölder bounds
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le`).

The bounded error term allows `\bar∂u` to differ from an `Lᵖ`-small or `Lᵖ`-bounded function by
bounded zeroth-order terms, as for the equation `\bar∂u + ν u = g` with bounded `ν` and bounded
`u`. The exponent `1 - 2 / p` is the exponent of Morrey's embedding `W^{1,p} ⊆ C^{1 - 2 / p}` in
the plane; for `p = 2 + 2 / m` it is `1 / (m + 1)`.

## The argument

Fix a compact set `K ⊆ U`. On a bounded open neighbourhood `V` of `K` inside `U` the bounded
maps `u` and `\bar∂u - g` lie in `Lᵖ(V)` with uniform bounds, so the interior estimate for the
Cauchy–Riemann operator
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`) bounds the
derivative `Du` in `Lᵖ(K)` uniformly over the family. Applied to a closed thickening `L` of `K`
inside `U`, Morrey's inequality on the ball of radius `|x - y|` about the midpoint of `x` and `y`
(`TauCeti.dist_le_of_contDiffOn_ball_midpoint_of_finrank_lt`) bounds `‖u x - u y‖` by a
multiple of `|x - y|^(1 - 2 / p)` for nearby points `x, y ∈ K`, and the sup bound handles
distant points (`HolderOnWith.of_dist_lt_of_dist_le`). The subsequence comes from the
Arzelà–Ascoli theorem on the open set `U`
(`EquicontinuousOn.exists_strictMono_tendstoLocallyUniformlyOn`).

## Main results

* `TauCeti.exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le`: the uniform interior
  `W^{1,p}` bound.
* `TauCeti.exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le`: the uniform Hölder bound on
  compact subsets.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le`: a
  locally uniformly convergent subsequence, with Hölder continuous limit.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B (Morrey's inequality and interior estimates
  for the Cauchy–Riemann operator).
-/

public section

open scoped ENNReal NNReal ContDiff Topology
open MeasureTheory Metric Set Filter

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Uniform interior `W^{1,p}` bounds from `\bar∂` bounds.** Let `1 < p < ∞`, let `U ⊆ ℂ` be
open and `K ⊆ U` compact, and let `A, M, B ≥ 0`. There is a constant `N` such that every map `u`
smooth on `U` with `‖u‖ ≤ A` on `U`, and `‖\bar∂u - g‖ ≤ M` on `U` for some `g` with
`‖g‖_{Lᵖ(U)} ≤ B`, satisfies `‖Du‖_{Lᵖ(K)} ≤ N`. -/
theorem exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (A M B : ℝ≥0) :
    ∃ N : ℝ≥0, ∀ u g : ℂ → F, ContDiffOn ℝ ∞ u U → (∀ z ∈ U, ‖u z‖ ≤ A) →
      (∀ z ∈ U, ‖conjWirtingerDeriv u z 1 - g z‖ ≤ M) →
      eLpNorm g p (volume.restrict U) ≤ B → eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤ N := by
  -- Work on a bounded open neighbourhood `V` of `K` in `U`, where bounded maps lie in `Lᵖ`.
  set V := U ∩ thickening 1 K
  have hV : IsOpen V := hU.inter isOpen_thickening
  have hVU : V ⊆ U := inter_subset_left
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F) hp
    hp_top hV hK (subset_inter hKU (self_subset_thickening one_pos K))
  set S : ℝ≥0∞ := volume V ^ p.toReal⁻¹
  have hS : S ≠ (∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (hK.isBounded.thickening.subset inter_subset_right).measure_lt_top.ne
  have hbound : ∀ {f : ℂ → F} {c : ℝ≥0}, AEStronglyMeasurable f (volume.restrict V) →
      (∀ z ∈ U, ‖f z‖ ≤ c) → eLpNorm f p (volume.restrict V) ≤ S * ENNReal.ofReal c := by
    intro f c hf hfc
    refine (eLpNorm_le_of_ae_bound hf ((ae_restrict_iff' hV.measurableSet).2
      (Eventually.of_forall fun z hz ↦ hfc z (hVU hz)))).trans_eq ?_
    rw [Measure.restrict_apply_univ]
  refine ⟨(C₁ * (S * ENNReal.ofReal M + B + S * ENNReal.ofReal A)).toNNReal,
    fun u g hu hA hM hB ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (by simp [ENNReal.mul_ne_top, hS])]
  have hgm : AEStronglyMeasurable g (volume.restrict V) :=
    (aestronglyMeasurable_of_eLpNorm_ne_top (hB.trans_lt ENNReal.coe_lt_top).ne).mono_measure
      (Measure.restrict_mono hVU le_rfl)
  have hdm : AEStronglyMeasurable (fun z ↦ conjWirtingerDeriv u z 1) (volume.restrict V) :=
    ((hu.conjWirtingerDeriv_apply_of_isOpen hU (m := 0) (by simp) 1).continuousOn.mono
      hVU).aestronglyMeasurable hV.measurableSet
  -- Split `\bar∂u` as the bounded `\bar∂u - g` plus `g`.
  have hderiv : eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict V) ≤
      S * ENNReal.ofReal M + B :=
    calc eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict V)
        = eLpNorm ((fun z ↦ conjWirtingerDeriv u z 1 - g z) + g) p (volume.restrict V) := by
          congr 1
          ext z
          simp
      _ ≤ eLpNorm (fun z ↦ conjWirtingerDeriv u z 1 - g z) p (volume.restrict V) +
          eLpNorm g p (volume.restrict V) := eLpNorm_add_le hp.le
      _ ≤ S * ENNReal.ofReal M + B :=
          add_le_add (hbound (hdm.sub hgm) hM)
            ((eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)).trans hB)
  refine (hC₁ u (hu.mono hVU)).trans ?_
  gcongr
  exact hbound (hu.continuousOn.mono hVU |>.aestronglyMeasurable hV.measurableSet) hA

/-- **Uniform Hölder bounds from `\bar∂` bounds.** Let `2 < p < ∞`, let `U ⊆ ℂ` be open and
`K ⊆ U` compact, and let `A, M, B ≥ 0`. There is a constant `C` such that every map `u` smooth on
`U` with `‖u‖ ≤ A` on `U`, and `‖\bar∂u - g‖ ≤ M` on `U` for some `g` with `‖g‖_{Lᵖ(U)} ≤ B`, is
Hölder continuous on `K` with exponent `1 - 2 / p` and constant `C`. -/
theorem exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le {p : ℝ≥0} (hp : 2 < p)
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (A M B : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ u g : ℂ → F, ContDiffOn ℝ ∞ u U → (∀ z ∈ U, ‖u z‖ ≤ A) →
      (∀ z ∈ U, ‖conjWirtingerDeriv u z 1 - g z‖ ≤ M) →
      eLpNorm g p (volume.restrict U) ≤ B → HolderOnWith C (1 - 2 / p) u K := by
  -- A uniform bound `N` on `‖Du‖_{Lᵖ}` over a closed thickening `L = cthickening δ K` in `U`.
  obtain ⟨δ, hδ, hLU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨N, hN⟩ := exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le (F := F)
    (p := p) (by exact_mod_cast one_lt_two.trans hp) ENNReal.coe_ne_top hU hK.cthickening hLU A M B
  set α : ℝ≥0 := 1 - 2 / p
  have hα : (α : ℝ) = 1 - (Module.finrank ℝ ℂ : ℝ) / (p : ℝ) := by
    rw [Complex.finrank_real_complex, NNReal.coe_sub ((div_le_one₀ (zero_lt_two.trans hp)).2
      hp.le), NNReal.coe_div]
    norm_num
  have hp2 : (Module.finrank ℝ ℂ : ℝ≥0) < p := by simpa using hp
  -- Morrey's constant in the plane.
  set c : ℝ := 2 ^ (Module.finrank ℝ ℂ + 1) /
      (Module.finrank ℝ ℂ * (volume : Measure ℂ).real (ball 0 1)) *
      (Module.finrank ℝ ℂ * (volume : Measure ℂ).real (ball 0 1) * (p - 1) /
        (p - Module.finrank ℝ ℂ)) ^ (1 - 1 / (p : ℝ)) * 2 ^ (α : ℝ)
  set δ' : ℝ≥0 := (δ / 2).toNNReal
  have hδ' : (δ' : ℝ) = δ / 2 := Real.coe_toNNReal _ (by positivity)
  refine ⟨c.toNNReal * N + 2 * A * δ' ^ (-(α : ℝ)), fun u g hu hA hM hB ↦
    HolderOnWith.of_dist_lt_of_dist_le (by rw [← NNReal.coe_pos, hδ']; positivity)
      (fun x hx y _ hxy ↦ ?_) fun x hx y hy ↦ ?_⟩
  · -- Morrey's inequality on the ball of radius `|x - y|` about the midpoint of `x` and `y`.
    rw [hδ'] at hxy
    have hball : ball (midpoint ℝ x y) ‖x - y‖ ⊆ cthickening δ K := fun z hz ↦
      closedBall_subset_cthickening hx δ <| mem_closedBall.2 <| by
        have hmid : dist (midpoint ℝ x y) x = dist x y / 2 := by
          rw [dist_comm, dist_left_midpoint]
          norm_num
          ring
        rw [mem_ball, ← dist_eq_norm] at hz
        linarith [dist_triangle z (midpoint ℝ x y) x]
    refine (dist_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := volume)
      ((hu.mono (hball.trans hLU)).of_le (by simp)) hp2 ((eLpNorm_mono_measure _
        (Measure.restrict_mono hball le_rfl)).trans (hN u g hu hA hM hB))).trans ?_
    rw [← hα, NNReal.coe_mul]
    gcongr
    exact Real.le_coe_toNNReal c
  · -- Points at distance at least `δ / 2` are handled by the sup bound.
    calc dist (u x) (u y) ≤ ‖u x‖ + ‖u y‖ := dist_le_norm_add_norm _ _
      _ ≤ A + A := add_le_add (hA x (hKU hx)) (hA y (hKU hy))
      _ = ((2 * A : ℝ≥0) : ℝ) := by push_cast; ring

/-- **Locally uniformly convergent subsequences.** Let `2 < p < ∞`, let `U ⊆ ℂ` be open and let
`u n` be maps smooth on `U` into a finite-dimensional complex Hilbert space, with `‖u n‖ ≤ A` on
`U` and `‖\bar∂(u n) - g n‖ ≤ M` on `U` for some `g n` with `‖g n‖_{Lᵖ(U)} ≤ B`. Then a subsequence
of `u n` converges locally uniformly on `U`, and the limit is Hölder continuous with exponent
`1 - 2 / p` on every compact subset of `U`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le
    [FiniteDimensional ℂ F] {p : ℝ≥0} (hp : 2 < p) {U : Set ℂ} (hU : IsOpen U) {A M B : ℝ≥0}
    {u g : ℕ → ℂ → F} (hu : ∀ n, ContDiffOn ℝ ∞ (u n) U) (hA : ∀ n, ∀ z ∈ U, ‖u n z‖ ≤ A)
    (hM : ∀ n, ∀ z ∈ U, ‖conjWirtingerDeriv (u n) z 1 - g n z‖ ≤ M)
    (hB : ∀ n, eLpNorm (g n) p (volume.restrict U) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F,
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K := by
  classical
  have hH : ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, ∀ n, HolderOnWith C (1 - 2 / p) (u n) K :=
    fun K hK hKU ↦ (exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le hp hU hK hKU A M B).imp
      fun C hC n ↦ hC (u n) (g n) (hu n) (hA n) (hM n) (hB n)
  have hα : 0 < 1 - 2 / p := tsub_pos_of_lt ((div_lt_one₀ (zero_lt_two.trans hp)).2 hp)
  -- A common Hölder bound on a closed disc about each point of `U` gives equicontinuity.
  have hequi : EquicontinuousOn u U := equicontinuousOn_of_forall_holderOnWith hα fun x hx ↦ by
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨C, hC⟩ := hH (closedBall x (r / 2)) (isCompact_closedBall x _)
      ((closedBall_subset_ball (by linarith)).trans hrU)
    exact ⟨C, _, closedBall_mem_nhds x (by positivity), hC⟩
  obtain ⟨φ, hφ, v, hconvOn⟩ := hequi.exists_strictMono_tendstoLocallyUniformlyOn hU fun z hz ↦
    ⟨closedBall 0 A, isCompact_closedBall _ _, fun n ↦ mem_closedBall_zero_iff.2 (hA n z hz)⟩
  refine ⟨φ, hφ, v, hconvOn, fun K hK hKU ↦ ?_⟩
  obtain ⟨C, hC⟩ := hH K hK hKU
  exact ⟨C, HolderOnWith.of_tendsto (fun z hz ↦ hconvOn.tendsto_at (hKU hz))
    (Eventually.of_forall fun n ↦ hC (φ n))⟩

end TauCeti
