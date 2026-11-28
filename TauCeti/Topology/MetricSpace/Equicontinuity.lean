/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Equicontinuity from slice distance bounds, and uniform attainment from rate bounds

When `g : X × Y → Z` is jointly continuous on a product with `Y` compact, the tube lemma around
each compact slice `{x₀} × Y` upgrades pointwise continuity of `g` to locally uniform control in
`y : Y`: every `δ > 0` holds uniformly across `Y` on a neighbourhood of `x₀`. Consequently, any
family `F : ι → X → W` into a pseudometric space whose distances are controlled linearly by uniform
`Y`-slice distance bounds of `g` (such as marginal integrals, suprema, infima, or log-partition
transforms of `g`) is equicontinuous on `X`.

Separately, uniform equicontinuity of a family `(g_k)` turns a bound `F k p ≤ C (η + s(p) L)`,
valid whenever `g_k` moves by at most `η` over distances at most `√(s p)`, into the uniform
smallness `F k p < ε` for all `k` once `s p` is small enough.

Finally, the iterates of a `1`-Lipschitz map are `1`-Lipschitz, so they form a uniformly
equicontinuous family, and maps that are Hölder on a set with one constant and one positive exponent
form a family uniformly equicontinuous on that set.

## Main statements

* `Metric.uniformEquicontinuousOn_iff`: uniform equicontinuity on a set in terms of distances.
* `Metric.equicontinuous_of_forall_dist_le`: a family `F : ι → X → W` controlled linearly by every
  uniform `Y`-slice distance bound of a jointly continuous map `g : X × Y → Z` with `Y` compact is
  equicontinuous.
* `UniformEquicontinuous.exists_forall_lt_of_le_mul_add_mul`: a bound of the form
  `C (η + s L)` over a uniformly equicontinuous family gives uniform attainment as `s → 0`.
* `LipschitzWith.uniformEquicontinuous_iterate`: the iterates of a `1`-Lipschitz map are uniformly
  equicontinuous.
* `HolderOnWith.uniformEquicontinuousOn`: maps sharing a Hölder constant and a positive exponent on
  a set are uniformly equicontinuous on it.
-/

public section

open Filter Set Topology

namespace Metric

/-- **Tube-lemma equicontinuity criterion.** If `g : X × Y → Z` is jointly continuous into a
pseudometric space with `Y` compact, and a family `F : ι → X → W` into a pseudometric space has
distances controlled linearly by every uniform `Y`-slice distance bound of `g`, then `F` is
equicontinuous. -/
theorem equicontinuous_of_forall_dist_le {X Y Z W ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [PseudoMetricSpace Z] [PseudoMetricSpace W]
    {g : X × Y → Z} (hg : Continuous g) {F : ι → X → W} {L : ℝ}
    (hosc : ∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, dist (g (x₁, y)) (g (x₂, y)) ≤ δ) →
      ∀ i, dist (F i x₁) (F i x₂) ≤ L * δ) :
    Equicontinuous F := by
  intro x₀
  rw [Metric.uniformity_basis_dist.equicontinuousAt_iff_right]
  intro r hr
  set M : ℝ := max L 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
  set δ : ℝ := r / (2 * M)
  have hδ : 0 < δ := div_pos hr (mul_pos two_pos hM)
  have hn : IsOpen {z : X × Y | dist (g z) (g (x₀, z.2)) < δ} :=
    isOpen_lt (hg.dist (hg.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hx₀u, huv_univ, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x₀)) isCompact_univ hn
      (by rintro ⟨x, y⟩ ⟨rfl, _⟩; simpa using hδ)
  filter_upwards [hu.mem_nhds (hx₀u rfl)] with x hxu i
  rw [dist_comm]
  calc dist (F i x) (F i x₀)
      ≤ L * δ := hosc x x₀ δ hδ.le (fun y ↦ (huv ⟨hxu, huv_univ (mem_univ y)⟩).le) i
    _ ≤ M * δ := mul_le_mul_of_nonneg_right (le_max_left L 1) hδ.le
    _ = r / 2 := by simp only [δ]; field_simp [hM.ne']
    _ < r := half_lt_self hr

/-- Characterization of uniform equicontinuity on a set for families of functions between
(pseudo) metric spaces. -/
theorem uniformEquicontinuousOn_iff {ι X W : Type*} [PseudoMetricSpace X] [PseudoMetricSpace W]
    {F : ι → X → W} {S : Set X} :
    UniformEquicontinuousOn F S ↔ ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε := by
  rw [(uniformity_basis_dist.inf_principal (S ×ˢ S)).uniformEquicontinuousOn_iff
    uniformity_basis_dist]
  refine forall₂_congr fun ε _ ↦ exists_congr fun δ ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun h x hx y hy hxy ↦ h x y ⟨hxy, hx, hy⟩, fun h x y hxy ↦ h x hxy.2.1 y hxy.2.2 hxy.1⟩

end Metric

namespace UniformEquicontinuous

open Real

/-- `X ε / (2 (X + 1)) < ε / 2` for `X ≥ 0` and `ε > 0`. -/
private theorem mul_div_two_mul_add_one_lt {ε : ℝ} (hε : 0 < ε) (X : ℝ) (hX : 0 ≤ X) :
    X * (ε / (2 * (X + 1))) < ε / 2 := by
  have hX1 : X / (X + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  calc X * (ε / (2 * (X + 1))) = ε / 2 * (X / (X + 1)) := by field_simp
    _ < ε / 2 * 1 := mul_lt_mul_of_pos_left hX1 (by positivity)
    _ = ε / 2 := mul_one _

/-- **From a rate of attainment to uniform attainment.** Let `(g_k)` be a uniformly equicontinuous
family of real functions, and let `F k p ≤ C (η + s(p) L)` whenever `g_k` moves by at most `η`
over distances at most `√(s p)`, where `C ≥ 0` and `s ≥ 0`. Then `F k p < ε` for all `k` and all
`p` with `s p` small enough. -/
theorem exists_forall_lt_of_le_mul_add_mul {κ X P : Type*} [PseudoMetricSpace X]
    {g : κ → X → ℝ} (hg : UniformEquicontinuous g) {F : κ → P → ℝ} {s : P → ℝ}
    (hs : ∀ p, 0 ≤ s p) {C L : ℝ} (hC : 0 ≤ C)
    (hF : ∀ η k p, (∀ x y, dist x y ≤ √(s p) → |g k x - g k y| ≤ η) →
      F k p ≤ C * (η + s p * L))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k p, s p < δ → F k p < ε := by
  set R := C * |L|
  set η := ε / (2 * (C + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁η⟩ := Metric.uniformEquicontinuous_iff.1 hg η hη
  refine ⟨min (δ₁ ^ 2) (ε / (2 * (R + 1))), by positivity, fun k p hp ↦ ?_⟩
  have hsδ : √(s p) < δ₁ := by
    rw [← sqrt_sq hδ₁.le]
    exact sqrt_lt_sqrt (hs p) (hp.trans_le (min_le_left _ _))
  have key := hF η k p fun x y hxy ↦ by
    simpa [Real.dist_eq] using (hδ₁η x y (hxy.trans_lt hsδ) k).le
  have hR : C * (s p * L) ≤ R * s p := by
    calc _ = C * s p * L := by ring
      _ ≤ C * s p * |L| := mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hC (hs p))
      _ = _ := by ring
  have hRs : R * s p ≤ R * (ε / (2 * (R + 1))) :=
    mul_le_mul_of_nonneg_left (hp.le.trans (min_le_right _ _)) (by positivity)
  -- Each of the two terms is less than `ε / 2`.
  have h₁ := mul_div_two_mul_add_one_lt hε C hC
  have h₂ := mul_div_two_mul_add_one_lt hε R (by positivity)
  calc _ ≤ C * (η + s p * L) := key
    _ = C * η + C * (s p * L) := by ring
    _ < ε := by linarith

end UniformEquicontinuous

/-- The iterates of a `1`-Lipschitz map are uniformly equicontinuous. -/
theorem LipschitzWith.uniformEquicontinuous_iterate {X : Type*} [PseudoEMetricSpace X]
    {f : X → X} (hf : LipschitzWith 1 f) : UniformEquicontinuous fun n : ℕ ↦ f^[n] :=
  LipschitzWith.uniformEquicontinuous _ 1 fun n ↦ by simpa using hf.iterate n

/-- Maps that are `r`-Hölder on `s` with one constant `C`, for a fixed exponent `r > 0`, form a
family uniformly equicontinuous on `s`. Compare `LipschitzWith.uniformEquicontinuous`. -/
theorem HolderOnWith.uniformEquicontinuousOn {ι X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] (f : ι → X → Y) {s : Set X} {C r : NNReal} (hr : 0 < r)
    (h : ∀ i, HolderOnWith C r (f i) s) : UniformEquicontinuousOn f s := by
  rw [(uniformity_basis_edist.inf_principal (s ×ˢ s)).uniformEquicontinuousOn_iff
    uniformity_basis_edist]
  intro ε hε
  have hC : Tendsto (fun d : ENNReal ↦ (C : ENNReal) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hr
  obtain ⟨δ, hδ, H⟩ := ENNReal.nhds_zero_basis.mem_iff.1 (hC (gt_mem_nhds hε))
  exact ⟨δ, hδ, fun x y hxy i ↦ ((h i).edist_le hxy.2.1 hxy.2.2).trans_lt (H hxy.1)⟩
