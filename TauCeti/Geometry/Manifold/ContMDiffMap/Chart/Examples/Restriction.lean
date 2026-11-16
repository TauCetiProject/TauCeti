/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Restriction to `(0, 1)` is not continuous for the strong Whitney topologies

Restriction of `C^n` functions from `ℝ` to the open interval `U = (0, 1)` is not continuous from
the strong Whitney topology of `ℝ` to that of `U`, for any finite or infinite smoothness order
`n`. So the closedness hypothesis of `ContMDiffMap.continuous_restrict_manifoldStrongWhitney`
cannot be dropped.

The strong neighbourhood of `0` on `U` used here asks for `|g (1 / (j + 2))| < 1 / (j + 2)` for
every `j`; its compact coordinate sets accumulate only at the frontier point `0`, so they are
locally finite in `U` but not in `ℝ`. A bump function `ψ` equal to `1` near `0` has compact support,
so its small multiples `δ • ψ` tend to `0` strongly on `ℝ`
(`ContMDiffMap.tendsto_smul_manifoldStrongWhitney`), but no nonzero multiple restricts into this
neighbourhood: at the points `1 / (j + 2) < δ` it takes the value `δ`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, pp. 34–36, for the strong `C^r`
  topology.
-/

public section

open Set Filter Topology TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

/-- The open unit interval as an open subset of `ℝ`. -/
private abbrev U₀ : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

/-- The points `1 / (j + 2)` lie in `(0, 1)`. -/
private theorem one_div_add_two_mem_Ioo (j : ℕ) : (1 / (j + 2) : ℝ) ∈ Ioo 0 1 :=
  ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])⟩

/-- The point `1 / (j + 2)` of `(0, 1)`. -/
private noncomputable def point (j : ℕ) : U₀ :=
  ⟨1 / (j + 2), one_div_add_two_mem_Ioo j⟩

/-- The points `1 / (j + 2)` accumulate only at `0`, so they form a locally finite family in
`(0, 1)`. -/
private theorem locallyFinite_singleton_point : LocallyFinite fun j ↦ ({point j} : Set U₀) := by
  intro p
  have hp : (0 : ℝ) < p.1 := p.2.1
  refine ⟨{q | p.1 / 2 < q.1}, (isOpen_lt continuous_const continuous_subtype_val).mem_nhds
    (half_lt_self hp), (finite_lt_nat ⌈2 / p.1⌉₊).subset ?_⟩
  rintro j ⟨_, rfl, hj⟩
  -- `p / 2 < 1 / (j + 2)` forces `j + 2 < 2 / p`.
  replace hj : (p.1 : ℝ) / 2 < 1 / (j + 2) := hj
  have hlt : (j : ℝ) < 2 / p.1 := by
    rw [lt_div_iff₀ hp]
    rw [lt_div_iff₀ (by positivity)] at hj
    nlinarith
  exact Nat.cast_lt.mp (hlt.trans_le (Nat.le_ceil _))

/-- The coordinate of the point `1 / (j + 2)` in its own chart, as a compact coordinate set. -/
private noncomputable def pointCompacts (j : ℕ) : Compacts (extChartAt 𝓘(ℝ) (point j)).target :=
  ⟨{⟨_, mem_extChartAt_target (point j)⟩}, isCompact_singleton⟩

/-- The strong neighbourhood of `0` on `(0, 1)` asking for `|g (1 / (j + 2))| < 1 / (j + 2)` for
every `j`. -/
private noncomputable def control (n : ℕ∞) : StrongCkControl 𝓘(ℝ) U₀ n where
  ι := ℕ
  center := point
  compact := pointCompacts
  order := 0
  order_le := by simp
  tolerance j := 1 / (j + 2)
  tolerance_pos _ := by positivity
  locallyFinite := locallyFinite_singleton_point.subset fun j ↦ by
    rintro _ ⟨_, ⟨_, rfl, rfl⟩, rfl⟩
    exact extChartAt_to_inv (point j)

/-- A function in the neighbourhood `control` satisfies `|g (1 / (j + 2))| < 1 / (j + 2)`. -/
private theorem norm_lt_of_mem_ball_control {n : ℕ∞} {g : C^n⟮𝓘(ℝ), U₀; 𝓘(ℝ), ℝ⟯}
    (hg : g ∈ (control n).ball 0) (j : ℕ) : ‖g (point j)‖ < 1 / (j + 2) := by
  have hb : chartCkSeminorm (point j) (pointCompacts j) 0 (by simp) g < 1 / (j + 2) := by
    -- The control's data unfold to the point `1 / (j + 2)`, order `0` and that tolerance.
    have h := StrongCkControl.mem_ball.mp hg j
    rw [sub_zero] at h
    exact h
  have h := (chartCkSeminorm_lt_iff _ _ _ _ _ (by positivity)).mp hb 0 le_rfl _ rfl
  rwa [chartIteratedFDeriv_self_target_apply, norm_iteratedFDerivWithin_zero,
    Function.comp_apply, extChartAt_to_inv] at h

/-- **Restriction from `ℝ` to `(0, 1)` is not continuous for the strong Whitney topologies.** -/
theorem not_continuous_restrict_Ioo_manifoldStrongWhitney {n : ℕ∞} :
    ¬ Continuous[manifoldStrongWhitneyTopology, manifoldStrongWhitneyTopology]
      (fun f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ ↦ f.restrict ⟨Ioo 0 1, isOpen_Ioo⟩) := by
  intro hcont
  let := (manifoldStrongWhitneyTopology : TopologicalSpace C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯)
  let := (manifoldStrongWhitneyTopology : TopologicalSpace C^n⟮𝓘(ℝ), U₀; 𝓘(ℝ), ℝ⟯)
  -- A bump function equal to `1` on `[-1, 1]`.
  let ψ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let u : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ := ⟨ψ, ψ.contDiff.contMDiff⟩
  -- Small multiples of `u` restrict into the neighbourhood `control`, so some positive one does.
  have hlim : Tendsto (fun δ : ℝ ↦ (δ • u).restrict U₀) (𝓝 0) (𝓝 0) := by
    have h := (hcont.tendsto 0).comp (tendsto_smul_manifoldStrongWhitney u ψ.hasCompactSupport)
    rwa [restrict_zero] at h
  obtain ⟨δ, hδ, hδpos⟩ := (((hlim.eventually (((control n).isOpen_ball 0).mem_nhds
    ((control n).mem_ball_self 0))).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Ioi 0))).exists
  -- At a point `1 / (j + 2) < δ`, where `ψ = 1`, the restriction takes the value `δ`.
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδpos
  have hle : (1 / (j + 2) : ℝ) ≤ 1 / (j + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hψ : ψ (1 / (j + 2)) = 1 := ψ.one_of_mem_closedBall <| by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_of_nonneg (by positivity)]
    exact (one_div_add_two_mem_Ioo j).2.le
  have h := norm_lt_of_mem_ball_control hδ j
  rw [restrict_apply, coe_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [point, coeFn_mk, hψ, mul_one, Real.norm_of_nonneg hδpos.le] at h
  linarith

end ContMDiffMap
