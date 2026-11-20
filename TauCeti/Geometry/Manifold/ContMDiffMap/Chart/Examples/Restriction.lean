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
  have hp : (0 : ℝ) < p.val := p.property.1
  refine ⟨{q | p.val / 2 < q.val}, (isOpen_lt continuous_const continuous_subtypeVal).mem_nhds
    (half_lt_self hp), (finite_lt_nat ⌈2 / p.val⌉₊).subset ?_⟩
  rintro j ⟨_, rfl, hj⟩
  -- `p / 2 < 1 / (j + 2)` forces `j + 2 < 2 / p`.
  replace hj : (p.val : ℝ) / 2 < 1 / (j + 2) := hj
  have hlt : (j : ℝ) < 2 / p.val := by
    rw [lt_div_iff₀ hp]
    rw [lt_div_iff₀ (by positivity)] at hj
    nlinarith
  exact Nat.cast_lt.mp (hlt.trans_le (Nat.le_ceil _))

/-- The strong neighbourhood of `0` on `(0, 1)` asking for `|g (1 / (j + 2))| < 1 / (j + 2)` for
every `j`. -/
private noncomputable def control (n : ℕ∞) : StrongCkControl 𝓘(ℝ) U₀ n :=
  .ofPoints point locallyFinite_singleton_point (fun j ↦ 1 / (j + 2)) fun _ ↦ by positivity

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
  have h : ‖(δ • u).restrict U₀ (point j)‖ < 1 / (j + 2) := by
    simpa using StrongCkControl.mem_ball_ofPoints.mp hδ j
  rw [restrict_apply, coe_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [point, coeFn_mk, hψ, mul_one, Real.norm_of_nonneg hδpos.le] at h
  linarith

end ContMDiffMap
