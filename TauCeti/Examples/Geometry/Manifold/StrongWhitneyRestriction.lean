/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong

/-!
# Restriction to a non-closed open set is not strongly continuous

Restriction of smooth maps to an open subset `U` of a manifold is continuous for the strong
Whitney topologies when `U` is also closed
(`ContMDiffMap.continuous_restrict_manifoldStrongWhitney`), and from the strong to the weak Whitney
topology for every open `U`. This file shows that closedness cannot be dropped from the first
statement: restriction from `ℝ` to the open interval `(0, 1)` is not continuous for the strong
Whitney topologies of `C^n` maps, for every order `n ≤ ∞`
(`TauCeti.not_continuous_restrict_Ioo_manifoldStrongWhitney`).

The witness is a strong neighbourhood of `0` on `(0, 1)` whose tolerances shrink towards the
missing endpoint `0`: the value at the point `1 / (j + 2)` must be smaller than `1 / (j + 2)`.
These points are locally finite in `(0, 1)` but not in `ℝ`, and no strong neighbourhood of `0` on
`ℝ` forces maps to be small near `0` at such rates.
-/

public section

open Set Filter Topology TopologicalSpace ContMDiffMap
open scoped Manifold

namespace TauCeti

variable {n : ℕ∞}

/-- The open interval `(0, 1)`, as an open subset of `ℝ`. -/
private def unitInterval₀ : Opens ℝ :=
  ⟨Ioo 0 1, isOpen_Ioo⟩

/-- The points `1 / (j + 2)` of the open interval `(0, 1)`. -/
private noncomputable def unitInterval₀Point (j : ℕ) : unitInterval₀ :=
  ⟨1 / (j + 2), by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

/-- The points `1 / (j + 2)` are locally finite in `(0, 1)`: near a point `p` of `(0, 1)` only the
finitely many with `p / 2 < 1 / (j + 2)` occur. -/
private theorem locallyFinite_unitInterval₀Point :
    LocallyFinite fun j ↦ ({unitInterval₀Point j} : Set unitInterval₀) := by
  intro p
  have hp : (0 : ℝ) < p := p.2.1
  refine ⟨{q | (p : ℝ) / 2 < q}, (isOpen_lt continuous_const continuous_subtype_val).mem_nhds
    (half_lt_self hp), (finite_lt_nat ⌈2 / (p : ℝ)⌉₊).subset fun j ⟨q, hqj, hq⟩ ↦ ?_⟩
  rw [mem_singleton_iff.mp hqj] at hq
  have hq : (p : ℝ) / 2 < 1 / (j + 2) := hq
  have hj : (j : ℝ) + 2 < 2 / p := by
    rw [lt_div_iff₀ hp]
    rw [lt_div_iff₀ (by positivity)] at hq
    linarith
  exact_mod_cast (by linarith : (j : ℝ) < 2 / p).trans_le (Nat.le_ceil _)

/-- The strong neighbourhood of `0` on `(0, 1)` given by the value tolerances `1 / (j + 2)` at the
points `1 / (j + 2)`. -/
private noncomputable def unitInterval₀Control : StrongCkControl 𝓘(ℝ) unitInterval₀ n where
  ι := ℕ
  center := unitInterval₀Point
  compact j := ⟨{⟨extChartAt 𝓘(ℝ) (unitInterval₀Point j) (unitInterval₀Point j),
    mem_extChartAt_target _⟩}, isCompact_singleton⟩
  order := 0
  order_le := by simp
  tolerance j := 1 / (j + 2)
  tolerance_pos j := by positivity
  locallyFinite := locallyFinite_unitInterval₀Point.subset fun j ↦ by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [Compacts.coe_mk, mem_singleton_iff] at hz
    rw [hz, mem_singleton_iff]
    exact extChartAt_to_inv _

/-- A smooth map on `(0, 1)` within the neighbourhood `unitInterval₀Control.ball 0` of `0` is
smaller than `1 / (j + 2)` at the point `1 / (j + 2)`. -/
private theorem abs_lt_of_mem_ball_unitInterval₀Control {g : C^n⟮𝓘(ℝ), unitInterval₀; 𝓘(ℝ), ℝ⟯}
    (hg : g ∈ unitInterval₀Control.ball 0) (j : ℕ) :
    |g (unitInterval₀Point j)| < 1 / (j + 2) := by
  simpa [unitInterval₀Control] using
    StrongCkControl.norm_sub_lt_of_mem_ball hg j (z := ⟨_, mem_extChartAt_target _⟩) rfl

open scoped TauCeti.ManifoldStrongWhitney in
/-- **Restriction to a non-closed open set need not be strongly continuous.** Restriction from `ℝ`
to the open interval `(0, 1)` is not continuous for the strong Whitney topologies of `C^n` maps,
for every `n ≤ ∞`. Compare `ContMDiffMap.continuous_restrict_manifoldStrongWhitney`, which gives
continuity for a clopen subset. -/
theorem not_continuous_restrict_Ioo_manifoldStrongWhitney :
    ¬Continuous[manifoldStrongWhitneyTopology, manifoldStrongWhitneyTopology]
      fun f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ ↦ f.restrict ⟨Ioo 0 1, isOpen_Ioo⟩ := by
  intro h
  let β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ := ⟨β, β.contDiff.contMDiff⟩
  -- The restrictions of `δ • ψ` tend to `0` as `δ → 0`, so for some `δ > 0` the restriction lies in
  -- the strong neighbourhood `unitInterval₀Control.ball 0` of `0` on `(0, 1)`.
  have hball : unitInterval₀Control.ball (0 : C^n⟮𝓘(ℝ), unitInterval₀; 𝓘(ℝ), ℝ⟯) ∈
      𝓝 ((0 : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯).restrict unitInterval₀) :=
    (unitInterval₀Control.isOpen_ball _).mem_nhds <| by
      convert unitInterval₀Control.mem_ball_self _
      exact ContMDiffMap.ext fun _ ↦ by simp
  obtain ⟨δ, hδc, hδ⟩ := ((((h.tendsto 0).comp (tendsto_smul_nhds_zero_manifoldStrongWhitney
    (ψ := ψ) β.hasCompactSupport)).eventually hball).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin |>.exists (f := 𝓝[>] (0 : ℝ))
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  have hlt : |(δ • ψ).restrict unitInterval₀ (unitInterval₀Point j)| < 1 / (j + 2) :=
    abs_lt_of_mem_ball_unitInterval₀Control hδc j
  -- At the point `1 / (j + 2)` the bump is `1`, so the restriction of `δ • ψ` has value `δ` there.
  have hψ : ψ (1 / (j + 2) : ℝ) = 1 := β.one_of_mem_closedBall <| by
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_le_one (by positivity)]
    linarith
  have hval : (δ • ψ).restrict unitInterval₀ (unitInterval₀Point j) = δ := by
    rw [ContMDiffMap.restrict_apply, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact (congrArg (δ * ·) hψ).trans (mul_one δ)
  rw [hval, abs_of_pos hδ] at hlt
  have : (1 : ℝ) / (j + 2) ≤ 1 / (j + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

end TauCeti
