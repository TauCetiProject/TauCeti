/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Slice orders from Laurent unit forms

An analytic function agreeing with a fixed Laurent power times an analytic unit off a
coordinate hyperplane has locally constant slice order on that hyperplane. The Laurent
representation is allowed to use an integer exponent; analyticity forces that exponent to
be nonnegative. This lets finite extensions of meromorphic root branches retain their
contact orders after poles have been removed from other branches.
-/

public section

open Filter Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A fixed Laurent unit form off a coordinate hyperplane makes the slice order of an
analytic function with complete codomain locally constant on the hyperplane. The equality
need not be supplied on the hyperplane itself. -/
theorem AnalyticAt.eventually_analyticOrderAt_eq_of_zpow_smul_unit
    {G w : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜} {b : ℤ}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) (hw : AnalyticAt 𝕜 w (x₀, y₀))
    (hw0 : w (x₀, y₀) ≠ 0)
    (heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → G p = (p.2 - y₀) ^ b • w p) :
    ∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ G (x, y)) y₀ =
      analyticOrderAt (fun y ↦ G (x₀, y)) y₀ := by
  have hne := ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
    (hw.continuousAt.eventually_ne hw0)
  rw [nhds_prod_eq] at heq
  have horder : ∀ᶠ x in 𝓝 x₀,
      (analyticOrderAt (fun y ↦ G (x, y)) y₀).map (Nat.cast : ℕ → ℤ) = (b : WithTop ℤ) := by
    filter_upwards [heq.curry, hG.eventually_analyticAt_curry_right,
      hw.eventually_analyticAt_curry_right, hne] with x hx hGx hwx hwx0
    rw [← hGx.meromorphicOrderAt_eq]
    refine (meromorphicOrderAt_eq_int_iff hGx.meromorphicAt).2 ⟨_, hwx, hwx0, ?_⟩
    exact eventually_nhdsWithin_iff.2 hx
  exact horder.mono fun x hx ↦ ENat.map_natCast_injective
    (hx.trans horder.self_of_nhds.symm)
