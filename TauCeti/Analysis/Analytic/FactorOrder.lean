/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ConstantOrder
public import TauCeti.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.ENat.BigOperators

/-!
# Orders of factors in analytic families

The order of a slice of a jointly analytic function cannot increase near a parameter where
it is finite. Consequently, if a finite product has constant finite slice order, each factor
has constant slice order. Over `ℝ` or `ℂ`, each factor is therefore a power of the distinguished
variable times an analytic unit, locally at the base point.

Applied to the product of squared differences of analytic polynomial roots, this gives the
power-times-unit form of each root difference from the corresponding form of the discriminant.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4.
-/

public section

open Filter Topology

namespace TauCeti

section Slice

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Near a parameter where a jointly analytic function has finite slice order `m`,
its slice orders are at most `m`. -/
theorem eventually_analyticOrderAt_curry_right_le {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ}
    (hm : analyticOrderAt (fun y ↦ G (x₀, y)) y₀ = m) :
    ∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ G (x, y)) y₀ ≤ m := by
  induction m generalizing G with
  | zero =>
    have hne := hG.curry_right.analyticOrderAt_eq_zero.1 hm
    have hev := ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
      (hG.continuousAt.eventually_ne hne)
    filter_upwards [hev, hG.eventually_analyticAt_curry_right] with x hx hGx
    simp [hGx.analyticOrderAt_eq_zero.2 hx]
  | succ m ih =>
    -- The partial derivative lowers the central slice order by one. Its nearby
    -- slice orders control those of `G`, except where `G` is already nonzero.
    let H : E × 𝕜 → F := fun p ↦ fderiv 𝕜 G p (0, 1)
    have hH : AnalyticAt 𝕜 H (x₀, y₀) :=
      ((ContinuousLinearMap.apply 𝕜 F ((0 : E), (1 : 𝕜))).analyticAt _).comp hG.fderiv
    have hderiv {p : E × 𝕜} (hp : AnalyticAt 𝕜 G p) :
        deriv (fun y ↦ G (p.1, y)) p.2 = H p :=
      (hp.differentiableAt.hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
    have heq : ∀ᶠ x in 𝓝 x₀,
        (fun y ↦ H (x, y)) =ᶠ[𝓝 y₀] deriv (fun y ↦ G (x, y)) := by
      have hev := hG.eventually_analyticAt
      rw [nhds_prod_eq] at hev
      exact hev.curry.mono fun x hx ↦ hx.mono fun y hy ↦ (hderiv hy).symm
    have h0 : G (x₀, y₀) = 0 :=
      apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun y ↦ G (x₀, y)) (by simp [hm])
    have hHm : analyticOrderAt (fun y ↦ H (x₀, y)) y₀ = m := by
      have hd := hG.curry_right.analyticOrderAt_deriv_add_one
      simp only [h0, sub_zero] at hd
      rw [hm, ← analyticOrderAt_congr heq.self_of_nhds, Nat.cast_succ] at hd
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hd
    filter_upwards [ih hH hHm, heq, hG.eventually_analyticAt_curry_right] with x hx hxy hGx
    by_cases hz : G (x, y₀) = 0
    · have hd := hGx.analyticOrderAt_deriv_add_one
      simp only [hz, sub_zero] at hd
      rw [← analyticOrderAt_congr hxy] at hd
      rw [← hd, Nat.cast_succ]
      exact add_le_add hx le_rfl
    · simp [hGx.analyticOrderAt_eq_zero.2 hz]

end Slice

section Factors

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If a finite product of jointly analytic functions has constant finite slice order,
then every factor has constant slice order near the parameter. -/
theorem eventually_analyticOrderAt_factor_eq {s : Finset ι} {G : ι → E × 𝕜 → 𝕜}
    {x₀ : E} {y₀ : 𝕜} (hG : ∀ i ∈ s, AnalyticAt 𝕜 (G i) (x₀, y₀)) {m : ℕ}
    (hm : ∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ ∏ i ∈ s, G i (x, y)) y₀ = m) :
    ∀ᶠ x in 𝓝 x₀, ∀ i ∈ s,
      analyticOrderAt (fun y ↦ G i (x, y)) y₀ =
        analyticOrderAt (fun y ↦ G i (x₀, y)) y₀ := by
  classical
  have hsum₀ : (∑ i ∈ s, analyticOrderAt (fun y ↦ G i (x₀, y)) y₀) = m := by
    rw [← analyticOrderAt_prod (fun i hi ↦ (hG i hi).curry_right)]
    simpa only [Finset.prod_fn] using hm.self_of_nhds
  have hfinite : ∀ i ∈ s, analyticOrderAt (fun y ↦ G i (x₀, y)) y₀ ≠ ⊤ :=
    ENat.sum_ne_top.1 (by rw [hsum₀]; exact ENat.natCast_ne_top m)
  have hupper : ∀ᶠ x in 𝓝 x₀, ∀ i ∈ s,
      analyticOrderAt (fun y ↦ G i (x, y)) y₀ ≤
        analyticOrderAt (fun y ↦ G i (x₀, y)) y₀ := by
    rw [eventually_all_finset]
    intro i hi
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfinite i hi)
    rw [← hn]
    exact eventually_analyticOrderAt_curry_right_le (hG i hi) hn.symm
  have hanalytic : ∀ᶠ x in 𝓝 x₀, ∀ i ∈ s, AnalyticAt 𝕜 (fun y ↦ G i (x, y)) y₀ := by
    rw [eventually_all_finset]
    exact fun i hi ↦ (hG i hi).eventually_analyticAt_curry_right
  filter_upwards [hm, hupper, hanalytic] with x hmx hx hax
  have hfinite_x : ∀ i ∈ s, analyticOrderAt (fun y ↦ G i (x, y)) y₀ ≠ ⊤ :=
    fun i hi ↦ ne_top_of_le_ne_top (hfinite i hi) (hx i hi)
  -- All orders are finite, so natural-number sums give cancellation: no summand
  -- can decrease while their sum stays fixed.
  have hsum : (∑ i ∈ s, analyticOrderNatAt (fun y ↦ G i (x, y)) y₀) =
      ∑ i ∈ s, analyticOrderNatAt (fun y ↦ G i (x₀, y)) y₀ := by
    have hsum_x : (∑ i ∈ s, analyticOrderAt (fun y ↦ G i (x, y)) y₀) = m := by
      rw [← analyticOrderAt_prod hax]
      simpa only [Finset.prod_fn] using hmx
    simpa only [ENat.toNat_sum hfinite_x, ENat.toNat_sum hfinite, analyticOrderNatAt] using
      congrArg ENat.toNat (hsum_x.trans hsum₀.symm)
  have hnat : ∀ i ∈ s, analyticOrderNatAt (fun y ↦ G i (x, y)) y₀ ≤
      analyticOrderNatAt (fun y ↦ G i (x₀, y)) y₀ := by
    intro i hi
    simpa only [analyticOrderNatAt] using ENat.toNat_le_toNat (hx i hi) (hfinite i hi)
  intro i hi
  rw [← Nat.cast_analyticOrderNatAt (hfinite_x i hi),
    ← Nat.cast_analyticOrderNatAt (hfinite i hi),
    (Finset.sum_eq_sum_iff_of_le hnat).1 hsum i hi]

end Factors

section Units

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every factor of a jointly analytic product of constant finite slice order is locally
a centered power of the distinguished variable times an analytic unit. -/
theorem exists_factor_eq_pow_mul_unit {s : Finset ι} {G : ι → E × 𝕜 → 𝕜}
    {x₀ : E} {y₀ : 𝕜} (hG : ∀ i ∈ s, AnalyticAt 𝕜 (G i) (x₀, y₀)) {m : ℕ}
    (hm : ∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ ∏ i ∈ s, G i (x, y)) y₀ = m) :
    ∀ i ∈ s, ∃ n : ℕ, ∃ u : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 u (x₀, y₀) ∧ u (x₀, y₀) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), G i p = (p.2 - y₀) ^ n * u p := by
  have heq := eventually_analyticOrderAt_factor_eq hG hm
  have hsum : (∑ i ∈ s, analyticOrderAt (fun y ↦ G i (x₀, y)) y₀) = m := by
    rw [← analyticOrderAt_prod (fun i hi ↦ (hG i hi).curry_right)]
    simpa only [Finset.prod_fn] using hm.self_of_nhds
  intro i hi
  have hfinite := ENat.sum_ne_top.1 (by rw [hsum]; exact ENat.natCast_ne_top m) i hi
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfinite
  obtain ⟨u, hu, hu0, hGu⟩ := (hG i hi).eventually_analyticOrderAt_eq_natCast_iff.1
    (heq.mono fun x hx ↦ (hx i hi).trans hn.symm)
  exact ⟨n, u, hu, hu0, by simpa only [smul_eq_mul] using hGu⟩

end Units

end TauCeti
