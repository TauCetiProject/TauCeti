/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.OrbitCutoff.Discrete

/-!
# Unfolding sums over orbits

Let a discrete subgroup `Γ` of a second countable locally compact group `G` act on a countable set
`Y`, and let `k_y` (`y ∈ Y`) be measurable functions on `G` with `k_{γ • y} (γ x) = k_y (x)`. The
integral over `Γ \ G` of the sum of the `k_z` over the orbit of `y` is the integral of `k_y` over
`Γ_y \ G`, where `Γ_y` is the stabiliser of `y`
(`Subgroup.integral_tsum_orbit_eq_integral_stabilizer`). The hypothesis is that the sum of the
norms `‖k_z‖` over the orbit has finite integral over `Γ \ G`, or equivalently that `k_y` is
integrable over `Γ_y \ G`; integrability over `Γ \ G` of the sum of the `k_z` themselves does not
suffice, since it allows cancellation. This is the unfolding of Poincaré-type series.

More generally, if `C ⊂ Y` is a block, in the sense that `γ` carries a point of `C` into `C`
exactly when `γ` lies in a subgroup `S ⊂ Γ`, and `∑_{y ∈ D} ‖k_y‖` has finite integral over
`Γ \ G`, or equivalently `∑_{y ∈ C} ‖k_y‖` has finite integral over `S \ G`, then the integral
over `Γ \ G` of the sum over the union `D` of the translates of `C` is the integral over `S \ G` of
the sum over `C` (`Subgroup.integral_tsum_block`).

Integrals over `Γ \ G` are integrals against `Γ.cutoffMeasure μ`
(`TauCeti/MeasureTheory/Group/OrbitCutoff/Basic.lean`).

## References

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(`New.tsum_cutoff_smul_mem_block`, `New.lintegral_tsum_block`,
`New.integral_tsum_eq_integral_tsum_block`, `New.tsum_integral_eq_integral_tsum_block`,
`New.integral_tsum_block`, `New.integral_tsum_orbit_eq_integral_stabilizer`).
-/

public section

open MeasureTheory Measure Set MulAction ProbabilityTheory

open scoped ENNReal

namespace Subgroup

variable {G Y : Type*} [Group G] {Γ S : Subgroup G} [MulAction Γ Y] {C D : Set Y}

open scoped Classical in
/-- Let `γ ∈ Γ` carry a point of `C` into `C` exactly when `γ ∈ S`, and let `D` be the union of the
translates of `C`. If the values of `β` along each `S`-orbit in `G` sum to one, then the sum of
`β (γ x)` over the `γ` that carry `y` into `C` is `1` if `y ∈ D` and `0` otherwise. -/
private theorem tsum_ite_smul_mem_eq (hS : S ≤ Γ) (hC : ∀ γ : Γ, ∀ y ∈ C, γ • y ∈ C ↔ ↑γ ∈ S)
    (hD : ∀ y, y ∈ D ↔ ∃ γ : Γ, γ • y ∈ C) {β : G → ℝ≥0∞} (hβ : ∀ x, ∑' s : S, β (s * x) = 1)
    (y : Y) (x : G) :
    ∑' γ : Γ, (if γ • y ∈ C then β (γ * x) else 0) = if y ∈ D then 1 else 0 := by
  split_ifs with hy
  · obtain ⟨γ₀, hγ₀⟩ := (hD y).1 hy
    -- `(γ γ₀) • y ∈ C` exactly when `γ ∈ S`
    let b : G → ℝ≥0∞ := (S : Set G).indicator fun g ↦ β (g * (γ₀ * x))
    calc ∑' γ : Γ, (if γ • y ∈ C then β (γ * x) else 0)
      _ = ∑' γ : Γ, (if (γ * γ₀) • y ∈ C then β (↑(γ * γ₀) * x) else 0) :=
          ((Equiv.mulRight γ₀).tsum_eq _).symm
      _ = ∑' γ : Γ, b γ := by
          refine tsum_congr fun γ ↦ ?_
          simp [b, indicator, mul_smul, mul_assoc, hC _ _ hγ₀]
      _ = ∑' g : G, b g :=
          tsum_subtype_eq_of_support_subset fun g hg ↦ hS (support_indicator_subset hg)
      _ = ∑' s : S, β (s * (γ₀ * x)) := (tsum_subtype (S : Set G) _).symm
      _ = 1 := hβ _
  · simp [not_exists.1 (mt (hD y).2 hy)]

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [Countable Y] {μ : Measure G} [μ.IsHaarMeasure]

/-- **Unfolding over a block, for nonnegative functions.** Let `γ ∈ Γ` carry a point of `C ⊂ Y`
into `C` exactly when `γ ∈ S ⊂ Γ`, and let `D` be the union of the translates of `C`. For
measurable `g_y ≥ 0` with `g_{γ • y} (γ x) = g_y (x)`,
`∫_{Γ\G} ∑_{y ∈ D} g_y = ∫_{S\G} ∑_{y ∈ C} g_y`. -/
theorem lintegral_tsum_block (hS : S ≤ Γ) (hC : ∀ γ : Γ, ∀ y ∈ C, γ • y ∈ C ↔ ↑γ ∈ S)
    (hD : ∀ y, y ∈ D ↔ ∃ γ : Γ, γ • y ∈ C) {g : Y → G → ℝ≥0∞} (hg : ∀ y, Measurable (g y))
    (hg_inv : ∀ (γ : Γ) y x, g (γ • y) (γ * x) = g y x) :
    ∫⁻ x, ∑' y : D, g y x ∂Γ.cutoffMeasure μ = ∫⁻ x, ∑' y : C, g y x ∂S.cutoffMeasure μ := by
  classical
  -- With the chosen cutoff `β` of `S`, unfold `β x ∑_C g_y x` along `Γ`, and substitute
  -- `y ↦ γ • y` in the term of `γ`.
  have : DiscreteTopology S := .of_subset (s := (Γ : Set G)) inferInstance hS
  have : Countable Γ := countable_of_Lindelof_of_discrete
  let β : G → ℝ≥0∞ := (count : Measure S).orbitCutoff
  have hβ := isOrbitCutoff_count_iff.1 (isOrbitCutoff_orbitCutoff (count : Measure S) (X := G))
  have hβ_one (x : G) : ∑' s : S, β (s * x) = 1 := hβ.2 x
  have h_term (γ : Γ) (x : G) : β (γ * x) * ∑' y : C, g y (γ * x) =
      ∑' y : Y, (if γ • y ∈ C then β (γ * x) else 0) * g y x := by
    rw [tsum_subtype C fun y ↦ g y (γ * x), ← (MulAction.toPerm γ).tsum_eq,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun y ↦ ?_
    simp only [toPerm_apply, indicator, hg_inv]
    split_ifs <;> simp
  have h_sum (x : G) : ∑' γ : Γ, β (γ * x) * ∑' y : C, g y (γ * x) = ∑' y : D, g y x := by
    simp only [h_term]
    rw [tsum_comm]
    simp only [ENNReal.tsum_mul_right, tsum_ite_smul_mem_eq hS hC hD hβ_one,
      tsum_subtype D fun y ↦ g y x]
    exact tsum_congr fun y ↦ by by_cases hy : y ∈ D <;> simp [hy, indicator]
  calc ∫⁻ x, ∑' y : D, g y x ∂Γ.cutoffMeasure μ
    _ = ∫⁻ x, ∫⁻ γ : Γ, β (γ • x) * ∑' y : C, g y (γ • x) ∂count ∂Γ.cutoffMeasure μ := by
        simp only [lintegral_count, ← h_sum, Subgroup.smul_def, smul_eq_mul]
    _ = ∫⁻ x, β x * ∑' y : C, g y x ∂μ :=
        lintegral_cutoffMeasure_lintegral (f := fun x ↦ β x * ∑' y : C, g y x)
          (hβ.1.mul (Measurable.tsum fun y : C ↦ hg y))
    _ = ∫⁻ x, ∑' y : C, g y x ∂S.cutoffMeasure μ := by
        rw [Subgroup.cutoffMeasure, cutoffMeasure_def, lintegral_withDensity_eq_lintegral_mul _ hβ.1
          (Measurable.tsum fun y : C ↦ hg y)]
        simp only [Pi.mul_apply, β]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- **Unfolding over a block.** Let `γ ∈ Γ` carry a point of `C ⊂ Y` into `C` exactly when
`γ ∈ S ⊂ Γ`, let `D` be the union of the translates of `C`, and let the `k_y` be measurable with
`k_{γ • y} (γ x) = k_y (x)`. If `∑_{y ∈ D} ‖k_y‖` has finite integral over `Γ \ G`, or
`∑_{y ∈ C} ‖k_y‖` has finite integral over `S \ G`, then both have, `∑_{y ∈ D} k_y` is integrable
over `Γ \ G`, `∑_{y ∈ C} k_y` is integrable over `S \ G`, and
`∫_{Γ\G} ∑_{y ∈ D} k_y = ∫_{S\G} ∑_{y ∈ C} k_y`. -/
theorem integral_tsum_block (hS : S ≤ Γ) (hC : ∀ γ : Γ, ∀ y ∈ C, γ • y ∈ C ↔ ↑γ ∈ S)
    (hD : ∀ y, y ∈ D ↔ ∃ γ : Γ, γ • y ∈ C) {k : Y → G → E} (hk : ∀ y, Measurable (k y))
    (hk_inv : ∀ (γ : Γ) y x, k (γ • y) (γ * x) = k y x)
    (h_fin : ∫⁻ x, ∑' y : D, ‖k y x‖ₑ ∂Γ.cutoffMeasure μ < ∞ ∨
      ∫⁻ x, ∑' y : C, ‖k y x‖ₑ ∂S.cutoffMeasure μ < ∞) :
    ∫⁻ x, ∑' y : D, ‖k y x‖ₑ ∂Γ.cutoffMeasure μ < ∞ ∧
      ∫⁻ x, ∑' y : C, ‖k y x‖ₑ ∂S.cutoffMeasure μ < ∞ ∧
      Integrable (fun x ↦ ∑' y : D, k y x) (Γ.cutoffMeasure μ) ∧
      Integrable (fun x ↦ ∑' y : C, k y x) (S.cutoffMeasure μ) ∧
      ∫ x, ∑' y : D, k y x ∂Γ.cutoffMeasure μ = ∫ x, ∑' y : C, k y x ∂S.cutoffMeasure μ := by
  -- `(x, y) ↦ k_y x` has the same law on `(Γ \ G) × D` and on `(S \ G) × C`; then Fubini.
  let : MeasurableSpace Y := ⊤
  have h_unfold (f : E → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ x, ∑' y : D, f (k y x) ∂Γ.cutoffMeasure μ = ∫⁻ x, ∑' y : C, f (k y x) ∂S.cutoffMeasure μ :=
    lintegral_tsum_block hS hC hD (g := fun y x ↦ f (k y x)) (fun y ↦ hf.comp (hk y))
      fun γ y x ↦ by simp [hk_inv]
  rw [h_unfold _ measurable_eNorm, or_self] at h_fin
  have hD_fin : ∫⁻ x, ∑' y : D, ‖k y x‖ₑ ∂Γ.cutoffMeasure μ < ∞ := by
    rwa [h_unfold _ measurable_eNorm]
  have h_meas (T : Set Y) : Measurable fun p : G × T ↦ k p.2 p.1 :=
    measurable_from_prod_countable_left fun y ↦ hk y
  have h_dist : IdentDistrib (fun p : G × D ↦ k p.2 p.1) (fun p : G × C ↦ k p.2 p.1)
      ((Γ.cutoffMeasure μ).prod count) ((S.cutoffMeasure μ).prod count) := by
    refine ⟨(h_meas D).aemeasurable, (h_meas C).aemeasurable, ext_of_lintegral _ fun f hf ↦ ?_⟩
    rw [lintegral_map hf (h_meas D), lintegral_map hf (h_meas C),
      lintegral_prod (fun p : G × D ↦ f (k p.2 p.1)) (hf.comp (h_meas D)).aemeasurable,
      lintegral_prod (fun p : G × C ↦ f (k p.2 p.1)) (hf.comp (h_meas C)).aemeasurable]
    simpa only [lintegral_count] using h_unfold f hf
  have hC_int : Integrable (fun p : G × C ↦ k p.2 p.1) ((S.cutoffMeasure μ).prod count) := by
    refine ⟨(h_meas C).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ (h_meas C).eNorm.aemeasurable]
    simpa only [lintegral_count] using h_fin
  have hD_int := h_dist.integrable_iff.2 hC_int
  refine ⟨hD_fin, h_fin,
    integrable_tsum_of_integrable_prod_count (k := fun (y : D) x ↦ k y x) hD_int,
    integrable_tsum_of_integrable_prod_count (k := fun (y : C) x ↦ k y x) hC_int, ?_⟩
  calc ∫ x, ∑' y : D, k y x ∂Γ.cutoffMeasure μ
      _ = ∫ p : G × D, k p.2 p.1 ∂(Γ.cutoffMeasure μ).prod count :=
        (integral_prod_count_eq_integral_tsum (k := fun (y : D) x ↦ k y x) hD_int).symm
      _ = ∫ p : G × C, k p.2 p.1 ∂(S.cutoffMeasure μ).prod count := h_dist.integral_eq
      _ = ∫ x, ∑' y : C, k y x ∂S.cutoffMeasure μ :=
        integral_prod_count_eq_integral_tsum (k := fun (y : C) x ↦ k y x) hC_int

/-- **Unfolding over an orbit.** Let the `k_y` be measurable with `k_{γ • y} (γ x) = k_y (x)`, and
let `Γ_y` be the stabiliser of `y`, as a subgroup of `G`. If the sum of `‖k_z‖` over the orbit of
`y` has finite integral over `Γ \ G`, or `k_y` is integrable over `Γ_y \ G`, then both hold, the
sum of the `k_z` over the orbit is integrable over `Γ \ G`, and
`∫_{Γ\G} ∑_{z ∈ Γ y} k_z = ∫_{Γ_y\G} k_y`. -/
theorem integral_tsum_orbit_eq_integral_stabilizer {k : Y → G → E} (hk : ∀ y, Measurable (k y))
    (hk_inv : ∀ (γ : Γ) y x, k (γ • y) (γ * x) = k y x) {y : Y}
    (h_fin : ∫⁻ x, ∑' z : orbit Γ y, ‖k z x‖ₑ ∂Γ.cutoffMeasure μ < ∞ ∨
      Integrable (k y) (((stabilizer Γ y).map Γ.subtype).cutoffMeasure μ)) :
    ∫⁻ x, ∑' z : orbit Γ y, ‖k z x‖ₑ ∂Γ.cutoffMeasure μ < ∞ ∧
      Integrable (fun x ↦ ∑' z : orbit Γ y, k z x) (Γ.cutoffMeasure μ) ∧
      Integrable (k y) (((stabilizer Γ y).map Γ.subtype).cutoffMeasure μ) ∧
      ∫ x, ∑' z : orbit Γ y, k z x ∂Γ.cutoffMeasure μ =
        ∫ x, k y x ∂((stabilizer Γ y).map Γ.subtype).cutoffMeasure μ := by
  -- The block `C = {y}`: the orbit is the union of its translates.
  have hS : (stabilizer Γ y).map Γ.subtype ≤ Γ := by
    simpa using (stabilizer Γ y).map_le_range Γ.subtype
  have hC (γ : Γ) : ∀ z ∈ ({y} : Set Y), γ • z ∈ ({y} : Set Y) ↔
      ↑γ ∈ (stabilizer Γ y).map Γ.subtype := by
    simp
  have hD (z : Y) : z ∈ orbit Γ y ↔ ∃ γ : Γ, γ • z ∈ ({y} : Set Y) := by
    simp [mem_orbit_symm (a₁ := z), mem_orbit_iff]
  have h_block : ∫⁻ x, ∑' z : orbit Γ y, ‖k z x‖ₑ ∂Γ.cutoffMeasure μ < ∞ ∨
      ∫⁻ x, ∑' z : ({y} : Set Y), ‖k z x‖ₑ ∂((stabilizer Γ y).map Γ.subtype).cutoffMeasure μ < ∞ :=
    h_fin.imp_right fun h_int ↦ by simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  obtain ⟨h_orbit, -, h_int, h_int', h_eq⟩ :=
    integral_tsum_block (μ := μ) hS hC hD hk hk_inv h_block
  simp only [tsum_fintype, Finset.univ_unique, default_coe_singleton, Finset.sum_singleton]
    at h_int' h_eq
  exact ⟨h_orbit, h_int, h_int', h_eq⟩

end Subgroup
