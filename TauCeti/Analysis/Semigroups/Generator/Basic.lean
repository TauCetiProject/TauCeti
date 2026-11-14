/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Semigroups.GrowthBound
import Mathlib.Topology.Algebra.Group.Order

/-!
# Generators of strongly continuous semigroups

This file defines the infinitesimal generator as a `LinearPMap`, exposes domain
membership through the explicit right-difference-quotient limit, and proves the local
orbit-integral lemmas giving density of the generator domain. These include the shift identity
`S(h) ∫_0^t S(σ) y dσ - ∫_0^t S(σ) y dσ = ∫_t^{t+h} S(σ) y dσ - ∫_0^h S(σ) y dσ` for `t, h ≥ 0`
(`StronglyContinuousSemigroup.realOperator_intervalIntegral_orbit_sub`), together with
continuity and norm bounds for the orbit integral `∫_0^τ S(σ) y dσ`.

## References
Ported and adapted (Apache 2.0) from `mrdouglasny/hille-yosida`; references include
Engel--Nagel, Linares, Pazy, Hille, and Yosida.
-/

public section

noncomputable section

open scoped Topology NNReal
open MeasureTheory

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The integral averages `(1/t) • ∫_{(0,t]} g u du` of a function that is locally strongly
measurable and continuous at `0` from the right tend to `g 0` as `t → 0⁺`. -/
private theorem tendsto_average_Ioc_zero_of_stronglyMeasurableAtFilter_continuousWithinAt_Ioi
    {g : ℝ → X} (hmeas : StronglyMeasurableAtFilter g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) volume)
    (hg0 : ContinuousWithinAt g (Set.Ioi 0) 0) :
    Filter.Tendsto
      (fun t => (1 / t) • ∫ u in Set.Ioc 0 t, g u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) := by
  have h_ftc :
      HasDerivWithinAt (fun u => ∫ t in (0 : ℝ)..u, g t) (g 0) (Set.Ioi 0) 0 :=
    (intervalIntegral.integral_hasDerivWithinAt_right IntervalIntegrable.refl hmeas
      hg0).Ioi_of_Ici
  have h_slope :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp h_ftc
  refine h_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [slope_def_module, sub_zero, intervalIntegral.integral_same, sub_zero,
    intervalIntegral.integral_of_le ht.le, one_div]

/-! ## The Infinitesimal Generator -/

/-- The generator difference quotient `(S t x - x)/t`; its `t → 0⁺` limit (when it
exists) is the generator value at `x`. -/
private def StronglyContinuousSemigroup.genQuot (S : StronglyContinuousSemigroup X)
    (x : X) (t : ℝ) : X := (1 / t) • (S.realOperator t x - x)

omit [CompleteSpace X] in
/-- The generator difference quotient is additive in the limit. -/
private theorem StronglyContinuousSemigroup.genQuot_tendsto_add
    (S : StronglyContinuousSemigroup X) {x y Ax Ay : X}
    (hx : Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax))
    (hy : Filter.Tendsto (S.genQuot y) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ay)) :
    Filter.Tendsto (S.genQuot (x + y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ax + Ay)) := by
  have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      S.genQuot (x + y) t = S.genQuot x t + S.genQuot y t := by
    filter_upwards with t
    simp only [StronglyContinuousSemigroup.genQuot]
    rw [ContinuousLinearMap.map_add, add_sub_add_comm, smul_add]
  exact (hx.add hy).congr' (heq.mono (fun _ h => h.symm))

omit [CompleteSpace X] in
/-- The generator difference quotient is `ℝ`-homogeneous in the limit. -/
private theorem StronglyContinuousSemigroup.genQuot_tendsto_smul
    (S : StronglyContinuousSemigroup X) (c : ℝ) {x Ax : X}
    (hx : Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax)) :
    Filter.Tendsto (S.genQuot (c • x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c • Ax)) := by
  have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      S.genQuot (c • x) t = c • S.genQuot x t := by
    filter_upwards with t
    simp only [StronglyContinuousSemigroup.genQuot, map_smul, smul_sub, smul_comm c (1 / t)]
  exact (hx.const_smul c).congr' (heq.mono (fun _ h => h.symm))

/-- The domain `D(A)` of the generator, as a `ℝ`-submodule of `X`. -/
def StronglyContinuousSemigroup.domain (S : StronglyContinuousSemigroup X) :
    Submodule ℝ X where
  carrier := { x | ∃ Ax : X,
    Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax) }
  add_mem' := by
    rintro x y ⟨Ax, hAx⟩ ⟨Ay, hAy⟩
    exact ⟨Ax + Ay, S.genQuot_tendsto_add hAx hAy⟩
  zero_mem' := by
    refine ⟨0, ?_⟩
    have h0 :
        (fun t => (1 / t) • (S.realOperator t (0 : X) - 0)) = fun _ => (0 : X) := by
      ext t
      simp
    rw [h0]; exact tendsto_const_nhds
  smul_mem' := by
    rintro c x ⟨Ax, hAx⟩
    exact ⟨c • Ax, S.genQuot_tendsto_smul c hAx⟩

/-- The infinitesimal generator `A` as an unbounded operator (`LinearPMap`),
`A x = lim_{t→0⁺} (S t x - x)/t` on the domain `D(A)` where the limit exists
([EN] Def. II.1.2). Modelled as `X →ₗ.[ℝ] X` so it composes with Mathlib's
unbounded-operator API. -/
noncomputable def StronglyContinuousSemigroup.generator
    (S : StronglyContinuousSemigroup X) : X →ₗ.[ℝ] X where
  domain := S.domain
  toFun :=
    { toFun := fun x => Classical.choose x.property
      map_add' := fun x y => by
        -- additivity of the difference-quotient limit (`genQuot_tendsto_add`), after
        -- reconciling the submodule coercion `↑(x + y) = ↑x + ↑y`.
        have h := S.genQuot_tendsto_add (Classical.choose_spec x.property)
          (Classical.choose_spec y.property)
        rw [← Submodule.coe_add] at h
        exact tendsto_nhds_unique (Classical.choose_spec (x + y).property) h
      map_smul' := fun c x => by
        -- `ℝ`-homogeneity of the difference-quotient limit (`genQuot_tendsto_smul`), after
        -- reconciling the submodule coercion `↑(c • x) = c • ↑x`.
        have h := S.genQuot_tendsto_smul c (Classical.choose_spec x.property)
        rw [← Submodule.coe_smul] at h
        exact tendsto_nhds_unique (Classical.choose_spec (c • x).property) h }

omit [CompleteSpace X] in
/-- `S.generator.domain` is the generator domain submodule. -/
@[simp] theorem StronglyContinuousSemigroup.generator_domain
    (S : StronglyContinuousSemigroup X) : S.generator.domain = S.domain := by
  rfl

omit [CompleteSpace X] in
/-- A vector lies in the generator domain iff its difference quotient `(S t x - x)/t`
converges as `t → 0⁺` ([EN] Def. II.1.2). -/
theorem StronglyContinuousSemigroup.mem_domain_iff_tendsto
    (S : StronglyContinuousSemigroup X) (x : X) :
    x ∈ S.domain ↔ ∃ y, Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y) :=
  by rfl

omit [CompleteSpace X] in
/-- Characteristic property of the generator: for `x` in the domain, the difference
quotient `(S t x - x)/t` converges to `S.generator x` as `t → 0⁺` ([EN] Def. II.1.2). -/
theorem StronglyContinuousSemigroup.generator_tendsto
    (S : StronglyContinuousSemigroup X) (x : S.domain) :
    Filter.Tendsto (fun t => (1 / t) • (S.realOperator t (x : X) - (x : X)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (S.generator ⟨(x : X), by
        rw [S.generator_domain]
        exact x.property⟩)) := by
  simp only [StronglyContinuousSemigroup.generator]
  exact Classical.choose_spec x.property

omit [CompleteSpace X] in
/-- The generator difference quotient, rebased at `s`: the defining quotient of `S.generator` at
`x` (`generator_tendsto`), precomposed with `u ↦ u - s` so that it approaches `s` from the right
rather than `0`. -/
theorem StronglyContinuousSemigroup.generator_tendsto_comp_sub_const
    (S : StronglyContinuousSemigroup X) (x : S.domain) (s : ℝ) :
    Filter.Tendsto (fun u : ℝ => (u - s)⁻¹ • (S.realOperator (u - s) (x : X) - (x : X)))
      (nhdsWithin s (Set.Ioi s))
      (nhds (S.generator ⟨(x : X), by
        rw [S.generator_domain]
        exact x.property⟩)) := by
  have hshift : Filter.Tendsto (fun u : ℝ => u - s) (nhdsWithin s (Set.Ioi s))
      (nhdsWithin 0 (Set.Ioi 0)) :=
    le_of_eq (by rw [Filter.map_subRight_nhdsGT, sub_self])
  simpa [Function.comp_def, one_div] using (S.generator_tendsto x).comp hshift

omit [CompleteSpace X] in
/-- Eliminator for the generator: if the difference quotient `(S t x - x)/t` of an
`x ∈ D(A)` converges to `y`, then `A x = y`. -/
theorem StronglyContinuousSemigroup.generator_eq_of_tendsto
    (S : StronglyContinuousSemigroup X) {x : X} (hx : x ∈ S.domain) {y : X}
    (h : Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y)) :
    S.generator ⟨x, by
      rw [S.generator_domain]
      exact hx⟩ = y :=
  tendsto_nhds_unique (S.generator_tendsto ⟨x, hx⟩) h

omit [CompleteSpace X] in
/-- If the generator difference quotient of every vector of `A.domain` converges to `A x`, then
`A` is a restriction of the generator. -/
theorem StronglyContinuousSemigroup.le_generator_of_forall_tendsto
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X}
    (h : ∀ x : A.domain, Filter.Tendsto
      (fun t => (1 / t) • (S.realOperator t (x : X) - (x : X)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (A x))) :
    A ≤ S.generator := by
  have hmem : ∀ x : A.domain, (x : X) ∈ S.domain := fun x =>
    (S.mem_domain_iff_tendsto (x : X)).mpr ⟨A x, h x⟩
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · rw [S.generator_domain]
    exact hmem ⟨x, hx⟩
  · rw [← S.generator_eq_of_tendsto (hmem x) (h x)]
    exact congrArg _ (Subtype.ext hxy)

omit [CompleteSpace X] in
/-- If every generator difference quotient converges to `L x` for a linear operator `L`, then
the generator domain is the whole space and the generator is `L` as a total `LinearPMap`. -/
theorem StronglyContinuousSemigroup.generator_eq_toPMap_top_of_forall_tendsto
    (S : StronglyContinuousSemigroup X) (L : X →ₗ[ℝ] X)
    (h : ∀ x, Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (L x))) :
    S.domain = ⊤ ∧ S.generator = L.toPMap ⊤ := by
  have hmem : ∀ x, x ∈ S.domain := fun x => (S.mem_domain_iff_tendsto x).mpr ⟨L x, h x⟩
  have hdomain : S.domain = ⊤ := by
    ext x
    simp [hmem x]
  refine ⟨hdomain, ?_⟩
  refine LinearPMap.ext ?_ ?_
  · rw [S.generator_domain, hdomain, LinearMap.toPMap_domain]
  · intro x hx _
    -- `LinearPMap.ext` leaves the goal on the coercion of `S.generator`, whose argument still
    -- carries the membership proof from the old domain; `change` names the bundled element.
    change S.generator ⟨x, hx⟩ = L x
    exact S.generator_eq_of_tendsto (hmem x) (h x)



/-- The integral average `(1/t) • ∫_{(0,t]} S(u)x du` of the orbit tends to `x` as `t → 0⁺`. -/
theorem StronglyContinuousSemigroup.tendsto_average_orbit_zero
    (S : StronglyContinuousSemigroup X) (x : X) :
    Filter.Tendsto
      (fun t => (1 / t) • ∫ u in Set.Ioc 0 t, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  have h_cont_Ioi : ContinuousOn (fun u => S.realOperator u x) (Set.Ioi 0) :=
    (S.realOperator_continuousOn_Ici x).mono Set.Ioi_subset_Ici_self
  have h := tendsto_average_Ioc_zero_of_stronglyMeasurableAtFilter_continuousWithinAt_Ioi
    (g := fun u => S.realOperator u x)
    (h_cont_Ioi.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
    ((S.realOperator_continuousWithinAt x 0).mono Set.Ioi_subset_Ici_self)
  simpa using h

/-- Joint continuity of the orbit integral `(τ, y) ↦ ∫_0^τ S(σ) y dσ`. -/
theorem StronglyContinuousSemigroup.continuous_intervalIntegral_orbit
    (S : StronglyContinuousSemigroup X) :
    Continuous fun p : ℝ × X => ∫ σ in (0 : ℝ)..p.1, S.realOperator σ p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × X) σ => S.realOperator σ p.2)
    (S.continuous_realOperator_uncurry.comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst))) continuous_fst

omit [CompleteSpace X] in
/-- `‖∫_0^τ S(σ) y dσ‖ ≤ C ‖y‖ τ` when `S` is bounded by `C` on `(0, τ]`. -/
theorem StronglyContinuousSemigroup.norm_intervalIntegral_orbit_le
    (S : StronglyContinuousSemigroup X) {C τ : ℝ} (hτ : 0 ≤ τ)
    (hC : ∀ σ ∈ Set.Ioc 0 τ, ‖S.realOperator σ‖ ≤ C) (y : X) :
    ‖∫ σ in (0 : ℝ)..τ, S.realOperator σ y‖ ≤ C * ‖y‖ * τ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := τ) (f := fun σ => S.realOperator σ y) (C := C * ‖y‖) fun σ hσ => by
      rw [Set.uIoc_of_le hτ] at hσ
      exact (S.realOperator σ).le_of_opNorm_le (hC _ hσ) _
  rwa [sub_zero, abs_of_nonneg hτ] at h

/-- `S(a) ∫_0^b S(σ) y dσ = ∫_a^{a+b} S(σ) y dσ` for `a, b ≥ 0`. -/
theorem StronglyContinuousSemigroup.realOperator_intervalIntegral_orbit
    (S : StronglyContinuousSemigroup X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : X) :
    S.realOperator a (∫ σ in (0 : ℝ)..b, S.realOperator σ y) =
      ∫ σ in a..a + b, S.realOperator σ y := by
  rw [← (S.realOperator a).intervalIntegral_comp_comm
      ((S.continuous_realOperator_apply y).intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun σ => S.realOperator (σ + a) y)]
  · rw [intervalIntegral.integral_comp_add_right (fun σ => S.realOperator σ y), zero_add,
      add_comm b a]
  · intro σ hσ
    rw [Set.uIcc_of_le hb] at hσ
    simp only
    rw [← S.realOperator_add_apply a σ ha hσ.1, add_comm]

/-- The shift identity for orbit integrals:
`S(h) ∫_0^t S(σ) y dσ - ∫_0^t S(σ) y dσ = ∫_t^{t+h} S(σ) y dσ - ∫_0^h S(σ) y dσ`
for `t, h ≥ 0`. -/
theorem StronglyContinuousSemigroup.realOperator_intervalIntegral_orbit_sub
    (S : StronglyContinuousSemigroup X) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (y : X) :
    S.realOperator h (∫ σ in (0 : ℝ)..t, S.realOperator σ y) -
        ∫ σ in (0 : ℝ)..t, S.realOperator σ y =
      (∫ σ in t..t + h, S.realOperator σ y) - ∫ σ in (0 : ℝ)..h, S.realOperator σ y := by
  have hi (a b : ℝ) : IntervalIntegrable (fun σ => S.realOperator σ y) volume a b :=
    (S.continuous_realOperator_apply y).intervalIntegrable a b
  rw [S.realOperator_intervalIntegral_orbit hh ht, add_comm t h]
  exact intervalIntegral.integral_interval_sub_interval_comm' (hi _ _) (hi _ _) (hi _ _)

/-- `(S(h) - 1) ∫_0^τ S = (S(τ) - 1) ∫_0^h S` for `τ, h ≥ 0`: both sides are
`∫_τ^{τ+h} S - ∫_0^h S`. -/
theorem StronglyContinuousSemigroup.realOperator_intervalIntegral_orbit_sub_comm
    (S : StronglyContinuousSemigroup X) {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h) (y : X) :
    S.realOperator h (∫ σ in (0 : ℝ)..τ, S.realOperator σ y) -
        ∫ σ in (0 : ℝ)..τ, S.realOperator σ y =
      S.realOperator τ (∫ σ in (0 : ℝ)..h, S.realOperator σ y) -
        ∫ σ in (0 : ℝ)..h, S.realOperator σ y := by
  have hi (a b : ℝ) : IntervalIntegrable (fun σ => S.realOperator σ y) volume a b :=
    (S.continuous_realOperator_apply y).intervalIntegrable a b
  rw [S.realOperator_intervalIntegral_orbit_sub hτ hh,
    S.realOperator_intervalIntegral_orbit_sub hh hτ, add_comm h τ]
  exact intervalIntegral.integral_interval_sub_interval_comm' (hi _ _) (hi _ _) (hi _ _)

private theorem StronglyContinuousSemigroup.tendsto_average_orbit_at
    (S : StronglyContinuousSemigroup X) (x : X) (t : ℝ) :
    Filter.Tendsto (fun h => (1 / h) • ∫ u in t..t + h, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x)) := by
  set f := fun u => S.realOperator u x
  have hf : Continuous f := S.continuous_realOperator_apply x
  have h_ftc : HasDerivAt (fun u => ∫ z in t..u, f z) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt
  have h_slope := h_ftc.tendsto_slope_zero_right
  simpa [f, one_div, intervalIntegral.integral_same] using h_slope

/-- The difference quotient of the local orbit integral `∫₀ᵗ S(u)x du` converges to
`S t x - x` as the time-step `→ 0⁺` (the limit underlying [EN] Lemma II.1.3). -/
private theorem StronglyContinuousSemigroup.tendsto_quot_integral_orbit
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun h => (1 / h) •
        (S.realOperator h (∫ u in Set.Ioc 0 t, S.realOperator u x)
        - ∫ u in Set.Ioc 0 t, S.realOperator u x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x - x)) := by
  set y := ∫ u in (0 : ℝ)..t, S.realOperator u x
  have h_zero : Filter.Tendsto
      (fun h => (1 / h) • ∫ u in (0 : ℝ)..h, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    have h := S.tendsto_average_orbit_zero x
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [intervalIntegral.integral_of_le hh.le]
  have h_t : Filter.Tendsto
      (fun h => (1 / h) • ∫ u in t..t + h, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x)) :=
    S.tendsto_average_orbit_at x t
  have h_lim := h_t.sub h_zero
  have h_interval : Filter.Tendsto
      (fun h => (1 / h) • (S.realOperator h y - y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x - x)) := by
    refine h_lim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [S.realOperator_intervalIntegral_orbit_sub ht.le hh.le x]
    rw [smul_sub]
  simpa [y, intervalIntegral.integral_of_le ht.le] using h_interval

/-- The local orbit integral `∫₀ᵗ S(u)x du` lies in the generator domain `D(A)`
([EN] Lemma II.1.3). For `t ≤ 0` the integral is over an empty interval, hence `0`. -/
theorem StronglyContinuousSemigroup.integral_orbit_mem_domain
    (S : StronglyContinuousSemigroup X) (x : X) (t : ℝ) :
    (∫ u in Set.Ioc 0 t, S.realOperator u x) ∈ S.domain := by
  rcases le_or_gt t 0 with ht | ht
  · simp [Set.Ioc_eq_empty (not_lt.2 ht)]
  · exact (S.mem_domain_iff_tendsto _).mpr ⟨_, S.tendsto_quot_integral_orbit x ht⟩

/-- The generator value on the local orbit integral: `A (∫₀ᵗ S(u)x du) = S t x - x`
([EN] Lemma II.1.3). For `t ≤ 0` both sides are `0`. -/
theorem StronglyContinuousSemigroup.generator_integral_orbit
    (S : StronglyContinuousSemigroup X) (x : X) (t : ℝ) :
    S.generator ⟨∫ u in Set.Ioc 0 t, S.realOperator u x, by
      rw [S.generator_domain]
      exact S.integral_orbit_mem_domain x t⟩
      = S.realOperator t x - x := by
  rcases le_or_gt t 0 with ht | ht
  · have h0 : (∫ u in Set.Ioc 0 t, S.realOperator u x) = 0 := by
      simp [Set.Ioc_eq_empty (not_lt.2 ht)]
    have h : (⟨∫ u in Set.Ioc 0 t, S.realOperator u x, by
        rw [S.generator_domain]
        exact S.integral_orbit_mem_domain x t⟩ : S.generator.domain) = 0 := Subtype.ext h0
    rw [h, LinearPMap.map_zero, S.realOperator_of_nonpos_apply ht, sub_self]
  · exact S.generator_eq_of_tendsto (S.integral_orbit_mem_domain x t)
      (S.tendsto_quot_integral_orbit x ht)

/-- The generator domain of a strongly continuous semigroup is dense
([EN] Lemma II.1.3 and its density corollary). -/
theorem StronglyContinuousSemigroup.dense_domain
    (S : StronglyContinuousSemigroup X) : Dense (S.domain : Set X) := by
  intro x
  refine mem_closure_of_tendsto
    (f := fun t => (1 / t) • ∫ u in Set.Ioc 0 t, S.realOperator u x)
    (b := nhdsWithin 0 (Set.Ioi (0 : ℝ))) ?_ ?_
  · simpa using S.tendsto_average_orbit_zero x
  · filter_upwards [self_mem_nhdsWithin] with t _
    exact S.domain.smul_mem (1 / t) (S.integral_orbit_mem_domain x t)

/-- Two continuous linear maps that agree on the (dense) generator domain are equal. -/
theorem StronglyContinuousSemigroup.continuousLinearMap_ext_of_eqOn_domain
    (S : StronglyContinuousSemigroup X)
    {f g : X →L[ℝ] X} (h : ∀ x ∈ S.domain, f x = g x) : f = g :=
  ContinuousLinearMap.ext_on (R₁ := ℝ) (s := (S.domain : Set X))
    (by rw [Submodule.span_eq]; exact S.dense_domain) h

end TauCeti.Semigroups

end
