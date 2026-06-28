/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Generators of strongly continuous semigroups

This file defines the infinitesimal generator as a `LinearPMap`, exposes domain
membership through the explicit right-difference-quotient limit, and proves the local
orbit-integral lemmas giving density of the generator domain.

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

/-! ## The Infinitesimal Generator -/

/-- The generator difference quotient `(S t x - x)/t`; its `t → 0⁺` limit (when it
exists) is the generator value at `x`. -/
private def StronglyContinuousSemigroup.genQuot (S : StronglyContinuousSemigroup X)
    (x : X) (t : ℝ) : X := (1 / t) • (S.realOperator t x - x)

/-- Membership predicate for the generator's domain: the difference quotient
`(S t x - x)/t` converges as `t → 0⁺` ([EN] Def. II.1.2, [Linares] Def. 2).
Equivalently `x ∈ S.domain`; the generator itself is the `LinearPMap`
`StronglyContinuousSemigroup.generator`. -/
private def StronglyContinuousSemigroup.IsInGeneratorDomain (S : StronglyContinuousSemigroup X)
    (x : X) : Prop :=
  ∃ Ax : X, Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax)

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
    rw [map_add, add_sub_add_comm, smul_add]
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
/-- Eliminator for the generator: if the difference quotient `(S t x - x)/t` of an
`x ∈ D(A)` converges to `y`, then `A x = y` (by uniqueness of limits). -/
theorem StronglyContinuousSemigroup.generator_eq_of_tendsto
    (S : StronglyContinuousSemigroup X) {x : X} (hx : x ∈ S.domain) {y : X}
    (h : Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y)) :
    S.generator ⟨x, by
      rw [S.generator_domain]
      exact hx⟩ = y :=
  tendsto_nhds_unique (S.generator_tendsto ⟨x, hx⟩) h



/-- The integral average `(1/t) • ∫_{(0,t]} S(u)x du` of the orbit tends to `x` as `t → 0⁺`. -/
private theorem StronglyContinuousSemigroup.tendsto_average_orbit_zero
    (S : StronglyContinuousSemigroup X) (x : X) :
    Filter.Tendsto
      (fun t => (1 / t) • ∫ u in Set.Ioc 0 t, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  set f := fun t => S.realOperator t x
  -- Modify `f` for `t < 0` so the FTC sees two-sided continuity at `0`.
  set g : ℝ → X := fun t => if 0 ≤ t then f t else x with hg_def
  have hg_cont : Filter.Tendsto g (nhds 0) (nhds x) := by
    rw [← nhdsLT_sup_nhdsGE (0 : ℝ)]
    apply Filter.Tendsto.sup
    · exact (tendsto_const_nhds (x := x)).congr' (by
        filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
        simp only [g, if_neg (not_le.mpr ht)])
    · exact (S.strong_cont x).congr' (by
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
        simp only [g, f, if_pos ht])
  have hg_eq : ∀ t, 0 < t →
      ∫ u in Set.Ioc 0 t, g u = ∫ u in Set.Ioc 0 t, f u := by
    intro t ht
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    simp [hg_def, hu.1.le]
  have hg_continuous : Continuous g := by
    have hg_pw : g = Set.piecewise (Set.Ici 0) f (fun _ => x) := rfl
    rw [hg_pw]
    apply continuous_piecewise
    · intro t ht
      have := frontier_Ici_subset (a := (0:ℝ)) ht
      simp only [Set.mem_singleton_iff] at this
      subst this
      simp [f]
    · rw [closure_Ici]
      exact fun t₀ ht₀ => S.strongContWithinAt x t₀ ht₀
    · exact continuousOn_const
  have h_ftc : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, g t) x 0 :=
    intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
      IntervalIntegrable.refl
      (hg_continuous.stronglyMeasurableAtFilter volume (nhds 0))
      (hg_cont.mono_left inf_le_left)
  have h_slope := h_ftc.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at h_slope
  exact h_slope.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [one_div, intervalIntegral.integral_of_le (le_of_lt ht), hg_eq t ht])

private theorem StronglyContinuousSemigroup.intervalIntegrable_orbit
    (S : StronglyContinuousSemigroup X) (x : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u => S.realOperator u x) volume a b := by
  have h_cont : ContinuousOn (fun u => S.realOperator u x) (Set.Ici 0) :=
    fun u hu => S.strongContWithinAt x u hu
  exact (h_cont.mono fun u hu => by
    exact (le_inf ha hb).trans hu.1).intervalIntegrable

private theorem StronglyContinuousSemigroup.local_integral_shift_identity
    (S : StronglyContinuousSemigroup X) (x : X) {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    S.realOperator h (∫ u in (0 : ℝ)..t, S.realOperator u x) -
        ∫ u in (0 : ℝ)..t, S.realOperator u x =
      (∫ u in t..t + h, S.realOperator u x) - ∫ u in (0 : ℝ)..h, S.realOperator u x := by
  set f := fun u => S.realOperator u x
  have hf_zero_t : IntervalIntegrable f volume (0 : ℝ) t :=
    S.intervalIntegrable_orbit x le_rfl ht.le
  have hf_h_th : IntervalIntegrable f volume h (t + h) :=
    S.intervalIntegrable_orbit x hh.le (by linarith)
  have hf_zero_h : IntervalIntegrable f volume (0 : ℝ) h :=
    S.intervalIntegrable_orbit x le_rfl hh.le
  have hf_h_zero : IntervalIntegrable f volume h (0 : ℝ) := hf_zero_h.symm
  have h_push : S.realOperator h (∫ u in (0 : ℝ)..t, f u) = ∫ u in h..t + h, f u := by
    rw [← (S.realOperator h).intervalIntegral_comp_comm hf_zero_t]
    rw [intervalIntegral.integral_congr (g := fun u => f (u + h))]
    · simp [zero_add]
    · intro u hu
      have hu_nonneg : 0 ≤ u := by
        rw [Set.uIcc_of_le ht.le] at hu
        exact hu.1
      have h_semigroup_apply :
          S.realOperator h (S.realOperator u x) = S.realOperator (u + h) x := by
        rw [← ContinuousLinearMap.comp_apply, ← S.semigroup h u hh.le hu_nonneg, add_comm]
      simpa [f] using h_semigroup_apply
  have h_sub :
      (∫ u in h..t + h, f u) - ∫ u in (0 : ℝ)..t, f u =
        (∫ u in t..t + h, f u) - ∫ u in (0 : ℝ)..h, f u := by
    exact intervalIntegral.integral_interval_sub_interval_comm'
      hf_h_th hf_zero_t hf_h_zero
  rw [h_push, h_sub]

private theorem StronglyContinuousSemigroup.tendsto_average_orbit_at
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun h => (1 / h) • ∫ u in t..t + h, S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x)) := by
  set f := fun u => S.realOperator u x
  have h_cont_at : ContinuousAt f t := by
    have h := S.strongContWithinAt x t ht.le
    rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds ht)] at h
  have h_ftc : HasDerivAt (fun u => ∫ z in t..u, f z) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right
      IntervalIntegrable.refl
      ((ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi
        (s := Set.Ioi (0 : ℝ)) (f := f) (by
          intro u hu
          have h := S.strongContWithinAt x u hu.le
          rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds hu)] at h)) t ht)
      h_cont_at
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
    S.tendsto_average_orbit_at x ht
  have h_lim := h_t.sub h_zero
  have h_interval : Filter.Tendsto
      (fun h => (1 / h) • (S.realOperator h y - y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t x - x)) := by
    refine h_lim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [StronglyContinuousSemigroup.local_integral_shift_identity S x ht hh]
    rw [smul_sub]
  simpa [y, intervalIntegral.integral_of_le ht.le] using h_interval

/-- The local orbit integral `∫₀ᵗ S(u)x du` lies in the generator domain `D(A)`
([EN] Lemma II.1.3). -/
theorem StronglyContinuousSemigroup.integral_orbit_mem_domain
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    (∫ u in Set.Ioc 0 t, S.realOperator u x) ∈ S.domain :=
  (S.mem_domain_iff_tendsto _).mpr ⟨_, S.tendsto_quot_integral_orbit x ht⟩

/-- The generator value on the local orbit integral: `A (∫₀ᵗ S(u)x du) = S t x - x`
([EN] Lemma II.1.3). -/
theorem StronglyContinuousSemigroup.generator_integral_orbit
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    S.generator ⟨∫ u in Set.Ioc 0 t, S.realOperator u x, by
      rw [S.generator_domain]
      exact S.integral_orbit_mem_domain x ht⟩
      = S.realOperator t x - x :=
  S.generator_eq_of_tendsto (S.integral_orbit_mem_domain x ht)
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
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact S.domain.smul_mem (1 / t) (S.integral_orbit_mem_domain x ht)

end TauCeti.Semigroups

end
