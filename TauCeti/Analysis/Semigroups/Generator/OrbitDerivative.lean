/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Invariance
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiability of semigroup orbits

This file characterizes membership in the infinitesimal generator domain by right
differentiability of the orbit at zero. For a vector in the generator domain, it then computes
the right derivative at every nonnegative time in the equivalent forms `A (S t x)` and
`S t (A x)`.

## References

The argument follows Engel--Nagel, *One-Parameter Semigroups for Linear Evolution
Equations*, Lemma II.1.3(ii).
-/

public section

noncomputable section

open scoped Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace StronglyContinuousSemigroup


/-- At time zero, the right derivative of the orbit of a generator-domain vector is its
generator. -/
theorem realOperator_hasDerivWithinAt_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s (x : X))
      (S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  unfold slope
  simpa [S.realOperator_zero_apply] using S.generator_tendsto x

/-- The orbit of a generator-domain vector is right-differentiable at time zero. -/
theorem realOperator_differentiableWithinAt_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    DifferentiableWithinAt ℝ (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici 0) 0 :=
  (S.realOperator_hasDerivWithinAt_zero x).differentiableWithinAt

/-- The right derivative at zero of the orbit of a generator-domain vector is its generator. -/
@[simp]
theorem realOperator_derivWithin_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    derivWithin (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici 0) 0 =
      S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩ :=
  (S.realOperator_hasDerivWithinAt_zero x).derivWithin (uniqueDiffWithinAt_Ici 0)

/-- The orbit has right derivative `y` at zero exactly when its initial vector belongs to the
generator domain and the generator value is `y`. -/
theorem realOperator_hasDerivWithinAt_zero_iff (S : StronglyContinuousSemigroup X)
    (x y : X) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s x) y (Set.Ici 0) 0 ↔
      ∃ hx : x ∈ S.domain,
        S.generator ⟨x, by rw [S.generator_domain]; exact hx⟩ = y := by
  constructor
  · intro h
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    unfold slope at h
    have ht : Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
      simpa [S.realOperator_zero_apply] using h
    have hx : x ∈ S.domain := (S.mem_domain_iff_tendsto x).2 ⟨y, ht⟩
    exact ⟨hx, S.generator_eq_of_tendsto hx ht⟩
  · rintro ⟨hx, hxy⟩
    rw [← hxy]
    exact S.realOperator_hasDerivWithinAt_zero ⟨x, hx⟩

/-- A vector belongs to the generator domain exactly when its orbit is right-differentiable
at time zero. -/
theorem mem_domain_iff_differentiableWithinAt_realOperator_zero
    (S : StronglyContinuousSemigroup X) (x : X) :
    x ∈ S.domain ↔
      DifferentiableWithinAt ℝ (fun s : ℝ => S.realOperator s x) (Set.Ici 0) 0 := by
  constructor
  · intro hx
    exact S.realOperator_differentiableWithinAt_zero ⟨x, hx⟩
  · intro hx
    obtain ⟨y, hy⟩ := hx
    have hy' := hy.hasDerivWithinAt
    refine (S.mem_domain_iff_tendsto x).2 ⟨y 1, ?_⟩
    rw [hasDerivWithinAt_iff_tendsto_slope] at hy'
    unfold slope at hy'
    simpa [S.realOperator_zero_apply] using hy'

/-! ## Right derivatives at nonnegative times -/

/-- At every nonnegative time, if the evolved vector belongs to the generator domain, then the
right derivative of the orbit is the generator evaluated on that evolved vector. -/
theorem realOperator_hasDerivWithinAt (S : StronglyContinuousSemigroup X)
    {x : X} {t : ℝ} (ht : 0 ≤ t) (hxt : S.realOperator t x ∈ S.domain) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s x)
      (S.generator ⟨S.realOperator t x, by rw [S.generator_domain]; exact hxt⟩)
      (Set.Ici t) t := by
  let y : S.domain := ⟨S.realOperator t x, hxt⟩
  have htranslate : HasDerivWithinAt (fun s : ℝ => S.realOperator (s - t) (y : X))
      (S.generator ⟨y, by rw [S.generator_domain]; exact y.property⟩) (Set.Ici t) t := by
    have hinner : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Set.Ici t) t := by
      simpa using (hasDerivWithinAt_id t (Set.Ici t)).sub_const t
    have hmaps : Set.MapsTo (fun s : ℝ => s - t) (Set.Ici t) (Set.Ici 0) := by
      intro s hs
      simpa only [Set.mem_Ici, sub_nonneg] using hs
    have hcomp :=
      (S.realOperator_hasDerivWithinAt_zero y).scomp_of_eq t hinner hmaps (by ring)
    exact (hcomp.congr (fun _ _ => rfl) rfl).congr_deriv (one_smul ℝ _)
  refine htranslate.congr (fun s hs => ?_) ?_
  · have hst : 0 ≤ s - t := sub_nonneg.mpr hs
    calc
      S.realOperator s x = S.realOperator ((s - t) + t) x := by ring_nf
      _ = S.realOperator (s - t) (S.realOperator t x) := by
        rw [S.realOperator_add _ _ hst ht]
        rfl
      _ = S.realOperator (s - t) y := rfl
  · simp only [sub_self, S.realOperator_zero_apply, y]

/-- At every nonnegative time, the right derivative of the orbit is the semigroup operator
applied to the generator. -/
theorem realOperator_hasDerivWithinAt_map_generator
    (S : StronglyContinuousSemigroup X) (x : S.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s (x : X))
      (S.realOperator t (S.generator ⟨x, by
        rw [S.generator_domain]
        exact x.property⟩)) (Set.Ici t) t := by
  rw [← S.realOperator_generator_map ht x]
  exact S.realOperator_hasDerivWithinAt ht (S.realOperator_mem_domain ht x.property)

/-- On the nonnegative half-line, the orbit of a generator-domain vector has derivative equal
to the generator evaluated on the evolved vector. At positive times this is a two-sided
derivative; only the derivative at zero is one-sided. -/
theorem realOperator_hasDerivWithinAt_Ici (S : StronglyContinuousSemigroup X)
    [CompleteSpace X] (x : S.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s (x : X))
      (S.generator ⟨S.realOperator t x, by
        rw [S.generator_domain]
        exact S.realOperator_mem_domain ht x.property⟩) (Set.Ici 0) t := by
  let z : X := S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩
  let g : ℝ → X := fun s => (x : X) + ∫ u in (0 : ℝ)..s, S.realOperator u z
  have hzmeas : StronglyMeasurableAtFilter (fun u : ℝ => S.realOperator u z)
      (nhdsWithin t (Set.Ici 0)) MeasureTheory.volume := by
    have hae : MeasureTheory.AEStronglyMeasurable (fun u : ℝ => S.realOperator u z)
        (MeasureTheory.volume.restrict (Set.Ici 0)) :=
      (S.realOperator_continuousOn_Ici z).aestronglyMeasurable measurableSet_Ici
    exact AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hae
      self_mem_nhdsWithin
  have horbit : ∀ s : ℝ, 0 ≤ s → S.realOperator s (x : X) = g s := by
    intro s hs
    let b := s + 1
    have hb : 0 < b := by dsimp [b]; linarith
    have hzcont : ContinuousOn (fun u : ℝ => S.realOperator u z) (Set.Icc 0 b) :=
      (S.realOperator_continuousOn_Ici z).mono Set.Icc_subset_Ici_self
    have hzint : IntervalIntegrable (fun u : ℝ => S.realOperator u z) MeasureTheory.volume 0 b :=
      (by simpa [Set.uIcc_of_le hb.le] using hzcont :
        ContinuousOn (fun u : ℝ => S.realOperator u z) (Set.uIcc 0 b)).intervalIntegrable
    apply eq_of_has_deriv_right_eq
        (f := fun u : ℝ => S.realOperator u (x : X))
        (g := g) (f' := fun u => S.realOperator u z) (a := 0) (b := b)
    · intro u hu
      simpa [z] using S.realOperator_hasDerivWithinAt_map_generator x hu.1
    · intro u hu
      have hcont := S.realOperator_continuousWithinAt z u hu.1
      have hmeas : StronglyMeasurableAtFilter (fun v : ℝ => S.realOperator v z)
          (nhdsWithin u (Set.Ioi u)) MeasureTheory.volume := by
        have hae : MeasureTheory.AEStronglyMeasurable (fun v : ℝ => S.realOperator v z)
            (MeasureTheory.volume.restrict (Set.Ioi u)) :=
          ((S.realOperator_continuousOn_Ici z).mono (by
            intro v hv
            exact hu.1.trans hv.le)).aestronglyMeasurable measurableSet_Ioi
        exact AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hae
          self_mem_nhdsWithin
      have huit : IntervalIntegrable (fun v : ℝ => S.realOperator v z)
          MeasureTheory.volume 0 u := by
        apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le hu.1] using
          (S.realOperator_continuousOn_Ici z).mono (by
            intro v hv
            exact hv.1)
      have hint := intervalIntegral.integral_hasDerivWithinAt_right
        (s := Set.Ici u) (t := Set.Ioi u)
        huit hmeas (hcont.mono (by intro v hv; exact hu.1.trans hv.le))
      change HasDerivWithinAt (fun s => (x : X) + ∫ v in (0 : ℝ)..s,
        S.realOperator v z) (S.realOperator u z) (Set.Ici u) u
      have h := (hasDerivWithinAt_const u (Set.Ici u) (x : X)).add hint
      exact h.congr (fun _ _ => rfl) rfl |>.congr_deriv (zero_add _)
    · exact (S.realOperator_continuousOn_Ici x).mono Set.Icc_subset_Ici_self
    · intro u hu
      exact continuousWithinAt_const.add
        (intervalIntegral.continuousWithinAt_primitive
          (MeasureTheory.NullSingletonClass.measure_singleton u)
          (by simpa [max_eq_right hb.le] using hzint))
    · simp [g]
    · exact ⟨hs, by dsimp [b]; linarith⟩
  have hg : HasDerivWithinAt g (S.realOperator t z) (Set.Ici 0) t := by
    have hzint : IntervalIntegrable (fun u : ℝ => S.realOperator u z)
        MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le ht] using
        (S.realOperator_continuousOn_Ici z).mono (by
          intro u hu
          exact hu.1)
    rcases ht.eq_or_lt with rfl | ht
    · have hcont := S.realOperator_continuousWithinAt z 0 le_rfl
      have hmeas : StronglyMeasurableAtFilter (fun v : ℝ => S.realOperator v z)
          (nhdsWithin 0 (Set.Ioi 0)) MeasureTheory.volume := by
        have hae : MeasureTheory.AEStronglyMeasurable (fun v : ℝ => S.realOperator v z)
            (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
          ((S.realOperator_continuousOn_Ici z).mono Set.Ioi_subset_Ici_self)
            |>.aestronglyMeasurable measurableSet_Ioi
        exact AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hae
          self_mem_nhdsWithin
      have hint := intervalIntegral.integral_hasDerivWithinAt_right
        (s := Set.Ici 0) (t := Set.Ioi 0) hzint hmeas
        (hcont.mono Set.Ioi_subset_Ici_self)
      simp only [S.realOperator_zero_apply] at hint
      rw [S.realOperator_zero_apply]
      change HasDerivWithinAt (fun s => (x : X) + ∫ v in (0 : ℝ)..s,
        S.realOperator v z) z (Set.Ici 0) 0
      have h := (hasDerivWithinAt_const 0 (Set.Ici 0) (x : X)).add hint
      exact h.congr (fun _ _ => rfl) rfl |>.congr_deriv (zero_add _)
    · have hcont := S.realOperator_continuousAt_of_pos z ht
      have hmeas := ContinuousOn.stronglyMeasurableAtFilter (μ := MeasureTheory.volume)
        isOpen_Ioi ((S.realOperator_continuousOn_Ici z).mono Set.Ioi_subset_Ici_self) t ht
      have hint := intervalIntegral.integral_hasDerivAt_right hzint
        hmeas hcont
      change HasDerivWithinAt (fun s => (x : X) + ∫ v in (0 : ℝ)..s,
        S.realOperator v z) (S.realOperator t z) (Set.Ici 0) t
      have h := ((hasDerivAt_const t (x : X)).add hint).hasDerivWithinAt
        (s := Set.Ici 0)
      exact h.congr (fun _ _ => rfl) rfl |>.congr_deriv (zero_add _)
  rw [S.realOperator_generator_map ht x]
  exact hg.congr (fun s hs => horbit s hs) (horbit t ht)

/-- The orbit of a generator-domain vector is right-differentiable at every nonnegative time. -/
theorem realOperator_differentiableWithinAt (S : StronglyContinuousSemigroup X)
    (x : S.domain) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableWithinAt ℝ (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici t) t :=
  (S.realOperator_hasDerivWithinAt ht
    (S.realOperator_mem_domain ht x.property)).differentiableWithinAt

/-- The right derivative of an orbit at a nonnegative time is the generator evaluated on the
evolved vector, provided that vector belongs to the generator domain. -/
theorem realOperator_derivWithin (S : StronglyContinuousSemigroup X)
    {x : X} {t : ℝ} (ht : 0 ≤ t) (hxt : S.realOperator t x ∈ S.domain) :
    derivWithin (fun s : ℝ => S.realOperator s x) (Set.Ici t) t =
      S.generator ⟨S.realOperator t x, by rw [S.generator_domain]; exact hxt⟩ :=
  (S.realOperator_hasDerivWithinAt ht hxt).derivWithin (uniqueDiffWithinAt_Ici t)

/-- The right derivative of the orbit at a nonnegative time is the semigroup operator applied
to the generator. -/
theorem realOperator_derivWithin_map_generator (S : StronglyContinuousSemigroup X)
    (x : S.domain) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici t) t =
      S.realOperator t (S.generator ⟨x, by
        rw [S.generator_domain]
        exact x.property⟩) :=
  (S.realOperator_hasDerivWithinAt_map_generator x ht).derivWithin
    (uniqueDiffWithinAt_Ici t)

end StronglyContinuousSemigroup

end TauCeti.Semigroups
