/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Missingness at random

One full observation of a missing-data problem is a triple `w = (r, x, y) : Bool × X × ℝ`: a
covariate `x`, a real response `y`, and an indicator `r`, equal to `true` when the response is
observed. The observed part of `w` is `observe w = (r, x, if r then y else 0)`; the indicator is
kept, so the placeholder `0` of a missing response is never confused with an observed `0`.

A law `Q` of full observations is missing at random with propensity `π : X → ℝ` when `π` is
measurable with values in `[0, 1]` and `Q(R = 1, (X, Y) ∈ A) = ∫_{(X, Y) ∈ A} π(X) dQ` for every
measurable set `A` of covariate–response pairs (Little–Rubin, (6.51), p. 134, in set-function
form): the probability of observing the response depends on the covariate only.

## Main definitions

* `TauCeti.observe`: the observed part `(R, X, R Y)` of a full observation.
* `TauCeti.IsMissingAtRandom Q π`: `Q` is missing at random with propensity `π`.

## Main results

* `TauCeti.measurable_observe`: `observe` is measurable.
* `TauCeti.isMissingAtRandom_iff`: the defining conditions of missingness at random.
* `TauCeti.IsMissingAtRandom.integral_ite_eq`: under missingness at random,
  `E[1{R = 1} g(X, Y)] = E[π(X) g(X, Y)]`.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley, 2019.

The transfer lemma `IsMissingAtRandom.integral_ite_eq` is adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Asymptotics/CrossFitting/FoldBounds.lean`
(`integral_ite_observed_eq`, there stated on rectangles).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

variable {X : Type*}

/-- The observed part `(R, X, R Y)` of a full observation `(R, X, Y)`: the response is replaced
by the placeholder `0` when it is missing. -/
def observe (w : Bool × X × ℝ) : Bool × X × ℝ :=
  (w.1, w.2.1, if w.1 then w.2.2 else 0)

/-- The defining formula of `observe`. -/
theorem observe_def (w : Bool × X × ℝ) : observe w = (w.1, w.2.1, if w.1 then w.2.2 else 0) := by
  rw [observe]

/-- An observed response is kept. -/
@[simp]
theorem observe_true (x : X) (y : ℝ) : observe (true, x, y) = (true, x, y) := by
  simp [observe_def]

/-- A missing response is replaced by the placeholder `0`. -/
@[simp]
theorem observe_false (x : X) (y : ℝ) : observe (false, x, y) = (false, x, 0) := by
  simp [observe_def]

variable [MeasurableSpace X]

/-- The observed part of a full observation is a measurable function of it. -/
@[fun_prop]
theorem measurable_observe : Measurable (observe : Bool × X × ℝ → Bool × X × ℝ) := by
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (Measurable.ite hS (measurable_snd.comp measurable_snd) measurable_const))

/-- Missingness at random with propensity `π`, in set-function form: `π` is measurable with
values in `[0, 1]`, and for every measurable set `A` of covariate–response pairs,
`Q(R = 1, (X, Y) ∈ A) = ∫_{(X, Y) ∈ A} π(X) dQ`. -/
def IsMissingAtRandom (Q : Measure (Bool × X × ℝ)) (π : X → ℝ) : Prop :=
  Measurable π ∧ (∀ x, π x ∈ Icc 0 1) ∧ ∀ A : Set (X × ℝ), MeasurableSet A →
    Q.real {w | w.1 = true ∧ w.2 ∈ A} = ∫ w in {w | w.2 ∈ A}, π w.2.1 ∂Q

/-- The defining conditions of missingness at random with propensity `π`. -/
theorem isMissingAtRandom_iff {Q : Measure (Bool × X × ℝ)} {π : X → ℝ} :
    IsMissingAtRandom Q π ↔ Measurable π ∧ (∀ x, π x ∈ Icc 0 1) ∧
      ∀ A : Set (X × ℝ), MeasurableSet A →
        Q.real {w | w.1 = true ∧ w.2 ∈ A} = ∫ w in {w | w.2 ∈ A}, π w.2.1 ∂Q :=
  Iff.rfl

namespace IsMissingAtRandom

variable {Q : Measure (Bool × X × ℝ)} {π : X → ℝ}

/-- Missingness at random from its defining conditions. -/
theorem of_measureReal_eq (hπ : Measurable π) (hπ01 : ∀ x, π x ∈ Icc 0 1)
    (hA : ∀ A : Set (X × ℝ), MeasurableSet A →
      Q.real {w | w.1 = true ∧ w.2 ∈ A} = ∫ w in {w | w.2 ∈ A}, π w.2.1 ∂Q) :
    IsMissingAtRandom Q π :=
  ⟨hπ, hπ01, hA⟩

/-- The propensity of missingness at random is measurable. -/
theorem measurable (h : IsMissingAtRandom Q π) : Measurable π := h.1

/-- The propensity of missingness at random is nonnegative. -/
theorem nonneg (h : IsMissingAtRandom Q π) (x : X) : 0 ≤ π x := (h.2.1 x).1

/-- The propensity of missingness at random is at most `1`. -/
theorem le_one (h : IsMissingAtRandom Q π) (x : X) : π x ≤ 1 := (h.2.1 x).2

/-- The defining identity of missingness at random:
`Q(R = 1, (X, Y) ∈ A) = ∫_{(X, Y) ∈ A} π(X) dQ` for every measurable `A`. -/
theorem measureReal_eq (h : IsMissingAtRandom Q π) {A : Set (X × ℝ)} (hA : MeasurableSet A) :
    Q.real {w | w.1 = true ∧ w.2 ∈ A} = ∫ w in {w | w.2 ∈ A}, π w.2.1 ∂Q :=
  h.2.2 A hA

/-- **Transfer from the observed event to the propensity.** Under missingness at random,
`E[1{R = 1} g(X, Y)] = E[π(X) g(X, Y)]` for every measurable `g` for which the left side is
integrable. -/
theorem integral_ite_eq [IsFiniteMeasure Q] (h : IsMissingAtRandom Q π) {g : X × ℝ → ℝ}
    (hg : Measurable g) (hgi : Integrable (fun w ↦ if w.1 then g w.2 else 0) Q) :
    ∫ w, (if w.1 then g w.2 else 0) ∂Q = ∫ w, π w.2.1 * g w.2 ∂Q := by
  set S : Set (Bool × X × ℝ) := {w | w.1 = true} with hSdef
  have hS : MeasurableSet S := measurable_fst (measurableSet_singleton true)
  have hsnd : Measurable[MeasurableSpace.comap (fun w : Bool × X × ℝ ↦ w.2) inferInstance]
      fun w : Bool × X × ℝ ↦ w.2 := comap_measurable _
  have hite : ∀ w : Bool × X × ℝ,
      (if w.1 then g w.2 else 0) = g w.2 * S.indicator (fun _ ↦ (1 : ℝ)) w := by
    intro w; by_cases hw : w.1 = true <;> simp [hSdef, hw]
  have hπi : Integrable (fun w : Bool × X × ℝ ↦ π w.2.1) Q :=
    (integrable_const (1 : ℝ)).mono' (h.measurable.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun w ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg _)]; exact h.le_one _)
  simp_rw [hite]
  have key := MeasureTheory.integral_mul_eq_of_forall_setIntegral_eq (μ := Q)
    (measurable_snd.comap_le) (f := S.indicator fun _ ↦ (1 : ℝ))
    (g := fun w ↦ π w.2.1) (h := fun w ↦ g w.2) ((integrable_const 1).indicator hS) hπi
    ((h.measurable.comp measurable_fst).comp hsnd).stronglyMeasurable ?_
    (hg.comp hsnd).stronglyMeasurable (by simpa only [hite] using hgi)
  · rw [key]; simp_rw [mul_comm]
  · rintro _ ⟨A, hA, rfl⟩
    -- The event `{(X, Y) ∈ A} ∩ {R = 1}` is the event of the defining identity.
    have hset : Prod.snd ⁻¹' A ∩ S = {w | w.1 = true ∧ w.2 ∈ A} := by
      ext
      simp [hSdef, and_comm]
    rw [setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one, hset]
    exact (h.measureReal_eq hA).symm

end IsMissingAtRandom

end TauCeti
