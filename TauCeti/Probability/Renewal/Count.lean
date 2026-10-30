/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Natural-valued renewal counts

`renewalCountNat T t` is the number of positive-index arrivals by time `t` on paths whose
arrival times tend to infinity. On every other path it is zero at all times. Using one
exceptional event for the whole path preserves monotonicity and right continuity everywhere.
Zero increments are allowed, so genuine arrivals at zero are retained.

On a nonexplosive path the natural count agrees with the extended count `renewalCount` and
satisfies the inverse relations with `arrival`. In particular it can be used as an arrival
index when defining the excess waiting time. For nondegenerate i.i.d. increments the two
counts agree almost surely, simultaneously at all times. Whenever nonexplosion holds almost
surely, any other natural-valued version agreeing on the nonexplosion event has the same
process law. The process law also transfers to the canonical product realization of the increments.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0)

open scoped Classical in
/-- The natural-valued renewal count, equal to the extended count on nonexplosive paths
and zero at every time on explosive paths. The artificial arrival at index zero is omitted. -/
def renewalCountNat (t : ℝ≥0) (ω : Ω) : ℕ :=
  if Tendsto (fun n ↦ arrival T n ω) atTop atTop then ⌊(renewalCount T t ω).toReal⌋₊ else 0

open scoped Classical in
lemma renewalCountNat_def (t : ℝ≥0) (ω : Ω) :
    renewalCountNat T t ω =
      if Tendsto (fun n ↦ arrival T n ω) atTop atTop then
        ⌊(renewalCount T t ω).toReal⌋₊ else 0 := (rfl)

/-- The exceptional value is zero for the entire explosive path. -/
@[simp]
lemma renewalCountNat_eq_zero_of_not_tendsto {ω : Ω}
    (hω : ¬ Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    renewalCountNat T t ω = 0 := by
  simp [renewalCountNat_def, hω]

variable {T}

/-- On a nonexplosive path the natural count is exactly the extended count. -/
@[simp]
lemma natCast_renewalCountNat {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    (renewalCountNat T t ω : ℝ≥0∞) = renewalCount T t ω := by
  obtain ⟨n, hn⟩ := exists_renewalCount_eq_natCast
    ((tendsto_arrival_atTop_iff.1 hω t).ne)
  simp [renewalCountNat_def, hω, hn]

/-- The natural count reaches `n` exactly when the `n`-th arrival has occurred. -/
lemma le_renewalCountNat_iff {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) {t : ℝ≥0} {n : ℕ} :
    n ≤ renewalCountNat T t ω ↔ arrival T n ω ≤ t := by
  rw [← Nat.cast_le (α := ℝ≥0∞), natCast_renewalCountNat hω]
  exact natCast_le_renewalCount_iff

/-- On a nonexplosive path the number of arrivals tends to infinity with time. -/
lemma tendsto_renewalCountNat_atTop {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) :
    Tendsto (fun t ↦ renewalCountNat T t ω) atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [eventually_ge_atTop (arrival T n ω)] with t ht
  exact (le_renewalCountNat_iff hω).2 ht

/-- The count equals `n` exactly between the `n`-th and `(n + 1)`-st arrivals,
including the left endpoint and excluding the right endpoint. -/
lemma renewalCountNat_eq_iff {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) {t : ℝ≥0} {n : ℕ} :
    renewalCountNat T t ω = n ↔ arrival T n ω ≤ t ∧ t < arrival T (n + 1) ω := by
  rw [← Nat.cast_inj (R := ℝ≥0∞), natCast_renewalCountNat hω]
  exact renewalCount_eq_natCast_iff

/-- The arrival indexed by the count has already occurred. -/
lemma arrival_renewalCountNat_le {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    arrival T (renewalCountNat T t ω) ω ≤ t :=
  (renewalCountNat_eq_iff hω |>.1 rfl).1

/-- The arrival immediately after the count is strictly in the future. -/
lemma lt_arrival_renewalCountNat_succ {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    t < arrival T (renewalCountNat T t ω + 1) ω :=
  (renewalCountNat_eq_iff hω |>.1 rfl).2

variable (T)

/-- The natural count is nondecreasing, including on explosive paths. -/
lemma monotone_renewalCountNat (ω : Ω) : Monotone fun t ↦ renewalCountNat T t ω := by
  by_cases hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop
  · intro s t hst
    rw [le_renewalCountNat_iff hω]
    exact (arrival_renewalCountNat_le hω s).trans hst
  · simp only [renewalCountNat_eq_zero_of_not_tendsto T hω]
    exact monotone_const

/-- The natural count is locally constant to the right, even on the exceptional event. -/
lemma eventually_renewalCountNat_eq_nhdsGE (t : ℝ≥0) (ω : Ω) :
    ∀ᶠ s in 𝓝[≥] t, renewalCountNat T s ω = renewalCountNat T t ω := by
  filter_upwards [eventually_renewalCount_eq_nhdsGE (T := T) t ω] with s hs
  simp [renewalCountNat_def, hs]

/-- Every natural-count path is right-continuous. -/
lemma continuousWithinAt_renewalCountNat_Ici (t : ℝ≥0) (ω : Ω) :
    ContinuousWithinAt (fun s ↦ renewalCountNat T s ω) (Ici t) t :=
  tendsto_const_nhds.congr' <|
    (eventually_renewalCountNat_eq_nhdsGE T t ω).mono fun _ hs ↦ hs.symm

/-- Forming the count commutes with a change of sample space. -/
@[simp]
lemma renewalCountNat_comp {Ω' : Type*} (f : Ω' → Ω) (t : ℝ≥0) (ω : Ω') :
    renewalCountNat (fun n ω ↦ T n (f ω)) t ω = renewalCountNat T t (f ω) := by
  classical
  simp only [renewalCountNat_def, renewalCount_def, arrival_def]

variable {T} [MeasurableSpace Ω]

/-- The natural-valued count is measurable. -/
@[fun_prop]
lemma measurable_renewalCountNat (hT : ∀ n, Measurable (T n)) (t : ℝ≥0) :
    Measurable (renewalCountNat T t) := by
  simp only [funext (renewalCountNat_def T t)]
  exact Measurable.ite (measurableSet_tendsto atTop (measurable_arrival hT))
    (measurable_renewalCount hT t).ennreal_toReal.nat_floor measurable_const

variable {P : Measure Ω}

/-- For nondegenerate i.i.d. increments, the natural and extended counts agree almost surely
on one event for all times. -/
theorem ae_natCast_renewalCountNat (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, ∀ t, (renewalCountNat T t ω : ℝ≥0∞) = renewalCount T t ω := by
  filter_upwards [ae_tendsto_arrival_atTop hT hindep hid hzero] with ω hω
  exact natCast_renewalCountNat hω

/-- Changing the natural-valued count on explosive paths does not change its process law
when nonexplosion holds almost surely. This equality of pushforwards needs no measurability
assumption on the chosen version. -/
theorem map_renewalCountNat_eq_of_nonexplosion
    (hP : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ ω, Tendsto (fun n ↦ arrival T n ω) atTop atTop →
      ∀ t, (N t ω : ℝ≥0∞) = renewalCount T t ω) :
    P.map (fun ω t ↦ renewalCountNat T t ω) = P.map (fun ω t ↦ N t ω) := by
  apply Measure.map_congr
  filter_upwards [hP] with ω hω
  funext t
  exact_mod_cast (natCast_renewalCountNat hω t).trans (hN ω hω t).symm

/-- The entire natural-count process has the same law in any i.i.d. realization as on the
canonical product space. This includes its exceptional-path convention and all finite-time
joint distributions. -/
theorem map_renewalCountNat_eq_infinitePi_map (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    P.map (fun ω t ↦ renewalCountNat T t ω) =
      (Measure.infinitePi fun _ : ℕ ↦ P.map (T 0)).map
        (fun (w : ℕ → ℝ≥0) t ↦ renewalCountNat (fun n w ↦ w n) t w) := by
  have hcomp : (fun ω t ↦ renewalCountNat T t ω) =
      (fun (w : ℕ → ℝ≥0) t ↦ renewalCountNat (fun n w ↦ w n) t w) ∘
        (fun ω n ↦ T n ω) := by
    funext ω t
    exact renewalCountNat_comp (fun n w ↦ w n) (fun ω n ↦ T n ω) t ω
  rw [hcomp, ← Measure.map_map
    (measurable_pi_iff.2 fun t ↦ measurable_renewalCountNat (fun n ↦ measurable_pi_apply n) t)
    (measurable_pi_iff.2 hT), hindep.map_fun_eq_infinitePi_map hT]
  simp_rw [fun n ↦ (hid n).map_eq]

end TauCeti.Probability
