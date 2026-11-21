/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
public import TauCeti.NumberTheory.Equidistribution.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.List.TFAE
import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Analysis.SpecificLimits.Cesaro
import TauCeti.MeasureTheory.Measure.AddCircle
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier

/-!
# Weyl's equidistribution criteria on circles and tori

This file develops Fourier-analytic equidistribution criteria on additive circles `AddCircle T`
and finite-dimensional unit tori `UnitAddTorus d`:

* `TauCeti.TorusIrrational`: a torus point `α : UnitAddTorus d` is irrational if no nonzero integer
  frequency vector `k : d → ℤ` annihilates it (`∑ i, k i • α i ≠ 0`), equivalently
  `UnitAddTorus.mFourier k α ≠ 1` for all `k ≠ 0` (`TauCeti.torusIrrational_iff_mFourier`).
* `TauCeti.asympEquidistributed_addCircle_iff`, `TauCeti.weyl_criterion_addCircle`,
  `TauCeti.asympEquidistributed_unitAddTorus_iff`, and `TauCeti.weyl_criterion`: Weyl's criterion
  characterizing asymptotic equidistribution for an arbitrary probability measure or Haar measure
  in terms of character averages.
* `TauCeti.asympEquidistributed_unitAddTorus_iff_forall_linear_comb`: a sequence in `UnitAddTorus d`
  is equidistributed for Haar measure iff every nonzero integer linear combination of its
  coordinates is equidistributed on `UnitAddCircle`.
* `TauCeti.totallyAsympEquidistributed_unitAddTorus_iff_rational_twist`: total equidistribution on
  `UnitAddTorus d` is equivalent to vanishing of all rationally twisted Weyl sums.
* `TauCeti.uniformDistribution_mod_one_tfae`: equivalence of Haar equidistribution on
  `UnitAddCircle`, convergence of fractional-part interval frequencies, and Weyl's exponential-sum
  criterion for a real sequence.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Proposition 1.1.2, Corollary 1.1.3, Exercises 1.1.1 and 1.1.4).
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace TauCeti

section Helpers

/-- Integrating a continuous complex function against the empirical probability measure produces
its successor-indexed Cesàro average. -/
private theorem integral_empiricalMeasure_complex {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (x : ℕ → X) (f : C(X, ℂ)) (n : ℕ) :
    ∫ y, f y ∂(TauCeti.Probability.empiricalMeasure x n : Measure X) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), f (x i) := by
  rw [TauCeti.Probability.integral_empiricalMeasure f.continuous.stronglyMeasurable,
    Complex.real_smul]
  simp

/-- The fundamental character on `UnitAddCircle` evaluates to `1` only at `0`. -/
private theorem fourier_one_eq_one_iff (y : UnitAddCircle) :
    fourier 1 y = 1 ↔ y = 0 := by
  rw [fourier_one]
  constructor
  · intro h
    have hcircle : AddCircle.toCircle y = AddCircle.toCircle (0 : UnitAddCircle) := by
      apply Subtype.ext
      simpa using h
    exact AddCircle.injective_toCircle one_ne_zero hcircle
  · rintro rfl
    simp

/-- Evaluating `fourier a` at `(i / b : ℝ)` on `UnitAddCircle` coincides with the standard additive
character on `ZMod b`. -/
private theorem fourier_natCast_div_eq_stdAddChar {b : ℕ} [NeZero b] (a : ℤ) (i : ℕ) :
    fourier a (((i : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((i : ZMod b) * (a : ZMod b)) := by
  have hdiv : ((i : ℝ) / (b : ℝ) : UnitAddCircle) =
      ((((i : ZMod b).val : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle) := by
    rw [ZMod.val_natCast]
    have hsplit : (i : ℝ) / (b : ℝ) = ((i / b : ℕ) : ℝ) + ((i % b : ℕ) : ℝ) / (b : ℝ) := by
      have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne b)
      have hdm : (i : ℝ) = (b : ℝ) * ((i / b : ℕ) : ℝ) + ((i % b : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod i b).symm
      rw [hdm, add_div, mul_div_cancel_left₀ _ hb]
    have hnat0 : (((i / b : ℕ) : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨((i / b : ℕ) : ℤ), by rw [zsmul_eq_mul, mul_one, Int.cast_natCast]⟩
    rw [hsplit, AddCircle.coe_add, hnat0, zero_add]
  rw [hdiv, ZMod.fourier_val_div_eq_stdAddChar]

end Helpers

section TorusIrrational

variable {d : Type*} [Fintype d]

/-- A point `α : UnitAddTorus d` is irrational if no nonzero integer frequency vector annihilates
it under the pairing `k ↦ ∑ i, k i • α i`. -/
def TorusIrrational (α : UnitAddTorus d) : Prop :=
  ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0

/-- Unfolding characterization of `TorusIrrational`. -/
theorem torusIrrational_def {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0 :=
  Iff.rfl

/-- A torus point `α` is irrational iff every nontrivial Fourier character takes a value other
than `1` at `α`. -/
theorem torusIrrational_iff_mFourier {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → UnitAddTorus.mFourier k α ≠ 1 := by
  refine forall₂_congr fun k _ ↦ ?_
  rw [UnitAddTorus.mFourier_eq_fourier_sum, not_iff_not, fourier_one_eq_one_iff]

/-- On a one-dimensional torus, `TorusIrrational` coincides with having infinite additive order. -/
theorem torusIrrational_unique_iff [Unique d] {α : UnitAddTorus d} :
    TorusIrrational α ↔ addOrderOf (α default) = 0 := by
  rw [torusIrrational_def, addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_nsmul_eq_zero]
  constructor
  · intro h ⟨n, hn, hzero⟩
    refine h (fun _ ↦ (n : ℤ)) ?_ ?_
    · intro hk
      have := congrFun hk default
      exact hn.ne' (Int.ofNat_eq_zero.mp this)
    · simpa [Fintype.sum_unique, natCast_zsmul] using hzero
  · intro h k hk hsum
    have hk0 : k default ≠ 0 := fun h0 ↦ hk (funext fun i ↦ by rw [Unique.eq_default i]; exact h0)
    have hkd : k default • α default = 0 := by simpa [Fintype.sum_unique] using hsum
    refine h ⟨(k default).natAbs, Int.natAbs_pos.mpr hk0, ?_⟩
    rcases Int.natAbs_eq (k default) with heq | heq
    · rwa [← natCast_zsmul, ← heq]
    · have hneg : -(k default) = ((k default).natAbs : ℤ) := by omega
      rw [← natCast_zsmul, ← hneg, neg_zsmul, hkd, neg_zero]

/-- On an empty coordinate type, every torus point is vacuously irrational. -/
theorem torusIrrational_of_isEmpty [IsEmpty d] (α : UnitAddTorus d) :
    TorusIrrational α := fun k hk ↦ (hk (Subsingleton.elim k 0)).elim

/-- Scaling a torus point by a nonzero integer preserves and reflects irrationality. -/
theorem torusIrrational_zsmul_iff {α : UnitAddTorus d} {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  constructor
  · intro h k hk hsum
    refine h k hk ?_
    calc ∑ i, k i • (m • α) i
        = ∑ i, m • (k i • α i) := sum_congr rfl fun i _ ↦ by rw [Pi.smul_apply, zsmul_comm]
      _ = m • ∑ i, k i • α i := smul_sum.symm
      _ = 0 := by rw [hsum, smul_zero]
  · intro h k hk hsum
    have hmk : m • k ≠ 0 := by
      intro h0
      apply hk
      funext i
      have hi := congrFun h0 i
      rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left hm
    refine h (m • k) hmk ?_
    calc ∑ i, (m • k) i • α i
        = ∑ i, k i • (m • α) i := sum_congr rfl fun i _ ↦ by
            rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_zsmul]
      _ = 0 := hsum

/-- A nonzero integer multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.zsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) :=
  (torusIrrational_zsmul_iff hm).mpr hα

/-- Scaling a torus point by a nonzero natural number preserves and reflects irrationality. -/
theorem torusIrrational_nsmul_iff {α : UnitAddTorus d} {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  simpa [natCast_zsmul] using torusIrrational_zsmul_iff (α := α) (m := (m : ℤ))
    (Int.natCast_ne_zero.mpr hm)

/-- A nonzero natural-number multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.nsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) :=
  (torusIrrational_nsmul_iff hm).mpr hα

end TorusIrrational

section WeylCriteria

/-- **Weyl's criterion on `AddCircle T` for an arbitrary limit measure**: a sequence is
asymptotically equidistributed for `μ` iff the Cesàro averages of every integer Fourier character
converge to its `μ`-integral. -/
theorem asympEquidistributed_addCircle_iff {T : ℝ} [Fact (0 < T)] {x : ℕ → AddCircle T}
    {μ : ProbabilityMeasure (AddCircle T)} :
    AsympEquidistributed x μ ↔ ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (x i))
        atTop (𝓝 (∫ y, fourier k y ∂(μ : Measure (AddCircle T)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_fourier_tendsto]
  refine forall_congr' fun k ↦ ?_
  simp_rw [integral_empiricalMeasure_complex x (fourier k)]

/-- **Weyl's criterion on `AddCircle T`**: a sequence is asymptotically equidistributed for Haar
probability iff the Cesàro averages of every nonzero integer Fourier character tend to `0`. -/
theorem weyl_criterion_addCircle {T : ℝ} [Fact (0 < T)] {x : ℕ → AddCircle T} :
    AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure ↔ ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (x i))
        atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_haarAddCircle_iff]
  refine forall₂_congr fun k _ ↦ ?_
  simp_rw [integral_empiricalMeasure_complex x (fourier k)]

variable {d : Type*} [Fintype d]

/-- **Weyl's criterion on `UnitAddTorus d` for an arbitrary limit measure**: a sequence is
asymptotically equidistributed for `μ` iff the Cesàro averages of every multivariate Fourier
character converge to its `μ`-integral. -/
theorem asympEquidistributed_unitAddTorus_iff {x : ℕ → UnitAddTorus d}
    {μ : ProbabilityMeasure (UnitAddTorus d)} :
    AsympEquidistributed x μ ↔ ∀ k : d → ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i))
        atTop (𝓝 (∫ y, UnitAddTorus.mFourier k y ∂(μ : Measure (UnitAddTorus d)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_mFourier_tendsto]
  refine forall_congr' fun k ↦ ?_
  simp_rw [integral_empiricalMeasure_complex x (UnitAddTorus.mFourier k)]

/-- **Weyl's criterion on `UnitAddTorus d`**: a sequence is asymptotically equidistributed for
Haar probability (`volume`) iff the Cesàro averages of every nontrivial Fourier character tend
to `0`. -/
theorem weyl_criterion {x : ℕ → UnitAddTorus d} :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 →
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
            ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i))
          atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_volume_unitAddTorus_iff]
  refine forall₂_congr fun k _ ↦ ?_
  simp_rw [integral_empiricalMeasure_complex x (UnitAddTorus.mFourier k)]

/-- **Equidistribution on `UnitAddTorus d` via one-dimensional projections**: a sequence in
`UnitAddTorus d` is equidistributed for Haar probability iff every nonzero integer linear
combination of its coordinates is equidistributed on `UnitAddCircle`. -/
theorem asympEquidistributed_unitAddTorus_iff_forall_linear_comb {x : ℕ → UnitAddTorus d} :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 →
        AsympEquidistributed (fun n ↦ ∑ i, k i • x n i)
          AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion]
  constructor
  · intro hx k hk
    rw [weyl_criterion_addCircle]
    intro m hm
    have hmk : m • k ≠ 0 := by
      intro h0
      apply hk
      funext i
      have hi := congrFun h0 i
      rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left hm
    simpa only [UnitAddTorus.mFourier_zsmul] using hx (m • k) hmk
  · intro h k hk
    have h1 := (weyl_criterion_addCircle.mp (h k hk)) 1 one_ne_zero
    simpa only [← UnitAddTorus.mFourier_eq_fourier_sum] using h1

/-- Indicator of a residue class modulo `q > 0` expanded as a finite Fourier sum of rational
twists on `ZMod q`. -/
private theorem ite_mod_eq_sum_fourier {q r : ℕ} [NeZero q] (hr : r < q) (i : ℕ) :
    (if i % q = r then (1 : ℂ) else 0) =
      (q : ℂ)⁻¹ * ∑ a : ZMod q,
        ZMod.stdAddChar (-((r : ZMod q) * a)) *
          fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) := by
  let δ : ZMod q → ℂ := Pi.single (r : ZMod q) 1
  have hinv := congrFun (ZMod.dft.symm_apply_apply δ) (i : ZMod q)
  rw [ZMod.invDFT_apply] at hinv
  have hdft (a : ZMod q) : ZMod.dft δ a = ZMod.stdAddChar (-((r : ZMod q) * a)) := by
    rw [ZMod.dft_apply]
    simp [δ, Pi.single_apply]
  simp_rw [hdft] at hinv
  have hlhs : δ (i : ZMod q) = if i % q = r then 1 else 0 := by
    simp only [δ, Pi.single_apply, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  rw [hlhs, smul_eq_mul] at hinv
  rw [← hinv]
  congr 1
  refine sum_congr rfl fun a _ ↦ ?_
  rw [smul_eq_mul, mul_comm, fourier_natCast_div_eq_stdAddChar, Int.cast_natCast,
    ZMod.natCast_zmod_val, mul_comm (a : ZMod q)]

/-- Vanishing of rational twists modulo `q` implies vanishing of the Cesàro average masked to a
residue class `r < q`. -/
private theorem tendsto_cesaro_ite_mod_of_rational_twist {x : ℕ → UnitAddTorus d} {k : d → ℤ}
    {q r : ℕ} [NeZero q] (hr : r < q)
    (h : ∀ a : ℤ, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i) *
          fourier a (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ range (n + 1), if i % q = r then UnitAddTorus.mFourier k (x i) else 0)
      atTop (𝓝 (0 : ℂ)) := by
  have hsum : Tendsto (fun n : ℕ ↦ (q : ℂ)⁻¹ * ∑ a : ZMod q,
      ZMod.stdAddChar (-((r : ZMod q) * a)) *
        (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1),
          UnitAddTorus.mFourier k (x i) *
            fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)))
      atTop (𝓝 ((q : ℂ)⁻¹ * ∑ _a : ZMod q, (0 : ℂ))) :=
    tendsto_const_nhds.mul (tendsto_finsetSum Finset.univ fun a _ ↦ by
      simpa only [mul_zero] using tendsto_const_nhds.mul (h (a.val : ℤ)))
  simp only [sum_const_zero, mul_zero] at hsum
  refine hsum.congr fun n ↦ ?_
  have hterm (i : ℕ) :
      (if i % q = r then UnitAddTorus.mFourier k (x i) else 0) =
        (q : ℂ)⁻¹ * ∑ a : ZMod q,
          ZMod.stdAddChar (-((r : ZMod q) * a)) *
            (UnitAddTorus.mFourier k (x i) *
              fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) := by
    calc (if i % q = r then UnitAddTorus.mFourier k (x i) else 0)
        = (if i % q = r then (1 : ℂ) else 0) * UnitAddTorus.mFourier k (x i) := by
          split_ifs <;> simp
      _ = ((q : ℂ)⁻¹ * ∑ a : ZMod q,
            ZMod.stdAddChar (-((r : ZMod q) * a)) *
              fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) *
            UnitAddTorus.mFourier k (x i) := by rw [ite_mod_eq_sum_fourier hr i]
      _ = (q : ℂ)⁻¹ * ∑ a : ZMod q,
            ZMod.stdAddChar (-((r : ZMod q) * a)) *
              (UnitAddTorus.mFourier k (x i) *
                fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) := by
          rw [mul_assoc, sum_mul]
          congr 1
          exact sum_congr rfl fun a _ ↦ by ring
  simp_rw [hterm, Complex.real_smul, ← mul_sum]
  rw [sum_comm (s := range (n + 1)) (t := (Finset.univ : Finset (ZMod q)))]
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  rw [mul_left_comm ((n + 1 : ℂ)⁻¹) ((q : ℂ)⁻¹)]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← mul_sum, mul_left_comm]

/-- **Total equidistribution by rational twists**: a sequence in `UnitAddTorus d` is totally
equidistributed for Haar probability iff all its rationally twisted Weyl sums vanish in the
limit. -/
theorem totallyAsympEquidistributed_unitAddTorus_iff_rational_twist {x : ℕ → UnitAddTorus d} :
    TotallyAsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∀ b : ℕ, 0 < b → ∀ a : ℤ,
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
            ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i) *
              fourier a (((i : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle))
          atTop (𝓝 0) := by
  rw [totallyAsympEquidistributed_def]
  constructor
  · intro hx k hk b hb a
    have : NeZero b := ⟨hb.ne'⟩
    have hmod : ∀ r < b,
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
            ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x (b * i + r)) *
              fourier a ((((b * i + r : ℕ) : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle))
          atTop (𝓝 (0 : ℂ)) := by
      intro r _
      have hconst (i : ℕ) :
          fourier a ((((b * i + r : ℕ) : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle) =
            ZMod.stdAddChar ((r : ZMod b) * (a : ZMod b)) := by
        rw [fourier_natCast_div_eq_stdAddChar]
        simp
      have hlim := ((weyl_criterion.mp (hx b r hb)) k hk).mul_const
        (ZMod.stdAddChar ((r : ZMod b) * (a : ZMod b)))
      rw [zero_mul] at hlim
      refine hlim.congr fun n ↦ ?_
      simp_rw [hconst, ← sum_mul, Complex.real_smul, Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    have hbdd : ∃ C : ℝ, ∀ i : ℕ,
        ‖UnitAddTorus.mFourier k (x i) *
          fourier a (((i : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle)‖ ≤ C :=
      ⟨1, fun i ↦ by rw [norm_mul, UnitAddTorus.norm_mFourier_apply, norm_fourier_apply, mul_one]⟩
    have htot := tendsto_cesaro_of_forall_mod hb hbdd hmod
    simp only [sum_const_zero, smul_zero] at htot
    exact htot.congr fun n ↦ by simp [Complex.real_smul]
  · intro h q r hq
    have : NeZero q := ⟨hq.ne'⟩
    have heq : (fun n ↦ x (q * (n + r / q) + r % q)) = fun n ↦ x (q * n + r) := by
      funext n
      rw [Nat.mul_add, Nat.add_assoc, Nat.div_add_mod]
    rw [← heq, asympEquidistributed_comp_add_iff (x := fun n ↦ x (q * n + r % q)) (r / q),
      weyl_criterion]
    intro k hk
    have hmask := tendsto_cesaro_ite_mod_of_rational_twist (Nat.mod_lt r hq) (h k hk q hq)
    have hprog := tendsto_cesaro_mul_add_of_ite_mod hq (Nat.mod_lt r hq) hmask
    rw [smul_zero] at hprog
    exact hprog.congr fun n ↦ by simp [Complex.real_smul]

end WeylCriteria

section UniformDistributionModOne

/-- On `UnitAddCircle`, Haar probability coincides with `volume`, and singletons are null. -/
private theorem haarAddCircle_singleton_zero (c : UnitAddCircle) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) {c} = 0 := by
  have hvol : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  rw [hvol]
  have hm : Measurable (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hpre : {c} = (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹'
      {(AddCircle.equivIco 1 0 c : ℝ)} := by
    ext θ
    simp only [mem_singleton_iff, Set.mem_preimage]
    rw [← Subtype.ext_iff, (AddCircle.equivIco 1 0).injective.eq_iff]
  rw [hpre, ← Measure.map_apply hm (measurableSet_singleton _), AddCircle.map_coe_equivIco_volume 0,
    Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left Real.volume_singleton

/-- The frontier of the half-open arc `[a, b)` in `UnitAddCircle` (`0 ≤ a ≤ b ≤ 1`) is contained
in the two-point set `{(a : UnitAddCircle), (b : UnitAddCircle)}`. -/
private theorem frontier_preimage_equivIco_Ico_subset {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    frontier ((fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹' Ico a b) ⊆
      {(a : UnitAddCircle), (b : UnitAddCircle)} := by
  set E : Set UnitAddCircle :=
    (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹' Ico a b
  intro x hx
  by_contra hnot
  obtain ⟨hxa, hxb⟩ := not_or.mp (by simpa [mem_insert_iff, mem_singleton_iff] using hnot)
  set t : ℝ := (AddCircle.equivIco 1 0 x : ℝ)
  have ht0 : 0 ≤ t := (AddCircle.equivIco 1 0 x).2.1
  have ht1 : t < 1 := by simpa using (AddCircle.equivIco 1 0 x).2.2
  have hxt : (t : UnitAddCircle) = x := by simp [t]
  have himg_open (u v : ℝ) : IsOpen (((↑) : ℝ → UnitAddCircle) '' Ioo u v) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hmem01 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) : (y : UnitAddCircle) ∈ E ↔ y ∈ Ico a b := by
    have hy01 : y ∈ Ico (0 : ℝ) (0 + 1) := ⟨hy0, by linarith⟩
    simp only [E, Set.mem_preimage, AddCircle.equivIco_coe_of_mem hy01]
  have hdisj (u v : ℝ) (hxU : x ∈ ((↑) : ℝ → UnitAddCircle) '' Ioo u v)
      (hd : ∀ y ∈ Ioo u v, (y : UnitAddCircle) ∉ E) : False := by
    obtain ⟨_, ⟨y, hy, rfl⟩, hyE⟩ := mem_closure_iff.mp hx.1 _ (himg_open u v) hxU
    exact hd y hy hyE
  by_cases hmem : a < t ∧ t < b
  · refine hx.2 (mem_interior.mpr ⟨_, ?_, himg_open a b, ⟨t, hmem, hxt⟩⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem01 (by linarith [hy.1]) (by linarith [hy.2])).mpr ⟨hy.1.le, hy.2⟩
  · by_cases htlta : t < a
    · by_cases htpos : 0 < t
      · refine hdisj 0 a ⟨t, ⟨htpos, htlta⟩, hxt⟩ fun y hy hyE ↦ ?_
        linarith [hy.2, ((hmem01 hy.1.le (by linarith [hy.2])).mp hyE).1]
      · have ht_eq : t = 0 := le_antisymm (not_lt.mp htpos) ht0
        have hb_lt : b < 1 := lt_of_le_of_ne hb fun hb1 ↦ hxb <| by
          rw [← hxt, ht_eq, hb1]; simpa using (AddCircle.coe_period (1 : ℝ)).symm
        refine hdisj (b - 1) a ⟨0, ⟨by linarith, by linarith⟩, by simpa [ht_eq] using hxt⟩
          fun y hy hyE ↦ ?_
        by_cases hy0 : 0 ≤ y
        · linarith [hy.2, ((hmem01 hy0 (by linarith [hy.2])).mp hyE).1]
        · have hcoe : (y : UnitAddCircle) = ((y + 1 : ℝ) : UnitAddCircle) := by
            rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
          rw [hcoe, hmem01 (by linarith [hy.1]) (by linarith)] at hyE
          linarith [hy.1, hyE.2]
    · have hta : t ≠ a := fun h ↦ hxa (by rw [← hxt, h])
      have hbt : b < t := lt_of_le_of_ne (by
        by_contra hlt
        exact hmem ⟨lt_of_le_of_ne (not_lt.mp htlta) hta.symm, not_le.mp hlt⟩)
        fun h ↦ hxb (by rw [← hxt, h])
      refine hdisj b 1 ⟨t, ⟨hbt, ht1⟩, hxt⟩ fun y hy hyE ↦ ?_
      linarith [hy.1, ((hmem01 (by linarith [hy.1]) hy.2).mp hyE).2]

/-- Sum of a nontrivial `M`-th root of unity over `0, …, M - 1` vanishes when `0 < |k| < M`. -/
private theorem sum_fourier_div_eq_zero {k : ℤ} {M : ℕ} (hk : k ≠ 0) (hM : k.natAbs < M) :
    ∑ j ∈ range M, fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) = 0 := by
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  set ζ : ℂ := fourier k (((1 / (M : ℝ) : ℝ) : UnitAddCircle))
  have hpow (j : ℕ) : fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) = ζ ^ j := by
    simp only [ζ, fourier_coe_apply, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζM : ζ ^ M = 1 := by
    rw [← hpow M, div_self hM0, AddCircle.coe_period, fourier_eval_zero]
  have hζne : ζ ≠ 1 := by
    intro h1
    have hEq : fourier 1 (((k : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) = 1 := by
      rw [← h1]
      simp only [ζ, fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [fourier_one_eq_one_iff, AddCircle.coe_eq_zero_iff] at hEq
    obtain ⟨m, hm⟩ := hEq
    have hmul : (m : ℝ) * (M : ℝ) = (k : ℝ) := (eq_div_iff hM0).mp (by simpa using hm)
    have hmulZ : m * (M : ℤ) = k := by exact_mod_cast hmul
    have hdvd : M ∣ k.natAbs := ⟨m.natAbs, by
      simpa [Int.natAbs_mul, mul_comm] using congrArg Int.natAbs hmulZ.symm⟩
    exact Nat.not_lt.mpr (Nat.le_of_dvd (Int.natAbs_pos.mpr hk) hdvd) hM
  simp_rw [hpow]
  rw [geom_sum_eq hζne, hζM, sub_self, zero_div]

/-- Per-bucket Lipschitz error bound between `fourier k (u i)` and its value at the left grid
endpoint `j / M` over all indices `i ≤ n` whose fractional part falls in `[j / M, (j + 1) / M)`. -/
private theorem norm_sum_bucket_sub_le (u : ℕ → ℝ) (k : ℤ) (M n j : ℕ) :
    ‖∑ i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ))),
          (fourier k (u i : UnitAddCircle) -
            fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))‖ ≤
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)))).card : ℝ) *
        (2 * Real.pi * |(k : ℝ)| / (M : ℝ)) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ))),
          ‖fourier k (u i : UnitAddCircle) -
            fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)‖
      ≤ ∑ _i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ))),
          (2 * Real.pi * |(k : ℝ)| / (M : ℝ)) := by
        refine sum_le_sum fun i hi ↦ ?_
        have hmem := (mem_filter.mp hi).2
        rw [← AddCircle.coe_fract (u i)]
        refine (norm_fourier_coe_sub_le k (Int.fract (u i)) ((j : ℝ) / (M : ℝ))).trans ?_
        rw [norm_two_pi_I_mul_intCast_div one_pos, div_one]
        have habs : |Int.fract (u i) - (j : ℝ) / (M : ℝ)| ≤ 1 / (M : ℝ) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hmem.1)]
          have hlt : Int.fract (u i) < ((j : ℝ) + 1) / (M : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one] using hmem.2
          linarith [add_div (j : ℝ) 1 (M : ℝ)]
        calc 2 * Real.pi * |(k : ℝ)| * |Int.fract (u i) - (j : ℝ) / (M : ℝ)|
            ≤ 2 * Real.pi * |(k : ℝ)| * (1 / (M : ℝ)) := by gcongr
          _ = 2 * Real.pi * |(k : ℝ)| / (M : ℝ) := by ring
    _ = _ := by simp

/-- Partitioning `[0, 1)` into `M > 0` equal subintervals approximates the Weyl exponential average
of `u` within `2π|k| / M` by the frequency-weighted sum of character values at the grid points. -/
private theorem norm_avg_fourier_sub_bucket_le (u : ℕ → ℝ) (k : ℤ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle) -
      ∑ j ∈ range M,
        (((((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)))).card : ℝ) /
          ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)‖ ≤
      2 * Real.pi * |(k : ℝ)| / (M : ℝ) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  let I : ℕ → Set ℝ := fun j ↦ Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ))
  let bucket : ℕ → ℕ := fun i ↦ ⌊(M : ℝ) * Int.fract (u i)⌋₊
  have hmaps : ∀ i ∈ range (n + 1), bucket i ∈ range M := fun i _ ↦
    Finset.mem_range.mpr ((Nat.floor_lt (mul_nonneg hMreal.le (Int.fract_nonneg _))).mpr
      (by nlinarith [Int.fract_lt_one (u i)]))
  have hfilt (j : ℕ) :
      (range (n + 1)).filter (fun i ↦ bucket i = j) =
        (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j) :=
    filter_congr fun i _ ↦ by
      simp only [bucket, I, Set.mem_Ico,
        Nat.floor_eq_iff (mul_nonneg hMreal.le (Int.fract_nonneg _)),
        div_le_iff₀' hMreal, lt_div_iff₀' hMreal, Nat.cast_add, Nat.cast_one]
  have hSn : ∑ j ∈ range M,
        (((((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j)).card : ℝ) /
          ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ range M,
        ∑ _i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j),
          fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) := by
    simp only [sum_const, nsmul_eq_mul, mul_sum]
    exact sum_congr rfl fun j _ ↦ by push_cast; ring
  have hcard_sum : ∑ j ∈ range M,
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j)).card : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    have hnat : ∑ j ∈ range M, ((range (n + 1)).filter (fun i ↦ bucket i = j)).card = n + 1 :=
      ((Finset.sum_card_fiberwise_eq_card_filter (range (n + 1)) (range M) bucket).trans
        (by rw [filter_true_of_mem hmaps])).trans (card_range (n + 1))
    simp_rw [← hfilt]; exact_mod_cast hnat
  rw [(Finset.sum_fiberwise_of_maps_to hmaps (fun i ↦ fourier k (u i : UnitAddCircle))).symm, hSn,
    ← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j ∈ range M, _‖
      ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ range M,
          (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j)).card : ℝ) *
            (2 * Real.pi * |(k : ℝ)| / (M : ℝ)) := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
        rw [hfilt j, ← sum_sub_distrib]
        exact norm_sum_bucket_sub_le u k M n j
    _ = 2 * Real.pi * |(k : ℝ)| / (M : ℝ) := by
        rw [← sum_mul, hcard_sum, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

/-- Haar equidistribution of `n ↦ (u n : UnitAddCircle)` implies that fractional-part visit
frequencies in `[a, b) ⊆ [0, 1]` converge to `b - a`. -/
private theorem tendsto_fract_Ico_of_asympEquidistributed {u : ℕ → ℝ}
    (hu : AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
      AddCircle.haarAddCircle.toProbabilityMeasure)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦
        (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
          ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (b - a)) := by
  classical
  set E : Set UnitAddCircle :=
    (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹' Ico a b
  have hm : Measurable (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hfront : (AddCircle.haarAddCircle : Measure UnitAddCircle) (frontier E) = 0 :=
    measure_mono_null (frontier_preimage_equivIco_Ico_subset ha hab hb) (by
      rw [Set.insert_eq]
      exact measure_union_null (haarAddCircle_singleton_zero _) (haarAddCircle_singleton_zero _))
  have hmeas : (AddCircle.haarAddCircle : Measure UnitAddCircle).real E = b - a := by
    have hvol : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
      simp [AddCircle.volume_eq_smul_haarAddCircle]
    rw [Measure.real, hvol, ← Measure.map_apply hm measurableSet_Ico,
      AddCircle.map_coe_equivIco_volume 0, Measure.restrict_apply measurableSet_Ico,
      zero_add, Set.Ico_inter_Ico, max_eq_left ha, min_eq_left hb, Real.volume_Ico,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hfreq := hu.tendsto_frequency (hm measurableSet_Ico) hfront
  rw [Measure.coe_toProbabilityMeasure, hmeas] at hfreq
  refine hfreq.congr fun n ↦ congrArg (fun s : Finset ℕ ↦ (s.card : ℝ) / ((n + 1 : ℕ) : ℝ)) ?_
  exact filter_congr fun i _ ↦ by simp [AddCircle.coe_equivIco_mk_apply]

/-- Convergence of fractional-part visit frequencies in all subintervals `[a, b) ⊆ [0, 1]` implies
vanishing of all nonzero Weyl exponential averages. -/
private theorem tendsto_fourier_of_forall_fract_Ico {u : ℕ → ℝ}
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (fun n : ℕ ↦
        (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
          ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (b - a)))
    {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hMgt⟩ := exists_nat_gt (max (k.natAbs : ℝ) (4 * Real.pi * (k.natAbs : ℝ) / ε))
  have hMk : k.natAbs < M := by exact_mod_cast (le_max_left _ _).trans_lt hMgt
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hMk
  have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have hMlip : 2 * Real.pi * |(k : ℝ)| / (M : ℝ) < ε / 2 := by
    rw [show |(k : ℝ)| = (k.natAbs : ℝ) by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast], div_lt_iff₀ hMreal]
    linarith [(div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hMgt)]
  let S : ℕ → ℂ := fun n ↦ ∑ j ∈ range M,
    (((((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
        Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)))).card : ℝ) /
      ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)
  have hS : Tendsto S atTop (𝓝 0) := by
    have hS' := tendsto_finsetSum (range M) fun j hj ↦
      ((Complex.continuous_ofReal.tendsto _).comp
        (hfreq ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)) (by positivity)
          (by gcongr; exact_mod_cast Nat.le_succ j)
          ((div_le_one hMreal).mpr (by exact_mod_cast Finset.mem_range.mp hj)))).mul_const
        (fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))
    have hlen (j : ℕ) :
        ((((j + 1 : ℕ) : ℝ) / (M : ℝ) - (j : ℝ) / (M : ℝ) : ℝ) : ℂ) = (M : ℂ)⁻¹ := by
      push_cast; field_simp [hMreal.ne']; ring
    simpa only [S, Function.comp_apply, hlen, ← mul_sum, sum_fourier_div_eq_zero hk hMk, mul_zero]
      using hS'
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hS (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right]
  have hdiff := (norm_avg_fourier_sub_bucket_le u k hMpos n).trans_lt hMlip
  have hSn_lt : ‖S n‖ < ε / 2 := by simpa [dist_zero_right] using hN n hn
  have htri := norm_add_le
    (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle) - S n) (S n)
  rw [sub_add_cancel] at htri
  linarith

/-- **Classical equivalence for uniform distribution modulo `1`**: for `u : ℕ → ℝ`, Haar
equidistribution of `n ↦ (u n : UnitAddCircle)`, convergence of fractional-part visit frequencies
in every interval `[a, b) ⊆ [0, 1]`, and vanishing of all nonzero Weyl exponential sums are
equivalent. -/
theorem uniformDistribution_mod_one_tfae (u : ℕ → ℝ) :
    List.TFAE [
      AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
        AddCircle.haarAddCircle.toProbabilityMeasure,
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        Tendsto (fun n : ℕ ↦
          (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
            ((n + 1 : ℕ) : ℝ))
          atTop (𝓝 (b - a)),
      ∀ k : ℤ, k ≠ 0 →
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
            ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle))
          atTop (𝓝 0)
    ] := by
  tfae_have 1 → 2 := fun hu _ _ ha hab hb ↦ tendsto_fract_Ico_of_asympEquidistributed hu ha hab hb
  tfae_have 2 → 3 := fun hfreq _ hk ↦ tendsto_fourier_of_forall_fract_Ico hfreq hk
  tfae_have 3 → 1 := weyl_criterion_addCircle.mpr
  tfae_finish

end UniformDistributionModOne

end TauCeti
