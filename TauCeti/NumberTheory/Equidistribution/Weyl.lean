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
import Mathlib.Data.List.TFAE
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Analysis.SpecificLimits.Cesaro
import TauCeti.MeasureTheory.Measure.AddCircle
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier
import TauCeti.Topology.Instances.AddCircle.LiftIco

/-!
# Weyl's equidistribution criteria on circles and tori

Fourier-analytic equidistribution criteria on `AddCircle T` and `UnitAddTorus d`:

* `TauCeti.TorusIrrational` and `TauCeti.torusIrrational_iff_mFourier`: irrationality on
  `UnitAddTorus d` via non-annihilation by nonzero integer frequency vectors.
* `TauCeti.asympEquidistributed_addCircle_iff`, `TauCeti.weyl_criterion_addCircle`,
  `TauCeti.asympEquidistributed_unitAddTorus_iff`, `TauCeti.weyl_criterion`: Weyl's criterion on
  `AddCircle T` and `UnitAddTorus d`.
* `TauCeti.asympEquidistributed_unitAddTorus_iff_forall_linear_comb`: reduction to 1D projections.
* `TauCeti.totallyAsympEquidistributed_unitAddTorus_iff_rational_twist`: total equidistribution via
  rationally twisted Weyl sums.
* `TauCeti.uniformDistribution_mod_one_tfae`: equivalence of Haar equidistribution on
  `UnitAddCircle`, fractional-part interval frequencies, and Weyl's exponential sums.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Proposition 1.1.2, Corollary 1.1.3, Exercises 1.1.1 and 1.1.4).
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace TauCeti

section TorusIrrational

variable {d : Type*} [Fintype d]

/-- A point `α : UnitAddTorus d` is irrational if no nonzero integer frequency vector annihilates
it under the pairing `k ↦ ∑ i, k i • α i`. -/
def TorusIrrational (α : UnitAddTorus d) : Prop :=
  ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0

/-- Unfolding characterization of `TorusIrrational`. -/
theorem torusIrrational_def {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0 := Iff.rfl

/-- A torus point `α` is irrational iff every nontrivial Fourier character takes a value other
than `1` at `α`. -/
theorem torusIrrational_iff_mFourier {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → UnitAddTorus.mFourier k α ≠ 1 :=
  forall₂_congr fun _ _ ↦ by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, not_iff_not, fourier_one_eq_one_iff one_ne_zero]

/-- On a one-dimensional torus, `TorusIrrational` coincides with having infinite additive order. -/
theorem torusIrrational_unique_iff [Unique d] {α : UnitAddTorus d} :
    TorusIrrational α ↔ addOrderOf (α default) = 0 := by
  rw [torusIrrational_def, addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨fun h ⟨n, hn, hz⟩ ↦ h (fun _ ↦ n)
      (fun hk ↦ hn.ne' (Int.ofNat_eq_zero.mp (congrFun hk default)))
      (by simpa [Fintype.sum_unique, natCast_zsmul] using hz),
    fun h k hk hsum ↦ h ⟨(k default).natAbs, Int.natAbs_pos.mpr
      (fun h0 ↦ hk (funext fun i ↦ Unique.eq_default i ▸ h0)), ?_⟩⟩
  have hkd : k default • α default = 0 := by simpa [Fintype.sum_unique] using hsum
  rcases Int.natAbs_eq (k default) with heq | heq
  · rwa [← natCast_zsmul, ← heq]
  · rw [← natCast_zsmul, ← (by omega : -(k default) = ((k default).natAbs : ℤ)),
      neg_zsmul, hkd, neg_zero]

/-- On an empty coordinate type, every torus point is vacuously irrational. -/
theorem torusIrrational_of_isEmpty [IsEmpty d] (α : UnitAddTorus d) :
    TorusIrrational α := fun k hk ↦ (hk (Subsingleton.elim k 0)).elim

/-- Scaling a torus point by a nonzero integer preserves and reflects irrationality. -/
theorem torusIrrational_zsmul_iff {α : UnitAddTorus d} {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  refine ⟨fun h k hk hsum ↦ h k hk ?_, fun h k hk hsum ↦ h (m • k) (smul_ne_zero hm hk) ?_⟩
  · simp [Pi.smul_apply, zsmul_comm, ← smul_sum, hsum]
  · rw [← hsum]; exact sum_congr rfl fun _ _ ↦ by simp [mul_zsmul, zsmul_comm]

/-- A nonzero integer multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.zsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℤ} (hm : m ≠ 0) :
    TorusIrrational (m • α) := (torusIrrational_zsmul_iff hm).mpr hα

/-- Scaling a torus point by a nonzero natural number preserves and reflects irrationality. -/
theorem torusIrrational_nsmul_iff {α : UnitAddTorus d} {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) ↔ TorusIrrational α := by
  simpa [natCast_zsmul] using
    torusIrrational_zsmul_iff (α := α) (m := (m : ℤ)) (Int.natCast_ne_zero.mpr hm)

/-- A nonzero natural-number multiple of an irrational torus point is irrational. -/
theorem TorusIrrational.nsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℕ} (hm : m ≠ 0) :
    TorusIrrational (m • α) := (torusIrrational_nsmul_iff hm).mpr hα

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
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_complex]

/-- **Weyl's criterion on `AddCircle T`**: a sequence is asymptotically equidistributed for Haar
probability iff the Cesàro averages of every nonzero integer Fourier character tend to `0`. -/
theorem weyl_criterion_addCircle {T : ℝ} [Fact (0 < T)] {x : ℕ → AddCircle T} :
    AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure ↔ ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (x i))
        atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_haarAddCircle_iff]
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_complex]

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
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_complex]

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
  simp_rw [TauCeti.Probability.integral_empiricalMeasure_complex]

/-- **Equidistribution on `UnitAddTorus d` via one-dimensional projections**: a sequence in
`UnitAddTorus d` is equidistributed for Haar probability iff every nonzero integer linear
combination of its coordinates is equidistributed on `UnitAddCircle`. -/
theorem asympEquidistributed_unitAddTorus_iff_forall_linear_comb {x : ℕ → UnitAddTorus d} :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 →
        AsympEquidistributed (fun n ↦ ∑ i, k i • x n i)
          AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion]
  refine ⟨fun hx k hk ↦ weyl_criterion_addCircle.mpr fun m hm ↦ ?_, fun h k hk ↦ ?_⟩
  · simpa only [UnitAddTorus.mFourier_zsmul] using hx (m • k) (smul_ne_zero hm hk)
  · simpa only [← UnitAddTorus.mFourier_eq_fourier_sum] using
      (weyl_criterion_addCircle.mp (h k hk)) 1 one_ne_zero

/-- Vanishing of rational twists modulo `q` implies vanishing on residue class `r < q`. -/
private theorem tendsto_cesaro_ite_mod_of_rational_twist {x : ℕ → UnitAddTorus d} {k : d → ℤ}
    {q r : ℕ} [NeZero q] (hr : r < q)
    (h : ∀ a : ℤ, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x i) *
          fourier a (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ range (n + 1), if i % q = r then UnitAddTorus.mFourier k (x i) else 0)
      atTop (𝓝 (0 : ℂ)) := by
  have hsum : Tendsto (fun n : ℕ ↦ (q : ℂ)⁻¹ * ∑ a : ZMod q,
      ZMod.stdAddChar (-((r : ZMod q) * a)) * (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1),
        UnitAddTorus.mFourier k (x i) *
          fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle))) atTop (𝓝 0) := by
    have hsum' := (tendsto_const_nhds (x := (q : ℂ)⁻¹)).mul (tendsto_finsetSum
      (Finset.univ : Finset (ZMod q)) fun a _ ↦ by simpa only [mul_zero] using
        (tendsto_const_nhds (x := ZMod.stdAddChar (-((r : ZMod q) * a)))).mul (h (a.val : ℤ)))
    rwa [sum_const_zero, mul_zero] at hsum'
  refine hsum.congr fun n ↦ ?_
  have hterm (i : ℕ) : (if i % q = r then UnitAddTorus.mFourier k (x i) else 0) =
      (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (-((r : ZMod q) * a)) *
        (UnitAddTorus.mFourier k (x i) *
          fourier (a.val : ℤ) (((i : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) := by
    rw [(by split_ifs <;> simp :
      (if i % q = r then UnitAddTorus.mFourier k (x i) else 0) =
        (if i % q = r then (1 : ℂ) else 0) * UnitAddTorus.mFourier k (x i)),
      ZMod.ite_mod_eq_sum_fourier hr i, mul_assoc, sum_mul]
    exact congrArg ((q : ℂ)⁻¹ * ·) (sum_congr rfl fun _ _ ↦ by ring)
  simp_rw [hterm, Complex.real_smul, ← mul_sum]
  rw [sum_comm (s := range (n + 1)) (t := (Finset.univ : Finset (ZMod q))),
    mul_left_comm _ (q : ℂ)⁻¹]
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1; rw [mul_sum]; exact sum_congr rfl fun a _ ↦ by rw [← mul_sum, mul_left_comm]

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
  rw [totallyAsympEquidistributed_def]; constructor
  · intro hx k hk b hb a; have : NeZero b := ⟨hb.ne'⟩
    have hmod (r : ℕ) (_ : r < b) : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (x (b * i + r)) *
          fourier a ((((b * i + r : ℕ) : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle)) atTop (𝓝 (0 : ℂ)) := by
      have hlim := ((weyl_criterion.mp (hx b r hb)) k hk).mul_const
        (ZMod.stdAddChar ((r : ZMod b) * (a : ZMod b)))
      rw [zero_mul] at hlim; refine hlim.congr fun n ↦ ?_
      simp_rw [ZMod.fourier_natCast_div_eq_stdAddChar, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, zero_mul, zero_add, ← sum_mul, Complex.real_smul, Nat.cast_one]
      push_cast; ring
    simpa [Complex.real_smul] using tendsto_cesaro_of_forall_mod (f := fun i ↦
      UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle))
      hb (L := fun _ ↦ 0) hmod
  · intro h q r hq; have : NeZero q := ⟨hq.ne'⟩
    rw [← (funext fun n ↦ by rw [Nat.mul_add, Nat.add_assoc, Nat.div_add_mod] :
        (fun n ↦ x (q * (n + r / q) + r % q)) = fun n ↦ x (q * n + r)),
      asympEquidistributed_comp_add_iff (x := fun n ↦ x (q * n + r % q)) (r / q), weyl_criterion]
    intro k hk
    simpa [Complex.real_smul] using tendsto_cesaro_mul_add_of_ite_mod hq (Nat.mod_lt r hq)
      (tendsto_cesaro_ite_mod_of_rational_twist (Nat.mod_lt r hq) (h k hk q hq))

end WeylCriteria

section UniformDistributionModOne

/-- Per-bucket Lipschitz bound between `fourier k (u i)` and its left grid endpoint `j / M`. -/
private theorem norm_sum_bucket_sub_le (u : ℕ → ℝ) (k : ℤ) (M n j : ℕ) :
    ‖∑ i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ))),
          (fourier k (u i : UnitAddCircle) -
            fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))‖ ≤
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
            Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)))).card : ℝ) *
        (2 * Real.pi * |(k : ℝ)| / (M : ℝ)) := by
  refine (norm_sum_le _ _).trans ((sum_le_sum (g := fun _ ↦
    2 * Real.pi * |(k : ℝ)| / (M : ℝ)) fun i hi ↦ ?_).trans (by simp))
  have hmem := (mem_filter.mp hi).2; rw [← AddCircle.coe_fract (u i)]
  refine (norm_fourier_coe_sub_le k (Int.fract (u i)) ((j : ℝ) / (M : ℝ))).trans ?_
  rw [norm_two_pi_I_mul_intCast_div one_pos, div_one, mul_div_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
  rw [abs_of_nonneg (sub_nonneg.mpr hmem.1)]
  have hlt : Int.fract (u i) < ((j : ℝ) + 1) / (M : ℝ) := by simpa using hmem.2
  linarith [add_div (j : ℝ) 1 (M : ℝ), one_div (M : ℝ)]

/-- Partitioning `[0, 1)` into `M > 0` subintervals approximates the Weyl sum within `2π|k|/M`. -/
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
  have hmaps : ∀ i ∈ range (n + 1), bucket i ∈ range M := fun i _ ↦ mem_range.mpr
    ((Nat.floor_lt (mul_nonneg hMreal.le (Int.fract_nonneg _))).mpr
      (by nlinarith [Int.fract_lt_one (u i)]))
  have hfilt (j : ℕ) : (range (n + 1)).filter (fun i ↦ bucket i = j) =
      (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j) :=
    filter_congr fun i _ ↦ by simp only [bucket, I, Set.mem_Ico,
      Nat.floor_eq_iff (mul_nonneg hMreal.le (Int.fract_nonneg _)), div_le_iff₀' hMreal,
      lt_div_iff₀' hMreal, Nat.cast_add, Nat.cast_one]
  have hSn : ∑ j ∈ range M, (((((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j)).card : ℝ) /
          ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ range M, ∑ _i ∈ (range (n + 1)).filter
        (fun i ↦ Int.fract (u i) ∈ I j), fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) := by
    simp only [sum_const, nsmul_eq_mul, mul_sum]; exact sum_congr rfl fun j _ ↦ by push_cast; ring
  have hcard : ∑ j ∈ range M,
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j)).card : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    simp_rw [← hfilt]; exact_mod_cast ((sum_card_fiberwise_eq_card_filter (range (n + 1)) (range M)
      bucket).trans (by rw [filter_true_of_mem hmaps])).trans (card_range (n + 1))
  have hbound : ∑ j ∈ range M, ‖∑ i ∈ (range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ I j),
      (fourier k (u i : UnitAddCircle) - fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))‖ ≤
      ((n + 1 : ℕ) : ℝ) * (2 * Real.pi * |(k : ℝ)| / (M : ℝ)) :=
    (sum_le_sum fun j _ ↦ norm_sum_bucket_sub_le u k M n j).trans_eq (by rw [← sum_mul, hcard])
  rw [(sum_fiberwise_of_maps_to hmaps (fun i ↦ fourier k (u i : UnitAddCircle))).symm, hSn,
    ← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  simp_rw [hfilt, ← sum_sub_distrib]
  refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hbound) (by positivity)).trans_eq ?_
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

/-- Haar equidistribution implies convergence of fractional-part visit frequencies in `[a, b)`. -/
private theorem tendsto_fract_Ico_of_asympEquidistributed {u : ℕ → ℝ}
    (hu : AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
      AddCircle.haarAddCircle.toProbabilityMeasure)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦ (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (b - a)) := by
  classical
  set E : Set UnitAddCircle := (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) ⁻¹' Ico a b
  have hm : Measurable (fun θ : UnitAddCircle ↦ (AddCircle.equivIco 1 0 θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hmeas : (AddCircle.haarAddCircle : Measure UnitAddCircle).real E = b - a := by
    rw [Measure.real, (by simp [AddCircle.volume_eq_smul_haarAddCircle] :
        (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume),
      ← Measure.map_apply hm measurableSet_Ico, AddCircle.map_coe_equivIco_volume 0,
      Measure.restrict_apply measurableSet_Ico, zero_add, Set.Ico_inter_Ico, max_eq_left ha,
      min_eq_left hb, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hfreq := hu.tendsto_frequency (hm measurableSet_Ico) (measure_mono_null
    (AddCircle.frontier_preimage_equivIco_Ico_subset ha hab (by linarith))
    (by rw [Measure.coe_toProbabilityMeasure, Set.insert_eq]
        exact measure_union_null (measure_singleton _) (measure_singleton _)))
  rw [Measure.coe_toProbabilityMeasure, hmeas] at hfreq
  exact hfreq.congr fun n ↦ congrArg (fun s : Finset ℕ ↦ (s.card : ℝ) / ((n + 1 : ℕ) : ℝ))
    (filter_congr fun i _ ↦ by simp [AddCircle.coe_equivIco_mk_apply])

/-- Convergence of fractional-part frequencies on `[a, b) ⊆ [0, 1]` implies Weyl's criterion. -/
private theorem tendsto_fourier_of_forall_fract_Ico {u : ℕ → ℝ}
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (fun n : ℕ ↦
      (((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Ico a b)).card : ℝ) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (b - a))) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨M, hMgt⟩ := exists_nat_gt (max (k.natAbs : ℝ) (4 * Real.pi * (k.natAbs : ℝ) / ε))
  have hMk : k.natAbs < M := by exact_mod_cast (le_max_left _ _).trans_lt hMgt
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hMk
  have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  let S : ℕ → ℂ := fun n ↦ ∑ j ∈ range M,
    (((((range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈
        Ico ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)))).card : ℝ) /
      ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle)
  have hS : Tendsto S atTop (𝓝 0) := by
    have hlen (j : ℕ) : ((((j + 1 : ℕ) : ℝ) / (M : ℝ) - (j : ℝ) / (M : ℝ) : ℝ) : ℂ) =
        (M : ℂ)⁻¹ := by push_cast; field_simp [hMreal.ne']; ring
    simpa only [S, Function.comp_apply, hlen, ← mul_sum, ZMod.sum_fourier_div_eq_zero hk hMk,
      mul_zero] using tendsto_finsetSum (range M) fun j hj ↦ ((Complex.continuous_ofReal.tendsto
        _).comp (hfreq ((j : ℝ) / (M : ℝ)) (((j + 1 : ℕ) : ℝ) / (M : ℝ)) (by positivity)
          (by gcongr; exact_mod_cast Nat.le_succ j) ((div_le_one hMreal).mpr
            (by exact_mod_cast mem_range.mp hj)))).mul_const
      (fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hS (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩; rw [dist_zero_right]
  have hMlip : 2 * Real.pi * |(k : ℝ)| / (M : ℝ) < ε / 2 := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, div_lt_iff₀ hMreal]
    linarith [(div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hMgt)]
  linarith [norm_add_le (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), fourier k (u i : UnitAddCircle)
      - S n) (S n) |>.trans_eq' (by rw [sub_add_cancel]),
    (norm_avg_fourier_sub_bucket_le u k hMpos n).trans_lt hMlip,
    (by simpa [dist_zero_right] using hN n hn : ‖S n‖ < ε / 2)]

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
