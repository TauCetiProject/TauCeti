/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
public import TauCeti.NumberTheory.Equidistribution.Basic
import Mathlib.Analysis.Fourier.ZMod
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.SpecificLimits.Cesaro
import TauCeti.MeasureTheory.Measure.AddCircle
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier

/-!
# Weyl's equidistribution criteria on circles and tori

This file develops the Fourier-analytic theory of asymptotic equidistribution on `AddCircle T` and
`UnitAddTorus d = (ℝ / ℤ)^d`:

* `TauCeti.TorusIrrational`: no nonzero integer frequency annihilates `α : UnitAddTorus d`.
* Weyl criteria for arbitrary limit measures and Haar probability on `AddCircle T` and
  `UnitAddTorus d` (`TauCeti.weyl_criterion`), plus reduction to 1D projections
  (`TauCeti.asympEquidistributed_volume_iff_projections`).
* Rational-twist characterization of total equidistribution via discrete Fourier inversion on
  `ZMod q` (`TauCeti.totallyAsympEquidistributed_volume_iff_rational_twists`).
* Uniform distribution modulo one (`TauCeti.uniformDistribution_mod_one_tfae`).

## References

* T. Tao, *Higher Order Fourier Analysis*, AMS, 2012, §1.1.1 (Prop. 1.1.2, Cor. 1.1.3,
  Exercises 1.1.1 and 1.1.4).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Real

namespace TauCeti

section Irrational

variable {d : Type*} [Fintype d]

/-- A torus point `α : UnitAddTorus d` is irrational if no nonzero integer frequency annihilates
it, i.e., `∑ i, k i • α i ≠ 0` for every nonzero `k : d → ℤ`. -/
def TorusIrrational (α : UnitAddTorus d) : Prop :=
  ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0

/-- Definitional restatement of `TorusIrrational`. -/
theorem torusIrrational_def {α : UnitAddTorus d} :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → ∑ i, k i • α i ≠ 0 :=
  Iff.rfl

/-- On an empty coordinate type, every point of the zero-dimensional torus is irrational. -/
theorem torusIrrational_of_isEmpty [IsEmpty d] (α : UnitAddTorus d) : TorusIrrational α :=
  fun k hk ↦ (hk (Subsingleton.elim k 0)).elim

private theorem fourier_one_eq_one_iff (y : UnitAddCircle) : fourier 1 y = 1 ↔ y = 0 :=
  ⟨fun h ↦ AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0) <|
      Subtype.ext (by simpa [fourier_one, AddCircle.toCircle_zero] using h),
    fun h ↦ h ▸ fourier_eval_zero 1⟩

/-- A torus point is irrational if and only if every nonzero multivariate Fourier character takes a
value different from `1` at it. -/
theorem torusIrrational_iff_mFourier (α : UnitAddTorus d) :
    TorusIrrational α ↔ ∀ k : d → ℤ, k ≠ 0 → UnitAddTorus.mFourier k α ≠ 1 := by
  simp only [torusIrrational_def, UnitAddTorus.mFourier_eq_fourier_sum, ne_eq,
    fourier_one_eq_one_iff]

/-- For a one-element coordinate type, torus irrationality is equivalent to infinite additive
order of the single coordinate. -/
theorem torusIrrational_unique_iff [Unique d] (α : UnitAddTorus d) :
    TorusIrrational α ↔ addOrderOf (α default) = 0 := by
  rw [torusIrrational_def, addOrderOf_eq_zero_iff]
  refine ⟨fun h hfin ↦ ?_, fun hinf k hk hsum ↦ ?_⟩
  · obtain ⟨m, hmpos, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
    exact h (fun _ ↦ (m : ℤ)) (fun hk ↦ hmpos.ne' (Int.ofNat_eq_zero.1 (congrFun hk default)))
      (by simpa [Fintype.sum_unique] using hm0)
  · rw [Fintype.sum_unique] at hsum
    have hk0 : k default ≠ 0 := fun h0 ↦ hk (funext fun i ↦ Unique.eq_default i ▸ h0)
    refine hinf (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨(k default).natAbs, Int.natAbs_pos.2 hk0, ?_⟩)
    rcases Int.natAbs_eq (k default) with hpos | hneg
    · rw [← natCast_zsmul, ← hpos]; exact hsum
    · rw [← neg_eq_zero, ← natCast_zsmul, ← neg_zsmul, ← hneg]; exact hsum

/-- Scaling an irrational torus point by a nonzero integer preserves irrationality. -/
theorem TorusIrrational.zsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℤ}
    (hm : m ≠ 0) : TorusIrrational (m • α) := fun k hk hsum ↦ by
  refine hα (m • k) (smul_ne_zero hm hk) ?_
  convert hsum using 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, mul_zsmul, zsmul_comm]

/-- Scaling an irrational torus point by a nonzero natural number preserves irrationality. -/
theorem TorusIrrational.nsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℕ}
    (hm : m ≠ 0) : TorusIrrational (m • α) := by
  rw [← natCast_zsmul]; exact hα.zsmul (Nat.cast_ne_zero.2 hm)

end Irrational

section WeylCriteria

private theorem integral_empiricalMeasure_continuousMap {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (x : ℕ → X) (f : C(X, ℂ)) (n : ℕ) :
    ∫ y, f y ∂(TauCeti.Probability.empiricalMeasure x n : Measure X) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i) := by
  rw [TauCeti.Probability.integral_empiricalMeasure f.continuous.stronglyMeasurable,
    Complex.real_smul]
  push_cast; rfl

/-- **Weyl's criterion for an arbitrary limit measure on `AddCircle T`.** -/
theorem asympEquidistributed_iff_forall_fourier {T : ℝ} [Fact (0 < T)]
    (x : ℕ → AddCircle T) (μ : ProbabilityMeasure (AddCircle T)) :
    AsympEquidistributed x μ ↔ ∀ k : ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), fourier k (x i))
        atTop (𝓝 (∫ y, fourier k y ∂(μ : Measure (AddCircle T)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_fourier_tendsto]
  simp_rw [integral_empiricalMeasure_continuousMap]

/-- **Weyl's criterion for Haar equidistribution on `AddCircle T`.** -/
theorem asympEquidistributed_haarAddCircle_iff {T : ℝ} [Fact (0 < T)] (x : ℕ → AddCircle T) :
    AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure ↔ ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), fourier k (x i)) atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_haarAddCircle_iff]
  simp_rw [integral_empiricalMeasure_continuousMap]

variable {d : Type*} [Fintype d]

/-- **Weyl's criterion for an arbitrary limit measure on `UnitAddTorus d`.** -/
theorem asympEquidistributed_iff_forall_mFourier (x : ℕ → UnitAddTorus d)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    AsympEquidistributed x μ ↔ ∀ k : d → ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), UnitAddTorus.mFourier k (x i))
        atTop (𝓝 (∫ y, UnitAddTorus.mFourier k y ∂(μ : Measure (UnitAddTorus d)))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_mFourier_tendsto]
  simp_rw [integral_empiricalMeasure_continuousMap]

/-- **Weyl's criterion on the unit torus.** A sequence in `UnitAddTorus d` is equidistributed for
Haar probability (`volume.toProbabilityMeasure`) if and only if the Cesàro averages of every
nonzero multivariate Fourier character tend to `0`. -/
theorem weyl_criterion (x : ℕ → UnitAddTorus d) :
    AsympEquidistributed x volume.toProbabilityMeasure ↔ ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), UnitAddTorus.mFourier k (x i)) atTop (𝓝 0) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_volume_unitAddTorus_iff]
  simp_rw [integral_empiricalMeasure_continuousMap]

/-- **Equidistribution on `UnitAddTorus d` via one-dimensional projections.** A sequence is
equidistributed on `UnitAddTorus d` if and only if every nonzero integer linear combination of its
coordinates is equidistributed on `UnitAddCircle`. -/
theorem asympEquidistributed_volume_iff_projections (x : ℕ → UnitAddTorus d) :
    AsympEquidistributed x volume.toProbabilityMeasure ↔ ∀ k : d → ℤ, k ≠ 0 →
      AsympEquidistributed (fun n ↦ ∑ i, k i • x n i)
        AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion]
  simp_rw [asympEquidistributed_haarAddCircle_iff]
  have hproj (m : ℤ) (k : d → ℤ) (z : UnitAddTorus d) :
      fourier m (∑ i, k i • z i) = UnitAddTorus.mFourier (m • k) z := by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, fourier_apply, fourier_one, Finset.smul_sum]
    congr 2; exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_zsmul]
  simp_rw [hproj]
  exact ⟨fun h k hk m hm ↦ h (m • k) (smul_ne_zero hm hk),
    fun h k hk ↦ by simpa only [one_smul] using h k hk 1 one_ne_zero⟩

end WeylCriteria

section RationalTwists

variable {d : Type*} [Fintype d]

private theorem inv_mul_sum_stdAddChar_eq_ite {q : ℕ} [NeZero q] (r i : ZMod q) :
    (q : ℂ)⁻¹ * ∑ a : ZMod q, (ZMod.stdAddChar (a * i) : ℂ) * ZMod.stdAddChar (-(r * a)) =
      if i = r then 1 else 0 := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply (Pi.single r (1 : ℂ))) i
  rw [ZMod.invDFT_apply] at hinv
  simpa [ZMod.dft_apply, Pi.single_apply, smul_eq_mul] using hinv

private theorem sum_mod_class_eq_rational_twists (f : ℕ → ℂ) {q r : ℕ} [NeZero q] (hr : r < q)
    (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), f (q * j + r) =
      (q : ℂ)⁻¹ * ∑ a : ZMod q, (ZMod.stdAddChar (-((r : ZMod q) * a)) : ℂ) *
        ∑ i ∈ Finset.range (q * (m + 1)),
          f i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle) := by
  have hind : ∑ j ∈ Finset.range (m + 1), f (q * j + r) =
      ∑ i ∈ Finset.range (q * (m + 1)), (if (i : ZMod q) = (r : ZMod q) then 1 else 0) * f i := by
    symm
    rw [sum_range_mul_eq_sum_fin, Finset.sum_eq_single ⟨r, hr⟩]
    · exact Finset.sum_congr rfl fun _ _ ↦ by simp
    · intro b _ hne
      refine Finset.sum_eq_zero fun _ _ ↦ ?_
      have hmod : (b.val : ZMod q) ≠ (r : ZMod q) := fun h ↦ by
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt hr] at h
        exact hne (Fin.ext h)
      simp [hmod]
    · exact fun h ↦ (h (Finset.mem_univ _)).elim
  rw [hind]
  simp_rw [← inv_mul_sum_stdAddChar_eq_ite (r : ZMod q), mul_assoc, Finset.sum_mul,
    ← Finset.mul_sum]
  congr 1; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hchar : fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar (a * (i : ZMod q)) := by
    rw [show a * (i : ZMod q) = (((a.val : ℤ) * (i : ℕ) : ℤ) : ZMod q) by
        push_cast; rw [ZMod.natCast_zmod_val],
      fourier_coe_apply, ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  rw [hchar]; ring

private theorem tendsto_twisted_of_totallyAsympEquidistributed {x : ℕ → UnitAddTorus d}
    (htot : TotallyAsympEquidistributed x volume.toProbabilityMeasure) {k : d → ℤ} (hk : k ≠ 0)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (n + 1),
        UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
      atTop (𝓝 0) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.2 hq
  let f (i : ℕ) : ℂ := UnitAddTorus.mFourier k (x i) *
    fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle)
  have hcls (r : Fin q) : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), f (q * j + r)) atTop (𝓝 (0 : ℂ)) := by
    have hconst (j : ℕ) : fourier a ((((q * j + r : ℕ) : ℝ) / q : ℝ) : UnitAddCircle) =
        fourier a (((r : ℝ) / q : ℝ) : UnitAddCircle) := by
      rw [show (((q * j + r : ℕ) : ℝ) / q : ℝ) = (j : ℝ) + (r : ℝ) / q by
          push_cast; field_simp [hqR.ne'],
        AddCircle.coe_add, (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨(j : ℤ), by simp⟩, zero_add]
    have hr := ((weyl_criterion _).1 (totallyAsympEquidistributed_def.1 htot q r hq) k hk).mul_const
      (fourier a (((r : ℝ) / q : ℝ) : UnitAddCircle))
    rw [zero_mul] at hr
    exact hr.congr fun m ↦ by
      simp only [f, hconst, ← Finset.sum_mul, Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_natCast, mul_assoc]
  simpa only [Finset.sum_const_zero, smul_zero, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast] using
    tendsto_cesaro_of_mod_classes (g := f) (L := fun _ ↦ (0 : ℂ)) hq hcls

private theorem tendsto_mod_class_of_rational_twists {x : ℕ → UnitAddTorus d}
    (htwist : ∀ k : d → ℤ, k ≠ 0 → ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1),
          UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
        atTop (𝓝 0))
    {q : ℕ} (hq : 0 < q) (r : ℕ) :
    AsympEquidistributed (fun j ↦ x (q * j + r)) volume.toProbabilityMeasure := by
  rw [show (fun j ↦ x (q * j + r)) = fun j ↦ x (q * (j + r / q) + r % q) from funext fun j ↦ by
      rw [mul_add, add_assoc, Nat.div_add_mod r q],
    asympEquidistributed_comp_add_iff (fun j ↦ x (q * j + r % q)) (r / q), weyl_criterion]
  intro k hk
  have : NeZero q := ⟨hq.ne'⟩
  have hsub_top : Tendsto (fun m : ℕ ↦ q * (m + 1) - 1) atTop atTop :=
    Filter.tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨b, fun m hm ↦ by
      have : 1 * (m + 1) ≤ q * (m + 1) := Nat.mul_le_mul_right _ hq; omega⟩
  have hterm (a : ZMod q) : Tendsto (fun m : ℕ ↦
      (ZMod.stdAddChar (-(((r % q : ℕ) : ZMod q) * a)) : ℂ) *
        (((q * (m + 1) : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (q * (m + 1)),
          UnitAddTorus.mFourier k (x i) *
            fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle))) atTop (𝓝 0) := by
    have ha := (htwist k hk q hq (a.val : ℤ)).comp hsub_top
    simp only [Function.comp_def, Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos _))] at ha
    simpa using ha.const_mul (ZMod.stdAddChar (-(((r % q : ℕ) : ZMod q) * a)) : ℂ)
  have hsum := tendsto_finsetSum Finset.univ fun a _ ↦ hterm a
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr fun m ↦ ?_
  rw [sum_mod_class_eq_rational_twists (fun i ↦ UnitAddTorus.mFourier k (x i)) (Nat.mod_lt r hq) m,
    Finset.mul_sum]
  simp only [Nat.cast_mul, mul_inv]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Total equidistribution on `UnitAddTorus d` by rational twists.** A sequence is totally
equidistributed for Haar probability if and only if every nonzero Fourier character twisted by
every rational exponential `i ↦ e(a * i / q)` has Cesàro averages tending to `0`. -/
theorem totallyAsympEquidistributed_volume_iff_rational_twists (x : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributed x volume.toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∀ q : ℕ, 0 < q → ∀ a : ℤ,
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ Finset.range (n + 1),
            UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
          atTop (𝓝 0) :=
  ⟨fun htot _ hk _ hq a ↦ tendsto_twisted_of_totallyAsympEquidistributed htot hk hq a,
    fun htwist ↦ totallyAsympEquidistributed_def.2 fun _ r hq ↦
      tendsto_mod_class_of_rational_twists htwist hq r⟩

end RationalTwists

section UniformModOne

private def fractFreq (u : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (((Finset.range (n + 1)).filter fun i ↦ Int.fract (u i) ∈ Set.Ico a b).card : ℝ) / (n + 1 : ℕ)

private theorem coe_image_Ico_eq_preimage {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) =
      (fun θ : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ)) ⁻¹' Set.Ico a b := by
  ext θ
  refine ⟨?_, fun hθ ↦ ⟨(AddCircle.equivIco (1 : ℝ) 0 θ : ℝ), hθ, AddCircle.coe_equivIco⟩⟩
  rintro ⟨t, ht, rfl⟩
  simpa [AddCircle.equivIco_coe_of_mem (show t ∈ Set.Ico (0 : ℝ) (0 + 1) from
    ⟨ha.trans ht.1, by linarith [ht.2]⟩)] using ht

private theorem haarAddCircle_preimage_equivIco {s : Set ℝ} (hs : MeasurableSet s) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
        ((fun θ : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ)) ⁻¹' s) =
      volume (s ∩ Set.Ico (0 : ℝ) (0 + 1)) := by
  have hm : Measurable fun θ : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
      simp [AddCircle.volume_eq_smul_haarAddCircle],
    ← Measure.map_apply hm hs, AddCircle.map_coe_equivIco_volume, Measure.restrict_apply hs]

private theorem haarAddCircle_coe_image_Ico {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) =
      ENNReal.ofReal (b - a) := by
  rw [coe_image_Ico_eq_preimage ha hb, haarAddCircle_preimage_equivIco measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Ico ha (by linarith)), Real.volume_Ico]

private theorem haarAddCircle_frontier_coe_image_Ico (a b : ℝ) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (frontier (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b)) = 0 := by
  have hsing (θ : UnitAddCircle) : (AddCircle.haarAddCircle : Measure UnitAddCircle) {θ} = 0 := by
    have hpre : {θ} = (fun z : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)) ⁻¹'
        {(AddCircle.equivIco (1 : ℝ) 0 θ : ℝ)} := by
      ext z
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)⟩
    rw [hpre, haarAddCircle_preimage_equivIco (measurableSet_singleton _)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton _)
  have hsub : frontier (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) ⊆
      {(a : UnitAddCircle), (b : UnitAddCircle)} := by
    have hcl : closure (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) ⊆
        ((↑) : ℝ → UnitAddCircle) '' Set.Icc a b :=
      closure_minimal (Set.image_mono Set.Ico_subset_Icc_self)
        (isCompact_Icc.image (show Continuous fun t : ℝ ↦ (t : UnitAddCircle) from
          continuous_quotient_mk')).isClosed
    have hint : ((↑) : ℝ → UnitAddCircle) '' Set.Ioo a b ⊆
        interior (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) :=
      interior_maximal (Set.image_mono Set.Ioo_subset_Ico_self)
        (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
    intro θ hθ
    obtain ⟨t, ht, rfl⟩ := hcl hθ.1
    by_cases hta : t = a
    · exact Or.inl (hta ▸ rfl)
    · by_cases htb : t = b
      · exact Or.inr (htb ▸ rfl)
      · exact (hθ.2 (hint ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
          lt_of_le_of_ne ht.2 htb⟩, rfl⟩)).elim
  exact measure_mono_null hsub (measure_union_null_iff.2 ⟨hsing _, hsing _⟩)

private theorem sum_fourier_div_eq_zero {k : ℤ} {M : ℕ} (hk : k ≠ 0) (hM : k.natAbs < M) :
    ∑ j ∈ Finset.range M, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) = 0 := by
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (lt_of_le_of_lt (Nat.zero_le _) hM).ne'
  set ζ : ℂ := fourier k (((1 : ℝ) / M : ℝ) : UnitAddCircle)
  have hpow (j : ℕ) : fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) = ζ ^ j := by
    simp only [ζ, fourier_coe_apply, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hζ_ne : ζ ≠ 1 := fun h1 ↦ by
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 <|
      (fourier_one_eq_one_iff (((k : ℝ) / M : ℝ) : UnitAddCircle)).1
        (by rw [← h1]; simp only [ζ, fourier_coe_apply]; congr 1; push_cast; ring)
    have hkmZ : k = m * (M : ℤ) := by
      simp only [zsmul_eq_mul, mul_one] at hm; exact_mod_cast (div_eq_iff hMR).1 hm.symm
    exact not_le_of_gt hM (Nat.le_of_dvd (Int.natAbs_pos.2 hk)
      (by rw [hkmZ, Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_left M m.natAbs))
  simp_rw [hpow]
  rw [geom_sum_eq hζ_ne, ← hpow M, div_self hMR, AddCircle.coe_period, fourier_eval_zero,
    sub_self, zero_div]

private theorem fract_bin_partition (u : ℕ → ℝ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    let B (j : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter
      fun i ↦ Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)
    (Finset.range M).biUnion B = Finset.range (n + 1) ∧
      Set.PairwiseDisjoint (↑(Finset.range M) : Set ℕ) B := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hM
  refine ⟨?_, fun j₁ _ j₂ _ hne ↦ ?_⟩
  · ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    refine ⟨fun ⟨_, _, hi, _⟩ ↦ hi, fun hi ↦ ?_⟩
    have := Int.fract_nonneg (u i); have := Int.fract_lt_one (u i)
    refine ⟨⌊(M : ℝ) * Int.fract (u i)⌋₊, (Nat.floor_lt (by positivity)).2 (by nlinarith),
      hi, ?_, ?_⟩
    · rw [div_le_iff₀ hMR, mul_comm]; exact Nat.floor_le (by positivity)
    · rw [lt_div_iff₀ hMR, mul_comm]; exact_mod_cast Nat.lt_floor_add_one _
  · simp only [Function.onFun, Finset.disjoint_left]
    intro i hi₁ hi₂
    have h12 : j₁ < j₂ + 1 := by
      exact_mod_cast (div_lt_div_iff_of_pos_right hMR).1
        ((Finset.mem_filter.1 hi₁).2.1.trans_lt (Finset.mem_filter.1 hi₂).2.2)
    have h21 : j₂ < j₁ + 1 := by
      exact_mod_cast (div_lt_div_iff_of_pos_right hMR).1
        ((Finset.mem_filter.1 hi₂).2.1.trans_lt (Finset.mem_filter.1 hi₁).2.2)
    omega

private theorem norm_fourier_sub_bin_le (x : ℝ) (k : ℤ) {M j : ℕ} (hM : 0 < M)
    (hmem : Int.fract x ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)) :
    ‖fourier k (x : UnitAddCircle) - fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖ ≤
      2 * π * (k.natAbs : ℝ) / M := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rw [← AddCircle.coe_fract x]
  have hlip := TauCeti.norm_fourier_coe_sub_le (T := (1 : ℝ)) k (Int.fract x) ((j : ℝ) / M)
  rw [TauCeti.norm_two_pi_I_mul_intCast_div zero_lt_one k, div_one] at hlip
  have habs : |Int.fract x - (j : ℝ) / M| ≤ (M : ℝ)⁻¹ := by
    rw [abs_of_nonneg (sub_nonneg.2 hmem.1)]
    have : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = (M : ℝ)⁻¹ := by
      push_cast; field_simp [hMR.ne']; ring
    linarith [hmem.2]
  have hkabs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  calc _ ≤ 2 * π * |(k : ℝ)| * |Int.fract x - (j : ℝ) / M| := hlip
    _ ≤ 2 * π * |(k : ℝ)| * (M : ℝ)⁻¹ := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = 2 * π * (k.natAbs : ℝ) / M := by rw [hkabs, div_eq_mul_inv]

private theorem norm_fourier_avg_sub_binned_le (u : ℕ → ℝ) (k : ℤ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle) -
      ∑ j ∈ Finset.range M,
        (fractFreq u ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M) n : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖ ≤
      2 * π * (k.natAbs : ℝ) / M := by
  let B (j : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter
    fun i ↦ Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)
  obtain ⟨hpart, hdisj⟩ := fract_bin_partition u hM n
  have hrew : ∑ j ∈ Finset.range M,
        (fractFreq u ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M) n : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range M, ∑ _i ∈ B j,
        fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [fractFreq, B, Complex.ofReal_div, Complex.ofReal_natCast, Finset.sum_const,
      nsmul_eq_mul]
    rw [div_eq_mul_inv]; ring
  have hdiff : ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle) -
        ∑ j ∈ Finset.range M, ∑ _i ∈ B j, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) =
      ∑ j ∈ Finset.range M, ∑ i ∈ B j,
        (fourier k (u i : UnitAddCircle) - fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)) := by
    rw [← hpart, Finset.sum_biUnion hdisj]; simp_rw [Finset.sum_sub_distrib]; rfl
  rw [hrew, ← mul_sub, hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j ∈ Finset.range M, ∑ i ∈ B j,
          (fourier k (u i : UnitAddCircle) - fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle))‖
      ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range M, ∑ i ∈ B j,
          ‖fourier k (u i : UnitAddCircle) - fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖ := by
        gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range M, ∑ _i ∈ B j, (2 * π * (k.natAbs : ℝ) / M) := by
        gcongr with j _ i hi; exact norm_fourier_sub_bin_le (u i) k hM (Finset.mem_filter.1 hi).2
    _ = 2 * π * (k.natAbs : ℝ) / M := by
        rw [← Finset.sum_biUnion hdisj, hpart, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
          ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

private theorem tendsto_fourier_of_forall_fract_Ico {u : ℕ → ℝ}
    (hu : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (fractFreq u a b) atTop (𝓝 (b - a)))
    {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (2 * π * (k.natAbs : ℝ) / (ε / 2))
  set M : ℕ := max (k.natAbs + 1) M₀
  have hMgt : k.natAbs < M := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hMgt
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hMpos
  have hMlip : 2 * π * (k.natAbs : ℝ) / M < ε / 2 := by
    have hlt : 2 * π * (k.natAbs : ℝ) / (ε / 2) < M :=
      lt_of_lt_of_le hM₀ (by exact_mod_cast le_max_right (k.natAbs + 1) M₀)
    rwa [div_lt_iff₀ hMR, ← div_lt_iff₀' (half_pos hε)]
  have hbin_sum : Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range M,
      (fractFreq u ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M) n : ℂ) *
        fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.range M) fun j hj ↦ by
      have hreal := hu ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M) (by positivity)
        (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hMR.le)
        ((div_le_one hMR).2 (by exact_mod_cast Finset.mem_range.1 hj))
      rw [show ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = (M : ℝ)⁻¹ by
        push_cast; field_simp [hMR.ne']; ring] at hreal
      exact ((Complex.continuous_ofReal.tendsto _).comp hreal).mul_const
        (fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle))
    rwa [← Finset.mul_sum, sum_fourier_div_eq_zero hk hMgt, mul_zero] at hsum
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbin_sum (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right]
  calc _ ≤ _ := norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add ((norm_fourier_avg_sub_binned_le u k hMpos n).trans_lt hMlip)
        (by simpa [dist_zero_right] using hN n hn)
    _ = ε := add_halves ε

/-- **Uniform distribution modulo one.** For a real sequence `u : ℕ → ℝ`, equidistribution of its
classes in `UnitAddCircle`, convergence of half-open `Int.fract` interval frequencies to interval
lengths, and vanishing of all nonzero scalar Fourier averages are equivalent. -/
theorem uniformDistribution_mod_one_tfae (u : ℕ → ℝ) :
    List.TFAE [AsympEquidistributed (fun n ↦ (u n : UnitAddCircle))
        AddCircle.haarAddCircle.toProbabilityMeasure,
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        Tendsto (fun n : ℕ ↦ (((Finset.range (n + 1)).filter
          (fun i ↦ Int.fract (u i) ∈ Set.Ico a b)).card : ℝ) / (n + 1 : ℕ)) atTop (𝓝 (b - a)),
      ∀ k : ℤ, k ≠ 0 → Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle)) atTop (𝓝 0)] := by
  tfae_have 1 → 2 := fun h a b ha hab hb ↦ by
    classical
    have hfreq := h.tendsto_frequency (haarAddCircle_frontier_coe_image_Ico a b)
    rw [Measure.coe_toProbabilityMeasure, haarAddCircle_coe_image_Ico ha hb,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab)] at hfreq
    refine hfreq.congr fun n ↦ ?_
    congr 3; ext i; simp [coe_image_Ico_eq_preimage ha hb]
  tfae_have 2 → 3 := fun h _ hk ↦ tendsto_fourier_of_forall_fract_Ico h hk
  tfae_have 3 → 1 := (asympEquidistributed_haarAddCircle_iff _).2
  tfae_finish

end UniformModOne

end TauCeti
