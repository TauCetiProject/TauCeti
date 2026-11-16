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
the unit torus `UnitAddTorus d = (ℝ / ℤ)^d`.

A torus point `α : UnitAddTorus d` is irrational (`TauCeti.TorusIrrational α`) when no nonzero
integer frequency `k : d → ℤ` annihilates it (`∑ i, k i • α i ≠ 0`), equivalently
`UnitAddTorus.mFourier k α ≠ 1` for every `k ≠ 0`. In one dimension this is Mathlib's
`addOrderOf a = 0`.

Specializing the Fourier weak convergence criteria of
`TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier` to empirical measures yields:
* Weyl's criterion for an arbitrary limit probability measure on `AddCircle T` and `UnitAddTorus d`.
* Weyl's criterion for Haar probability (`TauCeti.weyl_criterion`).
* Reduction of torus equidistribution to one-dimensional integer projections
  (`TauCeti.asympEquidistributed_volume_iff_projections`).
* Characterization of total equidistribution on `UnitAddTorus d` by vanishing of all rational
  twists (`TauCeti.totallyAsympEquidistributed_volume_iff_rational_twists`), via discrete Fourier
  inversion on `ZMod q`.
* The classical equivalence for uniform distribution modulo one
  (`TauCeti.uniformDistribution_mod_one_tfae`): circle equidistribution, convergence of half-open
  `Int.fract` interval frequencies, and vanishing of all nonzero scalar Fourier averages.

## Main definitions

* `TauCeti.TorusIrrational`: no nonzero integer frequency annihilates `α : UnitAddTorus d`.

## Main results

* `TauCeti.torusIrrational_iff_mFourier`, `TauCeti.torusIrrational_unique_iff`,
  `TauCeti.TorusIrrational.zsmul`, `TauCeti.TorusIrrational.nsmul`: character, one-dimensional,
  and scaling properties of `TorusIrrational`.
* `TauCeti.asympEquidistributed_iff_forall_fourier`,
  `TauCeti.asympEquidistributed_haarAddCircle_iff`,
  `TauCeti.asympEquidistributed_iff_forall_mFourier`, `TauCeti.weyl_criterion`: Weyl criteria
  for circles and tori.
* `TauCeti.asympEquidistributed_volume_iff_projections`: torus equidistribution via scalar
  projections.
* `TauCeti.totallyAsympEquidistributed_volume_iff_rational_twists`: total equidistribution via
  rational twists.
* `TauCeti.uniformDistribution_mod_one_tfae`: uniform distribution modulo one.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Proposition 1.1.2, Corollary 1.1.3, Exercises 1.1.1 and 1.1.4).
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

/-- The first Fourier character on `UnitAddCircle` takes the value `1` only at `0`. -/
private theorem fourier_one_eq_one_iff (y : UnitAddCircle) : fourier 1 y = 1 ↔ y = 0 := by
  constructor
  · intro h
    refine AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0) ?_
    exact Subtype.ext (by simpa [fourier_one, AddCircle.toCircle_zero] using h)
  · rintro rfl
    exact fourier_eval_zero 1

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
  constructor
  · intro h hfin
    obtain ⟨m, hmpos, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
    refine h (fun _ ↦ (m : ℤ)) ?_ ?_
    · intro hk
      exact hmpos.ne' (Int.ofNat_eq_zero.1 (congrFun hk default))
    · simpa [Fintype.sum_unique] using hm0
  · intro hinf k hk hsum
    rw [Fintype.sum_unique] at hsum
    have hk0 : k default ≠ 0 := fun h0 ↦ hk (funext fun i ↦ Unique.eq_default i ▸ h0)
    refine hinf (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨(k default).natAbs, Int.natAbs_pos.2 hk0, ?_⟩)
    rcases Int.natAbs_eq (k default) with hpos | hneg
    · rw [← natCast_zsmul, ← hpos]; exact hsum
    · rw [← neg_eq_zero, ← natCast_zsmul, ← neg_zsmul, ← hneg]; exact hsum

/-- Scaling an irrational torus point by a nonzero integer preserves irrationality. -/
theorem TorusIrrational.zsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℤ}
    (hm : m ≠ 0) : TorusIrrational (m • α) := by
  intro k hk hsum
  have hmk : m • k ≠ 0 := by
    intro h0
    refine hk (funext fun i ↦ ?_)
    have hi := congrFun h0 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at hi
    exact hi.resolve_left hm
  refine hα (m • k) hmk ?_
  convert hsum using 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_zsmul, zsmul_comm]

/-- Scaling an irrational torus point by a nonzero natural number preserves irrationality. -/
theorem TorusIrrational.nsmul {α : UnitAddTorus d} (hα : TorusIrrational α) {m : ℕ}
    (hm : m ≠ 0) : TorusIrrational (m • α) := by
  rw [← natCast_zsmul]
  exact hα.zsmul (Nat.cast_ne_zero.2 hm)

end Irrational

section WeylCriteria

/-- Evaluate the integral of a continuous complex function against an empirical measure. -/
private theorem integral_empiricalMeasure_continuousMap {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (x : ℕ → X) (f : C(X, ℂ)) (n : ℕ) :
    ∫ y, f y ∂(TauCeti.Probability.empiricalMeasure x n : Measure X) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i) := by
  rw [TauCeti.Probability.integral_empiricalMeasure f.continuous.stronglyMeasurable,
    Complex.real_smul]
  push_cast
  rfl

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
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_zsmul]
  simp_rw [hproj]
  constructor
  · intro h k hk m hm
    refine h (m • k) fun h0 ↦ hk (funext fun i ↦ ?_)
    have hi := congrFun h0 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at hi
    exact hi.resolve_left hm
  · intro h k hk
    simpa only [one_smul] using h k hk 1 one_ne_zero

end WeylCriteria

section RationalTwists

variable {d : Type*} [Fintype d]

/-- Discrete Fourier orthogonality on `ZMod q` picks out a single residue class `r`. -/
private theorem inv_mul_sum_stdAddChar_eq_ite {q : ℕ} [NeZero q] (r i : ZMod q) :
    (q : ℂ)⁻¹ * ∑ a : ZMod q, (ZMod.stdAddChar (a * i) : ℂ) * ZMod.stdAddChar (-(r * a)) =
      if i = r then 1 else 0 := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply (Pi.single r (1 : ℂ))) i
  rw [ZMod.invDFT_apply] at hinv
  have hdft (a : ZMod q) : ZMod.dft (Pi.single r (1 : ℂ)) a = ZMod.stdAddChar (-(r * a)) := by
    rw [ZMod.dft_apply]
    simp [Pi.single_apply]
  simp only [hdft, smul_eq_mul, Pi.single_apply] at hinv
  exact hinv

/-- Express the sum along a residue class `q * j + r` (`r < q`) as a finite linear combination of
rationally twisted sums over `range (q * (m + 1))`. -/
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
    · exact Finset.sum_congr rfl fun j _ ↦ by simp
    · intro b _ hne
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hmod : (b.val : ZMod q) ≠ (r : ZMod q) := by
        intro h
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt hr] at h
        exact hne (Fin.ext h)
      simp [hmod]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  rw [hind]
  simp_rw [← inv_mul_sum_stdAddChar_eq_ite (r : ZMod q), mul_assoc, Finset.sum_mul,
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hchar : fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar (a * (i : ZMod q)) := by
    have hcast : (((a.val : ℤ) * (i : ℕ) : ℤ) : ZMod q) = a * (i : ZMod q) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [← hcast, fourier_coe_apply, ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  rw [hchar]
  ring

/-- Total equidistribution implies vanishing of every rationally twisted Fourier average. -/
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
    have hconst (j : ℕ) :
        fourier a ((((q * j + r : ℕ) : ℝ) / q : ℝ) : UnitAddCircle) =
          fourier a (((r : ℝ) / q : ℝ) : UnitAddCircle) := by
      have hdiv : (((q * j + r : ℕ) : ℝ) / q : ℝ) = (j : ℝ) + (r : ℝ) / q := by
        push_cast; field_simp [hqR.ne']
      have hj0 : ((j : ℝ) : UnitAddCircle) = 0 :=
        (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨(j : ℤ), by simp⟩
      rw [hdiv, AddCircle.coe_add, hj0, zero_add]
    have hr := ((weyl_criterion _).1 (totallyAsympEquidistributed_def.1 htot q r hq) k hk).mul_const
      (fourier a (((r : ℝ) / q : ℝ) : UnitAddCircle))
    rw [zero_mul] at hr
    refine hr.congr fun m ↦ ?_
    simp only [f, hconst, ← Finset.sum_mul, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast, mul_assoc]
  have havg := tendsto_cesaro_of_mod_classes (g := f) (L := fun _ ↦ (0 : ℂ)) hq hcls
  simp only [Finset.sum_const_zero, smul_zero, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast] at havg
  exact havg

/-- Vanishing of all rationally twisted Fourier averages implies equidistribution along every
arithmetic progression `j ↦ x (q * j + r)`. -/
private theorem tendsto_mod_class_of_rational_twists {x : ℕ → UnitAddTorus d}
    (htwist : ∀ k : d → ℤ, k ≠ 0 → ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1),
          UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
        atTop (𝓝 0))
    {q : ℕ} (hq : 0 < q) (r : ℕ) :
    AsympEquidistributed (fun j ↦ x (q * j + r)) volume.toProbabilityMeasure := by
  have hshift : (fun j ↦ x (q * j + r)) = fun j ↦ x (q * (j + r / q) + r % q) := by
    funext j
    congr 1
    rw [mul_add, add_assoc, Nat.div_add_mod r q]
  rw [hshift, asympEquidistributed_comp_add_iff (fun j ↦ x (q * j + r % q)) (r / q), weyl_criterion]
  intro k hk
  have hr : r % q < q := Nat.mod_lt r hq
  have : NeZero q := ⟨hq.ne'⟩
  have hsub_top : Tendsto (fun m : ℕ ↦ q * (m + 1) - 1) atTop atTop :=
    Filter.tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨b, fun m hm ↦ by
      have h1 : 1 * (m + 1) ≤ q * (m + 1) := Nat.mul_le_mul_right _ hq
      omega⟩
  have hterm (a : ZMod q) : Tendsto (fun m : ℕ ↦
      (ZMod.stdAddChar (-(((r % q : ℕ) : ZMod q) * a)) : ℂ) *
        (((q * (m + 1) : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ Finset.range (q * (m + 1)),
            UnitAddTorus.mFourier k (x i) *
              fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle))) atTop (𝓝 0) := by
    have ha := (htwist k hk q hq (a.val : ℤ)).comp hsub_top
    have hsucc (m : ℕ) : q * (m + 1) - 1 + 1 = q * (m + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m))
    simp only [Function.comp_def, hsucc] at ha
    simpa using ha.const_mul (ZMod.stdAddChar (-(((r % q : ℕ) : ZMod q) * a)) : ℂ)
  have hsum := tendsto_finsetSum Finset.univ fun a _ ↦ hterm a
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr fun m ↦ ?_
  rw [sum_mod_class_eq_rational_twists (fun i ↦ UnitAddTorus.mFourier k (x i)) hr m,
    Finset.mul_sum]
  simp only [Nat.cast_mul, mul_inv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- **Total equidistribution on `UnitAddTorus d` by rational twists.** A sequence is totally
equidistributed for Haar probability if and only if every nonzero Fourier character twisted by
every rational exponential `i ↦ e(a * i / q)` has Cesàro averages tending to `0`. -/
theorem totallyAsympEquidistributed_volume_iff_rational_twists (x : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributed x volume.toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∀ q : ℕ, 0 < q → ∀ a : ℤ,
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ Finset.range (n + 1),
            UnitAddTorus.mFourier k (x i) * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
          atTop (𝓝 0) := by
  refine ⟨fun htot _ hk _ hq a ↦
    tendsto_twisted_of_totallyAsympEquidistributed htot hk hq a, fun htwist ↦ ?_⟩
  rw [totallyAsympEquidistributed_def]
  exact fun _ r hq ↦ tendsto_mod_class_of_rational_twists htwist hq r

end RationalTwists

section UniformModOne

/-- The image of `[a, b)` in `UnitAddCircle` (`0 ≤ a ≤ b ≤ 1`) is the preimage of `[a, b)` under
`equivIco 1 0`. -/
private theorem coe_image_Ico_eq_preimage {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) =
      (fun θ : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ)) ⁻¹' Set.Ico a b := by
  ext θ
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hmem : t ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨ha.trans ht.1, by linarith [ht.2]⟩
    simpa [AddCircle.equivIco_coe_of_mem hmem] using ht
  · intro hθ
    exact ⟨(AddCircle.equivIco (1 : ℝ) 0 θ : ℝ), hθ, AddCircle.coe_equivIco⟩

/-- The Haar measure of the arc `[a, b)` (`0 ≤ a ≤ b ≤ 1`) on `UnitAddCircle` is `b - a`. -/
private theorem haarAddCircle_coe_image_Ico {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) =
      ENNReal.ofReal (b - a) := by
  have hvol : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  have hm : Measurable fun θ : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  rw [hvol, coe_image_Ico_eq_preimage ha hb, ← Measure.map_apply hm measurableSet_Ico,
    AddCircle.map_coe_equivIco_volume, Measure.restrict_apply measurableSet_Ico]
  have hinter : Set.Ico a b ∩ Set.Ico (0 : ℝ) (0 + 1) = Set.Ico a b :=
    Set.inter_eq_left.2 fun t ht ↦ ⟨ha.trans ht.1, by linarith [ht.2]⟩
  rw [hinter, Real.volume_Ico]

/-- A singleton on `UnitAddCircle` has Haar measure zero. -/
private theorem haarAddCircle_singleton (θ : UnitAddCircle) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) {θ} = 0 := by
  have hvol : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  have hm : Measurable fun z : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hpre : {θ} = (fun z : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)) ⁻¹'
      {(AddCircle.equivIco (1 : ℝ) 0 θ : ℝ)} := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)⟩
  rw [hvol, hpre, ← Measure.map_apply hm (measurableSet_singleton _),
    AddCircle.map_coe_equivIco_volume, Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null Set.inter_subset_left (measure_singleton _)

/-- The frontier of the image of `[a, b)` in `UnitAddCircle` is Haar-null. -/
private theorem haarAddCircle_frontier_coe_image_Ico (a b : ℝ) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
      (frontier (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b)) = 0 := by
  have hsub : frontier (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) ⊆
      {(a : UnitAddCircle), (b : UnitAddCircle)} := by
    have hcont : Continuous ((↑) : ℝ → UnitAddCircle) := continuous_quotient_mk'
    have hcl : closure (((↑) : ℝ → UnitAddCircle) '' Set.Ico a b) ⊆
        ((↑) : ℝ → UnitAddCircle) '' Set.Icc a b :=
      closure_minimal (Set.image_mono Set.Ico_subset_Icc_self) (isCompact_Icc.image hcont).isClosed
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
  exact measure_mono_null hsub (measure_union_null_iff.2
    ⟨haarAddCircle_singleton _, haarAddCircle_singleton _⟩)

/-- The geometric sum `∑ j < M, fourier k (j / M)` vanishes whenever `0 < |k| < M`. -/
private theorem sum_fourier_div_eq_zero {k : ℤ} {M : ℕ} (hk : k ≠ 0) (hM : k.natAbs < M) :
    ∑ j ∈ Finset.range M, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) = 0 := by
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hMpos.ne'
  set ζ : ℂ := fourier k (((1 : ℝ) / M : ℝ) : UnitAddCircle)
  have hpow (j : ℕ) : fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) = ζ ^ j := by
    simp only [ζ, fourier_coe_apply, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hζ_ne : ζ ≠ 1 := by
    intro h1
    have hzero : (((k : ℝ) / M : ℝ) : UnitAddCircle) = 0 := by
      refine (fourier_one_eq_one_iff _).1 ?_
      rw [← h1]; simp only [ζ, fourier_coe_apply]; congr 1; push_cast; ring
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hzero
    simp only [zsmul_eq_mul, mul_one] at hm
    have hkmZ : k = m * (M : ℤ) := by exact_mod_cast (div_eq_iff hMR).1 hm.symm
    have hdvd : M ∣ k.natAbs := by
      rw [hkmZ, Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_left M m.natAbs
    exact not_le_of_gt hM (Nat.le_of_dvd (Int.natAbs_pos.2 hk) hdvd)
  have hζM : ζ ^ M = 1 := by
    rw [← hpow M, div_self hMR, AddCircle.coe_period, fourier_eval_zero]
  simp_rw [hpow]
  rw [geom_sum_eq hζ_ne, hζM, sub_self, zero_div]

/-- Partition of `Finset.range (n + 1)` into `M` fractional-part bins `[j / M, (j + 1) / M)`. -/
private theorem fract_bin_partition (u : ℕ → ℝ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    let B (j : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter
      fun i ↦ Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)
    (Finset.range M).biUnion B = Finset.range (n + 1) ∧
      Set.PairwiseDisjoint (↑(Finset.range M) : Set ℕ) B := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hM
  dsimp only
  refine ⟨?_, ?_⟩
  · ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    refine ⟨fun ⟨_, _, hi, _⟩ ↦ hi, fun hi ↦ ?_⟩
    set j := ⌊(M : ℝ) * Int.fract (u i)⌋₊
    have : 0 ≤ Int.fract (u i) := Int.fract_nonneg (u i)
    have : Int.fract (u i) < 1 := Int.fract_lt_one (u i)
    refine ⟨j, (Nat.floor_lt (by positivity)).2 (by nlinarith), hi, ?_, ?_⟩
    · rw [div_le_iff₀ hMR, mul_comm]; exact Nat.floor_le (by positivity)
    · rw [lt_div_iff₀ hMR, mul_comm]; exact_mod_cast Nat.lt_floor_add_one _
  · intro j₁ _ j₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro i hi₁ hi₂
    have h1 := (Finset.mem_filter.1 hi₁).2
    have h2 := (Finset.mem_filter.1 hi₂).2
    have h12 : j₁ < j₂ + 1 := by
      exact_mod_cast (div_lt_div_iff_of_pos_right hMR).1 (h1.1.trans_lt h2.2)
    have h21 : j₂ < j₁ + 1 := by
      exact_mod_cast (div_lt_div_iff_of_pos_right hMR).1 (h2.1.trans_lt h1.2)
    omega

/-- Within a fractional-part bin `[j / M, (j + 1) / M)`, `fourier k x` differs from
`fourier k (j / M)` by at most `2 * π * |k| / M`. -/
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
    have hstep : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = (M : ℝ)⁻¹ := by
      push_cast; field_simp [hMR.ne']; ring
    linarith [hmem.2]
  have hkabs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  calc ‖fourier k ((Int.fract x : ℝ) : UnitAddCircle) -
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖
      ≤ 2 * π * |(k : ℝ)| * |Int.fract x - (j : ℝ) / M| := hlip
    _ ≤ 2 * π * |(k : ℝ)| * (M : ℝ)⁻¹ := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = 2 * π * (k.natAbs : ℝ) / M := by rw [hkabs, div_eq_mul_inv]

/-- Partitioning `range (n + 1)` into `M` equal fractional-part bins `[j / M, (j + 1) / M)`
approximates the Cesàro average of `fourier k` up to `2 * π * |k| / M`. -/
private theorem norm_fourier_avg_sub_binned_le (u : ℕ → ℝ) (k : ℤ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle) -
      ∑ j ∈ Finset.range M,
        (((((Finset.range (n + 1)).filter fun i ↦
          Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)).card : ℝ) /
            (n + 1 : ℕ) : ℝ) : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖ ≤
      2 * π * (k.natAbs : ℝ) / M := by
  let B (j : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter
    fun i ↦ Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)
  obtain ⟨hpart, hdisj⟩ := fract_bin_partition u hM n
  have hrew : ∑ j ∈ Finset.range M,
        (((B j).card : ℝ) / (n + 1 : ℕ) : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range M, ∑ _i ∈ B j,
        fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_const, nsmul_eq_mul, Complex.ofReal_natCast, div_eq_mul_inv]
    ring
  have hdiff : ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle) -
        ∑ j ∈ Finset.range M, ∑ _i ∈ B j, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) =
      ∑ j ∈ Finset.range M, (∑ i ∈ B j, fourier k (u i : UnitAddCircle) -
        ∑ _i ∈ B j, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_biUnion hdisj, hpart]
  have hrew' : ∑ j ∈ Finset.range M,
        (((((Finset.range (n + 1)).filter fun i ↦
          Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)).card : ℝ) /
            (n + 1 : ℕ) : ℝ) : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range M, ∑ _i ∈ B j,
        fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hrew
  rw [hrew', ← mul_sub, hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j ∈ Finset.range M,
          (∑ i ∈ B j, fourier k (u i : UnitAddCircle) -
            ∑ _i ∈ B j, fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle))‖
      ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range M, ∑ i ∈ B j,
          ‖fourier k (u i : UnitAddCircle) - fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [← Finset.sum_sub_distrib]
        exact norm_sum_le _ _
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range M, ∑ _i ∈ B j, (2 * π * (k.natAbs : ℝ) / M) := by
        gcongr with j _ i hi
        exact norm_fourier_sub_bin_le (u i) k hM (Finset.mem_filter.1 hi).2
    _ = 2 * π * (k.natAbs : ℝ) / M := by
        rw [← Finset.sum_biUnion hdisj, hpart, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
          ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- For `0 < |k| < M`, the `M`-bin approximation to the `k`-th Fourier average tends to `0`. -/
private theorem tendsto_binned_fourier_zero {u : ℕ → ℝ}
    (hu : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (fun n : ℕ ↦ (((Finset.range (n + 1)).filter
        (fun i ↦ Int.fract (u i) ∈ Set.Ico a b)).card : ℝ) / (n + 1 : ℕ))
        atTop (𝓝 (b - a)))
    {k : ℤ} {M : ℕ} (hk : k ≠ 0) (hM : k.natAbs < M) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range M,
      (((((Finset.range (n + 1)).filter fun i ↦
        Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)).card : ℝ) /
          (n + 1 : ℕ) : ℝ) : ℂ) *
        fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle)) atTop (𝓝 0) := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (lt_of_le_of_lt (Nat.zero_le _) hM)
  have hbin (j : ℕ) (hj : j ∈ Finset.range M) :
      Tendsto (fun n : ℕ ↦
        (((((Finset.range (n + 1)).filter fun i ↦
          Int.fract (u i) ∈ Set.Ico ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M)).card : ℝ) /
            (n + 1 : ℕ) : ℝ) : ℂ) *
          fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle))
        atTop (𝓝 (((M : ℝ)⁻¹ : ℂ) * fourier k (((j : ℝ) / M : ℝ) : UnitAddCircle))) := by
    have hreal := hu ((j : ℝ) / M) (((j + 1 : ℕ) : ℝ) / M) (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hMR.le)
      ((div_le_one hMR).2 (by exact_mod_cast Finset.mem_range.1 hj))
    have hdiff : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = (M : ℝ)⁻¹ := by
      push_cast; field_simp [hMR.ne']; ring
    rw [hdiff] at hreal
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast] using
      ((Complex.continuous_ofReal.tendsto _).comp hreal).mul_const _
  have hsum := tendsto_finsetSum (Finset.range M) hbin
  rw [← Finset.mul_sum, sum_fourier_div_eq_zero hk hM, mul_zero] at hsum
  exact hsum

/-- Uniform distribution of fractional parts in `[a, b)` implies vanishing of every nonzero scalar
Fourier average. -/
private theorem tendsto_fourier_of_forall_fract_Ico {u : ℕ → ℝ}
    (hu : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Tendsto (fun n : ℕ ↦ (((Finset.range (n + 1)).filter
        (fun i ↦ Int.fract (u i) ∈ Set.Ico a b)).card : ℝ) / (n + 1 : ℕ))
        atTop (𝓝 (b - a)))
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
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_binned_fourier_zero hu hk hMgt)
    (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right]
  have hsmall := hN n hn
  rw [dist_zero_right] at hsmall
  calc ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), fourier k (u i : UnitAddCircle)‖
      ≤ _ := norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add ((norm_fourier_avg_sub_binned_le u k hMpos n).trans_lt hMlip) hsmall
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
  tfae_have 1 → 2 := by
    intro h a b ha hab hb
    classical
    let E : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Set.Ico a b
    have hfreq := h.tendsto_frequency (haarAddCircle_frontier_coe_image_Ico a b)
    rw [Measure.coe_toProbabilityMeasure, haarAddCircle_coe_image_Ico ha hb,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab)] at hfreq
    refine hfreq.congr fun n ↦ ?_
    have hfilt : (Finset.range (n + 1)).filter (fun i ↦ (u i : UnitAddCircle) ∈ E) =
        (Finset.range (n + 1)).filter (fun i ↦ Int.fract (u i) ∈ Set.Ico a b) := by
      ext i
      simp [E, coe_image_Ico_eq_preimage ha hb]
    rw [hfilt]
  tfae_have 2 → 3 := fun h _ hk ↦ tendsto_fourier_of_forall_fract_Ico h hk
  tfae_have 3 → 1 := (asympEquidistributed_haarAddCircle_iff _).2
  tfae_finish

end UniformModOne

end TauCeti
