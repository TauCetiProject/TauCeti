/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.Analysis.Normed.Ring.Ultra

import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.IntegralClosure.Quotient
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Power-bounded and topologically nilpotent elements of affinoid algebras

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, presented by a
surjection `π : K⟨X₁, …, Xₙ⟩ → A`, and let `A₀ = π(K⟨X₁, …, Xₙ⟩°)` be the image of the Gauss
unit ball. This file identifies the elements of supremum seminorm at most one with the elements
integral over `A₀`. Nilpotents are retained throughout: no reducedness is assumed.

For a complete ultrametric algebra norm on `A`, the presentation is continuous and `A₀` is a
bounded subring. Consequently the power-bounded elements of `A` are exactly the elements with
`|f|sup ≤ 1`, and the topologically nilpotent ones are exactly those with `|f|sup < 1`, or
equivalently `|f(x)| < 1` at every classical point `x`. In particular both sets depend only on
the algebra structure of `A`, not on the chosen norm. An open bounded subring `B` is the whole
unit ball `{f | |f|sup ≤ 1}` as soon as `B ⧸ ϖB` is reduced for some topologically nilpotent
element `ϖ ∈ B` regular in `A`, by the general criterion
`TauCeti.Huber.isPowerBounded_iff_mem_of_isReduced_quotient`.

Integrality is detected modulo every prime `𝔭` (`TauCeti.isIntegral_of_forall_isPrime`). A
Noether normalisation of the affinoid domain `A ⧸ 𝔭` adapted to the presentation sends the Gauss
unit ball into the image of `A₀`. The minimal polynomial of the residue of `f` over this Tate
algebra has coefficients of Gauss norm at most one, because the supremum seminorm is the spectral
value of the minimal polynomial; it therefore lifts to a monic polynomial over `A₀`.

## Main results

* `AlgHom.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`: for a Tate presentation `π`
  of `A`, an element is integral over `π(K⟨X⟩°)` if and only if `|f|sup ≤ 1`.
* `TauCeti.IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`: `A° = {f | |f|sup ≤ 1}`.
* `TauCeti.IsAffinoidAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one`:
  `A°° = {f | |f|sup < 1}`, with the pointwise form
  `TauCeti.IsAffinoidAlgebra.isTopologicallyNilpotent_iff_forall_pointNorm_lt_one`.
* `TauCeti.IsAffinoidAlgebra.mem_iff_supSeminorm_le_one_of_isReduced_quotient`: an open bounded
  subring `B` containing a topologically nilpotent regular element `ϖ` of `A` with `B ⧸ ϖB`
  reduced is `{f | |f|sup ≤ 1}`.
* `TauCeti.IsAffinoidAlgebra.isPowerBounded_mul_inverse_iff`: for a unit `c`, `b c⁻¹` is
  power-bounded if and only if `|b(x)| ≤ |c(x)|` at every classical point `x`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.2.3 and
  6.3.4.
* K. Fujiwara, F. Kato, *Foundations of Rigid Geometry I*, Appendix B, Proposition B.1.3(1).
-/

public section

open Polynomial

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " σ:max => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Modulo a prime `𝔭`, an element whose residue has supremum seminorm at most one becomes
integral over the image of the Gauss unit ball under a presentation. -/
private theorem isIntegral_quotient_of_supSeminorm_le_one {π : Tate σ →ₐ[K] A}
    (hπ : Function.Surjective π) (𝔭 : Ideal A) [𝔭.IsPrime] {f : A}
    (hf : supSeminorm K (Ideal.Quotient.mk 𝔭 f) ≤ 1) :
    IsIntegral ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) (Ideal.Quotient.mk 𝔭 f) := by
  classical
  let B := A ⧸ 𝔭
  have hB : IsAffinoidAlgebra K B := (isAffinoidAlgebra_tate.of_surjective π hπ).quotient 𝔭
  let π𝔭 := (Ideal.Quotient.mkₐ K 𝔭).comp π
  obtain ⟨n, g, hg, hgf, hball⟩ := π𝔭.exists_finite_injective_map_unitClosedBall_le
    ((Ideal.Quotient.mkₐ_surjective K 𝔭).comp hπ)
  let T := Tate (Fin n)
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K T B := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite T B := hgf
  have : Algebra.IsIntegral T B := Algebra.IsIntegral.of_finite T B
  have : FaithfulSMul T B := (faithfulSMul_iff_algebraMap_injective T B).mpr hg
  let x := Ideal.Quotient.mk 𝔭 f
  let p := minpoly T x
  have hp := minpoly.monic (Algebra.IsIntegral.isIntegral (R := T) x)
  -- Every coefficient of the minimal polynomial lies in the Gauss unit ball.
  have hcoeff (i : ℕ) : p.coeff i ∈ Subring.unitClosedBall T := by
    rw [Subring.mem_unitClosedBall]
    rcases lt_trichotomy i p.natDegree with hi | rfl | hi
    · have hle := (le_ciSup (Set.finite_range _).bddAbove (⟨i, hi⟩ : Fin p.natDegree)).trans
        ((hB.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := T) x).symm.le.trans hf)
      rw [← MvPowerSeries.supSeminorm_eq_norm]
      by_contra! h
      exact hle.not_gt (Real.one_lt_rpow h (one_div_pos.mpr (sub_pos.mpr (mod_cast hi))))
    · rw [hp.coeff_natDegree, norm_one]
    · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
      exact zero_le_one
  let A₀ := (Subring.unitClosedBall (Tate σ)).map π.toRingHom
  -- The minimal polynomial lifts to a monic polynomial over `A₀`.
  have hlifts : p.map (algebraMap T B) ∈ lifts (algebraMap A₀ B) := by
    refine (lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    obtain ⟨y, hy, hyx⟩ := hball ⟨p.coeff i, hcoeff i, rfl⟩
    exact ⟨⟨π y, y, hy, rfl⟩, by rw [coeff_map]; exact hyx⟩
  obtain ⟨q, hqp, -, hq⟩ := lifts_and_natDegree_eq_and_monic hlifts (hp.map _)
  exact ⟨q, hq, by rw [← eval_map, hqp, eval_map, ← aeval_def, minpoly.aeval]⟩

end TauCeti

namespace AlgHom

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [_root_.Finite σ] {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " σ:max => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- **Elements of supremum seminorm at most one are the integral elements over a presentation
ring.** For a Tate presentation `π` of an affinoid algebra, an element is integral over the image
under `π` of the Gauss unit ball if and only if its supremum seminorm is at most one. -/
theorem isIntegral_map_unitClosedBall_iff_supSeminorm_le_one (π : Tate σ →ₐ[K] A)
    (hπ : Function.Surjective π) {f : A} :
    IsIntegral ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) f ↔
      TauCeti.supSeminorm K f ≤ 1 := by
  have hA := TauCeti.isAffinoidAlgebra_tate.of_surjective π hπ
  refine ⟨fun ⟨q, hq, hqf⟩ ↦ ?_, fun hf ↦ ?_⟩
  · -- The coefficients of a monic equation over the presentation ring have `|·|sup ≤ 1`.
    have hp : (q.map (algebraMap _ A)).eval f = 0 := by rwa [eval_map]
    refine (hA.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero (hq.map _) hp).trans
      (Real.iSup_le (fun i ↦ Real.rpow_le_one (TauCeti.supSeminorm_nonneg _) ?_
        (one_div_nonneg.mpr (sub_nonneg.mpr (mod_cast i.2.le)))) zero_le_one)
    obtain ⟨y, hy, hyc⟩ := (q.coeff i).2
    have hyc : algebraMap _ A (q.coeff i) = π y := hyc.symm
    rw [coeff_map, hyc]
    exact (TauCeti.isAffinoidAlgebra_tate.supSeminorm_map_le hA π y).trans
      ((TauCeti.isAffinoidAlgebra_tate.supSeminorm_le_norm y).trans
        (Subring.mem_unitClosedBall.mp hy))
  · refine TauCeti.isIntegral_of_forall_isPrime fun 𝔭 _ ↦ ?_
    exact TauCeti.isIntegral_quotient_of_supSeminorm_le_one hπ 𝔭
      ((hA.supSeminorm_map_le (hA.quotient 𝔭) (Ideal.Quotient.mkₐ K 𝔭) f).trans hf)

end AlgHom

namespace TauCeti.IsAffinoidAlgebra

open Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Power-bounded elements of an affinoid algebra.** For every complete ultrametric algebra
norm on an affinoid algebra, an element is power-bounded if and only if its supremum seminorm is
at most one. -/
theorem isPowerBounded_iff_supSeminorm_le_one (hA : IsAffinoidAlgebra K A) {f : A} :
    Huber.IsPowerBounded f ↔ supSeminorm K f ≤ 1 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · -- The powers of `f` are norm-bounded, and `|f|sup ^ n ≤ ‖f ^ n‖`.
    obtain ⟨ϖ, hϖ⟩ := (Huber.IsTateRing.of_normedAlgebra K A).exists_isPseudoUniformizer
    obtain ⟨C, hC⟩ := hϖ.isBounded_iff_forall_norm_le.mp (Huber.isPowerBounded_iff.mp hf)
    by_contra! h
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop C |>.exists
    refine (hC _ ⟨n + 1, rfl⟩).not_gt (hn.trans_le ?_)
    calc supSeminorm K f ^ n ≤ supSeminorm K f ^ (n + 1) := pow_le_pow_right₀ h.le n.le_succ
      _ = supSeminorm K (f ^ (n + 1)) := (hA.supSeminorm_pow f n.succ_ne_zero).symm
      _ ≤ ‖f ^ (n + 1)‖ := hA.supSeminorm_le_norm _
  · -- `f` is integral over the image of the Gauss unit ball, which is power-bounded.
    obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
    have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
    have hπo := hA.isOpenQuotientMap π hπ
    have hle : (Subring.unitClosedBall _).map π.toRingHom ≤ Huber.powerBoundedSubring A := by
      rintro _ ⟨y, hy, rfl⟩
      exact Huber.mem_powerBoundedSubring.mpr <|
        (Huber.IsPowerBounded.of_norm_le_one (Subring.mem_unitClosedBall.mp hy)).map_of_isOpenMap
          hπo.continuous.continuousAt hπo.isOpenMap
    obtain ⟨q, hq, hqf⟩ := (π.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one hπ).mpr hf
    exact Huber.isPowerBounded_of_isIntegral
      ⟨q.map (Subring.inclusion hle), hq.map _, by rwa [eval₂_map]⟩

/-- **Topologically nilpotent elements of an affinoid algebra.** For every complete ultrametric
algebra norm on an affinoid algebra, an element is topologically nilpotent if and only if its
supremum seminorm is less than one. -/
theorem isTopologicallyNilpotent_iff_supSeminorm_lt_one (hA : IsAffinoidAlgebra K A) {f : A} :
    IsTopologicallyNilpotent f ↔ supSeminorm K f < 1 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · -- Some positive power of `f` has norm less than one.
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hf.eventually (Metric.ball_mem_nhds 0 one_pos))
    rw [← pow_lt_one_iff_of_nonneg (supSeminorm_nonneg f) N.succ_ne_zero,
      ← hA.supSeminorm_pow f N.succ_ne_zero]
    exact (hA.supSeminorm_le_norm _).trans_lt (mem_ball_zero_iff.mp (hN _ N.le_succ))
  · -- Write `f ^ n = c * u` with `|c| < 1` and `u` power-bounded.
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc0 hf
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact (hc1.trans (by simpa using hn)).false
    have hc : c ≠ 0 := norm_pos_iff.mp hc0
    have hu : Huber.IsPowerBounded (c⁻¹ • f ^ n) := by
      rw [hA.isPowerBounded_iff_supSeminorm_le_one, hA.supSeminorm_smul,
        hA.supSeminorm_pow f hn0, norm_inv, inv_mul_le_one₀ hc0]
      exact hn.le
    have hcn : IsTopologicallyNilpotent (algebraMap K A c) :=
      IsTopologicallyNilpotent.map (continuous_algebraMap K A)
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)
    refine IsTopologicallyNilpotent.of_pow hn0 ?_
    have hfu : f ^ n = c⁻¹ • f ^ n * algebraMap K A c := by
      rw [smul_mul_assoc, mul_comm, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hfu]
    exact hu.isTopologicallyNilpotent_mul hcn

/-- **Topologically nilpotent elements, pointwise.** For every complete ultrametric algebra norm on
an affinoid algebra, an element is topologically nilpotent if and only if it has absolute value
less than one at every classical point. -/
theorem isTopologicallyNilpotent_iff_forall_pointNorm_lt_one (hA : IsAffinoidAlgebra K A)
    {f : A} : IsTopologicallyNilpotent f ↔ ∀ x, pointNorm K x f < 1 := by
  rw [hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one, hA.supSeminorm_lt_iff one_pos]

/-- A power-bounded element lies in `A°°` exactly when its supremum seminorm is less than one. -/
theorem mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one (hA : IsAffinoidAlgebra K A)
    {a : Huber.powerBoundedSubring A} :
    a ∈ Huber.topologicallyNilpotentIdeal A ↔ supSeminorm K (a : A) < 1 := by
  rw [Huber.mem_topologicallyNilpotentIdeal, hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one]

/-- **A ring of definition with reduced quotient is the unit ball of the supremum seminorm.** Let
`B` be an open bounded subring of an affinoid algebra with a complete ultrametric algebra norm,
and `ϖ ∈ B` an element which is topologically nilpotent and left regular in `A`, for instance a
topologically nilpotent unit of `A`; it need not be a scalar. If `B ⧸ ϖB` is reduced, then
`B = A° = {f | |f|sup ≤ 1}`. -/
theorem mem_iff_supSeminorm_le_one_of_isReduced_quotient (hA : IsAffinoidAlgebra K A)
    {B : Subring A} (hBo : IsOpen (B : Set A)) (hBb : Huber.IsBounded (B : Set A)) {ϖ : B}
    (hϖ : IsTopologicallyNilpotent (ϖ : A)) (hϖr : IsLeftRegular (ϖ : A))
    (hred : IsReduced (B ⧸ Ideal.span {ϖ})) {f : A} :
    f ∈ B ↔ supSeminorm K f ≤ 1 := by
  rw [← Huber.isPowerBounded_iff_mem_of_isReduced_quotient hBo hBb hϖ hϖr hred,
    hA.isPowerBounded_iff_supSeminorm_le_one]

/-- **Power-bounded ratios.** In an affinoid algebra with a complete ultrametric algebra norm, for
a unit `c` the ratio `b c⁻¹` is power-bounded if and only if `|b(y)| ≤ |c(y)|` at every classical
point `y`. -/
theorem isPowerBounded_mul_inverse_iff (hA : IsAffinoidAlgebra K A) {b c : A} (hc : IsUnit c) :
    Huber.IsPowerBounded (b * Ring.inverse c) ↔
      ∀ y : MaximalSpectrum A, pointNorm K y b ≤ pointNorm K y c := by
  rw [hA.isPowerBounded_iff_supSeminorm_le_one, hA.supSeminorm_le_iff zero_le_one]
  refine forall_congr' fun y ↦ ?_
  have hpos : 0 < pointNorm K y c :=
    (pointNorm_nonneg c).lt_of_ne' (hA.isUnit_iff_forall_pointNorm_ne_zero.mp hc y)
  rw [hA.pointNorm_mul, hA.pointNorm_inverse y hc, ← div_eq_mul_inv, div_le_one hpos]

end TauCeti.IsAffinoidAlgebra
