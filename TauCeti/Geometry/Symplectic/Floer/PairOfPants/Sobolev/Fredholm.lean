/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Core.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.End.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.Sobolev.UnitaryFrame

/-!
# The linearized operator of a pair of pants is Fredholm

Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let `u` be a map from the pair of pants `S = ℂ ∖ {0, 1}` to `F` whose three ends
converge to nondegenerate one-periodic orbits of the end Hamiltonians, for Floer data that are the
pair-of-pants data far out on the ends. The realization `D_u : W^{1,2}_0(S, F) → L²(S, F)` of the
linearized Floer operator for the cylindrical metric
(`TauCeti.SymplecticForm.floerConformalSobolevOperator`) has finite-dimensional kernel and closed
range (`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`).
This file proves that its cokernel is finite too, so that `D_u` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_pairOfPants`). The finiteness of
the cokernel comes from a right parametrix spliced from local inverses.

* **Splicing.** Let finitely many cutoffs `β_i` sum to one on `S`, each attached to an end chart
  `φ'_q` and carrying a bounded operator `Q_i` on the cylinder such that `D` applied to the
  transfer of `Q_i h` is, read in the chart, `β_i h + K_i h + E_i h` with `K_i` compact. If
  `∑ ‖E_i‖ < 1`, the sum `P` of the transferred `Q_i` satisfies `D P = 1 + K + E` with `K` compact
  and `‖E‖ < 1`, so the range of `D` has finite codimension
  (`TauCeti.Floer.cofg_range_jetOperator_comp_subtypeL_of_sum_eq_one`, through
  `ContinuousLinearMap.cofg_range_of_comp_eq_one_add_add`).
* **The ends.** On each end `q` the cutoff is `ψ(a + b |w - c_q|²)`, radial around the center
  `c_q` of the end, for the smooth transition function `ψ`. Read in the end chart it vanishes
  below the height `T - 1` and is one beyond the height `T + 1`, and the bounds required by the
  transfer along the chart hold uniformly in `T`. Far enough out, an inverse of the end model
  carries such a cutoff up to a compact operator and an operator of norm at most `1 / 4`
  (`exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`, in
  the namespace `TauCeti.SymplecticForm`). The three end cutoffs sum to one outside a compact
  annular region of `S`.
* **The core.** The leftover `1 - ∑ β_q` is supported in that compact region. A finite partition
  of unity (`IsCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one`) splits it into cutoffs
  supported in small neighbourhoods `U` of points `z₀`, on which `D_u` is close to a frozen model
  with the same principal part, so each carries an inverse up to a compact operator
  (`exists_mem_nhds_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`,
  in the namespace `TauCeti.SymplecticForm`). Only the principal part of the frozen model
  matters: it is the stationary cylinder operator over the orbit of the end at `0`, with the
  constant structure `J(z₀, u z₀)`, which is invertible
  (`TauCeti.SymplecticForm.isInvertible_stationarySobolevOperator_of_compatible`).

The invertibility of the stationary operators at the asymptotic orbits is where the unitary
trivialization, the `C³` end Hamiltonians, the periodicity of the orbits and the `C²` structures
along them enter. The index of `D_u` is not computed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends and their
  parametrices spliced from local inverses.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on parametrices spliced from inverses of the end models.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Topology Manifold

namespace TauCeti.Floer

open StripSobolev

section Splice

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One piece of a spliced parametrix, read on `S`: if `D` applied to the transfer
`β · (Q h ∘ ψ)` along the end chart `φ'_q` is, read in the chart, `β(φ'_q) h + K h + E h`, then
for `g ∈ L²(S)` and `h` its reading in the chart, `D (β · (Q h ∘ ψ))` minus the transfers of
`K h` and `E h` is `β g`. -/
private theorem jetOperator_endTransfer_sub_sub_ae_eq {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (q : Puncture) {β : ℝ × ℝ → ℝ} {Q : Lp W 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V}
    {K E : Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure}
    (hid : ∀ h, ((positiveEndChartLp q).symm (jetOperator
      (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))) :
        ℝ × ℝ → W) =ᵐ[stripMeasure] fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ)
    (g : Lp W 2 (volume.restrict thricePuncturedSphereReal)) :
    ⇑(jetOperator (volume.restrict thricePuncturedSphereReal) M
        (endTransfer q β (Q ((positiveEndChartLp q).symm g))) -
      positiveEndChartLp q (K ((positiveEndChartLp q).symm g)) -
      positiveEndChartLp q (E ((positiveEndChartLp q).symm g)))
      =ᵐ[volume.restrict thricePuncturedSphereReal] fun z ↦ β z • g z := by
  set h := (positiveEndChartLp q).symm g
  set X := jetOperator (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))
  have hX : X - positiveEndChartLp q (K h) - positiveEndChartLp q (E h) =
      positiveEndChartLp q ((positiveEndChartLp q).symm X - K h - E h) := by
    rw [map_sub, map_sub, LinearIsometryEquiv.apply_symm_apply]
  rw [hX]
  refine positiveEndChartLp_ae_eq_smul q g ?_
  filter_upwards [Lp.coeFn_sub ((positiveEndChartLp q).symm X - K h) (E h),
    Lp.coeFn_sub ((positiveEndChartLp q).symm X) (K h), hid h] with ζ h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃]
  abel

variable [CompleteSpace W]

/-- **Splicing a right parametrix on the pair of pants.** Let `D` be a first-order operator on `S`
with coefficient field `M` on conformal jets, realized on `W^{1,2}_0(S, V)`. Suppose `S` carries
finitely many cutoffs `β_i`, each attached to an end chart `φ'_(q i)` and admissible for the
transfer along it (`endTransfer_mem_H1`), with `∑ β_i = 1` on `S`, and that each comes with a
bounded operator `Q_i : L²(ℝ × S¹, W) → W^{1,2}(ℝ × S¹, V)` inverting `D` on the transferred
sections up to a compact operator `K_i` and an operator `E_i`:

`D (β_i · (Q_i h ∘ ψ)) = φ'_(q i)-transfer of (β_i(φ'_(q i)) h + K_i h + E_i h)`.

If `∑ ‖E_i‖ < 1`, then the range of `D` has finite codimension. The parametrix is
`P g = ∑ β_i · (Q_i h_i ∘ ψ_i)` for the readings `h_i` of `g` in the charts: `D P = 1 + K + E`
with `K` compact and `‖E‖ < 1` (`ContinuousLinearMap.cofg_range_of_comp_eq_one_add_add`). -/
theorem cofg_range_jetOperator_comp_subtypeL_of_sum_eq_one
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} {ι : Type*} [Fintype ι] (q : ι → Puncture)
    {β : ι → ℝ × ℝ → ℝ} (hβ : ∀ i, ContDiff ℝ 2 (β i))
    (hβS : ∀ i, ∀ z ∈ tsupport (β i), Complex.equivRealProdCLM.symm z ≠ (q i).endCenter →
      z ∈ thricePuncturedSphereReal)
    (hB : ∀ i, ∃ B, ∀ z, Complex.equivRealProdCLM.symm z ≠ (q i).endCenter →
      |β i z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - (q i).endCenter‖ *
        (√(cylindricalWeight z) * |β i z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - (q i).endCenter‖ * ‖fderiv ℝ (β i) z‖ ≤ B)
    (hsum : ∀ z ∈ thricePuncturedSphereReal, ∑ i, β i z = 1)
    (Q : ι → Lp W 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V)
    (K E : ι → Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure)
    (hK : ∀ i, IsCompactOperator (K i)) (hE : ∑ i, ‖E i‖ < 1)
    (hid : ∀ i h, ((positiveEndChartLp (q i)).symm (jetOperator
      (volume.restrict thricePuncturedSphereReal) M (endTransfer (q i) (β i) (Q i h))) :
        ℝ × ℝ → W) =ᵐ[stripMeasure]
          fun ζ ↦ β i (positiveEndChart (q i) ζ) • h ζ + K i h ζ + E i h ζ) :
    ((jetOperator (volume.restrict thricePuncturedSphereReal) M).comp
      (ConformalSobolev.H1 V _ cylindricalWeight).subtypeL).range.CoFG := by
  classical
  set μS := volume.restrict thricePuncturedSphereReal
  set H := ConformalSobolev.H1 V thricePuncturedSphereReal cylindricalWeight
  set D := (jetOperator μS M).comp H.subtypeL
  -- The `L²` isometries along the end charts and their inverses, as operators.
  set tr : ι → Lp W 2 stripMeasure →L[ℝ] Lp W 2 μS := fun i ↦
    (positiveEndChartLp (W := W) (q i)).toContinuousLinearEquiv.toContinuousLinearMap
  set rd : ι → Lp W 2 μS →L[ℝ] Lp W 2 stripMeasure := fun i ↦
    (positiveEndChartLp (W := W) (q i)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- The parametrix `P g = ∑ β_i · (Q_i (rd_i g) ∘ ψ_i)`.
  choose B hB using hB
  set A : ι → Lp W 2 μS →L[ℝ] Lp (V × V × V) 2 μS := fun i ↦
    (endTransfer (q i) (β i)).comp ((CylinderSobolev.H1 V).subtypeL.comp ((Q i).comp (rd i)))
  have hA (g) : (∑ i, A i) g ∈ H := by
    rw [FunLike.coe_sum, Finset.sum_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      endTransfer_mem_H1 (q i) (hβ i) (hβS i) (hB i) (Q i _).property
  set P : Lp W 2 μS →L[ℝ] H := (∑ i, A i).codRestrict H hA
  -- `D P = 1 + K' + E'` with `K'` compact and `‖E'‖ < 1`.
  set K' : Lp W 2 μS →L[ℝ] Lp W 2 μS := ∑ i, (tr i).comp ((K i).comp (rd i))
  set E' : Lp W 2 μS →L[ℝ] Lp W 2 μS := ∑ i, (tr i).comp ((E i).comp (rd i))
  have hK' : IsCompactOperator K' :=
    (compactOperator (RingHom.id ℝ) (Lp W 2 μS) (Lp W 2 μS)).sum_mem fun i _ ↦
      ((hK i).comp_clm (rd i)).clm_comp (tr i)
  have hE' : ‖E'‖ < 1 := by
    refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) hE)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_of_le_one_left (norm_nonneg _)
      (positiveEndChartLp (W := W) (q i)).toLinearIsometry.norm_toContinuousLinearMap_le).trans ?_
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (positiveEndChartLp (W := W) (q i)).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
  have hDP : D.comp P = 1 + K' + E' := by
    ext1 g
    -- The pieces, minus their `K` and `E` parts, add up to `∑ β_i g = g`.
    have hg : ∑ i, (jetOperator μS M (A i g) - tr i (K i (rd i g)) - tr i (E i (rd i g))) = g := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_finsetSum Finset.univ fun i ↦
          jetOperator μS M (A i g) - tr i (K i (rd i g)) - tr i (E i (rd i g)),
        ae_all_iff.2 fun i ↦ jetOperator_endTransfer_sub_sub_ae_eq (q i) (hid i) g,
        ae_restrict_mem isOpen_thricePuncturedSphereReal.measurableSet] with z h₁ h₂ hz
      rw [h₁, Finset.sum_apply]
      refine (Finset.sum_congr rfl fun i _ ↦ h₂ i).trans ?_
      rw [← Finset.sum_smul, hsum z hz, one_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sub_sub, sub_eq_iff_eq_add] at hg
    simp only [D, P, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.coe_codRestrict_apply, FunLike.coe_sum, Finset.sum_apply, map_sum]
    rw [hg]
    simp [K', E']
    abel
  exact D.cofg_range_of_comp_eq_one_add_add hDP hK' hE'

end Splice

/-! ### Cutoffs near the punctures -/

section Cutoff

/-- The distance from a point of the positive end chart of `q` to the center of the end:
`|φ'_q(s, t) - c_q| = |b_q| exp (∓2πs)`, with the sign of the end. -/
theorem norm_equivRealProdCLM_symm_positiveEndChart_sub_endCenter (q : Puncture) (ζ : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ =
      ‖q.endScale‖ * exp (-(2 * π * (q.endSign * ζ.1))) := by
  rw [positiveEndChart_apply, equivRealProdCLM_symm_endChart, norm_cylindricalEndLift_sub_endCenter]
  simp

/-- A radial cutoff around `c`: `ψ(a + b |w - c|²)` for the smooth transition function `ψ`. -/
private def radialCutoff (c : ℂ) (a b : ℝ) (z : ℝ × ℝ) : ℝ :=
  smoothTransition (a + b * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2)

private theorem contDiff_radialCutoff (c : ℂ) (a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (radialCutoff c a b) :=
  smoothTransition.contDiff.comp (contDiff_const.add (contDiff_const.mul
    ((contDiff_norm_sq ℝ).comp (Complex.equivRealProdCLM.symm.contDiff.sub contDiff_const))))

private theorem abs_radialCutoff_le_one (c : ℂ) (a b : ℝ) (z : ℝ × ℝ) :
    |radialCutoff c a b z| ≤ 1 :=
  smoothTransition.abs_le_one _

private theorem hasFDerivAt_radialCutoff (c : ℂ) (a b : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (radialCutoff c a b)
      (deriv smoothTransition (a + b * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2) •
        b • (2 • (innerSL ℝ (Complex.equivRealProdCLM.symm z - c)).comp
          (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z :=
  (((Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).hasFDerivAt.sub_const c).norm_sq.const_mul
    b |>.const_add a).smoothTransition

/-- A radial cutoff has derivative zero where its argument lies outside `(0, 1)`, since `ψ'`
vanishes there. -/
private theorem fderiv_radialCutoff_eq_zero {c : ℂ} {a b : ℝ} {z : ℝ × ℝ}
    (h : a + b * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 ≤ 0 ∨
      1 ≤ a + b * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2) :
    fderiv ℝ (radialCutoff c a b) z = 0 := by
  rw [(hasFDerivAt_radialCutoff c a b z).fderiv]
  rcases h with h | h
  · rw [smoothTransition.deriv_of_nonpos h, zero_smul]
  · rw [smoothTransition.deriv_of_one_le h, zero_smul]

/-- The derivative of a radial cutoff around `c` decays like `|w - c|⁻¹`, with a constant depending
only on `a`. -/
private theorem norm_mul_norm_fderiv_radialCutoff_le {L : ℝ}
    (hL : ∀ x, ‖deriv smoothTransition x‖ ≤ L) (c : ℂ) (a b : ℝ) (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm z - c‖ * ‖fderiv ℝ (radialCutoff c a b) z‖ ≤
      L * (2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * (1 + |a|)) := by
  set w := Complex.equivRealProdCLM.symm z - c
  set g := a + b * ‖w‖ ^ 2
  set Φ := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hR : 0 ≤ L * (2 * ‖Φ‖ * (1 + |a|)) := by positivity
  by_cases hg : g ≤ 0 ∨ 1 ≤ g
  · rw [fderiv_radialCutoff_eq_zero hg, norm_zero, mul_zero]
    exact hR
  push Not at hg
  -- Where `ψ'` does not vanish, `0 < g < 1`, so `|b| |w - c|² ≤ 1 + |a|`.
  have hbw : |b| * ‖w‖ ^ 2 ≤ 1 + |a| := by
    have : |b * ‖w‖ ^ 2| ≤ 1 + |a| := by
      rw [abs_le]
      constructor <;> cases abs_cases a <;> nlinarith [hg.1, hg.2]
    rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 2)] at this
  rw [(hasFDerivAt_radialCutoff c a b z).fderiv]
  have hnorm : ‖deriv smoothTransition g • b • (2 • (innerSL ℝ w).comp Φ)‖ ≤
      L * (|b| * (2 * (‖w‖ * ‖Φ‖))) := by
    have h₂ : ‖(2 : ℕ) • (innerSL ℝ w).comp Φ‖ ≤ 2 * (‖w‖ * ‖Φ‖) := by
      refine norm_nsmul_le.trans ?_
      rw [Nat.cast_ofNat]
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by rw [innerSL_apply_norm])
    rw [norm_smul, norm_smul, ← Real.norm_eq_abs b]
    exact mul_le_mul (hL _) (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)) (by positivity) hL0
  calc ‖w‖ * ‖deriv smoothTransition g • b • (2 • (innerSL ℝ w).comp Φ)‖
      ≤ ‖w‖ * (L * (|b| * (2 * (‖w‖ * ‖Φ‖)))) := by gcongr
    _ = L * (2 * ‖Φ‖ * (|b| * ‖w‖ ^ 2)) := by ring
    _ ≤ L * (2 * ‖Φ‖ * (1 + |a|)) := by gcongr

/-- A radial cutoff is supported where its argument is nonnegative. -/
private theorem tsupport_radialCutoff_subset (c : ℂ) (a b : ℝ) :
    tsupport (radialCutoff c a b) ⊆
      {z | 0 ≤ a + b * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2} := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_le continuous_const (by fun_prop))
  by_contra h
  exact hz (smoothTransition.zero_of_nonpos (not_le.1 h).le)

private theorem two_lt_exp_four_pi : 2 < exp (4 * π) := by
  nlinarith [Real.add_one_le_exp (4 * π), Real.two_le_pi]

/-- The constant term of the cutoff of the end `q`. -/
private def endA (q : Puncture) : ℝ := if q = inf then -1 else 2

/-- The coefficient of the squared distance to the center in the cutoff of the end `q` at the
height `T`. -/
private def endB (q : Puncture) (T : ℝ) : ℝ :=
  if q = inf then exp (-(4 * π * T)) / 4 else -(4 * exp (4 * π * T))

/-- The cutoff of the end `q` at the height `T`: it vanishes below the height `T - 1` of the end
and is one beyond the height `T + 1`. -/
private def endCutoff (q : Puncture) (T : ℝ) : ℝ × ℝ → ℝ :=
  radialCutoff q.endCenter (endA q) (endB q T)

private theorem contDiff_endCutoff (q : Puncture) (T : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (endCutoff q T) :=
  contDiff_radialCutoff _ _ _

private theorem abs_endA_le (q : Puncture) : |endA q| ≤ 2 := by
  unfold endA
  split_ifs <;> norm_num

/-- Read in the positive end chart of an input end, the argument of the end cutoff is
`2 - exp (4π (T - s))`. -/
private theorem endArg_positiveEndChart_of_ne_inf {q : Puncture} (hq : q ≠ inf) (T : ℝ)
    (ζ : ℝ × ℝ) :
    endA q + endB q T *
        ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ ^ 2 =
      2 - exp (4 * π * (T - ζ.1)) := by
  have hexp : exp (4 * π * T) * exp (-(2 * π * ζ.1)) ^ 2 = exp (4 * π * (T - ζ.1)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [norm_equivRealProdCLM_symm_positiveEndChart_sub_endCenter]
  cases q
  · simp only [endA, endB, reduceCtorEq, ite_false, endSign_zero, endScale_zero, one_mul]
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linear_combination (-1 : ℝ) * hexp
  · simp only [endA, endB, reduceCtorEq, ite_false, endSign_one, endScale_one, one_mul]
    rw [show ‖-(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linear_combination (-1 : ℝ) * hexp
  · exact absurd rfl hq

/-- Read in the positive end chart of the output end, the argument of the end cutoff is
`exp (4π (s - T)) - 1`. -/
private theorem endArg_positiveEndChart_inf (T : ℝ) (ζ : ℝ × ℝ) :
    endA inf + endB inf T *
        ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) - inf.endCenter‖ ^ 2 =
      exp (4 * π * (ζ.1 - T)) - 1 := by
  have hexp : exp (-(4 * π * T)) * exp (-(2 * π * (-1 * ζ.1))) ^ 2 =
      exp (4 * π * (ζ.1 - T)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [norm_equivRealProdCLM_symm_positiveEndChart_sub_endCenter]
  simp only [endA, endB, ite_true, endSign_inf, endScale_inf]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  linear_combination hexp

/-- Below the height `T - 1` of the end, the argument of the end cutoff is negative. -/
private theorem endArg_positiveEndChart_neg (q : Puncture) {T : ℝ} {ζ : ℝ × ℝ}
    (h : ζ.1 ≤ T - 1) :
    endA q + endB q T *
      ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ ^ 2 < 0 := by
  have h4 := two_lt_exp_four_pi
  by_cases hq : q = inf
  · subst hq
    rw [endArg_positiveEndChart_inf]
    have : exp (4 * π * (ζ.1 - T)) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  · rw [endArg_positiveEndChart_of_ne_inf hq]
    have : exp (4 * π) ≤ exp (4 * π * (T - ζ.1)) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    linarith

/-- Beyond the height `T + 1` of the end, the argument of the end cutoff is at least one. -/
private theorem one_le_endArg_positiveEndChart (q : Puncture) {T : ℝ} {ζ : ℝ × ℝ}
    (h : T + 1 ≤ ζ.1) :
    1 ≤ endA q + endB q T *
      ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ ^ 2 := by
  have h4 := two_lt_exp_four_pi
  by_cases hq : q = inf
  · subst hq
    rw [endArg_positiveEndChart_inf]
    have : exp (4 * π) ≤ exp (4 * π * (ζ.1 - T)) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    linarith
  · rw [endArg_positiveEndChart_of_ne_inf hq]
    have : exp (4 * π * (T - ζ.1)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith

private theorem endCutoff_positiveEndChart_eq_zero (q : Puncture) {T : ℝ} {ζ : ℝ × ℝ}
    (h : ζ.1 ≤ T - 1) : endCutoff q T (positiveEndChart q ζ) = 0 :=
  smoothTransition.zero_of_nonpos (endArg_positiveEndChart_neg q h).le

private theorem fderiv_endCutoff_positiveEndChart_eq_zero (q : Puncture) {T : ℝ} {ζ : ℝ × ℝ}
    (h : ζ.1 ≤ T - 1 ∨ T + 1 ≤ ζ.1) : fderiv ℝ (endCutoff q T) (positiveEndChart q ζ) = 0 :=
  fderiv_radialCutoff_eq_zero (h.imp (fun h ↦ (endArg_positiveEndChart_neg q h).le)
    (one_le_endArg_positiveEndChart q))

/-- The end cutoff of `q` at the height `T` lives beyond the height `T - 1` of the end. -/
private theorem sub_one_lt_fst_positiveEndCoord_of_mem_tsupport (q : Puncture) {T : ℝ}
    {z : ℝ × ℝ} (hz : z ∈ tsupport (endCutoff q T))
    (hc : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    T - 1 < (positiveEndCoord q z).1 := by
  have h := tsupport_radialCutoff_subset _ _ _ hz
  rw [mem_ofPred_eq, ← positiveEndChart_positiveEndCoord q hc] at h
  by_contra hs
  exact (endArg_positiveEndChart_neg q (not_lt.1 hs)).not_ge h

/-- For `T ≥ 1`, the end cutoff is supported in `S` away from the center of its end. -/
private theorem mem_thricePuncturedSphereReal_of_mem_tsupport_endCutoff (q : Puncture) {T : ℝ}
    (hT : 1 ≤ T) {z : ℝ × ℝ} (hz : z ∈ tsupport (endCutoff q T))
    (hc : Complex.equivRealProdCLM.symm z ≠ q.endCenter) : z ∈ thricePuncturedSphereReal := by
  rw [← positiveEndChart_positiveEndCoord q hc]
  exact positiveEndChart_mem_thricePuncturedSphereReal
    (by linarith [sub_one_lt_fst_positiveEndCoord_of_mem_tsupport q hz hc])

/-- The bounds on the end cutoffs required by the transfer along the end chart, uniformly in the
height `T ≥ 1`. -/
private theorem endCutoff_bound {L : ℝ} (hL : ∀ x, ‖deriv smoothTransition x‖ ≤ L) (q : Puncture)
    {T : ℝ} (hT : 1 ≤ T) {z : ℝ × ℝ} (hc : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    |endCutoff q T z| ≤ 3 + L * (2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * 3) ∧
      ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          (√(cylindricalWeight z) * |endCutoff q T z|) ≤
        3 + L * (2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * 3) ∧
      ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ (endCutoff q T) z‖ ≤
        3 + L * (2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * 3) := by
  set Φ := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hLΦ : 0 ≤ L * (2 * ‖Φ‖ * 3) := by positivity
  have h1 := abs_radialCutoff_le_one q.endCenter (endA q) (endB q T) z
  refine ⟨by unfold endCutoff; linarith, ?_, ?_⟩
  · by_cases h0 : endCutoff q T z = 0
    · rw [h0, abs_zero, mul_zero, mul_zero]
      positivity
    -- On its support the cutoff lives on the part `s ≥ 0` of the end, where `|w - c_q|² ρ ≤ 5`.
    have hzt : z ∈ tsupport (endCutoff q T) := subset_tsupport _ h0
    have hs := sub_one_lt_fst_positiveEndCoord_of_mem_tsupport q hzt hc
    have hρ := norm_sub_endCenter_sq_mul_cylindricalWeight_le q
      (mem_thricePuncturedSphereReal_of_mem_tsupport_endCutoff q hT hzt hc) (by linarith)
    have hsq : ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * √(cylindricalWeight z) ≤ 3 := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
    calc ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
          (√(cylindricalWeight z) * |endCutoff q T z|)
        = ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * √(cylindricalWeight z) *
            |endCutoff q T z| := by ring
      _ ≤ 3 * 1 := mul_le_mul hsq (by unfold endCutoff; exact h1) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  · refine (norm_mul_norm_fderiv_radialCutoff_le hL q.endCenter (endA q) (endB q T) z).trans ?_
    have := abs_endA_le q
    have : L * (2 * ‖Φ‖ * (1 + |endA q|)) ≤ L * (2 * ‖Φ‖ * 3) := by gcongr; linarith
    linarith

/-! ### The compact core -/

/-- The closed region `m ≤ |w|²`, `m ≤ |w - 1|²`, `|w|² ≤ M` of the plane: for `m > 0`, a compact
subset of `S`. -/
private def annularRegion (m M : ℝ) : Set (ℝ × ℝ) :=
  {z | m ≤ ‖Complex.equivRealProdCLM.symm z‖ ^ 2 ∧ m ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ^ 2 ∧
    ‖Complex.equivRealProdCLM.symm z‖ ^ 2 ≤ M}

private theorem isCompact_annularRegion (m M : ℝ) : IsCompact (annularRegion m M) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [annularRegion, ofPred_and]
    exact (isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const))
  · refine (Metric.isBounded_closedBall (x := 0)
      (r := ‖(Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)‖ * √M)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hw : ‖Complex.equivRealProdCLM.symm z‖ ≤ √M :=
      Real.le_sqrt_of_sq_le hz.2.2
    calc ‖z‖ = ‖(Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) (Complex.equivRealProdCLM.symm z)‖ := by
          simp
      _ ≤ _ := ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _).trans (by gcongr)

private theorem annularRegion_subset {m : ℝ} (hm : 0 < m) (M : ℝ) :
    annularRegion m M ⊆ thricePuncturedSphereReal := by
  intro z hz
  refine mem_thricePuncturedSphereReal_iff.2 ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := hz.1
    rw [h, norm_zero] at this
    linarith [pow_two_nonneg (0 : ℝ)]
  · have := hz.2.1
    rw [h, sub_self, norm_zero] at this
    linarith [pow_two_nonneg (0 : ℝ)]

/-- Outside the core region `annularRegion (exp (-4πT) / 4) (9 exp (4πT))`, one end cutoff is one
and the others vanish, so the end cutoffs sum to one. -/
private theorem sum_endCutoff_eq_one {T : ℝ} (hT : 1 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ annularRegion (exp (-(4 * π * T)) / 4) (9 * exp (4 * π * T))) :
    ∑ q, endCutoff q T z = 1 := by
  set w := Complex.equivRealProdCLM.symm z
  set X := exp (-(4 * π * T))
  set E := exp (4 * π * T)
  have hE : 2 ≤ E := two_lt_exp_four_pi.le.trans (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))
  have hXE : X * E = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hX : 0 < X := Real.exp_pos _
  have hX2 : X ≤ 1 / 2 := by nlinarith
  have hw₀ := norm_nonneg w
  have hw₁ := norm_nonneg (w - 1)
  have ht₁ : ‖w‖ - 1 ≤ ‖w - 1‖ := by simpa using norm_sub_norm_le w 1
  have ht₂ : 1 - ‖w‖ ≤ ‖w - 1‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le (1 : ℂ) w
  rw [Puncture.sum_univ]
  simp only [endCutoff, radialCutoff, endA, endB, reduceCtorEq, ite_false, ite_true, endCenter_zero,
    endCenter_one, endCenter_inf, sub_zero]
  simp only [annularRegion, mem_ofPred_eq, not_and_or, not_le] at hz
  rcases hz with h | h | h
  · -- Near `0`: the cutoff of the end at `0` is one.
    have hw : ‖w‖ < 1 / 2 := by nlinarith
    rw [smoothTransition.one_of_one_le (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith)]
    norm_num
  · -- Near `1`: the cutoff of the end at `1` is one.
    have hw : ‖w - 1‖ < 1 / 2 := by nlinarith
    rw [smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.one_of_one_le (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith)]
    norm_num
  · -- Far out: the cutoff of the end at `∞` is one.
    have hw : 3 < ‖w‖ := by nlinarith
    rw [smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.one_of_one_le (by nlinarith)]
    norm_num

/-- The function `1 - ∑_q β_q` left over by the end cutoffs at the height `T ≥ 1` is supported in
the core region. -/
private theorem tsupport_one_sub_sum_endCutoff_subset {T : ℝ} (hT : 1 ≤ T) :
    tsupport (fun z ↦ 1 - ∑ q, endCutoff q T z) ⊆
      annularRegion (exp (-(4 * π * T)) / 4) (9 * exp (4 * π * T)) :=
  closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (by simp [sum_endCutoff_eq_one hT h]))
    (isCompact_annularRegion _ _).isClosed

/-- The core region `annularRegion (exp (-4πT) / 4) (9 exp (4πT))` has an open neighbourhood
inside the compact region `annularRegion (exp (-4πT) / 16) (36 exp (4πT))`. -/
private theorem exists_isOpen_annularRegion_subset (T : ℝ) :
    ∃ O, IsOpen O ∧ annularRegion (exp (-(4 * π * T)) / 4) (9 * exp (4 * π * T)) ⊆ O ∧
      O ⊆ annularRegion (exp (-(4 * π * T)) / 16) (36 * exp (4 * π * T)) := by
  have hX : 0 < exp (-(4 * π * T)) := Real.exp_pos _
  have hE : 0 < exp (4 * π * T) := Real.exp_pos _
  refine ⟨{z | exp (-(4 * π * T)) / 16 < ‖Complex.equivRealProdCLM.symm z‖ ^ 2 ∧
    exp (-(4 * π * T)) / 16 < ‖Complex.equivRealProdCLM.symm z - 1‖ ^ 2 ∧
      ‖Complex.equivRealProdCLM.symm z‖ ^ 2 < 36 * exp (4 * π * T)}, ?_, fun z hz ↦ ?_,
    fun z hz ↦ ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩⟩
  · simp only [ofPred_and]
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const))
  · obtain ⟨h₁, h₂, h₃⟩ := hz
    exact ⟨by linarith, by linarith, by linarith⟩

/-- Read in the positive end chart of the end at `0`, the region
`annularRegion (exp (-4πT) / 16) (36 exp (4πT))` lies over the heights `-T - 3 < s < T + 1`. -/
private theorem positiveEndChart_zero_notMem_annularRegion {T : ℝ} {ζ : ℝ × ℝ}
    (h : ζ.1 ≤ -T - 3 ∨ T + 1 ≤ ζ.1) :
    positiveEndChart zero ζ ∉ annularRegion (exp (-(4 * π * T)) / 16) (36 * exp (4 * π * T)) := by
  have hn := norm_equivRealProdCLM_symm_positiveEndChart_sub_endCenter zero ζ
  simp only [endCenter_zero, sub_zero, endSign_zero, endScale_zero, one_mul] at hn
  rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hn
  have hsq : ‖Complex.equivRealProdCLM.symm (positiveEndChart zero ζ)‖ ^ 2 =
      exp (-(4 * π * ζ.1)) / 4 := by
    rw [hn, mul_pow, sq (exp _), ← Real.exp_add]
    ring_nf
  simp only [annularRegion, mem_ofPred_eq, hsq, not_and_or, not_le]
  have hπ := Real.two_le_pi
  rcases h with h | h
  · -- Far below, the point lies beyond `|w|² = 36 exp (4πT)`.
    right; right
    have h12 : 313 ≤ exp (12 * π) := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (x := 12 * π) (by positivity)]
    have : exp (4 * π * T) * exp (12 * π) ≤ exp (-(4 * π * ζ.1)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    nlinarith [Real.exp_pos (4 * π * T)]
  · -- Far above, the point lies within `|w|² = exp (-4πT) / 16` of `0`.
    left
    have h4 : 41 ≤ exp (4 * π) := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (x := 4 * π) (by positivity)]
    have : exp (-(4 * π * ζ.1)) * exp (4 * π) ≤ exp (-(4 * π * T)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    nlinarith [Real.exp_pos (-(4 * π * ζ.1)), Real.exp_pos (-(4 * π * T))]

/-- A `C¹` function supported in a compact subset of `S` satisfies the bounds required by the
transfer along every end chart. -/
private theorem exists_bound_of_tsupport_subset {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : K ⊆ thricePuncturedSphereReal)
    (hβK : tsupport β ⊆ K) (c : ℂ) :
    ∃ B, ∀ z, Complex.equivRealProdCLM.symm z ≠ c →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - c‖ * (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - c‖ * ‖fderiv ℝ β z‖ ≤ B := by
  have hρ : ContinuousOn (fun z ↦ √(cylindricalWeight z)) K :=
    (isWeight_cylindricalWeight.continuousOn.mono hKS).sqrt
  have hc : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z - c‖ := by fun_prop
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn (hβ.continuous.abs.continuousOn)
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn
    (hc.continuousOn.mul (hρ.mul hβ.continuous.abs.continuousOn))
  obtain ⟨B₃, hB₃⟩ := hK.exists_bound_of_continuousOn
    (hc.continuousOn.mul (hβ.continuous_fderiv one_ne_zero).norm.continuousOn)
  refine ⟨max (max B₁ B₂) (max B₃ 0), fun z _ ↦ ?_⟩
  by_cases hz : z ∈ K
  · refine ⟨?_, ?_, ?_⟩
    · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₁ z hz).trans (by simp))
    · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₂ z hz).trans (by simp))
    · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₃ z hz).trans (by simp))
  -- Off `K` the function vanishes near `z`.
  have hzt : z ∉ tsupport β := fun h ↦ hz (hβK h)
  have h0 : β z = 0 := image_eq_zero_of_notMem_tsupport hzt
  have hd : fderiv ℝ β z = 0 := by
    rw [((notMem_tsupport_iff_eventuallyEq).1 hzt).fderiv_eq]
    simp
  simp [h0, hd]

end Cutoff

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer StripSobolev
open scoped NNReal

section Fredholm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The end pieces of a right parametrix.** Under the hypotheses of
`isFredholm_floerConformalSobolevOperator_pairOfPants`, for every large enough height `T` the
cutoff of each end `q` at the height `T` carries an inverse of the end model of `D_u` up to a
compact operator and an operator of norm at most `1 / 4`. -/
private theorem exists_endCutoff_pieces (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : Puncture → ℝ → F → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F} (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] F))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ T₀, ∀ T, T₀ ≤ T → ∀ q, ∃ (Q : Lp F 2 stripMeasure →L[ℝ] CylinderSobolev.H1 F)
      (K E : Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure), IsCompactOperator K ∧
        ‖E‖ ≤ 1 / 4 ∧ ∀ h, ((positiveEndChartLp q).symm (jetOperator
          (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
              (endTransfer q (endCutoff q T) (Q h))) : ℝ × ℝ → F) =ᵐ[stripMeasure]
          fun ζ ↦ endCutoff q T (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ := by
  obtain ⟨L', hL'⟩ := smoothTransition.exists_forall_norm_deriv_le
  -- Far out on each end the data are those of the end, and the end model is invertible.
  have hend (q : Puncture) :=
    ω.exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer hH
      ((hHs q).of_le (by norm_num)) (hJe q) (T := max R₁ 1)
    (fun ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun ζ hζ ↦ hK q _ (positiveEndChart_mem_thricePuncturedSphereReal
      (by linarith [le_max_right R₁ 1])) (by
        rw [fst_positiveEndCoord_positiveEndChart]; exact (le_max_left _ _).trans hζ))
    (fun ζ hζ ↦ (hu _ (positiveEndChart_mem_thricePuncturedSphereReal
      (by linarith [le_max_right R₁ 1]))).differentiableAt one_ne_zero)
    (fun ζ hζ ↦ hF q _ (positiveEndChart_mem_thricePuncturedSphereReal
      (by linarith [le_max_right R₁ 1])) (by
        rw [fst_positiveEndCoord_positiveEndChart]; exact (le_max_left _ _).trans hζ))
    hM (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt) (hux q) (hδ q)
    (isInvertible_stationarySobolevOperator_of_compatible ω hω (hX q)
      (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      (hx q) (hxp q) (hnd q) (fun t ↦ hJex q t) (hJx q) fun t ↦ by
        have h₁ := hJeq q (R₁, t + 1) le_rfl
        rw [positiveEndChart_add_one, hJeq q (R₁, t) le_rfl] at h₁
        simp only [hxp q t, ← h₁])
  choose Q hQ using hend
  -- The bound `B` of the end cutoffs does not depend on the height.
  set B := 3 + L' * (2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ * 3)
  have hB : 0 < B := by
    have : 0 ≤ L' := (norm_nonneg _).trans (hL' 0)
    positivity
  choose T₀ hT₀ using fun q ↦ hQ q (1 / (4 * B)) (by positivity)
  refine ⟨1 + ∑ q, |T₀ q|, fun T hT q ↦ ?_⟩
  have hTq : T₀ q ≤ T - 1 := by
    have := (le_abs_self (T₀ q)).trans
      (Finset.single_le_sum (f := fun q ↦ |T₀ q|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q))
    linarith
  have hT1 : 1 ≤ T := by
    have : 0 ≤ ∑ q, |T₀ q| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    linarith
  obtain ⟨K, E, hKc, hE, hid⟩ := hT₀ q (β := endCutoff q T) (T₁ := T + 1) (contDiff_endCutoff q T)
    (fun z hz hc ↦ mem_thricePuncturedSphereReal_of_mem_tsupport_endCutoff q hT1 hz hc)
    (fun z hc ↦ endCutoff_bound hL' q hT1 hc)
    (fun ζ hζ ↦ endCutoff_positiveEndChart_eq_zero q (hζ.trans hTq))
    (fun ζ hζ ↦ fderiv_endCutoff_positiveEndChart_eq_zero q (hζ.imp (·.trans hTq) id))
  exact ⟨Q q, K, E, hKc, hE.trans_eq (by field_simp; ring), hid⟩

/-- **A frozen piece of the core.** At each point `z₀` of `S` there are a neighbourhood `U` and
an operator `Q` such that every cutoff supported in `U`, admissible for the transfer along the end
chart of `0`, carries an inverse of `D_u` up to a compact operator. The model is the stationary
cylinder operator over the nondegenerate orbit `x` with the constant structure `J(z₀, u z₀)`,
which has the principal part of `D_u` at `z₀`. -/
private theorem exists_frozen_piece (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ} {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal,
      ContinuousAt (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal)) (z₀ : ℝ × ℝ) :
    ∃ U ∈ 𝓝 z₀, ∃ Q : Lp F 2 stripMeasure →L[ℝ] CylinderSobolev.H1 F,
      z₀ ∈ thricePuncturedSphereReal → ∀ {β : ℝ × ℝ → ℝ} {B T₀ T₁ : ℝ}, ContDiff ℝ 1 β →
        (∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ zero.endCenter →
          z ∈ thricePuncturedSphereReal) →
        (∀ z, Complex.equivRealProdCLM.symm z ≠ zero.endCenter →
          |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - zero.endCenter‖ *
            (√(cylindricalWeight z) * |β z|) ≤ B ∧
            ‖Complex.equivRealProdCLM.symm z - zero.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B) →
        tsupport β ⊆ U →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → β (positiveEndChart zero ζ) = 0) →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart zero ζ) = 0) →
        ∃ K : Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure, IsCompactOperator K ∧
          ∀ h, ((positiveEndChartLp zero).symm (jetOperator
            (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
                (endTransfer zero β (Q h))) : ℝ × ℝ → F) =ᵐ[stripMeasure]
            fun ζ ↦ β (positiveEndChart zero ζ) • h ζ + K h ζ := by
  by_cases hz₀ : z₀ ∈ thricePuncturedSphereReal
  swap
  · exact ⟨univ, univ_mem, 0, fun h ↦ absurd h hz₀⟩
  have hS : Continuous fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) :=
    (continuous_fderiv_slice_right (f := fun t ↦ ω.hamiltonianVectorField (H t))
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) (hH.of_le (by norm_num)))).comp
        (continuous_id.prodMk (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))
  obtain ⟨U, hU, Q, hQ⟩ :=
    exists_mem_nhds_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer
      ω zero hM (hJ z₀ hz₀) hS
      (isInvertible_stationarySobolevOperator_of_compatible ω hω hX hH hHp hx hxp hnd
        (fun _ ↦ hc z₀ hz₀) contDiff_const fun _ ↦ rfl)
  exact ⟨U, hU, Q, fun _ ↦ hQ⟩

/-- **The core pieces of a right parametrix.** Under the hypotheses of `exists_frozen_piece`, for
every height `T ≥ 1` the function `1 - ∑_q β_q` left over by the end cutoffs `β_q` at the height
`T` is a finite sum of cutoffs supported in a compact part of `S`, each carrying a frozen piece
along the end chart of `0`. -/
private theorem exists_core_pieces (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ} {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal,
      ContinuousAt (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ (ι : Type) (_ : Fintype ι) (γ : ι → ℝ × ℝ → ℝ)
      (Q : ι → Lp F 2 stripMeasure →L[ℝ] CylinderSobolev.H1 F)
      (K : ι → Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure),
      (∀ i, ContDiff ℝ 2 (γ i)) ∧
      (∀ i, ∀ z ∈ tsupport (γ i), Complex.equivRealProdCLM.symm z ≠ zero.endCenter →
        z ∈ thricePuncturedSphereReal) ∧
      (∀ i, ∃ B, ∀ z, Complex.equivRealProdCLM.symm z ≠ zero.endCenter →
        |γ i z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - zero.endCenter‖ *
          (√(cylindricalWeight z) * |γ i z|) ≤ B ∧
          ‖Complex.equivRealProdCLM.symm z - zero.endCenter‖ * ‖fderiv ℝ (γ i) z‖ ≤ B) ∧
      (∀ z, ∑ i, γ i z = 1 - ∑ q, endCutoff q T z) ∧ (∀ i, IsCompactOperator (K i)) ∧
      ∀ i h, ((positiveEndChartLp zero).symm (jetOperator
        (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
            (endTransfer zero (γ i) (Q i h))) : ℝ × ℝ → F) =ᵐ[stripMeasure]
        fun ζ ↦ γ i (positiveEndChart zero ζ) • h ζ + K i h ζ := by
  classical
  set X := exp (-(4 * π * T))
  set E := exp (4 * π * T)
  -- The leftover `κ = 1 - ∑ β_q` lives in the core region, inside an open set `O` whose closure
  -- is a compact part of `S`.
  set κ : ℝ × ℝ → ℝ := fun z ↦ 1 - ∑ q, endCutoff q T z
  have hκ : ContDiff ℝ 2 κ := contDiff_const.sub (ContDiff.sum fun q _ ↦ contDiff_endCutoff q T)
  have hκK := tsupport_one_sub_sum_endCutoff_subset hT
  obtain ⟨O, hO, hKO, hOK⟩ := exists_isOpen_annularRegion_subset T
  have hCO : tsupport κ ⊆ O := hκK.trans hKO
  have hKS := annularRegion_subset (by positivity : 0 < X / 16) (36 * E)
  -- A finite partition of unity on the support of `κ`, subordinate to the frozen pieces.
  choose U hU Q hQ using exists_frozen_piece ω hω hX hH hHp hx hxp hnd hJ hc hM
  obtain ⟨s, χ, hχ, -, -, hχ1⟩ :=
    ((isCompact_annularRegion _ _).of_isClosed_subset (isClosed_tsupport κ) hκK
      ).exists_contDiff_tsupport_subset_finset_sum_eq_one
      (U := fun z : tsupport κ ↦ interior (U z) ∩ O) (fun _ ↦ isOpen_interior.inter hO)
      fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, mem_interior_iff_mem_nhds.2 (hU z), hCO hz⟩
  set γ : s → ℝ × ℝ → ℝ := fun i x ↦ κ x * χ i x
  have hγ (i : s) : ContDiff ℝ 2 (γ i) := hκ.mul ((hχ i).1.of_le (by norm_cast))
  have hγO (i : s) : tsupport (γ i) ⊆ interior (U i) ∩ O :=
    tsupport_mul_subset_right.trans (hχ i).2.2
  have hγK (i : s) : tsupport (γ i) ⊆ annularRegion (X / 16) (36 * E) :=
    fun z hz ↦ hOK (hγO i hz).2
  have hγB (i : s) := exists_bound_of_tsupport_subset ((hγ i).of_le (by norm_num))
    (isCompact_annularRegion _ _) hKS (hγK i) zero.endCenter
  -- Read in the end chart of `0`, the cutoffs live over the heights `-T - 3 < s < T + 1`.
  have hγ0 (i : s) {ζ : ℝ × ℝ} (h : ζ.1 ≤ -T - 3 ∨ T + 1 ≤ ζ.1) :
      positiveEndChart zero ζ ∉ tsupport (γ i) := fun hz ↦
    positiveEndChart_zero_notMem_annularRegion h (hγK i hz)
  have hpiece (i : s) := hQ i (hKS (hOK (hCO i.val.property))) (β := γ i) (T₀ := -T - 3)
    (T₁ := T + 1) ((hγ i).of_le (by norm_num)) (fun z hz _ ↦ hKS (hγK i hz)) (hγB i).choose_spec
    (fun z hz ↦ interior_subset (hγO i hz).1)
    (fun ζ h ↦ image_eq_zero_of_notMem_tsupport (hγ0 i h))
    (fun ζ h ↦ by
      rw [((notMem_tsupport_iff_eventuallyEq).1 (hγ0 i h)).fderiv_eq]
      simp)
  choose K hK hid using hpiece
  refine ⟨s, inferInstance, γ, fun i ↦ Q i, K, hγ, fun i z hz _ ↦ hKS (hγK i hz), hγB,
    fun z ↦ ?_, hK, hid⟩
  simp only [γ]
  rw [Finset.sum_coe_sort s fun i ↦ κ z * χ i z, ← Finset.mul_sum]
  by_cases hz : z ∈ tsupport κ
  · rw [hχ1 z hz, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    exact (image_eq_zero_of_notMem_tsupport hz).symm

/-- **The linearized operator of a pair of pants is Fredholm.** Let `F` be a finite-dimensional
complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let `H_q` be jointly
`C³` period-one Hamiltonians on the three ends of the pair of pants `S = ℂ ∖ {0, 1}`, with
nondegenerate one-periodic orbits `x_q` of the end Hamiltonians read in the positive end charts.
Let `(J, K_s, K_t)` be Floer data on `S` which far out on each end are the structures `J_q(t)` of
a `C¹` family and the pair-of-pants perturbation of the `H_q`, with `J_q(t)` compatible with `ω`
and `C²` in `t` along `x_q`. Let `u` be `C¹` on `S`, solve the Floer equation far out on the ends,
and converge there to the orbits `x_q`, while on all of `S` the structures `J(z, u z)` are
`ω`-compatible and the data are regular along `u`. Then the realization
`D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator for the cylindrical metric is
Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_pairOfPants (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : Puncture → ℝ → F → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] F))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  classical
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  have hM := ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs₂
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe
    hJeq hK hJ hKs hKt hu hF hux hδ
  -- The end pieces, at a height `T` where their operators `E_q` have norms at most `1 / 4`.
  obtain ⟨T₀, hT₀⟩ := exists_endCutoff_pieces ω hω hH hHs hX hx hxp hnd hJe hJex hJx hJeq hK hu hF
    hM hux hδ
  set T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  choose Qe Ke Ee hKe hEe hide using hT₀ T (le_max_left _ _)
  -- The core pieces, in the end chart of `0`.
  obtain ⟨ι, _, γ, Qc, Kc, hγ, hγS, hγB, hγsum, hKc, hidc⟩ := exists_core_pieces (J := J) (u := u)
    (Ks := Ks) (Kt := Kt) ω hω (hX zero)
    (contDiff_uncurry_positiveEndHamiltonian (hHs zero)) (periodic_positiveEndHamiltonian (hH zero))
    (hx zero) (hxp zero) (hnd zero) (fun z hz ↦ (hJ z hz).continuousAt.comp
      (f := fun z ↦ (z, u z)) (continuousAt_id.prodMk (hu z hz).continuousAt)) hc hM hT1
  obtain ⟨L', hL'⟩ := smoothTransition.exists_forall_norm_deriv_le
  -- Splicing the pieces gives a right parametrix modulo compact operators.
  have hcofg := cofg_range_jetOperator_comp_subtypeL_of_sum_eq_one (ι := Puncture ⊕ ι)
    (Sum.elim id fun _ ↦ zero) (β := Sum.elim (fun q ↦ endCutoff q T) γ)
    (fun i ↦ by rcases i with q | i; exacts [contDiff_endCutoff q T, hγ i])
    (fun i ↦ by rcases i with q | i; exacts [fun z hz hc ↦
      mem_thricePuncturedSphereReal_of_mem_tsupport_endCutoff q hT1 hz hc, hγS i])
    (fun i ↦ by rcases i with q | i; exacts [⟨_, fun z hc ↦ endCutoff_bound hL' q hT1 hc⟩, hγB i])
    (fun z _ ↦ by simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hγsum]; ring)
    (Sum.elim Qe Qc) (Sum.elim Ke Kc) (Sum.elim Ee fun _ ↦ 0)
    (fun i ↦ by rcases i with q | i; exacts [hKe q, hKc i])
    (by
      simp [Fintype.sum_sum_type, Puncture.sum_univ, ContinuousLinearMap.opNorm_zero]
      linarith [hEe zero, hEe one, hEe inf])
    (fun i h ↦ by
      rcases i with q | i
      · exact hide q h
      · filter_upwards [hidc i h, Lp.coeFn_zero (E := F) (p := 2) (μ := stripMeasure)] with ζ h₁ h₂
        simp only [Sum.elim_inr]
        rw [h₁, zero_apply, h₂, Pi.zero_apply, add_zero])
  have hker := ω.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants hH hHs₂ hX hx hnd
    hJe hJex hJeq hK hJ hKs hKt hu hc hF hux hδ
  rw [floerConformalSobolevOperator_def] at hker ⊢
  exact .of_finite_ker_coker _ hker hcofg

end Fredholm

end TauCeti.SymplecticForm
