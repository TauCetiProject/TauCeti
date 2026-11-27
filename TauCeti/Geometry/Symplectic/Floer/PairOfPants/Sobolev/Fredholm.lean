/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Core.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.End.Parametrix
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
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
(`TauCeti.SymplecticForm.floerConformalSobolevOperator`) has finite-dimensional kernel
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`) and
closed range (`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pairOfPants`).
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
  transfer along the chart hold uniformly in `T`, since the derivative bound of the radial cutoff
  (`Real.smoothTransition.norm_sub_mul_norm_fderiv_add_mul_norm_sub_sq_le`) does not depend on
  `b`. Far enough out, an inverse of the end model
  carries such a cutoff up to a compact operator and an operator of norm at most `1 / 4`
  (`hasEndParametrixPiece_floerConformalJetCoeff`, in
  the namespace `TauCeti.SymplecticForm`). The three end cutoffs sum to one outside the compact
  truncation `S_{T+1}` of `S` (`TauCeti.ThricePuncturedSphere.truncation`).
* **The core.** The leftover `1 - ∑ β_q` is supported in that compact region. A finite partition
  of unity (`IsCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one`) splits it into cutoffs
  supported in small neighbourhoods `U` of points `z₀`, on which `D_u` is close to a frozen model
  with the same principal part, so each carries an inverse up to a compact operator
  (`exists_mem_nhds_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`,
  in the namespace `TauCeti.SymplecticForm`). Only the principal part of the frozen model
  matters: it is the stationary cylinder operator over the orbit of the end at `0`, with the
  constant structure `J(z₀, u z₀)`, which is invertible
  (`TauCeti.SymplecticForm.isInvertible_stationarySobolevOperator_of_compatible`).

The splicing uses the data only through the end pieces, so it proves more generally that `D_u`
is Fredholm as soon as its kernel is finite-dimensional and each end carries an end piece
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_endParametrix`); for data
that are the pair-of-pants data far out on an end with a nondegenerate asymptotic orbit, the end
piece is the one above
(`TauCeti.SymplecticForm.hasEndParametrixPiece_floerConformalJetCoeff_of_isNondegenerateFixedPt`).

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
    (hid : ∀ h, ((positiveEndChartLp q).symm (jetOperator 2
      (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))) :
        ℝ × ℝ → W) =ᵐ[stripMeasure] fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ)
    (g : Lp W 2 (volume.restrict thricePuncturedSphereReal)) :
    ⇑(jetOperator 2 (volume.restrict thricePuncturedSphereReal) M
        (endTransfer q β (Q ((positiveEndChartLp q).symm g))) -
      positiveEndChartLp q (K ((positiveEndChartLp q).symm g)) -
      positiveEndChartLp q (E ((positiveEndChartLp q).symm g)))
      =ᵐ[volume.restrict thricePuncturedSphereReal] fun z ↦ β z • g z := by
  set h := (positiveEndChartLp q).symm g
  set X := jetOperator 2 (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))
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
    (hid : ∀ i h, ((positiveEndChartLp (q i)).symm (jetOperator 2
      (volume.restrict thricePuncturedSphereReal) M (endTransfer (q i) (β i) (Q i h))) :
        ℝ × ℝ → W) =ᵐ[stripMeasure]
          fun ζ ↦ β i (positiveEndChart (q i) ζ) • h ζ + K i h ζ + E i h ζ) :
    ((jetOperator 2 (volume.restrict thricePuncturedSphereReal) M).comp
      (ConformalSobolev.H1 V _ cylindricalWeight).subtypeL).range.CoFG := by
  classical
  set μS := volume.restrict thricePuncturedSphereReal
  set H := ConformalSobolev.H1 V thricePuncturedSphereReal cylindricalWeight
  set D := (jetOperator 2 μS M).comp H.subtypeL
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
    have hg :
        ∑ i, (jetOperator 2 μS M (A i g) - tr i (K i (rd i g)) - tr i (E i (rd i g))) = g := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_finsetSum Finset.univ fun i ↦
          jetOperator 2 μS M (A i g) - tr i (K i (rd i g)) - tr i (E i (rd i g)),
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

private theorem two_lt_exp_four_pi : 2 < exp (4 * π) := by
  nlinarith [Real.add_one_le_exp (4 * π), Real.two_le_pi]

/-- The constant term of the cutoff of the end `q`. -/
private def endA (q : Puncture) : ℝ := if q = inf then -1 else 2

/-- The coefficient of the squared distance to the center in the cutoff of the end `q` at the
height `T`. -/
private def endB (q : Puncture) (T : ℝ) : ℝ :=
  if q = inf then exp (-(4 * π * T)) / 4 else -(4 * exp (4 * π * T))

/-- The cutoff of the end `q` at the height `T`, the radial cutoff
`ψ(a + b |w - c_q|²)` around the center of the end read through `Complex.equivRealProdCLM`: it
vanishes below the height `T - 1` of the end and is one beyond the height `T + 1`. -/
private def endCutoff (q : Puncture) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  smoothTransition (endA q + endB q T * ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2)

private theorem contDiff_endCutoff (q : Puncture) (T : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (endCutoff q T) :=
  (smoothTransition.contDiff_add_mul_norm_sub_sq _ _ _).comp
    Complex.equivRealProdCLM.symm.contDiff

/-- The derivative of the end cutoff is that of the radial cutoff on `ℂ`, composed with
`Complex.equivRealProdCLM.symm`. -/
private theorem fderiv_endCutoff (q : Puncture) (T : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (endCutoff q T) z =
      (fderiv ℝ (fun w : ℂ ↦ smoothTransition (endA q + endB q T * ‖w - q.endCenter‖ ^ 2))
        (Complex.equivRealProdCLM.symm z)).comp
        (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) :=
  ((smoothTransition.hasFDerivAt_add_mul_norm_sub_sq _ _ _ _).differentiableAt.hasFDerivAt.comp z
    (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).hasFDerivAt).fderiv

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
  by rw [fderiv_endCutoff, smoothTransition.fderiv_add_mul_norm_sub_sq_eq_zero
    (h.imp (fun h ↦ (endArg_positiveEndChart_neg q h).le) (one_le_endArg_positiveEndChart q)),
    ContinuousLinearMap.zero_comp]

/-- The end cutoff of `q` at the height `T` lives beyond the height `T - 1` of the end. -/
private theorem sub_one_lt_fst_positiveEndCoord_of_mem_tsupport (q : Puncture) {T : ℝ}
    {z : ℝ × ℝ} (hz : z ∈ tsupport (endCutoff q T))
    (hc : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    T - 1 < (positiveEndCoord q z).1 := by
  have h := smoothTransition.tsupport_add_mul_norm_sub_sq_subset _ _ _
    (tsupport_comp_subset_preimage _ Complex.equivRealProdCLM.symm.continuous hz)
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
  have h1 := smoothTransition.abs_le_one
    (endA q + endB q T * ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2)
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
  · have hw := smoothTransition.norm_sub_mul_norm_fderiv_add_mul_norm_sub_sq_le hL q.endCenter
      (endA q) (endB q T) (Φ z)
    have := abs_endA_le q
    have : 2 * L * (1 + |endA q|) * ‖Φ‖ ≤ L * (2 * ‖Φ‖ * 3) := by
      nlinarith [norm_nonneg Φ, mul_nonneg hL0 (norm_nonneg Φ)]
    rw [fderiv_endCutoff]
    calc ‖Φ z - q.endCenter‖ * ‖(fderiv ℝ (fun w : ℂ ↦
            smoothTransition (endA q + endB q T * ‖w - q.endCenter‖ ^ 2)) (Φ z)).comp Φ‖
        ≤ ‖Φ z - q.endCenter‖ * (‖fderiv ℝ (fun w : ℂ ↦
            smoothTransition (endA q + endB q T * ‖w - q.endCenter‖ ^ 2)) (Φ z)‖ * ‖Φ‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * L * (1 + |endA q|) * ‖Φ‖ := by
          rw [← mul_assoc]
          gcongr
      _ ≤ _ := by linarith

/-! ### The compact core -/

/-- Outside the truncation `S_{T+1}`, one end cutoff at the height `T ≥ 1` is one and the others
vanish, so the end cutoffs sum to one. -/
private theorem sum_endCutoff_eq_one {T : ℝ} (hT : 1 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1)) :
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
  -- The squared radii of the truncation `S_{T+1}`, against `exp (∓4πT)`.
  have ha : exp (-(2 * π * (T + 1))) ^ 2 ≤ X := by
    rw [← Real.exp_natCast_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.pi_pos])
  have hb : 2 * E ≤ exp (2 * π * (T + 1)) ^ 2 := by
    rw [← Real.exp_natCast_mul, show ((2 : ℕ) : ℝ) * (2 * π * (T + 1)) = 4 * π * T + 4 * π by
      push_cast; ring, Real.exp_add]
    nlinarith [Real.exp_pos (4 * π * T), two_lt_exp_four_pi]
  have ha₀ := Real.exp_pos (-(2 * π * (T + 1)))
  have hb₀ := Real.exp_pos (2 * π * (T + 1))
  rw [Puncture.sum_univ]
  simp only [endCutoff, endA, endB, reduceCtorEq, ite_false, ite_true, endCenter_zero,
    endCenter_one, endCenter_inf, sub_zero]
  rw [mem_preimage, truncation_eq] at hz
  simp only [mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, not_and_or,
    not_le] at hz
  rcases hz with (h | h) | h
  · -- Near `0`: the cutoff of the end at `0` is one.
    have h : ‖w‖ ^ 2 < X / 4 := by nlinarith
    have hw : ‖w‖ < 1 / 2 := by nlinarith
    rw [smoothTransition.one_of_one_le (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith)]
    norm_num
  · -- Near `1`: the cutoff of the end at `1` is one.
    have h : ‖w - 1‖ ^ 2 < X / 4 := by nlinarith
    have hw : ‖w - 1‖ < 1 / 2 := by nlinarith
    rw [smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.one_of_one_le (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith)]
    norm_num
  · -- Far out: the cutoff of the end at `∞` is one.
    have h : 8 * E < ‖w‖ ^ 2 := by nlinarith
    have hw : 3 < ‖w‖ := by nlinarith
    rw [smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.one_of_one_le (by nlinarith)]
    norm_num

/-- The function `1 - ∑_q β_q` left over by the end cutoffs at the height `T ≥ 1` is supported in
the truncation `S_{T+1}`. -/
private theorem tsupport_one_sub_sum_endCutoff_subset {T : ℝ} (hT : 1 ≤ T) :
    tsupport (fun z ↦ 1 - ∑ q, endCutoff q T z) ⊆
      Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1) :=
  closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (by simp [sum_endCutoff_eq_one hT h]))
    (isCompact_preimage_truncation _).isClosed

/-- The truncation `S_{T+1}` has an open neighbourhood inside the truncation `S_{T+2}`: the points
of `S` below the height `T + 2` on every end. -/
private theorem exists_isOpen_preimage_truncation_subset (T : ℝ) :
    ∃ O, IsOpen O ∧ Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1) ⊆ O ∧
      O ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 2) := by
  refine ⟨⋂ q, thricePuncturedSphereReal ∩
      (fun z : ℝ × ℝ ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) ⁻¹'
        Iio (T + 2), isOpen_iInter_of_finite fun q ↦ isOpen_endSign_mul_re_endCoord_lt q _,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [mem_preimage_truncation_iff] at hz
    exact mem_iInter.2 fun q ↦ ⟨hz.1, by
      rw [mem_preimage, mem_Iio, ← fst_positiveEndCoord]
      linarith [hz.2 q]⟩
  · have hz := mem_iInter.1 hz
    refine mem_preimage_truncation_iff.2 ⟨(hz zero).1, fun q ↦ ?_⟩
    have hq := (hz q).2
    rw [mem_preimage, mem_Iio, ← fst_positiveEndCoord] at hq
    exact hq.le

/-- Read in the positive end chart of the end at `0`, the truncation `S_{T+2}` lies over the
heights `-T - 3 < s < T + 3`. -/
private theorem positiveEndChart_zero_notMem_preimage_truncation {T : ℝ} {ζ : ℝ × ℝ}
    (h : ζ.1 ≤ -T - 3 ∨ T + 3 ≤ ζ.1) :
    positiveEndChart zero ζ ∉ Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 2) := by
  rw [mem_preimage_truncation_iff, not_and_or, not_forall]
  right
  rcases h with h | h
  · -- Far below on the end at `0`, the point lies beyond the height `T + 2` of the output end.
    have hn := norm_equivRealProdCLM_symm_positiveEndChart_sub_endCenter zero ζ
    simp only [endCenter_zero, sub_zero, endSign_zero, endScale_zero, one_mul] at hn
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hn
    have hw : Complex.equivRealProdCLM.symm (positiveEndChart zero ζ) ≠ 0 := by
      rw [← norm_ne_zero_iff, hn]
      positivity
    refine ⟨inf, not_le.2 ((lt_fst_positiveEndCoord_inf_iff hw).2 ?_)⟩
    rw [hn]
    have h2π : 4 < exp (2 * π) := by nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
    have : exp (2 * π * (T + 2)) * exp (2 * π) ≤ exp (-(2 * π * ζ.1)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    nlinarith [Real.exp_pos (2 * π * (T + 2))]
  · -- Far above on the end at `0`, the point lies beyond the height `T + 2` of that end.
    exact ⟨zero, not_le.2 (by rw [fst_positiveEndCoord_positiveEndChart]; linarith)⟩

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
  simp [h0, fderiv_of_notMem_tsupport ℝ hzt]

end Cutoff

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer StripSobolev
open scoped NNReal

section EndPieces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The end pieces of a right parametrix.** Let `D` be a first-order operator on `S` with an
essentially bounded coefficient field `M` on conformal jets, and let each end `q` carry an end
piece (`TauCeti.Floer.HasEndParametrixPiece`): an operator `Q` inverting `D` on cutoffs living far
enough out on `q`, up to a compact operator and an operator of norm at most `B ε`. Then for every
large enough height `T` the cutoff of each end `q` at the height `T` carries such an inverse with
an error of norm at most `1 / 4`. -/
private theorem exists_endCutoff_pieces {M : ℝ × ℝ → V × V × V →L[ℝ] V}
    (hend : ∀ q : Puncture, HasEndParametrixPiece q M) :
    ∃ T₀, ∀ T, T₀ ≤ T → ∀ q, ∃ (Q : Lp V 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V)
      (K E : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure), IsCompactOperator K ∧
        ‖E‖ ≤ 1 / 4 ∧ ∀ h, ((positiveEndChartLp q).symm (jetOperator 2
          (volume.restrict thricePuncturedSphereReal) M
              (endTransfer q (endCutoff q T) (Q h))) : ℝ × ℝ → V) =ᵐ[stripMeasure]
          fun ζ ↦ endCutoff q T (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ := by
  obtain ⟨L', hL'⟩ := smoothTransition.exists_forall_norm_deriv_le
  choose Q hQ using fun q ↦ (hasEndParametrixPiece_def q M).1 (hend q)
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

end EndPieces

section Fredholm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

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
          ∀ h, ((positiveEndChartLp zero).symm (jetOperator 2
            (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
                (endTransfer zero β (Q h))) : ℝ × ℝ → F) =ᵐ[stripMeasure]
            fun ζ ↦ β (positiveEndChart zero ζ) • h ζ + K h ζ := by
  by_cases hz₀ : z₀ ∈ thricePuncturedSphereReal
  swap
  · exact ⟨univ, univ_mem, 0, fun h ↦ absurd h hz₀⟩
  have hS := ω.continuous_fderiv_hamiltonianVectorField_comp (hH.of_le (by norm_num))
    (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
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
      ∀ i h, ((positiveEndChartLp zero).symm (jetOperator 2
        (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
            (endTransfer zero (γ i) (Q i h))) : ℝ × ℝ → F) =ᵐ[stripMeasure]
        fun ζ ↦ γ i (positiveEndChart zero ζ) • h ζ + K i h ζ := by
  classical
  -- The leftover `κ = 1 - ∑ β_q` lives in the truncation `S_{T+1}`, inside an open set `O`
  -- contained in the compact truncation `S_{T+2}` of `S`.
  set κ : ℝ × ℝ → ℝ := fun z ↦ 1 - ∑ q, endCutoff q T z
  have hκ : ContDiff ℝ 2 κ := contDiff_const.sub (ContDiff.sum fun q _ ↦ contDiff_endCutoff q T)
  have hκK := tsupport_one_sub_sum_endCutoff_subset hT
  obtain ⟨O, hO, hKO, hOK⟩ := exists_isOpen_preimage_truncation_subset T
  have hCO : tsupport κ ⊆ O := hκK.trans hKO
  have hKS := preimage_truncation_subset_thricePuncturedSphereReal (T + 2)
  -- A finite partition of unity on the support of `κ`, subordinate to the frozen pieces.
  choose U hU Q hQ using exists_frozen_piece ω hω hX hH hHp hx hxp hnd hJ hc hM
  obtain ⟨s, χ, hχ, -, -, hχ1⟩ :=
    ((isCompact_preimage_truncation _).of_isClosed_subset (isClosed_tsupport κ) hκK
      ).exists_contDiff_tsupport_subset_finset_sum_eq_one
      (U := fun z : tsupport κ ↦ interior (U z) ∩ O) (fun _ ↦ isOpen_interior.inter hO)
      fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, mem_interior_iff_mem_nhds.2 (hU z), hCO hz⟩
  set γ : s → ℝ × ℝ → ℝ := fun i x ↦ κ x * χ i x
  have hγ (i : s) : ContDiff ℝ 2 (γ i) := hκ.mul ((hχ i).1.of_le (by norm_cast))
  have hγO (i : s) : tsupport (γ i) ⊆ interior (U i) ∩ O :=
    tsupport_mul_subset_right.trans (hχ i).2.2
  have hγK (i : s) : tsupport (γ i) ⊆
      Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 2) :=
    fun z hz ↦ hOK (hγO i hz).2
  have hγB (i : s) := exists_bound_of_tsupport_subset ((hγ i).of_le (by norm_num))
    (isCompact_preimage_truncation _) hKS (hγK i) zero.endCenter
  -- Read in the end chart of `0`, the cutoffs live over the heights `-T - 3 < s < T + 3`.
  have hγ0 (i : s) {ζ : ℝ × ℝ} (h : ζ.1 ≤ -T - 3 ∨ T + 3 ≤ ζ.1) :
      positiveEndChart zero ζ ∉ tsupport (γ i) := fun hz ↦
    positiveEndChart_zero_notMem_preimage_truncation h (hγK i hz)
  have hpiece (i : s) := hQ i (hKS (hOK (hCO i.val.property))) (β := γ i) (T₀ := -T - 3)
    (T₁ := T + 3) ((hγ i).of_le (by norm_num)) (fun z hz _ ↦ hKS (hγK i hz)) (hγB i).choose_spec
    (fun z hz ↦ interior_subset (hγO i hz).1)
    (fun ζ h ↦ image_eq_zero_of_notMem_tsupport (hγ0 i h))
    (fun ζ h ↦ fderiv_of_notMem_tsupport ℝ (hγ0 i h))
  choose K hK hid using hpiece
  refine ⟨s, inferInstance, γ, fun i ↦ Q i, K, hγ, fun i z hz _ ↦ hKS (hγK i hz), hγB,
    fun z ↦ ?_, hK, hid⟩
  simp only [γ]
  rw [Finset.sum_coe_sort s fun i ↦ κ z * χ i z, ← Finset.mul_sum]
  by_cases hz : z ∈ tsupport κ
  · rw [hχ1 z hz, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    exact (image_eq_zero_of_notMem_tsupport hz).symm

/-- **The linearized Floer operator on the pair of pants is Fredholm once its ends carry
parametrix pieces.** Let `F` be a finite-dimensional complex inner product space whose symplectic
form `ω` is `Im ⟪·, ·⟫`, and let `(J, K_s, K_t)` be Floer data on the pair of pants
`S = ℂ ∖ {0, 1}` with `J(z, u z)` continuous along `u` and `ω`-compatible, whose coefficient field
on the conformal jets of the cylindrical weight is essentially bounded along `u`. Suppose that the
realization `D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator has
finite-dimensional kernel, and that each end `q` carries an end piece of a right parametrix
(`TauCeti.Floer.HasEndParametrixPiece`): an operator `Q` such that `D_u` applied to the transfer
`β · (Q h ∘ ψ)` along the end chart, for a cutoff `β` living far enough out on `q`, is the transfer
of `β(φ'_q) h + K h + E h` with `K` compact and `‖E‖ ≤ B ε`, as given by
`TauCeti.Floer.hasEndParametrixPiece_of_tendsto_endModelCoeff`. Then `D_u` is
Fredholm.

The ends are not otherwise constrained, so this applies whether the data are the pair-of-pants
data far out on each end or, for instance, a translate of them on an end. The core of `S` is
covered by frozen pieces, whose models are stationary cylinder operators with constant compatible
structures; their invertibility is what the nondegenerate one-periodic orbit `x₀` of the auxiliary
`C³` Hamiltonian `H₀` supplies. -/
theorem isFredholm_floerConformalSobolevOperator_of_endParametrix (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H₀ : ℝ → F → ℝ} {L₀ : ℝ≥0}
    (hX₀ : LipschitzWith L₀ (ω.timeDependentHamiltonianSuspension H₀))
    (hH₀ : ContDiff ℝ 3 (uncurry H₀)) (hH₀p : Periodic H₀ 1) {x₀ : ℝ → F}
    (hx₀ : ∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H₀ t) (x₀ t)) t) (hx₀p : Periodic x₀ 1)
    (hnd₀ : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H₀ hX₀ 0 1) (x₀ 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ} {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal,
      ContinuousAt (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    (hker : FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).ker)
    (hend : ∀ q : Puncture, HasEndParametrixPiece q (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  classical
  -- The end pieces, at a height `T` where their operators `E_q` have norms at most `1 / 4`.
  obtain ⟨T₀, hT₀⟩ := exists_endCutoff_pieces hend
  set T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  choose Qe Ke Ee hKe hEe hide using hT₀ T (le_max_left _ _)
  -- The core pieces, in the end chart of `0`.
  obtain ⟨ι, _, γ, Qc, Kc, hγ, hγS, hγB, hγsum, hKc, hidc⟩ := exists_core_pieces (J := J) (u := u)
    (Ks := Ks) (Kt := Kt) ω hω hX₀ hH₀ hH₀p hx₀ hx₀p hnd₀ hJ hc hM hT1
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
  rw [floerConformalSobolevOperator_def] at hker ⊢
  exact .of_finite_ker_coker _ hker hcofg

/-- **The end piece of a pair of pants at a nondegenerate orbit.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
the Floer data `(J, K_s, K_t)` beyond the height `R₁` of the end `q` of `S` be the structures
`J_q(t)` of a `C¹` family, read in the positive end chart, and the pair-of-pants perturbation of
period-one Hamiltonians `H` with `H_q` jointly `C³`. Let `u` be differentiable and solve the Floer
equation there, with essentially bounded coefficient field on conformal jets, and let the loops of
`u ∘ φ'_q` converge uniformly to a nondegenerate one-periodic orbit `x` of the end Hamiltonian, with
slice defect tending uniformly to zero, along which `J_q(t)` is `ω`-compatible and `C²` in `t`.
Then `D_u` has an end piece of a right parametrix on `q`
(`TauCeti.Floer.HasEndParametrixPiece`): the stationary operator at `x` is invertible
(`isInvertible_stationarySobolevOperator_of_compatible`), so
`hasEndParametrixPiece_floerConformalJetCoeff` applies. -/
theorem hasEndParametrixPiece_floerConformalJetCoeff_of_isNondegenerateFixedPt
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : Puncture → ℝ → F → ℝ}
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ContDiff ℝ 3 (uncurry (H q))) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) hX 0 1) (x 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F} {Jq : ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJq : ContDiff ℝ 1 fun p : ℝ × F ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJqx : ∀ t, ω.Compatible (Jq t (x t)))
    (hJx : ContDiff ℝ 2 fun t ↦ (Jq t (x t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Jq ζ.2)
    {Ks Kt : ℝ × ℝ → F → ℝ}
    (hK : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hu : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      DifferentiableAt ℝ u z)
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] F))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    HasEndParametrixPiece q (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) := by
  -- Beyond the height `max R₁ 1`, the chart lands in `S` at end coordinates at least `R₁`.
  have hS {ζ : ℝ × ℝ} (hζ : max R₁ 1 ≤ ζ.1) : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by linarith [le_max_right R₁ 1])
  have hR {ζ : ℝ × ℝ} (hζ : max R₁ 1 ≤ ζ.1) : R₁ ≤ (positiveEndCoord q (positiveEndChart q ζ)).1 :=
    by rw [fst_positiveEndCoord_positiveEndChart]; exact (le_max_left _ _).trans hζ
  exact ω.hasEndParametrixPiece_floerConformalJetCoeff hH (hHs.of_le (by norm_num)) hJq
    (T := max R₁ 1) (fun ζ hζ ↦ hJeq ζ ((le_max_left _ _).trans hζ))
    (fun ζ hζ ↦ hK _ (hS hζ) (hR hζ)) (fun ζ hζ ↦ hu _ (hS hζ) (hR hζ))
    (fun ζ hζ ↦ hF _ (hS hζ) (hR hζ)) hM
    (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) hux hδ
    (isInvertible_stationarySobolevOperator_of_compatible ω hω hX
      (contDiff_uncurry_positiveEndHamiltonian hHs) (periodic_positiveEndHamiltonian (hH q))
      hx hxp hnd hJqx hJx
      (periodic_apply_of_forall_positiveEndChart_add_eq q 0
        (fun ζ hζ ↦ by rw [add_zero]; exact hJeq ζ hζ) hxp))

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
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  have hM := ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs₂
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe
    hJeq hK hJ hKs hKt hu hF hux hδ
  -- Far out on each end the data are those of the end, at a nondegenerate orbit.
  have hend (q : Puncture) :=
    ω.hasEndParametrixPiece_floerConformalJetCoeff_of_isNondegenerateFixedPt hω hH (hHs q) (hX q)
      (hx q) (hxp q) (hnd q) (hJe q) (hJex q) (hJx q) (hJeq q) (hK q)
      (fun z hz _ ↦ (hu z hz).differentiableAt one_ne_zero) (hF q) hM (hux q) (hδ q)
  exact isFredholm_floerConformalSobolevOperator_of_endParametrix ω hω (hX zero)
    (contDiff_uncurry_positiveEndHamiltonian (hHs zero)) (periodic_positiveEndHamiltonian (hH zero))
    (hx zero) (hxp zero) (hnd zero) (fun z hz ↦ (hJ z hz).continuousAt.comp
      (f := fun z ↦ (z, u z)) (continuousAt_id.prodMk (hu z hz).continuousAt)) hc hM
    (ω.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants hH hHs₂ hX hx hnd
      hJe hJex hJeq hK hJ hKs hKt hu hc hF hux hδ) hend

end Fredholm

end TauCeti.SymplecticForm
