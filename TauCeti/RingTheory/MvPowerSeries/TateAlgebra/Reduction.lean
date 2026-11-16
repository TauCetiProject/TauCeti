/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Polynomial reduction of Gauss-normed restricted power series modulo open ideals

For an ultrametric normed commutative ring `R`, any open ideal `J : Ideal R` contains an open norm
ball around `0`. Thus every unit-radius restricted power series
`f ∈ MvPowerSeries.IsRestricted.subring (fun _ : σ ↦ 1)` has only finitely many coefficients outside
`J`, and coefficientwise reduction modulo `J` lands in `MvPolynomial σ (R ⧸ J)`.

## Main definitions and results

* `Ideal.isRestrictedReduction`: the surjective ring homomorphism
  `MvPowerSeries.IsRestricted.subring (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J)` reducing each
  coefficient modulo an open ideal `J` (`Ideal.isRestrictedReduction_surjective`,
  `Ideal.mem_ker_isRestrictedReduction`).
* `Ideal.continuous_comp_isRestrictedReduction`, `TauCeti.MvPowerSeries.map_isRestrictedReduction`,
  and `TauCeti.MvPowerSeries.isRestrictedReduction_restrictedMap`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace Ideal

open Filter Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

private theorem finite_support_mk_coeff_isRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (Function.support fun ν ↦
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R))).Finite := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  refine (show {ν | ε ≤ ‖MvPowerSeries.coeff ν (f : MvPowerSeries σ R)‖}.Finite by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds hε)).subset fun ν hν ↦ ?_
  rw [Function.mem_support, Ne, Ideal.Quotient.eq_zero_iff_mem] at hν
  exact not_lt.mp fun hlt ↦ hν (hball (Set.mem_ofPred_eq.mpr hlt))

private noncomputable def isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPolynomial σ (R ⧸ J) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_mk_coeff_isRestricted J hJ f))

private theorem coe_isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (isRestrictedReductionFun J hJ f : MvPowerSeries σ (R ⧸ J)) =
      MvPowerSeries.map (Ideal.Quotient.mk J) (f : MvPowerSeries σ R) := by
  ext ν; simp [MvPolynomial.coeff_coe, isRestrictedReductionFun, Finsupp.ofSupportFinite_coe]

/-- **Polynomial reduction of Gauss-normed restricted series modulo an open ideal.** -/
noncomputable def isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J) where
  toFun := isRestrictedReductionFun J hJ
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_mul' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_add' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]

/-- `isRestrictedReduction` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (ν : σ →₀ ℕ) :
    (J.isRestrictedReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R)) := by
  rw [← MvPolynomial.coeff_coe]; simp [isRestrictedReduction, coe_isRestrictedReductionFun]

/-- On polynomials, `isRestrictedReduction` is coefficientwise reduction modulo `J`. -/
@[simp]
theorem isRestrictedReduction_polynomialToRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (p : MvPolynomial σ R) :
    J.isRestrictedReduction hJ (TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ 1) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν
  simp [TauCeti.MvPowerSeries.coe_polynomialToRestricted, MvPolynomial.coeff_map,
    MvPolynomial.coeff_coe]

/-- `isRestrictedReduction` sends a constant series to the constant polynomial on its residue. -/
@[simp]
theorem isRestrictedReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    J.isRestrictedReduction (σ := σ) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simpa using isRestrictedReduction_polynomialToRestricted (σ := σ) J hJ (MvPolynomial.C r)

/-- `isRestrictedReduction` sends each coordinate variable to the corresponding variable. -/
@[simp]
theorem isRestrictedReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : σ) :
    J.isRestrictedReduction hJ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ =
      MvPolynomial.X i := by
  simpa using isRestrictedReduction_polynomialToRestricted J hJ (MvPolynomial.X i)

/-- Every polynomial over `R ⧸ J` lifts to a polynomial (hence restricted series) over `R`. -/
theorem isRestrictedReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedReduction (σ := σ) hJ) := fun p ↦
  let ⟨q, hq⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  ⟨TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ 1) q, by simp [hq]⟩

/-- A series lies in `ker (J.isRestrictedReduction hJ)` iff every coefficient lies in `J`. -/
theorem mem_ker_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    f ∈ RingHom.ker (J.isRestrictedReduction hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries σ R) ∈ J := by
  rw [RingHom.mem_ker, MvPolynomial.ext_iff]; simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Precomposing any map with `isRestrictedReduction` is continuous for the Gauss norm. -/
theorem continuous_comp_isRestrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (g : MvPolynomial σ (R ⧸ J) → X) :
    Continuous (g ∘ J.isRestrictedReduction hJ) := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [Metric.ball_mem_nhds f₀ hε] with f hf
  rw [Metric.mem_ball, dist_eq_norm] at hf
  refine congrArg g (MvPolynomial.ext _ _ fun ν ↦ ?_)
  rw [coeff_isRestrictedReduction, coeff_isRestrictedReduction, Ideal.Quotient.eq]
  exact hball <| by
    simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, Set.mem_ofPred_eq,
      AddSubgroupClass.coe_sub, map_sub] using
      (MvPowerSeries.norm_coeff_mul_prod_le (f₀ - f) ν).trans_lt (by rwa [norm_sub_rev])

end Ideal

namespace TauCeti.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- `isRestrictedReduction` is compatible with enlarging the open ideal. -/
@[simp]
theorem map_isRestrictedReduction {I J : Ideal R} (hI : IsOpen (I : Set R))
    (hJ : IsOpen (J : Set R)) (hIJ : I ≤ J)
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hIJ) (I.isRestrictedReduction hI f) =
      J.isRestrictedReduction hJ f := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- **Functoriality of `isRestrictedReduction` under bounded coefficient maps.** -/
theorem isRestrictedReduction_restrictedMap {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (I : Ideal R) (hI : IsOpen (I : Set R))
    (J : Ideal S) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    J.isRestrictedReduction hJ (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedReduction hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

end TauCeti.MvPowerSeries
