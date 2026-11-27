/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.UnitBall

import Mathlib.Algebra.Polynomial.Laurent.Roots
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Group.NullFamily

/-!
# Laurent evaluation on the unit circle

Over an ultrametric normed field with infinite residue field, a Laurent sum with coefficients of
norm at most one and a coefficient of norm one attains norm one on the unit circle. The finite
case follows by lifting a nonroot of the reduced Laurent polynomial. For a summable family in
a complete field, the omitted terms have smaller norm and leave the norm of the value unchanged.

## References

* M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), §§1–2.
-/

public section

namespace TauCeti

open Filter _root_.IsLocalRing
open scoped Topology LaurentPolynomial

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

/-- A finite Laurent sum with coefficients in the closed unit ball and a coefficient of norm
one takes a value of norm one on the unit circle if the residue field is infinite. -/
theorem exists_norm_sum_mul_zpow_eq_one [Infinite (ResidueField (Subring.unitClosedBall E))]
    (s : Finset ℤ) (b : ℤ → Subring.unitClosedBall E) {j : ℤ} (hj : j ∈ s)
    (hb : ‖(b j : E)‖ = 1) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖∑ n ∈ s, (b n : E) * u ^ n‖ = 1 := by
  classical
  let O := Subring.unitClosedBall E
  let k := ResidueField O
  let π : O →+* k := residue O
  let P : k[T;T⁻¹] := ∑ n ∈ s, LaurentPolynomial.C (π (b n)) * LaurentPolynomial.T n
  have hj' : π (b j) ≠ 0 :=
    ((isUnit_unitClosedBall_iff_norm_eq_one.mpr hb).map π).ne_zero
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun Q : k[T;T⁻¹] ↦ Q.coeff j) h
    simp only [P, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Finset.sum_ite_eq', hj, ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    exact hj' hc
  have : Infinite kˣ := unitsEquivNeZero.infinite_iff.mpr
    ((Set.finite_singleton (0 : k)).infinite_compl).to_subtype
  obtain ⟨v, hv⟩ : ∃ v : kˣ, P.smeval v ≠ 0 := by
    by_contra! h
    exact hP (P.eq_zero_of_infinite_smeval_eq_zero (S := k) (Set.infinite_univ.mono fun x _ ↦ h x))
  rw [← LaurentPolynomial.eval₂_eq_smeval, Algebra.algebraMap_self] at hv
  obtain ⟨u, huv⟩ := surjective_units_map_of_local_ringHom π residue_surjective
    (by simpa only [π] using (inferInstance : IsLocalHom (residue O))) v
  refine ⟨(u.val : E), isUnit_unitClosedBall_iff_norm_eq_one.mp u.isUnit, ?_⟩
  let y : O := ∑ n ∈ s, b n * (u ^ n).val
  have hvpow (n : ℤ) : π (u ^ n).val = (v ^ n).val := by
    rw [← huv, ← map_zpow]
    exact (Units.coe_map (π : O →* k) (u ^ n)).symm
  have hy : π y ≠ 0 := by
    intro hyzero
    apply hv
    calc
      LaurentPolynomial.eval₂ (RingHom.id k) v P =
          ∑ n ∈ s, π (b n) * (v ^ n).val := by
        simp only [P, map_sum, LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply]
      _ = π y := by simp only [y, map_sum, map_mul, hvpow]
      _ = 0 := hyzero
  have hnorm : ‖O.subtype y‖ = 1 := isUnit_unitClosedBall_iff_norm_eq_one.mp <| by
    rwa [← notMem_maximalIdeal, ← residue_eq_zero_iff]
  have hpow (n : ℤ) : O.subtype (u ^ n).val = (u.val : E) ^ n := by
    let v' := Units.map O.subtype.toMonoidHom u
    calc
      O.subtype (u ^ n).val = ((v' ^ n : Eˣ) : E) :=
        congrArg Units.val (map_zpow (Units.map O.subtype.toMonoidHom) u n)
      _ = (u.val : E) ^ n := Units.val_zpow_eq_zpow_val v' n
  simpa only [y, map_sum, map_mul, hpow, Subring.coe_subtype] using hnorm

variable [CompleteSpace E]

/-- A summable Laurent family with coefficients of norm at most one and a coefficient of norm
one takes a value of norm one on the unit circle if the residue field is infinite. -/
theorem exists_norm_tsum_mul_zpow_eq_one
    [Infinite (ResidueField (Subring.unitClosedBall E))]
    {a : ℤ → E} (ha : Summable a) (hle : ∀ n, ‖a n‖ ≤ 1) {j : ℤ} (hj : ‖a j‖ = 1) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖∑' n : ℤ, a n * u ^ n‖ = 1 := by
  classical
  have hs : {n : ℤ | ¬ ‖a n‖ < 1}.Finite :=
    eventually_cofinite.mp <|
      (tendsto_norm_zero.comp ha.tendsto_cofinite_zero).eventually (gt_mem_nhds zero_lt_one)
  let s := hs.toFinset
  obtain ⟨u, hu, hus⟩ := exists_norm_sum_mul_zpow_eq_one s
    (fun n ↦ ⟨a n, Subring.mem_unitClosedBall.mpr (hle n)⟩)
    (hs.mem_toFinset.mpr (by simp [hj])) hj
  have hnorm (n : ℤ) : ‖a n * u ^ n‖ = ‖a n‖ := by
    rw [norm_mul, norm_zpow, hu, one_zpow, mul_one]
  have hsum : Summable (fun n : ℤ ↦ a n * u ^ n) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hnorm, norm_zero] using ha.tendsto_cofinite_zero.norm
  have htail : ‖∑' n : {n // n ∉ s}, a n.val * u ^ n.val‖ < 1 :=
    (hsum.subtype (· ∉ s)).hasSum.norm_lt_of_forall_norm_lt zero_lt_one fun n ↦ by
      rw [Function.comp_apply, hnorm]
      simpa [s] using n.property
  refine ⟨u, hu, ?_⟩
  rw [← hsum.sum_add_tsum_subtype_compl s,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hus.trans_ne htail.ne'), hus,
    max_eq_left htail.le]

end TauCeti
