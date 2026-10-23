/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FredholmDet
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent

/-!
# Fredholm series along idempotent decompositions

Let `R` be a complete ultrametric normed commutative ring with Tate scalars and `I` a discrete
index type. For an endomorphism `u` of the model space `C₀(I, R)`, the Fredholm series
`H_u(T) = det (1 - T u)` is the principal-minor series `u.matrixCoeff.charPowerSeries` of its
matrix.

If `u` and `v` are row compact and `u v = 0`, then `(1 - T u) (1 - T v) = 1 - T (u + v)`, and
correspondingly

`H_(u + v) = H_u H_v`
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_add_of_mul_eq_zero`).

No commutativity is needed. The proof evaluates both sides at every scalar `a`, where the identity
is the multiplicativity of the Fredholm determinant applied to `a • u` and `a • v`, and then uses
that an entire series over Tate scalars is determined by its values
(`PowerSeries.IsEntire.eq_of_forall_evalAt_eq`), since the powers of a pseudo-uniformiser are
non-zero-divisors tending to `0`
(`TauCeti.HasZeroSequenceOfUnits.frequently_mem_nonZeroDivisors_nhds_zero`).

Consequently, if a row-compact `u` commutes with a bounded idempotent `e`, then

`H_u = H_(u e) H_(u (1 - e))`
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_eq_mul_of_commute`),

and more generally `H_u = ∏ᵢ H_(u eᵢ)` for a complete family of orthogonal idempotents `eᵢ`
commuting with a row-compact `u`. Here `u e` and `u (1 - e)` are again endomorphisms of
`C₀(I, R)`: they are the extensions of the restrictions of `u` to the invariant summands
`range e` and `range (1 - e)` through the presentations of these summands as retracts of
`C₀(I, R)`. This is a statement about a specified decomposition; it does not assert
multiplicativity of `H` on arbitrary products.

When the idempotent `e` is itself row compact, its range is finitely generated projective
(`ContinuousLinearMap.IsRowCompact.projective_range_of_isIdempotentElem`), and the factor `H_(u e)`
is a polynomial for every continuous `u`
(`ContinuousLinearMap.IsRowCompact.exists_charPowerSeries_matrixCoeff_mul_eq_coe`). Indeed
`e = e π_S e w` for a finite coordinate projection `π_S` and a continuous `w`, so by cyclicity
`H_(u e)` is the Fredholm series of `π_S (e w u e)`, the polynomial determinant of a finite block.
Thus, if a row-compact `u` commutes with a row-compact idempotent `e`, the finite projective
invariant summand `range e` splits off a polynomial factor `H_(u e)` of `H_u`, and the
complementary factor is the Fredholm series `H_(u (1 - e))` on the invariant complement
`range (1 - e)`.

## Main results

* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_add_of_mul_eq_zero`:
  `H_(u + v) = H_u H_v` when `u v = 0`.
* `ContinuousLinearMap.charPowerSeries_matrixCoeff_sum_of_mul_eq_zero`: the finite version for
  pairwise annihilating row-compact operators.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_eq_prod_of_commute`:
  `H_u = ∏ᵢ H_(u eᵢ)` for a complete family of orthogonal idempotents commuting with `u`.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_eq_mul_of_commute`:
  `H_u = H_(u e) H_(u (1 - e))` for an idempotent `e` commuting with `u`.
* `ContinuousLinearMap.IsRowCompact.exists_charPowerSeries_matrixCoeff_mul_eq_coe`: for a
  row-compact idempotent `e`, the Fredholm series of `u e` is a polynomial.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

namespace ContinuousLinearMap

/-- **Multiplicativity of Fredholm series for annihilating operators.** If `u` and `v` are
row-compact endomorphisms of `C₀(I, R)` with `u v = 0`, then `det (1 - T (u + v))` is the product
of `det (1 - T u)` and `det (1 - T v)`, reflecting `(1 - T u) (1 - T v) = 1 - T (u + v)`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_add_of_mul_eq_zero
    {u v : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (hv : v.IsRowCompact)
    (huv : u * v = 0) :
    (u + v).matrixCoeff.charPowerSeries =
      u.matrixCoeff.charPowerSeries * v.matrixCoeff.charPowerSeries := by
  refine (hu.add hv).isEntire_charPowerSeries.eq_of_forall_evalAt_eq
    (hu.isEntire_charPowerSeries.mul hv.isEntire_charPowerSeries)
    TauCeti.HasZeroSequenceOfUnits.frequently_mem_nonZeroDivisors_nhds_zero fun a ↦ ?_
  -- At `a`, this is the multiplicativity of the Fredholm determinant for `a • u` and `a • v`,
  -- since `a • u + a • v - (a • u) (a • v) = a • (u + v)`.
  have hsmul : a • u + a • v - (a • u) * (a • v) = a • (u + v) := by
    have h0 : (a • u) * (a • v) = 0 := by
      ext x : 1
      have hx : u (v x) = 0 := congr($huv x)
      simp [hx]
    -- The operator subtraction only unfolds to the additive group subtraction at default
    -- transparency, so `sub_zero` is applied by `exact` rather than `rw`.
    rw [h0]
    exact (sub_zero _).trans (smul_add a u v).symm
  rw [← (hu.add hv).fredholmDet_smul, ← hsmul, (hu.smul a).fredholmDet_add_sub_mul (hv.smul a),
    hu.fredholmDet_smul, hv.fredholmDet_smul,
    hu.isEntire_charPowerSeries.evalAt_mul hv.isEntire_charPowerSeries]

/-- **Multiplicativity of Fredholm series for a finite annihilating family.** If the
endomorphisms `u i` of `C₀(I, R)`, for `i ∈ s`, are row compact and `u i * u j = 0` for `i ≠ j`,
then `det (1 - T ∑ᵢ u i) = ∏ᵢ det (1 - T u i)`. -/
theorem charPowerSeries_matrixCoeff_sum_of_mul_eq_zero {ι : Type*} {s : Finset ι}
    {u : ι → C₀(I, R) →L[R] C₀(I, R)} (hu : ∀ i ∈ s, (u i).IsRowCompact)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → u i * u j = 0) :
    (∑ i ∈ s, u i).matrixCoeff.charPowerSeries =
      ∏ i ∈ s, (u i).matrixCoeff.charPowerSeries := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixCoeff_zero, Matrix.charPowerSeries_zero]
  | insert i s hi ih =>
    have hs : (∑ j ∈ s, u j).IsRowCompact :=
      Finset.sum_induction u (fun w : C₀(I, R) →L[R] C₀(I, R) ↦ w.IsRowCompact)
        (fun _ _ ↦ IsRowCompact.add) isRowCompact_zero fun j hj ↦ hu j (by simp [hj])
    have hmul : u i * ∑ j ∈ s, u j = 0 := by
      rw [Finset.mul_sum (R := C₀(I, R) →L[R] C₀(I, R))]
      exact Finset.sum_eq_zero fun j hj ↦ h i (by simp) j (by simp [hj]) fun hij ↦ hi (hij ▸ hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      (hu i (by simp)).charPowerSeries_matrixCoeff_add_of_mul_eq_zero hs hmul,
      ih (fun j hj ↦ hu j (by simp [hj]))
        fun j hj k hk ↦ h j (by simp [hj]) k (by simp [hk])]

/-- **The finite partition formula.** If a row-compact endomorphism `u` of `C₀(I, R)` commutes
with a complete family of orthogonal idempotents `e i`, then its Fredholm series is the product
`det (1 - T u) = ∏ᵢ det (1 - T u e i)` of the Fredholm series of its parts on the invariant
summands `range (e i)`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_eq_prod_of_commute {ι : Type*} [Fintype ι]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {e : ι → C₀(I, R) →L[R] C₀(I, R)}
    (he : CompleteOrthogonalIdempotents e) (hue : ∀ i, Commute u (e i)) :
    u.matrixCoeff.charPowerSeries = ∏ i, (u * e i).matrixCoeff.charPowerSeries := by
  conv_lhs => rw [← mul_one u, ← he.complete, Finset.mul_sum (R := C₀(I, R) →L[R] C₀(I, R))]
  refine charPowerSeries_matrixCoeff_sum_of_mul_eq_zero (fun i _ ↦ hu.comp_clm (e i))
    fun i _ j _ hij ↦ ?_
  -- `(u eᵢ) (u eⱼ) = u u eᵢ eⱼ = 0` for `i ≠ j`.
  rw [mul_assoc, ← mul_assoc (e i), ← (hue i).eq, mul_assoc u (e i), he.ortho hij, mul_zero,
    mul_zero]

/-- **Splitting along a commuting idempotent.** If a row-compact endomorphism `u` of `C₀(I, R)`
commutes with an idempotent `e`, then `det (1 - T u) = det (1 - T u e) det (1 - T u (1 - e))`:
the Fredholm series is the product of those of its parts on the invariant summands `range e` and
`range (1 - e)`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_eq_mul_of_commute
    {u e : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (he : IsIdempotentElem e)
    (hue : Commute u e) :
    u.matrixCoeff.charPowerSeries =
      (u * e).matrixCoeff.charPowerSeries * (u * (1 - e)).matrixCoeff.charPowerSeries := by
  rw [hu.charPowerSeries_matrixCoeff_eq_prod_of_commute (e := ![e, 1 - e])
    (CompleteOrthogonalIdempotents.of_isIdempotentElem (R := C₀(I, R) →L[R] C₀(I, R)) he)
      fun i ↦ by
        fin_cases i
        exacts [hue, (Commute.one_right u).sub_right (R := C₀(I, R) →L[R] C₀(I, R)) hue],
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **Row-compact idempotents split off polynomial factors.** If `e` is a row-compact idempotent
endomorphism of `C₀(I, R)`, whose range is then finitely generated projective, the Fredholm series
`det (1 - T u e)` is a polynomial for every continuous endomorphism `u`. -/
theorem IsRowCompact.exists_charPowerSeries_matrixCoeff_mul_eq_coe
    {e : C₀(I, R) →L[R] C₀(I, R)} (he : e.IsRowCompact) (he' : IsIdempotentElem e)
    (u : C₀(I, R) →L[R] C₀(I, R)) :
    ∃ Q : Polynomial R, (u * e).matrixCoeff.charPowerSeries = (Q : PowerSeries R) := by
  obtain ⟨S, hS⟩ := he.exists_ringOpNorm_sub_mul_indicatorCLM_mul_lt_one he'
  obtain ⟨w, hw⟩ := exists_mul_mul_mul_eq_of_isIdempotentElem he' hS
  set c : C₀(I, R) →L[R] C₀(I, R) := indicatorCLM R (S : Set I)
  have hc : c.IsRowCompact := by
    simpa only [comp_id] using
      isRowCompact_indicatorCLM_comp S (ContinuousLinearMap.id R C₀(I, R))
  -- `u e = (u e c) (e w)` since `e = e c e w`; cycle the row-compact factor `u e c` to the right,
  -- then cycle the coordinate projection `c` to the left.
  have huec : (u * e * c).IsRowCompact := by
    rw [mul_assoc, mul_def, mul_def]
    exact (he.comp_clm c).clm_comp u
  refine ⟨((e * w * u * e).matrixCoeff.submatrix (Subtype.val : S → I) Subtype.val).charpolyRev,
    ?_⟩
  calc (u * e).matrixCoeff.charPowerSeries
      = (u * e * c * (e * w)).matrixCoeff.charPowerSeries := by
        conv_lhs => rw [← hw]
        simp only [mul_assoc]
    _ = (e * w * (u * e * c)).matrixCoeff.charPowerSeries :=
        huec.charPowerSeries_matrixCoeff_mul_comm _
    _ = (c * (e * w * u * e)).matrixCoeff.charPowerSeries := by
        rw [hc.charPowerSeries_matrixCoeff_mul_comm]
        simp only [mul_assoc]
    _ = _ := charPowerSeries_matrixCoeff_indicatorCLM_comp S _

end ContinuousLinearMap
