/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Zero loci of polynomials are Haar-null

Let `R` be a T0 (hence Hausdorff), locally compact, second countable topological integral domain
in which `0` is not isolated, for instance the ring of integers of a nonarchimedean local field.
The zero locus of a nonzero polynomial in finitely many variables over `R` is null for every
additive Haar measure on `ι → R`. Indeed the additive Haar measure of `R` vanishes on points, so
the zero locus is null for the product of these measures
(`MvPolynomial.measure_pi_setOfPred_eval_eq_zero`), which is a Haar measure on `ι → R`; and Haar
measures on a second countable group have the same null sets.

This is the polynomial case of the statement that analytic functions vanishing on no nonempty open
set have Haar-null zero sets, as used in the reference below.

## Main results

* `MvPolynomial.addHaar_setOfPred_eval_eq_zero`: the zero locus of a nonzero polynomial is null
  for every additive Haar measure.

## References

* J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. Math. IHÉS 54
  (1981), §6.4, proof of Proposition 13, p. 168.
-/

public section

open MeasureTheory Topology

namespace MvPolynomial

/-- **Zero loci of polynomials are Haar-null.** Let `R` be a T0 (hence Hausdorff), locally
compact, second countable topological integral domain in which `0` is not isolated. The zero locus
of a nonzero polynomial in finitely many variables over `R` is null for every additive Haar measure
on `ι → R`. -/
theorem addHaar_setOfPred_eval_eq_zero {R ι : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [IsTopologicalRing R] [T0Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [(𝓝[≠] (0 : R)).NeBot] [MeasurableSpace R] [BorelSpace R]
    [Finite ι] (μ : Measure (ι → R)) [μ.IsAddHaarMeasure] (P : MvPolynomial ι R)
    (hP : P ≠ 0) : μ {x | eval x P = 0} = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  exact Measure.absolutelyContinuous_isAddHaarMeasure μ (Measure.pi fun _ => Measure.addHaar)
    (measure_pi_setOfPred_eval_eq_zero _ P hP)

end MvPolynomial
