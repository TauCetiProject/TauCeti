/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.AggregateWeight

/-!
# Row degrees in standard bideterminant coordinates

The degree in a row of variables of a standard bideterminant is the content of its tableau
at that row. In coordinates indexed by classes and by products of standard bases, the sum
of these degrees is the same for every row. The formula counts the powers charged when one
row of variables is scaled in integral coordinates on a space of forms.

The total-degree computation is the mean-degree step `New.Data.sumDegreeOf_eq` and
`New.Data.mul_sumDegreeOf_le` in `grh/src/New/UpperBound/Divisibility/ColengthAtLevel.lean`
of lsernau/grh-lean (revision `72fead1`). Here the average is computed exactly from the
semistandard tableau basis.
-/

public section

open Finset MvPolynomial

namespace TauCeti.DualWeylModule

/-- The degree of a standard bideterminant in the variables in row `a` is the number of
occurrences of `a` in its tableau. -/
@[simp] theorem weightedTotalDegree_bideterminant_ssytFilling (R : Type*)
    [CommRing R] [Nontrivial R] {N n : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (T : BoundedSSYT N μ) (a : Fin N) :
    weightedTotalDegree (rowWeight a) (bideterminant R μ hμ (ssytFilling T)) = T.weight a := by
  let p := bideterminant R μ hμ (ssytFilling T)
  have hp : p ≠ 0 := by
    dsimp only [p]
    rw [← coe_standardBasis, ne_eq, Submodule.coe_eq_zero]
    exact (standardBasis R N hμ).ne_zero T
  have hhom : IsWeightedHomogeneous (rowWeight a) p (T.weight a) := by
    simpa only [BoundedSSYT.weight_apply] using
      isWeightedHomogeneous_bideterminant (R := R) hμ T a
  calc
    _ = p.support.sup (fun _ ↦ T.weight a) :=
      Finset.sup_congr rfl fun _ hd ↦ hhom (mem_support_iff.mp hd)
    _ = _ := Finset.sup_const (support_nonempty.mpr hp) _

/-- In a family of standard bideterminant bases, take one basis coordinate at each place and
add its degrees in row `a`. Summing over all such choices and all classes, then multiplying by
the number of rows, gives the number of coordinates times the total size of the shapes. -/
theorem card_mul_sum_prod_sum_weightedTotalDegree_standardBasis (R : Type*) [CommRing R]
    [Nontrivial R] {C σ : Type*} [Fintype C] [Fintype σ] [DecidableEq σ] {N : ℕ}
    {n : σ → ℕ} (μ : σ → YoungDiagram) (hμ : ∀ w, (μ w).colLen 0 ≤ n w) (a : Fin N) :
    N * (∑ v : C × (∀ w, BoundedSSYT N (μ w)), ∑ w,
      weightedTotalDegree (rowWeight a)
        (standardBasis R N (hμ w) (v.2 w) : MvPolynomial (Fin N × Fin (n w)) R)) =
      Fintype.card (C × (∀ w, BoundedSSYT N (μ w))) * ∑ w, (μ w).card := by
  simpa only [coe_standardBasis, weightedTotalDegree_bideterminant_ssytFilling] using
    (BoundedSSYT.card_mul_sum_prod_sum_weight_apply (C := C) μ a)

end TauCeti.DualWeylModule
