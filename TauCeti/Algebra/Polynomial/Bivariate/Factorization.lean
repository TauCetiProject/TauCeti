/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Factorization of bivariate polynomials

Every nonzero bivariate polynomial `P : R[X][Y]` over a domain with well-founded divisibility
(`WfDvdMonoid R`) decomposes as `C c * l.prod`, where `c : R[X]` is a nonzero factor from the
coefficient ring `R[X]` and `l` is a list of irreducible bivariate polynomials of positive outer
`Y`-natural degree (`0 < F.natDegree`).

## Main results

* `Polynomial.exists_C_mul_list_prod_irreducible`: decomposition of a nonzero bivariate
  polynomial into a coefficient-ring factor in `R[X]` and irreducibles of positive outer
  `Y`-natural degree.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Every nonzero bivariate polynomial over a well-founded divisibility domain factors as
`C c * l.prod`, where `c : R[X]` is nonzero and every factor in `l` is irreducible of positive
natural degree in the outer variable `Y`. -/
theorem exists_C_mul_list_prod_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (P : R[X][Y]) (hP : P ≠ 0) :
    ∃ (c : R[X]) (l : List R[X][Y]), c ≠ 0 ∧
      (∀ F ∈ l, Irreducible F ∧ 0 < F.natDegree) ∧ P = C c * l.prod := by
  classical
  obtain ⟨f, hf_irr, u, hu⟩ := WfDvdMonoid.exists_factors P hP
  have hpart := Multiset.prod_filter_mul_prod_filter_not (s := f)
    (fun F : R[X][Y] ↦ 0 < F.natDegree)
  let fpos := f.filter fun F : R[X][Y] ↦ 0 < F.natDegree
  let fzero := f.filter fun F : R[X][Y] ↦ ¬ 0 < F.natDegree
  have hfzero_eq : fzero.prod = C (fzero.map fun F ↦ F.coeff 0).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id' fzero]
    congr 1
    exact Multiset.map_congr rfl fun F hF ↦
      eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos (Multiset.mem_filter.mp hF).2)
  have hu_deg : (u : R[X][Y]).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit (R := R[X]) u.isUnit
  have hu_eq : (u : R[X][Y]) = C ((u : R[X][Y]).coeff 0) :=
    eq_C_of_natDegree_eq_zero hu_deg
  let c : R[X] := (u : R[X][Y]).coeff 0 * (fzero.map fun F ↦ F.coeff 0).prod
  have hP_eq : P = C c * fpos.prod := by
    rw [← hu, ← hpart, hfzero_eq, hu_eq]
    simp only [c, map_mul]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    apply hP
    rw [hP_eq, h0, map_zero, zero_mul]
  refine ⟨c, fpos.toList, hc0, ?_, ?_⟩
  · intro F hF
    have hF' := Multiset.mem_filter.mp (Multiset.mem_toList.mp hF)
    exact ⟨hf_irr F hF'.1, hF'.2⟩
  · simpa [Multiset.prod_toList] using hP_eq

end Polynomial
