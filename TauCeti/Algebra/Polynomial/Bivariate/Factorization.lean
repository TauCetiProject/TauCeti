/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.Polynomial.Roots

/-!
# Factorization of bivariate polynomials

Every nonzero bivariate polynomial `P : R[X][Y]` over a domain with well-founded divisibility
(`WfDvdMonoid R`) decomposes as `C c * s.prod`, where `c : R[X]` is a nonzero factor from the
coefficient ring `R[X]` and `s` is a multiset of irreducible bivariate polynomials of positive outer
`Y`-natural degree (`0 < F.natDegree`).

When specializing `P` at `b` kills neither `c` nor any factor `F ∈ s`, the root multiplicity of
`P.map (evalRingHom b)` at `a` equals the sum of the root multiplicities of the specialized factors
(`Polynomial.rootMultiplicity_map_evalRingHom_eq_sum`).

## Main results

* `Polynomial.exists_C_mul_multiset_prod_irreducible`: decomposition of a nonzero bivariate
  polynomial into a coefficient-ring factor in `R[X]` and a multiset of irreducibles of positive
  outer `Y`-natural degree.
* `Polynomial.rootMultiplicity_map_evalRingHom_eq_sum`: exact fiberwise root multiplicity formula
  for a bivariate factorization `P = C c * s.prod`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Every nonzero bivariate polynomial over a well-founded divisibility domain factors as
`C c * s.prod`, where `c : R[X]` is nonzero and every factor in `s` is irreducible of positive
natural degree in the outer variable `Y`. -/
theorem exists_C_mul_multiset_prod_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (P : R[X][Y]) (hP : P ≠ 0) :
    ∃ (c : R[X]) (s : Multiset R[X][Y]), c ≠ 0 ∧
      (∀ F ∈ s, Irreducible F ∧ 0 < F.natDegree) ∧ P = C c * s.prod := by
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
  refine ⟨c, fpos, hc0, ?_, hP_eq⟩
  intro F hF
  have hF' := Multiset.mem_filter.mp hF
  exact ⟨hf_irr F hF'.1, hF'.2⟩

/-- Over an integral domain, if `P = C c * s.prod` and specialization at `b` kills neither `c`
nor any factor in `s`, then the fiberwise root multiplicity of `P(X, b)` at `a` equals the sum of
the fiberwise root multiplicities of the factors `F ∈ s`. -/
theorem rootMultiplicity_map_evalRingHom_eq_sum {K : Type*} [CommRing K] [IsDomain K]
    {P : K[X][Y]} {c : K[X]} {s : Multiset K[X][Y]}
    (hPeq : P = C c * s.prod) {a b : K} (hcp : c.eval b ≠ 0)
    (hs_ne : ∀ F ∈ s, F.map (evalRingHom b) ≠ 0) :
    (P.map (evalRingHom b)).rootMultiplicity a =
      (s.map fun F ↦ (F.map (evalRingHom b)).rootMultiplicity a).sum := by
  have hmap_ne : ∀ p ∈ s.map (mapRingHom (evalRingHom b)), p ≠ 0 := by
    intro p hp
    obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.mp hp
    rw [coe_mapRingHom]
    exact hs_ne F hF
  have hmap_prod_ne : (s.map (mapRingHom (evalRingHom b))).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 ↦ hmap_ne 0 h0 rfl
  have hPmap_eq :
      P.map (evalRingHom b) = C (c.eval b) * (s.map (mapRingHom (evalRingHom b))).prod := by
    rw [hPeq, Polynomial.map_mul, map_C, coe_evalRingHom, ← coe_mapRingHom, map_multiset_prod]
  rw [hPmap_eq, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hcp) hmap_prod_ne),
    rootMultiplicity_eq_zero (by simpa using hcp), zero_add,
    rootMultiplicity_multiset_prod a _ hmap_ne, Multiset.map_map]
  simp only [Function.comp_apply, coe_mapRingHom]

end Polynomial
