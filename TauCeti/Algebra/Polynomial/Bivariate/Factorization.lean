/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.Polynomial.Roots

/-!
# Factorization and specialization of polynomials over polynomial and domain bases

Every nonzero polynomial `P : A[X]` over a commutative semiring without zero divisors satisfying
well-founded divisibility (`WfDvdMonoid A`) decomposes as `C c * s.prod`, where `c : A` is nonzero
and `s` is a multiset of irreducible polynomials of positive natural degree
(`Polynomial.exists_C_mul_multiset_prod_irreducible`). In the bivariate case `A := R[X]`, where
`P : R[X][Y]`, `c` is a factor in the inner variable `X` and each `F ∈ s` is irreducible of
positive outer `Y`-natural degree.

Whenever a ring homomorphism `φ : A →+* K` into an integral domain does not annihilate `P`, the
mapped polynomial `P.map φ` factors as `C (φ c) * (s.map (mapRingHom φ)).prod`, so `P.map φ ≠ 0`
iff `φ c ≠ 0` and `F.map φ ≠ 0` for every `F ∈ s`
(`Polynomial.map_ne_zero_iff_of_eq_C_mul_multiset_prod`), and the root multiplicity of `P.map φ`
at `a` equals the sum of the root multiplicities of `F.map φ` at `a`
(`Polynomial.rootMultiplicity_map_eq_sum`).

In the bivariate specialization `φ = evalRingHom b : R[X] →+* R`, `P.map (evalRingHom b)`
evaluates the coefficient polynomials (the inner variable `X`) at `b`, yielding the univariate
fiber `P(b, Y)`. For any primitive bivariate polynomial `F : R[X][Y]`, this inner-variable
specialization `F(b, Y)` is nonzero for every `b : R`
(`Polynomial.IsPrimitive.map_evalRingHom_ne_zero`).

## Main results

* `Polynomial.exists_C_mul_multiset_prod_irreducible`: decomposition of a nonzero polynomial
  `P : A[X]` into a coefficient-ring factor `c : A` and a multiset `s` of irreducibles of
  positive natural degree.
* `Polynomial.natDegree_eq_sum_of_eq_C_mul_multiset_prod`: outer natural degree of `C c * s.prod`.
* `Polynomial.natDegree_swap_eq_of_eq_C_mul_multiset_prod`: swapped (inner-variable) natural
  degree of a bivariate product `C c * s.prod`.
* `Polynomial.map_eq_C_mul_multiset_prod`: action of a coefficient map `φ` on `C c * s.prod`.
* `Polynomial.map_ne_zero_iff_of_eq_C_mul_multiset_prod`: characterization of `P.map φ ≠ 0` in
  terms of `φ c ≠ 0` and `F.map φ ≠ 0` for all `F ∈ s`.
* `Polynomial.rootMultiplicity_map_eq_sum`: exact root multiplicity formula for `P.map φ` when
  `P = C c * s.prod` and `P.map φ ≠ 0` (in particular for `P(b, Y)` at `Y = a`).
* `Polynomial.IsPrimitive.map_evalRingHom_ne_zero`: specializing the inner variable `X` of a
  primitive bivariate polynomial `F : R[X][Y]` at any `b : R` yields a nonzero polynomial
  `F(b, Y)`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Every nonzero polynomial over a commutative semiring without zero divisors and with
well-founded divisibility factors as `C c * s.prod`, where `c : A` is nonzero and every factor in
`s` is irreducible of positive natural degree. In the bivariate case `A := R[X]`, `c` lies in
`R[X]` and each `F ∈ s` has positive natural degree in the outer variable `Y`. -/
theorem exists_C_mul_multiset_prod_irreducible {A : Type*} [CommSemiring A]
    [NoZeroDivisors A] [WfDvdMonoid A] (P : A[X]) (hP : P ≠ 0) :
    ∃ (c : A) (s : Multiset A[X]), c ≠ 0 ∧
      (∀ F ∈ s, Irreducible F ∧ 0 < F.natDegree) ∧ P = C c * s.prod := by
  classical
  obtain ⟨f, hf_irr, u, hu⟩ := WfDvdMonoid.exists_factors P hP
  have hpart := Multiset.prod_filter_mul_prod_filter_not (s := f)
    (fun F : A[X] ↦ 0 < F.natDegree)
  let fpos := f.filter fun F : A[X] ↦ 0 < F.natDegree
  let fzero := f.filter fun F : A[X] ↦ ¬ 0 < F.natDegree
  have hfzero_eq : fzero.prod = C (fzero.map fun F ↦ F.coeff 0).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id' fzero]
    congr 1
    exact Multiset.map_congr rfl fun F hF ↦
      eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos (Multiset.mem_filter.mp hF).2)
  have hu_deg : (u : A[X]).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit (R := A) u.isUnit
  have hu_eq : (u : A[X]) = C ((u : A[X]).coeff 0) :=
    eq_C_of_natDegree_eq_zero hu_deg
  let c : A := (u : A[X]).coeff 0 * (fzero.map fun F ↦ F.coeff 0).prod
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

/-- Over a commutative semiring without zero divisors, if `P = C c * s.prod` with `c ≠ 0` and all
factors in `s` nonzero, then `P.natDegree` equals the sum of the natural degrees of the factors in
`s`. -/
theorem natDegree_eq_sum_of_eq_C_mul_multiset_prod {A : Type*} [CommSemiring A] [NoZeroDivisors A]
    {P : A[X]} {c : A} {s : Multiset A[X]} (hPeq : P = C c * s.prod) (hc0 : c ≠ 0)
    (hs0 : ∀ F ∈ s, F ≠ 0) :
    P.natDegree = (s.map natDegree).sum := by
  rw [hPeq, natDegree_C_mul hc0, natDegree_multiset_prod s fun h0 ↦ hs0 0 h0 rfl]

/-- Over a commutative semiring without zero divisors, if a bivariate polynomial factors as
`P = C c * s.prod` with `c ≠ 0` and all factors in `s` nonzero, then `(Bivariate.swap P).natDegree`
is `c.natDegree` plus the sum of `(Bivariate.swap F).natDegree` over `F ∈ s`. -/
theorem natDegree_swap_eq_of_eq_C_mul_multiset_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {P : R[X][Y]} {c : R[X]} {s : Multiset R[X][Y]} (hPeq : P = C c * s.prod) (hc0 : c ≠ 0)
    (hs0 : ∀ F ∈ s, F ≠ 0) :
    (Bivariate.swap P).natDegree =
      c.natDegree + (s.map fun F ↦ (Bivariate.swap F).natDegree).sum := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact absurd (Subsingleton.elim c 0) hc0
  have hswap_ne : ∀ q ∈ s.map (Bivariate.swap (R := R)), q ≠ 0 := by
    intro q hq
    obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.mp hq
    simpa using hs0 F hF
  have hmap_c : c.map (C : R →+* R[X]) ≠ 0 := by
    simpa using (Polynomial.map_injective (C : R →+* R[X]) C_injective).ne hc0
  have hswap_prod : (s.map (Bivariate.swap (R := R))).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 ↦ hswap_ne 0 h0 rfl
  rw [hPeq, map_mul, Bivariate.swap_C, map_multiset_prod,
    natDegree_mul hmap_c hswap_prod,
    natDegree_map_eq_of_injective C_injective,
    natDegree_multiset_prod _ fun h0 ↦ hswap_ne 0 h0 rfl,
    Multiset.map_map, Function.comp_def]

/-- Mapping a factorization `P = C c * s.prod` along a coefficient homomorphism `φ` gives
`P.map φ = C (φ c) * (s.map (mapRingHom φ)).prod`. -/
theorem map_eq_C_mul_multiset_prod {A K : Type*} [CommSemiring A] [CommSemiring K] (φ : A →+* K)
    {P : A[X]} {c : A} {s : Multiset A[X]} (hPeq : P = C c * s.prod) :
    P.map φ = C (φ c) * (s.map (mapRingHom φ)).prod := by
  rw [hPeq, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_multiset_prod]

/-- Over a ring without zero divisors, if `P = C c * s.prod`, then `P.map φ ≠ 0` if and only if
`φ c ≠ 0` and `F.map φ ≠ 0` for every factor `F ∈ s`. -/
theorem map_ne_zero_iff_of_eq_C_mul_multiset_prod {A K : Type*} [CommSemiring A] [CommSemiring K]
    [NoZeroDivisors K] {φ : A →+* K} {P : A[X]} {c : A} {s : Multiset A[X]}
    (hPeq : P = C c * s.prod) :
    P.map φ ≠ 0 ↔ φ c ≠ 0 ∧ ∀ F ∈ s, F.map φ ≠ 0 := by
  rw [map_eq_C_mul_multiset_prod φ hPeq, mul_ne_zero_iff, C_ne_zero]
  refine and_congr_right fun hcp ↦ ⟨fun h F hF h0 ↦ ?_, fun h ↦ ?_⟩
  · exact h (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨F, hF, h0⟩))
  · have : Nontrivial K := ⟨⟨φ c, 0, hcp⟩⟩
    exact Multiset.prod_ne_zero fun h0 ↦
      let ⟨F, hF, hFeq⟩ := Multiset.mem_map.mp h0
      h F hF hFeq

/-- Over an integral domain `K`, if `P = C c * s.prod` in `A[X]` and `P.map φ ≠ 0` for a ring
homomorphism `φ : A →+* K`, then the root multiplicity of `P.map φ` at `a` equals the sum of the
root multiplicities of `F.map φ` at `a` over `F ∈ s`. In the bivariate specialization `A := R[X]`
and `φ = evalRingHom b`, this computes the fiberwise root multiplicity of `P(b, Y)` at `Y = a`. -/
theorem rootMultiplicity_map_eq_sum {A K : Type*} [CommSemiring A] [CommRing K] [IsDomain K]
    {φ : A →+* K} {P : A[X]} {c : A} {s : Multiset A[X]}
    (hPeq : P = C c * s.prod) (hPmap : P.map φ ≠ 0) (a : K) :
    (P.map φ).rootMultiplicity a =
      (s.map fun F ↦ (F.map φ).rootMultiplicity a).sum := by
  obtain ⟨hcp, hs_ne⟩ := (map_ne_zero_iff_of_eq_C_mul_multiset_prod hPeq).mp hPmap
  have hmap_ne : ∀ p ∈ s.map (mapRingHom φ), p ≠ 0 := by
    intro p hp
    obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.mp hp
    rw [coe_mapRingHom]
    exact hs_ne F hF
  have hmap_prod_ne : (s.map (mapRingHom φ)).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 ↦ hmap_ne 0 h0 rfl
  rw [map_eq_C_mul_multiset_prod φ hPeq,
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hcp) hmap_prod_ne),
    rootMultiplicity_eq_zero (by simpa using hcp), zero_add,
    rootMultiplicity_multiset_prod a _ hmap_ne, Multiset.map_map]
  simp only [Function.comp_apply, coe_mapRingHom]

/-- Over a nontrivial commutative ring, specializing the inner variable `X` (i.e. evaluating the
coefficient polynomials in `R[X]`) of a primitive bivariate polynomial `F : R[X][Y]` at any scalar
`b : R` yields a nonzero univariate polynomial `F(b, Y)` (unlike specializing the outer variable
`Y`, which can vanish). -/
theorem IsPrimitive.map_evalRingHom_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {F : R[X][Y]} (hF : F.IsPrimitive) (b : R) :
    F.map (evalRingHom b) ≠ 0 := by
  intro h0
  have hdvd : C (X - C b) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot, IsRoot]
    have hi : (F.map (evalRingHom b)).coeff i = 0 := by rw [h0, coeff_zero]
    simpa [coeff_map] using hi
  exact not_isUnit_X_sub_C b (hF _ hdvd)

end Polynomial
