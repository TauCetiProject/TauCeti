/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Tschirnhaus transforms of a polynomial

For `f T : R[X]` with `f` monic, the Tschirnhaus transform `Polynomial.tschirnhausPolynomial f T`
is the polynomial that replaces each root `α` of `f` by the value `T(α)`: in a domain in which `f`
splits, its roots are exactly those values, listed with multiplicity. It is defined as the
two-variable resultant `Res_Y(f(Y), X - T(Y))`, so it is a function of the coefficients of `f` and
`T` alone: no splitting field is chosen, and the construction makes sense over any commutative
ring.

The defining resultant is taken in `(R[X])[Y]`, where `f.map C` is `f(Y)` and `C X - T.map C` is
`X - T(Y)`. Over a domain in which `f` splits, expanding the resultant along the roots of `f`
gives the product formula `∏ (X - C (T.eval α))`, and from it the monicity and the degree of the
transform, which hold over every domain by base change to a splitting field of `f`.

The point of the construction is to *choose* `T`: classically one picks a transform that separates
the roots of `f`, so that a resolvent which took a repeated value at the roots of `f` no longer
does at the roots of the transform. An arbitrary `T` achieves neither — it need not separate the
roots, and it need not preserve the Galois group. It is for a separable `f` and such an admissible
`T` that the Galois group is unchanged; that field-theoretic half is in
`TauCeti/FieldTheory/GaloisGroups/Tschirnhaus.lean`.

## Main declarations

* `Polynomial.tschirnhausPolynomial`: the transform, as a two-variable resultant.

## Main results

* `Polynomial.tschirnhausPolynomial_def`: the defining resultant, and
  `Polynomial.Monic.tschirnhausPolynomial_eq_resultant`: the transform computed with any valid
  degree bound for `T`.
* `Polynomial.tschirnhausPolynomial_X_add_C`: transforming along a shift is the substitution
  `X ↦ X - c` that depresses a polynomial.
* `Polynomial.Monic.map_tschirnhausPolynomial`: the transform commutes with base change.
* `Polynomial.Monic.tschirnhausPolynomial_eq_prod`: the product formula over a domain in which
  `f` splits, with `Polynomial.Monic.roots_tschirnhausPolynomial` reading the roots off it.
* `Polynomial.Monic.tschirnhausPolynomial`, `Polynomial.Monic.natDegree_tschirnhausPolynomial`:
  the transform of a monic polynomial over a domain is monic of the same degree.
* `Polynomial.tschirnhausPolynomial_X`, `Polynomial.tschirnhausPolynomial_C`,
  `Polynomial.tschirnhausPolynomial_X_sub_C`: the transform along `X`, along a constant, and of a
  linear polynomial.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §6.3.
-/

public section

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {f T : R[X]}

/-- The **Tschirnhaus transform** of `f` along `T`: the resultant `Res_Y(f(Y), X - T(Y))`, taken
in `(R[X])[Y]`. For monic `f` over a domain it is monic of the same degree as `f`, and in a domain
in which `f` splits its roots are the values of `T` at the roots of `f`. -/
def tschirnhausPolynomial (f T : R[X]) : R[X] :=
  (f.map (C : R →+* R[X])).resultant (C X - T.map C)

/-- The Tschirnhaus transform, unfolded to its defining resultant. -/
theorem tschirnhausPolynomial_def (f T : R[X]) :
    f.tschirnhausPolynomial T = (f.map (C : R →+* R[X])).resultant (C X - T.map C) := (rfl)

/-- The polynomial `X - T(Y)`, read in `Y`, has degree at most that of `T`. -/
private theorem natDegree_C_X_sub_map_C_le (T : R[X]) {k : ℕ} (hT : T.natDegree ≤ k) :
    (C X - T.map (C : R →+* R[X])).natDegree ≤ k :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_map_le.trans hT))

/-- The Tschirnhaus transform may be computed with any valid degree bound for `T` in place of
`T.natDegree`. This is what makes the transform stable under a base change that lowers the degree
of `T`. -/
theorem Monic.tschirnhausPolynomial_eq_resultant (hf : f.Monic) (T : R[X]) {k : ℕ}
    (hT : T.natDegree ≤ k) :
    f.tschirnhausPolynomial T = (f.map C).resultant (C X - T.map C) f.natDegree k := by
  rw [tschirnhausPolynomial, ← natDegree_map_eq_of_injective C_injective f,
    (hf.map (C : R →+* R[X])).resultant_of_le (natDegree_C_X_sub_map_C_le T hT)]

/-- **The Tschirnhaus transform commutes with base change.** No hypothesis on `T` is needed: the
transform reads the coefficients of `f` and `T`, and `Polynomial.map` commutes with that. -/
@[simp]
theorem Monic.map_tschirnhausPolynomial (hf : f.Monic) (T : R[X]) (φ : R →+* S) :
    (f.tschirnhausPolynomial T).map φ = (f.map φ).tschirnhausPolynomial (T.map φ) := by
  nontriviality S
  -- mapping the coefficients commutes with adjoining a variable
  have hC : ∀ p : R[X], (p.map (C : R →+* R[X])).map (mapRingHom φ) =
      (p.map φ).map (C : S →+* S[X]) := fun p ↦ by
    rw [map_map, map_map, mapRingHom_comp_C]
  rw [hf.tschirnhausPolynomial_eq_resultant T le_rfl,
    (hf.map φ).tschirnhausPolynomial_eq_resultant (T.map φ) (natDegree_map_le (f := φ) (p := T)),
    hf.natDegree_map φ]
  have h : (C X - T.map (C : R →+* R[X])).map (mapRingHom φ) =
      C X - (T.map φ).map (C : S →+* S[X]) := by
    rw [Polynomial.map_sub, map_C, hC, coe_mapRingHom, map_X]
  rw [← hC, ← h, resultant_map_map, coe_mapRingHom]

/-- **The product formula for the Tschirnhaus transform.** Over a domain in which `f` splits, the
transform of a monic `f` is the product of `X - T(α)` over the roots `α` of `f`, counted with
multiplicity. -/
theorem Monic.tschirnhausPolynomial_eq_prod [IsDomain R] (hf : f.Monic) (hsp : f.Splits)
    (T : R[X]) :
    f.tschirnhausPolynomial T = (f.roots.map fun α ↦ X - C (T.eval α)).prod := by
  rw [tschirnhausPolynomial, resultant_eq_prod_eval _ _ _ le_rfl (hsp.map (C : R →+* R[X])),
    (hf.map (C : R →+* R[X])).leadingCoeff, one_pow, one_mul,
    hsp.roots_map_of_injective C_injective, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ ↦ ?_
  simp [eval_map, eval₂_at_apply]

/-- Reassociate the product of the formula above through the multiset of transformed roots, which
is the shape that `Polynomial.roots_multiset_prod_X_sub_C` and
`Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` read. -/
private theorem map_X_sub_C_eval (T : R[X]) (s : Multiset R) :
    (s.map fun α ↦ X - C (T.eval α)) = (s.map T.eval).map fun a ↦ X - C a := by
  rw [Multiset.map_map]; rfl

/-- **The roots of a Tschirnhaus transform are the values of `T` at the roots.** Over a domain in
which `f` splits, this is an equality of multisets, so multiplicities are matched too. -/
@[simp]
theorem Monic.roots_tschirnhausPolynomial [IsDomain R] (hf : f.Monic) (hsp : f.Splits)
    (T : R[X]) : (f.tschirnhausPolynomial T).roots = f.roots.map T.eval := by
  rw [hf.tschirnhausPolynomial_eq_prod hsp, map_X_sub_C_eval T f.roots,
    roots_multiset_prod_X_sub_C]

/-- The monicity and the degree of a Tschirnhaus transform over an arbitrary domain, proved
together because they share one base change: along the embedding of `R` into a splitting field of
`f` over the fraction field, the transform becomes the product formula above. The two halves are
stated separately below. -/
private theorem monic_and_natDegree_tschirnhausPolynomial [IsDomain R] (hf : f.Monic) (T : R[X]) :
    (f.tschirnhausPolynomial T).Monic ∧
      (f.tschirnhausPolynomial T).natDegree = f.natDegree := by
  set K := FractionRing R
  set L := (f.map (algebraMap R K)).SplittingField
  set φ := (algebraMap K L).comp (algebraMap R K) with hφ
  have hinj : Function.Injective φ :=
    (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective R K)
  have hsp : (f.map φ).Splits := by
    rw [hφ, ← map_map]
    exact IsSplittingField.splits _ _
  have hprod : (f.tschirnhausPolynomial T).map φ =
      (((f.map φ).roots.map (T.map φ).eval).map fun a ↦ X - C a).prod := by
    rw [hf.map_tschirnhausPolynomial T φ, (hf.map φ).tschirnhausPolynomial_eq_prod hsp,
      map_X_sub_C_eval (T.map φ) (f.map φ).roots]
  refine ⟨?_, ?_⟩
  · rw [hinj.monic_map_iff, hprod]
    exact monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C _
  · have h : ((f.tschirnhausPolynomial T).map φ).natDegree = f.natDegree := by
      rw [hprod, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map,
        ← hsp.natDegree_eq_card_roots, hf.natDegree_map]
    rwa [natDegree_map_eq_of_injective hinj] at h

/-- **A Tschirnhaus transform preserves the degree.** -/
@[simp]
theorem Monic.natDegree_tschirnhausPolynomial [IsDomain R] (hf : f.Monic) (T : R[X]) :
    (f.tschirnhausPolynomial T).natDegree = f.natDegree :=
  (monic_and_natDegree_tschirnhausPolynomial hf T).2

/-- **A Tschirnhaus transform of a monic polynomial is monic.** -/
theorem Monic.tschirnhausPolynomial [IsDomain R] (hf : f.Monic) (T : R[X]) :
    (f.tschirnhausPolynomial T).Monic :=
  (monic_and_natDegree_tschirnhausPolynomial hf T).1

/-- The transform along `X` is the identity: `X` fixes every root. -/
@[simp]
theorem tschirnhausPolynomial_X (f : R[X]) : f.tschirnhausPolynomial X = f := by
  nontriviality R
  have h : (C X - X : (R[X])[X]).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X]
  rw [tschirnhausPolynomial, map_X, h, resultant_C_sub_X_right _ _ _ le_rfl, eval_map, eval₂_C_X]

/-- The transform along a constant collapses every root to that constant. -/
@[simp]
theorem tschirnhausPolynomial_C (f : R[X]) (c : R) :
    f.tschirnhausPolynomial (C c) = (X - C c) ^ f.natDegree := by
  rw [tschirnhausPolynomial, map_C, ← C_sub, natDegree_C, resultant_C_zero_right,
    natDegree_map_eq_of_injective C_injective]

/-- **The transform along a shift is the classical substitution.** Transforming along `X + c`
translates every root by `c`, which on the coefficient side is the substitution `X ↦ X - c` used
to depress a polynomial. -/
@[simp]
theorem tschirnhausPolynomial_X_add_C (f : R[X]) (c : R) :
    f.tschirnhausPolynomial (X + C c) = f.comp (X - C c) := by
  nontriviality R
  have hrw : (C X - (X + C c).map (C : R →+* R[X])) = C (X - C c) - X := by
    rw [Polynomial.map_add, map_X, map_C, C_sub]
    ring
  have hdeg : ((C (X - C c) - X : (R[X])[X])).natDegree = 1 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X]
  rw [tschirnhausPolynomial, hrw, hdeg, resultant_C_sub_X_right _ _ _ le_rfl, eval_map, comp]

/-- The transform of a monic linear polynomial evaluates `T` at its root. -/
@[simp]
theorem tschirnhausPolynomial_X_sub_C (a : R) (T : R[X]) :
    (X - C a).tschirnhausPolynomial T = X - C (T.eval a) := by
  nontriviality R
  rw [tschirnhausPolynomial, Polynomial.map_sub, map_X, map_C, natDegree_X_sub_C,
    resultant_X_sub_C_left _ _ (C a) le_rfl, eval_sub, eval_C, eval_map, eval₂_at_apply]

end Polynomial
