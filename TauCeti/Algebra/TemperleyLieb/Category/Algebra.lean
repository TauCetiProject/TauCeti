/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category
public import TauCeti.Algebra.TemperleyLieb.Dimension
public import TauCeti.Combinatorics.PlanarMatching.Generator
import Mathlib.RingTheory.FiniteType

/-!
# The diagram algebras of the linear Temperley–Lieb category

For a commutative ring `R` and a loop value `δ : R`, the **diagram algebra** `TauCeti.TLAlg R δ n`
is the endomorphism `R`-algebra `End (TLCat.of n)` of the linear Temperley–Lieb category
`TauCeti.TLCat R δ`: it is free on the planar matchings of `n + n` points, and two diagrams multiply
by stacking and evaluating each closed circle at `δ`. Its ring and algebra structures are those of
Mathlib's `CategoryTheory.End`, whose product reverses composition: `x * y` stacks `x` on top of
`y`.

Its generators `TauCeti.TLAlg.e R δ i`, for `i < n - 1`, are the images of the diagrams
`TauCeti.TLDiagCat.e n i`, which join the points `i` and `i + 1` by a cap below and a cup above.
They satisfy the defining relations of the presented Temperley–Lieb algebra
`TauCeti.TemperleyLieb R δ n`, so its universal property gives the algebra map
`TauCeti.TemperleyLieb.toTLAlg : TemperleyLieb R δ n →ₐ[R] TLAlg R δ n` sending each generator to
the corresponding diagram. Since the presented algebra is spanned by `catalan n` reduced words and
the diagram algebra is free of rank `catalan n`, this map is injective as soon as it is surjective
(`TauCeti.TemperleyLieb.injective_toTLAlg_of_surjective`).

## Main definitions

* `TauCeti.TLAlg R δ n`: the endomorphism algebra of `TLCat.of n`.
* `TauCeti.TLAlg.e R δ i`: the Temperley–Lieb generator joining the points `i` and `i + 1`.
* `TauCeti.TemperleyLieb.toTLAlg`: the algebra map from the presented Temperley–Lieb algebra to the
  diagram algebra.

## Main results

* `TauCeti.TLAlg.e_mul_self`, `TauCeti.TLAlg.e_mul_e_mul_e`, `TauCeti.TLAlg.commute_e`: the
  Temperley–Lieb relations among the diagram generators.
* `TauCeti.TemperleyLieb.toTLAlg_e`: the algebra map sends the generator `e δ i` to `TLAlg.e R δ i`.
* `TauCeti.TemperleyLieb.injective_toTLAlg_of_surjective`: a surjective `toTLAlg` is injective.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The **diagram algebra** on `n` strands: the endomorphism `R`-algebra of the object `of n` of
the linear Temperley–Lieb category at loop value `δ`. The product `x * y` stacks `x` on top of
`y`. -/
abbrev TLAlg (R : Type u) [CommRing R] (δ : R) (n : ℕ) : Type u :=
  End (TLCat.of n : TLCat R δ)

namespace TLAlg

variable (R : Type u) [CommRing R] (δ : R) {n : ℕ}

/-- The **Temperley–Lieb generator** of the diagram algebra on `n` strands joining the points `i`
and `i + 1`: a cap on the bottom points `i` and `i + 1`, a cup on the top points `i` and `i + 1`,
and straight strands elsewhere. -/
noncomputable def e (i : Fin (n - 1)) : TLAlg R δ n :=
  End.of ((TLCat.linearize R δ).map (TLDiagCat.e n i))

@[simp]
theorem asHom_e (i : Fin (n - 1)) :
    (e R δ i).asHom = (TLCat.linearize R δ).map (TLDiagCat.e n i) := (rfl)

/-- The generator `e R δ i` is the basis diagram of the matching of `TLDiagCat.e n i`. -/
theorem asHom_e_eq_diagBasis (i : Fin (n - 1)) :
    (e R δ i).asHom = TLCat.diagBasis (TLCat.of n) (TLCat.of n) (TLDiagCat.e n i).diagram.matching
    := by
  simp [TLCat.linearize_map]

/-- On two strands the generator is `cap ≫ cup`. -/
theorem asHom_e_two (i : Fin (2 - 1)) : (e R δ i).asHom = TLCat.cap ≫ TLCat.cup := by
  simp [TLDiagCat.e_two]

variable {R δ}

/-- Over a nontrivial ring the generators are nonzero. -/
theorem e_ne_zero [Nontrivial R] (i : Fin (n - 1)) : e R δ i ≠ 0 := fun h =>
  TLCat.diagBasis_ne_zero (R := R) (δ := δ) (X := TLCat.of n) (Y := TLCat.of n)
    (TLDiagCat.e n i).diagram.matching (by rw [← asHom_e_eq_diagBasis, h, End.zero_asHom])

/-- **The quadratic relation** `e i * e i = δ • e i`: stacking a generator on itself closes a
circle, which evaluates to `δ`. -/
theorem e_mul_self (i : Fin (n - 1)) : e R δ i * e R δ i = δ • e R δ i := by
  rw [e, ← End.of_comp, ← Functor.map_comp, TLDiagCat.e_comp_e_self, ← End.of_smul]
  simp [TLCat.linearize_map]

/-- **The adjacent relation** `e i * e j * e i = e i` for adjacent `i` and `j`: two generators
sharing a strand straighten a zigzag. -/
theorem e_mul_e_mul_e {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    e R δ i * e R δ j * e R δ i = e R δ i := by
  rw [e, e, ← End.of_comp, ← End.of_comp, ← Functor.map_comp, ← Functor.map_comp,
    TLDiagCat.e_comp_e_comp_e n h]

/-- **The distant relation**: generators at distance at least two commute. -/
theorem commute_e {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (e R δ i) (e R δ j) := by
  rw [commute_iff_eq, e, e, ← End.of_comp, ← End.of_comp, ← Functor.map_comp,
    ← Functor.map_comp, TLDiagCat.e_comp_e_comm n h]

end TLAlg

namespace TemperleyLieb

variable {R : Type u} [CommRing R] {δ : R} {n : ℕ}

variable (R δ n) in
/-- The algebra map from the **presented Temperley–Lieb algebra** to the **diagram algebra**,
sending each generator `e δ i` to the diagram `TLAlg.e R δ i`. It exists because the diagram
generators satisfy the Temperley–Lieb relations. -/
noncomputable def toTLAlg : TemperleyLieb R δ n →ₐ[R] TLAlg R δ n :=
  lift (TLAlg.e R δ) TLAlg.e_mul_self TLAlg.e_mul_e_mul_e fun h => (TLAlg.commute_e h).eq

@[simp]
theorem toTLAlg_e (i : Fin (n - 1)) : toTLAlg R δ n (e δ i) = TLAlg.e R δ i :=
  lift_e _ _ _ _ i

/-- **Surjectivity suffices.** The presented algebra is spanned by `catalan n` reduced words and
the diagram algebra is free of rank `catalan n`, so if `toTLAlg` is surjective then it is also
injective. -/
theorem injective_toTLAlg_of_surjective (h : Function.Surjective (toTLAlg R δ n)) :
    Function.Injective (toTLAlg R δ n) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact fun x y _ => (Module.subsingleton R _).elim x y
  refine injective_of_catalan_le_finrank_range (toTLAlg R δ n).toLinearMap ?_
  rw [LinearMap.range_eq_top.mpr h, finrank_top, TLCat.finrank_end_of]

end TemperleyLieb

end TauCeti
