/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacePermutation.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Archimedean factors in place permutation lattices

For a finite Galois extension of number fields `L/K`, the Herbrand quotient of the permutation
lattice on the infinite places of `L` is `2^r`, where `r` is the number of infinite places of
`K` ramified in `L`. Such a place is real and becomes complex; its decomposition group has
order two. Every other infinite place contributes one.

Combining this with the finite-place calculation gives the quotient of the permutation lattice
on all infinite places and the primes above a finite set `S`. This is the place lattice used in
the logarithmic comparison for the Herbrand quotient of the `S`-units.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3.
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII.
-/

public noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- The infinite-place permutation lattice has one factor of two for each ramified infinite
place of the base field, and a factor of one for each unramified place. -/
theorem herbrandQuotient_ofMulAction_infinitePlace_eq_prod :
    TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by
  classical
  let e := orbitRelEquiv (k := K) (K := L)
  let := Fintype.ofEquiv (InfinitePlace K) e.symm
  rw [TateCohomology.herbrandQuotient_ofMulAction]
  refine Fintype.prod_equiv e _ _ fun q ↦ ?_
  have hq : e q = q.out.comap (algebraMap K L) :=
    (congrArg e (Quotient.out_eq q).symm).trans
      (orbitRelEquiv_apply_mk'' (k := K) (K := L) q.out)
  rw [card_stabilizer, hq, isUnramifiedIn_comap]
  split <;> simp

open scoped Classical in
/-- The Herbrand quotient of the infinite-place permutation lattice is `2^r`, where `r` is
exactly the number of infinite places of `K` ramified in `L`. -/
theorem herbrandQuotient_ofMulAction_infinitePlace :
    TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) =
      (2 : ℚ) ^ (Finset.univ.filter fun v : InfinitePlace K ↦ ¬ v.IsUnramifiedIn L).card := by
  classical
  rw [herbrandQuotient_ofMulAction_infinitePlace_eq_prod]
  simpa only [ite_not, Finset.prod_const] using
    (Finset.prod_filter (s := Finset.univ)
      (p := fun v : InfinitePlace K ↦ ¬ v.IsUnramifiedIn L) (f := fun _ ↦ (2 : ℚ))).symm

open scoped Classical in
/-- The place permutation lattice for a finite set of finite places, together with every
infinite place, has quotient `2^r` times the product of the finite local degrees. The primes
above the finite places may be chosen arbitrarily. -/
theorem herbrandQuotient_ofMulAction_places
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient
      (Rep.ofMulAction ℤ (L ≃ₐ[K] L)
        (InfinitePlace L ⊕ ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) ↑S))) =
      (2 : ℚ) ^ (Finset.univ.filter fun v : InfinitePlace K ↦ ¬ v.IsUnramifiedIn L).card *
        ∏ v : S, (Module.finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  classical
  let := (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 L) S.finite_toSet).to_subtype
  rw [TateCohomology.herbrandQuotient_ofMulAction_sum,
    herbrandQuotient_ofMulAction_infinitePlace, herbrandQuotient_ofMulAction_primesAbove S w]

end TauCeti.ClassFieldTheory
