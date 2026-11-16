/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.Algebra.MonoidAlgebra.Reduced

/-!
# Frobenius on monoid algebras and reduced group algebras

Let `R` be a commutative semiring of exponential characteristic `p` and `M` a commutative monoid.
The `p`-th power map of the monoid algebra `R[M]` raises both the coefficients and the monomials
to the `p`-th power: `(∑ aₘ m) ^ p = ∑ aₘ ^ p m ^ p`. Hence it is injective as soon as it is
injective on `R` and on `M`, and this decides when `R[M]` is reduced.

For a commutative ring `R` of prime characteristic `p`, the monoid algebra `R[M]` is reduced
exactly when `R` is reduced and the `p`-th power map of `M` is injective. In characteristic zero
there is no condition on the monoid when it is a group: the group algebra of a commutative group
over a reduced `ℚ`-algebra is reduced (`MonoidAlgebra.isReduced_of_algebraRat`). Together these
give the criterion over a domain `R` of exponential characteristic `p`: the group algebra `R[G]`
of a commutative group `G` is reduced exactly when `G` has no `p`-torsion.

For a field `k` this is the algebraic form of the statement that the diagonalizable group with
character group `G` is geometrically reduced, equivalently smooth when `G` is finitely generated,
exactly when `G` has no `p`-torsion.

## Main declarations

* `MonoidAlgebra.expChar`: a monoid algebra has the exponential characteristic of its
  coefficients.
* `MonoidAlgebra.mapRingHom_frobenius_mapDomainRingHom_powMonoidHom`: the `p`-th power map of
  `R[M]` in terms of the Frobenius of `R` and the `p`-th power map of `M`.
* `MonoidAlgebra.pow_expChar_injective`: the `p`-th power map of `R[M]` is injective when `R` is
  reduced and the `p`-th power map of `M` is injective.
* `MonoidAlgebra.isReduced_iff_isReduced_and_pow_injective`: in prime characteristic `p`, the
  monoid algebra `R[M]` is reduced exactly when `R` is reduced and the `p`-th power map of `M`
  is injective.
* `MonoidAlgebra.isReduced_iff_forall_pow_eq_one_imp_eq_one`: over a domain of exponential
  characteristic `p`, the group algebra of a commutative group is reduced exactly when the group
  has no `p`-torsion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.5.

The formula for the `p`-th power map is the monoid-algebra form of Mathlib's
`Polynomial.map_frobenius_expand`.
-/

public section

open scoped MonoidAlgebra

namespace MonoidAlgebra

/-- A monoid algebra has the exponential characteristic of its coefficient semiring. -/
instance expChar {R M : Type*} [Semiring R] [MulOneClass M] (p : ℕ) [ExpChar R p] :
    ExpChar R[M] p :=
  expChar_of_injective_ringHom (f := singleOneRingHom) single_right_injective p

section Semiring

variable {R M : Type*} [CommSemiring R] [CommMonoid M] (p : ℕ) [ExpChar R p]

/-- In exponential characteristic `p`, the `p`-th power of an element of a commutative monoid
algebra is obtained by raising its coefficients and its monomials to the `p`-th power. -/
theorem mapRingHom_frobenius_mapDomainRingHom_powMonoidHom (x : R[M]) :
    mapRingHom M (frobenius R p) (mapDomainRingHom R (powMonoidHom p) x) = x ^ p := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [(expChar_pos R p).ne']
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_pow_expChar]
  | single m a => simp [frobenius_def]

end Semiring

section Ring

variable {R M : Type*} [CommRing R] [CommMonoid M] (p : ℕ)

/-- In exponential characteristic `p`, the `p`-th power map of a commutative monoid algebra over
a reduced ring is injective when the `p`-th power map of the monoid is injective. -/
theorem pow_expChar_injective [IsReduced R] [ExpChar R p]
    (hM : Function.Injective fun m : M ↦ m ^ p) : Function.Injective fun x : R[M] ↦ x ^ p := by
  have hpow : ⇑(powMonoidHom p : M →* M) = fun m ↦ m ^ p := funext (powMonoidHom_apply p)
  intro x y hxy
  beta_reduce at hxy
  rw [← mapRingHom_frobenius_mapDomainRingHom_powMonoidHom p x,
    ← mapRingHom_frobenius_mapDomainRingHom_powMonoidHom p y, coe_mapRingHom,
    mapDomainRingHom_apply, mapDomainRingHom_apply, hpow] at hxy
  exact mapDomain_injective hM (map_injective _ (frobenius_inj R p) hxy)

/-- **A commutative monoid algebra in prime characteristic `p` is reduced exactly when its
coefficient ring is reduced and the `p`-th power map of the monoid is injective.** -/
theorem isReduced_iff_isReduced_and_pow_injective [Fact p.Prime] [CharP R p] :
    IsReduced R[M] ↔ IsReduced R ∧ Function.Injective fun m : M ↦ m ^ p := by
  have hp : p.Prime := Fact.out
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.ne_one
  refine ⟨fun h ↦ ⟨isReduced_of_injective (singleOneRingHom (R := R) (M := M))
      single_right_injective, fun m n hmn ↦ ?_⟩, fun ⟨_, hM⟩ ↦ ?_⟩
  · have hmn : m ^ p = n ^ p := hmn
    refine single_left_injective (one_ne_zero (α := R)) (frobenius_inj R[M] p ?_)
    simp [frobenius_def, hmn]
  · rw [isReduced_iff_pow_one_lt p hp.one_lt]
    intro x hx
    exact pow_expChar_injective p hM (by simpa [zero_pow hp.ne_zero] using hx)

end Ring

section Group

variable (R : Type*) [CommRing R] (G : Type*) [CommGroup G] (p : ℕ)

/-- **The group algebra of a commutative group over a domain of exponential characteristic `p`
is reduced exactly when the group has no `p`-torsion.** In characteristic zero, where `p = 1`,
the condition is empty and every such group algebra is reduced. -/
theorem isReduced_iff_forall_pow_eq_one_imp_eq_one [IsDomain R] [ExpChar R p] :
    IsReduced R[G] ↔ ∀ g : G, g ^ p = 1 → g = 1 := by
  rcases ‹ExpChar R p› with _ | hp
  · have : CharZero (FractionRing R) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
    exact iff_of_true
      (isReduced_of_injective (mapRingHom G (algebraMap R (FractionRing R)))
        (map_injective _ (IsFractionRing.injective R (FractionRing R))))
      fun g hg ↦ (pow_one g).symm.trans hg
  · have : Fact p.Prime := ⟨hp⟩
    rw [isReduced_iff_isReduced_and_pow_injective p, and_iff_right (inferInstance : IsReduced R)]
    have hpow : ⇑(powMonoidHom p : G →* G) = fun g ↦ g ^ p := funext (powMonoidHom_apply p)
    simpa only [hpow] using injective_iff_map_eq_one (powMonoidHom p : G →* G)

end Group

end MonoidAlgebra
