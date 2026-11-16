/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.GroupTheory.FiniteAbelian.Duality
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.RingTheory.Polynomial.Cyclotomic.Reflect

/-!
# Primitive Dirichlet characters: local Euler polynomials and quadratic products

For a prime `p` and a nonzero level `N`, a character `χ` mod `N` has `p ∤ χ.conductor` if and only
if `χ` factors through the prime-to-`p` part `ordCompl[p] N` of `N`
(`DirichletCharacter.not_dvd_conductor_iff_factorsThrough_ordCompl`). Characters whose conductor is
divisible by `p` satisfy `χ.primitiveCharacter p = 0`, while the remaining characters biject with
all characters modulo `ordCompl[p] N` and evaluate at `p` as characters of
`(ZMod (ordCompl[p] N))ˣ`. When the coefficient domain has enough roots of unity, taking the
product of `1 - C (χ.primitiveCharacter p) * X` over all characters modulo `N` therefore yields
`(1 - X ^ f) ^ (φ(ordCompl[p] N) / f)`, where `f = orderOf (p : ZMod (ordCompl[p] N))`.

For primitive quadratic characters, their product at the least common multiple level is principal
exactly when the original characters coincide, including their levels. This separates the
exceptional equal-character case in two-character arguments for real Dirichlet L-functions.
Only one of the two characters needs to be quadratic.

## Main results

* `DirichletCharacter.prod_one_sub_C_mul_X_primitiveCharacter`:
  `∏ χ : DirichletCharacter R N, (1 - C (χ.primitiveCharacter p) * X) = (1 - X ^ f) ^ (φ(m) / f)`
  for `m = ordCompl[p] N` and `f = orderOf (p : ZMod m)`.
* `DirichletCharacter.IsPrimitive.mul_eq_one_iff`: the common-level product of two primitive
  characters, one of them quadratic, is principal iff they coincide.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
-/

public section

namespace DirichletCharacter

variable {R : Type*} {N M : ℕ}

/-- **Local Euler polynomial across all primitive characters of level dividing `N`.** For a prime
`p` and a nonzero level `N`, let `m = ordCompl[p] N` and `f = orderOf (p : ZMod m)`. Over any
integral domain `R` with enough roots of unity for `(ZMod m)ˣ`,
`∏ χ : DirichletCharacter R N, (1 - C (χ.primitiveCharacter p) * X) = (1 - X ^ f) ^ (φ(m) / f)`. -/
theorem prod_one_sub_C_mul_X_primitiveCharacter [CommRing R] [IsDomain R] {N p : ℕ} [NeZero N]
    (hp : p.Prime) [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod (ordCompl[p] N))ˣ)] :
    ∏ χ : DirichletCharacter R N,
      (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X) =
        (1 - Polynomial.X ^ orderOf (p : ZMod (ordCompl[p] N))) ^
          ((ordCompl[p] N).totient / orderOf (p : ZMod (ordCompl[p] N))) := by
  classical
  set m := ordCompl[p] N
  have hm : m ∣ N := Nat.ordCompl_dvd N p
  have : NeZero m := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (NeZero.ne N)
  set u : (ZMod m)ˣ := ZMod.unitOfCoprime p hcop
  have hord : orderOf u = orderOf (p : ZMod m) := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime]
  -- Split off characters whose conductor is divisible by `p`; they contribute `1`.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun χ : DirichletCharacter R N ↦
    χ.FactorsThrough m)]
  have hnot : ∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter R N ↦ ¬ χ.FactorsThrough m),
      (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X) = 1 := by
    refine Finset.prod_eq_one fun χ hχ ↦ ?_
    have hnotfac : ¬ χ.FactorsThrough m := (Finset.mem_filter.mp hχ).2
    have hd : p ∣ χ.conductor :=
      not_not.mp ((not_dvd_conductor_iff_factorsThrough_ordCompl χ hp).not.mpr hnotfac)
    have hzero : χ.primitiveCharacter (p : ZMod χ.conductor) = 0 :=
      MulChar.map_nonunit _ fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hd
    simp [hzero]
  rw [hnot, mul_one]
  -- Biject the remaining characters with `(ZMod m)ˣ →* Rˣ`.
  let e : {χ : DirichletCharacter R N // χ.FactorsThrough m} ≃ ((ZMod m)ˣ →* Rˣ) :=
    (factorsThroughEquiv hm).trans MulChar.equivToUnitHom
  have : Fintype ((ZMod m)ˣ →* Rˣ) := Fintype.ofEquiv _ e
  have hstep : ∏ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter R N ↦ χ.FactorsThrough m),
      (1 - Polynomial.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * Polynomial.X) =
      ∏ᶠ φ : (ZMod m)ˣ →* Rˣ, (1 - Polynomial.C ((φ u : Rˣ) : R) * Polynomial.X) := by
    rw [Finset.prod_subtype _ (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))),
      finprod_eq_prod_of_fintype]
    refine Fintype.prod_equiv e _ _ fun ⟨χ, hχ⟩ ↦ ?_
    have hval : χ.primitiveCharacter (p : ZMod χ.conductor) =
        ((e ⟨χ, hχ⟩ u : Rˣ) : R) := by
      have h1 := primitiveCharacter_changeLevel_apply_of_isCoprime hm
        (factorsThroughEquiv hm ⟨χ, hχ⟩) (a := (p : ℤ)) (Nat.isCoprime_iff_coprime.mpr hcop)
      have h2 : changeLevel hm (factorsThroughEquiv hm ⟨χ, hχ⟩) = χ := by
        rw [factorsThroughEquiv_apply]
        exact hχ.eq_changeLevel.symm
      rw [h2, Int.cast_natCast, Int.cast_natCast] at h1
      rw [h1, ← ZMod.coe_unitOfCoprime p hcop]
      exact (MulChar.coe_toUnitHom _ u).symm
    rw [hval]
  rw [hstep, CommGroup.finprod_monoidHom_apply R u
    (fun ζ : Rˣ ↦ 1 - Polynomial.C (ζ : R) * Polynomial.X)]
  -- Evaluate the root-of-unity product and compute the quotient cardinality.
  have hpos : 0 < orderOf u := orderOf_pos u
  have : NeZero (orderOf u) := ⟨hpos.ne'⟩
  have : HasEnoughRootsOfUnity R (orderOf u) :=
    HasEnoughRootsOfUnity.of_dvd R (Monoid.order_dvd_exponent u)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot R (orderOf u)
  rw [Polynomial.finprod_one_sub_C_mul_X_rootsOfUnity hpos hζ, hord]
  congr 1
  have hlag : Nat.card ((ZMod m)ˣ ⧸ Subgroup.zpowers u) * orderOf u = m.totient := by
    rw [← Subgroup.index_eq_card, ← Nat.card_zpowers, Subgroup.index_mul_card,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact Nat.eq_div_of_mul_eq_left (hord ▸ hpos.ne') (hord ▸ hlag)

section Quadratic

variable [CommRing R]

/-- The common-level product of two primitive characters, one of them quadratic, is principal
exactly when they are the same primitive character. In particular, different primitive levels
cannot give a principal product. -/
theorem IsPrimitive.mul_eq_one_iff {χ : DirichletCharacter R N}
    {ψ : DirichletCharacter R M} [NeZero N] [NeZero M]
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψq : ψ.IsQuadratic) :
    χ.mul ψ = 1 ↔ ∃ h : N = M, h ▸ χ = ψ := by
  have : NeZero (Nat.lcm N M) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
  have hq := hψq.changeLevel (Nat.dvd_lcm_right N M)
  rw [DirichletCharacter.mul, mul_eq_one_iff_eq_inv, hq.inv]
  exact hχ.changeLevel_eq_changeLevel_iff hψ _ _

end Quadratic

end DirichletCharacter
