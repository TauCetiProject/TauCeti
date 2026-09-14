/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# Coefficients of the different ideal in a tower

This file reads Mathlib's transitivity theorem for different ideals at a height-one prime.  If
`A ⊆ B ⊆ C` is a tower of Dedekind domains and `Q` is a height-one prime of `C` above `P` in
`B`, then

`mult_Q(𝔇(C/A)) = mult_Q(𝔇(C/B)) + e(Q/P) mult_P(𝔇(B/A))`.

The first term comes from additivity of multiplicities on products.  The second comes from the
factorization law for an extended ideal: extending a prime from `B` to `C` multiplies its
coefficient at `Q` by the ramification index.  This is the ideal-theoretic coefficient formula
used by the tower law for different exponents of function-field places.

## Main results

* `TauCeti.multiplicity_differentIdeal_tower`: the coefficientwise transitivity formula.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.4.12.
-/

public section

open IsDedekindDomain Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [Module.Finite A B] [Module.Finite B C]
variable [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing C)]

variable (A) in
/-- **The coefficientwise tower law for different ideals**: at a height-one prime `Q` of `C`
above `P` in `B`, the coefficient of the different of `C / A` is the coefficient of the
different of `C / B` plus the ramification index times the coefficient of the different of
`B / A`.

This is the ideal-theoretic form of Stichtenoth, Corollary 3.4.12. -/
theorem multiplicity_differentIdeal_tower (P : HeightOneSpectrum B)
    (Q : HeightOneSpectrum C) [Q.asIdeal.LiesOver P.asIdeal] :
    multiplicity Q.asIdeal (differentIdeal A C) =
      multiplicity Q.asIdeal (differentIdeal B C) +
        Q.asIdeal.ramificationIdx B * multiplicity P.asIdeal (differentIdeal A B) := by
  -- Combine Mathlib's `differentIdeal_eq_differentIdeal_mul_differentIdeal` and
  -- `emultiplicity_map_eq_ramificationIdx'_mul`; no factorization of the different is rebuilt.
  let _ : Module.Finite A C := .trans B C
  let _ : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (FractionRing A) (FractionRing B)
      (FractionRing C)
  let _ : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) (FractionRing B)
      (FractionRing C)
  have hAB : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hBC : differentIdeal B C ≠ ⊥ := differentIdeal_ne_bot
  have hmap : (differentIdeal A B).map (algebraMap B C) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hAB
  have hprod : differentIdeal B C * (differentIdeal A B).map (algebraMap B C) ≠ ⊥ :=
    mul_ne_zero hBC hmap
  have hfiniteProd : FiniteMultiplicity Q.asIdeal
      (differentIdeal B C * (differentIdeal A B).map (algebraMap B C)) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime) hprod
  have hfiniteMap : FiniteMultiplicity Q.asIdeal
      ((differentIdeal A B).map (algebraMap B C)) := hfiniteProd.mul_right
  have hfiniteAB : FiniteMultiplicity P.asIdeal (differentIdeal A B) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime P.ne_bot P.isPrime) hAB
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hAB
    P.irreducible Q.irreducible Q.ne_bot
  rw [hfiniteMap.emultiplicity_eq_multiplicity, hfiniteAB.emultiplicity_eq_multiplicity,
    P.asIdeal.ramificationIdx'_eq_ramificationIdx Q.asIdeal P.ne_bot] at he
  have hcoeff : multiplicity Q.asIdeal ((differentIdeal A B).map (algebraMap B C)) =
      Q.asIdeal.ramificationIdx B * multiplicity P.asIdeal (differentIdeal A B) := by
    exact_mod_cast he
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal A B C,
    multiplicity_mul (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime) hfiniteProd, hcoeff]

end TauCeti

end
