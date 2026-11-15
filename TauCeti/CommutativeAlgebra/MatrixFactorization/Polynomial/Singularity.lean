/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Orlov
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Polynomial.Cokernel
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.KrullDimension.Polynomial
import TauCeti.RingTheory.Polynomial.ExpandBasis

/-!
# Singularity equivalence for the polynomial potential `X ^ n`

Let `R` be a regular commutative ring of finite Krull dimension (for instance a field, a principal
ideal domain, a Dedekind domain, or a regular local ring). Then `R[X]` is regular
(`Polynomial.isRegularRing_of_isRegularRing`) of finite Krull dimension `dim R + 1`
(`Polynomial.ringKrullDim_of_isNoetherianRing`).

For every natural number `n`, `(X ^ n : R[X])` is a nonzerodivisor in `R[X]`; when `0 < n`, the
power-substitution endomorphism `Polynomial.expand R n : R[X] →ₐ[R] R[X]` sending `X` to `X ^ n` is
even finite free, hence flat (`TauCeti.Polynomial.flat_expand`), in every characteristic. Orlov's
affine theorem therefore applies directly to the polynomial potential `X ^ n` over `R[X]`, giving a
triangle equivalence

```text
  HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n))).
```

On the elementary rank-one matrix factorizations `powerXOfLE R hi` (`i ≤ n`, with maps `X ^ i` and
`X ^ (n - i)`), the singularity-category cokernel functor evaluates to the cyclic `A`-module
`A ⧸ (x ^ i)` placed in degree zero (`quotientSingularityCokernelPowerXOfLEIso` and
`singularityCokernelPowerXOfLEIso`), where `A = AdjoinRoot (X ^ n : R[X])` and
`x = AdjoinRoot.root (X ^ n : R[X])`.

## Main definitions and results

In `TauCeti.MatrixFactorization.HomotopyCategory`:

* `quotientSingularityCokernel_isEquivalence_X_pow` and
  `quotientSingularityCokernel_isEquivalence_X_pow_of_krullDimLE`: for `[IsRegularRing R]` with
  `ringKrullDim R < ⊤` (or `[Ring.KrullDimLE d R]`) and any `n : ℕ`, `quotientSingularityCokernel`
  on `HMF(R[X], X ^ n)` is an equivalence (deduced for `0 < n` from Orlov's affine theorem via
  `TauCeti.Polynomial.flat_expand`).
* `powerXSingularityCokernelEquivalence` and `powerXSingularityCokernelEquivalence_isTriangulated`:
  the triangle equivalence `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))`.
* `powerXSingularityCokernelEquivalenceOfKrullDimLE` and
  `powerXSingularityCokernelEquivalenceOfKrullDimLE_isTriangulated`: specializations under
  `[Ring.KrullDimLE d R]` (synthesized automatically for fields, principal ideal domains, Dedekind
  domains, and subsingleton rings).
* `quotientSingularityCokernelPowerXOfLEIso` and `singularityCokernelPowerXOfLEIso`: the image of
  `powerXOfLE R hi` in the singularity category is isomorphic to the cyclic module `A ⧸ (x ^ i)`
  placed in degree zero.

## References

* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

universe v u

open CategoryTheory Polynomial

namespace TauCeti.MatrixFactorization.HomotopyCategory

section Equivalence

variable (R : Type u) [CommRing R] [IsRegularRing R]

/-- **Singularity equivalence for `X ^ n` over `R[X]`.** Over any regular commutative ring `R` of
finite Krull dimension and for every `n : ℕ` (including `n = 0`, where both categories vanish),
`quotientSingularityCokernel : HMF(R[X], X ^ n) ⥤ D_sg(mod-(R[X] ⧸ (X ^ n)))` is an equivalence of
categories. For `0 < n`, this applies Orlov's affine theorem along the flat endomorphism
`Polynomial.expand R n : R[X] →ₐ[R] R[X]`. -/
theorem quotientSingularityCokernel_isEquivalence_X_pow (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).IsEquivalence := by
  have hdimX : ringKrullDim R[X] < ⊤ := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    induction hd : ringKrullDim R using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe e =>
      induction e with
      | top => exact absurd hd hdim.ne
      | coe d => exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (d + 1))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact quotientSingularityCokernel_isEquivalence_of_isRegularRing_of_ringKrullDim_lt_top.{v, u}
      hdimX (pow_mem Polynomial.X_mem_nonZeroDivisors 0)
  · exact quotientSingularityCokernel_isEquivalence_of_flat_polynomial.{v, u, u} hdimX
      (TauCeti.Polynomial.flat_expand R hn) (Polynomial.expand_X n)

/-- The equivalence `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))` for a regular ring `R` of
finite Krull dimension. -/
def powerXSingularityCokernelEquivalence (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    HomotopyCategory (S := R[X]) (w := (X ^ n : R[X])) ≌
      SingularityCategory (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) :=
  haveI := quotientSingularityCokernel_isEquivalence_X_pow.{v, u} R n hdim
  (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).asEquivalence

/-- The forward functor of `powerXSingularityCokernelEquivalence` is
`quotientSingularityCokernel`. -/
@[simp]
theorem powerXSingularityCokernelEquivalence_functor (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    (powerXSingularityCokernelEquivalence.{v, u} R n hdim).functor =
      quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X])) :=
  (rfl)

/-- **The `X ^ n` polynomial singularity equivalence is triangulated.** -/
theorem powerXSingularityCokernelEquivalence_isTriangulated (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    letI := quotientSingularityCokernelCommShift.{v, u}
      (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n)
    letI : (powerXSingularityCokernelEquivalence.{v, u} R n hdim).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (powerXSingularityCokernelEquivalence_functor.{v, u} R n hdim).symm) ℤ
    letI := (powerXSingularityCokernelEquivalence.{v, u} R n hdim).commShiftInverse ℤ
    letI := (powerXSingularityCokernelEquivalence.{v, u} R n hdim).commShift_of_functor ℤ
    (powerXSingularityCokernelEquivalence.{v, u} R n hdim).IsTriangulated :=
  isTriangulated_of_functor_eq_quotientSingularityCokernel.{v, u}
    (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n) _
    (powerXSingularityCokernelEquivalence_functor.{v, u} R n hdim)

/-- Specialization of `quotientSingularityCokernel_isEquivalence_X_pow` under a typeclass Krull
dimension bound `[Ring.KrullDimLE d R]` (synthesized automatically for fields, principal ideal
domains, Dedekind domains, and subsingleton rings). -/
theorem quotientSingularityCokernel_isEquivalence_X_pow_of_krullDimLE (d : ℕ)
    [Ring.KrullDimLE d R] (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_X_pow.{v, u} R n <|
    (Order.KrullDimLE.krullDim_le (n := d) (α := PrimeSpectrum R)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

/-- Specialization of `powerXSingularityCokernelEquivalence` when `[Ring.KrullDimLE d R]` is
available by typeclass synthesis (covering fields, principal ideal domains, Dedekind domains, and
subsingleton rings). -/
def powerXSingularityCokernelEquivalenceOfKrullDimLE (d : ℕ) [Ring.KrullDimLE d R] (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    HomotopyCategory (S := R[X]) (w := (X ^ n : R[X])) ≌
      SingularityCategory (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) :=
  powerXSingularityCokernelEquivalence.{v, u} R n <|
    (Order.KrullDimLE.krullDim_le (n := d) (α := PrimeSpectrum R)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

/-- Unfolds `powerXSingularityCokernelEquivalenceOfKrullDimLE`. -/
theorem powerXSingularityCokernelEquivalenceOfKrullDimLE_def (d : ℕ) [Ring.KrullDimLE d R] (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n =
      powerXSingularityCokernelEquivalence.{v, u} R n
        ((Order.KrullDimLE.krullDim_le (n := d) (α := PrimeSpectrum R)).trans_lt
          (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))) :=
  (rfl)

/-- The forward functor of `powerXSingularityCokernelEquivalenceOfKrullDimLE` is
`quotientSingularityCokernel`. -/
@[simp]
theorem powerXSingularityCokernelEquivalenceOfKrullDimLE_functor (d : ℕ) [Ring.KrullDimLE d R]
    (n : ℕ) [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n).functor =
      quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X])) :=
  (rfl)

/-- **The bounded-dimension `X ^ n` polynomial singularity equivalence is triangulated.** -/
theorem powerXSingularityCokernelEquivalenceOfKrullDimLE_isTriangulated (d : ℕ)
    [Ring.KrullDimLE d R] (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    letI := quotientSingularityCokernelCommShift.{v, u}
      (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n)
    letI : (powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (powerXSingularityCokernelEquivalenceOfKrullDimLE_functor.{v, u} R d n).symm) ℤ
    letI := (powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n).commShiftInverse ℤ
    letI := (powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n).commShift_of_functor ℤ
    (powerXSingularityCokernelEquivalenceOfKrullDimLE.{v, u} R d n).IsTriangulated :=
  isTriangulated_of_functor_eq_quotientSingularityCokernel.{v, u}
    (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n) _
    (powerXSingularityCokernelEquivalenceOfKrullDimLE_functor.{v, u} R d n)

end Equivalence

section PowerXObject

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {i n : ℕ}

/-- In `D_sg(mod-AdjoinRoot (X ^ n : R[X]))`, `singularityCokernel` along `AdjoinRoot.mk (X ^ n)`
sends the rank-one factorization `powerXOfLE R hi` (`i ≤ n`, with maps `X ^ i` and `X ^ (n - i)`)
to the cyclic module `A ⧸ (x ^ i)` placed in degree zero. -/
def singularityCokernelPowerXOfLEIso (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))] :
    (singularityCokernel.{v, u} (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self).obj
        ((nullHomotopic (S := R[X]) (w := (X ^ n : R[X]))).quotientFunctor.obj
          (powerXOfLE R hi)) ≅
      (SingularityCategory.Q (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))).obj
        ((DerivedCategory.Bounded.singleFunctor
            (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X]))) 0).obj
          (FGModuleCat.of (AdjoinRoot (X ^ n : R[X]))
            (AdjoinRoot (X ^ n : R[X]) ⧸
              Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}))) :=
  eqToIso (singularityCokernel_obj_quotientFunctor_obj
      (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi)) ≪≫
    (SingularityCategory.Q _).mapIso
      ((DerivedCategory.Bounded.singleFunctor _ 0).mapIso
        (powerXOfLEFGModuleCokernelIso R hi))

@[simp]
theorem singularityCokernelPowerXOfLEIso_hom (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))] :
    (singularityCokernelPowerXOfLEIso.{v, u} R hi).hom =
      eqToHom (singularityCokernel_obj_quotientFunctor_obj
          (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi)) ≫
        (SingularityCategory.Q _).map
          ((DerivedCategory.Bounded.singleFunctor _ 0).map
            (powerXOfLEFGModuleCokernelIso R hi).hom) :=
  (rfl)

@[simp]
theorem singularityCokernelPowerXOfLEIso_inv (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))] :
    (singularityCokernelPowerXOfLEIso.{v, u} R hi).inv =
      (SingularityCategory.Q _).map
          ((DerivedCategory.Bounded.singleFunctor _ 0).map
            (powerXOfLEFGModuleCokernelIso R hi).inv) ≫
        eqToHom (singularityCokernel_obj_quotientFunctor_obj
          (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi)).symm :=
  (rfl)

/-- In `D_sg(mod-(R[X] ⧸ (X ^ n)))`, `quotientSingularityCokernel` sends the rank-one factorization
`powerXOfLE R hi` (`i ≤ n`, with maps `X ^ i` and `X ^ (n - i)`) to the cyclic module `A ⧸ (x ^ i)`
placed in degree zero. -/
def quotientSingularityCokernelPowerXOfLEIso (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).obj
        ((nullHomotopic (S := R[X]) (w := (X ^ n : R[X]))).quotientFunctor.obj
          (powerXOfLE R hi)) ≅
      (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).obj
        ((DerivedCategory.Bounded.singleFunctor
            (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).obj
          (FGModuleCat.of (R[X] ⧸ Ideal.span {(X ^ n : R[X])})
            ((R[X] ⧸ Ideal.span {(X ^ n : R[X])}) ⧸
              Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X ^ n : R[X])}) X) ^ i}))) :=
  -- `Mathlib.RingTheory.AdjoinRoot` exposes `AdjoinRoot`, `AdjoinRoot.mk`, and `AdjoinRoot.root`
  -- as the `Ideal.Quotient` modulo `Ideal.span {X ^ n}`.
  eqToIso (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)) ≪≫
    (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).mapIso
      ((DerivedCategory.Bounded.singleFunctor
          (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).mapIso
        (powerXOfLEFGModuleCokernelIso R hi))

@[simp]
theorem quotientSingularityCokernelPowerXOfLEIso_hom (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (quotientSingularityCokernelPowerXOfLEIso.{v, u} R hi).hom =
      eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)) ≫
        (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).map
          ((DerivedCategory.Bounded.singleFunctor
              (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).map
            (powerXOfLEFGModuleCokernelIso R hi).hom) :=
  (rfl)

@[simp]
theorem quotientSingularityCokernelPowerXOfLEIso_inv (hi : i ≤ n)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (quotientSingularityCokernelPowerXOfLEIso.{v, u} R hi).inv =
      (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).map
          ((DerivedCategory.Bounded.singleFunctor
              (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).map
            (powerXOfLEFGModuleCokernelIso R hi).inv) ≫
        eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)).symm :=
  (rfl)

end PowerXObject

end TauCeti.MatrixFactorization.HomotopyCategory
