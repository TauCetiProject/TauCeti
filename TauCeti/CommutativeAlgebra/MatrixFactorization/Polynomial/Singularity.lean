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
ideal domain, or a regular local ring). Then `R[X]` is regular
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
`A ⧸ (x ^ i)` placed in degree zero (`singularityCokernelPowerXOfLEIso`), where
`A = AdjoinRoot (X ^ n : R[X]) = R[X] ⧸ (X ^ n)` and `x = AdjoinRoot.root (X ^ n : R[X])`.

## Main definitions and results

In `TauCeti.MatrixFactorization`:

* `powerXOfLEFGModuleCokernelIso`: in `FGModuleCat (AdjoinRoot (X ^ n : R[X]))`, the reduced
  cokernel of `powerXOfLE R hi` (`i ≤ n`) is isomorphic to the cyclic quotient `A ⧸ (x ^ i)`.

In `TauCeti.MatrixFactorization.HomotopyCategory`:

* `polynomialSingularityCokernel_isEquivalence`: for `[IsRegularRing R]` with `ringKrullDim R < ⊤`
  and any `n : ℕ`, `quotientSingularityCokernel` on `HMF(R[X], X ^ n)` is an equivalence (deduced
  for `0 < n` from Orlov's affine theorem via `TauCeti.Polynomial.flat_expand`).
* `polynomialSingularityCokernelEquivalence` and
  `polynomialSingularityCokernelEquivalence_isTriangulated`: the triangle equivalence
  `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))` (with `[FiniteRingKrullDim R]` specializations
  covering all fields and regular local rings without extra hypotheses).
* `singularityCokernelPowerXOfLEIso`: in `D_sg(mod-AdjoinRoot (X ^ n : R[X]))`, the image of
  `powerXOfLE R hi` is isomorphic to the cyclic module `A ⧸ (x ^ i)` placed in degree zero.

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

namespace TauCeti.MatrixFactorization

section CyclicCokernel

variable (R : Type u) [CommRing R] {i n : ℕ}

/-- In `FGModuleCat (AdjoinRoot (X ^ n : R[X]))`, the reduced cokernel of `powerXOfLE R hi`
(`i ≤ n`) is isomorphic to the cyclic quotient `A ⧸ (x ^ i)`. -/
def powerXOfLEFGModuleCokernelIso (hi : i ≤ n) :
    cokernelFunctor.obj
      ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj (powerXOfLE R hi)) ≅
    FGModuleCat.of (AdjoinRoot (X ^ n : R[X]))
      (AdjoinRoot (X ^ n : R[X]) ⧸ Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) where
  hom := ObjectProperty.homMk (powerXOfLECokernelQuotientIso R hi).hom
  inv := ObjectProperty.homMk (powerXOfLECokernelQuotientIso R hi).inv
  hom_inv_id := ObjectProperty.hom_ext _ (powerXOfLECokernelQuotientIso R hi).hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ (powerXOfLECokernelQuotientIso R hi).inv_hom_id

/-- Forgetting finite generation on `powerXOfLEFGModuleCokernelIso` recovers
`powerXOfLECokernelQuotientIso`. -/
@[simp]
theorem forget₂_mapIso_powerXOfLEFGModuleCokernelIso (hi : i ≤ n) :
    (forget₂ (FGModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))
          (ModuleCat.{u} (AdjoinRoot (X ^ n : R[X])))).mapIso
        (powerXOfLEFGModuleCokernelIso R hi) =
      powerXOfLECokernelQuotientIso R hi :=
  (rfl)

end CyclicCokernel

namespace HomotopyCategory

section Equivalence

variable (R : Type u) [CommRing R] [IsRegularRing R]

/-- **Singularity equivalence for `X ^ n` over `R[X]`.** Over any regular commutative ring `R` of
finite Krull dimension and for every `n : ℕ` (including `n = 0`, where both categories vanish),
`quotientSingularityCokernel : HMF(R[X], X ^ n) ⥤ D_sg(mod-(R[X] ⧸ (X ^ n)))` is an equivalence of
categories. For `0 < n`, this applies Orlov's affine theorem along the flat endomorphism
`Polynomial.expand R n : R[X] →ₐ[R] R[X]`. -/
theorem polynomialSingularityCokernel_isEquivalence (n : ℕ)
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
  · exact quotientSingularityCokernel_isEquivalence_of_isRegularRing.{v, u} hdimX
      (pow_mem Polynomial.X_mem_nonZeroDivisors 0)
  · exact quotientSingularityCokernel_isEquivalence_of_flat_polynomial.{v, u, u} hdimX
      (TauCeti.Polynomial.flat_expand R hn) (Polynomial.expand_X n)

/-- The equivalence `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))` for a regular ring `R` of
finite Krull dimension. -/
def polynomialSingularityCokernelEquivalence (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    HomotopyCategory (S := R[X]) (w := (X ^ n : R[X])) ≌
      SingularityCategory (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) :=
  haveI := polynomialSingularityCokernel_isEquivalence.{v, u} R n hdim
  (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).asEquivalence

/-- The forward functor of `polynomialSingularityCokernelEquivalence` is
`quotientSingularityCokernel`. -/
@[simp]
theorem polynomialSingularityCokernelEquivalence_functor (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).functor =
      quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X])) :=
  (rfl)

/-- **The `X ^ n` polynomial singularity equivalence is triangulated.** -/
theorem polynomialSingularityCokernelEquivalence_isTriangulated (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]
    (hdim : ringKrullDim R < ⊤) :
    letI := quotientSingularityCokernelCommShift.{v, u}
      (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n)
    letI : (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (polynomialSingularityCokernelEquivalence_functor.{v, u} R n hdim).symm) ℤ
    letI := (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).commShiftInverse ℤ
    letI := (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).commShift_of_functor ℤ
    (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).IsTriangulated := by
  let := quotientSingularityCokernelCommShift.{v, u}
    (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n)
  let e := eqToIso (polynomialSingularityCokernelEquivalence_functor.{v, u} R n hdim).symm
  let : (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).commShiftInverse ℤ
  let := (polynomialSingularityCokernelEquivalence.{v, u} R n hdim).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientSingularityCokernel_isTriangulated.{v, u}
    (pow_mem (Polynomial.X_mem_nonZeroDivisors (R := R)) n)
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

/-- Specialization of `polynomialSingularityCokernelEquivalence` when `[FiniteRingKrullDim R]` is
available by typeclass synthesis (covering all fields, principal ideal domains, and regular local
rings). -/
def polynomialSingularityCokernelEquivalenceOfFiniteRingKrullDim [FiniteRingKrullDim R] (n : ℕ)
    [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    HomotopyCategory (S := R[X]) (w := (X ^ n : R[X])) ≌
      SingularityCategory (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) :=
  polynomialSingularityCokernelEquivalence.{v, u} R n ringKrullDim_lt_top

end Equivalence

section PowerXObject

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {i n : ℕ}

/-- In `D_sg(mod-AdjoinRoot (X ^ n : R[X]))`, the singularity-category cokernel functor sends the
rank-one factorization `powerXOfLE R hi` (`i ≤ n`, with maps `X ^ i` and `X ^ (n - i)`) to the
cyclic module `A ⧸ (x ^ i)` placed in degree zero. Because `AdjoinRoot (X ^ n : R[X])` is
definitionally `R[X] ⧸ Ideal.span {X ^ n}`,
`singularityCokernel (AdjoinRoot.mk _) AdjoinRoot.mk_self` agrees definitionally with
`quotientSingularityCokernel`. -/
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

end PowerXObject

end HomotopyCategory

end TauCeti.MatrixFactorization
