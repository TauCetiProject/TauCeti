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

Over a regular commutative ring `R` of finite Krull dimension, `R[X]` is regular of Krull dimension
`dim R + 1` and `Polynomial.expand R n` (`0 < n`) is flat (`TauCeti.Polynomial.flat_expand`), so
Orlov's affine theorem gives a triangle equivalence `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))`
(`powerXSingularityCokernelEquivalence`,
`quotientSingularityCokernel_isEquivalence_X_pow_of_krullDimLE`), sending `powerXOfLE R hi`
(`i ≤ n`) to `(R[X] ⧸ (X ^ n)) ⧸ (x ^ i)` (`quotientSingularityCokernelPowerXOfLEIso`).

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

section FixedPow
variable (n : ℕ) [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]

/-- **Singularity equivalence for `X ^ n` over `R[X]`**: `X ^ n` is a non-zero-divisor of the
regular ring `R[X]` of finite Krull dimension. -/
theorem quotientSingularityCokernel_isEquivalence_X_pow (hdim : ringKrullDim R < ⊤) :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).IsEquivalence := by
  have hdimX : ringKrullDim R[X] < ⊤ := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    cases hd : ringKrullDim R with
    | bot => exact WithBot.bot_lt_coe _
    | coe e =>
      lift e to ℕ using fun he ↦ hdim.ne (by simp [hd, he])
      exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (e + 1))
  exact quotientSingularityCokernel_isEquivalence_of_isRegularRing hdimX
    (pow_mem Polynomial.X_mem_nonZeroDivisors n)

/-- Equivalence `HMF(R[X], X ^ n) ≌ D_sg(mod-(R[X] ⧸ (X ^ n)))` for `ringKrullDim R < ⊤`. -/
def powerXSingularityCokernelEquivalence (hdim : ringKrullDim R < ⊤) :
    HomotopyCategory (S := R[X]) (w := (X ^ n : R[X])) ≌
      SingularityCategory (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) :=
  haveI := quotientSingularityCokernel_isEquivalence_X_pow.{v, u} R n hdim
  (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).asEquivalence

@[simp] theorem powerXSingularityCokernelEquivalence_functor (hdim : ringKrullDim R < ⊤) :
    (powerXSingularityCokernelEquivalence.{v, u} R n hdim).functor =
      quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X])) := (rfl)

/-- **The `X ^ n` polynomial singularity equivalence is triangulated.** -/
theorem powerXSingularityCokernelEquivalence_isTriangulated (hdim : ringKrullDim R < ⊤) :
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

end FixedPow

/-- Specialization of `quotientSingularityCokernel_isEquivalence_X_pow` under
`[Ring.KrullDimLE d R]` (covering fields, PIDs, Dedekind domains, and subsingleton rings). -/
theorem quotientSingularityCokernel_isEquivalence_X_pow_of_krullDimLE (d : ℕ) [Ring.KrullDimLE d R]
    (n : ℕ) [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))] :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).IsEquivalence :=
  quotientSingularityCokernel_isEquivalence_X_pow.{v, u} R n <|
    (Order.KrullDimLE.krullDim_le (n := d) (α := PrimeSpectrum R)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

end Equivalence

section PowerXObject

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {i n : ℕ} (hi : i ≤ n)
  [HasDerivedCategory.{v} (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))]

/-- In `D_sg(mod-(R[X] ⧸ (X ^ n)))`, `quotientSingularityCokernel` sends `powerXOfLE R hi` (`i ≤ n`)
to the cyclic module `(R[X] ⧸ (X ^ n)) ⧸ (x ^ i)` placed in degree zero. -/
def quotientSingularityCokernelPowerXOfLEIso :
    (quotientSingularityCokernel.{v, u} (S := R[X]) (w := (X ^ n : R[X]))).obj
        ((nullHomotopic (S := R[X]) (w := (X ^ n : R[X]))).quotientFunctor.obj (powerXOfLE R hi)) ≅
      (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).obj
        ((DerivedCategory.Bounded.singleFunctor
            (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).obj
          (FGModuleCat.of (R[X] ⧸ Ideal.span {(X ^ n : R[X])})
            ((R[X] ⧸ Ideal.span {(X ^ n : R[X])}) ⧸
              Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X ^ n : R[X])}) X) ^ i}))) :=
  -- `AdjoinRoot`, `mk`, and `root` reduce definitionally to `Ideal.Quotient`.
  eqToIso (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)) ≪≫
    (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).mapIso
      ((DerivedCategory.Bounded.singleFunctor
          (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).mapIso
        (powerXOfLEFGModuleCokernelIso R hi))

@[simp] theorem quotientSingularityCokernelPowerXOfLEIso_hom :
    (quotientSingularityCokernelPowerXOfLEIso.{v, u} R hi).hom =
      eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)) ≫
        (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).map
          ((DerivedCategory.Bounded.singleFunctor
              (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).map
            (powerXOfLEFGModuleCokernelIso R hi).hom) := (rfl)

@[simp] theorem quotientSingularityCokernelPowerXOfLEIso_inv :
    (quotientSingularityCokernelPowerXOfLEIso.{v, u} R hi).inv =
      (SingularityCategory.Q (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])}))).map
          ((DerivedCategory.Bounded.singleFunctor
              (FGModuleCat.{u} (R[X] ⧸ Ideal.span {(X ^ n : R[X])})) 0).map
            (powerXOfLEFGModuleCokernelIso R hi).inv) ≫
        eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj (powerXOfLE R hi)).symm :=
  (rfl)

end PowerXObject

end TauCeti.MatrixFactorization.HomotopyCategory
