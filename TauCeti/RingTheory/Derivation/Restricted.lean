/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CharP.LinearMaps
public import TauCeti.Algebra.Lie.Restricted.Basic
public import TauCeti.RingTheory.Derivation.Lie
public import TauCeti.RingTheory.Derivation.PPow

/-!
# The restricted Lie algebra structure on derivations

For an `R`-algebra `A` of exponential characteristic `p`, `Derivation.pPow p` (defined in
`TauCeti.RingTheory.Derivation.PPow`, together with `R`-homogeneity and Hochschild's `A`-scaling
formula `Derivation.pPow_smul`) satisfies Jacobson's additivity formula (`Derivation.pPow_add`):

`(D + E).pPow p = D.pPow p + E.pPow p + TauCeti.LieAlgebra.jacobson p D E`.

When `R` is a commutative ring and `A` is a commutative `R`-algebra of prime characteristic `p`,
this equips `Derivation R A A` with a canonical restricted Lie algebra structure
(`Derivation.instRestrictedLieAlgebra`), and the canonical inclusion
`Derivation.toEndRestrictedLieHom` into `Module.End R A` is an injective morphism of restricted
Lie algebras extending `Derivation.toLinearMapLieHom`.

## Main definitions

* `Derivation.instRestrictedLieAlgebra`: the restricted Lie algebra structure on `Derivation R A A`
  with `p`-map `D ↦ D.pPow p`.
* `Derivation.toEndRestrictedLieHom`: the restricted Lie algebra embedding
  `Derivation R A A → Module.End R A`.

## Main results

* `Derivation.pPow_add`: Jacobson's formula for `(D + E).pPow p`.
* `Derivation.pMap_eq_pPow`: rewrite exposing `RestrictedLieAlgebra.pMap D = D.pPow p`.
* `Derivation.toEndRestrictedLieHom_injective`: injectivity of `Derivation.toEndRestrictedLieHom`.

## References

* N. Jacobson, *Restricted Lie algebras of characteristic `p`*, Trans. Amer. Math. Soc. **50**
  (1941), 15–25.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: Applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), §5 (5.0).
-/

public section

namespace Derivation

section CommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section EndHom

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Jacobson's formula for the `p`-th power of a sum of derivations in exponential
characteristic `p`. -/
theorem pPow_add (D E : Derivation R A A) (p : ℕ) [ExpChar A p] :
    (D + E).pPow p = D.pPow p + E.pPow p + TauCeti.LieAlgebra.jacobson p D E := by
  refine toLinearMapLieHom_injective ?_
  have : ExpChar (Module.End R A) p := inferInstance
  calc
    (toLinearMapLieHom R A ((D + E).pPow p) : Module.End R A)
      = ((toLinearMapLieHom R A D : Module.End R A) + toLinearMapLieHom R A E) ^ p := by
        rw [toLinearMapLieHom_apply, toLinearMap_pPow, ← map_add, toLinearMapLieHom_apply]
    _ = (toLinearMapLieHom R A D : Module.End R A) ^ p +
          (toLinearMapLieHom R A E : Module.End R A) ^ p +
          TauCeti.LieAlgebra.jacobson p (toLinearMapLieHom R A D) (toLinearMapLieHom R A E) :=
        TauCeti.LieAlgebra.add_pow_eq_jacobson p _ _
    _ = toLinearMapLieHom R A (D.pPow p + E.pPow p + TauCeti.LieAlgebra.jacobson p D E) := by
        simp only [map_add, toLinearMapLieHom_apply, toLinearMap_pPow, LieHom.map_jacobson]

/-- Derivations of a commutative `R`-algebra of prime characteristic `p` form a restricted Lie
algebra with `p`-map `D ↦ D.pPow p`. -/
instance instRestrictedLieAlgebra (p : ℕ) [Fact p.Prime] [CharP A p] :
    TauCeti.RestrictedLieAlgebra R (Derivation R A A) p where
  prime := Fact.out
  p_nsmul_eq_zero D := by
    ext a
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  pMap D := D.pPow p
  pMap_smul c D := D.pPow_const_smul p c
  ad_pMap D := D.ad_pPow p
  pMap_add D E := D.pPow_add E p

/-- Expose the `p`-map of `Derivation.instRestrictedLieAlgebra` as `Derivation.pPow p`. -/
@[simp]
theorem pMap_eq_pPow (p : ℕ) [Fact p.Prime] [CharP A p] (D : Derivation R A A) :
    TauCeti.RestrictedLieAlgebra.pMap (R := R) (p := p) D = D.pPow p :=
  (rfl)

variable (R A) in
/-- The canonical embedding `Derivation R A A → Module.End R A` as an injective morphism of
restricted Lie algebras into the associative restricted Lie algebra `ofAssociative`. -/
def toEndRestrictedLieHom (p : ℕ) [Fact p.Prime] [CharP A p] :
    @TauCeti.RestrictedLieHom R p (Derivation R A A) (Module.End R A) _ _ _ _ _ _
      (@TauCeti.RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
        (CharP.cast_eq_zero (Module.End R A) p)) :=
  @TauCeti.RestrictedLieHom.mk R p (Derivation R A A) (Module.End R A) _ _ _ _ _ _
    (@TauCeti.RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
      (CharP.cast_eq_zero (Module.End R A) p))
    (toLinearMapLieHom R A) fun D => by
      dsimp only [LieHom.toFun_eq_coe]
      rw [pMap_eq_pPow, toLinearMapLieHom_apply, toLinearMapLieHom_apply, toLinearMap_pPow]
      exact (TauCeti.RestrictedLieAlgebra.ofAssociative_pMap R (Module.End R A) p
        (CharP.cast_eq_zero (Module.End R A) p) (D : Module.End R A)).symm

/-- Evaluating `toEndRestrictedLieHom` on a derivation returns its underlying linear
endomorphism. -/
@[simp]
theorem toEndRestrictedLieHom_apply (p : ℕ) [Fact p.Prime] [CharP A p] (D : Derivation R A A) :
    toEndRestrictedLieHom R A p D = (D : Module.End R A) :=
  toLinearMapLieHom_apply D

/-- The underlying Lie algebra morphism of `toEndRestrictedLieHom` is `toLinearMapLieHom`. -/
@[simp]
theorem toLieHom_toEndRestrictedLieHom (p : ℕ) [Fact p.Prime] [CharP A p] :
    @TauCeti.RestrictedLieHom.toLieHom R p (Derivation R A A) (Module.End R A) _ _ _ _ _ _
      (@TauCeti.RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
        (CharP.cast_eq_zero (Module.End R A) p))
      (toEndRestrictedLieHom R A p) = toLinearMapLieHom R A :=
  (rfl)

/-- The restricted Lie algebra morphism `Derivation.toEndRestrictedLieHom` is injective. -/
theorem toEndRestrictedLieHom_injective (p : ℕ) [Fact p.Prime] [CharP A p] :
    Function.Injective (toEndRestrictedLieHom R A p) :=
  toLinearMapLieHom_injective

end EndHom

end CommRing

end Derivation

section Examples

open Polynomial

-- Witness: over mixed-characteristic base ring `ℤ`, `RestrictedLieHom.ad` expresses the
-- adjoint representation of `Derivation ℤ (ZMod p)[X] (ZMod p)[X]`.
example (p : ℕ) [Fact p.Prime] (D : Derivation ℤ (ZMod p)[X] (ZMod p)[X]) :
    TauCeti.RestrictedLieHom.ad ℤ (Derivation ℤ (ZMod p)[X] (ZMod p)[X]) p D =
      LieAlgebra.ad ℤ (Derivation ℤ (ZMod p)[X] (ZMod p)[X]) D :=
  TauCeti.RestrictedLieHom.ad_apply _ _ _ D

-- Witness: `Derivation.pPow_add` also holds in exponential characteristic `1` (characteristic `0`).
example (D E : Derivation ℚ ℚ[X] ℚ[X]) :
    (D + E).pPow 1 = D.pPow 1 + E.pPow 1 := by
  rw [Derivation.pPow_add, TauCeti.LieAlgebra.jacobson_one, add_zero]

end Examples
