/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Polynomial.Periodic
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Augmenting the periodic resolution of a truncated polynomial module

The alternating multiplication maps on `R[X]/(X^n)` give an exact two-periodic complex. The
quotient by the image of multiplication by `x^i` is the cyclic module
`(R[X]/(X^n))/(x^i)`. This file supplies the augmentation and proves its cokernel property, so
the periodic complex is the tail of a free resolution of that cyclic module.

The construction works over a commutative ring. In particular, it applies to the polynomial
matrix factorization of `X^n` over a field without a characteristic hypothesis.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits Polynomial

variable (R : Type u) [CommRing R]

/-- The augmentation from the regular module over `R[X]/(X^n)` to its cyclic quotient by
`x^i`. -/
def powerXAugmentation (n i : ℕ) :
    ModuleCat.of (AdjoinRoot (X ^ n : R[X])) (AdjoinRoot (X ^ n : R[X])) ⟶
      ModuleCat.of (AdjoinRoot (X ^ n : R[X]))
        (AdjoinRoot (X ^ n : R[X]) ⧸ Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) :=
  ModuleCat.ofHom (Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}).mkQ

/-- The augmentation sends an element to its residue class modulo `x^i`. -/
@[simp] theorem powerXAugmentation_apply (n i : ℕ) (a : AdjoinRoot (X ^ n : R[X])) :
    powerXAugmentation R n i a =
      Submodule.Quotient.mk a := (rfl)

/-- The image of multiplication by `x^i` is the principal ideal `(x^i)`. -/
theorem rootPowHom_range (n i : ℕ) :
    (rootPowHom R n i).hom.range =
      Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i} := by
  have h : (rootPowHom R n i).hom =
      LinearMap.toSpanSingleton (AdjoinRoot (X ^ n : R[X])) (AdjoinRoot (X ^ n : R[X]))
        (AdjoinRoot.root (X ^ n : R[X]) ^ i) := by
    apply LinearMap.ext
    intro a
    -- The categorical morphism and its underlying linear map have the same application.
    change rootPowHom R n i a = _
    rw [rootPowHom_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  rw [h, LinearMap.range_toSpanSingleton]

/-- Multiplication by `x^i` followed by the quotient by `(x^i)` is exact at the regular
module. -/
theorem exact_rootPowHom_powerXAugmentation (n i : ℕ) :
    Function.Exact (rootPowHom R n i).hom (powerXAugmentation R n i).hom := by
  rw [LinearMap.exact_iff]
  simpa only [powerXAugmentation, ModuleCat.hom_ofHom, Submodule.ker_mkQ] using
    (rootPowHom_range R n i).symm

/-- Multiplication by `x^i` vanishes after passing to the cyclic quotient. -/
@[simp] theorem rootPowHom_comp_powerXAugmentation (n i : ℕ) :
    rootPowHom R n i ≫ powerXAugmentation R n i = 0 :=
  ModuleCat.hom_ext (exact_rootPowHom_powerXAugmentation R n i).linearMap_comp_eq_zero

/-- The augmentation is surjective. -/
theorem powerXAugmentation_surjective (n i : ℕ) :
    Function.Surjective (powerXAugmentation R n i).hom :=
  Submodule.mkQ_surjective _

/-- The augmentation is a cokernel of multiplication by `x^i`. -/
def powerXAugmentationIsCokernel (n i : ℕ) :
    IsColimit (CokernelCofork.ofπ (powerXAugmentation R n i)
      (rootPowHom_comp_powerXAugmentation R n i)) :=
  ModuleCat.isColimitCokernelCofork (rootPowHom R n i) (powerXAugmentation R n i)
    (exact_rootPowHom_powerXAugmentation R n i)
    (powerXAugmentation_surjective R n i)

/-- The categorical cokernel of multiplication by `x^i` is the cyclic quotient by `(x^i)`. -/
def rootPowHomCokernelIso (n i : ℕ) :
    cokernel (rootPowHom R n i) ≅
      ModuleCat.of (AdjoinRoot (X ^ n : R[X]))
        (AdjoinRoot (X ^ n : R[X]) ⧸ Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) :=
  ModuleCat.cokernelIsoRangeQuotient (rootPowHom R n i) ≪≫
    (Submodule.quotEquivOfEq _ _ (rootPowHom_range R n i)).toModuleIso

/-- The canonical cokernel projection, followed by the identification with the cyclic module,
is the augmentation. -/
@[simp] theorem cokernel_π_comp_rootPowHom_cokernelIso_hom (n i : ℕ) :
    cokernel.π (rootPowHom R n i) ≫ (rootPowHomCokernelIso R n i).hom =
      powerXAugmentation R n i := by
  -- Expose the two canonical quotient isomorphisms to rewrite the cokernel projection.
  dsimp [rootPowHomCokernelIso]
  rw [← Category.assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  -- Both maps are quotient maps; the second only changes the named defining submodule.
  change (Submodule.quotEquivOfEq _ _ (rootPowHom_range R n i))
    (Submodule.Quotient.mk a) = Submodule.Quotient.mk a
  exact Submodule.quotEquivOfEq_mk _ _ (rootPowHom_range R n i) a

end TauCeti.MatrixFactorization
