/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Basic
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Polynomial.Augmentation
public import TauCeti.Algebra.Category.FGModuleCat.Cyclic

/-!
# The cyclic cokernel of a polynomial matrix factorization

Put `A = R[X]/(X ^ n)` and let `x` be the class of `X`. Reduction of the factorization with
maps `X ^ i` and `X ^ (n - i)` has cokernel `A/(x ^ i)`. The comparison is compatible with the
projection from its odd free module, so it supplies the augmentation of the alternating periodic
complex. It applies over every commutative coefficient ring, including the boundary indices
`i = 0` and `i = n`.

The final comparison uses the existing right module `FGModuleCat.cyclicModule (x ^ i)`.
Commutativity identifies left `A`-modules with right `A`-modules by restriction along
`RingEquiv.toOpposite A`; the comparison is stated in `ModuleCat A` with that explicit
restriction, rather than identifying their scalar carriers definitionally.

The quotient comparison uses Mathlib's `ModuleCat.cokernelIsoRangeQuotient` and
`Ideal.quotientEquivAlg`. The matrix factorization and its cokernel follow D. Eisenbud,
*Homological algebra on a complete intersection, with an application to group representations*,
Trans. Amer. Math. Soc. **260** (1980), Section 5. No MCM or stable-equivalence assertion is
made here.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits Polynomial MulOpposite

variable (R : Type u) [CommRing R] {i n : ℕ}

/-- The reduction of `powerXOfLE` has cokernel `A/(x ^ i)`. -/
def powerXOfLECokernelQuotientIso (hi : i ≤ n) :
    ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X])) ⋙ cokernelFunctor).obj
      (powerXOfLE R hi)).obj ≅
        ModuleCat.of (AdjoinRoot (X ^ n : R[X]))
          (AdjoinRoot (X ^ n : R[X]) ⧸
            Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) :=
  cokernelFunctorObjIso _ ≪≫
    cokernel.mapIso _ _
      ((CurvedDuplex.eval₀ _ _).mapIso (powerXOfLEBaseChangeDuplexIso R hi))
      ((CurvedDuplex.eval₁ _ _).mapIso (powerXOfLEBaseChangeDuplexIso R hi))
      (powerXOfLEBaseChangeDuplexIso R hi).hom.comm₀.symm ≪≫
    rootPowHomCokernelIso R n i

/-- The projection followed by the quotient comparison is the scalar-extension counit
followed by the ordinary cyclic quotient projection. -/
@[reassoc (attr := simp)]
theorem cokernelπ_comp_powerXOfLECokernelQuotientIso_hom (hi : i ≤ n) :
    cokernelπ ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj (powerXOfLE R hi)) ≫
      (powerXOfLECokernelQuotientIso R hi).hom =
        Functor.OplaxMonoidal.η (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) ≫
          ModuleCat.ofHom (Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}).mkQ := by
  dsimp only [powerXOfLECokernelQuotientIso, Iso.trans_hom]
  rw [cokernelπ_objIso_hom_assoc]
  -- The target differential of the duplex is `rootPowHom`, but its opaque indexed carrier
  -- blocks rewriting the inner composite isomorphism. Use its known component presentation.
  change cokernel.π ((baseChangeToCurvedDuplex (AdjoinRoot.mk (X ^ n : R[X]))
      AdjoinRoot.mk_self).obj (powerXOfLE R hi)).d₀ ≫
    cokernel.map _ (rootPowHom R n i)
      (powerXOfLEBaseChangeDuplexIso R hi).hom.f₀
      (powerXOfLEBaseChangeDuplexIso R hi).hom.f₁
      (powerXOfLEBaseChangeDuplexIso R hi).hom.comm₀.symm ≫
    (rootPowHomCokernelIso R n i).hom = _
  dsimp only [cokernel.map]
  rw [cokernel.π_desc_assoc]
  rw [powerXOfLEBaseChangeDuplexIso_hom_f₁]
  have hAug : powerXAugmentation R n i =
      ModuleCat.ofHom (Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}).mkQ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact powerXAugmentation_apply R n i a
  exact (Category.assoc _ _ _).trans
    (congrArg (Functor.OplaxMonoidal.η
      (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) ≫ ·)
      ((cokernel_π_comp_rootPowHom_cokernelIso_hom R n i).trans hAug))

/-- The reduced polynomial factorization has the cyclic right-module cokernel `A/(x ^ i)`,
viewed as a left module through the commutativity isomorphism `A ≃ Aᵐᵒᵖ`. -/
def powerXOfLECokernelIso (hi : i ≤ n) :
    ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X])) ⋙ cokernelFunctor).obj
      (powerXOfLE R hi)).obj ≅
        (ModuleCat.restrictScalars (RingEquiv.toOpposite (AdjoinRoot (X ^ n : R[X]))).toRingHom).obj
          (FGModuleCat.cyclicModule (AdjoinRoot.root (X ^ n : R[X]) ^ i)).obj :=
  powerXOfLECokernelQuotientIso R hi ≪≫
    FGModuleCat.quotientSpanCyclicModuleIso (AdjoinRoot.root (X ^ n : R[X]) ^ i)

/-- The right cyclic-module comparison sends an odd-module representative to the class of
its scalar-extension counit image. -/
theorem cokernelπ_comp_powerXOfLECokernelIso_hom_apply (hi : i ≤ n)
    (a : ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj
      (powerXOfLE R hi)).obj.X₁.obj) :
    (powerXOfLECokernelIso R hi).hom
      (cokernelπ ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj (powerXOfLE R hi)) a) =
        Submodule.Quotient.mk (op (Functor.OplaxMonoidal.η
          (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) a)) := by
  have h := ConcreteCategory.congr_hom (cokernelπ_comp_powerXOfLECokernelQuotientIso_hom R hi) a
  simp only [ConcreteCategory.comp_apply] at h
  dsimp only [powerXOfLECokernelIso, Iso.trans_hom]
  simp only [ConcreteCategory.comp_apply]
  rw [h]
  exact FGModuleCat.quotientSpanCyclicModuleIso_hom_mk _ _

end TauCeti.MatrixFactorization
