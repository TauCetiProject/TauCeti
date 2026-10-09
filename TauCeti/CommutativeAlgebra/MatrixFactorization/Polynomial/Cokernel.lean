/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Polynomial.Periodic
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

private theorem range_rootPowHom (n i : ℕ) :
    LinearMap.range (rootPowHom R n i).hom =
      Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i} := by
  have h : (rootPowHom R n i).hom =
      LinearMap.mul (AdjoinRoot (X ^ n : R[X])) (AdjoinRoot (X ^ n : R[X]))
        (AdjoinRoot.root (X ^ n : R[X]) ^ i) := by
    apply LinearMap.ext
    intro a
    exact rootPowHom_apply R n i a
  rw [h]
  exact Ideal.range_mul' _

/-- The cokernel of multiplication by `x ^ i` on the regular module is `A/(x ^ i)`. -/
def rootPowHomCokernelIso (n i : ℕ) :
    cokernel (rootPowHom R n i) ≅
      ModuleCat.of (AdjoinRoot (X ^ n : R[X]))
        (AdjoinRoot (X ^ n : R[X]) ⧸
          Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ (range_rootPowHom R n i)).toModuleIso

/-- The comparison sends the cokernel projection to the cyclic quotient projection. -/
@[reassoc (attr := simp)]
theorem rootPowHomCokernelIso_π_hom (n i : ℕ) :
    cokernel.π (rootPowHom R n i) ≫ (rootPowHomCokernelIso R n i).hom =
      ModuleCat.ofHom (Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}).mkQ := by
  rw [rootPowHomCokernelIso, Iso.trans_hom, ← Category.assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Submodule.quotEquivOfEq_mk _ _ (range_rootPowHom R n i) a

/-- The reduction of `powerXOfLE` has cokernel `A/(x ^ i)`. -/
def powerXOfLECokernelQuotientIso (hi : i ≤ n) :
    ((cokernelFunctor (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self).obj
      (powerXOfLE R hi)).obj ≅
        ModuleCat.of (AdjoinRoot (X ^ n : R[X]))
          (AdjoinRoot (X ^ n : R[X]) ⧸
            Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i}) :=
  cokernelFunctorObjIso _ _ _ ≪≫
    cokernel.mapIso _ _
      ((CurvedDuplex.eval₀ _ _).mapIso (powerXOfLEBaseChangeDuplexIso R hi))
      ((CurvedDuplex.eval₁ _ _).mapIso (powerXOfLEBaseChangeDuplexIso R hi))
      (powerXOfLEBaseChangeDuplexIso R hi).hom.comm₀.symm ≪≫
    rootPowHomCokernelIso R n i

/-- The projection followed by the quotient comparison is the scalar-extension counit
followed by the ordinary cyclic quotient projection. -/
@[reassoc]
theorem powerXOfLECokernelQuotientIso_π_hom (hi : i ≤ n) :
    cokernelπ (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi) ≫
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
  exact (Category.assoc _ _ _).trans
    (congrArg (Functor.OplaxMonoidal.η
      (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) ≫ ·)
      (rootPowHomCokernelIso_π_hom R n i))

/-- The reduced polynomial factorization has the cyclic right-module cokernel `A/(x ^ i)`,
viewed as a left module through the commutativity isomorphism `A ≃ Aᵐᵒᵖ`. -/
def powerXOfLECokernelIso (hi : i ≤ n) :
    ((cokernelFunctor (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self).obj
      (powerXOfLE R hi)).obj ≅
        (ModuleCat.restrictScalars (RingEquiv.toOpposite (AdjoinRoot (X ^ n : R[X]))).toRingHom).obj
          (FGModuleCat.cyclicModule (AdjoinRoot.root (X ^ n : R[X]) ^ i)).obj := by
  let A := AdjoinRoot (X ^ n : R[X])
  let a : A := AdjoinRoot.root (X ^ n : R[X]) ^ i
  let e := Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {op a})
    (AlgEquiv.toOpposite A A) (by simp [Ideal.map_span])
  refine powerXOfLECokernelQuotientIso R hi ≪≫ ?_
  let e' : (A ⧸ Ideal.span {a}) ≃ₗ[A]
      (ModuleCat.restrictScalars (RingEquiv.toOpposite A).toRingHom).obj
        (FGModuleCat.cyclicModule a).obj :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        -- Restriction uses multiplication by `op c` on the right-module quotient.
        change e (Ideal.Quotient.mk (Ideal.span {a}) c * x) =
          Ideal.Quotient.mk (Ideal.span {op a}) (op c) * e x
        rw [map_mul]
        congr 1 }
  exact e'.toModuleIso

/-- The right cyclic-module comparison sends an odd-module representative to the class of
its scalar-extension counit image. -/
theorem powerXOfLECokernelIso_hom_cokernelπ (hi : i ≤ n)
    (a : ((baseChangeToCurvedDuplex (AdjoinRoot.mk (X ^ n : R[X]))
      AdjoinRoot.mk_self).obj (powerXOfLE R hi)).X₁) :
    (powerXOfLECokernelIso R hi).hom
      (cokernelπ (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi) a) =
        Submodule.Quotient.mk (op (Functor.OplaxMonoidal.η
          (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) a)) := by
  let e := Ideal.quotientEquivAlg
    (Ideal.span {AdjoinRoot.root (X ^ n : R[X]) ^ i})
    (Ideal.span {op (AdjoinRoot.root (X ^ n : R[X]) ^ i)})
    (AlgEquiv.toOpposite (AdjoinRoot (X ^ n : R[X])) (AdjoinRoot (X ^ n : R[X])))
    (by simp [Ideal.map_span])
  have h := ConcreteCategory.congr_hom (powerXOfLECokernelQuotientIso_π_hom R hi) a
  simp only [ConcreteCategory.comp_apply] at h
  -- The final isomorphism reuses this quotient equivalence, with the target action transported
  -- to the explicitly restricted right-module carrier.
  change e ((powerXOfLECokernelQuotientIso R hi).hom
    (cokernelπ (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self (powerXOfLE R hi) a)) = _
  rw [h]
  rfl

end TauCeti.MatrixFactorization
