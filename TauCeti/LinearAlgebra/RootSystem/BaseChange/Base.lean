/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# Pullback, scalar restriction, and scalar extension of root-pairing bases

This file provides foundational transport operations for `RootPairing.Base` without depending on
automorphism or Weyl-group theory:

* Pulling back a base `b : P.Base` along injective `R`-linear maps `fM : M₀ →ₗ[R] M` and
  `fN : N₀ →ₗ[R] N` compatible with roots and coroots over a faithful `R`-algebra `S`
  (`RootPairing.Base.comapOfInjective`).
* Restricting a base `b : P.Base` of a balanced, `K`-valued root pairing `P` over a field `L`
  along Mathlib's `RootPairing.restrictScalars' K`
  (`Mathlib/LinearAlgebra/RootSystem/BaseChange.lean`, giving `RootPairing.Base.restrictScalars'`).
* Extending scalars of a base `b : P.Base` along `RootPairing.baseChange`
  (`TauCeti/LinearAlgebra/RootSystem/BaseChange/Basic.lean`) for a faithful flat `R`-algebra `S`
  and a finite free coweight module `N` (`RootPairing.Base.baseChange`), together with invariance of
  the `T`-valued and integral Cartan matrices (`RootPairing.Base.cartanMatrixIn_baseChange_apply`,
  `RootPairing.Base.cartanMatrix_baseChange_apply`).

## Main definitions

* `RootPairing.Base.comapOfInjective`: pullback of a base along injective `R`-linear maps over a
  faithful `R`-algebra.
* `RootPairing.Base.restrictScalars'`: restriction of scalars of a base along
  `RootPairing.restrictScalars'`.
* `RootPairing.Base.baseChange`: scalar extension of a base along `RootPairing.baseChange`.

## Main results

* `RootPairing.Base.support_comapOfInjective`, `RootPairing.Base.support_restrictScalars'`, and
  `RootPairing.Base.support_baseChange`: base transport leaves `support` unchanged.
* `RootPairing.Base.cartanMatrixIn_baseChange_apply` and
  `RootPairing.Base.cartanMatrix_baseChange_apply`: scalar extension preserves every entry of the
  `T`-valued and integral Cartan matrices.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  C.43 and C.51.
-/

public section

open Function Module Set

namespace RootPairing

section BaseComap

variable {ι R S M₀ N₀ M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {P₀ : RootPairing ι R M₀ N₀} {P : RootPairing ι S M N} (b : P.Base)
  (fM : M₀ →ₗ[R] M) (fN : N₀ →ₗ[R] N) (hfM : Injective fM) (hfN : Injective fN)
  (hroot : ∀ i, fM (P₀.root i) = P.root i) (hcoroot : ∀ i, fN (P₀.coroot i) = P.coroot i)

/-- **Pullback of a base `b : P.Base`** along injective `R`-linear maps `fM : M₀ →ₗ[R] M` and
`fN : N₀ →ₗ[R] N` over a faithful `R`-algebra `S` compatible with roots and coroots. -/
noncomputable def Base.comapOfInjective : P₀.Base where
  support := b.support
  linearIndepOn_root :=
    (((funext hroot : fM ∘ P₀.root = P.root).symm ▸ b.linearIndepOn_root).restrict_scalars'
      R).of_comp fM
  linearIndepOn_coroot :=
    (((funext hcoroot : fN ∘ P₀.coroot = P.coroot).symm ▸ b.linearIndepOn_coroot).restrict_scalars'
      R).of_comp fN
  root_mem_or_neg_mem i := (fM.toAddMonoidHom.mem_closure_image_or_neg_mem_iff hfM).mp <| by
    simpa only [← image_comp, Function.comp_def, LinearMap.toAddMonoidHom_coe, hroot] using
      b.root_mem_or_neg_mem i
  coroot_mem_or_neg_mem i := (fN.toAddMonoidHom.mem_closure_image_or_neg_mem_iff hfN).mp <| by
    simpa only [← image_comp, Function.comp_def, LinearMap.toAddMonoidHom_coe, hcoroot] using
      b.coroot_mem_or_neg_mem i

/-- `Base.comapOfInjective` leaves `support` unchanged. -/
@[simp] theorem Base.support_comapOfInjective :
    (b.comapOfInjective fM fN hfM hfN hroot hcoroot).support = b.support := (rfl)

end BaseComap

section RestrictScalarsBase

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
  {P : RootPairing ι L M N} (b : P.Base) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- **Restriction of scalars of a base** along `RootPairing.restrictScalars'`, keeping the same
simple indices `b.support`. -/
noncomputable def Base.restrictScalars' : (P.restrictScalars' K).Base :=
  b.comapOfInjective (Submodule.span K (range P.root)).subtype
    (Submodule.span K (range P.coroot)).subtype Subtype.val_injective Subtype.val_injective
    (P.restrictScalars_coe_root K) (P.restrictScalars_coe_coroot K)

/-- `Base.restrictScalars'` leaves `support` unchanged. -/
@[simp] theorem Base.support_restrictScalars' : (b.restrictScalars' K).support = b.support := (rfl)

end RestrictScalarsBase

section BaseBaseChange

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

variable (b : P.Base) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S] [Flat R S]
  [Free R N] [Module.Finite R N]

/-- **Extension of scalars of a base**: the base of `P.baseChange S` with the same simple root
indices `b.support`. -/
noncomputable def Base.baseChange : (P.baseChange S).Base where
  support := b.support
  linearIndepOn_root := by
    simpa only [LinearIndepOn, Function.comp_def, P.baseChange_root S] using
      Module.Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_root
  linearIndepOn_coroot := by
    simpa only [LinearIndepOn, Function.comp_def, P.baseChange_coroot S] using
      Module.Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    simpa only [← image_comp, Function.comp_def, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, P.baseChange_root S] using
      (TensorProduct.mk R S M 1).toAddMonoidHom.map_mem_closure_image_or_neg_mem
        (b.root_mem_or_neg_mem i)
  coroot_mem_or_neg_mem i := by
    simpa only [← image_comp, Function.comp_def, LinearMap.toAddMonoidHom_coe,
      TensorProduct.mk_apply, P.baseChange_coroot S] using
      (TensorProduct.mk R S N 1).toAddMonoidHom.map_mem_closure_image_or_neg_mem
        (b.coroot_mem_or_neg_mem i)

/-- Scalar extension of a base leaves `support` unchanged. -/
@[simp] theorem Base.support_baseChange : (b.baseChange S).support = b.support := (rfl)

/-- Scalar extension preserves every entry of the `T`-valued Cartan matrix of a base. -/
@[simp] theorem Base.cartanMatrixIn_baseChange_apply (T : Type*) [CommRing T] [Algebra T R]
    [Algebra T S] [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T]
    (i j : (b.baseChange S).support) :
    (b.baseChange S).cartanMatrixIn T i j =
      b.cartanMatrixIn T ⟨i, (b.support_baseChange S).le i.property⟩
        ⟨j, (b.support_baseChange S).le j.property⟩ := by simp [Base.cartanMatrixIn_def]

/-- Scalar extension preserves every entry of the integral Cartan matrix of a crystallographic
root pairing. -/
theorem Base.cartanMatrix_baseChange_apply [CharZero S] [P.IsCrystallographic]
    (i j : (b.baseChange S).support) :
    (b.baseChange S).cartanMatrix i j = b.cartanMatrix ⟨i, (b.support_baseChange S).le i.property⟩
      ⟨j, (b.support_baseChange S).le j.property⟩ := b.cartanMatrixIn_baseChange_apply S ℤ i j

end BaseBaseChange

end RootPairing
