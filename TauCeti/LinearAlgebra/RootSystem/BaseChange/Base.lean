/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# Pullback and extension of scalars of a base

This file provides transport operations for `RootPairing.Base`:

* Pulling back a base `b : P.Base` along injective `R`-linear maps `fM : M₀ →ₗ[R] M` and
  `fN : N₀ →ₗ[R] N` compatible with roots and coroots over a faithful `R`-algebra `S`
  (`RootPairing.Base.comapOfInjective`, `RootPairing.Base.support_comapOfInjective`).
* Extending a base of a root pairing along an injective flat ring map to a base of the
  tensor-product root pairing (`RootPairing.Base.baseChange`), with the same simple-root indices.
  The positive cones, integer root coefficients, heights and Cartan matrices are preserved. No
  spanning hypothesis is imposed on the roots or coroots: in particular this construction applies to
  integral reductive root data with central directions in their character and cocharacter lattices.

For an integral datum, `b.baseChange ℚ` gives its chosen base over the rationals. One can then
restrict to the rational root and coroot spans using `Base.restrictScalars'` and decompose into
based irreducible components.

The root pairing itself is `RootPairing.baseChange`; preservation of linear independence uses
Mathlib's `Module.Flat.linearIndependent_one_tmul`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  C.43 and C.51.
-/

public section

open Function Module TensorProduct Set

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

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)
  (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Free R N] [Module.Finite R N]

variable {P} (b : P.Base) [Flat R S]

/-- Extension of a base along an injective flat ring map, on the same simple-root support. -/
noncomputable def Base.baseChange : (P.baseChange S).Base where
  support := b.support
  linearIndepOn_root := by
    simpa only [LinearIndepOn, baseChange_root] using
      (Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_root)
  linearIndepOn_coroot := by
    simpa only [LinearIndepOn, baseChange_coroot] using
      (Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_coroot)
  root_mem_or_neg_mem i := (b.root_mem_or_neg_mem i).imp
    (fun h ↦ by simpa only [baseChange_root] using (P.mem_closure_root_baseChange_iff S).mpr h)
    fun h ↦ by
      simpa only [baseChange_root, tmul_neg] using (P.mem_closure_root_baseChange_iff S).mpr h
  coroot_mem_or_neg_mem i := (b.coroot_mem_or_neg_mem i).imp
    (fun h ↦ by simpa only [baseChange_coroot] using
      (P.mem_closure_coroot_baseChange_iff S).mpr h)
    fun h ↦ by
      simpa only [baseChange_coroot, tmul_neg] using (P.mem_closure_coroot_baseChange_iff S).mpr h

@[simp]
theorem Base.support_baseChange : (b.baseChange S).support = b.support := (rfl)

/-- The simple-root indices of the extended base are those of the original base. -/
def Base.supportBaseChangeEquiv : (b.baseChange S).support ≃ b.support :=
  Equiv.subtypeEquivRight fun _ ↦ by rw [Base.support_baseChange]

@[simp]
theorem Base.coe_supportBaseChangeEquiv (i : (b.baseChange S).support) :
    (b.supportBaseChangeEquiv S i : ι) = i := (rfl)

@[simp]
theorem Base.coe_supportBaseChangeEquiv_symm (i : b.support) :
    ((b.supportBaseChangeEquiv S).symm i : ι) = i := (rfl)

/-- Extension of scalars preserves the Cartan matrix with values in any common coefficient
ring. In particular it preserves the integer Cartan matrix of a crystallographic pairing. -/
@[simp]
theorem Base.cartanMatrixIn_baseChange (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [P.IsValuedIn T]
    (i j : (b.baseChange S).support) :
    (b.baseChange S).cartanMatrixIn T i j =
      b.cartanMatrixIn T (b.supportBaseChangeEquiv S i) (b.supportBaseChangeEquiv S j) := by
  simp only [Base.cartanMatrixIn, Matrix.of_apply, Base.coe_supportBaseChangeEquiv,
    baseChange_pairingIn]

variable [CharZero R] [CharZero S]

/-- The integer simple-root coefficients of an extended root are unchanged. -/
@[simp]
theorem Base.rootCoefficients_baseChange (i : ι) (j : (b.baseChange S).support) :
    (b.baseChange S).rootCoefficients i j =
      b.rootCoefficients i (b.supportBaseChangeEquiv S j) := by
  have h : (P.baseChange S).root i =
      ∑ k : b.support, b.rootCoefficients i k •
        (P.baseChange S).root k := by
    simpa only [map_sum, map_zsmul, baseChange_root, TensorProduct.mk_apply] using
      (congrArg (TensorProduct.mk R S M 1) (b.sum_rootCoefficients_smul_root i)).symm
  exact (b.baseChange S).rootCoefficients_apply_of_injective Subtype.val_injective
    (fun k ↦ k.property) h (b.supportBaseChangeEquiv S j)

/-- Extension of a base preserves root heights. -/
@[simp]
theorem Base.height_baseChange (i : ι) : (b.baseChange S).height i = b.height i := by
  rw [← (b.baseChange S).sum_rootCoefficients_eq_height, ← b.sum_rootCoefficients_eq_height]
  simp only [Base.rootCoefficients_baseChange]
  exact (b.supportBaseChangeEquiv S).sum_comp _

/-- A root is positive for the extended base exactly when it was positive for the original base. -/
@[simp]
theorem Base.isPos_baseChange_iff (i : ι) : (b.baseChange S).IsPos i ↔ b.IsPos i := by
  simp only [Base.isPos_iff, Base.height_baseChange]

end RootPairing
