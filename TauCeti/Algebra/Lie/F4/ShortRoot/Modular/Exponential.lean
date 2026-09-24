/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ModularLattice
public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.DividedAction
public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
public import TauCeti.Algebra.Lie.BaseChange.Cancel
public import TauCeti.Algebra.Lie.BaseChange.Module
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Field.ZMod

/-!
# Integral root exponentials on the modular F₄ short-root ideal

This file identifies the ambient integral root exponential on the modular short-root ideal
with the existing sparse linear and divided-square matrices.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §12, for integral divided powers.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule
open scoped TensorProduct
open TauCeti.F4ShortRoot

noncomputable section

attribute [local instance high] Algebra.toModule

/-- The three-term root polynomial on the scalar extension of the modular short-root ideal. -/
noncomputable def f4ShortRootExponential {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) :
    Module.End A (A ⊗[ZMod 2] f4ShortRootLieIdeal) :=
  1 + t • (f4ShortRootSignedSimpleAdjoint k).baseChange A +
    t ^ 2 • (f4ShortRootDividedAdjointSquare k).baseChange A

/-- On pure tensors, the restricted root action is its three-term divided-power polynomial. -/
@[simp] theorem f4ShortRootExponential_apply {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (z : f4ShortRootLieIdeal) :
    f4ShortRootExponential k t ((1 : A) ⊗ₜ[ZMod 2] z) =
      (1 : A) ⊗ₜ[ZMod 2] z +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootSignedSimpleAdjoint k z) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootDividedAdjointSquare k z) := by
  unfold f4ShortRootExponential
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul]

/-- Include the scalar-extended short-root ideal in the integral Chevalley lattice after
canceling the intermediate base change through `ZMod 2`. -/
noncomputable def f4ShortRootBaseChangeInclusion {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] :
    A ⊗[ZMod 2] f4ShortRootLieIdeal →ₗ[A] A ⊗[ℤ] f4ChevalleyLieLattice :=
  (TauCeti.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice).toLinearMap.comp
    ((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A)

/-- Evaluate the scalar-extended ideal inclusion as inclusion followed by cancellation. -/
theorem f4ShortRootBaseChangeInclusion_apply {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (z : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    f4ShortRootBaseChangeInclusion (A := A) z =
      TauCeti.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice
        (((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A) z) := by
  simp only [f4ShortRootBaseChangeInclusion, LinearMap.comp_apply,
    LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom]

/-- On a pure tensor, the scalar-extended ideal inclusion is the scalar-tower cancellation of the
underlying modular vector. -/
@[simp] theorem f4ShortRootBaseChangeInclusion_tmul {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (a : A) (z : f4ShortRootLieIdeal) :
    f4ShortRootBaseChangeInclusion (A := A) (a ⊗ₜ[ZMod 2] z) =
      TauCeti.cancelBaseChange ℤ (ZMod 2) A
        f4ChevalleyLieLattice
          (a ⊗ₜ[ZMod 2] (z : f4ModularChevalleyLieAlgebra)) := by
  -- Expand the inclusion and its two subtype coercions on this pure tensor.
  change (TauCeti.cancelBaseChange ℤ (ZMod 2) A
      f4ChevalleyLieLattice)
        (((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A) (a ⊗ₜ[ZMod 2] z)) = _
  exact congrArg (TauCeti.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice)
    (LinearMap.baseChange_tmul f4ShortRootLieIdeal.incl.toLinearMap a z)

/-- Scalar extension preserves the injection of the short-root ideal into the Chevalley lattice. -/
theorem f4ShortRootBaseChangeInclusion_injective {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] :
    Function.Injective (f4ShortRootBaseChangeInclusion (A := A)) := by
  let _ : Module.Free (ZMod 2) A := Module.Free.of_divisionRing (ZMod 2) A
  have hbase : Function.Injective ((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f4ShortRootLieIdeal.incl.toLinearMap
      f4ShortRootLieIdeal.incl_injective
  intro x y hxy
  apply hbase
  apply (TauCeti.cancelBaseChange ℤ (ZMod 2) A
    f4ChevalleyLieLattice).injective
  exact hxy

/-- The scalar-extended adjoint action on the modular short-root ideal, with the ambient
Chevalley lattice written directly as `A ⊗[ℤ] Lℤ`. -/
noncomputable def f4ShortRootBaseChangeAdjoint {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] :
    A ⊗[ℤ] f4ChevalleyLieLattice →ₗ[A]
      Module.End A (A ⊗[ZMod 2] f4ShortRootLieIdeal) :=
  -- Endomorphisms carry the commutator Lie bracket for this adjoint representation.
  letI : LieRing (Module.End A (A ⊗[ZMod 2] f4ShortRootLieIdeal)) :=
    LieRing.ofAssociativeRing
  (LieModule.toEnd A
    (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
    (A ⊗[ZMod 2] f4ShortRootLieIdeal)).toLinearMap.comp
      (TauCeti.cancelBaseChange ℤ (ZMod 2) A
        f4ChevalleyLieLattice).symm.toLinearMap

/-- The scalar-extended adjoint acts through cancellation of the two scalar extensions. -/
@[simp] theorem f4ShortRootBaseChangeAdjoint_apply
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : A ⊗[ℤ] f4ChevalleyLieLattice)
    (z : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    f4ShortRootBaseChangeAdjoint x z =
      (LieModule.toEnd A
        (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
        (A ⊗[ZMod 2] f4ShortRootLieIdeal))
        ((TauCeti.cancelBaseChange ℤ (ZMod 2) A
          f4ChevalleyLieLattice).symm x) z := by
  rfl

private theorem f4ShortRootInclusion_baseChange_lie
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
    (z : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    ((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A) ⁅x, z⁆ =
      ⁅x, ((f4ShortRootLieIdeal.incl.toLinearMap).baseChange A) z⁆ := by
  exact LieModuleHom.baseChange_map_lie A (LieSubmodule.incl f4ShortRootLieIdeal) x z

/-- Evaluating the scalar-extended adjoint action and then including the ideal is the ambient
Lie bracket. -/
theorem f4ShortRootBaseChangeInclusion_adjoint {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A]
    (x : A ⊗[ℤ] f4ChevalleyLieLattice)
    (z : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    f4ShortRootBaseChangeInclusion (A := A) (f4ShortRootBaseChangeAdjoint x z) =
      ⁅x, f4ShortRootBaseChangeInclusion (A := A) z⁆ := by
  let e := TauCeti.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice
  let f := (f4ShortRootLieIdeal.incl.toLinearMap).baseChange A
  calc
    _ = e (f ((LieModule.toEnd A
        (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
        (A ⊗[ZMod 2] f4ShortRootLieIdeal)) (e.symm x) z)) := by
      have hinc : f4ShortRootBaseChangeInclusion (A := A)
          (f4ShortRootBaseChangeAdjoint x z) =
          e (f (f4ShortRootBaseChangeAdjoint x z)) := by
        simpa only [e, f] using
          f4ShortRootBaseChangeInclusion_apply (f4ShortRootBaseChangeAdjoint x z)
      exact hinc.trans (congrArg (fun w => e (f w))
        (f4ShortRootBaseChangeAdjoint_apply x z))
    _ = e (f ⁅e.symm x, z⁆) := congrArg (fun w => e (f w))
      (LieModule.toEnd_apply_apply A _ _ (e.symm x) z)
    _ = e ⁅e.symm x, f z⁆ := congrArg e
      (f4ShortRootInclusion_baseChange_lie (e.symm x) z)
    _ = ⁅e (e.symm x), e (f z)⁆ := e.map_lie _ _
    _ = ⁅x, e (f z)⁆ :=
      congrArg (fun w => ⁅w, e (f z)⁆) (e.apply_symm_apply x)
    _ = _ := by
      have hinc : f4ShortRootBaseChangeInclusion (A := A) z = e (f z) := by
        simpa only [e, f] using f4ShortRootBaseChangeInclusion_apply z
      exact congrArg (fun w => ⁅x, w⁆) hinc.symm

/-- On a scalar-extended pure tensor, the ambiently indexed adjoint action is the base change of
the original modular adjoint action. -/
theorem f4ShortRootBaseChangeAdjoint_cancel_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : f4ModularChevalleyLieAlgebra) :
    f4ShortRootBaseChangeAdjoint
        (TauCeti.cancelBaseChange ℤ (ZMod 2) A
          f4ChevalleyLieLattice ((1 : A) ⊗ₜ[ZMod 2] x)) =
      (f4ShortRootAdjoint x).baseChange A := by
  let e := TauCeti.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice
  -- The imported restricted adjoint is opaque here, so compare its action pointwise.
  have hrho : (LieModule.toEnd (ZMod 2) f4ModularChevalleyLieAlgebra
      f4ShortRootLieIdeal) x = f4ShortRootAdjoint x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change ⁅x, (y : f4ModularChevalleyLieAlgebra)⁆ =
      (f4ShortRootAdjoint x y : f4ModularChevalleyLieAlgebra)
    exact (coe_f4ShortRootAdjoint_apply x y).symm
  -- Expand scalar cancellation and the transported adjoint on this pure tensor.
  change (LieModule.toEnd A
      (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
      (A ⊗[ZMod 2] f4ShortRootLieIdeal))
        (e.symm (e ((1 : A) ⊗ₜ[ZMod 2] x))) = _
  calc
    _ = (LieModule.toEnd A
        (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
        (A ⊗[ZMod 2] f4ShortRootLieIdeal)) ((1 : A) ⊗ₜ[ZMod 2] x) :=
      congrArg (LieModule.toEnd A
        (A ⊗[ZMod 2] f4ModularChevalleyLieAlgebra)
        (A ⊗[ZMod 2] f4ShortRootLieIdeal))
        (e.symm_apply_apply ((1 : A) ⊗ₜ[ZMod 2] x))
    _ = (LieModule.toEnd (ZMod 2) f4ModularChevalleyLieAlgebra
        f4ShortRootLieIdeal x).baseChange A :=
      LieModule.toEnd_baseChange (ZMod 2) A
        f4ModularChevalleyLieAlgebra f4ShortRootLieIdeal x
    _ = _ := congrArg (LinearMap.baseChange A) hrho

/-- The matrix of the scalar-extended adjoint action on a pure tensor is obtained by applying the
coefficient map entrywise to the original modular matrix. -/
theorem f4ShortRootBaseChangeAdjoint_toMatrix_cancel_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : f4ModularChevalleyLieAlgebra) :
    LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootBaseChangeAdjoint
          (TauCeti.cancelBaseChange ℤ (ZMod 2) A
            f4ChevalleyLieLattice ((1 : A) ⊗ₜ[ZMod 2] x))) =
      (f4ShortRootAdjointMatrix x).map (algebraMap (ZMod 2) A) := by
  calc
    _ = LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        ((f4ShortRootAdjoint x).baseChange A) :=
      congrArg (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A))
        (f4ShortRootBaseChangeAdjoint_cancel_tmul x)
    -- The imported adjoint matrix is opaque here; use its public coordinate equality.
    _ = _ :=
      (Module.Basis.toMatrix_baseChange_baseChange (S := A) f4ShortRootLieIdealBasis
        (f4ShortRootAdjoint x)).trans
        (congrArg (fun m : Matrix (Fin 26) (Fin 26) (ZMod 2) =>
          m.map (algebraMap (ZMod 2) A))
          (f4ShortRootAdjointMatrix_eq_toMatrix x).symm)

/-- A modular ideal vector with an integral lift maps to that lift after scalar extension. -/
theorem f4ShortRootBaseChangeInclusion_tmul_of_coe_eq {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (a : A) (z : f4ShortRootLieIdeal)
    (y : f4ChevalleyLieLattice)
    (h : (z : f4ModularChevalleyLieAlgebra) = 1 ⊗ₜ[ℤ] y) :
    f4ShortRootBaseChangeInclusion (A := A) (a ⊗ₜ[ZMod 2] z) = a ⊗ₜ[ℤ] y := by
  rw [f4ShortRootBaseChangeInclusion_tmul, h, TauCeti.cancelBaseChange_tmul]
  simp

/-- On any ideal vector represented by a single integral tensor, the integral root exponential
intertwines the modular three-term polynomial with the scalar-tower inclusion. -/
theorem f4RootExponential_intertwines_tmul_of_coe_eq {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A)
    (z : f4ShortRootLieIdeal) (y : f4ChevalleyLieLattice)
    (hz : (z : f4ModularChevalleyLieAlgebra) = 1 ⊗ₜ[ℤ] y)
    (hd1 : (f4ShortRootSignedSimpleAdjoint k z : f4ModularChevalleyLieAlgebra) =
      1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), y⁆)
    (hd2 : (f4ShortRootDividedAdjointSquare k z : f4ModularChevalleyLieAlgebra) =
      1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k y) :
    f4RootExponential k t
        (f4ShortRootBaseChangeInclusion (A := A) ((1 : A) ⊗ₜ[ZMod 2] z)) =
      f4ShortRootBaseChangeInclusion (A := A)
        (f4ShortRootExponential (A := A) k t ((1 : A) ⊗ₜ[ZMod 2] z)) := by
  have hzA : f4ShortRootBaseChangeInclusion (A := A) ((1 : A) ⊗ₜ[ZMod 2] z) =
      (1 : A) ⊗ₜ[ℤ] y :=
    f4ShortRootBaseChangeInclusion_tmul_of_coe_eq (A := A) (1 : A) z y hz
  have hd1A : f4ShortRootBaseChangeInclusion (A := A)
      ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootSignedSimpleAdjoint k z) =
        (1 : A) ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), y⁆ :=
    f4ShortRootBaseChangeInclusion_tmul_of_coe_eq (A := A) (1 : A) _ _ hd1
  have hd2A : f4ShortRootBaseChangeInclusion (A := A)
      ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootDividedAdjointSquare k z) =
        (1 : A) ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k y :=
    f4ShortRootBaseChangeInclusion_tmul_of_coe_eq (A := A) (1 : A) _ _ hd2
  have hpoly := f4ShortRootExponential_apply (A := A) k t z
  let ι := f4ShortRootBaseChangeInclusion (A := A)
  let z₀ := (1 : A) ⊗ₜ[ZMod 2] z
  let z₁ := (1 : A) ⊗ₜ[ZMod 2] f4ShortRootSignedSimpleAdjoint k z
  let z₂ := (1 : A) ⊗ₜ[ZMod 2] f4ShortRootDividedAdjointSquare k z
  have hmap : ι (z₀ + t • z₁ + t ^ 2 • z₂) =
      ι z₀ + t • ι z₁ + t ^ 2 • ι z₂ := by
    simp only [map_add, map_smul]
  calc
    _ = f4RootExponential k t ((1 : A) ⊗ₜ[ℤ] y) :=
      congrArg (f4RootExponential k t) hzA
    _ = (1 : A) ⊗ₜ[ℤ] y +
        t • ((1 : A) ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), y⁆) +
        t ^ 2 • ((1 : A) ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k y) :=
      f4RootExponential_tmul k t y
    _ = _ := (congrArg ι hpoly).trans
      (hmap.trans
        (congrArg₂ (· + ·)
          (congrArg₂ (· + ·) hzA (congrArg (t • ·) hd1A))
          (congrArg (t ^ 2 • ·) hd2A))) |>.symm

private theorem f4RootExponential_intertwines_basis_of_coe_eq
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (b : Fin 26) (y : f4ChevalleyLieLattice)
    (hz : (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      1 ⊗ₜ[ℤ] y) :
    f4RootExponential k t
        (f4ShortRootBaseChangeInclusion (A := A)
          ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis b)) =
      f4ShortRootBaseChangeInclusion (A := A)
        (f4ShortRootExponential (A := A) k t
          ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis b)) := by
  have hd1 : (f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) :
      f4ModularChevalleyLieAlgebra) =
        1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), y⁆ := by
    calc
      _ = ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
            (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra)⁆ :=
        coe_f4ShortRootSignedSimpleAdjoint_apply k _
      _ = ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), 1 ⊗ₜ[ℤ] y⁆ :=
        congrArg (fun z => ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), z⁆) hz
      _ = _ := by
        rw [f4ModularRootVector_eq, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  have hd2 : (f4ShortRootDividedAdjointSquare k (f4ShortRootLieIdealBasis b) :
      f4ModularChevalleyLieAlgebra) =
        1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k y := by
    calc
      _ = f4ModularDividedAdjointSquare k
          (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) :=
        (f4ModularDividedAdjointSquare_basis k b).symm
      _ = f4ModularDividedAdjointSquare k (1 ⊗ₜ[ℤ] y) :=
        congrArg (f4ModularDividedAdjointSquare k) hz
      _ = _ := f4ModularDividedAdjointSquare_tmul k y
  exact f4RootExponential_intertwines_tmul_of_coe_eq k t
    (f4ShortRootLieIdealBasis b) y hz hd1 hd2

/-- The integral root exponential preserves the scalar-extended modular short-root ideal on every
canonical basis column, where its action is the base-changed sparse three-term polynomial. -/
theorem f4RootExponential_intertwines_basis {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A) (b : Fin 26) :
    f4RootExponential k t
        (f4ShortRootBaseChangeInclusion (A := A)
          ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis b)) =
      f4ShortRootBaseChangeInclusion (A := A)
        (f4ShortRootExponential (A := A) k t
          ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis b)) := by
  have hlift : ∃ y : f4ChevalleyLieLattice,
      (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) = 1 ⊗ₜ[ℤ] y := by
    obtain ⟨i | j, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective b
    · exact ⟨f4IntegralRootVector i,
        (coe_f4ShortRootLieIdealBasis_symm_inl i).trans (f4ModularRootVector_eq i)⟩
    · refine ⟨f4IntegralSimpleCoroot (f4ShortSimpleIndex j), ?_⟩
      exact (coe_f4ShortRootLieIdealBasis _).trans
        ((congrArg f4ModularChevalleyBasis (f4ShortRootBasisCoordinate_symm_inr j)).trans
          ((f4ModularSimpleCoroot_eq_basis _).symm.trans (f4ModularSimpleCoroot_eq _)))
  obtain ⟨y, hy⟩ := hlift
  exact f4RootExponential_intertwines_basis_of_coe_eq k t b y hy

/-- The scalar-extended modular short-root ideal is preserved by every signed-simple integral
root exponential, and the induced action is the sparse three-term polynomial. -/
theorem f4RootExponential_intertwines {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A)
    (x : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    f4RootExponential k t (f4ShortRootBaseChangeInclusion (A := A) x) =
      f4ShortRootBaseChangeInclusion (A := A) (f4ShortRootExponential k t x) := by
  have hmaps : (f4RootExponential k t).comp
        (f4ShortRootBaseChangeInclusion (A := A)) =
      (f4ShortRootBaseChangeInclusion (A := A)).comp (f4ShortRootExponential k t) := by
    apply (f4ShortRootLieIdealBasis.baseChange A).ext
    intro b
    simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply]
    exact f4RootExponential_intertwines_basis k t b
  exact LinearMap.congr_fun hmaps x

/-- The restricted root action at zero is the identity. -/
@[simp] theorem f4ShortRootExponential_zero {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootExponential (A := A) k 0 = 1 := by
  simp [f4ShortRootExponential]

/-- In the scalar-extended canonical basis, the modular root exponential is the existing sparse
root matrix plus its divided-square term. -/
theorem f4ShortRootExponential_toMatrix {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A) :
    LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A) (f4ShortRootExponential k t) =
      1 + t • (rootMatrix k).map (Int.cast : ℤ → A) +
        t ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → A) := by
  let B := f4ShortRootLieIdealBasis.baseChange A
  let T := LinearMap.toMatrixAlgEquiv B
  have hbase (f : Module.End (ZMod 2) f4ShortRootLieIdeal) :
      T (f.baseChange A) =
        (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis f).map
          (algebraMap (ZMod 2) A) := by
    -- Here `B` abbreviates the scalar-extended basis.
    change LinearMap.toMatrix B B (f.baseChange A) = _
    exact Module.Basis.toMatrix_baseChange_baseChange (S := A) f4ShortRootLieIdealBasis f
  -- This imported matrix is opaque, so compare entries using its public evaluation lemma.
  have hd1matrix : LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
      (f4ShortRootSignedSimpleAdjoint k) = f4ShortRootSignedSimpleAdjointMatrix k := by
    ext i j
    exact (LinearMap.toMatrix_apply _ _ _ _ _).trans
      (f4ShortRootSignedSimpleAdjointMatrix_apply k i j).symm
  -- Here `T` is the matrix algebra equivalence applied to the defining quadratic polynomial.
  change T (1 + t • (f4ShortRootSignedSimpleAdjoint k).baseChange A +
      t ^ 2 • (f4ShortRootDividedAdjointSquare k).baseChange A) = _
  simp only [map_add, map_smul, map_one, hbase, hd1matrix,
    f4ShortRootSignedSimpleAdjointMatrix_eq_rootMatrix_map,
    f4ShortRootDividedAdjointSquare_toMatrix, Matrix.map_map]
  simp only [Function.comp_def, map_intCast]

/-- The induced root exponential is exactly the existing carrier root-subgroup point. -/
theorem f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootExponential k (Multiplicative.toAdd u)) =
      ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  exact (f4ShortRootExponential_toMatrix k (Multiplicative.toAdd u)).trans
    (coe_rootSubgroupPoints_eq k A u).symm

/-- Restricted root actions compose by addition of their parameters. -/
theorem f4ShortRootExponential_add {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t u : A) :
    f4ShortRootExponential k (t + u) =
      f4ShortRootExponential k t * f4ShortRootExponential k u := by
  let B := f4ShortRootLieIdealBasis.baseChange A
  apply (LinearMap.toMatrixAlgEquiv B).injective
  calc
    LinearMap.toMatrix B B (f4ShortRootExponential k (t + u)) =
        ((rootSubgroupPoints k A (Multiplicative.ofAdd (t + u)) :
          Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
      simpa only [B, toAdd_ofAdd] using
        f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k
          (Multiplicative.ofAdd (t + u))
    _ = ((rootSubgroupPoints k A (Multiplicative.ofAdd t) :
          Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) *
        ((rootSubgroupPoints k A (Multiplicative.ofAdd u) :
          Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
      rw [ofAdd_add, map_mul]
      rfl
    _ = (LinearMap.toMatrixAlgEquiv B) (f4ShortRootExponential k t) *
        (LinearMap.toMatrixAlgEquiv B) (f4ShortRootExponential k u) := by
      exact congrArg₂ (· * ·)
        (f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k
          (Multiplicative.ofAdd t)).symm
        (f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k
          (Multiplicative.ofAdd u)).symm
    _ = _ := (map_mul (LinearMap.toMatrixAlgEquiv B) _ _).symm

/-- The action with opposite parameter is a left inverse. -/
@[simp] theorem f4ShortRootExponential_neg_mul {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A) :
    f4ShortRootExponential k (-t) * f4ShortRootExponential k t = 1 := by
  calc
    _ = f4ShortRootExponential k (-t + t) :=
      (f4ShortRootExponential_add k (-t) t).symm
    _ = 1 := by simpa only [neg_add_cancel] using f4ShortRootExponential_zero (A := A) k

/-- The action with opposite parameter is a right inverse. -/
@[simp] theorem f4ShortRootExponential_mul_neg {A : Type*} [CommRing A]
    [Algebra (ZMod 2) A] (k : Fin 4 ⊕ Fin 4) (t : A) :
    f4ShortRootExponential k t * f4ShortRootExponential k (-t) = 1 := by
  calc
    _ = f4ShortRootExponential k (t + -t) :=
      (f4ShortRootExponential_add k t (-t)).symm
    _ = 1 := by simpa only [add_neg_cancel] using f4ShortRootExponential_zero (A := A) k

/-- Conjugation by a signed-simple root exponential carries the scalar-extended adjoint action
to the adjoint action of the transformed ambient vector. -/
theorem f4ShortRootExponential_adjoint_intertwines
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A)
    (x : A ⊗[ℤ] f4ChevalleyLieLattice)
    (z : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    f4ShortRootExponential k t (f4ShortRootBaseChangeAdjoint x z) =
      f4ShortRootBaseChangeAdjoint (f4RootExponential k t x)
        (f4ShortRootExponential k t z) := by
  apply f4ShortRootBaseChangeInclusion_injective
  calc
    _ = f4RootExponential k t
        (f4ShortRootBaseChangeInclusion (A := A)
          (f4ShortRootBaseChangeAdjoint x z)) :=
      (f4RootExponential_intertwines k t _).symm
    _ = f4RootExponential k t
        ⁅x, f4ShortRootBaseChangeInclusion (A := A) z⁆ :=
      congrArg (f4RootExponential k t)
        (f4ShortRootBaseChangeInclusion_adjoint x z)
    _ = ⁅f4RootExponential k t x,
        f4RootExponential k t (f4ShortRootBaseChangeInclusion (A := A) z)⁆ := by
      calc
        _ = f4RootExponentialLieEquiv k t
            ⁅x, f4ShortRootBaseChangeInclusion (A := A) z⁆ :=
          (f4RootExponentialLieEquiv_apply k t _).symm
        _ = ⁅f4RootExponentialLieEquiv k t x,
            f4RootExponentialLieEquiv k t
              (f4ShortRootBaseChangeInclusion (A := A) z)⁆ :=
          (f4RootExponentialLieEquiv k t).map_lie _ _
        _ = _ := congrArg₂ (fun u v => ⁅u, v⁆)
          (f4RootExponentialLieEquiv_apply k t x)
          (f4RootExponentialLieEquiv_apply k t _)
    _ = ⁅f4RootExponential k t x,
        f4ShortRootBaseChangeInclusion (A := A) (f4ShortRootExponential k t z)⁆ :=
      congrArg (fun w => ⁅f4RootExponential k t x, w⁆)
        (f4RootExponential_intertwines k t z)
    _ = _ := (f4ShortRootBaseChangeInclusion_adjoint
      (f4RootExponential k t x) (f4ShortRootExponential k t z)).symm

/-- The pointwise adjoint intertwining identity as an equality in the endomorphism algebra. -/
theorem f4ShortRootExponential_mul_adjoint
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A)
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootExponential k t * f4ShortRootBaseChangeAdjoint x =
      f4ShortRootBaseChangeAdjoint (f4RootExponential k t x) *
        f4ShortRootExponential k t := by
  apply LinearMap.ext
  intro z
  -- Multiplication of endomorphisms evaluates as composition at `z`.
  change f4ShortRootExponential k t (f4ShortRootBaseChangeAdjoint x z) =
    f4ShortRootBaseChangeAdjoint (f4RootExponential k t x)
      (f4ShortRootExponential k t z)
  exact f4ShortRootExponential_adjoint_intertwines k t x z

/-- In the canonical matrix coordinates, left multiplication by a root exponential intertwines
the represented adjoint operator with the operator of the transformed ambient vector. -/
theorem f4ShortRootExponential_toMatrix_mul_adjoint
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A)
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    let B := f4ShortRootLieIdealBasis.baseChange A
    LinearMap.toMatrix B B (f4ShortRootExponential k t) *
        LinearMap.toMatrix B B (f4ShortRootBaseChangeAdjoint x) =
      LinearMap.toMatrix B B
          (f4ShortRootBaseChangeAdjoint
            (f4RootExponential k t x)) *
        LinearMap.toMatrix B B (f4ShortRootExponential k t) := by
  let B := f4ShortRootLieIdealBasis.baseChange A
  let T := LinearMap.toMatrixAlgEquiv B
  calc
    T (f4ShortRootExponential k t) * T (f4ShortRootBaseChangeAdjoint x) =
        T (f4ShortRootExponential k t * f4ShortRootBaseChangeAdjoint x) :=
      (T.map_mul _ _).symm
    _ = T (f4ShortRootBaseChangeAdjoint (f4RootExponential k t x) *
        f4ShortRootExponential k t) := congrArg T
      (f4ShortRootExponential_mul_adjoint k t x)
    _ = T (f4ShortRootBaseChangeAdjoint (f4RootExponential k t x)) *
        T (f4ShortRootExponential k t) := T.map_mul _ _

end

end TauCeti.DynkinType
