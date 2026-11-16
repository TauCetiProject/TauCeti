/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Naturality and heterobasic duality of tensor products

The canonical map `E* ⊗ F* → (E ⊗ F)*` commutes with precomposition in both variables.
In particular it transports the tensor product of transposed endomorphisms to the transpose
of their tensor product. This applies to grading operators as well as algebra actions.
For finite projective modules the map is Mathlib's equivalence `TensorProduct.dualDistribEquiv`.

Over an `R`-algebra `S`, this file also shows that Mathlib's heterobasic duality map
`TensorProduct.AlgebraTensorModule.dualDistrib R S M N` is an `S`-linear equivalence
`Dual S M ⊗[R] Dual R N ≃ₗ[S] Dual S (M ⊗[R] N)` whenever `M` is finite projective over `S`
and `N` is finite projective over `R`.
-/

public section

namespace LinearMap

open Module TensorProduct

variable {R E F E' F' : Type*} [CommSemiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [AddCommMonoid E'] [Module R E'] [AddCommMonoid F'] [Module R F']

/-- Tensor duality is contravariantly natural in both module variables. No finiteness or
projectivity is needed for the canonical map to intertwine precomposition. -/
theorem dualDistrib_comp_map_dualMap (f : E →ₗ[R] E') (g : F →ₗ[R] F') :
    dualDistrib R E F ∘ₗ map f.dualMap g.dualMap =
      (map f g).dualMap ∘ₗ dualDistrib R E' F' := by
  ext φ ψ e w
  simp

end LinearMap

namespace TauCeti.TensorProduct.AlgebraTensorModule

open Module _root_.TensorProduct

variable (R S M N : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N]
  [Module.Finite S M] [Module.Projective S M] [Module.Finite R N] [Module.Projective R N]

/-- For a finite projective `S`-module `M` and a finite projective `R`-module `N`, the heterobasic
duality map `TensorProduct.AlgebraTensorModule.dualDistrib R S M N` is bijective. -/
theorem dualDistrib_bijective :
    Function.Bijective (_root_.TensorProduct.AlgebraTensorModule.dualDistrib R S M N) := by
  let f : S ⊗[R] Dual R N →ₗ[S] Dual S (S ⊗[R] N) :=
    _root_.TensorProduct.AlgebraTensorModule.dualDistrib R S S N ∘ₗ
      _root_.TensorProduct.AlgebraTensorModule.map
        (LinearMap.ringLmapEquivSelf S S S).symm.toLinearMap LinearMap.id
  have hf_bij : Function.Bijective f := by
    let e₀ : S ⊗[R] Dual R N ≃ₗ[R] Dual S (S ⊗[R] N) :=
      (_root_.TensorProduct.comm R S (Dual R N)) ≪≫ₗ
        (dualTensorHomEquiv R N S) ≪≫ₗ
        ((LinearMap.liftBaseChangeEquiv S).restrictScalars R)
    have hfe₀ : ⇑f = ⇑e₀ := by
      refine funext fun w ↦ ?_
      induction w using _root_.TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s g =>
        refine _root_.TensorProduct.AlgebraTensorModule.ext fun t n ↦ ?_
        simp [f, e₀, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    rw [hfe₀]
    exact e₀.bijective
  let baseChangeDualEquiv : S ⊗[R] Dual R N ≃ₗ[S] Dual S (S ⊗[R] N) :=
    LinearEquiv.ofBijective f hf_bij
  let e : Dual S M ⊗[R] Dual R N ≃ₗ[S] Dual S (M ⊗[R] N) :=
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Dual S M) (Dual R N)).symm ≪≫ₗ
      (_root_.TensorProduct.congr (LinearEquiv.refl S (Dual S M)) baseChangeDualEquiv) ≪≫ₗ
      (_root_.TensorProduct.dualDistribEquiv S M (S ⊗[R] N)) ≪≫ₗ
      (Module.Dual.congr (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N))
  have hfe : ⇑(_root_.TensorProduct.AlgebraTensorModule.dualDistrib R S M N) = ⇑e := by
    refine funext fun w ↦ ?_
    induction w using _root_.TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ ψ =>
      refine _root_.TensorProduct.AlgebraTensorModule.ext fun m n ↦ ?_
      simp [e, baseChangeDualEquiv, f, Algebra.smul_def, mul_comm]
  rw [hfe]
  exact e.bijective

/-- The heterobasic tensor-dual map `Dual S M ⊗[R] Dual R N → Dual S (M ⊗[R] N)` as an `S`-linear
equivalence for finite projective modules `M` over `S` and `N` over `R`. -/
noncomputable def dualDistribEquiv :
    Dual S M ⊗[R] Dual R N ≃ₗ[S] Dual S (M ⊗[R] N) :=
  LinearEquiv.ofBijective
    (_root_.TensorProduct.AlgebraTensorModule.dualDistrib R S M N)
    (dualDistrib_bijective R S M N)

/-- The underlying `S`-linear map of `dualDistribEquiv` is `AlgebraTensorModule.dualDistrib`. -/
@[simp]
theorem toLinearMap_dualDistribEquiv :
    (dualDistribEquiv R S M N).toLinearMap =
      _root_.TensorProduct.AlgebraTensorModule.dualDistrib R S M N := by
  ext
  simp [dualDistribEquiv]

/-- Applying `dualDistribEquiv` agrees with `AlgebraTensorModule.dualDistrib`. -/
@[simp]
theorem dualDistribEquiv_apply (w : Dual S M ⊗[R] Dual R N) :
    dualDistribEquiv R S M N w =
      _root_.TensorProduct.AlgebraTensorModule.dualDistrib R S M N w := by
  simp [dualDistribEquiv]

end TauCeti.TensorProduct.AlgebraTensorModule
