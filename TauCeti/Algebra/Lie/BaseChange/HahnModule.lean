/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Basic
public import TauCeti.Algebra.Lie.Loop.HahnModule
public import TauCeti.RingTheory.HahnSeries.TensorProduct

/-!
# Scalar extension of a Lie algebra to Hahn series

For a Lie algebra `L` over a commutative ring `R`, the scalar extension
`HahnSeries Γ R ⊗[R] L` carries Mathlib's scalar-extension bracket
`⁅f ⊗ x, g ⊗ y⁆ = f g ⊗ ⁅x, y⁆`, while the `L`-valued Hahn series `HahnModule Γ R L` carry the
coefficient convolution bracket. The canonical comparison map, sending `f ⊗ x` to `f` times the
constant series `x`, intertwines the two brackets, so it is a morphism of Lie algebras over
`HahnSeries Γ R`. When `L` is finite free over `R` it is bijective, hence a Lie algebra
equivalence over `HahnSeries Γ R`.

For `Γ = ℤ` and a finite-dimensional Lie algebra `L` over a field `K`, this identifies the formal
currents `K((t)) ⊗[K] L` (`TauCeti.currentAlgebra K L`) with the formal loop algebra `L((t))`
as Lie algebras over `K((t))`. The comparison preserves coefficients, and it restricts to the
embedding `LieAlgebra.LoopAlgebra.toHahnModule` of polynomial loops `L[t, t⁻¹]`.

## Main definitions and results

* `HahnModule.tensorProductLieHom`: the comparison map preserves brackets, so it is a morphism
  of Lie algebras over `HahnSeries Γ R`, for an arbitrary coefficient Lie algebra.
* `HahnModule.tensorProductLieEquiv`: for finite free `L`, the Lie algebra equivalence
  `HahnSeries Γ R ⊗[R] L ≃ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L`.
* `HahnModule.coeff_tensorProductToHahnModule`: on formal currents, the comparison preserves
  coefficients.
* `HahnModule.tensorProductToHahnModule_ofLoop`: on polynomial loops, the comparison is
  `LieAlgebra.LoopAlgebra.toHahnModule`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

noncomputable section

open TensorProduct HahnSeries

namespace HahnModule

variable {Γ R L : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [LieRing L] [LieAlgebra R L]

variable (Γ R L) in
/-- The scalar-extension map to Lie-valued Hahn series, as a morphism of Lie algebras over
`HahnSeries Γ R`. It sends `f ⊗ x` to `f` times the constant series `x`, and intertwines the
scalar-extension bracket with the coefficient convolution bracket. -/
def tensorProductLieHom : HahnSeries Γ R ⊗[R] L →ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L where
  __ := tensorProductToHahnModule Γ R L
  map_lie' {z w} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp [hz, hz']
    | tmul f x =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp [hw, hw']
      | tmul g y => simp [single_lie_single, mul_smul, smul_comm f g]

/-- The Lie algebra morphism is the scalar-extension map. -/
@[simp]
theorem tensorProductLieHom_apply (z : HahnSeries Γ R ⊗[R] L) :
    tensorProductLieHom Γ R L z = tensorProductToHahnModule Γ R L z :=
  (rfl)

/-- The underlying linear map of the Lie algebra morphism is the scalar-extension map. -/
@[simp]
theorem toLinearMap_tensorProductLieHom :
    (tensorProductLieHom Γ R L : HahnSeries Γ R ⊗[R] L →ₗ[HahnSeries Γ R] HahnModule Γ R L) =
      tensorProductToHahnModule Γ R L :=
  (rfl)

variable (Γ R L) in
/-- For a finite free Lie algebra `L` over `R`, the scalar extension `HahnSeries Γ R ⊗[R] L`
and the `L`-valued Hahn series are isomorphic as Lie algebras over `HahnSeries Γ R`. For a
finite-dimensional Lie algebra over a field `K`, this is `K((t)) ⊗[K] L ≃ L((t))`. -/
def tensorProductLieEquiv [Module.Free R L] [Module.Finite R L] :
    HahnSeries Γ R ⊗[R] L ≃ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L :=
  LieEquiv.ofBijective (tensorProductLieHom Γ R L)
    (tensorProductToHahnModule_bijective_of_basis (Module.Free.chooseBasis R L))

/-- The Lie algebra equivalence is the scalar-extension map. -/
@[simp]
theorem tensorProductLieEquiv_apply [Module.Free R L] [Module.Finite R L]
    (z : HahnSeries Γ R ⊗[R] L) :
    tensorProductLieEquiv Γ R L z = tensorProductToHahnModule Γ R L z :=
  (rfl)

/-- The underlying linear equivalence of the Lie algebra equivalence is
`HahnModule.tensorProductEquiv`. -/
@[simp]
theorem toLinearEquiv_tensorProductLieEquiv [Module.Free R L] [Module.Finite R L] :
    (tensorProductLieEquiv Γ R L).toLinearEquiv = tensorProductEquiv Γ R L :=
  LinearEquiv.ext fun z ↦ by
    rw [LieEquiv.coe_toLinearEquiv, tensorProductLieEquiv_apply, tensorProductEquiv_apply]

/-- The inverse Lie algebra equivalence is the inverse of `HahnModule.tensorProductEquiv`. -/
@[simp]
theorem tensorProductLieEquiv_symm_apply [Module.Free R L] [Module.Finite R L]
    (x : HahnModule Γ R L) :
    (tensorProductLieEquiv Γ R L).symm x = (tensorProductEquiv Γ R L).symm x := by
  rw [LieEquiv.symm_apply_eq, tensorProductLieEquiv_apply, ← tensorProductEquiv_apply,
    LinearEquiv.apply_symm_apply]

/-! ### Formal currents and polynomial loops -/

section Current

open scoped LaurentSeries

-- Match the coefficientwise scalar action used to define formal currents.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- On formal currents, the comparison with module-valued Laurent series preserves
coefficients. -/
@[simp]
theorem coeff_tensorProductToHahnModule {V : Type*} [AddCommGroup V] [Module R V]
    (u : TauCeti.currentAlgebra R V) (n : ℤ) :
    ((of R).symm (tensorProductToHahnModule ℤ R V u)).coeff n =
      TauCeti.CurrentAlgebra.coeff R V n u := by
  induction u using TensorProduct.inductionOn with
  | tmul f x => simp
  | add u v hu hv => simp only [map_add, of_symm_add, HahnSeries.coeff_add, hu, hv]

/-- On polynomial loops, the comparison of formal currents with `L`-valued Laurent series is the
embedding `LieAlgebra.LoopAlgebra.toHahnModule`. -/
@[simp]
theorem tensorProductToHahnModule_ofLoop (p : LieAlgebra.loopAlgebra R ℤ L) :
    tensorProductToHahnModule ℤ R L (TauCeti.CurrentAlgebra.ofLoop R L p) =
      LieAlgebra.LoopAlgebra.toHahnModule R ℤ L p := by
  ext n
  rw [coeff_tensorProductToHahnModule, TauCeti.CurrentAlgebra.coeff_ofLoop,
    LieAlgebra.LoopAlgebra.coeff_toHahnModule]

end Current

end HahnModule
