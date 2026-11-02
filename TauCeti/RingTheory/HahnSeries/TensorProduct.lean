/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Scalar extension and module-valued Hahn series

The canonical map `R⟦Γ⟧ ⊗[R] V → HahnModule Γ R V` sends `f ⊗ v` to the series with
coefficients `f.coeff g • v`, or equivalently to `f` times the constant series `v`.
For a finite free coefficient module this is an isomorphism over `R⟦Γ⟧`: expansion in any
finite basis of `V` writes a module-valued series as a finite sum of scalar series times
constant basis vectors. The map itself is independent of that basis.

In particular, for a finite-dimensional vector space `V` over a field `K`, this identifies
`K((t)) ⊗[K] V` with `V((t))` on Mathlib's `HahnModule ℤ K V` carrier, with its convolution
action of scalar Laurent series. This supplies the scalar-extension interpretation of
module-valued Laurent series used in residue duality.
-/

public section

noncomputable section

open TensorProduct HahnSeries

namespace HahnModule

variable {Γ R V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

variable [CommSemiring R] [AddCommMonoid V] [Module R V]

variable (R Γ V) in
/-- The canonical scalar-extension map to module-valued Hahn series, sending `f ⊗ v` to
`f` times the constant series `v`. -/
def tensorProductToHahnModule :
    HahnSeries Γ R ⊗[R] V →ₗ[HahnSeries Γ R] HahnModule Γ R V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun f ↦
        { toFun := fun v ↦ f • of R (single 0 v)
          map_add' := fun v w ↦ by rw [single_add, of_add, smul_add]
          map_smul' := fun r v ↦ by
            apply HahnModule.ext
            funext g
            simp only [coeff_smul_single_zero, RingHom.id_apply, of_symm_smul',
              HahnSeries.coeff_smul]
            exact (smul_comm r (f.coeff g) v).symm }
      map_add' := fun f h ↦
        LinearMap.ext fun v ↦ _root_.add_smul f h (of R (single 0 v))
      map_smul' := fun f h ↦ LinearMap.ext fun v ↦ mul_smul f h (of R (single 0 v)) }

/-- The scalar-extension map on a pure tensor is multiplication by a constant series. -/
@[simp]
theorem tensorProductToHahnModule_tmul (f : HahnSeries Γ R) (v : V) :
    tensorProductToHahnModule Γ R V (f ⊗ₜ[R] v) = f • of R (single 0 v) :=
  (rfl)

/-- Scalar extension commutes with linear maps on the coefficient module, coefficient by
coefficient. No finiteness assumption is needed for this naturality identity. -/
theorem coeff_tensorProductToHahnModule_map {W : Type*} [AddCommMonoid W] [Module R W]
    (ℓ : V →ₗ[R] W) (z : HahnSeries Γ R ⊗[R] V) (g : Γ) :
    ((of R).symm (tensorProductToHahnModule Γ R W
      (TensorProduct.map (.id : HahnSeries Γ R →ₗ[R] _) ℓ z))).coeff g =
      ℓ (((of R).symm (tensorProductToHahnModule Γ R V z)).coeff g) := by
  induction z using TensorProduct.inductionOn with
  | tmul f v => simp
  | add z w hz hw => simp [hz, hw]

/-- A finite basis expands a module-valued Hahn series into scalar coordinate series times
constant basis vectors. -/
theorem sum_map_coord_smul_single {ι : Type*} [Fintype ι] (b : Module.Basis ι R V)
    (x : HahnModule Γ R V) :
    ∑ i, ((of R).symm x).map (b.coord i) • of R (single 0 (b i)) = x := by
  apply HahnModule.ext
  funext g
  -- Use the bundled linear equivalence so `map_sum` distributes the inverse of `of`.
  rw [← ofLinearEquiv_symm_apply]
  simp only [map_sum, ofLinearEquiv_symm_apply, coeff_sum, coeff_smul_single_zero, map_coeff,
    Module.Basis.coord_apply]
  exact b.sum_repr _

/-- The scalar-extension map is bijective whenever the coefficient module has a finite basis. -/
theorem tensorProductToHahnModule_bijective_of_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι R V) : Function.Bijective (tensorProductToHahnModule Γ R V) := by
  classical
  let := Fintype.ofFinite ι
  let inv : HahnModule Γ R V →+ HahnSeries Γ R ⊗[R] V :=
    ∑ i, { toFun := fun x ↦ ((of R).symm x).map (b.coord i) ⊗ₜ[R] b i
           map_zero' := by
             rw [of_symm_zero, show (0 : HahnSeries Γ V).map (b.coord i) = 0 by ext; simp,
               zero_tmul]
           map_add' := fun x y ↦ by
             rw [of_symm_add, ← add_tmul]
             congr 1
             exact HahnSeries.map_add (b.coord i).toAddMonoidHom }
  have right : Function.RightInverse inv (tensorProductToHahnModule Γ R V) := by
    intro x
    simp only [inv, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      map_sum, tensorProductToHahnModule_tmul]
    exact sum_map_coord_smul_single b x
  have left : Function.LeftInverse inv (tensorProductToHahnModule Γ R V) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul f v =>
      have hc (i : ι) :
          ((of R).symm (tensorProductToHahnModule Γ R V (f ⊗ₜ[R] v))).map (b.coord i) =
            b.repr v i • f := by
        ext g
        simp [smul_eq_mul, mul_comm]
      simp only [inv, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hc,
        smul_tmul, ← tmul_sum, b.sum_repr]
    | add z w hz hw => simp only [map_add, hz, hw]
  exact ⟨left.injective, right.surjective⟩

variable (R Γ V) in
/-- Finite free coefficient modules commute with scalar extension to Hahn series. In
particular this is `K((t)) ⊗[K] V ≃ V((t))` for finite-dimensional `V`. -/
def tensorProductEquiv [Module.Free R V] [Module.Finite R V] :
    HahnSeries Γ R ⊗[R] V ≃ₗ[HahnSeries Γ R] HahnModule Γ R V :=
  LinearEquiv.ofBijective (tensorProductToHahnModule Γ R V)
    (tensorProductToHahnModule_bijective_of_basis (Module.Free.chooseBasis R V))

/-- The equivalence has the canonical scalar-extension map as its forward map. -/
@[simp]
theorem tensorProductEquiv_apply [Module.Free R V] [Module.Finite R V]
    (z : HahnSeries Γ R ⊗[R] V) :
    tensorProductEquiv Γ R V z = tensorProductToHahnModule Γ R V z :=
  (rfl)

/-- In any finite basis, the inverse comparison is the sum of the scalar coordinate series
tensored with the corresponding basis vectors. -/
theorem tensorProductEquiv_symm_apply [Module.Free R V] [Module.Finite R V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R V) (x : HahnModule Γ R V) :
    (tensorProductEquiv Γ R V).symm x =
      ∑ i, ((of R).symm x).map (b.coord i) ⊗ₜ[R] b i := by
  apply (tensorProductEquiv Γ R V).injective
  rw [LinearEquiv.apply_symm_apply, tensorProductEquiv_apply, map_sum]
  simp only [tensorProductToHahnModule_tmul]
  exact (sum_map_coord_smul_single b x).symm

/-- The inverse comparison sends a vector-valued monomial to a pure tensor. -/
@[simp]
theorem tensorProductEquiv_symm_single [Module.Free R V] [Module.Finite R V]
    (g : Γ) (v : V) :
    (tensorProductEquiv Γ R V).symm (of R (single g v)) = single g 1 ⊗ₜ[R] v := by
  apply (tensorProductEquiv Γ R V).injective
  simp

end HahnModule
