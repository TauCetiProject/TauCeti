/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.ShiftClosure.Basic
public import TauCeti.CategoryTheory.DG.SingleObj

/-!
# The shift closure of the one-object differential graded category of an algebra

For a differential graded algebra `(A, d)`, the shift closure of its one-object differential
graded category `TauCeti.DGSingleObj h` has the objects `⋆[r]`, and a morphism `⋆[r] ⟶ ⋆[s]` of
degree `n` is an element of `A` of degree `n + s - r`.  This file names that element,
`TauCeti.DGSingleObj.shiftCoeff`, and computes the differential and composition of the shift
closure on it: the differential is `(-1)^(s - r) d`, and composition is multiplication in the
reversed order with the product of the shift-closure sign and the Koszul sign of the one-object
category.

These formulas turn statements about matrices of morphisms between shifted copies of `⋆`, such as
the twisting matrices of one-sided twisted complexes over `A`, into identities in `A`.

## Main definitions

* `TauCeti.DGSingleObj.shiftCoeff`: the element of `A` underlying a morphism `⋆[r] ⟶ ⋆[s]`.

## Main results

* `TauCeti.DGSingleObj.shiftCoeff_injective`: a morphism is determined by its underlying element.
* `TauCeti.DGSingleObj.shiftCoeff_dgDifferential`: the differential is `(-1)^(s - r) d`.
* `TauCeti.DGSingleObj.shiftCoeff_dgComp`: composition is signed multiplication in the reversed
  order.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DGSingleObj

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-- The element of `A` underlying a morphism `⋆[r] ⟶ ⋆[s]` of degree `n` of the shift closure of
the one-object differential graded category: it has degree `n + s - r`. -/
noncomputable def shiftCoeff {X Y : DGShiftClosure (DGSingleObj h)} {n : ℤ} :
    DGHom R n X Y →ₗ[R] A :=
  (𝒜 _).subtype ∘ₗ (dgHomEquiv X.obj Y.obj _).toLinearMap ∘ₗ
    (DGShiftClosure.dgHomEquiv R X Y n).toLinearMap

theorem shiftCoeff_apply {X Y : DGShiftClosure (DGSingleObj h)} {n : ℤ} (f : DGHom R n X Y) :
    shiftCoeff f = (dgHomEquiv X.obj Y.obj _ (DGShiftClosure.dgHomEquiv R X Y n f) : A) :=
  (rfl)

/-- The underlying element of a morphism `⋆[r] ⟶ ⋆[s]` of degree `n` has degree `n + s - r`. -/
theorem shiftCoeff_mem {X Y : DGShiftClosure (DGSingleObj h)} {n : ℤ} (f : DGHom R n X Y) :
    shiftCoeff f ∈ 𝒜 (n + (Y.shift - X.shift)) :=
  (dgHomEquiv X.obj Y.obj _ (DGShiftClosure.dgHomEquiv R X Y n f)).2

/-- A morphism of the shift closure is determined by its underlying element. -/
theorem shiftCoeff_injective {X Y : DGShiftClosure (DGSingleObj h)} {n : ℤ} :
    Function.Injective (shiftCoeff (X := X) (Y := Y) (n := n)) := fun _ _ hfg ↦
  (DGShiftClosure.dgHomEquiv R X Y n).injective <|
    (dgHomEquiv X.obj Y.obj _).injective <| Subtype.ext hfg

/-- The **differential of the shift closure** on underlying elements: for `f : ⋆[r] ⟶ ⋆[s]`, it
is `(-1)^(s - r) d`. -/
@[simp↓]
theorem shiftCoeff_dgDifferential {X Y : DGShiftClosure (DGSingleObj h)} (n : ℤ)
    (f : DGHom R n X Y) :
    shiftCoeff (dgDifferential R n f) = (Y.shift - X.shift).negOnePow • d (shiftCoeff f) := by
  rw [shiftCoeff_apply, shiftCoeff_apply, DGShiftClosure.dgHomEquiv_dgDifferential,
    map_zsmul_unit, Units.smul_def, Units.smul_def, Submodule.coe_smul_of_tower,
    dgHomEquiv_dgHomComplex_d (by ring)]

/-- **Composition in the shift closure** on underlying elements: a degree-`p` morphism
`f : ⋆[r] ⟶ ⋆[s]` followed by `g : ⋆[s] ⟶ ⋆[t]` of degree `q` is `g * f`, with the sign
`(-1)^((t - s) * (p + s - r))` of the shift closure and the Koszul sign of the one-object category
for the degrees `p + s - r` and `q + t - s` of the underlying elements. -/
@[simp↓]
theorem shiftCoeff_dgComp {X Y Z : DGShiftClosure (DGSingleObj h)} {p q n : ℤ}
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (hpq : p + q = n) :
    shiftCoeff (dgComp R f g hpq) =
      ((Z.shift - Y.shift) * (p + (Y.shift - X.shift))).negOnePow •
        ((p + (Y.shift - X.shift)) * (q + (Z.shift - Y.shift))).negOnePow •
          (shiftCoeff g * shiftCoeff f) := by
  rw [shiftCoeff_apply, shiftCoeff_apply, shiftCoeff_apply, DGShiftClosure.dgHomEquiv_dgComp,
    map_zsmul_unit, Units.smul_def, Submodule.coe_smul_of_tower, dgHomEquiv_dgComp,
    ← Units.smul_def]

end DGSingleObj

end TauCeti
