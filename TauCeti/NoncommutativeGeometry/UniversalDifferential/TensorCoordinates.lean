/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.OneForms

/-!
# Tensor coordinates for universal one-forms

Universal one-forms of a possibly nonunital algebra `A` identify with `A⁺ ⊗[k] A`, where
`A⁺ = Unitization k A` is the forced unitization, even if `A` already has a unit.
The equivalence `UniversalOneForms.tensorEquiv` sends `x • d a` to `x ⊗ a`; its inverse
sends `x ⊗ a` to `x • d a`.

These coordinates give the tensor-word model used to construct higher universal forms.
Left multiplication acts on the first tensor factor, whereas right multiplication obeys the
Leibniz relation `x (d a) b = x d(ab) - (xa) d b`. In particular the right action is not the
naive action on the last tensor factor. An induction principle expresses that every one-form
is a finite sum of terms `x • d a`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, universal differential forms.
-/

public section

open MulOpposite TensorProduct
open scoped TensorProduct

namespace TauCeti.UniversalOneForms

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

private def fromTensor : Unitization k A ⊗[k] A →ₗ[k] UniversalOneForms k A :=
  TensorProduct.lift ((Algebra.lsmul k k (UniversalOneForms k A)).toLinearMap.compl₂ (d k A))

@[simp]
private theorem fromTensor_tmul (x : Unitization k A) (a : A) :
    fromTensor k A (x ⊗ₜ[k] a) = x • d k A a := rfl

private def toTensor : UniversalOneForms k A →ₗ[k] Unitization k A ⊗[k] A :=
  ((Unitization.sndHom k k A).lTensor (Unitization k A)).comp (UniversalOneForms k A).subtype

private theorem fromTensor_snd (t : Unitization k A ⊗[k] Unitization k A) :
    fromTensor k A ((Unitization.sndHom k k A).lTensor (Unitization k A) t) =
      tensorLift k A (derivation k A) t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, Unitization.sndHom_apply, fromTensor_tmul, d_snd,
      tensorLift_tmul]
  | add t s ht hs =>
    simp only [map_add, ht, hs]

private theorem fromTensor_toTensor (ω : UniversalOneForms k A) :
    fromTensor k A (toTensor k A ω) = ω := by
  rw [toTensor, LinearMap.comp_apply, Submodule.subtype_apply, fromTensor_snd,
    tensorLift_derivation_coe]

private theorem toTensor_fromTensor (t : Unitization k A ⊗[k] A) :
    toTensor k A (fromTensor k A t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul x a => simp [toTensor, coe_smul_left]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Tensor coordinates on universal one-forms: `x • d a` corresponds to `x ⊗ a`.
The tensor factor `A` is the original algebra, not its forced unitization. -/
def tensorEquiv : UniversalOneForms k A ≃ₗ[k] Unitization k A ⊗[k] A :=
  { toTensor k A with
    invFun := fromTensor k A
    left_inv := fromTensor_toTensor k A
    right_inv := toTensor_fromTensor k A }

/-- The coordinate map is the restriction of the second-factor projection onto `A`. -/
theorem tensorEquiv_apply (ω : UniversalOneForms k A) :
    tensorEquiv k A ω =
      (Unitization.sndHom k k A).lTensor (Unitization k A) ω.1 := (rfl)

/-- A pure tensor corresponds to the one-form `x • d a`. -/
@[simp]
theorem tensorEquiv_symm_tmul (x : Unitization k A) (a : A) :
    (tensorEquiv k A).symm (x ⊗ₜ[k] a) = x • d k A a := (rfl)

/-- The tensor coordinates of `x • d a`. -/
-- Simplify before `d_apply` expands the differential to the unitization derivation.
@[simp↓]
theorem tensorEquiv_smul_d (x : Unitization k A) (a : A) :
    tensorEquiv k A (x • d k A a) = x ⊗ₜ[k] a := by
  simpa only [tensorEquiv_symm_tmul] using (tensorEquiv k A).apply_symm_apply (x ⊗ₜ[k] a)

/-- In tensor coordinates the universal differential is `a ↦ 1 ⊗ a`. -/
@[simp↓]
theorem tensorEquiv_d (a : A) :
    tensorEquiv k A (d k A a) = 1 ⊗ₜ[k] a := by
  simpa only [one_smul] using tensorEquiv_smul_d k A 1 a

/-- Every universal one-form is a finite sum of terms `x • d a`. -/
@[elab_as_elim]
theorem induction_on {P : UniversalOneForms k A → Prop} (ω : UniversalOneForms k A)
    (h : ∀ (x : Unitization k A) (a : A), P (x • d k A a))
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) : P ω := by
  rw [← (tensorEquiv k A).symm_apply_apply ω]
  induction tensorEquiv k A ω using TensorProduct.inductionOn with
  | tmul x a => simpa only [tensorEquiv_symm_tmul] using h x a
  | add t s ht hs => simpa only [map_add] using hadd _ _ ht hs

/-- Left multiplication of a one-form acts on the first tensor factor. -/
theorem tensorEquiv_smul_left (x : Unitization k A) (ω : UniversalOneForms k A) :
    tensorEquiv k A (x • ω) =
      (LinearMap.mulLeft k x).rTensor A (tensorEquiv k A ω) := by
  induction ω using induction_on k A with
  | h y a => simp only [smul_smul, tensorEquiv_smul_d, LinearMap.rTensor_tmul,
      LinearMap.mulLeft_apply]
  | hadd ω η hω hη => simp only [smul_add, map_add, hω, hη]

/-- Right multiplication on a tensor word, including scalar components of the multiplier. -/
theorem tensorEquiv_smul_right_smul_d (x : Unitization k A) (a : A)
    (y : Unitization k A) :
    tensorEquiv k A (op y • (x • d k A a)) =
      x ⊗ₜ[k] ((a : Unitization k A) * y).snd -
        (x * (a : Unitization k A)) ⊗ₜ[k] y.snd := by
  rw [smul_right_smul_d, _root_.map_sub (tensorEquiv k A), tensorEquiv_smul_d,
    tensorEquiv_smul_d]

end TauCeti.UniversalOneForms
