/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.NoncommutativeGeometry.UniversalDifferential.TensorCoordinates

/-!
# Functoriality of universal one-forms

A nonunital algebra homomorphism `f : A →ₙₐ[k] B` induces a linear map on universal
one-forms, sending `x • d a` to `Unitization.map f x • d (f a)`. This map commutes with
the universal differential and intertwines both outer actions along the induced homomorphism
of forced unitizations. In tensor coordinates it is the tensor product of `Unitization.map f`
and `f`; in the multiplication-kernel model it applies `Unitization.map f` to both factors.

Identity and composition laws make these the degree-one maps used when transporting
universal differential-form words along algebra homomorphisms. The forced unitization is
retained even for unital algebras, and `f` need not preserve an existing unit.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, universal differential forms.
-/

public section

open MulOpposite TensorProduct
open scoped TensorProduct

namespace TauCeti.UniversalOneForms

universe u v w z

variable (k : Type u) {A : Type v} {B : Type w} {C : Type z} [CommRing k]
  [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  [NonUnitalRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]

noncomputable section

/-- The map on universal one-forms induced by a nonunital algebra homomorphism. -/
def map (f : A →ₙₐ[k] B) : UniversalOneForms k A →ₗ[k] UniversalOneForms k B :=
  (tensorEquiv k B).symm.toLinearMap ∘ₗ
    TensorProduct.map (Unitization.map f).toLinearMap (LinearMap.ofClass f) ∘ₗ
      (tensorEquiv k A).toLinearMap

/-- In tensor coordinates the map on one-forms applies the induced unitization map to the
first factor and the original homomorphism to the second. -/
@[simp]
theorem tensorEquiv_map (f : A →ₙₐ[k] B) (ω : UniversalOneForms k A) :
    tensorEquiv k B (map k f ω) =
      TensorProduct.map (Unitization.map f).toLinearMap (LinearMap.ofClass f)
        (tensorEquiv k A ω) := by
  simp [map]

/-- The induced map sends the word `x • d a` to `f⁺ x • d (f a)`. -/
private theorem map_smul_d (f : A →ₙₐ[k] B) (x : Unitization k A) (a : A) :
    map k f (x • d k A a) = Unitization.map f x • d k B (f a) := by
  apply (tensorEquiv k B).injective
  rw [tensorEquiv_map, tensorEquiv_smul_d, tensorEquiv_smul_d]
  simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.coe_ofClass]

/-- The universal differential is natural for nonunital algebra homomorphisms. -/
@[simp↓]
theorem map_d (f : A →ₙₐ[k] B) (a : A) : map k f (d k A a) = d k B (f a) := by
  simpa only [map_one, one_smul] using map_smul_d k f 1 a

/-- The universal derivation of the forced unitization is natural as well. -/
@[simp]
theorem map_derivation (f : A →ₙₐ[k] B) (x : Unitization k A) :
    map k f ((derivation k A) x) = (derivation k B) (Unitization.map f x) := by
  rw [← d_snd, map_d, ← d_snd, Unitization.snd_map]

/-- The induced map intertwines the left outer actions along the unitization map. -/
@[simp↓]
theorem map_smul_left (f : A →ₙₐ[k] B) (x : Unitization k A)
    (ω : UniversalOneForms k A) :
    map k f (x • ω) = Unitization.map f x • map k f ω := by
  induction ω using induction_on k A with
  | h y a => simp only [smul_smul, map_smul_d, map_mul]
  | hadd ω η hω hη => simp only [smul_add, map_add, hω, hη]

/-- The induced map intertwines the right outer actions along the unitization map. -/
@[simp↓]
theorem map_smul_right (f : A →ₙₐ[k] B) (x : Unitization k A)
    (ω : UniversalOneForms k A) :
    map k f (op x • ω) = op (Unitization.map f x) • map k f ω := by
  induction ω using induction_on k A with
  | h y a =>
    simp only [smul_right_smul_d, _root_.map_sub, map_smul_d,
      ← Unitization.snd_map, map_mul, Unitization.map_inr]
  | hadd ω η hω hη => simp only [smul_add, map_add, hω, hη]

/-- In the multiplication-kernel model the induced map applies the unitization map to
both tensor factors. -/
@[simp]
theorem coe_map (f : A →ₙₐ[k] B) (ω : UniversalOneForms k A) :
    ((map k f ω : UniversalOneForms k B) : Unitization k B ⊗[k] Unitization k B) =
      TensorProduct.map (Unitization.map f).toLinearMap (Unitization.map f).toLinearMap ω.1 := by
  induction ω using induction_on k A with
  | h x a =>
    simp only [map_smul_d, coe_smul_left, coe_d, map_sub, leftAction_tmul,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, map_mul, Unitization.map_inr]
  | hadd ω η hω hη => simp only [map_add, Submodule.coe_add, hω, hη]

/-- The identity homomorphism induces the identity on universal one-forms. -/
@[simp]
theorem map_id : map k (NonUnitalAlgHom.id k A) = LinearMap.id := by
  apply LinearMap.ext
  intro ω
  induction ω using induction_on k A with
  | h x a => simp only [map_smul_d, Unitization.map_id, AlgHom.id_apply,
      NonUnitalAlgHom.coe_id, id_eq, LinearMap.id_apply]
  | hadd ω η hω hη => simp only [map_add, hω, hη, LinearMap.id_apply]

/-- The map on universal one-forms preserves composition. -/
theorem map_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) :
    map k (g.comp f) = (map k g).comp (map k f) := by
  apply LinearMap.ext
  intro ω
  induction ω using induction_on k A with
  | h x a => simp only [LinearMap.comp_apply, map_smul_d, Unitization.map_comp,
      AlgHom.comp_apply, NonUnitalAlgHom.comp_apply]
  | hadd ω η hω hη => simp only [map_add, hω, hη, LinearMap.comp_apply]

/-- The zero homomorphism induces the zero map on universal one-forms. -/
@[simp]
theorem map_zero : map k (0 : A →ₙₐ[k] B) = 0 := by
  apply LinearMap.ext
  intro ω
  induction ω using induction_on k A with
  | h x a => simp only [map_smul_d, NonUnitalAlgHom.zero_apply, _root_.map_zero,
      smul_zero, LinearMap.zero_apply]
  | hadd ω η hω hη => simp only [map_add, hω, hη, LinearMap.zero_apply, add_zero]

end

end TauCeti.UniversalOneForms
