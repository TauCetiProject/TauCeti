/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic

/-!
# Algebraic specializations of the graded Grothendieck group

The graded Grothendieck group of a graded exact category is a module over
`ℤ[q,q⁻¹]`.  Evaluating `q` at a unit `u : ℤˣ` makes `ℤ` a module over this Laurent
coefficient ring, and extension of scalars gives

`ℤ ⊗[ℤ[q,q⁻¹]] LaurentK0 E`.

The only integer units are `1` and `-1`.  At `q = 1`, a grading shift has the same class as the
original object.  At `q = -1`, one grading shift negates its class, and an `n`-fold shift acts by
`n.negOnePow`.

A conflation-exact functor which forgets grading and identifies the grading shift with itself
therefore factors canonically through specialization at `q = 1`.  No claim is made that this
factor is an isomorphism: that requires additional hypotheses on the graded and ungraded
categories.

## Main definitions

* `TauCeti.LaurentK0.Specialization`: extension of scalars along evaluation at an integer unit.
* `TauCeti.LaurentK0.SpecializationAtOne` and
  `TauCeti.LaurentK0.SpecializationAtNegOne`: the specializations at `q = 1` and `q = -1`.
* `TauCeti.LaurentK0.Specialization.map`: the canonical additive map into a specialization.
* `TauCeti.LaurentK0.Specialization.desc`: the universal map out of a specialization.
* `TauCeti.LaurentK0.Specialization.mapForgettingAtOne`: the factor of a grading-forgetful map.

## Main results

* `TauCeti.LaurentK0.Specialization.map_smul`: Laurent scalars evaluate under specialization.
* `TauCeti.LaurentK0.Specialization.atOne_map_shiftZPow`: every shift is unchanged at `q = 1`.
* `TauCeti.LaurentK0.Specialization.atNegOne_map_shiftZPow`: an `n`-fold shift has sign
  `n.negOnePow` at `q = -1`.
* `TauCeti.LaurentK0.Specialization.mapForgettingAtOne_comp_map`: the induced ungraded `K₀` map
  factors through specialization at `q = 1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2 and Proposition 2.7.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w w' v v' u u'

namespace LaurentK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- The coefficient module `ℤ` obtained by evaluating `ℤ[q,q⁻¹]` at the integer unit `a`.

It is kept as a named class-valued definition because the tensor product which defines
`Specialization E a` must remember this particular module structure. -/
@[instance_reducible]
noncomputable def evaluationModule (a : ℤˣ) : Module (LaurentPolynomial ℤ) ℤ :=
  Module.compHom ℤ (laurentEval a).toRingHom

/-- **The graded Grothendieck group specialized at the integer unit `a`.**  This is extension of
scalars from `ℤ[q,q⁻¹]` to `ℤ` along evaluation at `q = a`. -/
noncomputable abbrev Specialization (E : GradedExactStructure C) (a : ℤˣ) : Type w :=
  @TensorProduct (LaurentPolynomial ℤ) inferInstance ℤ (LaurentK0 E) inferInstance inferInstance
    (evaluationModule a) inferInstance

/-- The graded Grothendieck group specialized at `q = 1`. -/
noncomputable abbrev SpecializationAtOne (E : GradedExactStructure C) : Type w :=
  Specialization E 1

/-- The graded Grothendieck group specialized at `q = -1`. -/
noncomputable abbrev SpecializationAtNegOne (E : GradedExactStructure C) : Type w :=
  Specialization E (-1)

namespace Specialization

variable (E : GradedExactStructure C) (a : ℤˣ)

noncomputable instance : AddCommGroup (Specialization E a) := inferInstanceAs
  (AddCommGroup
    (@TensorProduct (LaurentPolynomial ℤ) inferInstance ℤ (LaurentK0 E) inferInstance
      inferInstance (evaluationModule a) inferInstance))

/-- The canonical additive map from graded `K₀` to its specialization. -/
noncomputable def map : LaurentK0 E →+ Specialization E a := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := evaluationModule a
  exact
    { toFun := fun x => 1 ⊗ₜ[LaurentPolynomial ℤ] x
      map_zero' := by rw [TensorProduct.tmul_zero]
      map_add' := fun _ _ => by rw [TensorProduct.tmul_add] }

private theorem map_apply (x : LaurentK0 E) :
    map E a x =
      @TensorProduct.tmul (LaurentPolynomial ℤ) inferInstance ℤ (LaurentK0 E) inferInstance
        inferInstance (evaluationModule a) inferInstance 1 x :=
  (rfl)

/-- The specialized class of an object. -/
noncomputable def of (X : C) : Specialization E a :=
  map E a (LaurentK0.of E X)

theorem of_eq_map (X : C) : of E a X = map E a (LaurentK0.of E X) :=
  (rfl)

/-- **Laurent scalars evaluate under specialization.** -/
theorem map_smul (p : LaurentPolynomial ℤ) (x : LaurentK0 E) :
    map E a (p • x) = (laurentEval a p : ℤ) • map E a x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := evaluationModule a
  calc
    map E a (p • x) = (p • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x :=
      TensorProduct.tmul_smul p 1 x
    _ = (laurentEval a p : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x := by
      congr 1
      simp [RingHom.toModule_smul]
    _ = ((laurentEval a p : ℤ) • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x := by
      simp
    _ = (laurentEval a p : ℤ) •
        @TensorProduct.tmul (LaurentPolynomial ℤ) inferInstance ℤ (LaurentK0 E) inferInstance
          inferInstance (evaluationModule a) inferInstance 1 x :=
      (TensorProduct.smul_tmul' _ _ _).symm
    _ = (laurentEval a p : ℤ) • map E a x := by
      rw [map_apply]

/-- Specialization sends the `n`-fold grading shift to multiplication by `aⁿ`. -/
theorem map_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    map E a (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      ((a ^ n : ℤˣ) : ℤ) • map E a (LaurentK0.ofExactK0 E x) := by
  rw [← LaurentK0.T_smul, map_smul, laurentEval_T]

/-- At `q = 1`, every iterated grading shift has the same specialized class. -/
theorem atOne_map_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    map E 1 (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      map E 1 (LaurentK0.ofExactK0 E x) := by
  rw [map_shiftZPow]
  simp

/-- At `q = -1`, an `n`-fold grading shift multiplies the specialized class by
`n.negOnePow`. -/
theorem atNegOne_map_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    map E (-1) (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      (n.negOnePow : ℤ) • map E (-1) (LaurentK0.ofExactK0 E x) := by
  simpa only [Int.negOnePow] using map_shiftZPow E (-1) n x

/-- At `q = 1`, shifting an object once does not change its specialized class. -/
@[simp]
theorem atOne_of_shift (X : C) : of E 1 (E.shift.functor.obj X) = of E 1 X := by
  rw [of_eq_map, of_eq_map, ← LaurentK0.T_one_smul_of, map_smul]
  simp

/-- At `q = -1`, shifting an object once negates its specialized class. -/
@[simp]
theorem atNegOne_of_shift (X : C) : of E (-1) (E.shift.functor.obj X) = -of E (-1) X := by
  rw [of_eq_map, of_eq_map, ← LaurentK0.T_one_smul_of, map_smul]
  simp

section UniversalProperty

variable {G : Type*} [AddCommGroup G]

private def zsmulAddHom (f : LaurentK0 E →+ G) : ℤ →+ LaurentK0 E →+ G where
  toFun n :=
    { toFun := fun x => n • f x
      map_zero' := by simp
      map_add' := fun x y => by simp }
  map_zero' := by ext; simp
  map_add' := fun m n => by ext; simp [add_smul]

@[simp]
private theorem zsmulAddHom_apply (f : LaurentK0 E →+ G) (n : ℤ) (x : LaurentK0 E) :
    zsmulAddHom E f n x = n • f x :=
  rfl

/-- **The universal map out of a specialization.**  An additive map out of graded `K₀` factors
through evaluation at `a` when it sends Laurent scalar multiplication to multiplication by the
evaluated integer. -/
noncomputable def desc (f : LaurentK0 E →+ G)
    (hf : ∀ (p : LaurentPolynomial ℤ) (x : LaurentK0 E),
      f (p • x) = (laurentEval a p : ℤ) • f x) : Specialization E a →+ G := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := evaluationModule a
  refine TensorProduct.liftAddHom (zsmulAddHom E f) ?_
  intro p n x
  simp only [zsmulAddHom_apply]
  rw [hf]
  simp [RingHom.toModule_smul, mul_smul, Int.mul_comm]

@[simp]
theorem desc_map (f : LaurentK0 E →+ G)
    (hf : ∀ (p : LaurentPolynomial ℤ) (x : LaurentK0 E),
      f (p • x) = (laurentEval a p : ℤ) • f x) (x : LaurentK0 E) :
    desc E a f hf (map E a x) = f x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := evaluationModule a
  rw [desc, map_apply, TensorProduct.liftAddHom_tmul]
  simp

/-- Additive maps out of a specialization are determined by their values on the image of graded
`K₀`. -/
theorem hom_ext {f g : Specialization E a →+ G}
    (h : ∀ x : LaurentK0 E, f (map E a x) = g (map E a x)) : f = g := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := evaluationModule a
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
      have hn : n ⊗ₜ[LaurentPolynomial ℤ] x =
          n • (1 ⊗ₜ[LaurentPolynomial ℤ] x) := by
        calc
          n ⊗ₜ[LaurentPolynomial ℤ] x = (n • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x := by
            simp
          _ = n • (1 ⊗ₜ[LaurentPolynomial ℤ] x) :=
            (TensorProduct.smul_tmul' _ _ _).symm
      rw [hn, map_zsmul, map_zsmul]
      exact congrArg (n • ·) (h x)
  | add x y hx hy => simp [hx, hy]

/-- Additive maps out of a specialized graded `K₀` are determined by specialized object classes. -/
theorem hom_ext_of {f g : Specialization E a →+ G} (h : ∀ X : C, f (of E a X) = g (of E a X)) :
    f = g := by
  apply hom_ext E a
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, LaurentK0.ofExactK0 E y = x :=
    ⟨(LaurentK0.ofExactK0 E).symm x, by simp⟩
  have key :
      (f.comp (map E a)).comp (LaurentK0.ofExactK0 E).toAddMonoidHom =
        (g.comp (map E a)).comp (LaurentK0.ofExactK0 E).toAddMonoidHom :=
    ExactK0.hom_ext fun X => by simpa [of] using h X
  simpa using DFunLike.congr_fun key y

end UniversalProperty

section ForgetGrading

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
variable {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

private noncomputable def forgetMap (hU : E.toExactStructure.IsConflationExact E' F) :
    LaurentK0 E →+ ExactK0 E' :=
  (ExactK0.map F hU).comp (LaurentK0.ofExactK0 E).symm.toAddMonoidHom

@[simp]
private theorem forgetMap_of (hU : E.toExactStructure.IsConflationExact E' F) (X : C) :
    forgetMap E hU (LaurentK0.of E X) = ExactK0.of (F.obj X) := by
  rw [← LaurentK0.ofExactK0_exactK0_of, forgetMap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, ExactK0.map_of]

private theorem forgetMap_smul (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (p : LaurentPolynomial ℤ) (x : LaurentK0 E) :
    forgetMap E hU (p • x) = (laurentEval (1 : ℤˣ) p : ℤ) • forgetMap E hU x := by
  obtain ⟨y, rfl⟩ : ∃ y, LaurentK0.ofExactK0 E y = x :=
    ⟨(LaurentK0.ofExactK0 E).symm x, by simp⟩
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [add_smul, map_add, hp, hq, map_add]
  | C_mul_T n b =>
      rw [mul_smul, LaurentK0.T_smul, laurentPolynomialC_smul, map_zsmul]
      simp only [forgetMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply]
      rw [GradedExactStructure.map_shiftZPow_of_commShift hU comm, map_mul, laurentEval_C,
        laurentEval_T]
      simp

/-- **The map on `K₀` induced by forgetting grading factors through specialization at `q = 1`.**

The commuting isomorphism says that a grading shift becomes invisible after applying `F`; it does
not imply that this factor is an isomorphism. -/
noncomputable def mapForgettingAtOne
    (hU : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    SpecializationAtOne E →+ ExactK0 E' :=
  desc E 1 (forgetMap E hU) (forgetMap_smul E hU comm)

@[simp]
theorem mapForgettingAtOne_of (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (X : C) :
    mapForgettingAtOne E hU comm (of E 1 X) = ExactK0.of (F.obj X) := by
  rw [of_eq_map, mapForgettingAtOne, desc_map, forgetMap_of]

/-- The explicit factorization equation for the grading-forgetful map. -/
theorem mapForgettingAtOne_comp_map (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) :
    (mapForgettingAtOne E hU comm).comp (map E 1) =
      (ExactK0.map F hU).comp (LaurentK0.ofExactK0 E).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  rw [AddMonoidHom.comp_apply, mapForgettingAtOne, desc_map, forgetMap]

/-- The factor through specialization at `q = 1` is characterized by its values on object
classes. -/
theorem mapForgettingAtOne_unique (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (g : SpecializationAtOne E →+ ExactK0 E')
    (hg : ∀ X : C, g (of E 1 X) = ExactK0.of (F.obj X)) :
    g = mapForgettingAtOne E hU comm := by
  apply hom_ext_of E 1
  intro X
  rw [hg, mapForgettingAtOne_of]

end ForgetGrading

end Specialization

end LaurentK0

end TauCeti
