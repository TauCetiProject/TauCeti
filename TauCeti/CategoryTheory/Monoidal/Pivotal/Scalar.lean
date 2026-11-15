/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical

/-!
# Traces on objects with scalar endomorphisms

Let `C` be a pivotal monoidal category that is preadditive and `R`-linear over a commutative
semiring `R`, with `R`-bilinear tensor product. When an object `X` has scalar endomorphisms over
`R`, meaning that `algebraMap R (End X)` is bijective, every endomorphism `f : X ⟶ X` is its scalar
`TauCeti.endAlgEquivOfBijective hX (End.of f)` times `𝟙 X`. Because the categorical traces are
`R`-linear, the trace of `f` is that scalar times the categorical dimension of `X`:

* `leftTrace f = endAlgEquivOfBijective hX (End.of f) • leftDim X`;
* `rightTrace f = endAlgEquivOfBijective hX (End.of f) • rightDim X`;
* `trace f = endAlgEquivOfBijective hX (End.of f) • quantumDim X` in a spherical category.

For an automorphism `a : X ≅ X`, the scalars of `a.inv` and `a.hom` are inverse to each other in
`R`, so `leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X`. Comparing two pivotal
structures `P` and `Q` on `C` writes the left and right dimensions of `X` for `P` as the left and
right traces for `Q` of an automorphism of `X` and its inverse, so `leftDim X ≫ rightDim X` does
not depend on the pivotal structure (`TauCeti.leftDim_comp_rightDim_eq_of_bijective`).

When every scalar `𝟙_ C ⟶ 𝟙_ C` is in the image of `algebraMap R (End (𝟙_ C))`, left and right
scalar actions on every object agree, so the left and right traces and dimensions are
multiplicative on tensor products. Over an algebraically closed field, a simple object with
finite-dimensional endomorphisms satisfies bijectivity by Schur's lemma, recovering the field
results of `TauCeti.CategoryTheory.Monoidal.Pivotal.Simple` as corollaries.

## Main declarations

* `TauCeti.leftTrace_eq_smul_leftDim_of_bijective`,
  `TauCeti.rightTrace_eq_smul_rightDim_of_bijective`, and
  `TauCeti.trace_eq_smul_quantumDim_of_bijective`: traces of endomorphisms of an object with
  scalar endomorphisms;
* `TauCeti.leftTrace_inv_comp_rightTrace_hom_of_bijective` and
  `TauCeti.leftDim_comp_rightDim_eq_of_bijective`: invariance of `leftDim X ≫ rightDim X` under
  automorphisms and under change of pivotal structure;
* `TauCeti.leftTrace_tensorHom_eq_comp_of_surjective`,
  `TauCeti.rightTrace_tensorHom_eq_comp_of_surjective`,
  `TauCeti.leftDim_tensor_eq_comp_of_surjective`, and
  `TauCeti.rightDim_tensor_eq_comp_of_surjective`: multiplicativity of traces and dimensions when
  the tensor unit has scalar endomorphisms.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

section Bijective

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [PivotalCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

/-- For an object `X` with scalar endomorphisms over `R`, the left trace of `f : X ⟶ X` is its
scalar times the left dimension of `X`. -/
theorem leftTrace_eq_smul_leftDim_of_bijective {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) (f : X ⟶ X) :
    leftTrace f = endAlgEquivOfBijective hX (End.of f) • leftDim X := by
  conv_lhs => rw [← endAlgEquivOfBijective_of_smul_id hX f]
  rw [leftTrace_smul, leftTrace_id]

/-- For an object `X` with scalar endomorphisms over `R`, the right trace of `f : X ⟶ X` is its
scalar times the right dimension of `X`. -/
theorem rightTrace_eq_smul_rightDim_of_bijective {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfBijective hX (End.of f) • rightDim X := by
  conv_lhs => rw [← endAlgEquivOfBijective_of_smul_id hX f]
  rw [rightTrace_smul, rightTrace_id]

/-- In a spherical category, for an object `X` with scalar endomorphisms over `R`, the trace of
`f : X ⟶ X` is its scalar times the quantum dimension of `X`. -/
theorem trace_eq_smul_quantumDim_of_bijective [SphericalCategory C] {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) (f : X ⟶ X) :
    trace f = endAlgEquivOfBijective hX (End.of f) • quantumDim X := by
  rw [trace_eq_leftTrace, leftTrace_eq_smul_leftDim_of_bijective hX, quantumDim_eq_leftDim]

/-- For an automorphism `a` of an object `X` with scalar endomorphisms over `R`, the left trace of
`a.inv` followed by the right trace of `a.hom` equals `leftDim X ≫ rightDim X`: the inverse
scalars of `a.inv` and `a.hom` cancel. -/
theorem leftTrace_inv_comp_rightTrace_hom_of_bijective {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) (a : X ≅ X) :
    leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X := by
  rw [leftTrace_eq_smul_leftDim_of_bijective hX, rightTrace_eq_smul_rightDim_of_bijective hX,
    Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm,
    endAlgEquivOfBijective_hom_mul_inv hX a, one_smul]

end Bijective

section ChangeOfPivotal

variable (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C] [MonoidalLinear R C]

/-- **`leftDim X ≫ rightDim X` does not depend on the pivotal structure** when `X` has scalar
endomorphisms over a commutative semiring `R`: two pivotal structures differ on `X` by a unit
scalar and its inverse. -/
theorem leftDim_comp_rightDim_eq_of_bijective (P Q : PivotalCategory C) {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) :
    @leftDim C _ _ _ P X ≫ @rightDim C _ _ _ P X =
      @leftDim C _ _ _ Q X ≫ @rightDim C _ _ _ Q X := by
  rw [leftDim_eq_leftTrace P Q, rightDim_eq_rightTrace P Q]
  let _ := Q
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv] using
    leftTrace_inv_comp_rightTrace_hom_of_bijective hX
      (@pivotalIsoApp C _ _ _ P X ≪≫ (pivotalIsoApp X).symm)

end ChangeOfPivotal

section SurjectiveUnit

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [PivotalCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

/-- If `algebraMap R (End (𝟙_ C))` is surjective, the left trace is multiplicative on tensor
products of endomorphisms. -/
theorem leftTrace_tensorHom_eq_comp_of_surjective
    (h : Function.Surjective (algebraMap R (End (𝟙_ C)))) {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g :=
  leftTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ Y)

/-- If `algebraMap R (End (𝟙_ C))` is surjective, the right trace is multiplicative on tensor
products of endomorphisms. -/
theorem rightTrace_tensorHom_eq_comp_of_surjective
    (h : Function.Surjective (algebraMap R (End (𝟙_ C)))) {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g :=
  rightTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ X)

/-- If `algebraMap R (End (𝟙_ C))` is surjective, the left dimension is multiplicative on tensor
products of objects. -/
theorem leftDim_tensor_eq_comp_of_surjective
    (h : Function.Surjective (algebraMap R (End (𝟙_ C)))) (X Y : C) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y :=
  leftDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ Y)

/-- If `algebraMap R (End (𝟙_ C))` is surjective, the right dimension is multiplicative on tensor
products of objects. -/
theorem rightDim_tensor_eq_comp_of_surjective
    (h : Function.Surjective (algebraMap R (End (𝟙_ C)))) (X Y : C) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y :=
  rightDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ X)

end SurjectiveUnit

end TauCeti
