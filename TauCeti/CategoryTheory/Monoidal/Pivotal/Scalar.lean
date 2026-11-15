/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical

/-!
# Traces on objects with scalar endomorphisms

Let `C` be a pivotal monoidal category which is `R`-linear over a commutative semiring `R`. When an
object `X` has scalar endomorphisms over `R`, meaning that the structure map `algebraMap R (End X)`
is bijective, every endomorphism `f : X ⟶ X` is `TauCeti.endAlgEquivOfBijective R hX (End.of f)`
times `𝟙 X`. By `R`-linearity of the categorical traces, the trace of `f` is that scalar times the
corresponding dimension of `X`:

* `leftTrace f = endAlgEquivOfBijective R hX (End.of f) • leftDim X`;
* `rightTrace f = endAlgEquivOfBijective R hX (End.of f) • rightDim X`;
* `trace f = endAlgEquivOfBijective R hX (End.of f) • quantumDim X` in a spherical category.

For an automorphism `a : X ≅ X`, the scalars of `a.inv` and `a.hom` are inverse to each other in
`R`, so `leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X`. Comparing two pivotal
structures `P` and `Q` on `C` rewrites the dimensions of `X` for `P` as traces for `Q` of a
mutually inverse pair of automorphisms of `X`, so the product `leftDim X ≫ rightDim X` does not
depend on the pivotal structure (`TauCeti.leftDim_comp_rightDim_eq_of_bijective`).

When the structure map `R → End (𝟙_ C)` on the tensor unit is surjective, every scalar
`𝟙_ C ⟶ 𝟙_ C` acts on every object in the same way from the left and from the right, so the left
and right traces and dimensions are multiplicative on tensor products.

Over an algebraically closed field, Schur's lemma supplies
`Function.Bijective (algebraMap k (End X))` for every simple object with finite-dimensional
endomorphisms, recovering the results of `TauCeti.CategoryTheory.Monoidal.Pivotal.Simple`.

## Main declarations

* `TauCeti.leftTrace_eq_smul_leftDim_of_bijective`,
  `TauCeti.rightTrace_eq_smul_rightDim_of_bijective` and
  `TauCeti.trace_eq_smul_quantumDim_of_bijective`: traces on an object with scalar endomorphisms;
* `TauCeti.leftTrace_inv_comp_rightTrace_hom_of_bijective`: cancellation of scalars on an
  automorphism;
* `TauCeti.leftDim_comp_rightDim_eq_of_bijective`: `leftDim X ≫ rightDim X` is independent of the
  pivotal structure when `X` has scalar endomorphisms;
* `TauCeti.leftTrace_tensorHom_eq_comp_of_surjective` and its companions: multiplicativity of
  traces and dimensions when `algebraMap R (End (𝟙_ C))` is surjective.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

variable (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [PivotalCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]

section Object

variable {X : C} (hX : Function.Bijective (algebraMap R (End X)))
include hX

/-- When `X` has scalar endomorphisms over `R`, the left trace of `f : X ⟶ X` is its scalar times
the left dimension of `X`. -/
theorem leftTrace_eq_smul_leftDim_of_bijective (f : X ⟶ X) :
    leftTrace f = endAlgEquivOfBijective R hX (End.of f) • leftDim X := by
  have hf : f = endAlgEquivOfBijective R hX (End.of f) • 𝟙 X :=
    (endAlgEquivOfBijective_smul_id hX (End.of f)).symm
  conv_lhs => rw [hf, leftTrace_smul, leftTrace_id]

/-- When `X` has scalar endomorphisms over `R`, the right trace of `f : X ⟶ X` is its scalar times
the right dimension of `X`. -/
theorem rightTrace_eq_smul_rightDim_of_bijective (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfBijective R hX (End.of f) • rightDim X := by
  have hf : f = endAlgEquivOfBijective R hX (End.of f) • 𝟙 X :=
    (endAlgEquivOfBijective_smul_id hX (End.of f)).symm
  conv_lhs => rw [hf, rightTrace_smul, rightTrace_id]

/-- In a spherical category, when `X` has scalar endomorphisms over `R`, the trace of `f : X ⟶ X`
is its scalar times the quantum dimension of `X`. -/
theorem trace_eq_smul_quantumDim_of_bijective [SphericalCategory C] (f : X ⟶ X) :
    trace f = endAlgEquivOfBijective R hX (End.of f) • quantumDim X := by
  rw [trace_eq_leftTrace, leftTrace_eq_smul_leftDim_of_bijective R hX, quantumDim_eq_leftDim]

/-- For an automorphism `a` of an object `X` with scalar endomorphisms, the left trace of `a.inv`
followed by the right trace of `a.hom` equals `leftDim X ≫ rightDim X`: the scalars of `a.inv` and
`a.hom` are inverse to each other in `R`. -/
theorem leftTrace_inv_comp_rightTrace_hom_of_bijective (a : X ≅ X) :
    leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X := by
  have h :
      endAlgEquivOfBijective R hX (End.of a.hom) *
        endAlgEquivOfBijective R hX (End.of a.inv) = 1 := by
    rw [← map_mul, ← End.of_comp]
    simp
  rw [leftTrace_eq_smul_leftDim_of_bijective R hX, rightTrace_eq_smul_rightDim_of_bijective R hX]
  simp [smul_smul, h]

end Object

section ChangeOfPivotal

omit [PivotalCategory C]

/-- **`leftDim X ≫ rightDim X` does not depend on the pivotal structure** when `X` has scalar
endomorphisms over `R`: two pivotal structures differ on `X` by an automorphism of `X` and its
inverse, whose scalars cancel. -/
theorem leftDim_comp_rightDim_eq_of_bijective (P Q : PivotalCategory C) {X : C}
    (hX : Function.Bijective (algebraMap R (End X))) :
    @leftDim C _ _ _ P X ≫ @rightDim C _ _ _ P X =
      @leftDim C _ _ _ Q X ≫ @rightDim C _ _ _ Q X := by
  rw [leftDim_eq_leftTrace P Q, rightDim_eq_rightTrace P Q]
  let _ := Q
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv] using
    leftTrace_inv_comp_rightTrace_hom_of_bijective R hX
      (@pivotalIsoApp C _ _ _ P X ≪≫ (pivotalIsoApp X).symm)

end ChangeOfPivotal

section ScalarUnit

variable (h : Function.Surjective (algebraMap R (End (𝟙_ C))))
include h

/-- When `algebraMap R (End (𝟙_ C))` is surjective, the left trace is multiplicative on tensor
products. -/
theorem leftTrace_tensorHom_eq_comp_of_surjective {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g :=
  leftTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective R h _ Y)

/-- When `algebraMap R (End (𝟙_ C))` is surjective, the right trace is multiplicative on tensor
products. -/
theorem rightTrace_tensorHom_eq_comp_of_surjective {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g :=
  rightTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective R h _ X)

/-- When `algebraMap R (End (𝟙_ C))` is surjective, the left dimension is multiplicative on tensor
products. -/
theorem leftDim_tensor_eq_comp_of_surjective (X Y : C) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y :=
  leftDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective R h _ Y)

/-- When `algebraMap R (End (𝟙_ C))` is surjective, the right dimension is multiplicative on tensor
products. -/
theorem rightDim_tensor_eq_comp_of_surjective (X Y : C) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y :=
  rightDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective R h _ X)

end ScalarUnit

end TauCeti
