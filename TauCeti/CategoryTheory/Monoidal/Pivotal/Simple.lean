/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.ScalarTrace
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Traces of endomorphisms of simple objects

Let `C` be a pivotal category which is `k`-linear, for an algebraically closed field `k`, with
kernels. By Schur's lemma every endomorphism `f` of a simple object `X` with finite-dimensional
endomorphisms is the scalar `TauCeti.endAlgEquivOfSimple k X (End.of f)` times `𝟙 X`. Since the
traces are `k`-linear, the trace of `f` is that scalar times the dimension of `X`:

* `leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X`;
* `rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X`;
* `trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X` in a spherical category.

When the unit `𝟙_ C` is itself simple with finite-dimensional endomorphisms, applying
`endAlgEquivOfSimple k (𝟙_ C)` to these identities reads the traces as elements of `k`, by the
`simp` lemmas for `End.of` of `TauCeti.CategoryTheory.Linear.Endomorphism`.

The product `leftDim X ≫ rightDim X` of the two dimensions of a simple object does not depend on
the pivotal structure, although each factor may (`TauCeti.leftDim_comp_rightDim_eq`).

When the unit is simple, every scalar `𝟙_ C ⟶ 𝟙_ C` is a multiple of the identity, so it acts on
every object in the same way from the left and from the right. Hence the left and right
dimensions are multiplicative on tensor products, as in a braided category
(`TauCeti.leftDim_tensor_eq_comp_of_simple` and `TauCeti.rightDim_tensor_eq_comp_of_simple`); for
the traces themselves, apply `TauCeti.leftTrace_tensorHom_eq_comp_of_surjective` and its
companion to `(TauCeti.bijective_algebraMap_end_of_simple k (𝟙_ C)).surjective`.

All of these are the special case, through Schur's lemma, of the statements of
`TauCeti.CategoryTheory.Monoidal.Pivotal.ScalarTrace` for objects whose endomorphisms are the
scalars of a commutative semiring.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [HasKernels C]
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

/-- The left trace of an endomorphism of a simple object is its scalar times the left dimension. -/
theorem leftTrace_eq_smul_leftDim (f : X ⟶ X) :
    leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X :=
  leftTrace_eq_smul_leftDim_of_algebraMap_eq (algebraMap_endAlgEquivOfSimple _)

/-- The right trace of an endomorphism of a simple object is its scalar times the right
dimension. -/
theorem rightTrace_eq_smul_rightDim (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X :=
  rightTrace_eq_smul_rightDim_of_algebraMap_eq (algebraMap_endAlgEquivOfSimple _)

/-- In a spherical category, the trace of an endomorphism of a simple object is its scalar times
the quantum dimension. -/
theorem trace_eq_smul_quantumDim [SphericalCategory C] (f : X ⟶ X) :
    trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X :=
  trace_eq_smul_quantumDim_of_algebraMap_eq (algebraMap_endAlgEquivOfSimple _)

section ChangeOfPivotal

omit [PivotalCategory C]

variable (P Q : PivotalCategory C)

include k in
/-- For a simple object `X`, the left dimension followed by the right dimension of `X` is the same
for any two pivotal structures `P` and `Q` on `C`, although each dimension separately may
change. -/
theorem leftDim_comp_rightDim_eq :
    @leftDim C _ _ _ P X ≫ @rightDim C _ _ _ P X =
      @leftDim C _ _ _ Q X ≫ @rightDim C _ _ _ Q X :=
  leftDim_comp_rightDim_eq_of_surjective P Q (bijective_algebraMap_end_of_simple k X).surjective

end ChangeOfPivotal

section SimpleUnit

variable [Simple (𝟙_ C)] [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]

include k in
/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, the left dimension is multiplicative. -/
theorem leftDim_tensor_eq_comp_of_simple (X Y : C) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y :=
  leftDim_tensor_eq_comp_of_surjective
    (bijective_algebraMap_end_of_simple k (𝟙_ C)).surjective X Y

include k in
/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, the right dimension is multiplicative. -/
theorem rightDim_tensor_eq_comp_of_simple (X Y : C) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y :=
  rightDim_tensor_eq_comp_of_surjective
    (bijective_algebraMap_end_of_simple k (𝟙_ C)).surjective X Y

end SimpleUnit

end TauCeti
