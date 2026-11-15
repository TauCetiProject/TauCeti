/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Scalar
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Traces of endomorphisms of simple objects

Let `C` be a pivotal category which is `k`-linear, for an algebraically closed field `k`, with
kernels. By Schur's lemma every endomorphism `f` of a simple object `X` with finite-dimensional
endomorphisms is the scalar `TauCeti.endAlgEquivOfSimple k X (End.of f)` times `𝟙 X`. Specializing
the commutative-semiring trace formulas of `TauCeti.CategoryTheory.Monoidal.Pivotal.Scalar` to
`TauCeti.bijective_algebraMap_end_of_simple` expresses the trace of `f` as that scalar times the
dimension of `X`:

* `leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X`;
* `rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X`;
* `trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X` in a spherical category.

When the unit `𝟙_ C` is itself simple with finite-dimensional endomorphisms, applying
`endAlgEquivOfSimple k (𝟙_ C)` to these identities reads the traces as elements of `k`, by the
`simp` lemmas for `End.of` of `TauCeti.CategoryTheory.Linear.Endomorphism`.

For an automorphism `a` of a simple object the scalars of `a⁻¹` and `a` cancel, so
`leftTrace a⁻¹ ≫ rightTrace a = leftDim X ≫ rightDim X`, and `leftDim X ≫ rightDim X` does not
depend on the pivotal structure. When the unit is simple, every scalar `𝟙_ C ⟶ 𝟙_ C` is a multiple
of the identity, so the left and right traces and dimensions are multiplicative on tensor products
(`TauCeti.leftTrace_tensorHom_eq_comp_of_simple` and its companions).

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
    leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X := by
  rw [endAlgEquivOfSimple_eq_endAlgEquivOfBijective]
  exact leftTrace_eq_smul_leftDim_of_bijective (bijective_algebraMap_end_of_simple k X) f

/-- The right trace of an endomorphism of a simple object is its scalar times the right
dimension. -/
theorem rightTrace_eq_smul_rightDim (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X := by
  rw [endAlgEquivOfSimple_eq_endAlgEquivOfBijective]
  exact rightTrace_eq_smul_rightDim_of_bijective (bijective_algebraMap_end_of_simple k X) f

/-- In a spherical category, the trace of an endomorphism of a simple object is its scalar times
the quantum dimension. -/
theorem trace_eq_smul_quantumDim [SphericalCategory C] (f : X ⟶ X) :
    trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X := by
  rw [endAlgEquivOfSimple_eq_endAlgEquivOfBijective]
  exact trace_eq_smul_quantumDim_of_bijective (bijective_algebraMap_end_of_simple k X) f

include k in
/-- For an automorphism `a` of a simple object, the left trace of `a⁻¹` followed by the right trace
of `a` is the left dimension followed by the right dimension: the scalars of `a⁻¹` and `a`
cancel. -/
theorem leftTrace_inv_comp_rightTrace_hom (a : X ≅ X) :
    leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X :=
  leftTrace_inv_comp_rightTrace_hom_of_bijective (bijective_algebraMap_end_of_simple k X) a

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
  leftDim_comp_rightDim_eq_of_bijective k P Q (bijective_algebraMap_end_of_simple k X)

end ChangeOfPivotal

section SimpleUnit

variable [Simple (𝟙_ C)] [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]

include k in
/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, the left trace is multiplicative. -/
theorem leftTrace_tensorHom_eq_comp_of_simple {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g :=
  leftTrace_tensorHom_eq_comp_of_surjective
    (bijective_algebraMap_end_of_simple k (𝟙_ C)).surjective f g

include k in
/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, the right trace is multiplicative. -/
theorem rightTrace_tensorHom_eq_comp_of_simple {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g :=
  rightTrace_tensorHom_eq_comp_of_surjective
    (bijective_algebraMap_end_of_simple k (𝟙_ C)).surjective f g

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
