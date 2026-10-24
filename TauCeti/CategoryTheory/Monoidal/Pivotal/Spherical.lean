/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Tensor

/-!
# Spherical categories

A pivotal category is *spherical* when the left and right traces of every endomorphism agree.
In a spherical category the common value `trace f = leftTrace f = rightTrace f` is the
categorical trace, and the *quantum dimension* `quantumDim X = trace (𝟙 X)` is the common value
of the left and right dimensions of `X`.

The trace inherits the properties of both one-sided traces: it is cyclic, additive, linear in a
linear monoidal category, the identity on scalars, additive on biproducts, and invariant under
the right adjoint mate, so that `quantumDim Xᘁ = quantumDim X`. Since the left trace lets a
scalar act on the right of a loop and the right trace lets one act on the left, a scalar acting
on either side factors out of the trace. Combined with the nested-loop formula for the trace of
a tensor product, this makes the trace **multiplicative** in every spherical category:
`trace (f ⊗ₘ g) = trace f ≫ trace g`, and so
`quantumDim (X ⊗ Y) = quantumDim X ≫ quantumDim Y`.
No braiding is needed. For the one-sided traces of a merely pivotal category, multiplicativity
is only available when the relevant scalar acts on an object in the same way from both sides,
for instance in a braided category.

## Main declarations

* `TauCeti.SphericalCategory`: a pivotal category whose left and right traces agree;
* `TauCeti.trace` and `TauCeti.quantumDim`: the trace of an endomorphism and the quantum
  dimension of an object in a spherical category;
* `TauCeti.trace_comm`: cyclicity of the trace;
* `TauCeti.trace_rightAdjointMate` and `TauCeti.quantumDim_rightDual`: invariance under duality;
* `TauCeti.trace_scalar_whiskerRight_comp` and `TauCeti.trace_comp_whiskerLeft_scalar`: a scalar
  acting on either side factors out of the trace;
* `TauCeti.trace_tensorHom` and `TauCeti.quantumDim_tensor`: multiplicativity of the trace and
  of the quantum dimension;
* `TauCeti.trace_biproduct` and `TauCeti.quantumDim_biproduct`: additivity on finite
  biproducts.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
* [leanprover-community/mathlib4#42191](https://github.com/leanprover-community/mathlib4/pull/42191),
  for the names `SphericalCategory`, `leftTrace_eq_rightTrace`, `trace`, `trace_eq_leftTrace`
  and `trace_eq_rightTrace`
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

variable (C) in
/-- A pivotal category is *spherical* when the left and right traces of every endomorphism
agree. -/
class SphericalCategory : Prop where
  /-- The left and right traces of every endomorphism agree. -/
  leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) : leftTrace f = rightTrace f

/-- The *trace* of an endomorphism in a spherical category: the common value of its left and
right traces. The sphericity hypothesis is not needed to write down the formula, but it is
carried so that `trace` is only available where it does not depend on the side. -/
noncomputable def trace [_hC : SphericalCategory C] {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace f

variable [SphericalCategory C]

/-- The *quantum dimension* of an object of a spherical category: the trace of its identity. -/
noncomputable def quantumDim (X : C) : 𝟙_ C ⟶ 𝟙_ C :=
  trace (𝟙 X)

/-- The trace is the left trace. -/
theorem trace_eq_leftTrace {X : C} (f : X ⟶ X) : trace f = leftTrace f :=
  (rfl)

/-- The trace is the right trace. -/
theorem trace_eq_rightTrace {X : C} (f : X ⟶ X) : trace f = rightTrace f :=
  SphericalCategory.leftTrace_eq_rightTrace f

/-- The trace of an identity is the quantum dimension. -/
@[simp]
theorem trace_id (X : C) : trace (𝟙 X) = quantumDim X :=
  (rfl)

/-- In a spherical category the left and right dimensions agree. -/
theorem leftDim_eq_rightDim (X : C) : leftDim X = rightDim X := by
  rw [← leftTrace_id, ← rightTrace_id, SphericalCategory.leftTrace_eq_rightTrace]

/-- The quantum dimension is the left dimension. -/
theorem quantumDim_eq_leftDim (X : C) : quantumDim X = leftDim X := by
  rw [← trace_id, trace_eq_leftTrace, leftTrace_id]

/-- The quantum dimension is the right dimension. -/
theorem quantumDim_eq_rightDim (X : C) : quantumDim X = rightDim X := by
  rw [quantumDim_eq_leftDim, leftDim_eq_rightDim]

/-- **Cyclicity of the trace**: `trace (f ≫ g) = trace (g ≫ f)`. -/
theorem trace_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : trace (f ≫ g) = trace (g ≫ f) := by
  rw [trace_eq_leftTrace, trace_eq_leftTrace, leftTrace_comm]

/-- The trace is invariant under conjugation by an isomorphism. -/
theorem trace_conj {X Y : C} (i : X ≅ Y) (f : X ⟶ X) :
    trace (i.inv ≫ f ≫ i.hom) = trace f := by
  rw [trace_eq_leftTrace, trace_eq_leftTrace, leftTrace_conj]

/-- Isomorphic objects have the same quantum dimension. -/
theorem quantumDim_congr {X Y : C} (i : X ≅ Y) : quantumDim X = quantumDim Y := by
  rw [quantumDim_eq_leftDim, quantumDim_eq_leftDim, leftDim_congr i]

/-- The trace of the right adjoint mate `fᘁ` is the trace of `f`. -/
@[simp]
theorem trace_rightAdjointMate {X : C} (f : X ⟶ X) : trace (fᘁ) = trace f := by
  rw [trace_eq_leftTrace, leftTrace_rightAdjointMate, trace_eq_rightTrace]

/-- An object and its right dual have the same quantum dimension. -/
@[simp]
theorem quantumDim_rightDual (X : C) : quantumDim Xᘁ = quantumDim X := by
  rw [← trace_id, ← rightAdjointMate_id, trace_rightAdjointMate, trace_id]

/-- **The trace of a scalar is itself**: for `a : 𝟙_ C ⟶ 𝟙_ C`, `trace a = a`. -/
@[simp]
theorem trace_unit (a : 𝟙_ C ⟶ 𝟙_ C) : trace a = a := by
  rw [trace_eq_leftTrace, leftTrace_unit]

/-- The quantum dimension of the unit is `𝟙`. -/
@[simp]
theorem quantumDim_unit : quantumDim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  rw [quantumDim_eq_leftDim, leftDim_unit]

/-- A scalar acting on `X` from the left factors out of the trace. -/
theorem trace_scalar_whiskerRight_comp {X : C} (a : 𝟙_ C ⟶ 𝟙_ C) (f : X ⟶ X) :
    trace ((λ_ X).inv ≫ a ▷ X ≫ (λ_ X).hom ≫ f) = a ≫ trace f := by
  rw [trace_eq_rightTrace, trace_eq_rightTrace, rightTrace_scalar_whiskerRight_comp]

/-- A scalar acting on `X` from the right factors out of the trace. -/
theorem trace_comp_whiskerLeft_scalar {X : C} (f : X ⟶ X) (a : 𝟙_ C ⟶ 𝟙_ C) :
    trace (f ≫ (ρ_ X).inv ≫ X ◁ a ≫ (ρ_ X).hom) = trace f ≫ a := by
  rw [trace_eq_leftTrace, trace_eq_leftTrace, leftTrace_comp_whiskerLeft_scalar]

/-- **Multiplicativity of the trace**: in a spherical category,
`trace (f ⊗ₘ g) = trace f ≫ trace g`, with no braiding required. -/
@[simp]
theorem trace_tensorHom {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    trace (f ⊗ₘ g) = trace f ≫ trace g := by
  -- The left trace of `f` acts on `Y` from the left inside the loop of `g`; sphericity lets us
  -- close that loop on the other side, where a scalar acting from the left factors out.
  rw [trace_eq_leftTrace, leftTrace_tensorHom, ← trace_eq_leftTrace,
    trace_scalar_whiskerRight_comp, trace_eq_leftTrace f]

/-- **Multiplicativity of the quantum dimension**:
`quantumDim (X ⊗ Y) = quantumDim X ≫ quantumDim Y`. -/
@[simp]
theorem quantumDim_tensor (X Y : C) : quantumDim (X ⊗ Y) = quantumDim X ≫ quantumDim Y := by
  rw [← trace_id, ← trace_id, ← trace_id, ← id_tensorHom_id, trace_tensorHom]

section Linear

variable [Preadditive C] [MonoidalPreadditive C]

/-- The trace is additive. -/
@[simp]
theorem trace_add {X : C} (f g : X ⟶ X) : trace (f + g) = trace f + trace g := by
  simp only [trace_eq_leftTrace, leftTrace_add]

/-- The trace of zero is zero. -/
@[simp]
theorem trace_zero (X : C) : trace (0 : X ⟶ X) = 0 := by
  rw [trace_eq_leftTrace, leftTrace_zero]

/-- The zero object has quantum dimension zero. -/
@[simp]
theorem quantumDim_zero [HasZeroObject C] : quantumDim (0 : C) = 0 := by
  rw [quantumDim_eq_leftDim, leftDim_zero]

/-- The trace commutes with finite sums. -/
@[simp]
theorem trace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ X)) :
    trace (∑ i ∈ s, f i) = ∑ i ∈ s, trace (f i) := by
  simp only [trace_eq_leftTrace, leftTrace_sum]

/-- The trace commutes with negation. -/
@[simp]
theorem trace_neg {X : C} (f : X ⟶ X) : trace (-f) = -trace f := by
  simp only [trace_eq_leftTrace, leftTrace_neg]

/-- The trace commutes with subtraction. -/
@[simp]
theorem trace_sub {X : C} (f g : X ⟶ X) : trace (f - g) = trace f - trace g := by
  simp only [trace_eq_leftTrace, leftTrace_sub]

/-- The trace is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem trace_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C] {X : C} (r : R)
    (f : X ⟶ X) : trace (r • f) = r • trace f := by
  simp only [trace_eq_leftTrace, leftTrace_smul]

section Finite

variable {ι : Type*} [Fintype ι] {X : ι → C} [HasBiproduct X]

/-- The trace of an endomorphism of a finite biproduct is the sum of the traces of its diagonal
components. -/
theorem trace_biproduct (f : ⨁ X ⟶ ⨁ X) :
    trace f = ∑ i, trace (biproduct.ι X i ≫ f ≫ biproduct.π X i) := by
  simp only [trace_eq_leftTrace, leftTrace_biproduct f]

/-- The trace of a block-diagonal morphism is the sum of its block traces. -/
@[simp]
theorem trace_biproduct_map (f : ∀ i, X i ⟶ X i) :
    trace (biproduct.map f) = ∑ i, trace (f i) := by
  simp only [trace_eq_leftTrace, leftTrace_biproduct_map]

/-- The quantum dimension is additive on finite biproducts. -/
@[simp]
theorem quantumDim_biproduct : quantumDim (⨁ X) = ∑ i, quantumDim (X i) := by
  simp only [quantumDim_eq_leftDim, leftDim_biproduct]

end Finite

section Binary

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- The trace of an endomorphism of a binary biproduct is the sum of the traces of its two
diagonal components. -/
theorem trace_biprod (f : X ⊞ Y ⟶ X ⊞ Y) :
    trace f =
      trace (biprod.inl ≫ f ≫ biprod.fst) + trace (biprod.inr ≫ f ≫ biprod.snd) := by
  simp only [trace_eq_leftTrace, leftTrace_biprod f]

/-- The trace of a binary block-diagonal morphism is the sum of its block traces. -/
@[simp]
theorem trace_biprod_map (f : X ⟶ X) (g : Y ⟶ Y) :
    trace (biprod.map f g) = trace f + trace g := by
  simp only [trace_eq_leftTrace, leftTrace_biprod_map]

/-- The quantum dimension is additive on binary biproducts. -/
@[simp]
theorem quantumDim_biprod : quantumDim (X ⊞ Y) = quantumDim X + quantumDim Y := by
  simp only [quantumDim_eq_leftDim, leftDim_biprod]

end Binary

end Linear

end TauCeti
