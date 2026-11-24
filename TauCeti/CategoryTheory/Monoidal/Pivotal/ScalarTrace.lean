/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.CategoryTheory.Monoidal.Scalar

/-!
# Traces on objects with scalar endomorphisms

Let `C` be a pivotal category which is `R`-linear for a commutative semiring `R`. An object `X`
has *scalar endomorphisms* when the structure map `algebraMap R (End X)`, `r ↦ r • 𝟙 X`, is
bijective; over an algebraically closed field this is Schur's lemma for a simple object with
finite-dimensional endomorphisms (`TauCeti.bijective_algebraMap_end_of_simple`), but it also makes
sense over a ring such as `ℤ` or `ℤ/4`. This file proves the trace formulas of a pivotal category
for such objects. Only the existence of scalars is used, so the hypotheses below ask for
surjectivity of `algebraMap R (End X)` alone.

Since the traces are `R`-linear, the trace of an endomorphism `f` which is the scalar
`r • 𝟙 X` is `r` times the corresponding dimension:

* `leftTrace f = r • leftDim X`, `rightTrace f = r • rightDim X`, and
  `trace f = r • quantumDim X` in a spherical category.

For an automorphism `a` of `X` with scalar endomorphisms, the scalars of `a⁻¹` and `a` multiply to
an element acting as the identity on `X`, so
`leftTrace a⁻¹ ≫ rightTrace a = leftDim X ≫ rightDim X`.
Changing the pivotal structure turns the left dimension of `X` into the left trace of an
automorphism `a⁻¹` and the right dimension into the right trace of `a`, so the product
`leftDim X ≫ rightDim X` does not depend on the pivotal structure, although each factor may
(`TauCeti.leftDim_comp_rightDim_eq_of_surjective`).

When the unit `𝟙_ C` has scalar endomorphisms, every scalar acts on every object in the same way
from the left and from the right. Hence the left and right traces and dimensions are
multiplicative on tensor products (`TauCeti.leftTrace_tensorHom_eq_comp_of_surjective` and its
companions), as in a braided category.

The field forms of these statements, for simple objects over an algebraically closed field, are in
`TauCeti.CategoryTheory.Monoidal.Pivotal.Simple`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]

section Scalar

variable {X : C}

/-- The left trace of the endomorphism `algebraMap R (End X) r = r • 𝟙 X` is `r` times the left
dimension. -/
theorem leftTrace_eq_smul_leftDim_of_algebraMap_eq {f : X ⟶ X} {r : R}
    (h : algebraMap R (End X) r = End.of f) : leftTrace f = r • leftDim X := by
  rw [← leftTrace_id, ← leftTrace_smul, ← End.algebraMap_asHom, h]

/-- The right trace of the endomorphism `algebraMap R (End X) r = r • 𝟙 X` is `r` times the right
dimension. -/
theorem rightTrace_eq_smul_rightDim_of_algebraMap_eq {f : X ⟶ X} {r : R}
    (h : algebraMap R (End X) r = End.of f) : rightTrace f = r • rightDim X := by
  rw [← rightTrace_id, ← rightTrace_smul, ← End.algebraMap_asHom, h]

/-- In a spherical category, the trace of the endomorphism `algebraMap R (End X) r = r • 𝟙 X` is
`r` times the quantum dimension. -/
theorem trace_eq_smul_quantumDim_of_algebraMap_eq [SphericalCategory C] {f : X ⟶ X} {r : R}
    (h : algebraMap R (End X) r = End.of f) : trace f = r • quantumDim X := by
  rw [trace_eq_leftTrace, leftTrace_eq_smul_leftDim_of_algebraMap_eq h, quantumDim_eq_leftDim]

/-- For an automorphism `a` of an object whose endomorphisms are scalars, the left trace of `a⁻¹`
followed by the right trace of `a` is the left dimension followed by the right dimension. -/
theorem leftTrace_inv_comp_rightTrace_hom_of_surjective
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ X) :
    leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X := by
  obtain ⟨r, hr⟩ := End.exists_smul_id_eq_of_surjective hX a.hom
  obtain ⟨s, hs⟩ := End.exists_smul_id_eq_of_surjective hX a.inv
  -- The scalars of `a⁻¹` and `a` multiply to an element acting on `X` as the identity.
  have h : (s * r) • 𝟙 X = 𝟙 X := by
    have h := a.inv_hom_id
    rwa [← hr, ← hs, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at h
  -- Taking left traces, `s * r` also acts as the identity on `leftDim X ≫ rightDim X`.
  have hd : (r * s) • (leftDim X ≫ rightDim X) = leftDim X ≫ rightDim X := by
    rw [mul_comm, ← Linear.smul_comp, ← leftTrace_id, ← leftTrace_smul, h]
  simp [← hr, ← hs, leftTrace_smul, rightTrace_smul, smul_smul, hd]

end Scalar

section ChangeOfPivotal

omit [PivotalCategory C]

variable (P Q : PivotalCategory C)

/-- For an object `X` whose endomorphisms are scalars, the left dimension followed by the right
dimension of `X` is the same for any two pivotal structures `P` and `Q` on `C`, although each
dimension separately may change. -/
theorem leftDim_comp_rightDim_eq_of_surjective {X : C}
    (hX : Function.Surjective (algebraMap R (End X))) :
    @leftDim C _ _ _ P X ≫ @rightDim C _ _ _ P X =
      @leftDim C _ _ _ Q X ≫ @rightDim C _ _ _ Q X := by
  rw [leftDim_eq_leftTrace P Q, rightDim_eq_rightTrace P Q]
  -- Both dimensions for `P` are traces for `Q` of the automorphism `φ_X ≫ ψ_X⁻¹` of `X` and of
  -- its inverse, where `φ` and `ψ` are the pivotal isomorphisms of `P` and `Q`.
  let _ := Q
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv] using
    leftTrace_inv_comp_rightTrace_hom_of_surjective hX
      (@pivotalIsoApp C _ _ _ P X ≪≫ (pivotalIsoApp X).symm)

end ChangeOfPivotal

section ScalarUnit

variable (h : Function.Surjective (algebraMap R (End (𝟙_ C))))
include h

/-- If the endomorphisms of the tensor unit are scalars, the left trace is multiplicative. -/
theorem leftTrace_tensorHom_eq_comp_of_surjective {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (f ⊗ₘ g) = leftTrace f ≫ leftTrace g :=
  leftTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ Y)

/-- If the endomorphisms of the tensor unit are scalars, the right trace is multiplicative. -/
theorem rightTrace_tensorHom_eq_comp_of_surjective {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (f ⊗ₘ g) = rightTrace f ≫ rightTrace g :=
  rightTrace_tensorHom_eq_comp f g
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ X)

/-- If the endomorphisms of the tensor unit are scalars, the left dimension is multiplicative. -/
theorem leftDim_tensor_eq_comp_of_surjective (X Y : C) :
    leftDim (X ⊗ Y) = leftDim X ≫ leftDim Y :=
  leftDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ Y)

/-- If the endomorphisms of the tensor unit are scalars, the right dimension is multiplicative. -/
theorem rightDim_tensor_eq_comp_of_surjective (X Y : C) :
    rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y :=
  rightDim_tensor_eq_comp X Y
    (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_surjective h _ X)

end ScalarUnit

end TauCeti
