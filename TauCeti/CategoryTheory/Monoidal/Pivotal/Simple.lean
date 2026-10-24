/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
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

For an automorphism `a` of a simple object the scalars of `a⁻¹` and `a` cancel, so
`leftTrace a⁻¹ ≫ rightTrace a = leftDim X ≫ rightDim X`. Since changing the pivotal structure
changes the left dimension of `X` into the left trace of an automorphism `a⁻¹` and the right
dimension into the right trace of `a`, the product `leftDim X ≫ rightDim X` of the two dimensions
of a simple object does not depend on the pivotal structure, although each factor may.

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
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k f
  simp

/-- The right trace of an endomorphism of a simple object is its scalar times the right
dimension. -/
theorem rightTrace_eq_smul_rightDim (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X := by
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k f
  simp

/-- In a spherical category, the trace of an endomorphism of a simple object is its scalar times
the quantum dimension. -/
theorem trace_eq_smul_quantumDim [SphericalCategory C] (f : X ⟶ X) :
    trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X := by
  rw [trace_eq_leftTrace, leftTrace_eq_smul_leftDim k, quantumDim_eq_leftDim]

include k in
/-- For an automorphism `a` of a simple object, the left trace of `a⁻¹` followed by the right trace
of `a` is the left dimension followed by the right dimension: the scalars of `a⁻¹` and `a`
cancel. -/
theorem leftTrace_inv_comp_rightTrace_hom (a : X ≅ X) :
    leftTrace a.inv ≫ rightTrace a.hom = leftDim X ≫ rightDim X := by
  rw [leftTrace_eq_smul_leftDim k, rightTrace_eq_smul_rightDim k, Linear.smul_comp,
    Linear.comp_smul, smul_smul, ← map_mul, ← End.of_comp, Iso.hom_inv_id, End.of_id, map_one,
    one_smul]

section ChangeOfPivotal

omit [PivotalCategory C]

variable (P Q : PivotalCategory C)

include k in
/-- For a simple object `X`, the left dimension followed by the right dimension of `X` is the same
for any two pivotal structures `P` and `Q` on `C`, although each dimension separately may
change. -/
theorem leftDim_comp_rightDim_eq :
    @leftDim C _ _ _ P X ≫ @rightDim C _ _ _ P X =
      @leftDim C _ _ _ Q X ≫ @rightDim C _ _ _ Q X := by
  rw [leftDim_eq_leftTrace P Q, rightDim_eq_rightTrace P Q]
  -- Both dimensions for `P` are traces for `Q` of the automorphism `φ_X ≫ ψ_X⁻¹` of `X` and of
  -- its inverse, where `φ` and `ψ` are the pivotal isomorphisms of `P` and `Q`.
  exact @leftTrace_inv_comp_rightTrace_hom k _ _ C _ _ _ Q _ _ _ _ _ X _ _
    (@pivotalIsoApp C _ _ _ P X ≪≫ (@pivotalIsoApp C _ _ _ Q X).symm)

end ChangeOfPivotal

end TauCeti
