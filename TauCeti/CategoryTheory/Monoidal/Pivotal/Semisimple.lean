/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Simple
public import TauCeti.CategoryTheory.Semisimple.OppositePairing
import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
import TauCeti.CategoryTheory.Monoidal.Pivotal.Nondegenerate

/-!
# Pivotal structures on finite semisimple categories

In a finite semisimple rigid category every object is a finite biproduct of simple objects, so
pivotal structures and their traces are controlled by what happens on simple objects.

* A pivotal structure is a natural isomorphism out of the identity functor, so two pivotal
  structures whose components agree at every simple object are equal.
* Over an algebraically closed field `k`, two pivotal structures `P` and `Q` differ at a simple
  object `X` by an automorphism of `X`, which is a scalar `c`, and the left dimension of `X` for
  `P` is `c` times its left dimension for `Q`. So two pivotal structures with the same nonzero
  left dimensions at every simple object are equal.
* Every endomorphism of a biproduct of simple objects has trace equal to the sum of the scalars of
  its diagonal components times the dimensions of the summands. So a pivotal structure is spherical
  exactly when the left and right dimensions of every simple object agree.
* When `𝟙_ C` is simple, comparing a pivotal structure at a split simple `X` with
  `TauCeti.simpleDoubleDualIso X` gives `η_ X Xᘁ ≫ ε'_X = leftDim X ≫ rightDim X` and expresses
  `simpleDoubleDualIso X` and `simpleOppositeExactPairing X` as scalar multiples of `pivotalIsoApp`
  and `pivotalExactPairing` by `leftDim X` and its inverse.

## Main results

* `TauCeti.PivotalCategory.ext_of_simple`: pivotal structures agreeing on simple objects are
  equal.
* `TauCeti.PivotalCategory.ext_of_leftDim`: pivotal structures with the same nonzero left
  dimensions on simple objects are equal.
* `TauCeti.sphericalCategory_iff_leftDim_eq_rightDim`: a pivotal structure is spherical if and
  only if its left and right dimensions agree on simple objects.
* `TauCeti.leftTrace_pivotalIsoApp_hom_comp_simpleDoubleDualIso_inv`,
  `TauCeti.coevaluation_comp_simpleOppositeExactPairing_evaluation`,
  `TauCeti.simpleDoubleDualIso_hom_eq_smul_pivotalIsoApp_hom`,
  `TauCeti.simpleDoubleDualIso_inv_eq_smul_pivotalIsoApp_inv`,
  `TauCeti.simpleOppositeExactPairing_evaluation_eq_smul`, and
  `TauCeti.simpleOppositeExactPairing_coevaluation_eq_smul`: comparisons between
  `simpleOppositeExactPairing X` and the pivotal pairing on a split simple object `X`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C]

namespace PivotalCategory

/-- In a finite semisimple rigid category, two pivotal structures whose pivotal isomorphisms agree
at every simple object are equal. -/
theorem ext_of_simple {P Q : PivotalCategory C}
    (h : ∀ (X : C) [Simple X],
      (@pivotalIsoApp C _ _ _ P X).hom = (@pivotalIsoApp C _ _ _ Q X).hom) :
    P = Q := by
  ext : 1
  refine Iso.ext (natTrans_ext_of_simple fun X _ ↦ ?_)
  rw [@pivotalIso_hom_app C _ _ _ P, @pivotalIso_hom_app C _ _ _ Q, h]

variable (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include k in
/-- Over an algebraically closed field, two pivotal structures `P` and `Q` on a finite semisimple
rigid category are equal if every simple object has the same left dimension for `P` as for `Q`,
and that dimension is nonzero. -/
theorem ext_of_leftDim {P Q : PivotalCategory C}
    (h : ∀ (X : C) [Simple X], @leftDim C _ _ _ P X = @leftDim C _ _ _ Q X)
    (h₀ : ∀ (X : C) [Simple X], @leftDim C _ _ _ Q X ≠ 0) :
    P = Q := by
  refine ext_of_simple fun X _ ↦ ?_
  let _ := Q
  -- The left dimension of `X` for `P` is the scalar `c` of the automorphism `ψ_X ≫ φ_X⁻¹` of `X`
  -- times the left dimension for `Q`, where `φ` and `ψ` are the pivotal isomorphisms of `P` and
  -- `Q`. The hypotheses force `c = 1`.
  have hc : endAlgEquivOfSimple k X
      (End.of ((pivotalIsoApp X).hom ≫ (@pivotalIsoApp C _ _ _ P X).inv)) = 1 := by
    refine smul_left_injective k (h₀ X) ?_
    dsimp only
    rw [one_smul, ← leftTrace_eq_smul_leftDim, ← leftDim_eq_leftTrace, h]
  rw [endAlgEquivOfSimple_apply_eq_iff, one_smul] at hc
  exact ((Iso.comp_inv_eq_id _).1 hc).symm

end PivotalCategory

section Spherical

variable (k : Type w) [Field k] [IsAlgClosed k] [PivotalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include k in
/-- Over an algebraically closed field, a pivotal structure on a finite semisimple rigid category
is spherical if and only if the left and right dimensions of every simple object agree. -/
theorem sphericalCategory_iff_leftDim_eq_rightDim :
    SphericalCategory C ↔ ∀ (X : C) [Simple X], leftDim X = rightDim X := by
  refine ⟨fun _ X _ ↦ leftDim_eq_rightDim X, fun h ↦ ⟨fun {X} f ↦ ?_⟩⟩
  obtain ⟨ι, hι, g, hg, hbg, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  -- Conjugate `f` to an endomorphism of `⨁ g` and compare the traces of its diagonal components,
  -- which are endomorphisms of simple objects.
  rw [← leftTrace_conj e, ← rightTrace_conj e, leftTrace_biproduct, rightTrace_biproduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [leftTrace_eq_smul_leftDim k, rightTrace_eq_smul_rightDim k, h]

end Spherical

section OppositePairing

/-- For any simple object `X` in a finite semisimple pivotal category with simple tensor unit,
the left trace of `(pivotalIsoApp X).hom ≫ (simpleDoubleDualIso X).inv` is `𝟙 (𝟙_ C)`. -/
theorem leftTrace_pivotalIsoApp_hom_comp_simpleDoubleDualIso_inv [PivotalCategory C]
    [MonoidalPreadditive C] [Simple (𝟙_ C)] (X : C) [Simple X] :
    leftTrace ((pivotalIsoApp X).hom ≫ (simpleDoubleDualIso X).inv) = 𝟙 (𝟙_ C) := by
  rw [leftTrace_eq_pivotalIsoApp, ← whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc,
    coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation]

variable (k : Type w) [Field k] [IsAlgClosed k] [PivotalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [Simple (𝟙_ C)]
variable (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)]

include k in
/-- For a split simple object `X` in a finite semisimple pivotal category with simple tensor unit,
composing `η_ X Xᘁ` with the evaluation of `TauCeti.simpleOppositeExactPairing X` computes the
squared dimension `leftDim X ≫ rightDim X`. -/
@[reassoc]
theorem coevaluation_comp_simpleOppositeExactPairing_evaluation :
    η_ X Xᘁ ≫ @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      leftDim X ≫ rightDim X := by
  rw [← squaredNorm_simpleDoubleDualIso,
    squaredNorm_congr k (bijective_algebraMap_end_of_simple k X).surjective _ (pivotalIsoApp X),
    squaredNorm_pivotalIsoApp]

section Scalar

variable [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]

/-- `(simpleDoubleDualIso X).inv` is `(leftDim X)⁻¹` times `(pivotalIsoApp X).inv`. -/
theorem simpleDoubleDualIso_inv_eq_smul_pivotalIsoApp_inv :
    (simpleDoubleDualIso X).inv =
      (endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)))⁻¹ • (pivotalIsoApp X).inv := by
  set c := endAlgEquivOfSimple k X (End.of ((pivotalIsoApp X).hom ≫ (simpleDoubleDualIso X).inv))
  have hc : (pivotalIsoApp X).hom ≫ (simpleDoubleDualIso X).inv = c • 𝟙 X :=
    (endAlgEquivOfSimple_smul_id (k := k) _).symm
  have hcd : c * endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)) = 1 := by
    have h1 := congrArg (endAlgEquivOfSimple k (𝟙_ C) ∘ End.of)
      (leftTrace_pivotalIsoApp_hom_comp_simpleDoubleDualIso_inv X)
    simpa [leftTrace_eq_smul_leftDim k, smul_eq_mul] using h1
  rw [← eq_inv_of_mul_eq_one_left hcd,
    ← Iso.inv_hom_id_assoc (pivotalIsoApp X) (simpleDoubleDualIso X).inv, hc, Linear.comp_smul,
    Category.comp_id]

/-- `(simpleDoubleDualIso X).hom` is `leftDim X` times `(pivotalIsoApp X).hom`. -/
theorem simpleDoubleDualIso_hom_eq_smul_pivotalIsoApp_hom :
    (simpleDoubleDualIso X).hom =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)) • (pivotalIsoApp X).hom := by
  set d := endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X))
  have hd : d ≠ 0 := fun hd0 ↦
    leftDim_ne_zero_of_surjective (Simple.not_isZero X)
      (bijective_algebraMap_end_of_simple k X).surjective
      (by simpa [d] using (endAlgEquivOfSimple_apply_eq_iff (End.of (leftDim X)) 0).1 hd0)
  rw [← Category.comp_id (simpleDoubleDualIso X).hom, ← Iso.inv_hom_id (pivotalIsoApp X),
    ← one_smul k (pivotalIsoApp X).inv, ← mul_inv_cancel₀ hd, mul_smul,
    ← simpleDoubleDualIso_inv_eq_smul_pivotalIsoApp_inv k X, Linear.smul_comp, Linear.comp_smul,
    Iso.hom_inv_id_assoc]

/-- The coevaluation of `TauCeti.simpleOppositeExactPairing X` is `(leftDim X)⁻¹` times the
coevaluation of `TauCeti.pivotalExactPairing X`. -/
theorem simpleOppositeExactPairing_coevaluation_eq_smul :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)))⁻¹ •
        @ExactPairing.coevaluation C _ _ Xᘁ X (pivotalExactPairing X) := by
  rw [simpleOppositeExactPairing_coevaluation, pivotalExactPairing_coevaluation,
    simpleDoubleDualIso_inv_eq_smul_pivotalIsoApp_inv k X, MonoidalLinear.whiskerLeft_smul,
    Linear.comp_smul]

/-- The evaluation of `TauCeti.simpleOppositeExactPairing X` is `leftDim X` times the evaluation of
`TauCeti.pivotalExactPairing X`. -/
theorem simpleOppositeExactPairing_evaluation_eq_smul :
    @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)) •
        @ExactPairing.evaluation C _ _ Xᘁ X (pivotalExactPairing X) := by
  rw [simpleOppositeExactPairing_evaluation, pivotalExactPairing_evaluation,
    simpleDoubleDualIso_hom_eq_smul_pivotalIsoApp_hom k X, MonoidalLinear.smul_whiskerRight,
    Linear.smul_comp]

end Scalar

end OppositePairing

end TauCeti
