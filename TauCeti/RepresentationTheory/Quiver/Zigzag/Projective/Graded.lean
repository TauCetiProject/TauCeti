/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.QHom

/-!
# Zigzag vertex projectives in the graded-module category

The path-length grading restricted to `Z e_i` is an internal direct sum, not just a family of
subspaces. This makes each vertex projective an object of `TauCeti.GradedModuleCat`, and its
ungraded projectivity implies categorical projectivity. Internal shifts use `(P{d})_p = P_{p-d}`.

The categorical space `Hom(P_i, P_j{d})` is linearly equivalent to the homogeneous-map submodule
already computed for the zigzag projectives. When the graph has no isolated vertices
(`∀ i, ∃ j, G.Adj i j`), its Laurent support is finite, and its target-shift graded dimension is
exactly `TauCeti.zigzagProjectiveQHom`. Thus the quantum Cartan entries are
actual graded categorical Hom dimensions, ready for projective Euler evaluation.

These constructions concern the relation quotient. On a component with an edge it is the ordinary
zigzag algebra; singleton components of the public algebra instead use dual numbers.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Section 3.
* Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
* Năstăsescu--Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for projectivity in the
  graded-module category.
-/

public section

namespace TauCeti

open CategoryTheory

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- The vertex projective is a homogeneous submodule of the regular module: homogeneous
projection preserves the fixed-point equation `x * e_i = x`. -/
theorem isHomogeneous_zigzagProjective
    [DirectSum.Decomposition (zigzagIntegerGrade k G)] (i : V) :
    DirectSum.SetLike.IsHomogeneous (zigzagIntegerGrade k G)
      ((zigzagProjective k G i).restrictScalars k) := by
  have he : zigzagVertexIdempotent k G i ∈ zigzagIntegerGrade k G 0 := by
    -- Normalize the integer zero to the cast required by the extension-by-zero lemma.
    rw [show (0 : ℤ) = (0 : ℕ) from rfl, zigzagIntegerGrade_ofNat]
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)
  have hm : LinearMap.IsHomogeneous (LinearMap.mulRight k (zigzagVertexIdempotent k G i))
      (zigzagIntegerGrade k G) (zigzagIntegerGrade k G) 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx => mul_mem_zigzagIntegerGrade k G hx he
  intro p x hx
  rw [Submodule.restrictScalars_mem, mem_zigzagProjective_iff] at hx ⊢
  have h := hm.map_decompose p x
  rw [Int.add_zero] at h
  simpa only [LinearMap.mulRight_apply, hx] using h

/-- The restricted grading of `Z e_i` is an internal direct sum. -/
theorem isInternal_zigzagProjectiveGrade (i : V) :
    DirectSum.IsInternal (zigzagProjectiveGrade k G i) := by
  classical
  let _ := (isInternal_zigzagIntegerGrade k G).chooseDecomposition
  exact DirectSum.isInternal_comap (zigzagIntegerGrade k G) _
    ((zigzagProjective k G i).restrictScalars k).subtype Subtype.val_injective
    (fun _ _ => mem_zigzagProjectiveGrade_iff k G) fun p x =>
      ⟨⟨_, isHomogeneous_zigzagProjective k G i p x.2⟩, rfl⟩

/-- The graded left vertex projective `Z e_i`, with its induced path-length grading.
This is an abbreviation so its carrier and module structures remain those of the principal ideal. -/
noncomputable abbrev zigzagGradedProjective (i : V) :
    GradedModuleCat.{max u w} (zigzagIntegerGrade k G) where
  carrier := zigzagProjective k G i
  isAddCommGroup := Submodule.addCommGroup _
  isModule := Submodule.module _
  isModuleBase := Submodule.module' _
  grading := ⟨zigzagProjectiveGrade k G i, isInternal_zigzagProjectiveGrade k G i⟩
  gradedSMul := ⟨fun {_ _} _ _ ha hx =>
    (mem_zigzagProjectiveGrade_iff k G).2
      (mul_mem_zigzagIntegerGrade k G ha ((mem_zigzagProjectiveGrade_iff k G).1 hx))⟩

/-- The grading of the categorical projective is the restricted path-length grading. -/
@[simp]
theorem zigzagGradedProjective_piece (i : V) (p : ℤ) :
    (zigzagGradedProjective k G i).grading.piece p = zigzagProjectiveGrade k G i p :=
  (rfl)

-- This is not a simp lemma: `InternalGrading.shift_piece` already gives the unshifted normal form.
/-- Shifting the categorical projective agrees with the previously defined projective shift. -/
theorem zigzagGradedProjective_shift_piece (i : V) (d p : ℤ) :
    ((zigzagGradedProjective k G i).shiftObj d).grading.piece p =
      zigzagProjectiveShiftGrade k G i d p := by
  rw [InternalGrading.shift_piece, zigzagGradedProjective_piece,
    zigzagProjectiveShiftGrade_apply, sub_eq_add_neg]

/-- Every internally shifted vertex projective is projective in the graded-module category. -/
instance projective_zigzagGradedProjective_shift (i : V) (d : ℤ) :
    Projective ((zigzagGradedProjective k G i).shiftObj d) := by
  let _ := (isInternal_zigzagIntegerGrade k G).chooseDecomposition
  have := zigzagProjective_projective k G i
  exact GradedModuleCat.projective_of_module_projective _

/-- The vertex projective is projective in the graded-module category. -/
instance projective_zigzagGradedProjective (i : V) :
    Projective (zigzagGradedProjective k G i) := by
  let _ := (isInternal_zigzagIntegerGrade k G).chooseDecomposition
  have := zigzagProjective_projective k G i
  exact GradedModuleCat.projective_of_module_projective _

/-- Categorical graded maps `P_i → P_j{d}` are exactly the homogeneous maps in
`zigzagProjectiveTargetShiftHom`. The equivalence does not change the underlying linear map. -/
noncomputable def zigzagGradedProjectiveHomEquiv (i j : V) (d : ℤ) :
    ((zigzagGradedProjective k G i) ⟶ (zigzagGradedProjective k G j).shiftObj d) ≃ₗ[k]
      zigzagProjectiveTargetShiftHom k G i j d where
  toFun f := ⟨f.hom, by
    rw [mem_zigzagProjectiveTargetShiftHom_iff_isHomogeneous, LinearMap.isHomogeneous_def]
    intro p x hx
    have h := f.isHomogeneous.map_mem hx
    rw [zigzagGradedProjective_shift_piece, zigzagProjectiveShiftGrade_apply] at h
    simpa only [Int.add_zero, sub_eq_add_neg] using h⟩
  invFun f := GradedModuleCat.ofHom f.1 <| LinearMap.isHomogeneous_def.2 fun p x hx => by
    rw [zigzagGradedProjective_shift_piece, zigzagProjectiveShiftGrade_apply]
    simpa only [sub_eq_add_neg, add_zero] using
      ((mem_zigzagProjectiveTargetShiftHom_iff_isHomogeneous k G).1 f.2).map_mem hx
  left_inv _ := GradedModuleCat.hom_ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem coe_zigzagGradedProjectiveHomEquiv_apply {i j : V} {d : ℤ}
    (f : (zigzagGradedProjective k G i) ⟶ (zigzagGradedProjective k G j).shiftObj d) :
    (zigzagGradedProjectiveHomEquiv k G i j d f).1 = f.hom :=
  (rfl)

@[simp]
theorem hom_zigzagGradedProjectiveHomEquiv_symm_apply {i j : V} {d : ℤ}
    (f : zigzagProjectiveTargetShiftHom k G i j d) :
    ((zigzagGradedProjectiveHomEquiv k G i j d).symm f).hom = f.1 :=
  (rfl)

/-- Categorical shifted Hom spaces have the dimensions computed by the corner dictionary. -/
theorem finrank_zigzagGradedProjective_hom (i j : V) (d : ℤ) :
    Module.finrank k
      ((zigzagGradedProjective k G i) ⟶ (zigzagGradedProjective k G j).shiftObj d) =
      Module.finrank k (zigzagProjectiveTargetShiftHom k G i j d) :=
  (zigzagGradedProjectiveHomEquiv k G i j d).finrank_eq

/-- The categorical shifted Hom family has finite Laurent support. No cohomological vanishing
assumption is needed to define its q-Hom polynomial. -/
theorem hasFiniteLaurentSupport_zigzagGradedProjective_hom
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    HasFiniteLaurentSupport k
      (fun d : ℤ => (zigzagGradedProjective k G i) ⟶
        (zigzagGradedProjective k G j).shiftObj d) :=
  (hasFiniteLaurentSupport_zigzagProjectiveTargetShiftHom k G hns i j).of_equiv
    (fun d => (zigzagGradedProjectiveHomEquiv k G i j d).symm)

/-- The q-Hom polynomial already computed from homogeneous maps is the target-shift graded
dimension of the categorical Hom spaces. -/
theorem targetShiftGradedDimension_zigzagGradedProjective_hom
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    targetShiftGradedDimension k
      (fun d : ℤ => (zigzagGradedProjective k G i) ⟶
        (zigzagGradedProjective k G j).shiftObj d)
      (hasFiniteLaurentSupport_zigzagGradedProjective_hom k G hns i j) =
        zigzagProjectiveQHom k G hns i j := by
  rw [← targetShiftGradedDimension_equiv
    (hasFiniteLaurentSupport_zigzagProjectiveTargetShiftHom k G hns i j)
    (fun d => (zigzagGradedProjectiveHomEquiv k G i j d).symm)]
  -- The q-Hom definition is opaque across modules, so use its public coefficient formula.
  ext n
  rw [coeff_targetShiftGradedDimension, coeff_zigzagProjectiveQHom]

end TauCeti
