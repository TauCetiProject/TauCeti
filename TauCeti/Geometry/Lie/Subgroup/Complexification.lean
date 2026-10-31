/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
import TauCeti.LinearAlgebra.Complex.RealForm

/-!
# The complexified Lie algebras of the unitary and special unitary groups

The complexifications of the compact groups `U(n)` and `SU(n)` are `GL(n, ℂ)` and `SL(n, ℂ)`.
This file proves the Lie algebra half of these identifications: `𝔲(n)` and `𝔰𝔲(n)` are real
forms of `𝔤𝔩(n, ℂ)` and `𝔰𝔩(n, ℂ)`:

`𝔲(n) ⊗_ℝ ℂ ≅ 𝔤𝔩(n, ℂ)` and `𝔰𝔲(n) ⊗_ℝ ℂ ≅ 𝔰𝔩(n, ℂ)`,

as complex Lie algebras, by `c ⊗ X ↦ c • X`.  Here the Lie algebras of the subgroups
`unitarySubgroup (Matrix n n ℂ)ˣ` and `TauCeti.GLSpecialUnitary n ℂ` of the Lie group
`(Matrix n n ℂ)ˣ = GL(n, ℂ)` are those assigned by `TauCeti.Lie.lieSubalgebraOfSubgroup`, read in
matrix coordinates through `TauCeti.Lie.unitsLieAlgebraLieEquiv`, and `𝔤𝔩(n, ℂ)` is
`Matrix n n ℂ` with its commutator bracket.

The Lie algebra of `U(n)` is the skew-Hermitian matrices
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`),
so the first statement is the general fact that the skew-adjoint elements of a complex star module
are a real form of it (`LinearMap.isBaseChange_complex_of_star_eq_neg`): every complex matrix is
uniquely `X + i Y` with `X` and `Y` skew-Hermitian.  The Lie algebra of `SU(n)` is the trace-free
skew-Hermitian matrices, and the trace-free matrices are closed under the conjugate transpose, so
the second statement is the same fact for a star-closed subspace
(`LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`).

The statements are made for matrices rather than for a general complex star algebra because the
general linear Lie group uses the entrywise real structure of `Matrix n n ℂ`, which is not
syntactically the real structure `Module.complexToReal` restricted from its complex structure.

## Main results

* `TauCeti.Lie.isBaseChange_complex_unitarySubgroup`: the matrix coordinates exhibit
  `𝔤𝔩(n, ℂ)` as the complexification of the Lie algebra of `U(n)`.
* `TauCeti.Lie.unitaryComplexificationLieEquiv`: **the complex Lie algebra isomorphism
  `𝔲(n) ⊗_ℝ ℂ ≃ 𝔤𝔩(n, ℂ)`**, with `TauCeti.Lie.unitaryComplexificationLieEquiv_tmul` and
  `TauCeti.Lie.unitaryComplexificationLieEquiv_symm_apply`.
* `TauCeti.Lie.isBaseChange_complex_GLSpecialUnitary`: the matrix coordinates exhibit
  `𝔰𝔩(n, ℂ)` as the complexification of the Lie algebra of `SU(n)`.
* `TauCeti.Lie.specialUnitaryComplexificationLieEquiv`: **the complex Lie algebra isomorphism
  `𝔰𝔲(n) ⊗_ℝ ℂ ≃ 𝔰𝔩(n, ℂ)`**, with
  `TauCeti.Lie.coe_specialUnitaryComplexificationLieEquiv_tmul` and
  `TauCeti.Lie.specialUnitaryComplexificationLieEquiv_symm_apply`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section I.8 (complexifications of Lie algebras and the examples `𝔲(n)` and `𝔰𝔲(n)`).
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer, 2015, Section 3.6.
-/

public section

open Complex Manifold TensorProduct
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

variable (n : Type*) [Fintype n] [DecidableEq n]

/-! ### The unitary group -/

/-- **`𝔤𝔩(n, ℂ)` is the complexification of the Lie algebra of `U(n)`.**  The matrix coordinates of
the Lie algebra of the unitary group exhibit `Matrix n n ℂ` as its base change from `ℝ` to `ℂ`:
every complex matrix is uniquely `X + i Y` with `X` and `Y` in the Lie algebra of `U(n)`. -/
theorem isBaseChange_complex_unitarySubgroup :
    IsBaseChange ℂ (((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) :
        LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (Matrix n n ℂ)ˣ →ₗ⁅ℝ⁆ Matrix n n ℂ).comp
          (lieSubalgebraOfSubgroup (unitarySubgroup (Matrix n n ℂ)ˣ)).incl :
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (Matrix n n ℂ)ˣ)
          →ₗ⁅ℝ⁆ Matrix n n ℂ) :
      lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (Matrix n n ℂ)ˣ)
        →ₗ[ℝ] Matrix n n ℂ) := by
  refine LinearMap.isBaseChange_complex_of_star_eq_neg _
    ((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).injective.comp Subtype.val_injective)
    (fun X ↦ ?_) (fun A hA ↦ ?_)
  · have hX := X.2
    rw [← (unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).symm_apply_apply X.1,
      unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg] at hX
    exact hX
  · refine ⟨⟨(unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).symm A, ?_⟩, ?_⟩
    · rwa [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]
    · simp

/-- **The complexification of the Lie algebra of `U(n)` is `𝔤𝔩(n, ℂ)`**: the isomorphism of
complex Lie algebras from the Lie algebra of the unitary group with scalars extended to `ℂ` onto
`Matrix n n ℂ`, sending `c ⊗ X` to `c` times the matrix coordinates of `X`. -/
def unitaryComplexificationLieEquiv :
    ℂ ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (Matrix n n ℂ)ˣ)
      ≃ₗ⁅ℂ⁆ Matrix n n ℂ :=
  (isBaseChange_complex_unitarySubgroup n).lieEquiv

@[simp]
theorem unitaryComplexificationLieEquiv_tmul (c : ℂ)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (Matrix n n ℂ)ˣ)) :
    unitaryComplexificationLieEquiv n (c ⊗ₜ[ℝ] X) =
      c • unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _) :=
  (isBaseChange_complex_unitarySubgroup n).lieEquiv_tmul c X

theorem unitaryComplexificationLieEquiv_symm_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (Matrix n n ℂ)ˣ)) :
    (unitaryComplexificationLieEquiv n).symm
        (unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _)) =
      1 ⊗ₜ[ℝ] X :=
  (isBaseChange_complex_unitarySubgroup n).lieEquiv_symm_apply X

/-! ### The special unitary group -/

/-- The matrix coordinates of the Lie algebra of `SU(n)`, as a homomorphism of real Lie algebras
into `𝔤𝔩(n, ℂ)`. -/
private abbrev specialUnitaryToMatrix :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
        (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ) →ₗ⁅ℝ⁆ Matrix n n ℂ :=
  (unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) :
      LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (Matrix n n ℂ)ˣ →ₗ⁅ℝ⁆ Matrix n n ℂ).comp
    (lieSubalgebraOfSubgroup (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)).incl

/-- A matrix lies in the Lie algebra of `SU(n)`, in matrix coordinates, exactly when it is
skew-Hermitian and trace-free. -/
private theorem exists_specialUnitaryToMatrix_eq_iff (A : Matrix n n ℂ) :
    (∃ X, specialUnitaryToMatrix n X = A) ↔ Aᴴ = -A ∧ A.trace = 0 := by
  rw [← unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff]
  constructor
  · rintro ⟨X, rfl⟩
    have hX := X.2
    rwa [← (unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).symm_apply_apply X.1] at hX
  · intro hA
    exact ⟨⟨_, hA⟩, by simp⟩

/-- The matrix coordinates of an element of the Lie algebra of `SU(n)` are trace-free. -/
theorem unitsLieAlgebraLieEquiv_coe_mem_sl
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _) ∈
      LieAlgebra.SpecialLinear.sl n ℂ :=
  LieAlgebra.SpecialLinear.mem_sl_iff.2 ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨X, rfl⟩).2

/-- **`𝔰𝔩(n, ℂ)` is the complexification of the Lie algebra of `SU(n)`.**  The matrix coordinates
of the Lie algebra of the special unitary group, with values in the trace-free matrices, exhibit
`𝔰𝔩(n, ℂ)` as its base change from `ℝ` to `ℂ`: the trace-free matrices are closed under the
conjugate transpose, and their skew-Hermitian elements are the Lie algebra of `SU(n)`
(`LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`). -/
theorem isBaseChange_complex_GLSpecialUnitary :
    IsBaseChange ℂ (LinearMap.codRestrict
      ((LieAlgebra.SpecialLinear.sl n ℂ).toSubmodule.restrictScalars ℝ)
      (((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) :
          LeftInvariantDerivation 𝓘(ℝ, Matrix n n ℂ) (Matrix n n ℂ)ˣ →ₗ⁅ℝ⁆ Matrix n n ℂ).comp
            (lieSubalgebraOfSubgroup (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)).incl :
          lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
            (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ) →ₗ⁅ℝ⁆ Matrix n n ℂ) :
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
          (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ) →ₗ[ℝ] Matrix n n ℂ)
      (unitsLieAlgebraLieEquiv_coe_mem_sl n)) := by
  refine LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg _ (fun A hA ↦ ?_) _
    (fun X Y h ↦ Subtype.ext ((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).injective h))
    (fun X ↦ ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨X, rfl⟩).1) fun A hA hskew ↦ ?_
  · rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.SpecialLinear.mem_sl_iff] at hA ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hA, star_zero]
  · rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.SpecialLinear.mem_sl_iff] at hA
    exact (exists_specialUnitaryToMatrix_eq_iff n A).2 ⟨hskew, hA⟩

/-- The complexified matrix coordinates of the Lie algebra of `SU(n)` are those of
`TauCeti.Lie.isBaseChange_complex_GLSpecialUnitary`, read in `𝔤𝔩(n, ℂ)`. -/
private theorem coe_liftBaseChange_specialUnitary
    (u : ℂ ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    (((specialUnitaryToMatrix n : _ →ₗ[ℝ] Matrix n n ℂ).codRestrict
        ((LieAlgebra.SpecialLinear.sl n ℂ).toSubmodule.restrictScalars ℝ)
        (unitsLieAlgebraLieEquiv_coe_mem_sl n)).liftBaseChange ℂ u : Matrix n n ℂ) =
      (specialUnitaryToMatrix n).liftBaseChange ℂ u := by
  induction u with
  | tmul c X => rw [LinearMap.liftBaseChange_tmul, LieHom.liftBaseChange_tmul]; rfl
  | add u v hu hv => simp only [map_add, Submodule.coe_add, hu, hv]

/-- The complexified inclusion of the Lie algebra of `SU(n)` into `𝔤𝔩(n, ℂ)` is injective. -/
private theorem liftBaseChange_specialUnitary_injective :
    Function.Injective ((specialUnitaryToMatrix n).liftBaseChange ℂ) := fun u v h ↦
  (isBaseChange_complex_GLSpecialUnitary n).liftBaseChange_injective
    (Subtype.ext (by simpa only [coe_liftBaseChange_specialUnitary] using h))

/-- The complexified inclusion of the Lie algebra of `SU(n)` into `𝔤𝔩(n, ℂ)` has image
`𝔰𝔩(n, ℂ)`. -/
private theorem range_liftBaseChange_specialUnitary :
    ((specialUnitaryToMatrix n).liftBaseChange ℂ).range = LieAlgebra.SpecialLinear.sl n ℂ := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact coe_liftBaseChange_specialUnitary n u ▸ Subtype.prop _
  · intro hA
    obtain ⟨u, hu⟩ := (isBaseChange_complex_GLSpecialUnitary n).liftBaseChange_bijective.2 ⟨A, hA⟩
    exact ⟨u, (coe_liftBaseChange_specialUnitary n u).symm.trans (congrArg Subtype.val hu)⟩

/-- **The complexification of the Lie algebra of `SU(n)` is `𝔰𝔩(n, ℂ)`**: the isomorphism of
complex Lie algebras from the Lie algebra of the special unitary group with scalars extended to
`ℂ` onto the trace-free matrices, sending `c ⊗ X` to `c` times the matrix coordinates of `X`. -/
def specialUnitaryComplexificationLieEquiv :
    ℂ ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
        (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ) ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl n ℂ :=
  (LieEquiv.ofInjective _ (liftBaseChange_specialUnitary_injective n)).trans
    (LieEquiv.ofEq _ _ (by rw [range_liftBaseChange_specialUnitary]))

@[simp]
theorem coe_specialUnitaryComplexificationLieEquiv_tmul (c : ℂ)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    (specialUnitaryComplexificationLieEquiv n (c ⊗ₜ[ℝ] X) : Matrix n n ℂ) =
      c • unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _) := by
  simp [specialUnitaryComplexificationLieEquiv]

/-- The inverse isomorphism sends the matrix coordinates of `X` back to `1 ⊗ X`. -/
theorem specialUnitaryComplexificationLieEquiv_symm_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    (specialUnitaryComplexificationLieEquiv n).symm
        ⟨unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _),
          unitsLieAlgebraLieEquiv_coe_mem_sl n X⟩ =
      1 ⊗ₜ[ℝ] X := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_specialUnitaryComplexificationLieEquiv_tmul, one_smul])

end TauCeti.Lie
