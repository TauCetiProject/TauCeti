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
skew-Hermitian matrices, and the same decomposition of a trace-free matrix has trace-free parts.

The statements are made for matrices rather than for a general complex star algebra because the
general linear Lie group uses the entrywise real structure of `Matrix n n ℂ`, which is not
syntactically the real structure `Module.complexToReal` restricted from its complex structure.

## Main results

* `TauCeti.Lie.isBaseChange_complex_unitarySubgroup`: the matrix coordinates exhibit
  `𝔤𝔩(n, ℂ)` as the complexification of the Lie algebra of `U(n)`.
* `TauCeti.Lie.unitaryComplexificationLieEquiv`: **the complex Lie algebra isomorphism
  `𝔲(n) ⊗_ℝ ℂ ≃ 𝔤𝔩(n, ℂ)`**, with `TauCeti.Lie.unitaryComplexificationLieEquiv_tmul` and
  `TauCeti.Lie.unitaryComplexificationLieEquiv_symm_apply`.
* `TauCeti.Lie.specialUnitaryComplexificationLieEquiv`: **the complex Lie algebra isomorphism
  `𝔰𝔲(n) ⊗_ℝ ℂ ≃ 𝔰𝔩(n, ℂ)`.**

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

/-- The complexified inclusion of the Lie algebra of `SU(n)` into `𝔤𝔩(n, ℂ)` is injective: the
Lie algebra of `SU(n)` consists of skew-Hermitian matrices, and such matrices `X`, `Y` satisfy
`X + i Y = 0` only when both vanish. -/
private theorem liftBaseChange_specialUnitary_injective :
    Function.Injective ((specialUnitaryToMatrix n).liftBaseChange ℂ) := by
  rw [← LieHom.coe_toLinearMap, LieHom.coe_liftBaseChange]
  exact LinearMap.liftBaseChange_complex_injective_of_star_eq_neg _
    (fun X Y h ↦ Subtype.ext ((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).injective h))
    fun X ↦ ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨X, rfl⟩).1

/-- The complexified inclusion of the Lie algebra of `SU(n)` into `𝔤𝔩(n, ℂ)` has image
`𝔰𝔩(n, ℂ)`: a trace-free matrix `A` is `X + i Y` with `X = (A - Aᴴ) / 2` and
`Y = -i (A + Aᴴ) / 2`, both trace-free and skew-Hermitian. -/
private theorem range_liftBaseChange_specialUnitary :
    ((specialUnitaryToMatrix n).liftBaseChange ℂ).range = LieAlgebra.SpecialLinear.sl n ℂ := by
  rw [← LieSubalgebra.toSubmodule_inj, LieHom.range_toSubmodule, LieHom.coe_liftBaseChange]
  ext A
  rw [LinearMap.mem_range_liftBaseChange_complex_iff, LieSubalgebra.mem_toSubmodule,
    LieAlgebra.SpecialLinear.mem_sl_iff]
  constructor
  · rintro ⟨X, Y, rfl⟩
    have hX := ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨X, rfl⟩).2
    have hY := ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨Y, rfl⟩).2
    rw [LieHom.coe_toLinearMap, Matrix.trace_add, Matrix.trace_smul, hX, hY, smul_zero, add_zero]
  · intro hA
    obtain ⟨X, hX⟩ := (exists_specialUnitaryToMatrix_eq_iff n ((2⁻¹ : ℂ) • (A - Aᴴ))).2
      ⟨by simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, ← smul_neg],
        by simp [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, hA]⟩
    obtain ⟨Y, hY⟩ := (exists_specialUnitaryToMatrix_eq_iff n ((-(2⁻¹ * I)) • (A + Aᴴ))).2
      ⟨by simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm, ← smul_neg],
        by simp [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, hA]⟩
    refine ⟨X, Y, ?_⟩
    have hI : I * -(2⁻¹ * I) = (2⁻¹ : ℂ) := by
      rw [mul_neg, mul_left_comm, I_mul_I, mul_neg_one, neg_neg]
    rw [LieHom.coe_toLinearMap, hX, hY, smul_smul, hI]
    module

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

end TauCeti.Lie
