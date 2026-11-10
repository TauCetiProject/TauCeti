/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.SkewAdjoint.BaseChange
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
public import TauCeti.Geometry.Lie.Subgroup.Symplectic
import TauCeti.LinearAlgebra.Complex.RealForm

/-!
# The complexified Lie algebras of the classical matrix groups

The complexifications of the compact groups `U(n)`, `SU(n)` and `SO(n)` are `GL(n, ℂ)`,
`SL(n, ℂ)` and `SO(n, ℂ)`.  This file proves the Lie algebra half of these identifications:
`𝔲(n)`, `𝔰𝔲(n)` and `𝔰𝔬(n)` are real forms of `𝔤𝔩(n, ℂ)`, `𝔰𝔩(n, ℂ)` and `𝔰𝔬(n, ℂ)`:

`𝔲(n) ⊗_ℝ ℂ ≅ 𝔤𝔩(n, ℂ)`, `𝔰𝔲(n) ⊗_ℝ ℂ ≅ 𝔰𝔩(n, ℂ)` and `𝔰𝔬(n) ⊗_ℝ ℂ ≅ 𝔰𝔬(n, ℂ)`,

as complex Lie algebras, by `c ⊗ X ↦ c • X`.  The same holds for the noncompact real symplectic
group: `𝔰𝔭(2l, ℝ) ⊗_ℝ ℂ ≅ 𝔰𝔭(2l, ℂ)`.  Here the Lie algebra of a subgroup of the Lie group of units
`(Matrix n n 𝕜)ˣ = GL(n, 𝕜)` is the one assigned by `TauCeti.Lie.lieSubalgebraOfSubgroup`, read in
matrix coordinates through `TauCeti.Lie.unitsLieAlgebraLieEquiv`, and `𝔤𝔩(n, 𝕜)` is
`Matrix n n 𝕜` with its commutator bracket.

The unitary and special unitary groups are subgroups of `GL(n, ℂ)`.  The Lie algebra of `U(n)` is
the skew-Hermitian matrices
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`),
so the first statement is the general fact that the skew-adjoint elements of a complex star module
are a real form of it (`LinearMap.isBaseChange_complex_of_star_eq_neg`): every complex matrix is
uniquely `X + i Y` with `X` and `Y` skew-Hermitian.  The Lie algebra of `SU(n)` is the trace-free
skew-Hermitian matrices, and the trace-free matrices are closed under the conjugate transpose, so
the second statement is the same fact for a star-closed subspace
(`LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`).

The special orthogonal group `SO(n) = SU(n, ℝ)` and the real symplectic group are subgroups of
`GL(n, ℝ)`, and their Lie algebras are the real matrices skew-adjoint for a real matrix `J`: the
identity matrix for `𝔰𝔬(n)` and the standard symplectic matrix for `𝔰𝔭(2l, ℝ)`.  Extending scalars
from `ℝ` to any `ℝ`-algebra `S` turns the `J`-skew-adjoint real matrices into the `J`-skew-adjoint
matrices over `S` (`TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv`), so the Lie algebra of
such a group extends to `𝔰𝔬(n, S)` or `𝔰𝔭(2l, S)`; the complexifications are the case `S = ℂ`.

The unitary statements are made for matrices rather than for a general complex star algebra because
the general linear Lie group uses the entrywise real structure of `Matrix n n ℂ`, which is not
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
* `TauCeti.Lie.skewAdjointBaseChangeLieEquiv`: for a subgroup of `GL(m, ℝ)` whose Lie algebra is
  the `J`-skew-adjoint matrices, the isomorphism from its Lie algebra with scalars extended to `S`
  onto the `J`-skew-adjoint matrices over `S`.
* `TauCeti.Lie.specialOrthogonalBaseChangeLieEquiv`: **the Lie algebra isomorphism
  `S ⊗_ℝ 𝔰𝔬(n) ≃ 𝔰𝔬(n, S)`**, in particular `𝔰𝔬(n) ⊗_ℝ ℂ ≃ 𝔰𝔬(n, ℂ)`.
* `TauCeti.Lie.symplecticBaseChangeLieEquiv`: **the Lie algebra isomorphism
  `S ⊗_ℝ 𝔰𝔭(2l, ℝ) ≃ 𝔰𝔭(2l, S)`**, in particular `𝔰𝔭(2l, ℝ) ⊗_ℝ ℂ ≃ 𝔰𝔭(2l, ℂ)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section I.8 (complexifications of Lie algebras and the examples `𝔲(n)`, `𝔰𝔲(n)`, `𝔰𝔬(n)` and
  `𝔰𝔭(n, ℝ)`).
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
      (unitsLieAlgebraLieEquiv_coe_mem_sl (n := n))) := by
  refine LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg _ (fun A hA ↦ ?_) _
    (fun X Y h ↦ Subtype.ext ((unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).injective h))
    (fun X ↦ ((exists_specialUnitaryToMatrix_eq_iff n _).1 ⟨X, rfl⟩).1) fun A hA hskew ↦ ?_
  · rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.SpecialLinear.mem_sl_iff] at hA ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hA, star_zero]
  · rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.SpecialLinear.mem_sl_iff] at hA
    exact (exists_specialUnitaryToMatrix_eq_iff n A).2 ⟨hskew, hA⟩

/-- **The complexification of the Lie algebra of `SU(n)` is `𝔰𝔩(n, ℂ)`**: the isomorphism of
complex Lie algebras from the Lie algebra of the special unitary group with scalars extended to
`ℂ` onto the trace-free matrices, sending `c ⊗ X` to `c` times the matrix coordinates of `X`. -/
def specialUnitaryComplexificationLieEquiv :
    ℂ ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
        (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ) ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl n ℂ :=
  (isBaseChange_complex_GLSpecialUnitary n).lieEquivOfCodRestrict

@[simp]
theorem coe_specialUnitaryComplexificationLieEquiv_tmul (c : ℂ)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    (specialUnitaryComplexificationLieEquiv n (c ⊗ₜ[ℝ] X) : Matrix n n ℂ) =
      c • unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _) :=
  (isBaseChange_complex_GLSpecialUnitary n).coe_lieEquivOfCodRestrict_tmul c X

/-- The inverse isomorphism sends the matrix coordinates of `X` back to `1 ⊗ X`. -/
theorem specialUnitaryComplexificationLieEquiv_symm_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (GLSpecialUnitary n ℂ : Subgroup (Matrix n n ℂ)ˣ)) :
    (specialUnitaryComplexificationLieEquiv n).symm
        ⟨unitsLieAlgebraLieEquiv (R := Matrix n n ℂ) (X : LeftInvariantDerivation _ _),
          unitsLieAlgebraLieEquiv_coe_mem_sl X⟩ =
      1 ⊗ₜ[ℝ] X :=
  (isBaseChange_complex_GLSpecialUnitary n).lieEquivOfCodRestrict_symm_apply X

/-! ### Real matrix groups with skew-adjoint Lie algebras -/

section SkewAdjoint

variable {m : Type*} [Fintype m] [DecidableEq m] (S : Type*) [CommRing S] [Algebra ℝ S]

/-- **Extending the scalars of the Lie algebra of a real matrix group of skew-adjoint type.**  Let
`G` be a subgroup of `GL(m, ℝ)` whose Lie algebra, in matrix coordinates, consists of the matrices
skew-adjoint for a real matrix `J`.  For every `ℝ`-algebra `S`, extending the scalars of the Lie
algebra of `G` to `S` gives the Lie algebra of matrices over `S` skew-adjoint for `J`, by
`s ⊗ X ↦ s • X`.  For `S = ℂ` this exhibits the Lie algebra of `G` as a real form of the complex
Lie algebra of `J`-skew-adjoint matrices. -/
noncomputable def skewAdjointBaseChangeLieEquiv (G : Subgroup (Matrix m m ℝ)ˣ) (J : Matrix m m ℝ)
    (hG : ∀ A, (unitsLieAlgebraLieEquiv (R := Matrix m m ℝ)).symm A ∈
      lieSubalgebraOfSubgroup G ↔ A ∈ skewAdjointMatricesLieSubalgebra J) :
    S ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix m m ℝ)) G ≃ₗ⁅S⁆
      skewAdjointMatricesLieSubalgebra (J.map (algebraMap ℝ S)) :=
  (LieEquiv.baseChange S ((unitsLieAlgebraLieEquiv (R := Matrix m m ℝ)).ofSubalgebras _ _
    (LieSubalgebra.ext _ _ fun A ↦ by
      rw [LieSubalgebra.mem_map, ← hG]
      exact ⟨by rintro ⟨X, hX, rfl⟩; rwa [LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply],
        fun hA ↦ ⟨_, hA, LieEquiv.apply_symm_apply _ _⟩⟩))).trans
    (TauCeti.skewAdjointMatricesLieSubalgebraBaseChangeEquiv S J)

@[simp]
theorem coe_skewAdjointBaseChangeLieEquiv_tmul (G : Subgroup (Matrix m m ℝ)ˣ) (J : Matrix m m ℝ)
    (hG : ∀ A, (unitsLieAlgebraLieEquiv (R := Matrix m m ℝ)).symm A ∈
      lieSubalgebraOfSubgroup G ↔ A ∈ skewAdjointMatricesLieSubalgebra J) (s : S)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix m m ℝ)) G) :
    (skewAdjointBaseChangeLieEquiv S G J hG (s ⊗ₜ[ℝ] X) : Matrix m m S) =
      s • (unitsLieAlgebraLieEquiv (R := Matrix m m ℝ) (X : LeftInvariantDerivation _ _)).map
        (algebraMap ℝ S) := by
  simp [skewAdjointBaseChangeLieEquiv, LieEquiv.ofSubalgebras_apply]

/-- The inverse isomorphism sends the matrix coordinates of `X`, mapped into `S`, back to
`1 ⊗ X`. -/
theorem skewAdjointBaseChangeLieEquiv_symm_apply (G : Subgroup (Matrix m m ℝ)ˣ)
    (J : Matrix m m ℝ)
    (hG : ∀ A, (unitsLieAlgebraLieEquiv (R := Matrix m m ℝ)).symm A ∈
      lieSubalgebraOfSubgroup G ↔ A ∈ skewAdjointMatricesLieSubalgebra J)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix m m ℝ)) G) :
    (skewAdjointBaseChangeLieEquiv S G J hG).symm
        ⟨(unitsLieAlgebraLieEquiv (R := Matrix m m ℝ) (X : LeftInvariantDerivation _ _)).map
            (algebraMap ℝ S),
          by simpa using (skewAdjointBaseChangeLieEquiv S G J hG (1 ⊗ₜ[ℝ] X)).2⟩ =
      1 ⊗ₜ[ℝ] X := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_skewAdjointBaseChangeLieEquiv_tmul, one_smul])

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- **The Lie algebra of `SO(n)` extends to `𝔰𝔬(n, S)`.**  Extending the scalars of the Lie algebra
of the special orthogonal group `SO(n) = SU(n, ℝ)` to an `ℝ`-algebra `S` gives the orthogonal Lie
algebra over `S`, by `s ⊗ X ↦ s • X`.  For `S = ℂ` this is `𝔰𝔬(n) ⊗_ℝ ℂ ≅ 𝔰𝔬(n, ℂ)`, the Lie
algebra half of the identification of the complexification of `SO(n)` with `SO(n, ℂ)`. -/
noncomputable def specialOrthogonalBaseChangeLieEquiv :
    S ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℝ))
        (GLSpecialUnitary n ℝ : Subgroup (Matrix n n ℝ)ˣ) ≃ₗ⁅S⁆
      LieAlgebra.Orthogonal.so n S :=
  -- `LieAlgebra.Orthogonal.so n R` is defined as the Lie algebra of `1`-skew-adjoint matrices, so
  -- the membership criterion for `𝔰𝔬(n)` is the one `skewAdjointBaseChangeLieEquiv` asks for.
  (skewAdjointBaseChangeLieEquiv S _ 1
      unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff_mem_so).trans
    (LieEquiv.ofEq _ _ (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), LieAlgebra.Orthogonal.so]))

@[simp]
theorem coe_specialOrthogonalBaseChangeLieEquiv_tmul (s : S)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℝ))
      (GLSpecialUnitary n ℝ : Subgroup (Matrix n n ℝ)ˣ)) :
    (specialOrthogonalBaseChangeLieEquiv S n (s ⊗ₜ[ℝ] X) : Matrix n n S) =
      s • (unitsLieAlgebraLieEquiv (R := Matrix n n ℝ) (X : LeftInvariantDerivation _ _)).map
        (algebraMap ℝ S) := by
  rw [specialOrthogonalBaseChangeLieEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  exact coe_skewAdjointBaseChangeLieEquiv_tmul S _ _ _ s X

/-- The inverse isomorphism sends the matrix coordinates of `X`, mapped into `S`, back to
`1 ⊗ X`. -/
theorem specialOrthogonalBaseChangeLieEquiv_symm_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℝ))
      (GLSpecialUnitary n ℝ : Subgroup (Matrix n n ℝ)ˣ)) :
    (specialOrthogonalBaseChangeLieEquiv S n).symm
        ⟨(unitsLieAlgebraLieEquiv (R := Matrix n n ℝ) (X : LeftInvariantDerivation _ _)).map
            (algebraMap ℝ S),
          by simpa using (specialOrthogonalBaseChangeLieEquiv S n (1 ⊗ₜ[ℝ] X)).2⟩ =
      1 ⊗ₜ[ℝ] X := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_specialOrthogonalBaseChangeLieEquiv_tmul, one_smul])

/-- **The Lie algebra of `Sp(2l, ℝ)` extends to `𝔰𝔭(2l, S)`.**  Extending the scalars of the Lie
algebra of the real symplectic group to an `ℝ`-algebra `S` gives the symplectic Lie algebra over
`S`, by `s ⊗ X ↦ s • X`.  For `S = ℂ` this is `𝔰𝔭(2l, ℝ) ⊗_ℝ ℂ ≅ 𝔰𝔭(2l, ℂ)`: `𝔰𝔭(2l, ℝ)` is a
real form of `𝔰𝔭(2l, ℂ)`, the Lie algebra half of `Sp(2l, ℝ)` being a real form of `Sp(2l, ℂ)`. -/
noncomputable def symplecticBaseChangeLieEquiv (l : Type*) [Fintype l] [DecidableEq l] :
    S ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ))
        (GLSymplectic l ℝ : Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) ≃ₗ⁅S⁆
      LieAlgebra.Symplectic.sp l S :=
  -- `LieAlgebra.Symplectic.sp l R` is defined as the Lie algebra of `J`-skew-adjoint matrices, so
  -- the membership criterion for `𝔰𝔭(2l, ℝ)` is the one `skewAdjointBaseChangeLieEquiv` asks for.
  (skewAdjointBaseChangeLieEquiv S _ (Matrix.J l ℝ)
      unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp).trans
    (LieEquiv.ofEq _ _ (by rw [Matrix.map_J, LieAlgebra.Symplectic.sp]))

@[simp]
theorem coe_symplecticBaseChangeLieEquiv_tmul (l : Type*) [Fintype l] [DecidableEq l] (s : S)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ))
      (GLSymplectic l ℝ : Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ)) :
    (symplecticBaseChangeLieEquiv S l (s ⊗ₜ[ℝ] X) : Matrix (l ⊕ l) (l ⊕ l) S) =
      s • (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)
        (X : LeftInvariantDerivation _ _)).map (algebraMap ℝ S) := by
  rw [symplecticBaseChangeLieEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  exact coe_skewAdjointBaseChangeLieEquiv_tmul S _ _ _ s X

/-- The inverse isomorphism sends the matrix coordinates of `X`, mapped into `S`, back to
`1 ⊗ X`. -/
theorem symplecticBaseChangeLieEquiv_symm_apply (l : Type*) [Fintype l] [DecidableEq l]
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ))
      (GLSymplectic l ℝ : Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ)) :
    (symplecticBaseChangeLieEquiv S l).symm
        ⟨(unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)
            (X : LeftInvariantDerivation _ _)).map (algebraMap ℝ S),
          by simpa using (symplecticBaseChangeLieEquiv S l (1 ⊗ₜ[ℝ] X)).2⟩ =
      1 ⊗ₜ[ℝ] X := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_symplecticBaseChangeLieEquiv_tmul, one_smul])

end SkewAdjoint

end TauCeti.Lie
