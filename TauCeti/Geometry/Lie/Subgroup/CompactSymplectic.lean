/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Geometry.Lie.Subgroup.Symplectic
public import TauCeti.Geometry.Lie.Subgroup.Unitary
import TauCeti.LinearAlgebra.Complex.RealForm

/-!
# The compact symplectic group and its complexified Lie algebra

The **compact symplectic group** `Sp(n)` is the group of unitary matrices in the complex
symplectic group `Sp(2n, ℂ)`.  Inside the general linear Lie group
`GL (l ⊕ l) ℂ = (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ` it is the intersection
`TauCeti.GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ)` of two closed subgroups, so a closed
subgroup of the compact unitary group.  This file computes its Lie algebra `𝔰𝔭(n)` and identifies
the complexification of `𝔰𝔭(n)` with the complex symplectic Lie algebra:

`𝔰𝔭(n) ⊗_ℝ ℂ ≅ 𝔰𝔭(2n, ℂ)`,

as complex Lie algebras, by `c ⊗ X ↦ c • X`.  This is the Lie algebra half of the identification
of `Sp(2n, ℂ)` as the complexification of `Sp(n)`, alongside the unitary and special unitary cases
`𝔲(n) ⊗_ℝ ℂ ≅ 𝔤𝔩(n, ℂ)` and `𝔰𝔲(n) ⊗_ℝ ℂ ≅ 𝔰𝔩(n, ℂ)` of
`TauCeti/Geometry/Lie/Subgroup/Complexification.lean`.

The Lie algebra of an intersection of closed subgroups is the intersection of their Lie algebras
(`TauCeti.Lie.lieSubalgebraOfSubgroup_inf`).  Read in the canonical matrix coordinates of the
general linear Lie algebra, the symplectic factor contributes membership in Mathlib's symplectic
Lie algebra `LieAlgebra.Symplectic.sp l 𝕜`, and the unitary factor contributes `Aᴴ = -A`.  This
computation is made over any `RCLike` field `𝕜`; over `ℝ` the same intersection is the group of
orthogonal symplectic matrices, the realified unitary group `U(n)`.

Over `ℂ` the symplectic Lie algebra is closed under the conjugate transpose
(`LieAlgebra.Symplectic.conjTranspose_mem_sp`), so its skew-Hermitian elements are a real form of
it (`LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`): every element of `𝔰𝔭(2n, ℂ)` is
uniquely `X + i Y` with `X` and `Y` in `𝔰𝔭(n)`.

## Main results

* `TauCeti.Lie.lieSubalgebraOfSubgroup_GLSymplectic_inf_unitarySubgroup`: the Lie algebra of the
  compact symplectic group is the intersection of the Lie algebras of the symplectic and unitary
  groups.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_GLSymplectic_inf_unitarySubgroup_lieSubalgebra_iff`:
  **the Lie algebra of the compact symplectic group is the skew-Hermitian matrices in `sp`.**
* `TauCeti.Lie.isEmbeddedLieSubgroup_GLSymplectic_inf_unitarySubgroup`: the compact symplectic
  group is an embedded Lie subgroup of the general linear group, hence a Lie group.
* `TauCeti.Lie.isBaseChange_complex_GLSymplectic_inf_unitarySubgroup`: the matrix coordinates
  exhibit `𝔰𝔭(2n, ℂ)` as the complexification of the Lie algebra of `Sp(n)`.
* `TauCeti.Lie.compactSymplecticComplexificationLieEquiv`: **the complex Lie algebra isomorphism
  `𝔰𝔭(n) ⊗_ℝ ℂ ≃ 𝔰𝔭(2n, ℂ)`**, with
  `TauCeti.Lie.coe_compactSymplecticComplexificationLieEquiv_tmul` and
  `TauCeti.Lie.compactSymplecticComplexificationLieEquiv_symm_apply`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer, 2015, Section 1.2 (the compact symplectic group as
  `Sp(n; ℂ) ∩ U(2n)`) and Section 3.6 (complexifications of real Lie algebras).
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section I.8 (the real form `𝔰𝔭(n)` of `𝔰𝔭(n, ℂ)`).
-/

public section

open Manifold TensorProduct
open scoped Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

section RCLike

variable {l 𝕜 : Type*} [Fintype l] [DecidableEq l] [RCLike 𝕜]

/-- **The Lie algebra of the compact symplectic group splits.**  It is the intersection of the Lie
algebras of the symplectic and unitary groups, because both subgroups are closed. -/
theorem lieSubalgebraOfSubgroup_GLSymplectic_inf_unitarySubgroup :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
        (GLSymplectic l 𝕜 ⊓ unitarySubgroup (GL (l ⊕ l) 𝕜) :
          Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) =
      lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
          (GLSymplectic l 𝕜 : Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) ⊓
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
          (unitarySubgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) :=
  lieSubalgebraOfSubgroup_inf (isClosed_GLSymplectic l 𝕜)
    (isClosed_unitarySubgroup_units (Matrix (l ⊕ l) (l ⊕ l) 𝕜))

/-- **The Lie algebra of the compact symplectic group is `𝔰𝔭(n)`**, the skew-Hermitian matrices in
the symplectic Lie algebra: a matrix has both properties exactly when its inverse image under the
canonical units Lie equivalence belongs to the Lie subalgebra of the unitary symplectic matrices. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_GLSymplectic_inf_unitarySubgroup_lieSubalgebra_iff
    (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) :
    (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜)).symm A ∈
        lieSubalgebraOfSubgroup (GLSymplectic l 𝕜 ⊓ unitarySubgroup (GL (l ⊕ l) 𝕜) :
          Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) ↔
      A ∈ LieAlgebra.Symplectic.sp l 𝕜 ∧ Aᴴ = -A := by
  rw [lieSubalgebraOfSubgroup_GLSymplectic_inf_unitarySubgroup, LieSubalgebra.mem_inf,
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp,
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]

/-- **The compact symplectic group is an embedded Lie subgroup of the general linear group.**
Being a closed subgroup of the Lie group of units, the closed-subgroup theorem makes it a Lie
group for its subspace topology, with smooth inclusion of everywhere split differential. -/
theorem isEmbeddedLieSubgroup_GLSymplectic_inf_unitarySubgroup :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
      (GLSymplectic l 𝕜 ⊓ unitarySubgroup (GL (l ⊕ l) 𝕜) :
        Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ) :=
  isEmbeddedLieSubgroup_of_isClosed ((isClosed_GLSymplectic l 𝕜).inter
    (isClosed_unitarySubgroup_units (Matrix (l ⊕ l) (l ⊕ l) 𝕜)))

end RCLike

/-! ### The complexification -/

variable (l : Type*) [Fintype l] [DecidableEq l]

/-- **`𝔰𝔭(2n, ℂ)` is the complexification of the Lie algebra of `Sp(n)`.**  The matrix
coordinates of the Lie algebra of the compact symplectic group, with values in the symplectic Lie
algebra, exhibit `𝔰𝔭(2n, ℂ)` as its base change from `ℝ` to `ℂ`: the symplectic Lie algebra is
closed under the conjugate transpose, and its skew-Hermitian elements are the Lie algebra of
`Sp(n)`. -/
theorem isBaseChange_complex_GLSymplectic_inf_unitarySubgroup :
    IsBaseChange ℂ (LinearMap.codRestrict
      ((LieAlgebra.Symplectic.sp l ℂ).toSubmodule.restrictScalars ℝ)
      (((unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℂ) :
          LeftInvariantDerivation 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℂ) (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ
            →ₗ⁅ℝ⁆ Matrix (l ⊕ l) (l ⊕ l) ℂ).comp
          (lieSubalgebraOfSubgroup (GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ) :
            Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ)).incl) :
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℂ))
          (GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ) :
            Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ) →ₗ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℂ)
      fun X ↦ unitsLieAlgebraLieEquiv_mem_sp_of_mem_lieSubalgebraOfSubgroup
        (lieSubalgebraOfSubgroup_mono inf_le_left X.2)) := by
  let e := unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℂ)
  refine LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg _
    (fun A hA ↦ Matrix.star_eq_conjTranspose A ▸ LieAlgebra.Symplectic.conjTranspose_mem_sp hA) _
    (fun X Y h ↦ Subtype.ext (e.injective h)) (fun X ↦ ?_) fun A hA hskew ↦ ?_
  · have hX := X.2
    rw [← e.symm_apply_apply X.1,
      unitsLieAlgebraLieEquiv_symm_mem_GLSymplectic_inf_unitarySubgroup_lieSubalgebra_iff] at hX
    rw [Matrix.star_eq_conjTranspose]
    exact hX.2
  · rw [Matrix.star_eq_conjTranspose] at hskew
    refine ⟨⟨e.symm A, ?_⟩, by simp [e]⟩
    exact (unitsLieAlgebraLieEquiv_symm_mem_GLSymplectic_inf_unitarySubgroup_lieSubalgebra_iff
      A).2 ⟨hA, hskew⟩

/-- **The complexification of the Lie algebra of `Sp(n)` is `𝔰𝔭(2n, ℂ)`**: the isomorphism of
complex Lie algebras from the Lie algebra of the compact symplectic group with scalars extended to
`ℂ` onto the complex symplectic Lie algebra, sending `c ⊗ X` to `c` times the matrix coordinates
of `X`. -/
def compactSymplecticComplexificationLieEquiv :
    ℂ ⊗[ℝ] lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℂ))
        (GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ) :
          Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ) ≃ₗ⁅ℂ⁆
      LieAlgebra.Symplectic.sp l ℂ :=
  (isBaseChange_complex_GLSymplectic_inf_unitarySubgroup l).lieEquivOfCodRestrict

@[simp]
theorem coe_compactSymplecticComplexificationLieEquiv_tmul (c : ℂ)
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℂ))
      (GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ) :
        Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ)) :
    (compactSymplecticComplexificationLieEquiv l (c ⊗ₜ[ℝ] X) : Matrix (l ⊕ l) (l ⊕ l) ℂ) =
      c • unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℂ)
        (X : LeftInvariantDerivation _ _) :=
  (isBaseChange_complex_GLSymplectic_inf_unitarySubgroup l).coe_lieEquivOfCodRestrict_tmul c X

/-- The inverse isomorphism sends the matrix coordinates of `X` back to `1 ⊗ X`. -/
theorem compactSymplecticComplexificationLieEquiv_symm_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℂ))
      (GLSymplectic l ℂ ⊓ unitarySubgroup (GL (l ⊕ l) ℂ) :
        Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℂ)ˣ)) :
    (compactSymplecticComplexificationLieEquiv l).symm
        ⟨unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℂ) (X : LeftInvariantDerivation _ _),
          unitsLieAlgebraLieEquiv_mem_sp_of_mem_lieSubalgebraOfSubgroup
            (lieSubalgebraOfSubgroup_mono inf_le_left X.2)⟩ =
      1 ⊗ₜ[ℝ] X :=
  (isBaseChange_complex_GLSymplectic_inf_unitarySubgroup l).lieEquivOfCodRestrict_symm_apply X

end TauCeti.Lie
