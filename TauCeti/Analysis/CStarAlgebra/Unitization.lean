/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Unitization.LeftAction

/-!
# C⋆-algebra structure of the left-action unitization and right-action C⋆-norms

For a normed star algebra `A` with proper involution, `Unitization.LeftAction 𝕜 A` (defined in
`TauCeti.Analysis.Normed.Algebra.Unitization.LeftAction` as the subtype of
`(Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)).range`) carries a transported `StarRing` and
`StarModule` structure; left multiplication `Unitization.LeftAction.Lmul` is isometric when `A` is
regular, and `Unitization.starAlgEquivLeftAction` is an isometric `⋆`-algebra equivalence onto
`Unitization.LeftAction 𝕜 A` when `A` is complete, regular, and has no two-sided identity.

Specializing to C⋆-algebras, this file shows:
* For any `CStarRing A` over a densely normed star field `𝕜` (without assuming completeness of `A`,
  `CStarRing 𝕜`, or absence of an identity), `Unitization.LeftAction 𝕜 A` satisfies the
  C⋆-identity (`CStarRing (Unitization.LeftAction 𝕜 A)`) via `Unitization.norm_splitMul_snd_sq`.
  When `A` is a complex `NonUnitalCStarAlgebra` (so both `ℂ` and `A` are complete and `A` is
  regular), `Unitization.LeftAction ℂ A` is a unital `CStarAlgebra` (and `CommCStarAlgebra` in the
  commutative case).
* Over a densely normed C⋆-field `𝕜`, conjugating by the isometric involution expresses the
  unitization norm via `Unitization.rightAction 𝕜 A` (`Unitization.norm_eq_sup_rightAction`).
  When `A` is complete and has no two-sided identity, `Unitization.rightAction 𝕜 A` is an isometry;
  when both `𝕜` and `A` are complete, the range of `Unitization.rightAction 𝕜 A` in `A →L[𝕜] A` is
  closed whether or not `A` has an identity.

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2.
-/

public section

open ContinuousLinearMap

namespace Unitization

section RightAction

/-- For any C⋆-algebra `A` over a densely normed C⋆-field `𝕜` (with or without identity or
completeness), the C⋆-norm on `Unitization 𝕜 A` is the supremum of `‖u.fst‖` and the operator norm
of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_eq_sup_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] (u : Unitization 𝕜 A) :
    ‖u‖ = ‖u.fst‖ ⊔ ‖rightAction 𝕜 A u‖ := by
  have hL : algebraMap 𝕜 (A →L[𝕜] A) (star u.fst) + mul 𝕜 A (star u.snd) =
      star u.fst • ContinuousLinearMap.id 𝕜 A + mul 𝕜 A (star u.snd) := by
    rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  rw [← norm_star u, norm_eq_sup, fst_star, norm_star, snd_star, hL, rightAction_apply,
    ← norm_smul_id_add_mul_flip]

/-- In a complete C⋆-algebra without a two-sided identity, the C⋆-norm of `u : Unitization 𝕜 A`
equals the operator norm of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_rightAction_eq_norm {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖rightAction 𝕜 A u‖ = ‖u‖ := by
  rw [norm_eq_sup_rightAction]
  exact (max_eq_right (norm_fst_le_norm_rightAction hA u)).symm

/-- When a complete C⋆-algebra `A` has no two-sided identity, `Unitization.rightAction 𝕜 A` is an
isometry from `Unitization 𝕜 A` into `A →L[𝕜] A`. -/
theorem isometry_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜] [CStarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (rightAction 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_rightAction_eq_norm hA)

/-- For any complete C⋆-algebra over a complete densely normed C⋆-field, the right-action image of
`Unitization 𝕜 A` in `A →L[𝕜] A` is closed, whether or not `A` has an identity. -/
theorem isClosed_range_rightAction {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
    [CStarRing 𝕜] [CompleteSpace 𝕜] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]
    [CompleteSpace A] :
    IsClosed (Set.range (rightAction 𝕜 A)) := by
  by_cases hA : ∃ e : A, ∀ b : A, b * e = b
  · obtain ⟨e, he⟩ := hA
    rw [range_rightAction_of_right_identity he]
    exact (isometry_mul_flip 𝕜 A).isClosedEmbedding.isClosed_range
  · exact (isometry_rightAction
      (mt TauCeti.exists_right_identity_iff.mpr hA)).isClosedEmbedding.isClosed_range

end RightAction

namespace LeftAction

/-- For any C⋆-algebra `A` over a densely normed star field `𝕜`, the operator-norm subalgebra
`LeftAction 𝕜 A` satisfies the C⋆-identity. -/
instance instCStarRing {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] :
    CStarRing (LeftAction 𝕜 A) where
  norm_mul_self_le T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp T.2
    have hmul : lift (NonUnitalAlgHom.Lmul 𝕜 A) (star u * u) =
        ((star T * T : LeftAction 𝕜 A) : A →L[𝕜] A) := by
      rw [map_mul, Subalgebra.coe_mul, ← coe_star_of_eq hu, hu]
    simpa [← sq, AddSubgroupClass.coe_norm, ← hu, ← hmul, splitMul_apply] using
      norm_splitMul_snd_sq 𝕜 u

noncomputable instance instCStarAlgebra {A : Type*} [NonUnitalCStarAlgebra A] :
    CStarAlgebra (LeftAction ℂ A) where

noncomputable instance instCommCStarAlgebra {A : Type*} [NonUnitalCommCStarAlgebra A] :
    CommCStarAlgebra (LeftAction ℂ A) where

end LeftAction

end Unitization
