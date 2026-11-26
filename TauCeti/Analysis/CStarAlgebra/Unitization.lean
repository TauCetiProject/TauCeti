/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Unitization.LeftAction
import Mathlib.Analysis.CStarAlgebra.Multiplier

/-!
# C⋆-algebra structure of the left-action unitization and right-action C⋆-norms

For a seminormed star algebra `A` with faithful right multiplication (`FaithfulSMul Aᵐᵒᵖ A`),
`Unitization.LeftAction 𝕜 A` (defined in `TauCeti.Analysis.Normed.Algebra.Unitization.LeftAction`
as the subtype of `(Unitization.lift (NonUnitalAlgHom.Lmul 𝕜 A)).range`) carries a transported
`StarRing` and `StarModule` structure; left multiplication `Unitization.LeftAction.Lmul` is
isometric when `A` is regular, and `Unitization.starAlgEquivLeftAction` is a `⋆`-algebra
equivalence onto `Unitization.LeftAction 𝕜 A` when `A` has no two-sided identity (isometric when
`A` is a complete regular normed algebra).

Specializing to C⋆-algebras, this file shows:
* For any regular C⋆-algebra `A` over a nontrivially normed field `𝕜` (including every C⋆-algebra
  over a densely normed field, without assuming completeness, a star structure on `𝕜`, or absence
  of an identity), Mathlib's `DoubleCentralizer.norm_fst_eq_snd` expresses the minimal unitization
  norm via `Unitization.rightAction 𝕜 A` (`Unitization.norm_eq_sup_rightAction`). When `A` is
  complete and has no two-sided identity, `Unitization.rightAction 𝕜 A` is an isometry.
* For any `CStarRing A` over a densely normed star field `𝕜` (without assuming completeness of `A`,
  `CStarRing 𝕜`, or absence of an identity), `Unitization.LeftAction 𝕜 A` satisfies the
  C⋆-identity (`CStarRing (Unitization.LeftAction 𝕜 A)`) via `Unitization.norm_splitMul_snd_sq`.
  When `A` is a complex `NonUnitalCStarAlgebra` (so both `ℂ` and `A` are complete and `A` is
  regular), `Unitization.LeftAction ℂ A` is a unital `CStarAlgebra` (and `CommCStarAlgebra` in the
  commutative case).

## References

* B. Blackadar, *Operator Algebras*, Section II.1.2.
-/

public section

open ContinuousLinearMap
open scoped MultiplierAlgebra

namespace Unitization

/-- The algebra coordinate of a unitization element has norm at most twice the unitization
norm. -/
theorem norm_snd_le_two_mul_norm {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [RegularNormedAlgebra 𝕜 A] (x : Unitization 𝕜 A) : ‖x.snd‖ ≤ 2 * ‖x‖ := by
  -- The canonical metric inherits the extended distance from the auxiliary metric.
  have h : LipschitzWith 2 (addEquiv 𝕜 A) := fun a b => lipschitzWith_addEquiv a b
  have hbound := (norm_snd_le (addEquiv 𝕜 A x)).trans (h.norm_le_mul (map_zero _) x)
  rw [NNReal.coe_ofNat] at hbound
  exact hbound

section RightAction

/-- For any regular C⋆-algebra `A` over a nontrivially normed field `𝕜` (with or without identity
or completeness), the minimal unitization norm on `Unitization 𝕜 A` is the supremum of `‖u.fst‖`
and the operator norm of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_eq_sup_rightAction {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [RegularNormedAlgebra 𝕜 A]
    (u : Unitization 𝕜 A) :
    ‖u‖ = ‖u.fst‖ ⊔ ‖rightAction 𝕜 A u‖ := by
  rw [norm_eq_sup]
  congr 1
  simpa [DoubleCentralizer.add_fst, DoubleCentralizer.add_snd, DoubleCentralizer.algebraMap_fst,
    DoubleCentralizer.algebraMap_snd, DoubleCentralizer.coe_fst, DoubleCentralizer.coe_snd,
    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def, rightAction_apply] using
    DoubleCentralizer.norm_fst_eq_snd (algebraMap 𝕜 𝓜(𝕜, A) u.fst + (u.snd : 𝓜(𝕜, A)))

/-- In a complete regular C⋆-algebra without a two-sided identity, the minimal unitization norm
of `u : Unitization 𝕜 A` equals the operator norm of `Unitization.rightAction 𝕜 A u`. -/
theorem norm_rightAction_eq_norm {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [RegularNormedAlgebra 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) (u : Unitization 𝕜 A) :
    ‖rightAction 𝕜 A u‖ = ‖u‖ := by
  rw [norm_eq_sup_rightAction]
  exact (max_eq_right (norm_fst_le_norm_rightAction hA u)).symm

/-- When a complete regular C⋆-algebra `A` has no two-sided identity, `Unitization.rightAction 𝕜 A`
is an isometry from `Unitization 𝕜 A` into `A →L[𝕜] A`. -/
theorem isometry_rightAction {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [RegularNormedAlgebra 𝕜 A] [CompleteSpace A]
    (hA : ¬ ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b) :
    Isometry (rightAction 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_rightAction_eq_norm hA)

end RightAction

namespace LeftAction

/-- For any C⋆-algebra `A` over a densely normed star field `𝕜`, the operator-norm subalgebra
`LeftAction 𝕜 A` satisfies the C⋆-identity. -/
instance instCStarRing {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A] :
    CStarRing (LeftAction 𝕜 A) where
  norm_mul_self_le T := by
    obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp T.property
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
