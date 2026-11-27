/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialOrthogonal
public import TauCeti.Geometry.Lie.Exponential.OneParameter
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct

import TauCeti.Geometry.Lie.Adjoint.Units.Basic
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The Lie algebra of the special orthogonal group

The special orthogonal group `SO(n) = Matrix.specialOrthogonalGroup n ℝ` is a Lie group, with the
native structure of the special unitary group `Matrix.specialUnitaryGroup n ℝ`
(`TauCeti.Geometry.Manifold.Instances.Unitary.Special`), embedded in the matrices. This file
identifies its Lie algebra with the orthogonal Lie algebra `so(n) = LieAlgebra.Orthogonal.so n ℝ`
of skew-symmetric matrices: the differential at the identity of the inclusion
`SO(n) → Matrix n n ℝ` is a linear isomorphism onto `so(n)`
(`TauCeti.specialOrthogonalLieAlgebraEquiv`).

* It takes values in `so(n)`, because `SO(n)` lies in the orthogonal group, whose Lie algebra
  consists of skew-adjoint elements
  (`Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint`): differentiating `Aᵀ A = 1` at
  `A = 1` gives `Xᵀ + X = 0`.
* It is injective, because the inclusion is an immersion
  (`Matrix.specialUnitaryGroup.isImmersion_val`).
* It is surjective: a skew-symmetric matrix `X` is the velocity at `t = 0` of the smooth curve
  `t ↦ exp (t X)`, which stays in `SO(n)` (`Matrix.exp_mem_specialOrthogonalGroup_of_mem_so`).

It preserves the Lie brackets, so it is an isomorphism of Lie algebras: the inclusion is the
differential of the smooth homomorphism from `SO(n)` into the invertible matrices
(`Matrix.specialUnitaryGroup.toUnitsSmoothHom`), whose Lie algebra is the matrices with the
commutator bracket (`TauCeti.Lie.groupLieAlgebra_units_ad_apply`), and the differential of a smooth
homomorphism preserves brackets (`ContMDiffMonoidMorphism.groupLieAlgebraMap_lie`).

For `n = 3`, composing with the hat map `TauCeti.soThreeEquiv` identifies the dual of the Lie
algebra of `SO(3)` with `ℝ³` (`TauCeti.specialOrthogonalThreeDualEquiv`), and the coadjoint
stabilizer of the functional of `m ≠ 0` is the line of infinitesimal rotations about `m`.

As for the special unitary group, matrices carry the `ℓ²` operator norm: the statements are made
with `open scoped Matrix.Norms.L2Operator` and the local instance `Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `TauCeti.specialOrthogonalLieAlgebraEquiv`: the Lie algebra of `SO(n)` is isomorphic to `so(n)` as
  a Lie algebra, by the differential of the inclusion at the identity.
* `TauCeti.finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three`: the Lie algebra of `SO(3)` has
  dimension `3`.
* `TauCeti.specialOrthogonalThreeDualEquiv`: the dual of the Lie algebra of `SO(3)` is `ℝ³`, the
  vector `m` giving the functional `ν_m` that pairs `ξ` with `m ⬝ᵥ u` when `ξ` corresponds to `û`.
* `TauCeti.lieAnnihilator_specialOrthogonalThreeDualEquiv_toSubmodule_eq`,
  `TauCeti.finrank_lieAnnihilator_specialOrthogonalThreeDualEquiv`,
  `TauCeti.lieAnnihilator_specialOrthogonalThreeDualEquiv_eq_top_iff`: the coadjoint stabilizer of
  `ν_m` in the Lie algebra of `SO(3)` is the line of infinitesimal rotations about `m` for
  `m ≠ 0`, and all of it only for `m = 0`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Sections 3.3 and 3.4 (the Lie algebras of the matrix Lie groups `O(n)` and `SO(n)`).
-/

public section

noncomputable section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal
  LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The differential at the identity of the inclusion of `SO(n)` into the matrices takes values
in the skew-symmetric matrices `so(n)`. -/
theorem mvfderiv_specialOrthogonalGroup_val_mem_so
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ ∈
      LieAlgebra.Orthogonal.so n ℝ := by
  -- The inclusion factors through the orthogonal group `unitary (Matrix n n ℝ)`, whose Lie algebra
  -- consists of skew-adjoint matrices.
  let ι := Submonoid.inclusion
    (Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := ℝ))
  have hcomp : (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) =
      (Subtype.val : unitary (Matrix n n ℝ) → Matrix n n ℝ) ∘ ι := rfl
  have hι : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ)
      (Unitary.model (Matrix n n ℝ)) ι 1 :=
    Matrix.specialUnitaryGroup.isSmoothEmbedding_inclusion_unitaryGroup.contMDiff
      |>.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (Unitary.model (Matrix n n ℝ)) 𝓘(ℝ, Matrix n n ℝ)
      (Subtype.val : unitary (Matrix n n ℝ) → Matrix n n ℝ) 1 :=
    Unitary.contMDiff_val.mdifferentiableAt (by simp)
  rw [hcomp, mvfderiv_apply_eq_mfderiv_apply, mfderiv_comp_of_eq hval hι (map_one ι)]
  exact (Matrix.mem_so_iff_mem_skewAdjoint _).2
    (Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint _)

variable (n) in
/-- The differential at the identity of the inclusion `SO(n) → Matrix n n ℝ`, with values in
`so(n)`. -/
private def specialOrthogonalLieAlgebraMap :
    GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ) (Matrix.specialOrthogonalGroup n ℝ) →ₗ[ℝ]
      LieAlgebra.Orthogonal.so n ℝ :=
  LinearMap.codRestrict (LieAlgebra.Orthogonal.so n ℝ).toSubmodule
    (mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
      (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1).toLinearMap
    mvfderiv_specialOrthogonalGroup_val_mem_so

private theorem coe_specialOrthogonalLieAlgebraMap_apply
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    (specialOrthogonalLieAlgebraMap n ξ : Matrix n n ℝ) =
      mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ := by
  rw [specialOrthogonalLieAlgebraMap, LinearMap.codRestrict_apply]
  rfl

private theorem injective_specialOrthogonalLieAlgebraMap :
    Function.Injective (specialOrthogonalLieAlgebraMap n) := by
  intro ξ η h
  have h' := congrArg (fun A : LieAlgebra.Orthogonal.so n ℝ ↦ (A : Matrix n n ℝ)) h
  -- `h'` says that the differentials of the inclusion at `1` agree on `ξ` and `η`.
  exact (Matrix.specialUnitaryGroup.isImmersion_val.isImmersionAt 1).mfderiv_injective (by simp) h'

private theorem surjective_specialOrthogonalLieAlgebraMap :
    Function.Surjective (specialOrthogonalLieAlgebraMap n) := by
  rintro ⟨A, hA⟩
  -- The exponential line of `A` is a smooth curve in `SO(n)` through `1` with velocity `A`.
  let γ : ℝ → Matrix.specialOrthogonalGroup n ℝ := fun t ↦
    ⟨exp (t • A), Matrix.exp_mem_specialOrthogonalGroup_of_mem_so _
      ((LieAlgebra.Orthogonal.so n ℝ).smul_mem t hA)⟩
  have hγ0 : γ 0 = 1 := Subtype.ext (by simp [γ])
  have hγs : ContMDiff 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) ∞ γ :=
    Matrix.specialUnitaryGroup.contMDiff_iff.2 ((contDiff_exp_smul A).of_le le_top).contMDiff
  have hγ : MDifferentiableAt 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) γ 0 :=
    hγs.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ)
      (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 :=
    Matrix.specialUnitaryGroup.contMDiff_val.mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, Matrix n n ℝ) (Subtype.val ∘ γ) 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight A) := by
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    rw [zero_smul, exp_zero, one_mul] at h
    exact h.hasFDerivAt.hasMFDerivAt
  -- The chain rule along `Subtype.val ∘ γ = fun t ↦ exp (t • A)`, evaluated on the unit vector.
  have h1 := DFunLike.congr_fun ((mfderiv_comp_of_eq hval hγ hγ0).symm.trans hd.mfderiv) (1 : ℝ)
  -- The differential of the inclusion is taken at `γ 0`, which is `1`; at `1` the map is its
  -- codomain restriction to `so(n)`.
  have h2 : ∀ e : Matrix.specialOrthogonalGroup n ℝ, e = 1 →
      ∀ v, mfderiv (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ) Subtype.val e v =
        (specialOrthogonalLieAlgebraMap n v : Matrix n n ℝ) := by
    rintro e rfl v
    rw [coe_specialOrthogonalLieAlgebraMap_apply, mvfderiv_apply_eq_mfderiv_apply]
  refine ⟨mfderiv 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) γ 0 (1 : ℝ), Subtype.ext ?_⟩
  rw [← h2 _ hγ0]
  -- Both sides of `h1` evaluate by definition: `(L ∘ M) 1 = L (M 1)` and `(t ↦ t • A) 1 = 1 • A`.
  exact h1.trans (one_smul ℝ A)

private theorem bijective_specialOrthogonalLieAlgebraMap :
    Function.Bijective (specialOrthogonalLieAlgebraMap n) :=
  ⟨injective_specialOrthogonalLieAlgebraMap, surjective_specialOrthogonalLieAlgebraMap⟩

/-- The differential at the identity of the inclusion of `SO(n)` into the invertible matrices,
read in the matrices, is that of the inclusion into the matrices. -/
private theorem groupLieAlgebraMap_toUnitsSmoothHom
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    ((Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ).toMonoidHom.groupLieAlgebraMap
        (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ) ξ : Matrix n n ℝ) =
      (specialOrthogonalLieAlgebraMap n ξ : Matrix n n ℝ) := by
  have hφ : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ)
      (Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ) 1 :=
    (Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ).contMDiff_toFun.mdifferentiableAt (by simp)
  have hcomp : (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) =
      (Units.val : (Matrix n n ℝ)ˣ → Matrix n n ℝ) ∘
        Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ :=
    funext fun g ↦ (Matrix.specialUnitaryGroup.val_toUnitsSmoothHom_apply g).symm
  rw [coe_specialOrthogonalLieAlgebraMap_apply, mvfderiv_apply_eq_mfderiv_apply, hcomp,
    mfderiv_comp 1 ((Units.hasMFDerivAt_val (𝕜 := ℝ) _).mdifferentiableAt) hφ,
    (Units.hasMFDerivAt_val (𝕜 := ℝ) _).mfderiv, MonoidHom.groupLieAlgebraMap_apply]
  -- What is left is `id (dφ ξ) = dφ ξ`, both sides read in `Matrix n n ℝ`, which is the tangent
  -- space of the invertible matrices at `1` and their Lie algebra.
  rfl

/-- The differential at the identity of the inclusion `SO(n) → Matrix n n ℝ` preserves the Lie
bracket: it is the differential of the smooth homomorphism into the invertible matrices, whose Lie
algebra carries the commutator bracket. -/
private theorem specialOrthogonalLieAlgebraMap_lie
    (ξ η : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    specialOrthogonalLieAlgebraMap n ⁅ξ, η⁆ =
      ⁅specialOrthogonalLieAlgebraMap n ξ, specialOrthogonalLieAlgebraMap n η⁆ := by
  refine Subtype.ext ?_
  -- In the Lie algebra of the invertible matrices the bracket is the commutator.
  have h := Lie.groupLieAlgebra_units_ad_apply (R := Matrix n n ℝ)
    ((Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ).toMonoidHom.groupLieAlgebraMap
      (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ) ξ)
    ((Matrix.specialUnitaryGroup.toUnitsSmoothHom n ℝ).toMonoidHom.groupLieAlgebraMap
      (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ) η)
  rw [LieAlgebra.ad_apply, ← ContMDiffMonoidMorphism.groupLieAlgebraMap_lie,
    groupLieAlgebraMap_toUnitsSmoothHom, groupLieAlgebraMap_toUnitsSmoothHom,
    groupLieAlgebraMap_toUnitsSmoothHom] at h
  rw [LieSubalgebra.coe_bracket, Ring.lie_def]
  exact h

variable (n) in
/-- **The Lie algebra of the special orthogonal group is `so(n)`.** The differential at the
identity of the inclusion of `SO(n) = Matrix.specialOrthogonalGroup n ℝ` into the matrices is an
isomorphism of Lie algebras from its Lie algebra onto the skew-symmetric matrices
`so(n) = LieAlgebra.Orthogonal.so n ℝ`, with the commutator bracket. -/
def specialOrthogonalLieAlgebraEquiv :
    GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ) (Matrix.specialOrthogonalGroup n ℝ) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so n ℝ :=
  LieEquiv.ofBijective
    { specialOrthogonalLieAlgebraMap n with map_lie' := specialOrthogonalLieAlgebraMap_lie _ _ }
    bijective_specialOrthogonalLieAlgebraMap

/-- The element of `so(n)` attached to `ξ` is the differential of the inclusion
`SO(n) → Matrix n n ℝ` at the identity, applied to `ξ`. -/
@[simp]
theorem coe_specialOrthogonalLieAlgebraEquiv_apply
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    (specialOrthogonalLieAlgebraEquiv n ξ : Matrix n n ℝ) =
      mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ := by
  rw [← coe_specialOrthogonalLieAlgebraMap_apply]
  -- `specialOrthogonalLieAlgebraEquiv` is `LieEquiv.ofBijective` of the bracket-preserving
  -- `specialOrthogonalLieAlgebraMap`, so its forward map is that map.
  rfl

/-! ### The dual of the Lie algebra of `SO(3)` -/

section Three

open Module

/-- The Lie algebra of the rotation group `SO(3)`. -/
local notation "𝔰𝔬₃" => GroupLieAlgebra (Matrix.specialUnitaryGroup.model (Fin 3) ℝ)
  (Matrix.specialOrthogonalGroup (Fin 3) ℝ)

/-- **The dual of the Lie algebra of `SO(3)` is `ℝ³`.** The vector `m` gives the functional
`ν_m : ξ ↦ m ⬝ᵥ u` on the Lie algebra of `SO(3)`, where `u ⨯₃ ·` is the infinitesimal rotation of
`ξ`, that is, `ξ` corresponds to the hat matrix `û` under `TauCeti.specialOrthogonalLieAlgebraEquiv`
and `TauCeti.soThreeEquiv`. It is `TauCeti.soThreeDualEquiv` read through the Lie algebra
isomorphism `TauCeti.specialOrthogonalLieAlgebraEquiv`. -/
def specialOrthogonalThreeDualEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] Module.Dual ℝ 𝔰𝔬₃ :=
  (soThreeDualEquiv ℝ).trans (specialOrthogonalLieAlgebraEquiv (Fin 3)).toLinearEquiv.dualMap

/-- The Lie algebra of `SO(3)` has dimension `3`. -/
theorem finrank_groupLieAlgebra_specialOrthogonalGroup_fin_three : finrank ℝ 𝔰𝔬₃ = 3 :=
  (specialOrthogonalLieAlgebraEquiv (Fin 3)).toLinearEquiv.finrank_eq.trans finrank_so_three

/-- The functional `ν_m` pairs `ξ` with `m ⬝ᵥ u`, where `ξ` corresponds to `û`. -/
@[simp]
theorem specialOrthogonalThreeDualEquiv_apply (m : Fin 3 → ℝ) (ξ : 𝔰𝔬₃) :
    specialOrthogonalThreeDualEquiv m ξ =
      m ⬝ᵥ (soThreeEquiv ℝ).symm (specialOrthogonalLieAlgebraEquiv (Fin 3) ξ) := by
  rw [specialOrthogonalThreeDualEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    soThreeDualEquiv_apply, LieEquiv.coe_toLinearEquiv]

/-- **The coadjoint stabilizer of `ν_m` in the Lie algebra of `SO(3)`** is the preimage of the
stabilizer of the functional `m ⬝ᵥ ·` of `so(3)`, the infinitesimal rotations about the axis `m`. -/
theorem lieAnnihilator_specialOrthogonalThreeDualEquiv (m : Fin 3 → ℝ) :
    lieAnnihilator ℝ 𝔰𝔬₃ (specialOrthogonalThreeDualEquiv m) =
      (lieAnnihilator ℝ (LieAlgebra.Orthogonal.so (Fin 3) ℝ) (soThreeDualEquiv ℝ m)).comap
        (specialOrthogonalLieAlgebraEquiv (Fin 3)).toLieHom :=
  Module.Dual.lieAnnihilator_eq_comap (specialOrthogonalLieAlgebraEquiv (Fin 3)).surjective rfl

/-- **The coadjoint stabilizer of `ν_m`, for `m ≠ 0`, is the line of infinitesimal rotations about
the axis `m`**: the preimage under `TauCeti.specialOrthogonalLieAlgebraEquiv` of the span of the
hat matrix `m̂`. -/
theorem lieAnnihilator_specialOrthogonalThreeDualEquiv_toSubmodule_eq {m : Fin 3 → ℝ}
    (hm : m ≠ 0) :
    (lieAnnihilator ℝ 𝔰𝔬₃ (specialOrthogonalThreeDualEquiv m)).toSubmodule =
      (ℝ ∙ soThreeEquiv ℝ m).comap
        ((specialOrthogonalLieAlgebraEquiv (Fin 3)).toLinearEquiv :
          𝔰𝔬₃ →ₗ[ℝ] LieAlgebra.Orthogonal.so (Fin 3) ℝ) := by
  ext ξ
  rw [LieSubalgebra.mem_toSubmodule, lieAnnihilator_specialOrthogonalThreeDualEquiv,
    LieSubalgebra.mem_comap, ← LieSubalgebra.mem_toSubmodule,
    lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv hm, Submodule.mem_comap,
    LieEquiv.coe_toLieHom, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]

/-- **The coadjoint stabilizers of nonzero functionals on the Lie algebra of `SO(3)` are lines**:
for `m ≠ 0` the infinitesimal rotations fixing `ν_m` are those about the axis `m`. -/
theorem finrank_lieAnnihilator_specialOrthogonalThreeDualEquiv {m : Fin 3 → ℝ} (hm : m ≠ 0) :
    finrank ℝ (lieAnnihilator ℝ 𝔰𝔬₃ (specialOrthogonalThreeDualEquiv m)) = 1 := by
  -- A Lie subalgebra and its underlying submodule have the same carrier type.
  change finrank ℝ (lieAnnihilator ℝ 𝔰𝔬₃ (specialOrthogonalThreeDualEquiv m)).toSubmodule = 1
  rw [lieAnnihilator_specialOrthogonalThreeDualEquiv_toSubmodule_eq hm,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_span_singleton ((soThreeEquiv ℝ).map_ne_zero_iff.mpr hm)]

/-- The only functional on the Lie algebra of `SO(3)` fixed by its whole coadjoint action is
zero. -/
theorem lieAnnihilator_specialOrthogonalThreeDualEquiv_eq_top_iff {m : Fin 3 → ℝ} :
    lieAnnihilator ℝ 𝔰𝔬₃ (specialOrthogonalThreeDualEquiv m) = ⊤ ↔ m = 0 := by
  rw [lieAnnihilator_specialOrthogonalThreeDualEquiv, ← lieAnnihilator_soThreeDualEquiv_eq_top_iff]
  refine ⟨fun h ↦ eq_top_iff.2 fun A _ ↦ ?_, fun h ↦ eq_top_iff.2 fun ξ _ ↦
    (LieSubalgebra.mem_comap _ _).2 (h ▸ LieSubalgebra.mem_top _)⟩
  obtain ⟨ξ, rfl⟩ := (specialOrthogonalLieAlgebraEquiv (Fin 3)).surjective A
  exact (LieSubalgebra.mem_comap _ _).1 (h ▸ LieSubalgebra.mem_top ξ)

end Three

end TauCeti
