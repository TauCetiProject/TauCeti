/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Basic
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
public import Mathlib.Algebra.Exact.Basic

/-!
# The infinitesimal determinant of Spinᶜ

The determinant character has weight two on the central circle, whereas half-spinors have
weight one. Consequently a determinant infinitesimal parameter `a` lifts centrally as `a / 2`.
We construct this right inverse of the actual determinant differential and the resulting
splitting into its kernel and the determinant parameter. The exponential of the right inverse
is the central path `[1, exp(ia/2)]`; it is not a group-theoretic square-root character.

The operator-norm derivative of this path in the framed half-spin representation is proved
in `TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin`. No global principal connection is
constructed here.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped Manifold ContDiff

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

local notation "IC" => ModelWithCorners.prod 𝓘(ℝ, realSpinLieModel n) (𝓡 1)
local notation "G" => spinCGroup (realCliffordForm n 0) hQ
local notation "𝔤" => LeftInvariantDerivation IC G

/-- The actual determinant differential, normalized using `exp(it)` on the target circle,
is twice the central infinitesimal parameter. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom
    (X : LeftInvariantDerivation (𝓡 1) Circle) :
    ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)
        (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
          (ofCircleContinuousMonoidHom _ hQ) X) =
      2 * circleLieAlgebraEquiv X := by
  have h := LinearMap.congr_fun
    (ContinuousMonoidHom.lieWeight_comp (I := 𝓡 1) (I' := IC)
      (detContinuousMonoidHom _ hQ) (ofCircleContinuousMonoidHom _ hQ)) X
  simpa using h.symm

/-- The canonical central lift of an infinitesimal determinant parameter. The factor `1/2`
is forced by the differential of the square character. -/
def realDetLieLift : ℝ →ₗ[ℝ] 𝔤 :=
  (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
    (ofCircleContinuousMonoidHom _ hQ)).toLinearMap.comp
      (circleLieAlgebraEquiv.symm.toLinearMap.comp ((1 / 2 : ℝ) • LinearMap.id))

/-- Formula for the central lift in normalized circle Lie-algebra coordinates. -/
theorem realDetLieLift_apply (a : ℝ) :
    realDetLieLift n hQ a =
      ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
        (circleLieAlgebraEquiv.symm (a / 2)) := by
  simp [realDetLieLift, div_eq_mul_inv, mul_comm]

/-- The central half-parameter lift is a right inverse of the determinant differential. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realDetLieLift (a : ℝ) :
    ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)
      (realDetLieLift n hQ a) = a := by
  -- Congruence avoids costly dependent rewriting through the Lie-algebra models.
  calc
    _ = ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)
        (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)
          (circleLieAlgebraEquiv.symm (a / 2))) :=
      congrArg (ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ))
        (realDetLieLift_apply n hQ a)
    _ = 2 * circleLieAlgebraEquiv (circleLieAlgebraEquiv.symm (a / 2)) :=
      lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom n hQ _
    _ = a := by rw [LinearEquiv.apply_symm_apply]; ring

/-- Exponentiating the infinitesimal determinant lift gives the half-speed central path. -/
@[simp]
theorem lieExp_realDetLieLift (a : ℝ) :
    lieExp (realDetLieLift n hQ a) = ofCircle _ hQ (Circle.exp (a / 2)) := by
  rw [realDetLieLift_apply, ← ContinuousMonoidHom.map_lieExp, lieExp_circle,
    ofCircleContinuousMonoidHom_apply]

/-- A Lie-algebra ray in the determinant lift exponentiates to the half-speed central ray. -/
@[simp]
theorem lieExp_smul_realDetLieLift (t a : ℝ) :
    lieExp (t • realDetLieLift n hQ a) = ofCircle _ hQ (Circle.exp (t * a / 2)) := by
  -- Congruence avoids dependent rewriting through the Spinᶜ Lie-algebra model.
  calc
    _ = lieExp (realDetLieLift n hQ (t * a)) :=
      congrArg (fun X : 𝔤 ↦ lieExp X) ((realDetLieLift n hQ).map_smul t a).symm
    _ = _ := lieExp_realDetLieLift n hQ (t * a)

/-- The adjoint action fixes the central determinant lift. -/
@[simp]
theorem Ad_realDetLieLift (g : G) (a : ℝ) :
    Lie.Ad (I := IC) g (realDetLieLift n hQ a) = realDetLieLift n hQ a := by
  apply Lie.Ad_apply_eq_self_of_forall_commute
  intro t
  simp only [lieExp_smul_realDetLieLift]
  exact Subgroup.mem_center_iff.mp (ofCircle_mem_center _ hQ _) g

/-- The central determinant lift brackets trivially with every infinitesimal element. -/
@[simp]
theorem lie_realDetLieLift (X : 𝔤) (a : ℝ) : ⁅X, realDetLieLift n hQ a⁆ = 0 := by
  have h := Lie.hasDerivAt_Ad_lieExp_smul_apply_zero (I := IC) X (realDetLieLift n hQ a)
  simp only [Ad_realDetLieLift] at h
  exact h.unique (hasDerivAt_const 0 _)

/-- Bracketing the central determinant lift with any infinitesimal element gives zero. -/
@[simp]
theorem realDetLieLift_lie (a : ℝ) (X : 𝔤) : ⁅realDetLieLift n hQ a, X⁆ = 0 := by
  calc
    _ = -⁅X, realDetLieLift n hQ a⁆ := (lie_skew (realDetLieLift n hQ a) X).symm
    _ = -(0 : 𝔤) := congrArg Neg.neg (lie_realDetLieLift n hQ X a)
    _ = 0 := neg_zero

/-- Adding a determinant lift multiplies the exponential by the half-speed central phase. -/
@[simp]
theorem lieExp_add_realDetLieLift (X : 𝔤) (a : ℝ) :
    lieExp (X + realDetLieLift n hQ a) =
      lieExp X * ofCircle _ hQ (Circle.exp (a / 2)) := by
  calc
    _ = lieExp X * lieExp (realDetLieLift n hQ a) :=
      lieExp_add_of_commute (I := IC) (fun t ↦ by
        simp only [lieExp_smul_realDetLieLift]
        exact Subgroup.mem_center_iff.mp (ofCircle_mem_center _ hQ _) _)
    _ = _ := congrArg (fun z : G ↦ lieExp X * z) (lieExp_realDetLieLift n hQ a)

/-- The determinant differential is onto, even though the determinant character has no
chosen global square-root section. -/
theorem lieWeight_detContinuousMonoidHom_surjective :
    Function.Surjective (ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)) :=
  fun a ↦ ⟨realDetLieLift n hQ a, lieWeight_detContinuousMonoidHom_realDetLieLift n hQ a⟩

local notation "d" => ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)

/-- The determinant differential splits the Spinᶜ Lie algebra linearly. The second factor
is a determinant parameter, so reconstruction uses its half-speed central lift. -/
def realDetLieLinearEquiv : (LinearMap.ker d × ℝ) ≃ₗ[ℝ] 𝔤 :=
  ((LinearMap.exact_subtype_ker_map d).splitSurjectiveEquiv
    (LinearMap.ker d).injective_subtype
      ⟨realDetLieLift n hQ, by
        apply LinearMap.ext
        intro a
        exact lieWeight_detContinuousMonoidHom_realDetLieLift n hQ a⟩).val.symm

/-- Reconstruction adds the kernel component to the half-speed central lift. -/
@[simp]
theorem realDetLieLinearEquiv_apply (p : LinearMap.ker d × ℝ) :
    realDetLieLinearEquiv n hQ p = (p.1 : 𝔤) + realDetLieLift n hQ p.2 :=
  -- Mathlib has no application lemma for `splitSurjectiveEquiv`. Its forward splitting is
  -- the inverse of `ofBijective` on the sum of the kernel inclusion and chosen section;
  -- our inverse splitting therefore reconstructs by that sum, definitionally.
  (rfl)

/-- Every infinitesimal Spinᶜ element decomposes uniquely into an element of the determinant
kernel and the central lift of a determinant parameter. -/
theorem existsUnique_add_realDetLieLift_eq (X : 𝔤) :
    ∃! p : LinearMap.ker d × ℝ, (p.1 : 𝔤) + realDetLieLift n hQ p.2 = X := by
  simpa only [realDetLieLinearEquiv_apply] using
    (Function.bijective_iff_existsUnique _).mp (realDetLieLinearEquiv n hQ).bijective X

/-- The inverse splitting removes the central lift of the actual determinant differential. -/
@[simp]
theorem realDetLieLinearEquiv_symm_apply (X : 𝔤) :
    (realDetLieLinearEquiv n hQ).symm X =
      (⟨X - realDetLieLift n hQ (d X), by simp⟩, d X) := by
  apply (realDetLieLinearEquiv n hQ).injective
  exact ((realDetLieLinearEquiv n hQ).apply_symm_apply X).trans
    (by simp only [realDetLieLinearEquiv_apply, sub_add_cancel])

/-- The central weight-one inclusion `U(1) → Spinᶜ(n)` as a smooth homomorphism, obtained from
`ofCircleContinuousMonoidHom` by automatic smoothness. -/
def realOfCircleSmoothHom : ContMDiffMonoidMorphism (𝓡 1) IC ∞ Circle G :=
  (ofCircleContinuousMonoidHom (realCliffordForm n 0) hQ).toContMDiffMonoidMorphism (𝓡 1) IC

@[simp]
theorem realOfCircleSmoothHom_apply (z : Circle) :
    realOfCircleSmoothHom n hQ z = ofCircle (realCliffordForm n 0) hQ z := by
  simp [realOfCircleSmoothHom]

@[simp]
theorem realMkSmoothHom_comp_inr :
    (realMkSmoothHom n hQ).comp ContMDiffMonoidMorphism.inr = realOfCircleSmoothHom n hQ :=
  DFunLike.coe_injective <| funext fun z ↦ by simp [ofCircle_apply]

/-- The weight-two determinant character `Spinᶜ(n) → U(1)` as a smooth homomorphism, obtained from
`detContinuousMonoidHom` by automatic smoothness. -/
def realDetSmoothHom : ContMDiffMonoidMorphism IC (𝓡 1) ∞ G Circle :=
  (detContinuousMonoidHom (realCliffordForm n 0) hQ).toContMDiffMonoidMorphism IC (𝓡 1)

@[simp]
theorem realDetSmoothHom_apply (x : G) :
    realDetSmoothHom n hQ x = det (realCliffordForm n 0) hQ x := by
  simp [realDetSmoothHom]

@[simp]
theorem realDetSmoothHom_comp_realOfSpinSmoothHom :
    (realDetSmoothHom n hQ).comp (realOfSpinSmoothHom n hQ) = 1 :=
  DFunLike.coe_injective <| funext fun s ↦ by simp [det_ofSpin]

/-- In normalized circle Lie-algebra coordinates, `lieMap (realDetSmoothHom n hQ)` is the
determinant weight `lieWeight (detContinuousMonoidHom _ hQ)`. -/
@[simp]
theorem circleLieAlgebraEquiv_lieMap_realDetSmoothHom (Y : 𝔤) :
    circleLieAlgebraEquiv (lieMap (realDetSmoothHom n hQ) Y) = d Y :=
  (congrArg circleLieAlgebraEquiv
    (DFunLike.congr_fun
      (ContinuousMonoidHom.lieMap_def (I := IC) (I' := 𝓡 1)
        (detContinuousMonoidHom (realCliffordForm n 0) hQ)).symm Y)).trans
    (ContinuousMonoidHom.lieWeight_apply (I := IC) _ Y).symm

/-- The differential of `det` vanishes on the image of `𝔰𝔭𝔦𝔫(n)`. -/
@[simp]
theorem lieMap_realDetSmoothHom_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    lieMap (realDetSmoothHom n hQ) (lieMap (realOfSpinSmoothHom n hQ) X) = 0 :=
  (lieMap_lieMap_of_comp_eq (realDetSmoothHom_comp_realOfSpinSmoothHom n hQ) X).trans
    (by simp only [lieMap_one, zero_apply])

/-- The determinant differential vanishes on the image of `𝔰𝔭𝔦𝔫(n)` in `𝔰𝔭𝔦𝔫ᶜ(n)`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_lieMap_realOfSpinSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    d (lieMap (realOfSpinSmoothHom n hQ) X) = 0 :=
  (circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ _).symm.trans <|
    (congrArg circleLieAlgebraEquiv
      (lieMap_realDetSmoothHom_lieMap_realOfSpinSmoothHom n hQ X)).trans
      (map_zero circleLieAlgebraEquiv)

/-- On the central circle Lie algebra, the determinant weight of `realOfCircleSmoothHom` acts by
twice the normalized circle parameter. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    d (lieMap (realOfCircleSmoothHom n hQ) Z) = 2 * circleLieAlgebraEquiv Z :=
  (congrArg d (DFunLike.congr_fun
    (ContinuousMonoidHom.lieMap_def (I := 𝓡 1) (I' := IC)
      (ofCircleContinuousMonoidHom (realCliffordForm n 0) hQ)).symm Z)).trans
    (lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom n hQ Z)

/-- On the central circle Lie algebra, the differential of `det` acts by multiplication by `2`. -/
@[simp]
theorem lieMap_realDetSmoothHom_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    lieMap (realDetSmoothHom n hQ) (lieMap (realOfCircleSmoothHom n hQ) Z) = (2 : ℝ) • Z :=
  circleLieAlgebraEquiv.injective <|
    (circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ _).trans <|
      (lieWeight_detContinuousMonoidHom_lieMap_realOfCircleSmoothHom n hQ Z).trans
        (by rw [map_smul, smul_eq_mul] :
          circleLieAlgebraEquiv ((2 : ℝ) • Z) = 2 * circleLieAlgebraEquiv Z).symm

/-- Reconstructing the central determinant lift from the determinant weight of a central circle
derivation recovers that circle derivation. -/
theorem realDetLieLift_lieWeight_lieMap_realOfCircleSmoothHom
    (Z : LeftInvariantDerivation (𝓡 1) Circle) :
    realDetLieLift n hQ (d (lieMap (realOfCircleSmoothHom n hQ) Z)) =
      lieMap (realOfCircleSmoothHom n hQ) Z :=
  -- Congruence avoids costly `isDefEq` unfolding across the Spinᶜ Lie-algebra model.
  (congrArg (realDetLieLift n hQ)
    (lieWeight_detContinuousMonoidHom_lieMap_realOfCircleSmoothHom n hQ Z)).trans <|
    (realDetLieLift_apply n hQ _).trans <|
      (congrArg (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
        (ofCircleContinuousMonoidHom _ hQ)) <| by
          rw [mul_div_cancel_left₀ _ two_ne_zero, LinearEquiv.symm_apply_apply]).trans
        (DFunLike.congr_fun
          (ContinuousMonoidHom.lieMap_def (I := 𝓡 1) (I' := IC) _) Z)

/-- Membership in the kernel ideal of `det`'s Lie map is vanishing of the determinant weight. -/
theorem mem_ker_lieMap_realDetSmoothHom_iff (Y : 𝔤) :
    Y ∈ (lieMap (realDetSmoothHom n hQ)).ker ↔ d Y = 0 :=
  LieHom.mem_ker.trans <| circleLieAlgebraEquiv.map_eq_zero_iff.symm.trans <|
    Eq.to_iff (congrArg (· = 0) (circleLieAlgebraEquiv_lieMap_realDetSmoothHom n hQ Y))

end CliffordAlgebra.spinCGroup
