/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.HalfSpin
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character

/-!
# The infinitesimal determinant of Spinᶜ

The determinant character has weight two on the central circle, whereas half-spinors have
weight one. Consequently a determinant infinitesimal parameter `a` lifts centrally as `a / 2`.
We construct this right inverse of the actual determinant differential and the resulting
splitting into its kernel and the determinant parameter. The exponential of the right inverse
is the central path `[1, exp(ia/2)]`; it is not a group-theoretic square-root character.

For the actual framed half-spin representation, we also differentiate this path in operator
norm. At the identity its derivative is `(ia/2) Id`. This is the local representation-theoretic
normalization used when lifting a determinant connection; no global principal connection is
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

/-- The determinant character as a continuous homomorphism on the actual compact Spinᶜ group. -/
def realDetCharacter : G →ₜ* Circle where
  toMonoidHom := det _ hQ
  continuous_toFun := continuous_det _ hQ

/-- The weight-one central circle of the compact Spinᶜ group. -/
def realCentralCircle : Circle →ₜ* G where
  toMonoidHom := ofCircle _ hQ
  continuous_toFun := by
    have h : Continuous (fun z : Circle ↦ mk _ hQ (1, z)) :=
      (isLocalDiffeomorph_realMk n hQ).contMDiff.continuous.comp
        (continuous_const.prodMk continuous_id)
    exact h.congr fun z ↦ (ofCircle_apply _ hQ z).symm

/-- The bundled determinant character is the original quotient determinant. -/
@[simp]
theorem realDetCharacter_apply (x : G) : realDetCharacter n hQ x = det _ hQ x := (rfl)

/-- The bundled central inclusion is the original weight-one circle inclusion. -/
@[simp]
theorem realCentralCircle_apply (z : Circle) :
    realCentralCircle n hQ z = ofCircle _ hQ z := (rfl)

/-- The determinant restricted to the central circle is the square character. -/
@[simp]
theorem realDetCharacter_comp_realCentralCircle :
    (realDetCharacter n hQ).comp (realCentralCircle n hQ) =
      (ContinuousMonoidHom.id Circle) ^ 2 := by
  ext z
  simp [ContinuousMonoidHom.pow_apply, det_ofCircle]

/-- The actual determinant differential, normalized using `exp(it)` on the target circle,
is twice the central infinitesimal parameter. -/
@[simp]
theorem lieWeight_realDetCharacter_lieMap_realCentralCircle
    (X : LeftInvariantDerivation (𝓡 1) Circle) :
    ContinuousMonoidHom.lieWeight (I := IC) (realDetCharacter n hQ)
        (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (realCentralCircle n hQ) X) =
      2 * circleLieAlgebraEquiv X := by
  have h := LinearMap.congr_fun
    (ContinuousMonoidHom.lieWeight_comp (I := 𝓡 1) (I' := IC)
      (realDetCharacter n hQ) (realCentralCircle n hQ)) X
  simpa using h.symm

/-- The canonical central lift of an infinitesimal determinant parameter. The factor `1/2`
is forced by the differential of the square character. -/
def realDetLieLift : ℝ →ₗ[ℝ] 𝔤 :=
  (ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC)
    (realCentralCircle n hQ)).toLinearMap.comp
      (circleLieAlgebraEquiv.symm.toLinearMap.comp ((1 / 2 : ℝ) • LinearMap.id))

/-- Formula for the central lift in normalized circle Lie-algebra coordinates. -/
theorem realDetLieLift_apply (a : ℝ) :
    realDetLieLift n hQ a =
      ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (realCentralCircle n hQ)
        (circleLieAlgebraEquiv.symm (a / 2)) := by
  simp [realDetLieLift, div_eq_mul_inv, mul_comm]

/-- The central half-parameter lift is a right inverse of the determinant differential. -/
@[simp]
theorem lieWeight_realDetCharacter_realDetLieLift (a : ℝ) :
    ContinuousMonoidHom.lieWeight (I := IC) (realDetCharacter n hQ)
      (realDetLieLift n hQ a) = a := by
  have h := lieWeight_realDetCharacter_lieMap_realCentralCircle n hQ
    (circleLieAlgebraEquiv.symm (a / 2))
  have hcoord := congrArg (fun r : ℝ ↦ 2 * r)
    (circleLieAlgebraEquiv.apply_symm_apply (a / 2))
  exact (congrArg (ContinuousMonoidHom.lieWeight (I := IC) (realDetCharacter n hQ))
    (realDetLieLift_apply n hQ a)).trans (h.trans (hcoord.trans (by ring)))

/-- Exponentiating the infinitesimal determinant lift gives the half-speed central path. -/
@[simp]
theorem lieExp_realDetLieLift (a : ℝ) :
    lieExp (realDetLieLift n hQ a) = ofCircle _ hQ (Circle.exp (a / 2)) := by
  rw [realDetLieLift_apply, ← ContinuousMonoidHom.map_lieExp, lieExp_circle,
    realCentralCircle_apply]

/-- The determinant differential is onto, even though the determinant character has no
chosen global square-root section. -/
theorem surjective_lieWeight_realDetCharacter :
    Function.Surjective (ContinuousMonoidHom.lieWeight (I := IC) (realDetCharacter n hQ)) :=
  fun a ↦ ⟨realDetLieLift n hQ a, lieWeight_realDetCharacter_realDetLieLift n hQ a⟩

local notation "d" => ContinuousMonoidHom.lieWeight (I := IC) (realDetCharacter n hQ)

/-- Every infinitesimal Spinᶜ element decomposes uniquely into an element of the determinant
kernel and the central lift of a determinant parameter. -/
theorem existsUnique_realDetLie_decomposition (X : 𝔤) :
    ∃! p : LinearMap.ker d × ℝ, (p.1 : 𝔤) + realDetLieLift n hQ p.2 = X := by
  refine ⟨(⟨X - realDetLieLift n hQ (d X), by simp⟩, d X), by simp, ?_⟩
  rintro ⟨Y, a⟩ h
  have ha : d X = a := by
    have h' := congrArg d h.symm
    simpa only [map_add, lieWeight_realDetCharacter_realDetLieLift,
      LinearMap.mem_ker.mp Y.property, zero_add] using h'
  apply Prod.ext
  · apply Subtype.ext
    exact eq_sub_iff_add_eq.mpr
      ((congrArg (fun r : ℝ ↦ (Y : 𝔤) + realDetLieLift n hQ r) ha).trans h)
  · exact ha.symm

/-- The determinant differential splits the Spinᶜ Lie algebra linearly. The second factor
is a determinant parameter, so reconstruction uses its half-speed central lift. -/
def realDetLieEquiv : (LinearMap.ker d × ℝ) ≃ₗ[ℝ] 𝔤 :=
  LinearEquiv.ofBijective ((LinearMap.ker d).subtype.coprod (realDetLieLift n hQ))
    ((Function.bijective_iff_existsUnique _).mpr fun X ↦
      existsUnique_realDetLie_decomposition n hQ X)

/-- Reconstruction adds the kernel component to the half-speed central lift. -/
@[simp]
theorem realDetLieEquiv_apply (p : LinearMap.ker d × ℝ) :
    realDetLieEquiv n hQ p = (p.1 : 𝔤) + realDetLieLift n hQ p.2 := (rfl)

/-- The inverse splitting removes the central lift of the actual determinant differential. -/
@[simp]
theorem realDetLieEquiv_symm_apply (X : 𝔤) :
    (realDetLieEquiv n hQ).symm X =
      (⟨X - realDetLieLift n hQ (d X), by simp⟩, d X) := by
  apply (realDetLieEquiv n hQ).injective
  exact ((realDetLieEquiv n hQ).apply_symm_apply X).trans
    (by simp only [realDetLieEquiv_apply, sub_add_cancel])

end CliffordAlgebra.spinCGroup

namespace Orientation

open Module Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "S" => eigenspace (ρ (chirality Q o)) ε

-- Match the normed-algebra parent structures used by the framed smooth representation.
/-- Operator-norm ring structure on half-spin endomorphisms. -/
local instance : NormedRing (S →L[ℂ] S) := ContinuousLinearMap.toNormedRing
/-- Complex normed-space structure on half-spin endomorphisms. -/
local instance : NormedSpace ℂ (S →L[ℂ] S) := ContinuousLinearMap.toNormedSpace
/-- The underlying real normed algebra of half-spin endomorphisms. -/
local instance : NormedAlgebra ℝ (S →L[ℂ] S) := NormedAlgebra.complexToReal
/-- The real scalar action selected by the normed-algebra structure. -/
local instance : NormedSpace ℝ (S →L[ℂ] S) :=
  NormedAlgebra.toNormedSpace (𝕜 := ℝ) (S →L[ℂ] S)

/-- Along a determinant parameter with velocity `a`, the half-spin action has operator-norm
derivative `(ia/2) Id` times the phase at time `t`. Differentiation is over `ℝ`. -/
theorem hasDerivAt_realSpinCHalfSpinSmoothHom_central (a t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ realSpinCHalfSpinSmoothHom o hQ b ρ ε
      (lieExp (spinCGroup.realDetLieLift 4 hpos (s * a))))
      ((Complex.I * (a / 2) * (Circle.exp (t * a / 2) : ℂ)) • (1 : S →L[ℂ] S)) t := by
  simp only [spinCGroup.lieExp_realDetLieLift, realSpinCHalfSpinSmoothHom_ofCircle,
    Circle.coe_exp]
  have harg : HasDerivAt (fun s : ℝ ↦ ((s * a / 2 : ℝ) : ℂ) * Complex.I)
      (((a / 2 : ℝ) : ℂ) * Complex.I) t := by
    simpa only [one_mul, id_eq] using
      ((((hasDerivAt_id t).mul_const a).div_const 2).ofReal_comp).mul_const Complex.I
  convert ((Complex.hasDerivAt_exp _).comp t harg).smul_const (1 : S →L[ℂ] S) using 1
  · funext s
    simp only [Function.comp_apply]
  · congr 1
    push_cast
    ring

end Orientation
