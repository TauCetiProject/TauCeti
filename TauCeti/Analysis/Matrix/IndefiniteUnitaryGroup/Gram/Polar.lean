/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Gram.Section
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Haar.Basic
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.SkewHermitian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.MeasureTheory.Measure.Haar.Matrix.SkewAdjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex
import TauCeti.LinearAlgebra.Matrix.Kronecker.MulLeftMulRight
import TauCeti.LinearAlgebra.Prod

/-!
# The polar formula for the Gram map on bases

Let `A` be an invertible Hermitian complex matrix of size `r`, for instance a Hermitian involution
`J = diag(1, …, 1, -1, …, -1)`, and `U(A) = Matrix.unitaryGroupOf A`. The Gram map
`Y ↦ Yᴴ A Y` is invariant under `U(A)` acting on the left. Given a section `σ` of the Gram map
over an open set `V` of Hermitian matrices (`Matrix.IsGramSection A V σ`), every `Y` with
`Yᴴ A Y ∈ V` is `γ σ(Yᴴ A Y)` for a unique `γ ∈ U(A)`. The **polar formula**
(`Matrix.IsGramSection.lintegral_eq`) computes Lebesgue measure `dY` in these coordinates: for
every measurable `K ≥ 0`,

`∫_{Yᴴ A Y ∈ V} K(Y) dY = 2 ^ (-r) |det A| ^ (-2 r) ∫_V ∫_{U(A)} K(γ σ(T)) dμ^c(γ) dT`,

where `dT` is `TauCeti.hermitianLebesgue r` and `μ^c` is the Cayley measure
(`Matrix.unitaryGroupOf.cayleyMeasure`) built from the Lebesgue measure
`TauCeti.skewHermitianLebesgue r` of the coordinates `Im S_aa`, `Re S_ab`, `Im S_ab` (`a < b`) of
skew-Hermitian matrices. For a Hermitian involution `|det A| = 1`, and for the compact-dual
normalisation `μ^c / vol U(r)` the constant becomes `vol U(r) / 2 ^ r`, the same for every
signature.

## Proof

The map `Ψ(Z) = φ(S) σ(T)`, with `Z = S + T / 2` split into its skew-Hermitian part `S` and
Hermitian part `T / 2` and `φ` the Cayley chart of `U(A)`, is injective on the set of `Z` with `S`
in the source of the chart and `T ∈ V`, and its image is, up to a null set, the set of `Y` with
`Yᴴ A Y ∈ V`. The exceptional `Y = γ σ(T)` are those with `1 + γ` singular; for each `Y`, almost
every `g ∈ U(A)` moves `Y` to a nonexceptional `g Y` (right invariance of `μ^c`, and `μ^c` lives
on the image of the chart), so by Fubini's theorem and the invariance of `dY` under `U(A)` almost
every `Y` is nonexceptional. The Jacobian of `Ψ` is computed after multiplying by `Yᴴ A`:
`Yᴴ A dΨ(dZ) = σᴴ ω(dS) σ + σᴴ A dσ(dT)`, with `ω` the logarithmic derivative of the chart, whose
Jacobian is the Cayley density. The first term is skew-Hermitian, and the Hermitian part of the
second is `dT / 2`, so in skew-Hermitian and Hermitian coordinates this map is block triangular,
with Jacobian `|det σ| ^ (2 r)` times the Cayley density. Left multiplication by `Yᴴ A` has
Jacobian `|det σ| ^ (2 r) |det A| ^ (2 r)`, so `|det dΨ|` is the Cayley density divided by
`|det A| ^ (2 r)`. Finally `dZ = 2 ^ (-r) dS dT`
(`TauCeti.lintegral_eq_inv_two_pow_mul_lintegral_lintegral_add`).

Derivatives are taken for the Frobenius norm on matrices, as in
`TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Cayley`.

## Main results

* `Matrix.IsGramSection.lintegral_eq`: the polar formula.
* `Matrix.IsGramSection.lintegral_eq_of_mul_self_eq_one`: the polar formula for a Hermitian
  involution.

## Provenance

Adapted from `New.IsGramSection.lintegral_eq`, `New.IsGramSection.lintegral_eq_cayleyChart_mul`,
`New.IsGramSection.exists_hasFDerivAt_cayleyChart_mul`,
`New.IsGramSection.abs_det_skewAddHerm_symm_comp`, `New.IsGramSection.ae_isUnit_add`,
`New.IsGramSection.injOn_cayleyChart_mul` and `New.IsGramSection.preimage_gramCoords_ae_eq_image` in
`src/Lib/DiscreteSeries/Haar/GramPolar.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC). There `A` is a Hermitian involution, matrices are
read in real coordinates of their own, and the Haar measure is normalised; here `A` is any
invertible Hermitian matrix, the Hermitian and skew-Hermitian matrices are the submodules of Tau
Ceti's Cayley chart and Gram sections, and the constant is explicit for the unnormalised Cayley
measure. The measure on the tuples of vectors with a prescribed Gram matrix goes back to
C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace Matrix

/-! ### Skew-Hermitian and Hermitian coordinates -/

section Coordinates

variable {n : Type*}

/-- Square matrices in Hermitian and skew-Hermitian coordinates, `Z ↦ (Z + Zᴴ, (Z - Zᴴ) / 2)`, with
inverse `(T, S) ↦ S + T / 2`: Mathlib's decomposition `StarModule.decomposeProdAdjoint` into
self-adjoint and skew-adjoint parts, with the self-adjoint part doubled. -/
private def polarCoordEquiv :
    Matrix n n ℂ ≃ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ) ×
      skewAdjoint.submodule ℝ (Matrix n n ℂ) :=
  (StarModule.decomposeProdAdjoint ℝ (Matrix n n ℂ)).trans
    ((LinearEquiv.smulOfNeZero ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)) 2 two_ne_zero).prodCongr
      (LinearEquiv.refl ℝ (skewAdjoint.submodule ℝ (Matrix n n ℂ))))

/-- The Hermitian coordinate `Z + Zᴴ`, twice the self-adjoint part, of a square matrix
`Z = S + T / 2`. -/
private def hermCoord : Matrix n n ℂ →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ) :=
  LinearMap.fst ℝ _ _ ∘ₗ polarCoordEquiv.toLinearMap

/-- The skew-Hermitian coordinate `(Z - Zᴴ) / 2`, the skew-adjoint part, of a square matrix
`Z = S + T / 2`. -/
private def skewCoord : Matrix n n ℂ →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix n n ℂ) :=
  LinearMap.snd ℝ _ _ ∘ₗ polarCoordEquiv.toLinearMap

private theorem polarCoordEquiv_symm_apply
    (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    polarCoordEquiv.symm x = (x.2 : Matrix n n ℂ) + (2⁻¹ : ℝ) • (x.1 : Matrix n n ℂ) := by
  -- Mathlib's `decomposeProdAdjoint` lands in `selfAdjoint A × skewAdjoint A`, whose carriers are
  -- the submodules' only up to unfolding, so its apply lemmas do not match the composite and
  -- `rw`/`simp` fail. Unfold `trans`, `prodCongr`, `smulOfNeZero.symm` and
  -- `decomposeProdAdjoint.symm` (the sum of the two components) by hand instead.
  change (2⁻¹ : ℝ) • (x.1 : Matrix n n ℂ) + x.2 = _
  exact add_comm _ _

private theorem fst_polarCoordEquiv (Z : Matrix n n ℂ) : (polarCoordEquiv Z).1 = hermCoord Z := by
  simp [hermCoord]

private theorem snd_polarCoordEquiv (Z : Matrix n n ℂ) : (polarCoordEquiv Z).2 = skewCoord Z := by
  simp [skewCoord]

private theorem coe_hermCoord (Z : Matrix n n ℂ) :
    (hermCoord Z : Matrix n n ℂ) = Z + star Z := by
  -- As in `polarCoordEquiv_symm_apply`, Mathlib's apply lemmas for `decomposeProdAdjoint` do not
  -- match through the submodule carriers. Unfold `hermCoord`, `LinearMap.fst`, `smulOfNeZero` and
  -- `decomposeProdAdjoint` by hand to twice the self-adjoint part, which `simp` then computes.
  change (2 : ℝ) • (selfAdjointPart ℝ Z : Matrix n n ℂ) = _
  simp [smul_smul]

private theorem skewCoord_add_smul (S : skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (T : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    skewCoord ((S : Matrix n n ℂ) + (2⁻¹ : ℝ) • (T : Matrix n n ℂ)) = S := by
  rw [← polarCoordEquiv_symm_apply (T, S)]
  exact congrArg Prod.snd (polarCoordEquiv.apply_symm_apply (T, S))

private theorem hermCoord_add_smul (S : skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (T : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    hermCoord ((S : Matrix n n ℂ) + (2⁻¹ : ℝ) • (T : Matrix n n ℂ)) = T := by
  rw [← polarCoordEquiv_symm_apply (T, S)]
  exact congrArg Prod.fst (polarCoordEquiv.apply_symm_apply (T, S))

private theorem coe_skewCoord_add_smul_hermCoord (Z : Matrix n n ℂ) :
    (skewCoord Z : Matrix n n ℂ) + (2⁻¹ : ℝ) • (hermCoord Z : Matrix n n ℂ) = Z :=
  (polarCoordEquiv_symm_apply (polarCoordEquiv Z)).symm.trans (polarCoordEquiv.symm_apply_apply Z)

/-- A skew-Hermitian matrix is its own skew-Hermitian coordinate. -/
private theorem coe_skewCoord_of_star_eq_neg {Z : Matrix n n ℂ} (hZ : star Z = -Z) :
    (skewCoord Z : Matrix n n ℂ) = Z := by
  simpa using congrArg Subtype.val
    (skewCoord_add_smul ⟨Z, skewAdjoint.mem_iff.2 hZ⟩ (0 : selfAdjoint.submodule ℝ _))

end Coordinates

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An invertible complex matrix has determinant of positive squared absolute value. -/
private theorem normSq_det_pos {M : Matrix n n ℂ} (hM : IsUnit M) : 0 < normSq M.det :=
  normSq_pos.2 ((isUnit_iff_isUnit_det _).1 hM).ne_zero

namespace IsGramSection

open unitaryGroupOf

variable {A : Matrix n n ℂ} {V : Set (selfAdjoint.submodule ℝ (Matrix n n ℂ))}
  {σ : selfAdjoint.submodule ℝ (Matrix n n ℂ) → Matrix n n ℂ}

/-! ### The polar map and its Jacobian -/

section Jacobian

/-- The **polar map** `Z = S + T / 2 ↦ φ(S) σ(T)`, with `φ` the Cayley chart of `U(A)`. -/
private def polarMap (A : Matrix n n ℂ) (σ : selfAdjoint.submodule ℝ (Matrix n n ℂ) → Matrix n n ℂ)
    (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  cayleyChart A (skewCoord Z) * σ (hermCoord Z)

/-- The domain of the polar map: `S` in the source of the chart and `T ∈ V`. -/
private def polarDomain (A : Matrix n n ℂ) (V : Set (selfAdjoint.submodule ℝ (Matrix n n ℂ))) :
    Set (Matrix n n ℂ) :=
  {Z | skewCoord Z ∈ cayleyChartSource A ∧ hermCoord Z ∈ V}

open scoped Matrix.Norms.Frobenius

private theorem isOpen_polarDomain (hV : IsOpen V) : IsOpen (polarDomain A V) :=
  (isOpen_cayleyChartSource.preimage (LinearMap.continuous_of_finiteDimensional skewCoord)).inter
    (hV.preimage (LinearMap.continuous_of_finiteDimensional hermCoord))

/-- The polar map is differentiable on its domain, with derivative
`dZ ↦ φ(S) dσ(dT) + dφ(dS) σ(T)`. -/
private theorem exists_hasFDerivAt_polarMap (hσ : IsGramSection A V σ) {Z : Matrix n n ℂ}
    (hZ : Z ∈ polarDomain A V) :
    ∃ D : Matrix n n ℂ →L[ℝ] Matrix n n ℂ, HasFDerivAt (polarMap A σ) D Z ∧
      ∀ W, D W = cayleyChart A (skewCoord Z) * fderiv ℝ σ (hermCoord Z) (hermCoord W) +
        fderiv ℝ (cayleyChart A) (skewCoord Z) (skewCoord W) * σ (hermCoord Z) := by
  have h1 := (differentiableAt_cayleyChart (mem_cayleyChartSource.1 hZ.1)).hasFDerivAt.comp Z
    (LinearMap.toContinuousLinearMap skewCoord).hasFDerivAt
  have h2 := (hσ.differentiableAt hZ.2).hasFDerivAt.comp Z
    (LinearMap.toContinuousLinearMap hermCoord).hasFDerivAt
  exact ⟨_, h1.mul' h2, fun _ ↦ rfl⟩

/-- After multiplication by `Yᴴ A`, with `Y = φ(S) σ(T)` the value of the polar map at
`Z = S + T / 2`, its derivative at `S' + T' / 2` is `σ(T)ᴴ A dσ(T') + σ(T)ᴴ ω(S') σ(T)`, where
`ω(S') = φ(S)ᴴ A dφ(S')` is the logarithmic derivative of the chart. -/
private theorem mul_fderiv_polarMap (hA : A.IsHermitian) {Z : Matrix n n ℂ}
    (hZ : Z ∈ polarDomain A V) {D : Matrix n n ℂ →L[ℝ] Matrix n n ℂ}
    (hD : ∀ W, D W = cayleyChart A (skewCoord Z) * fderiv ℝ σ (hermCoord Z) (hermCoord W) +
        fderiv ℝ (cayleyChart A) (skewCoord Z) (skewCoord W) * σ (hermCoord Z))
    (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    star (cayleyChart A (skewCoord Z) * σ (hermCoord Z)) * A * D (polarCoordEquiv.symm x) =
      star (σ (hermCoord Z)) * A * fderiv ℝ σ (hermCoord Z) x.1 +
        star (σ (hermCoord Z)) * (star (cayleyChart A (skewCoord Z)) * A *
          fderiv ℝ (cayleyChart A) (skewCoord Z) x.2) * σ (hermCoord Z) := by
  have hc (X : Matrix n n ℂ) :
      star (cayleyChart A (skewCoord Z)) * (A * (cayleyChart A (skewCoord Z) * X)) = A * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      star_cayleyChart_mul_mul_cayleyChart hA (mem_cayleyChartSource.1 hZ.1)]
  rw [hD, polarCoordEquiv_symm_apply, hermCoord_add_smul, skewCoord_add_smul]
  simp only [star_mul, Matrix.mul_add, Matrix.mul_assoc, hc]

/-- **The polar derivative is block triangular.** Read in Hermitian and skew-Hermitian
coordinates, the derivative `D` of the polar map followed by multiplication by `Yᴴ A` keeps the
Hermitian coordinate, by `Matrix.IsGramSection.conjTranspose_mul_mul_fderiv_add`, and on
skew-Hermitian matrices its skew-Hermitian coordinate is `X ↦ σᴴ ω(X) σ`, with `ω` the logarithmic
derivative of the chart. So both have the same determinant. -/
private theorem det_mulLeft_comp_fderiv_polarMap (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) {Z : Matrix n n ℂ} (hZ : Z ∈ polarDomain A V)
    {D : Matrix n n ℂ →L[ℝ] Matrix n n ℂ}
    (hD : ∀ W, D W = cayleyChart A (skewCoord Z) * fderiv ℝ σ (hermCoord Z) (hermCoord W) +
        fderiv ℝ (cayleyChart A) (skewCoord Z) (skewCoord W) * σ (hermCoord Z)) :
    LinearMap.det (LinearMap.mulLeft ℝ (star (cayleyChart A (skewCoord Z) * σ (hermCoord Z)) * A)
        ∘ₗ (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)) =
      LinearMap.det (skewAdjointConjugate ℝ (star (σ (hermCoord Z))) ∘ₗ
        LinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
          (LinearMap.mulLeft ℝ (star (cayleyChart A (skewCoord Z)) * A) ∘ₗ
            (fderiv ℝ (cayleyChart A) (skewCoord Z) :
              skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ))
          (star_cayleyChart_mul_mul_fderiv_cayleyChart_mem hA hA'
            (mem_cayleyChartSource.1 hZ.1))) := by
  set ω := LinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (LinearMap.mulLeft ℝ (star (cayleyChart A (skewCoord Z)) * A) ∘ₗ
      (fderiv ℝ (cayleyChart A) (skewCoord Z) :
        skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ))
    (star_cayleyChart_mul_mul_fderiv_cayleyChart_mem hA hA' (mem_cayleyChartSource.1 hZ.1))
  have hω (X : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      (ω X : Matrix n n ℂ) =
        star (cayleyChart A (skewCoord Z)) * A * fderiv ℝ (cayleyChart A) (skewCoord Z) X := by
    simp [ω, Matrix.mul_assoc]
  have hωskew (X : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      star (star (σ (hermCoord Z)) * (ω X : Matrix n n ℂ) * σ (hermCoord Z)) =
        -(star (σ (hermCoord Z)) * (ω X : Matrix n n ℂ) * σ (hermCoord Z)) := by
    have h : star (ω X : Matrix n n ℂ) = -ω X := skewAdjoint.mem_iff.1 (ω X).property
    simp only [star_mul, h, star_star, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  -- The map in Hermitian and skew-Hermitian coordinates.
  let g := polarCoordEquiv.toLinearMap ∘ₗ
    (LinearMap.mulLeft ℝ (star (cayleyChart A (skewCoord Z) * σ (hermCoord Z)) * A) ∘ₗ
      (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)) ∘ₗ polarCoordEquiv.symm.toLinearMap
  -- Its Hermitian coordinate is the identity.
  have hg (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      g x = polarCoordEquiv (star (cayleyChart A (skewCoord Z) * σ (hermCoord Z)) * A *
        D (polarCoordEquiv.symm x)) := by
    simp [g, Matrix.mul_assoc]
  have hg1 (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      (g x).1 = x.1 := by
    apply Subtype.ext
    rw [hg, fst_polarCoordEquiv, coe_hermCoord, mul_fderiv_polarMap hA hZ hD, ← hω, star_add,
      hωskew]
    have h := hσ.conjTranspose_mul_mul_fderiv_add hZ.2 x.1
    rw [← star_eq_conjTranspose, ← star_eq_conjTranspose] at h
    rw [← h, star_mul, star_mul, star_eq_conjTranspose A, hA.eq, star_star, ← Matrix.mul_assoc]
    abel
  -- On skew-Hermitian matrices, its skew-Hermitian coordinate is `X ↦ σᴴ ω(X) σ`.
  have hg2 : LinearMap.snd ℝ _ _ ∘ₗ g ∘ₗ LinearMap.inr ℝ _ _ =
      skewAdjointConjugate ℝ (star (σ (hermCoord Z))) ∘ₗ ω := by
    refine LinearMap.ext fun X ↦ Subtype.ext ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply, hg,
      snd_polarCoordEquiv, LinearMap.comp_apply, mul_fderiv_polarMap hA hZ hD, ← hω,
      coe_skewAdjointConjugate_apply, map_zero, Matrix.mul_zero, zero_add,
      coe_skewCoord_of_star_eq_neg (hωskew X), star_eq_conjTranspose (σ (hermCoord Z)),
      conjTranspose_conjTranspose]
  rw [← hg2, ← LinearMap.det_eq_det_snd_comp_comp_inr hg1, LinearMap.det_conj]

/-- **The Jacobian of the polar map.** At a point `Z = S + T / 2` of its domain, the derivative of
the polar map has determinant of absolute value `|det A| ^ (-2 n)` times the Cayley density
`|det (1 - A⁻¹ S / 2)| ^ (-2 n)`. -/
private theorem abs_det_polarMap (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) {Z : Matrix n n ℂ} (hZ : Z ∈ polarDomain A V)
    {D : Matrix n n ℂ →L[ℝ] Matrix n n ℂ}
    (hD : ∀ W, D W = cayleyChart A (skewCoord Z) * fderiv ℝ σ (hermCoord Z) (hermCoord W) +
        fderiv ℝ (cayleyChart A) (skewCoord Z) (skewCoord W) * σ (hermCoord Z)) :
    |LinearMap.det (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)| =
      (normSq A.det ^ Fintype.card n)⁻¹ *
        (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (skewCoord Z : Matrix n n ℂ))).det ^
          Fintype.card n)⁻¹ := by
  -- Determinants of the factors: `|det φ(S)| = 1`, so multiplication by `Yᴴ A`, with
  -- `Y = φ(S) σ(T)`, has real determinant `(|det σ(T)| |det A|) ^ (2 n)`.
  have hcd : normSq (cayleyChart A (skewCoord Z)).det = 1 := by
    rw [← coe_cayleyChartUnitary hA hZ.1, normSq_eq_norm_sq, CStarRing.norm_of_mem_unitary
      (det_mem_unitary_of_mem_unitaryGroupOf hA' (cayleyChartUnitary A (skewCoord Z)).property),
      one_pow]
  have hdetP : normSq (star (cayleyChart A (skewCoord Z) * σ (hermCoord Z)) * A).det =
      normSq (σ (hermCoord Z)).det * normSq A.det := by
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose, det_mul, map_mul, Complex.star_def,
      normSq_conj, map_mul, hcd, one_mul]
  have hdetC : LinearMap.det (skewAdjointConjugate ℝ (star (σ (hermCoord Z)))) =
      normSq (σ (hermCoord Z)).det ^ Fintype.card n := by
    rw [det_skewAdjointConjugate Complex.mem_range_algebraMap_of_isSelfAdjoint
      Complex.val_mk0_I_mem_skewAdjoint, Algebra.norm_complex_apply, star_eq_conjTranspose,
      det_conjTranspose, Complex.star_def, normSq_conj]
  -- The block triangular form gives `det D` up to these factors.
  have key : (normSq (σ (hermCoord Z)).det * normSq A.det) ^ Fintype.card n *
      LinearMap.det (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) =
      normSq (σ (hermCoord Z)).det ^ Fintype.card n *
        (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (skewCoord Z : Matrix n n ℂ))).det ^
          Fintype.card n)⁻¹ := by
    rw [← hdetP, ← det_mulLeft_complex, ← LinearMap.det_comp,
      det_mulLeft_comp_fderiv_polarMap hA hA' hσ hZ hD, LinearMap.det_comp, hdetC,
      det_codRestrict_mulLeft_comp_fderiv_cayleyChart hA hA' (mem_cayleyChartSource.1 hZ.1)]
  -- Solve for `det D`, which is positive.
  have hs' := normSq_det_pos (hσ.isUnit hZ.2)
  have ha' := normSq_det_pos hA'
  rw [mul_pow] at key
  have hD' : LinearMap.det (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) =
      (normSq A.det ^ Fintype.card n)⁻¹ *
        (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (skewCoord Z : Matrix n n ℂ))).det ^
          Fintype.card n)⁻¹ := by
    field_simp at key ⊢
    linear_combination key
  rw [hD', abs_of_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg (normSq_nonneg _) _))
    (inv_nonneg.2 (pow_nonneg (normSq_nonneg _) _)))]

end Jacobian

/-! ### The polar map is a parametrisation -/

section Parametrisation

/-- The Gram matrix `Yᴴ A Y`, as a Hermitian matrix when `A` is Hermitian. -/
private def gramHerm (A Y : Matrix n n ℂ) : selfAdjoint.submodule ℝ (Matrix n n ℂ) :=
  (2⁻¹ : ℝ) • hermCoord (star Y * A * Y)

omit [DecidableEq n] in
private theorem coe_gramHerm (hA : A.IsHermitian) (Y : Matrix n n ℂ) :
    (gramHerm A Y : Matrix n n ℂ) = star Y * A * Y := by
  have h : star (star Y * A * Y) = star Y * A * Y := (isHermitian_conjTranspose_mul_mul Y hA).eq
  rw [gramHerm, Submodule.coe_smul, coe_hermCoord, h]
  module

omit [DecidableEq n] in
private theorem continuous_gramHerm : Continuous (gramHerm (n := n) A) := by
  have h : Continuous fun Y : Matrix n n ℂ ↦ star Y * A * Y := by fun_prop
  exact (continuous_const (y := (2⁻¹ : ℝ))).smul
    ((LinearMap.continuous_of_finiteDimensional hermCoord).comp h)

omit [DecidableEq n] in
/-- The Gram matrix is invariant under the unitary group. -/
private theorem gramHerm_mul (hA : A.IsHermitian) {g : Matrix n n ℂ} (hg : star g * A * g = A)
    (Y : Matrix n n ℂ) : gramHerm A (g * Y) = gramHerm A Y := by
  apply Subtype.ext
  rw [coe_gramHerm hA, coe_gramHerm hA, star_mul]
  calc star Y * star g * A * (g * Y) = star Y * (star g * A * g) * Y := by
        simp only [Matrix.mul_assoc]
    _ = star Y * A * Y := by rw [hg]

/-- On the domain of the polar map, the Gram matrix of `Ψ(S + T / 2)` is `T`. -/
private theorem gramHerm_polarMap (hA : A.IsHermitian) (hσ : IsGramSection A V σ)
    {Z : Matrix n n ℂ} (hZ : Z ∈ polarDomain A V) :
    gramHerm A (polarMap A σ Z) = hermCoord Z := by
  rw [polarMap, gramHerm_mul hA (star_cayleyChart_mul_mul_cayleyChart hA
    (mem_cayleyChartSource.1 hZ.1))]
  apply Subtype.ext
  rw [coe_gramHerm hA, ← hσ.conjTranspose_mul_mul hZ.2, star_eq_conjTranspose]

/-- The polar map is injective on its domain. -/
private theorem injOn_polarMap (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) : InjOn (polarMap A σ) (polarDomain A V) := by
  intro Z hZ Z' hZ' h
  have hT : hermCoord Z = hermCoord Z' := by
    rw [← gramHerm_polarMap hA hσ hZ, ← gramHerm_polarMap hA hσ hZ', h]
  have hc : cayleyChart A (skewCoord Z) = cayleyChart A (skewCoord Z') := by
    refine (hσ.isUnit hZ.2).mul_right_cancel ?_
    rw [← polarMap, h, polarMap, hT]
  have hS := injOn_cayleyChart hA' hZ.1 hZ'.1 hc
  rw [← coe_skewCoord_add_smul_hermCoord Z, ← coe_skewCoord_add_smul_hermCoord Z', hS, hT]

/-- Every `Y` with `T = Yᴴ A Y ∈ V` is `γ σ(T)` for some `γ` in the unitary group of `A`. -/
private theorem exists_mul_eq (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) {Y : Matrix n n ℂ} (hY : gramHerm A Y ∈ V) :
    ∃ γ : unitaryGroupOf A, ((γ : GL n ℂ) : Matrix n n ℂ) * σ (gramHerm A Y) = Y := by
  set s := σ (gramHerm A Y)
  have hsd : IsUnit s.det := (isUnit_iff_isUnit_det _).1 (hσ.isUnit hY)
  have hT : star Y * A * Y = star s * A * s :=
    (coe_gramHerm hA Y).symm.trans (hσ.conjTranspose_mul_mul hY).symm
  have hγ : star (Y * s⁻¹) * A * (Y * s⁻¹) = A :=
    calc star (Y * s⁻¹) * A * (Y * s⁻¹) = star s⁻¹ * (star Y * A * Y) * s⁻¹ := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = star (s * s⁻¹) * A * (s * s⁻¹) := by
          rw [hT]
          simp only [star_mul, Matrix.mul_assoc]
      _ = A := by rw [mul_nonsing_inv _ hsd, star_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨ofMatrix hA' (Y * s⁻¹) hγ, ?_⟩
  simp [Matrix.mul_assoc, nonsing_inv_mul _ hsd]

/-- Every `Y = γ σ(T)` with `T = Yᴴ A Y ∈ V` and `Y + σ(T)` invertible, that is, with `1 + γ`
invertible, is in the image of the polar map. -/
private theorem mem_image_polarMap (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) {Y : Matrix n n ℂ} (hY : gramHerm A Y ∈ V)
    (hYu : IsUnit (Y + σ (gramHerm A Y))) : Y ∈ polarMap A σ '' polarDomain A V := by
  obtain ⟨g, hgY⟩ := exists_mul_eq hA hA' hσ hY
  set T := gramHerm A Y
  have hg : IsUnit (1 + ((g : GL n ℂ) : Matrix n n ℂ)) := by
    refine isUnit_of_mul_isUnit_left (y := σ T) ?_
    rwa [Matrix.add_mul, Matrix.one_mul, hgY, add_comm]
  refine ⟨(cayleyChartInv A ((g : GL n ℂ) : Matrix n n ℂ) : Matrix n n ℂ) +
    (2⁻¹ : ℝ) • (T : Matrix n n ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [skewCoord_add_smul]
    exact cayleyChartInv_mem_cayleyChartSource hA g hg
  · rwa [hermCoord_add_smul]
  · rw [polarMap, skewCoord_add_smul, hermCoord_add_smul, cayleyChart_cayleyChartInv hA hA' g hg,
      hgY]

end Parametrisation


end IsGramSection

/-! ### Measures -/

section Measure

open unitaryGroupOf TauCeti

variable {m : Type*} [Fintype m] [DecidableEq m]

variable {A : Matrix m m ℂ} [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)]

namespace IsGramSection

variable {V : Set (selfAdjoint.submodule ℝ (Matrix m m ℂ))}
  {σ : selfAdjoint.submodule ℝ (Matrix m m ℂ) → Matrix m m ℂ}

/-- For Lebesgue-almost every `Y` with `T = Yᴴ A Y ∈ V`, written `Y = γ σ(T)` with `γ ∈ U(A)`,
the matrix `Y + σ(T) = (γ + 1) σ(T)` is invertible. For each `Y` this holds for `g Y` with almost
every `g ∈ U(A)`; by Fubini's theorem it holds for almost every `g Y` for some `g`, and `g`
preserves Lebesgue measure. -/
private theorem ae_isUnit_add (hA : A.IsHermitian) (hA' : IsUnit A) (hσ : IsGramSection A V σ)
    (μ : Measure (skewAdjoint.submodule ℝ (Matrix m m ℂ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ Y : Matrix m m ℂ, gramHerm A Y ∈ V → IsUnit (Y + σ (gramHerm A Y)) := by
  have := isHaarMeasure_cayleyMeasure μ hA hA'
  have := isMulRightInvariant_cayleyMeasure μ hA hA'
  have : SFinite (cayleyMeasure A μ) := by
    rw [cayleyMeasure_def]
    infer_instance
  let B : Set (Matrix m m ℂ) := {Y | gramHerm A Y ∈ V → IsUnit (Y + σ (gramHerm A Y))}
  have hgram : Measurable (gramHerm (n := m) A) := continuous_gramHerm.measurable
  have hB : MeasurableSet B := (hgram hσ.isOpen.measurableSet).imp
    ((measurable_id.add (hσ.measurable.comp hgram))
      IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.measurableSet)
  have horbit (Y : Matrix m m ℂ) :
      ∀ᵐ g : unitaryGroupOf A ∂cayleyMeasure A μ, ((g : GL m ℂ) : Matrix m m ℂ) * Y ∈ B := by
    by_cases hY : gramHerm A Y ∈ V
    · obtain ⟨γ, hγ⟩ := exists_mul_eq hA hA' hσ hY
      have htr : ∀ᵐ g : unitaryGroupOf A ∂cayleyMeasure A μ,
          IsUnit (1 + (((g * γ : unitaryGroupOf A) : GL m ℂ) : Matrix m m ℂ)) :=
        (measurePreserving_mul_right (cayleyMeasure A μ) γ).quasiMeasurePreserving.ae
          (ae_isUnit_one_add_cayleyMeasure μ hA)
      filter_upwards [htr] with g hg _
      rw [gramHerm_mul hA (mem_unitaryGroupOf_iff.1 g.property)]
      have h : ((g : GL m ℂ) : Matrix m m ℂ) * Y + σ (gramHerm A Y) =
          (1 + (((g * γ : unitaryGroupOf A) : GL m ℂ) : Matrix m m ℂ)) * σ (gramHerm A Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hγ,
          add_comm]
      rw [h]
      exact hg.mul (hσ.isUnit hY)
    · refine ae_of_all _ fun g hg ↦ ?_
      rw [gramHerm_mul hA (mem_unitaryGroupOf_iff.1 g.property)] at hg
      exact absurd hg hY
  have hcomm : ∀ᵐ g : unitaryGroupOf A ∂cayleyMeasure A μ, ∀ᵐ Y : Matrix m m ℂ,
      ((g : GL m ℂ) : Matrix m m ℂ) * Y ∈ B :=
    (Measure.ae_ae_comm (p := fun (g : unitaryGroupOf A) (Y : Matrix m m ℂ) ↦
      ((g : GL m ℂ) : Matrix m m ℂ) * Y ∈ B)
      (((continuous_val.comp continuous_fst).mul continuous_snd).measurable hB)).2
        (ae_of_all _ horbit)
  obtain ⟨g, hg⟩ := hcomm.exists
  have hmp := measurePreserving_mul_left_volume (κ := m) hA' g
  rw [← hmp.map_eq]
  exact (ae_map_iff hmp.measurable.aemeasurable hB).2 hg

end IsGramSection

end Measure

/-! ### The polar formula -/

section Polar

open unitaryGroupOf TauCeti

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
  {V : Set (selfAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℂ))}
  {σ : selfAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℂ) → Matrix (Fin r) (Fin r) ℂ}
  [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)]

namespace IsGramSection

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
/-- The set of `Y` with `Yᴴ A Y ∈ V` is the preimage of `V` under the Gram map. -/
private theorem preimage_eq_gramHerm (hA : A.IsHermitian) :
    (fun Y : Matrix (Fin r) (Fin r) ℂ ↦ Yᴴ * A * Y) ⁻¹' ((↑) '' V) = gramHerm A ⁻¹' V := by
  ext Y
  refine ⟨fun ⟨T, hT, hTY⟩ ↦ ?_, fun h ↦ ⟨_, h, coe_gramHerm hA Y⟩⟩
  have : gramHerm A Y = T := Subtype.ext ((coe_gramHerm hA Y).trans hTY.symm)
  rwa [Set.mem_preimage, this]

/-- Up to a null set, the `Y` with `Yᴴ A Y ∈ V` are the values of the polar map. -/
private theorem gramHerm_preimage_ae_eq_image (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) :
    gramHerm A ⁻¹' V =ᵐ[volume] polarMap A σ '' polarDomain A V := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_isUnit_add hA hA' hσ (skewHermitianLebesgue r)] with Y hY
  refine ⟨fun h ↦ mem_image_polarMap hA hA' hσ h (hY h), ?_⟩
  rintro ⟨Z, hZ, rfl⟩
  rw [Set.mem_preimage, gramHerm_polarMap hA hσ hZ]
  exact hZ.2

/-- The integrand `ρ(S) K(φ(S) σ(T))` of the polar formula at `Z = S + T / 2`, with `ρ` the Cayley
density and `φ` the group-valued Cayley chart. -/
private def polarIntegrand (A : Matrix (Fin r) (Fin r) ℂ)
    (σ : selfAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞) (Z : Matrix (Fin r) (Fin r) ℂ) : ℝ≥0∞ :=
  cayleyDensity A (skewCoord Z) *
    K (((cayleyChartUnitary A (skewCoord Z) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      σ (hermCoord Z))

private theorem measurable_polarIntegrand (hA : A.IsHermitian) (hσ : IsGramSection A V σ)
    {K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} (hK : Measurable K) :
    Measurable (polarIntegrand A σ K) := by
  have hskew : Measurable (skewCoord (n := Fin r)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hherm : Measurable (hermCoord (n := Fin r)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  exact (measurable_cayleyDensity.comp hskew).mul (hK.comp
    ((continuous_val.measurable.comp ((measurable_cayleyChartUnitary hA).comp hskew)).mul
      (hσ.measurable.comp hherm)))

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
/-- On the domain of the polar map, the Jacobian times `K ∘ Ψ` is `|det A| ^ (-2 r)` times the
integrand of the polar formula. -/
private theorem ofReal_abs_det_mul_eq (hA : A.IsHermitian) (hA' : IsUnit A)
    (hσ : IsGramSection A V σ) {K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ polarDomain A V) {D : Matrix (Fin r) (Fin r) ℂ →L[ℝ] Matrix (Fin r) (Fin r) ℂ}
    (hD : ∀ W, D W = cayleyChart A (skewCoord Z) * fderiv ℝ σ (hermCoord Z) (hermCoord W) +
        fderiv ℝ (cayleyChart A) (skewCoord Z) (skewCoord W) * σ (hermCoord Z)) :
    ENNReal.ofReal |D.det| * K (polarMap A σ Z) =
      ENNReal.ofReal (normSq A.det ^ r)⁻¹ * polarIntegrand A σ K Z := by
  have h := abs_det_polarMap hA hA' hσ hZ hD
  rw [Fintype.card_fin] at h
  rw [ContinuousLinearMap.det, h, ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg
    (normSq_nonneg _) _)), mul_assoc, polarMap]
  simp only [polarIntegrand, cayleyDensity_def, Fintype.card_fin, coe_cayleyChartUnitary hA hZ.1]

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
/-- The integrand of the polar formula in skew-Hermitian and Hermitian coordinates. -/
private theorem indicator_polarIntegrand_add (K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞)
    (T : selfAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℂ))
    (S : skewAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℂ)) :
    (polarDomain A V).indicator (polarIntegrand A σ K)
        ((S : Matrix (Fin r) (Fin r) ℂ) + (2⁻¹ : ℝ) • (T : Matrix (Fin r) (Fin r) ℂ)) =
      V.indicator (fun T ↦ cayleyDensity A S *
        K (((cayleyChartUnitary A S : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * σ T)) T := by
  by_cases hT : T ∈ V
  · rw [Set.indicator_of_mem hT]
    by_cases hS : S ∈ cayleyChartSource A
    · rw [Set.indicator_of_mem (show _ ∈ polarDomain A V from
        ⟨by rwa [skewCoord_add_smul], by rwa [hermCoord_add_smul]⟩)]
      simp only [polarIntegrand, skewCoord_add_smul, hermCoord_add_smul]
    · rw [Set.indicator_of_notMem fun h ↦ hS (by simpa [skewCoord_add_smul] using h.1),
        cayleyDensity_of_notMem hS, zero_mul]
  · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem fun h ↦ hT (by
      simpa [hermCoord_add_smul] using h.2)]

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
private theorem ofReal_inv_mul_inv_two_pow (hA' : IsUnit A) :
    ENNReal.ofReal (normSq A.det ^ r)⁻¹ * (2 ^ r)⁻¹ = (2 ^ r * ‖A.det‖ₑ ^ (2 * r))⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (normSq_det_pos hA') _), normSq_eq_norm_sq, ← pow_mul,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_comm]

/-- **The polar formula for the Gram map on bases.** Let `A` be an invertible Hermitian matrix of
size `r` and `σ` a section of the Gram map `Y ↦ Yᴴ A Y` over the open set `V` of Hermitian
matrices (`Matrix.IsGramSection`). For every measurable `K ≥ 0` on square matrices,

`∫_{Yᴴ A Y ∈ V} K(Y) dY = (2 ^ r |det A| ^ (2 r))⁻¹ ∫_V ∫_{U(A)} K(γ σ(T)) dμ^c(γ) dT`,

where `dY` is Lebesgue measure, `dT` is `TauCeti.hermitianLebesgue r` and `μ^c` is the Cayley
measure of `U(A)` built from `TauCeti.skewHermitianLebesgue r`. -/
theorem lintegral_eq (hA : A.IsHermitian) (hA' : IsUnit A) (hσ : IsGramSection A V σ)
    {K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Y in (fun Y ↦ Yᴴ * A * Y) ⁻¹' ((↑) '' V), K Y =
      (2 ^ r * ‖A.det‖ₑ ^ (2 * r))⁻¹ *
        ∫⁻ T in V, ∫⁻ γ, K (((γ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * σ T)
          ∂cayleyMeasure A (skewHermitianLebesgue r) ∂hermitianLebesgue r := by
  choose! D hD hDapp using fun Z (hZ : Z ∈ polarDomain A V) ↦ exists_hasFDerivAt_polarMap hσ hZ
  have hdom : MeasurableSet (polarDomain A V) := (isOpen_polarDomain hσ.isOpen).measurableSet
  -- Change variables along the polar map, then split `Z = S + T / 2`.
  rw [preimage_eq_gramHerm hA, setLIntegral_congr (gramHerm_preimage_ae_eq_image hA hA' hσ),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul_matrix hdom
      (fun Z hZ ↦ (hD Z hZ).hasFDerivWithinAt) (injOn_polarMap hA hA' hσ),
    setLIntegral_congr_fun hdom fun Z hZ ↦ ofReal_abs_det_mul_eq hA hA' hσ hZ (hDapp Z hZ),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hdom,
    lintegral_eq_inv_two_pow_mul_lintegral_lintegral_add
      ((measurable_polarIntegrand hA hσ hK).indicator hdom), ← mul_assoc,
    ofReal_inv_mul_inv_two_pow hA']
  simp only [indicator_polarIntegrand_add]
  congr 1
  rw [← lintegral_indicator hσ.isOpen.measurableSet]
  refine lintegral_congr fun T ↦ ?_
  by_cases hT : T ∈ V
  · simp only [Set.indicator_of_mem hT]
    exact (lintegral_cayleyMeasure _ hA (F := fun γ ↦
      K (((γ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * σ T))
      (hK.comp (continuous_val.measurable.mul measurable_const))).symm
  · simp only [Set.indicator_of_notMem hT, lintegral_zero]

/-- **The polar formula for a Hermitian involution** `J` (`J * J = 1`):
`∫_{Yᴴ J Y ∈ V} K(Y) dY = 2 ^ (-r) ∫_V ∫_{U(J)} K(γ σ(T)) dμ^c(γ) dT`. For the compact-dual
normalisation `μ^c / vol U(r)` of the Cayley measure the constant is `vol U(r) / 2 ^ r`, the same
for every signature. -/
theorem lintegral_eq_of_mul_self_eq_one (hA : A.IsHermitian) (hAA : A * A = 1)
    (hσ : IsGramSection A V σ) {K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Y in (fun Y ↦ Yᴴ * A * Y) ⁻¹' ((↑) '' V), K Y =
      (2 ^ r)⁻¹ * ∫⁻ T in V, ∫⁻ γ, K (((γ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * σ T)
          ∂cayleyMeasure A (skewHermitianLebesgue r) ∂hermitianLebesgue r := by
  have hAd : ‖A.det‖ = 1 := by
    have h : ‖A.det‖ ^ 2 = 1 := by rw [sq, ← norm_mul, ← det_mul, hAA, det_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  rw [hσ.lintegral_eq hA ⟨⟨A, A, hAA, hAA⟩, rfl⟩ hK, ← ofReal_norm, hAd]
  simp

end IsGramSection

end Polar

end Matrix


