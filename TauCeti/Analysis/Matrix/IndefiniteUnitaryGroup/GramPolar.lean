/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.GramSection
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Haar
import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.HaarTransport
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.SkewHermitian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.LinearAlgebra.Complex.Module
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

This is §1.3 (b) of the ShortGRH background roadmap HolomorphicDiscreteSeriesOfUnitaryGroups,
adapted from `New.IsGramSection.lintegral_eq`, `New.IsGramSection.lintegral_eq_cayleyChart_mul`,
`New.IsGramSection.exists_hasFDerivAt_cayleyChart_mul`, `New.IsGramSection.ae_isUnit_add` and
`New.IsGramSection.preimage_gramCoords_ae_eq_image` in
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

/-- The Hermitian coordinate `Z + Zᴴ` of a square matrix `Z = S + T / 2`. -/
private def hermCoord : Matrix n n ℂ →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ) where
  toFun Z := ⟨Z + star Z, by
    change _ ∈ selfAdjoint (Matrix n n ℂ)
    rw [selfAdjoint.mem_iff, star_add, star_star, add_comm]⟩
  map_add' Z W := Subtype.ext (by simp only [star_add, Submodule.coe_add]; abel)
  map_smul' c Z := Subtype.ext (by simp [smul_add])

/-- The skew-Hermitian coordinate `(Z - Zᴴ) / 2` of a square matrix `Z = S + T / 2`. -/
private def skewCoord : Matrix n n ℂ →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix n n ℂ) where
  toFun Z := ⟨(2⁻¹ : ℝ) • (Z - star Z), by
    change _ ∈ skewAdjoint (Matrix n n ℂ)
    rw [skewAdjoint.mem_iff, star_smul, star_trivial (2⁻¹ : ℝ), star_sub, star_star, ← smul_neg,
      neg_sub]⟩
  map_add' Z W := Subtype.ext (by simp only [star_add, Submodule.coe_add, ← smul_add]; abel_nf)
  map_smul' c Z := Subtype.ext (by simp [smul_sub, smul_comm c (2⁻¹ : ℝ)])

private theorem coe_hermCoord (Z : Matrix n n ℂ) :
    (hermCoord Z : Matrix n n ℂ) = Z + star Z := (rfl)

private theorem coe_skewCoord (Z : Matrix n n ℂ) :
    (skewCoord Z : Matrix n n ℂ) = (2⁻¹ : ℝ) • (Z - star Z) := (rfl)

private theorem coe_skewCoord_of_star_eq_neg {Z : Matrix n n ℂ} (hZ : star Z = -Z) :
    (skewCoord Z : Matrix n n ℂ) = Z := by
  rw [coe_skewCoord, hZ]
  module

private theorem skewCoord_add_smul (S : skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (T : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    skewCoord ((S : Matrix n n ℂ) + (2⁻¹ : ℝ) • (T : Matrix n n ℂ)) = S := by
  have hS : star (S : Matrix n n ℂ) = -S := skewAdjoint.mem_iff.1 S.property
  have hT : star (T : Matrix n n ℂ) = T := T.property
  apply Subtype.ext
  rw [coe_skewCoord, star_add, star_smul, star_trivial (2⁻¹ : ℝ), hS, hT]
  module

private theorem hermCoord_add_smul (S : skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (T : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    hermCoord ((S : Matrix n n ℂ) + (2⁻¹ : ℝ) • (T : Matrix n n ℂ)) = T := by
  have hS : star (S : Matrix n n ℂ) = -S := skewAdjoint.mem_iff.1 S.property
  have hT : star (T : Matrix n n ℂ) = T := T.property
  apply Subtype.ext
  rw [coe_hermCoord, star_add, star_smul, star_trivial (2⁻¹ : ℝ), hS, hT]
  module

private theorem coe_skewCoord_add_smul_hermCoord (Z : Matrix n n ℂ) :
    (skewCoord Z : Matrix n n ℂ) + (2⁻¹ : ℝ) • (hermCoord Z : Matrix n n ℂ) = Z := by
  rw [coe_skewCoord, coe_hermCoord]
  module

/-- A skew-Hermitian matrix is its own skew-Hermitian coordinate. -/
private theorem skewCoord_coe (X : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    skewCoord (X : Matrix n n ℂ) = X := by
  simpa using skewCoord_add_smul X 0

/-- Square matrices in Hermitian and skew-Hermitian coordinates, `Z ↦ (Z + Zᴴ, (Z - Zᴴ) / 2)`. -/
private def polarCoordEquiv :
    Matrix n n ℂ ≃ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ) ×
      skewAdjoint.submodule ℝ (Matrix n n ℂ) where
  toFun Z := (hermCoord Z, skewCoord Z)
  invFun x := (x.2 : Matrix n n ℂ) + (2⁻¹ : ℝ) • (x.1 : Matrix n n ℂ)
  map_add' Z W := by simp
  map_smul' c Z := by simp
  left_inv Z := coe_skewCoord_add_smul_hermCoord Z
  right_inv x := Prod.ext (hermCoord_add_smul x.2 x.1) (skewCoord_add_smul x.2 x.1)

private theorem polarCoordEquiv_symm_apply
    (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
    polarCoordEquiv.symm x = (x.2 : Matrix n n ℂ) + (2⁻¹ : ℝ) • (x.1 : Matrix n n ℂ) := (rfl)

end Coordinates

variable {n : Type*} [Fintype n] [DecidableEq n]

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

/-- An element of the unitary group of an invertible matrix has `|det g| ^ 2 = 1`. -/
private theorem normSq_det_eq_one (hA' : IsUnit A) {g : Matrix n n ℂ}
    (hg : star g * A * g = A) : normSq g.det = 1 := by
  have hAd : A.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hA').ne_zero
  have h := congrArg det hg
  rw [det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, Complex.star_def] at h
  have h' : ((normSq g.det : ℂ) - 1) * A.det = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    linear_combination h
  exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hAd)

/-- The real determinant of left multiplication by `P` on square complex matrices of size `n` is
`|det P| ^ (2 n)`. -/
private theorem det_mulLeft_real (P : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulLeft ℝ P : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) =
      normSq P.det ^ Fintype.card n := by
  have h : (LinearMap.mulLeft ℝ P : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) =
      (LinearMap.mulLeft ℂ P ∘ₗ LinearMap.mulRight ℂ 1).restrictScalars ℝ :=
    LinearMap.ext fun Z ↦ by simp
  rw [h, LinearMap.det_restrictScalars, det_mulLeft_comp_mulRight, det_one, one_pow, mul_one,
    Algebra.norm_complex_apply, map_pow]

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
  have hS := mem_cayleyChartSource.1 hZ.1
  set c := cayleyChart A (skewCoord Z)
  set s := σ (hermCoord Z)
  have hc : star c * A * c = A := star_cayleyChart_mul_mul_cayleyChart hA hS
  have hs : s.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (hσ.isUnit hZ.2)).ne_zero
  have hAd : A.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hA').ne_zero
  set P := star (c * s) * A
  let ω := LinearMap.codRestrict (skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (LinearMap.mulLeft ℝ (star c * A) ∘ₗ (fderiv ℝ (cayleyChart A) (skewCoord Z) :
      skewAdjoint.submodule ℝ (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ))
    (star_cayleyChart_mul_mul_fderiv_cayleyChart_mem hA hA' hS)
  have hω (X : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      (ω X : Matrix n n ℂ) = star c * A * fderiv ℝ (cayleyChart A) (skewCoord Z) X := (rfl)
  -- `Yᴴ A dΨ (S' + T' / 2) = sᴴ A dσ(T') + sᴴ ω(S') s`.
  have hPD (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      P * D (polarCoordEquiv.symm x) = star s * A * fderiv ℝ σ (hermCoord Z) x.1 +
        star s * (ω x.2 : Matrix n n ℂ) * s := by
    have h1 : hermCoord (polarCoordEquiv.symm x) = x.1 := hermCoord_add_smul x.2 x.1
    have h2 : skewCoord (polarCoordEquiv.symm x) = x.2 := skewCoord_add_smul x.2 x.1
    have hc' (X : Matrix n n ℂ) : star c * (A * (c * X)) = A * X := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc]
    rw [hD, h1, h2, hω]
    simp only [P, star_mul, Matrix.mul_add, Matrix.mul_assoc, hc']
  let g := polarCoordEquiv.toLinearMap ∘ₗ
    (LinearMap.mulLeft ℝ P ∘ₗ (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)) ∘ₗ
      polarCoordEquiv.symm.toLinearMap
  have hωskew (X : skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      star (star s * (ω X : Matrix n n ℂ) * s) = -(star s * (ω X : Matrix n n ℂ) * s) := by
    have h : star (ω X : Matrix n n ℂ) = -ω X := skewAdjoint.mem_iff.1 (ω X).property
    simp only [star_mul, h, star_star, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hg1 (x : selfAdjoint.submodule ℝ (Matrix n n ℂ) × skewAdjoint.submodule ℝ (Matrix n n ℂ)) :
      (g x).1 = x.1 := by
    apply Subtype.ext
    change hermCoord (P * D (polarCoordEquiv.symm x)) = (x.1 : Matrix n n ℂ)
    rw [coe_hermCoord, hPD, star_add, hωskew]
    have h := hσ.conjTranspose_mul_mul_fderiv_add hZ.2 x.1
    rw [← star_eq_conjTranspose, ← star_eq_conjTranspose] at h
    have hA'' : star A = A := hA.eq
    rw [← h, star_mul, star_mul, hA'', star_star, ← Matrix.mul_assoc]
    abel
  have hg2 : LinearMap.snd ℝ _ _ ∘ₗ g ∘ₗ LinearMap.inr ℝ _ _ =
      skewAdjointConjugate ℝ (star s) ∘ₗ ω := by
    refine LinearMap.ext fun X ↦ Subtype.ext ?_
    change (skewCoord (P * D (polarCoordEquiv.symm (0, X))) : Matrix n n ℂ) =
      skewAdjointConjugate ℝ (star s) (ω X)
    rw [hPD, coe_skewAdjointConjugate_apply, map_zero, Matrix.mul_zero, zero_add,
      coe_skewCoord_of_star_eq_neg (hωskew X), star_eq_conjTranspose s,
      conjTranspose_conjTranspose]
  have hdetω : LinearMap.det ω =
      (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (skewCoord Z : Matrix n n ℂ))).det ^ Fintype.card n)⁻¹ :=
    det_codRestrict_mulLeft_comp_fderiv_cayleyChart hA hA' hS
  have hdetC : LinearMap.det (skewAdjointConjugate ℝ (star s)) = normSq s.det ^ Fintype.card n := by
    rw [det_skewAdjointConjugate Complex.mem_range_algebraMap_of_isSelfAdjoint
      Complex.val_mk0_I_mem_skewAdjoint, Algebra.norm_complex_apply, star_eq_conjTranspose,
      det_conjTranspose, Complex.star_def, normSq_conj]
  have hdetP : normSq P.det = normSq s.det * normSq A.det := by
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose, det_mul, map_mul,
      Complex.star_def, normSq_conj, map_mul,
      normSq_det_eq_one hA' (star_cayleyChart_mul_mul_cayleyChart hA hS), one_mul]
  have key : (normSq s.det * normSq A.det) ^ Fintype.card n *
      LinearMap.det (D : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) =
      normSq s.det ^ Fintype.card n *
        (normSq (1 - (2 : ℂ)⁻¹ • (A⁻¹ * (skewCoord Z : Matrix n n ℂ))).det ^
          Fintype.card n)⁻¹ := by
    rw [← hdetP, ← det_mulLeft_real, ← LinearMap.det_comp, ← hdetC, ← hdetω,
      ← LinearMap.det_comp, ← hg2, ← LinearMap.det_eq_det_snd_comp_comp_inr hg1,
      LinearMap.det_conj]
  have hs' : 0 < normSq s.det := normSq_pos.2 hs
  have ha' : 0 < normSq A.det := normSq_pos.2 hAd
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
  have hA' : star A = A := hA.eq
  have h : star (star Y * A * Y) = star Y * A * Y := by
    rw [star_mul, star_mul, star_star, hA', Matrix.mul_assoc]
  change (2⁻¹ : ℝ) • (star Y * A * Y + star (star Y * A * Y)) = _
  rw [h]
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
  rw [coe_gramHerm hA, ← hσ.conjTranspose_mul_mul hZ.2]
  rfl

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
  have hγu : IsUnit (Y * s⁻¹) := (isUnit_iff_isUnit_det _).2 <| isUnit_iff_ne_zero.2 fun h ↦ by
    simpa [h] using normSq_det_eq_one hA' hγ
  refine ⟨⟨hγu.unit, mem_unitaryGroupOf_iff.2 (by simpa using hγ)⟩, ?_⟩
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

omit [DecidableEq m] in
/-- Lebesgue measure on complex matrices is an additive Haar measure. -/
private theorem isAddHaarMeasure_volume :
    (volume : Measure (Matrix m m ℂ)).IsAddHaarMeasure := by
  let e : (m → m → ℂ) ≃L[ℝ] Matrix m m ℂ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have h : (volume : Measure (Matrix m m ℂ)) = (volume : Measure (m → m → ℂ)).map e := rfl
  rw [h]
  exact e.isAddHaarMeasure_map _

open scoped Matrix.Norms.Frobenius in
omit [DecidableEq m] in
/-- The change of variables formula on complex matrices, for Lebesgue measure and derivatives for
the Frobenius norm. -/
private theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul_matrix
    {s : Set (Matrix m m ℂ)} {f : Matrix m m ℂ → Matrix m m ℂ}
    {f' : Matrix m m ℂ → Matrix m m ℂ →L[ℝ] Matrix m m ℂ} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : Matrix m m ℂ → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) := by
  have : @BorelSpace (Matrix m m ℂ)
      NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _ := by
    exact (inferInstance : BorelSpace (Matrix m m ℂ))
  have : @Measure.IsAddHaarMeasure (Matrix m m ℂ) _
      NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _ volume := by
    exact isAddHaarMeasure_volume
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hf g

open scoped Matrix.Norms.Frobenius in
omit [Fintype m] [DecidableEq m] in
/-- An additive Haar measure on the skew-Hermitian matrices is sigma-finite. -/
private theorem sigmaFinite_skewAdjoint [Finite m]
    (μ : Measure (skewAdjoint.submodule ℝ (Matrix m m ℂ))) [μ.IsAddHaarMeasure] :
    SigmaFinite μ := by
  have := Fintype.ofFinite m
  have := Matrix.borelSpace_skewAdjoint_frobenius (n := m)
  have := μ.isAddHaarMeasure_skewAdjoint_frobenius
  have := FiniteDimensional.proper_real (skewAdjoint.submodule ℝ (Matrix m m ℂ))
  exact @SigmaFinite.of_isFiniteMeasureOnCompacts _ _
    NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace inferInstance μ
    inferInstance

variable {A : Matrix m m ℂ} [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)]

omit [MeasurableSpace (unitaryGroupOf A)] [BorelSpace (unitaryGroupOf A)] in
/-- Left multiplication by an element of the unitary group of an invertible `A` preserves Lebesgue
measure on square matrices. -/
private theorem measurePreserving_mul_left (hA' : IsUnit A) (g : unitaryGroupOf A) :
    MeasurePreserving (fun Y : Matrix m m ℂ ↦ ((g : GL m ℂ) : Matrix m m ℂ) * Y) := by
  have hmeas : Measurable fun Y : Matrix m m ℂ ↦ ((g : GL m ℂ) : Matrix m m ℂ) * Y :=
    (continuous_const.mul continuous_id).measurable
  have hg : ‖((g : GL m ℂ) : Matrix m m ℂ).det‖ₑ = 1 := by
    have h := IsGramSection.normSq_det_eq_one hA' (mem_unitaryGroupOf_iff.1 g.property)
    rw [normSq_eq_norm_sq, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h
    rw [← ofReal_norm, h, ENNReal.ofReal_one]
  refine ⟨hmeas, Measure.ext_of_lintegral _ fun K hK ↦ ?_⟩
  rw [lintegral_map hK hmeas]
  have h := lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul
    ((isUnit_iff_isUnit_det _).1 (g : GL m ℂ).isUnit).ne_zero (det_one (n := m) (R := ℂ) ▸
      one_ne_zero) K
  simpa [hg] using h.symm

/-- Almost every element `h` of the unitary group, for the Cayley measure, has `1 + h`
invertible: the Cayley measure lives on the image of the chart. -/
private theorem ae_isUnit_one_add (hA : A.IsHermitian)
    (μ : Measure (skewAdjoint.submodule ℝ (Matrix m m ℂ))) :
    ∀ᵐ h : unitaryGroupOf A ∂cayleyMeasure A μ, IsUnit (1 + ((h : GL m ℂ) : Matrix m m ℂ)) := by
  have hopen : IsOpen {h : unitaryGroupOf A | IsUnit (1 + ((h : GL m ℂ) : Matrix m m ℂ))} :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage
      (continuous_const.add (Units.continuous_val.comp continuous_subtypeVal))
  rw [cayleyMeasure_def, ae_map_iff (measurable_cayleyChartUnitary hA).aemeasurable
    hopen.measurableSet]
  refine ae_of_all _ fun S ↦ ?_
  by_cases hS : S ∈ cayleyChartSource A
  · rw [coe_cayleyChartUnitary hA hS]
    exact isUnit_one_add_cayleyChart A S
  · rw [cayleyChartUnitary_of_notMem hS, OneMemClass.coe_one, Units.val_one]
    simpa using isUnit_one_add_cayleyChart A 0

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
    have : SigmaFinite μ := sigmaFinite_skewAdjoint μ
    rw [cayleyMeasure_def]
    infer_instance
  let B : Set (Matrix m m ℂ) := {Y | gramHerm A Y ∈ V → IsUnit (Y + σ (gramHerm A Y))}
  have hgram : Measurable (gramHerm (n := m) A) := continuous_gramHerm.measurable
  have hB : MeasurableSet B := (hgram hσ.isOpen.measurableSet).imp
    ((measurable_id.add (hσ.measurable.comp hgram))
      IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.measurableSet)
  have hcoe : Continuous fun g : unitaryGroupOf A ↦ ((g : GL m ℂ) : Matrix m m ℂ) :=
    Units.continuous_val.comp continuous_subtypeVal
  have horbit (Y : Matrix m m ℂ) :
      ∀ᵐ g : unitaryGroupOf A ∂cayleyMeasure A μ, ((g : GL m ℂ) : Matrix m m ℂ) * Y ∈ B := by
    by_cases hY : gramHerm A Y ∈ V
    · obtain ⟨γ, hγ⟩ := exists_mul_eq hA hA' hσ hY
      have htr : ∀ᵐ g : unitaryGroupOf A ∂cayleyMeasure A μ,
          IsUnit (1 + (((g * γ : unitaryGroupOf A) : GL m ℂ) : Matrix m m ℂ)) :=
        (measurePreserving_mul_right (cayleyMeasure A μ) γ).quasiMeasurePreserving.ae
          (ae_isUnit_one_add hA μ)
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
      (((hcoe.comp continuous_fst).mul continuous_snd).measurable hB)).2 (ae_of_all _ horbit)
  obtain ⟨g, hg⟩ := hcomm.exists
  have hmp := measurePreserving_mul_left hA' g
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

private theorem measurable_coe_unitaryGroupOf :
    Measurable fun g : unitaryGroupOf A ↦ ((g : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
  (Units.continuous_val.comp continuous_subtypeVal).measurable

private theorem measurable_polarIntegrand (hA : A.IsHermitian) (hσ : IsGramSection A V σ)
    {K : Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} (hK : Measurable K) :
    Measurable (polarIntegrand A σ K) := by
  have hskew : Measurable (skewCoord (n := Fin r)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hherm : Measurable (hermCoord (n := Fin r)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  exact (measurable_cayleyDensity.comp hskew).mul (hK.comp
    ((measurable_coe_unitaryGroupOf.comp ((measurable_cayleyChartUnitary hA).comp hskew)).mul
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
  have hAd : A.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hA').ne_zero
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (normSq_pos.2 hAd) _), normSq_eq_norm_sq, ← pow_mul,
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
      (hK.comp (measurable_coe_unitaryGroupOf.mul measurable_const))).symm
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
  rw [hσ.lintegral_eq hA ⟨⟨A, A, hAA, hAA⟩, rfl⟩ hK, ← ofReal_norm,
    norm_det_eq_one_of_mul_self_eq_one hAA]
  simp

end IsGramSection

end Polar

end Matrix


