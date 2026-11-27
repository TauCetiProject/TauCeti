/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Local sections of the Gram map

Let `A` be an invertible Hermitian complex matrix of size `n`, for instance a Hermitian involution
`J = diag(1, …, 1, -1, …, -1)`. The **Gram map** of `A` sends a square matrix `Y`, read as the
tuple of its columns, to the Hermitian matrix `Yᴴ * A * Y` of the values of the form of `A` on
those columns. It is constant on the orbits of the unitary group `Matrix.unitaryGroupOf A`
acting on the left, and its value at `Y = 1` is `A`.

A **section of the Gram map over an open set `V` of Hermitian matrices**
(`Matrix.IsGramSection A V σ`) is a measurable map `σ` from the Hermitian matrices to the square
matrices which on `V` is differentiable, takes invertible values, and satisfies
`(σ T)ᴴ * A * σ T = T`. Such a section, together with the action of `U(A)`, parametrises the
bases whose Gram matrix lies in `V`; this is how the polar formula for the Gram map is set up.

The main result, `Matrix.exists_isGramSection`, is that a section exists over a neighbourhood
of `A`, with value `1` at `A`. On the matrices `1 + A⁻¹ X / 2`, `X` Hermitian, the Gram map is
`X ↦ A + X + X A⁻¹ X / 4`, whose derivative at `X = 0` is the identity, so the inverse function
theorem inverts it near `A`; outside a small open set the section is extended by `1`, which keeps
it measurable.

Derivatives are taken for the Frobenius norm on matrices, as in
`TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.Cayley`; the norm is only a scoped instance.

## Main definitions

* `Matrix.IsGramSection A V σ`: `σ` is a measurable section of the Gram map of `A` over the open
  set `V`, differentiable with invertible values there.

## Main results

* `Matrix.exists_isGramSection`: for an invertible Hermitian `A`, there is a section of the Gram
  map of `A` over an open neighbourhood of `A`, with value `1` at `A`.
* `Matrix.IsGramSection.conjTranspose_mul_mul_fderiv_add`: the derivative of a section in a
  Hermitian direction `X` satisfies `(σ T)ᴴ A dσ(X) + dσ(X)ᴴ A σ T = X`.

## Provenance

`Matrix.IsGramSection` and `Matrix.exists_isGramSection` are adapted from `New.IsGramSection` and
`New.exists_isGramSection` in `src/Lib/DiscreteSeries/Haar/GramPolar.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There the
section is indexed by real coordinates of Hermitian matrices and `A` is a Hermitian involution;
here it is indexed by the Hermitian submodule and `A` is any invertible Hermitian matrix. The
underlying measure on tuples of vectors with prescribed Gram matrix goes back to C. L. Siegel,
*Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935).
-/

public section

noncomputable section

open Filter Topology
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

/-- `σ` is a **section of the Gram map** `Y ↦ Yᴴ * A * Y` over the set `V` of Hermitian
matrices: `V` is open, `σ` is measurable, and on `V` it is differentiable, takes invertible
values, and satisfies `(σ T)ᴴ * A * σ T = T`. Derivatives are for the Frobenius norm. -/
structure IsGramSection (A : Matrix n n ℂ) (V : Set (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
    (σ : selfAdjoint.submodule ℝ (Matrix n n ℂ) → Matrix n n ℂ) : Prop where
  /-- The set `V` is open. -/
  isOpen : IsOpen V
  /-- The section is measurable on all Hermitian matrices. -/
  measurable : Measurable σ
  /-- The section is differentiable on `V`. -/
  differentiableAt {T : selfAdjoint.submodule ℝ (Matrix n n ℂ)} : T ∈ V → DifferentiableAt ℝ σ T
  /-- On `V`, the Gram matrix of `σ T` is `T`. -/
  conjTranspose_mul_mul {T : selfAdjoint.submodule ℝ (Matrix n n ℂ)} :
    T ∈ V → (σ T)ᴴ * A * σ T = T
  /-- On `V`, the values of the section are invertible. -/
  isUnit {T : selfAdjoint.submodule ℝ (Matrix n n ℂ)} : T ∈ V → IsUnit (σ T)

namespace IsGramSection

variable {A : Matrix n n ℂ} {V S : Set (selfAdjoint.submodule ℝ (Matrix n n ℂ))}
  {σ : selfAdjoint.submodule ℝ (Matrix n n ℂ) → Matrix n n ℂ}

/-- A section of the Gram map over `V` restricts to a section over every open subset of `V`. -/
theorem mono (hσ : IsGramSection A V σ) (hS : IsOpen S) (hSV : S ⊆ V) : IsGramSection A S σ :=
  ⟨hS, hσ.measurable, fun hT ↦ hσ.differentiableAt (hSV hT),
    fun hT ↦ hσ.conjTranspose_mul_mul (hSV hT), fun hT ↦ hσ.isUnit (hSV hT)⟩

/-- The identity `(σ T)ᴴ * A * σ T = T` of a section, differentiated at `T ∈ V` in the
direction `X`: the Hermitian matrix `X` is `(σ T)ᴴ A dσ(X) + dσ(X)ᴴ A σ T`. -/
theorem conjTranspose_mul_mul_fderiv_add (hσ : IsGramSection A V σ)
    {T : selfAdjoint.submodule ℝ (Matrix n n ℂ)} (hT : T ∈ V)
    (X : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    (σ T)ᴴ * A * fderiv ℝ σ T X + (fderiv ℝ σ T X)ᴴ * A * σ T = X := by
  have hσT := (hσ.differentiableAt hT).hasFDerivAt
  have hd := (hσT.star.mul_const' A).mul' hσT
  have hid : HasFDerivAt (fun T' ↦ star (σ T') * A * σ T')
      (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL T :=
    (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.hasFDerivAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hσ.isOpen.mem_nhds hT) fun T' hT' ↦
        hσ.conjTranspose_mul_mul hT')
  have h := congrArg (· X) (hd.unique hid)
  exact h

end IsGramSection

section Existence

variable {A : Matrix n n ℂ}

/-- The Hermitian part `(Y + Yᴴ) / 2` of a square matrix, as a real linear map onto the Hermitian
matrices. -/
private def hermPart : Matrix n n ℂ →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ) where
  toFun Y := ⟨(2⁻¹ : ℝ) • (Y + star Y),
    (IsSelfAdjoint.all (2⁻¹ : ℝ)).smul (IsSelfAdjoint.add_star_self Y)⟩
  map_add' Y Z := by
    ext : 1
    simp only [star_add, Submodule.coe_add, ← smul_add]
    congr 1
    abel
  map_smul' c Y := by
    ext : 1
    simp [smul_add, smul_comm c]

omit [Fintype n] [DecidableEq n] in
private theorem coe_hermPart (Y : Matrix n n ℂ) :
    (hermPart Y : Matrix n n ℂ) = (2⁻¹ : ℝ) • (Y + star Y) := rfl

omit [Fintype n] [DecidableEq n] in
private theorem coe_hermPart_of_isSelfAdjoint {Y : Matrix n n ℂ} (hY : IsSelfAdjoint Y) :
    (hermPart Y : Matrix n n ℂ) = Y := by
  rw [coe_hermPart, hY.star_eq, ← two_smul ℝ Y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- The slice `X ↦ 1 + A⁻¹ X / 2` of square matrices through `1`, on which the Gram map has
derivative the identity at `X = 0`. -/
private def gramSlice (A : Matrix n n ℂ) (X : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    Matrix n n ℂ :=
  1 + (2 : ℂ)⁻¹ • (A⁻¹ * (X : Matrix n n ℂ))

/-- The derivative of the slice `gramSlice A`. -/
private def gramSliceDeriv (A : Matrix n n ℂ) :
    selfAdjoint.submodule ℝ (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  (((2 : ℂ)⁻¹ • A⁻¹ : Matrix n n ℂ) • (ContinuousLinearMap.id ℝ (Matrix n n ℂ))).comp
    (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL

private theorem hasFDerivAt_gramSlice (X : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    HasFDerivAt (gramSlice A) (gramSliceDeriv A) X := by
  refine ((gramSliceDeriv A).hasFDerivAt.const_add 1).congr_of_eventuallyEq ?_
  refine Eventually.of_forall fun Y ↦ ?_
  simp [gramSlice, gramSliceDeriv]

private theorem contDiff_gramSlice : ContDiff ℝ 1 (gramSlice A) := by
  have h : gramSlice A = fun X ↦ 1 + gramSliceDeriv A X := by
    ext1 X
    simp [gramSlice, gramSliceDeriv]
  rw [h]
  exact contDiff_const.add (gramSliceDeriv A).contDiff

/-- The Gram map of `A` on the slice `gramSlice A`, projected to the Hermitian matrices. -/
private def gramOnSlice (A : Matrix n n ℂ) (X : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    selfAdjoint.submodule ℝ (Matrix n n ℂ) :=
  hermPart (star (gramSlice A X) * A * gramSlice A X)

private theorem coe_gramOnSlice (hA : A.IsHermitian) (X : selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
    (gramOnSlice A X : Matrix n n ℂ) = (gramSlice A X)ᴴ * A * gramSlice A X := by
  refine coe_hermPart_of_isSelfAdjoint ?_
  rw [IsSelfAdjoint, star_mul, star_mul, star_star, ← Matrix.mul_assoc]
  exact congrArg (· * _) (congrArg (_ * ·) hA.eq)

private theorem contDiff_gramOnSlice : ContDiff ℝ 1 (gramOnSlice A) := by
  have h_star : ContDiff ℝ 1 fun X ↦ star (gramSlice A X) :=
    ((starL' ℝ : Matrix n n ℂ ≃L[ℝ] Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ).contDiff.comp
      contDiff_gramSlice
  exact (LinearMap.toContinuousLinearMap hermPart).contDiff.comp
    ((h_star.mul contDiff_const).mul contDiff_gramSlice)

/-- At `X = 0` the Gram map on the slice has derivative the identity. -/
private theorem hasFDerivAt_gramOnSlice_zero (hA : A.IsHermitian) (hA' : IsUnit A) :
    HasFDerivAt (gramOnSlice A)
      ((ContinuousLinearEquiv.refl ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)) :
        selfAdjoint.submodule ℝ (Matrix n n ℂ) →L[ℝ] selfAdjoint.submodule ℝ (Matrix n n ℂ)))
      0 := by
  have hd := (((hasFDerivAt_gramSlice (A := A) 0).star.mul_const' A).mul'
    (hasFDerivAt_gramSlice (A := A) 0))
  refine ((LinearMap.toContinuousLinearMap hermPart).hasFDerivAt.comp 0 hd).congr_fderiv ?_
  ext1 X
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA'
  have hinv : star A⁻¹ = A⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv, hA.eq]
  have hX : star (X : Matrix n n ℂ) = X := X.property
  have h1 : gramSlice A 0 = 1 := by simp [gramSlice]
  have hD : gramSliceDeriv A X = (2 : ℂ)⁻¹ • (A⁻¹ * (X : Matrix n n ℂ)) := by
    simp [gramSliceDeriv]
  have hsum : star (gramSlice A 0) * A * gramSliceDeriv A X +
      star (gramSliceDeriv A X) * A * gramSlice A 0 = (X : Matrix n n ℂ) := by
    rw [h1, hD, star_one, one_mul, mul_one, star_smul, star_mul, hX, hinv, Matrix.mul_smul,
      Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdet, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul A hdet, Matrix.one_mul, Matrix.mul_one, star_inv₀, star_ofNat,
      ← add_smul]
    norm_num
  apply Subtype.ext
  change (hermPart (star (gramSlice A 0) * A * gramSliceDeriv A X +
    star (gramSliceDeriv A X) * A * gramSlice A 0) : Matrix n n ℂ) = X
  rw [hsum, coe_hermPart_of_isSelfAdjoint X.property]

/-- **Local sections of the Gram map.** For an invertible Hermitian matrix `A`, there are an open
set `V` of Hermitian matrices containing `A` and a section `σ` of the Gram map `Y ↦ Yᴴ * A * Y`
over `V` with `σ A = 1`. -/
theorem exists_isGramSection (hA : A.IsHermitian) (hA' : IsUnit A) :
    ∃ (V : Set (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
      (σ : selfAdjoint.submodule ℝ (Matrix n n ℂ) → Matrix n n ℂ),
      IsGramSection A V σ ∧ ⟨A, hA.isSelfAdjoint⟩ ∈ V ∧ σ ⟨A, hA.isSelfAdjoint⟩ = 1 := by
  have hG := (contDiff_gramOnSlice (A := A)).contDiffAt (x := 0)
  have hG' := hasFDerivAt_gramOnSlice_zero hA hA'
  have hG0 : gramOnSlice A 0 = ⟨A, hA.isSelfAdjoint⟩ :=
    Subtype.ext (by rw [coe_gramOnSlice hA]; simp [gramSlice])
  set ψ := hG.localInverse hG' one_ne_zero
  have hψ : ContDiffAt ℝ 1 ψ (gramOnSlice A 0) := hG.to_localInverse hG' one_ne_zero
  set σ := fun T ↦ gramSlice A (ψ T)
  have hσ_base : σ (gramOnSlice A 0) = 1 := by
    simp [σ, ψ, hG.localInverse_apply_image hG' one_ne_zero, gramSlice]
  have hσ_cont : ContinuousAt σ (gramOnSlice A 0) :=
    (contDiff_gramSlice (A := A)).continuous.continuousAt.comp hψ.continuousAt
  have h_near : ∀ᶠ T in 𝓝 (gramOnSlice A 0),
      DifferentiableAt ℝ σ T ∧ (σ T)ᴴ * A * σ T = T ∧ IsUnit (σ T) := by
    filter_upwards [hψ.eventually (by simp),
      (hG.hasStrictFDerivAt hG' one_ne_zero).eventually_right_inverse,
      hσ_cont.eventually (Units.isOpen.mem_nhds (by rw [hσ_base]; exact isUnit_one))]
      with T h_diff h_inv h_unit
    refine ⟨((contDiff_gramSlice (A := A)).differentiable one_ne_zero _).comp T
      (h_diff.differentiableAt one_ne_zero), ?_, h_unit⟩
    rw [← coe_gramOnSlice hA]
    exact congrArg Subtype.val h_inv
  rw [hG0] at h_near hσ_base
  obtain ⟨V, hV, hV_open, h_base⟩ := eventually_nhds_iff.1 h_near
  -- Outside `V` the section is `1`, which makes it measurable.
  classical
  choose h_diff h_gram h_unit using hV
  have h_eq : Set.EqOn (V.piecewise σ 1) σ V := V.piecewise_eqOn σ 1
  refine ⟨V, V.piecewise σ 1,
    { isOpen := hV_open
      measurable := ContinuousOn.measurable_piecewise
        (fun T hT ↦ (h_diff T hT).continuousAt.continuousWithinAt) continuousOn_const
        hV_open.measurableSet
      differentiableAt := fun hT ↦
        (h_diff _ hT).congr_of_eventuallyEq (h_eq.eventuallyEq_of_mem (hV_open.mem_nhds hT))
      conjTranspose_mul_mul := fun hT ↦ by rw [h_eq hT, h_gram _ hT]
      isUnit := fun hT ↦ by simpa only [h_eq hT] using h_unit _ hT },
    h_base, (h_eq h_base).trans hσ_base⟩

end Existence

end Matrix
