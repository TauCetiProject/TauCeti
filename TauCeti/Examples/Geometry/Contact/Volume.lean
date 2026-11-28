/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ContactElements
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Contact.Standard.Volume
public import TauCeti.Geometry.Contact.Volume
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Examples: the contact volume criterion on `ℝ³`, `ℝ⁵` and the contact elements of the plane

On a manifold of dimension `2 n + 1` a one-form `α` is a contact form exactly when the top-degree
form `α ∧ (dα)ⁿ` vanishes nowhere
(`TauCeti.SmoothForm.isContactForm_iff_wedge_wedgePow_apply_ne_zero`). This file computes the
criterion on three coordinate examples, which pin down its sign and show that a weaker test
fails.

* **`ℝ³`.** For `α = dz - x dy` (`TauCeti.standardContactForm`) one has `dα = -dx ∧ dy` and

  `α ∧ dα = -dx ∧ dy ∧ dz`

  (`wedge_standardContactForm_wedgePow_mextDerivₗ`), which is nowhere zero: on the coordinate frame
  `(∂_x, ∂_y, ∂_z)` it takes the value `-1`
  (`wedge_standardContactForm_wedgePow_mextDerivₗ_apply_coordFrame`). The computation runs
  through the standard model `dz - p dq` on `ℝ × ℝ × ℝ` with coordinates `(q, p, z)`, whose
  volume form is `1! dz ∧ dq ∧ dp` (`TauCeti.wedge_innerProductContactForm_wedgePow_mextDerivₗ`
  for `n = 1`).
  The coordinate change `(q, p, z) = (y, x, z)` pulls `dz - p dq` back to `dz - x dy`
  (`TauCeti.mpullback_innerProductContactForm_real`), and it pulls `dz ∧ dq ∧ dp` back to
  `dz ∧ dy ∧ dx = -dx ∧ dy ∧ dz` (`mpullback_wedgeFamily_innerProductContactCoordForm`). So the
  general formula and this coordinate change agree on the sign of the volume form of `ℝ³`.
* **`ℝ⁵`.** On `ℝ⁵ = ℝ³ × ℝ²`, with coordinates `(x, y, z, u, v)`, the same expression
  `α = dz - x dy` (`fstPullbackStandardContactForm`), pulled back along the projection to `ℝ³`,
  vanishes nowhere (`fstPullbackStandardContactForm_apply_ne_zero`), and so does `dα = -dx ∧ dy`
  (`mextDeriv_fstPullbackStandardContactForm_ne_zero`); `dα` is even nonzero on the kernel of `α`
  at every point (`exists_mextDeriv_fstPullbackStandardContactForm_apply_ne_zero`). But `∂_u` and
  `∂_v` lie in the kernel of `α` and in the kernel of `dα`
  (`fstPullbackStandardContactForm_apply_of_fst_eq_zero`,
  `mextDeriv_fstPullbackStandardContactForm_apply_of_fst_eq_zero`), so `α` is contact at no point
  (`not_isContactFormAt_fstPullbackStandardContactForm`), and `α ∧ (dα)² = 0`
  (`wedge_fstPullbackStandardContactForm_wedgePow_mextDerivₗ`). A criterion asking only that `α`
  and `dα|ker α` be nonzero would accept this form; the criterion needs the top power `(dα)ⁿ`. The
  general reason is `TauCeti.injective_mfderiv_of_isContactFormAt_mpullback`: a form pulled back
  along a map is contact only where the differential of the map is injective.
* **Contact elements.** On `ℝ² × ℝ`, with coordinates `((x, y), τ)`, the form
  `α = cos τ dx + sin τ dy` (`TauCeti.contactElementForm`), whose kernel descends to the
  non-coorientable contact structure of the space of contact elements `ℝ² × ℝP¹`, satisfies

  `α ∧ dα = -dx ∧ dy ∧ dτ`

  (`wedge_contactElementForm_wedgePow_mextDerivₗ`). Both sides are top-degree forms, so it
  suffices to compare them on the frame `(R, e, ∂_τ)` with `R = (cos τ, sin τ, 0)`, which spans
  the kernel of `dα`, and `e = (-sin τ, cos τ, 0)`: there `α ∧ dα` is
  `α(R) dα(e, ∂_τ) = -1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Example 2.1.3 (the standard contact form and the volume criterion).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.Examples.ContactVolume

/-! ### The standard contact form on `ℝ³` -/

/-- The coordinate covectors `dx`, `dy`, `dz` of `ℝ³ = ℝ × ℝ × ℝ`. -/
private def coordCovector : Fin 3 → (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]

/-- The coordinate one-forms `dx`, `dy`, `dz` of `ℝ³ = ℝ × ℝ × ℝ`, indexed by `0`, `1`, `2`. -/
def coordForm (i : Fin 3) : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1 :=
  SmoothForm.const (ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ × ℝ) ℝ 0 (coordCovector i))

/-- The coordinate one-forms `dx`, `dy`, `dz` read the three coordinates of a tangent vector. -/
@[simp]
theorem coordForm_apply (i : Fin 3) (p : ℝ × ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    (coordForm i).val p ![v] = ![v.1, v.2.1, v.2.2] i := by
  rw [coordForm, SmoothForm.const_apply]
  -- On the model space `NormedSpace.fromTangentSpace` is the identity, and the covectors are the
  -- coordinate projections.
  fin_cases i <;> rfl

/-- The coordinate change `(q, p, z) = (y, x, z)` from `ℝ³` with coordinates `(x, y, z)` to the
standard model `ℝ × ℝ × ℝ` with coordinates `(q, p, z)`, as a continuous linear map. -/
private def swapCoord : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

private theorem swapCoord_apply (p : ℝ × ℝ × ℝ) : swapCoord p = (p.2.1, p.1, p.2.2) :=
  (rfl)

private theorem contMDiff_swapCoord : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ swapCoord :=
  swapCoord.contDiff.contMDiff

/-- The orthonormal basis `1` of `ℝ`, with which `dz - p dq` on `ℝ × ℝ × ℝ` has the coordinate
one-forms `dz, dq, dp`. -/
private def realBasis : OrthonormalBasis (Fin 1) ℝ ℝ :=
  OrthonormalBasis.singleton (Fin 1) ℝ

private theorem realBasis_apply (i : Fin 1) : realBasis i = 1 :=
  OrthonormalBasis.singleton_apply i

/-- The coordinate change `(q, p, z) = (y, x, z)` pulls the coordinate one-forms `dz, dq, dp` of
the standard model back to `dz, dy, dx`. -/
private theorem mpullback_innerProductContactCoordForm_real (r : Fin (1 + 2 * 1)) :
    SmoothForm.mpullback swapCoord contMDiff_swapCoord
        (innerProductContactCoordForm realBasis r) = (coordForm ∘ Equiv.swap 0 2) r := by
  refine Subtype.ext (funext fun p ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  -- A one-form only sees the single entry `v 0` of `v`.
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv, SmoothForm.mpullback_apply_one, swapCoord.mfderiv_eq, Function.comp_apply,
    coordForm_apply]
  -- The three coordinate one-forms of the model are `dz`, `dq` and `dp`, at the indices `0`, `1`
  -- and `2`.
  fin_cases r
  · exact innerProductContactCoordForm_castAdd_apply realBasis _ _
  · exact (innerProductContactCoordForm_natAdd_zero_apply realBasis 0 _ _).trans
      (by
        rw [realBasis_apply, Real.inner_apply, one_mul]
        exact congrArg (·.1) (swapCoord_apply (v 0)))
  · exact (innerProductContactCoordForm_natAdd_one_apply realBasis 0 _ _).trans
      (by
        rw [realBasis_apply, Real.inner_apply, one_mul]
        exact congrArg (·.2.1) (swapCoord_apply (v 0)))

/-- The coordinate change `(q, p, z) = (y, x, z)` pulls `dz ∧ dq ∧ dp` back to `-dx ∧ dy ∧ dz`. -/
private theorem mpullback_swapCoord_wedgeFamily :
    SmoothForm.mpullback swapCoord contMDiff_swapCoord
        (SmoothForm.wedgeFamily (innerProductContactCoordForm realBasis)) =
      -SmoothForm.wedgeFamily coordForm := by
  -- The pulled-back family `coordForm ∘ swap 0 2` is `dz, dy, dx`.
  rw [SmoothForm.mpullback_wedgeFamily, funext mpullback_innerProductContactCoordForm_real,
    SmoothForm.wedgeFamily_comp_perm, Equiv.Perm.sign_swap (by decide)]
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  exact neg_one_smul ℝ (SmoothForm.wedgeFamily coordForm)

/-- **The coordinate change of the standard model reverses the volume form.** The coordinate
change `(q, p, z) = (y, x, z)` pulls the volume form `dz ∧ dq ∧ dp` of the standard model
`ℝ × ℝ × ℝ`, for the orthonormal basis `1` of `ℝ`, back to `dz ∧ dy ∧ dx = -dx ∧ dy ∧ dz`. -/
theorem mpullback_wedgeFamily_innerProductContactCoordForm
    (hσ : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (fun p : ℝ × ℝ × ℝ ↦ (p.2.1, p.1, p.2.2))) :
    SmoothForm.mpullback (fun p : ℝ × ℝ × ℝ ↦ (p.2.1, p.1, p.2.2)) hσ
        (SmoothForm.wedgeFamily
          (innerProductContactCoordForm (OrthonormalBasis.singleton (Fin 1) ℝ))) =
      -SmoothForm.wedgeFamily coordForm := by
  rw [SmoothForm.mpullback_congr hσ contMDiff_swapCoord (funext fun p ↦ (swapCoord_apply p).symm)]
  exact mpullback_swapCoord_wedgeFamily

/-- **The volume form of `dz - x dy`.** On `ℝ³` with coordinates `(x, y, z)`, the standard contact
form `α = dz - x dy` satisfies `α ∧ dα = -dx ∧ dy ∧ dz`. -/
theorem wedge_standardContactForm_wedgePow_mextDerivₗ :
    SmoothForm.wedge standardContactForm
        ((mextDerivₗ 𝓘(ℝ, ℝ × ℝ × ℝ) 1 standardContactForm).wedgePow 1) =
      -SmoothForm.wedgeFamily coordForm := by
  have hα : SmoothForm.mpullback swapCoord contMDiff_swapCoord (innerProductContactForm ℝ) =
      standardContactForm := Subtype.ext (by
        rw [SmoothForm.coe_mpullback]
        exact mpullback_innerProductContactForm_real)
  rw [← hα, SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mpullback_wedgePow,
    ← SmoothForm.mpullback_wedge, wedge_innerProductContactForm_wedgePow_mextDerivₗ realBasis,
    map_smul, mpullback_swapCoord_wedgeFamily]
  simp

/-- On the coordinate frame `(∂_x, ∂_y, ∂_z)`, the volume form of `dz - x dy` takes the value
`-1`. In particular it vanishes nowhere. -/
theorem wedge_standardContactForm_wedgePow_mextDerivₗ_apply_coordFrame (p : ℝ × ℝ × ℝ) :
    (SmoothForm.wedge standardContactForm
        ((mextDerivₗ 𝓘(ℝ, ℝ × ℝ × ℝ) 1 standardContactForm).wedgePow 1)).val p
      ![((1, 0, 0) : ℝ × ℝ × ℝ), ((0, 1, 0) : ℝ × ℝ × ℝ), ((0, 0, 1) : ℝ × ℝ × ℝ)] = -1 := by
  rw [wedge_standardContactForm_wedgePow_mextDerivₗ, SmoothForm.neg_toRoughForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, SmoothForm.wedgeFamily_apply, Matrix.det_fin_three]
  simp

/-! ### A nowhere contact form on `ℝ⁵` -/

/-- The projection `ℝ⁵ = ℝ³ × ℝ² → ℝ³` is smooth. -/
private theorem contMDiff_fst_five :
    ContMDiff 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (Prod.fst : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ × ℝ) :=
  contDiff_fst.contMDiff

/-- The one-form `dz - x dy` on `ℝ⁵ = ℝ³ × ℝ²`, with coordinates `((x, y, z), (u, v))`: the pullback
of the standard contact form of `ℝ³` along the projection. -/
def fstPullbackStandardContactForm :
    SmoothForm 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ × ℝ) × (ℝ × ℝ)) ℝ 1 :=
  SmoothForm.mpullback Prod.fst contMDiff_fst_five standardContactForm

/-- The differential of the projection `ℝ⁵ = ℝ³ × ℝ² → ℝ³` is the projection. -/
private theorem mfderiv_fst_five (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p) :
    mfderiv 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ × ℝ) Prod.fst p v = v.1 := by
  rw [mfderiv_eq_fderiv, fderiv_fst]
  -- `ContinuousLinearMap.fst` applied to `v` is `v.1` by definition.
  rfl

/-- The form `fstPullbackStandardContactForm` evaluates a tangent vector `((a, b, c), w)` at
`((x, y, z), (u, v))` as
`c - x b`. -/
@[simp]
theorem fstPullbackStandardContactForm_apply (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p) :
    fstPullbackStandardContactForm.val p ![v] = v.1.2.2 - p.1.1 * v.1.2.1 := by
  rw [fstPullbackStandardContactForm, SmoothForm.mpullback_apply_one, mfderiv_fst_five]
  exact standardContactForm_apply p.1 v.1

/-- The exterior derivative of `fstPullbackStandardContactForm` is `-dx ∧ dy`. -/
theorem mextDeriv_fstPullbackStandardContactForm_apply (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    (v w : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p) :
    mextDeriv fstPullbackStandardContactForm.val p ![v, w] =
      w.1.1 * v.1.2.1 - v.1.1 * w.1.2.1 := by
  rw [fstPullbackStandardContactForm, SmoothForm.mextDeriv_mpullback_apply_two, mfderiv_fst_five,
    mfderiv_fst_five]
  exact mextDeriv_standardContactForm_apply p.1 v.1 w.1

/-- The form `dz - x dy` on `ℝ⁵` vanishes nowhere: it takes the value `1` on `∂_z`. -/
theorem fstPullbackStandardContactForm_apply_ne_zero (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) :
    fstPullbackStandardContactForm.val p ≠ 0 := by
  intro h
  have h₁ := fstPullbackStandardContactForm_apply p (((0, 0, 1), 0) : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
  rw [h] at h₁
  simp at h₁

/-- The exterior derivative `-dx ∧ dy` of `dz - x dy` on `ℝ⁵` vanishes nowhere: it takes the value
`-1` on `(∂_x, ∂_y)`. -/
theorem mextDeriv_fstPullbackStandardContactForm_ne_zero (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) :
    mextDeriv fstPullbackStandardContactForm.val p ≠ 0 := by
  intro h
  have h₁ := mextDeriv_fstPullbackStandardContactForm_apply p
    (((1, 0, 0), 0) : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    (((0, 1, 0), 0) : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
  rw [h] at h₁
  simp at h₁

/-- The exterior derivative of `dz - x dy` on `ℝ⁵` is nonzero even on the kernel of the form: the
kernel vectors `∂_x` and `∂_y + x ∂_z` pair to `-1`. -/
theorem exists_mextDeriv_fstPullbackStandardContactForm_apply_ne_zero (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) :
    ∃ v w : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p,
      fstPullbackStandardContactForm.val p ![v] = 0 ∧
        fstPullbackStandardContactForm.val p ![w] = 0 ∧
        mextDeriv fstPullbackStandardContactForm.val p ![v, w] ≠ 0 := by
  -- Name the tangent vectors, so that they keep their tangent-space type.
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p, v = ((1, 0, 0), 0) :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p, w = ((0, 1, p.1.1), 0) :=
    ⟨_, rfl⟩
  refine ⟨v, w, ?_, ?_, ?_⟩
  · rw [fstPullbackStandardContactForm_apply, hv]
    simp
  · rw [fstPullbackStandardContactForm_apply, hw]
    simp
  · rw [mextDeriv_fstPullbackStandardContactForm_apply, hv, hw]
    simp

/-- The tangent vectors of the `ℝ²` factor, spanned by `∂_u` and `∂_v`, lie in the kernel of
`dz - x dy` on `ℝ⁵`. -/
theorem fstPullbackStandardContactForm_apply_of_fst_eq_zero (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    {v : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p} (hv : v.1 = 0) :
    fstPullbackStandardContactForm.val p ![v] = 0 := by
  rw [fstPullbackStandardContactForm_apply, hv]
  simp

/-- The tangent vectors of the `ℝ²` factor, spanned by `∂_u` and `∂_v`, lie in the kernel of the
exterior derivative `-dx ∧ dy` of `dz - x dy` on `ℝ⁵`. -/
theorem mextDeriv_fstPullbackStandardContactForm_apply_of_fst_eq_zero (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ))
    {v : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p} (hv : v.1 = 0)
    (w : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p) :
    mextDeriv fstPullbackStandardContactForm.val p ![v, w] = 0 := by
  rw [mextDeriv_fstPullbackStandardContactForm_apply, hv]
  simp

/-- **The form `dz - x dy` on `ℝ⁵` is contact nowhere**, although it and its exterior derivative
vanish nowhere: the differential of the projection to `ℝ³` kills `∂_u`. -/
theorem not_isContactFormAt_fstPullbackStandardContactForm (p : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) :
    ¬IsContactFormAt fstPullbackStandardContactForm.val p := by
  intro h
  rw [fstPullbackStandardContactForm, SmoothForm.coe_mpullback] at h
  have hinj := injective_mfderiv_of_isContactFormAt_mpullback ((contMDiff_fst_five p).of_le
    (by simp)) ((standardContactForm.contMDiff p.1).of_le (by simp)) h
  -- The vector `∂_u`, named so that it keeps its tangent-space type, is killed by the
  -- differential of the projection.
  obtain ⟨e, he⟩ : ∃ e : TangentSpace 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) p, e = ((0, 0, 0), (1, 0)) :=
    ⟨_, rfl⟩
  -- The `ℝ³` component of `e` is the zero vector `(0, 0, 0)` by definition.
  have h₀ : e = 0 := hinj (by rw [map_zero, mfderiv_fst_five, he]; rfl)
  have h₁ := congrArg (fun x : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ x.2.1) h₀
  rw [he] at h₁
  exact one_ne_zero h₁

/-- **The volume form of `dz - x dy` on `ℝ⁵` vanishes identically**: `α ∧ (dα)² = 0`. -/
theorem wedge_fstPullbackStandardContactForm_wedgePow_mextDerivₗ :
    SmoothForm.wedge fstPullbackStandardContactForm
      ((mextDerivₗ 𝓘(ℝ, (ℝ × ℝ × ℝ) × (ℝ × ℝ)) 1 fstPullbackStandardContactForm).wedgePow 2) =
        0 := by
  have hrank : Module.finrank ℝ ((ℝ × ℝ × ℝ) × (ℝ × ℝ)) = 2 * 2 + 1 := by
    simp [Module.finrank_prod]
  refine Subtype.ext (funext fun p ↦ ?_)
  by_contra h
  exact not_isContactFormAt_fstPullbackStandardContactForm p
    ((SmoothForm.isContactFormAt_iff_wedge_wedgePow_apply_ne_zero hrank
      fstPullbackStandardContactForm p).2 h)

/-! ### The space of contact elements of the plane -/

open Real

/-- The coordinate covectors `dx`, `dy`, `dτ` of `ℝ² × ℝ = (ℝ × ℝ) × ℝ`. -/
private def elementCoordCovector : Fin 3 → ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
    ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ]

/-- The coordinate one-forms `dx`, `dy`, `dτ` of `ℝ² × ℝ = (ℝ × ℝ) × ℝ`, indexed by `0`, `1`,
`2`. -/
def elementCoordForm (i : Fin 3) : SmoothForm 𝓘(ℝ, (ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ) ℝ 1 :=
  SmoothForm.const
    (ContinuousAlternatingMap.ofSubsingleton ℝ ((ℝ × ℝ) × ℝ) ℝ 0 (elementCoordCovector i))

/-- The coordinate one-forms `dx`, `dy`, `dτ` read the three coordinates of a tangent vector. -/
@[simp]
theorem elementCoordForm_apply (i : Fin 3) (p : (ℝ × ℝ) × ℝ)
    (v : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :
    (elementCoordForm i).val p ![v] = ![v.1.1, v.1.2, v.2] i := by
  rw [elementCoordForm, SmoothForm.const_apply]
  -- On the model space `NormedSpace.fromTangentSpace` is the identity, and the covectors are the
  -- coordinate projections.
  fin_cases i <;> rfl

/-- The vectors `R = (cos τ, sin τ, 0)`, `e = (-sin τ, cos τ, 0)` and `∂_τ` of `ℝ² × ℝ`. -/
private def elementVectors (τ : ℝ) : Fin 3 → (ℝ × ℝ) × ℝ :=
  ![((cos τ, sin τ), 0), ((-sin τ, cos τ), 0), ((0, 0), 1)]

/-- The vectors `(R, e, ∂_τ)` are linearly independent: rotating the plane back by `τ` sends them
to the standard basis. -/
private theorem linearIndependent_elementVectors (τ : ℝ) :
    LinearIndependent ℝ (elementVectors τ) := by
  let L : ((ℝ × ℝ) × ℝ) →L[ℝ] Fin 3 → ℝ := ContinuousLinearMap.pi
    ![cos τ • elementCoordCovector 0 + sin τ • elementCoordCovector 1,
      -sin τ • elementCoordCovector 0 + cos τ • elementCoordCovector 1,
      elementCoordCovector 2]
  refine LinearIndependent.of_comp L.toLinearMap ?_
  convert (Pi.basisFun ℝ (Fin 3)).linearIndependent
  ext i j
  have h₁ : cos τ * cos τ + sin τ * sin τ = 1 := by rw [← sq, ← sq, cos_sq_add_sin_sq]
  have h₂ : sin τ * sin τ + cos τ * cos τ = 1 := by rw [add_comm, h₁]
  fin_cases i <;> fin_cases j <;>
    simp [L, elementVectors, elementCoordCovector, h₁, h₂, mul_comm]

/-- The frame `(R, e, ∂_τ)` of the tangent space at `((x, y), τ)`: the unit normal
`R = (cos τ, sin τ, 0)` of the contact element, which spans the kernel of `dα`, the unit vector
`e = (-sin τ, cos τ, 0)` along the contact element, and `∂_τ`. -/
private def elementFrame (p : (ℝ × ℝ) × ℝ) : Fin 3 → TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p :=
  elementVectors p.2

/-- The volume form of `cos τ dx + sin τ dy` takes the value `-1` on the frame `(R, e, ∂_τ)`:
`R` lies in the kernel of `dα`, so the value is `α(R) dα(e, ∂_τ) = 1 · (-1)`. -/
private theorem wedge_contactElementForm_apply_elementFrame (p : (ℝ × ℝ) × ℝ) :
    (SmoothForm.wedge contactElementForm
        ((mextDerivₗ 𝓘(ℝ, (ℝ × ℝ) × ℝ) 1 contactElementForm).wedgePow 1)).val p
      (elementFrame p) = -1 := by
  have hF : elementFrame p = Matrix.vecCons (elementFrame p 0)
      ![elementFrame p 1, elementFrame p 2] ∘ Fin.cast (Nat.add_comm 1 (2 * 1)) :=
    funext fun i ↦ by fin_cases i <;> rfl
  have he : (![elementFrame p 1, elementFrame p 2] ∘ Fin.cast (Nat.mul_one 2).symm) =
      ![elementFrame p 1, elementFrame p 2] :=
    funext fun i ↦ by fin_cases i <;> rfl
  simp only [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    SmoothForm.wedgePow_apply, mextDerivₗ_apply]
  rw [hF, ContinuousAlternatingMap.pairedWedge_wedgePow_apply_vecCons_of_forall _ _ 1
      (fun w ↦ by
        rw [mextDeriv_contactElementForm_apply]
        simp [elementFrame, elementVectors]
        ring),
    ContinuousAlternatingMap.wedgePow_one_apply, he, mextDeriv_contactElementForm_apply,
    contactElementForm_apply]
  simp [elementFrame, elementVectors]
  -- The remaining goal is `-X² = -1` with `X = cos² τ + sin² τ`, written as
  -- `X (-cos² τ - sin² τ) = -1`. Since `-X² + 1 = -(X + 1) (X - 1)`, it is `-(X + 1)` times the
  -- identity `X = 1`.
  linear_combination (-(cos p.2 ^ 2 + sin p.2 ^ 2 + 1)) * cos_sq_add_sin_sq p.2

/-- The form `-dx ∧ dy ∧ dτ` takes the value `-1` on the frame `(R, e, ∂_τ)`. -/
private theorem neg_wedgeFamily_elementCoordForm_apply_elementFrame (p : (ℝ × ℝ) × ℝ) :
    (-SmoothForm.wedgeFamily elementCoordForm).val p (elementFrame p) = -1 := by
  rw [SmoothForm.neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    SmoothForm.wedgeFamily_apply, Matrix.det_fin_three]
  simp only [Matrix.of_apply, elementCoordForm_apply]
  simp [elementFrame, elementVectors]
  linear_combination -cos_sq_add_sin_sq p.2

/-- **The volume form of the contact elements of the plane.** On `ℝ² × ℝ` with coordinates
`((x, y), τ)`, the contact form `α = cos τ dx + sin τ dy` satisfies `α ∧ dα = -dx ∧ dy ∧ dτ`. -/
theorem wedge_contactElementForm_wedgePow_mextDerivₗ :
    SmoothForm.wedge contactElementForm
        ((mextDerivₗ 𝓘(ℝ, (ℝ × ℝ) × ℝ) 1 contactElementForm).wedgePow 1) =
      -SmoothForm.wedgeFamily elementCoordForm := by
  refine Subtype.ext (funext fun p ↦ ?_)
  -- Both sides are top-degree forms, determined by their values on the frame `(R, e, ∂_τ)`.
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, (ℝ × ℝ) × ℝ) p) :=
    inferInstanceAs (FiniteDimensional ℝ ((ℝ × ℝ) × ℝ))
  have hrank : Fintype.card (Fin 3) = Module.finrank ℝ ((ℝ × ℝ) × ℝ) := by
    simp [Module.finrank_prod]
  have hF : LinearIndependent ℝ (elementFrame p) := linearIndependent_elementVectors p.2
  set B := basisOfLinearIndependentOfCardEqFinrank' _ hF hrank
  have hB : ⇑B = elementFrame p := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ContinuousAlternatingMap.ext fun v ↦
    (ContinuousAlternatingMap.apply_eq_det_mul _ B v).trans
      ((congrArg _ ?_).trans (ContinuousAlternatingMap.apply_eq_det_mul _ B v).symm)
  rw [hB, wedge_contactElementForm_apply_elementFrame,
    neg_wedgeFamily_elementCoordForm_apply_elementFrame]

/-- On the frame `(∂_x, ∂_y, ∂_τ)`, the volume form of `cos τ dx + sin τ dy` takes the value `-1`.
In particular it vanishes nowhere. -/
theorem wedge_contactElementForm_wedgePow_mextDerivₗ_apply_coordFrame (p : (ℝ × ℝ) × ℝ) :
    (SmoothForm.wedge contactElementForm
        ((mextDerivₗ 𝓘(ℝ, (ℝ × ℝ) × ℝ) 1 contactElementForm).wedgePow 1)).val p
      ![(((1, 0), 0) : (ℝ × ℝ) × ℝ), (((0, 1), 0) : (ℝ × ℝ) × ℝ), (((0, 0), 1) : (ℝ × ℝ) × ℝ)] =
      -1 := by
  rw [wedge_contactElementForm_wedgePow_mextDerivₗ, SmoothForm.neg_toRoughForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, SmoothForm.wedgeFamily_apply, Matrix.det_fin_three]
  simp

end TauCeti.Examples.ContactVolume
