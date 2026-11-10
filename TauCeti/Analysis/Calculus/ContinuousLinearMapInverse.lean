/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Inverting and differentiating continuous linear maps

This file collects facts about inverting and differentiating continuous linear maps, and about ring
inverses in a general normed algebra. The first is a perturbation criterion: a map differing from a
continuous linear equivalence `L` by less than `‖L⁻¹‖⁻¹` in operator norm is again invertible, by a
Neumann series. The second packages the derivative of a differentiable inverse family of continuous
linear maps at an invertible base point, including its action on a varying vector; that is the
analytic input for differentiating a vector-field pullback along a parametric family. The third part
works in an arbitrary normed algebra: it shows that the ring inverse of a `C^n` family of units is
`C^n`, and computes the velocity `Z * C - C * Z` of a family that intertwines a curve through `1`
with the constant `C`; the latter involves no inversion.

## Main results

* `ContinuousLinearMap.isInvertible_of_norm_sub_lt` and
  `ContinuousLinearMap.isInvertible_of_norm_sub_le_half`: a continuous linear map closer to an
  invertible one than the reciprocal norm of its inverse — or than half of it — is itself
  invertible.
* `ContinuousLinearMap.isInvertible_of_mul_norm_sub_lt`: the perturbation criterion phrased through
  an a priori estimate `‖x‖ ≤ C * ‖L x‖`, `C * ‖M - L‖ < 1`, as used in the method of
  continuity.
* `HasDerivAt.clm_inverse`: differentiates `(A t)⁻¹`.
* `HasDerivAt.clm_inverse_apply`: differentiates `(A t)⁻¹ (w t)`.
* `DifferentiableAt.clm_inverse_of_completeSpace`: the inverse of a differentiable family between
  Banach spaces is differentiable at an invertible base point.
* `HasDerivAt.clm_inverse_of_completeSpace`: the Banach-space specialization for an inverse family.
* `HasDerivAt.clm_inverse_apply_of_completeSpace`: the Banach-space specialization acting on a
  vector curve.
* `TauCeti.fderiv_eq_neg_comp_of_comp_eq_id`: the derivative of a family `φ` of left inverses
  of `ψ`, over any normed space of variables, is `-(φ ∘ ψ' ∘ φ)`.
* `ContDiffAt.inverse` and `ContDiff.inverse`: the ring inverse of a `C^n` family of units
  is `C^n`.
* `DifferentiableAt.deriv_eq_mul_sub_mul_of_mul_eq_mul`: a family `K` with `K t * P t = P t * C`
  and `P` of velocity `Z` through `1` has velocity `Z * C - C * Z` at that point.

-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Perturbation

/-- A continuous linear map that differs from a continuous linear equivalence `L` by less than
`‖L⁻¹‖⁻¹` in operator norm is itself invertible: `L⁻¹A` is close enough to `1` to be a unit of the
Banach algebra of endomorphisms of `E`. -/
theorem ContinuousLinearMap.isInvertible_of_norm_sub_lt [CompleteSpace E]
    (L : E ≃L[𝕜] F) {A : E →L[𝕜] F}
    (h : ‖A - (L : E →L[𝕜] F)‖₊ < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) : A.IsInvertible := by
  have hsymm : ‖(L.symm : F →L[𝕜] E)‖₊ ≠ 0 := by
    rintro h0
    rw [h0, inv_zero] at h
    simp at h
  have hpos : 0 < ‖(L.symm : F →L[𝕜] E)‖ := by
    simpa using pos_iff_ne_zero.2 hsymm
  have hreal : ‖A - (L : E →L[𝕜] F)‖ < ‖(L.symm : F →L[𝕜] E)‖⁻¹ := by
    rw [← NNReal.coe_lt_coe] at h
    simpa using h
  have hnorm : ‖(L.symm : F →L[𝕜] E).comp A - 1‖ < 1 :=
    calc
      ‖(L.symm : F →L[𝕜] E).comp A - 1‖ =
          ‖(L.symm : F →L[𝕜] E).comp (A - (L : E →L[𝕜] F))‖ := by
        congr 1
        ext x
        simp
      _ ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖A - (L : E →L[𝕜] F)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ < ‖(L.symm : F →L[𝕜] E)‖ * ‖(L.symm : F →L[𝕜] E)‖⁻¹ :=
          mul_lt_mul_of_pos_left hreal hpos
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  let _ : Nontrivial E := not_subsingleton_iff_nontrivial.mp (by
    intro hE
    let _ := hE
    exact hpos.ne' (norm_of_subsingleton _))
  let u : (E →L[𝕜] E)ˣ := Units.ofNearby 1 ((L.symm : F →L[𝕜] E).comp A) (by simpa using hnorm)
  refine ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 E u).trans L, ?_⟩
  ext x
  simp [u, ContinuousLinearEquiv.unitsEquiv_apply]

/-- A continuous linear map within `‖L⁻¹‖⁻¹ / 2` of a continuous linear equivalence `L` is
invertible. This is the shape in which Mathlib's inverse function theorem supplies the estimate. -/
theorem ContinuousLinearMap.isInvertible_of_norm_sub_le_half [CompleteSpace E]
    (L : E ≃L[𝕜] F) {A : E →L[𝕜] F}
    (h : ‖A - (L : E →L[𝕜] F)‖₊ ≤ ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2) : A.IsInvertible := by
  rcases eq_or_ne (‖(L.symm : F →L[𝕜] E)‖₊)⁻¹ 0 with h0 | h0
  · rw [h0, zero_div, le_zero_iff, nnnorm_eq_zero, sub_eq_zero] at h
    exact h ▸ ContinuousLinearMap.isInvertible_equiv
  · exact ContinuousLinearMap.isInvertible_of_norm_sub_lt L (h.trans_lt (NNReal.half_lt_self h0))

/-- **Invertibility is stable under perturbations small against an a priori estimate.** Let `E`
be a Banach space and `L : E →L[𝕜] F` surjective with `‖x‖ ≤ C * ‖L x‖`. Then every
`M : E →L[𝕜] F` with `C * ‖M - L‖ < 1` is invertible. -/
theorem ContinuousLinearMap.isInvertible_of_mul_norm_sub_lt [CompleteSpace E]
    {L M : E →L[𝕜] F} {C : ℝ} (hL : Function.Surjective L) (hC : ∀ x, ‖x‖ ≤ C * ‖L x‖)
    (hM : C * ‖M - L‖ < 1) : M.IsInvertible := by
  obtain ⟨e, rfl⟩ := isInvertible_of_surjective_of_forall_norm_le hL hC
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space every continuous linear map agrees with `e`.
    have hMe : M = e := ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]
    exact hMe ▸ isInvertible_equiv
  -- On a nontrivial space the estimate forces `0 < C`, and `‖e⁻¹‖ ≤ C`.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hC0 : 0 < C := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le (hC x)) (norm_nonneg _)
  have hsymm : ‖(e.symm : F →L[𝕜] E)‖ ≤ C := opNorm_le_bound _ hC0.le fun y ↦ by
    simpa using norm_inverse_apply_le_of_forall_norm_le e.surjective hC y
  have hsymm0 : 0 < ‖(e.symm : F →L[𝕜] E)‖ :=
    norm_pos_iff.2 fun h ↦ hx (by simpa using congr($h (e x)))
  refine isInvertible_of_norm_sub_lt e ?_
  rw [← NNReal.coe_lt_coe]
  push_cast
  calc ‖M - e‖ < C⁻¹ := by simpa using (lt_inv_mul_iff₀ hC0).2 hM
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖⁻¹ := inv_anti₀ hsymm0 hsymm

end Perturbation

section InverseFamily

/-- The derivative of a family of inverses: if `φ y ∘ ψ y = id` for `y` near `z` and
`ψ z ∘ φ z = id`, then the derivative of `φ` at `z` in the direction `v` is
`-(φ z ∘ ψ' v ∘ φ z)`. The maps may be linear over a larger field `𝕜'` than the field `𝕜` of
differentiation, and the variable lives in any normed space. `HasDerivAt.clm_inverse` is the
one-variable case. -/
theorem TauCeti.fderiv_eq_neg_comp_of_comp_eq_id {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {E₁ E₂ X : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜' E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜' E₂] [NormedSpace 𝕜 E₁] [IsScalarTower 𝕜 𝕜' E₁]
    [NormedSpace 𝕜 E₂] [IsScalarTower 𝕜 𝕜' E₂] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {φ : X → E₂ →L[𝕜'] E₁} {ψ : X → E₁ →L[𝕜'] E₂} {z : X} (hφ : DifferentiableAt 𝕜 φ z)
    (hψ : DifferentiableAt 𝕜 ψ z) (hl : ∀ᶠ y in 𝓝 z, φ y ∘L ψ y = .id 𝕜' E₁)
    (hr : ψ z ∘L φ z = .id 𝕜' E₂) (v : X) :
    fderiv 𝕜 φ z v = -(φ z ∘L (fderiv 𝕜 ψ z v ∘L φ z)) := by
  -- The product rule for `φ ∘ ψ`, which is constant near `z`; composition of `𝕜'`-linear maps
  -- is a continuous `𝕜`-bilinear map.
  have h := congrArg (fun L => L v)
    (((compL 𝕜' E₁ E₂ E₁).bilinearRestrictScalars 𝕜).fderiv_of_bilinear hφ hψ)
  have hl' : (fun y => φ y ∘L ψ y) =ᶠ[𝓝 z] fun _ => ContinuousLinearMap.id 𝕜' E₁ := hl
  simp only [hl'.fderiv_eq, fderiv_const_apply, zero_apply, add_apply, precompR_apply,
    precompL_apply, comp_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    compL_apply] at h
  -- Compose `0 = φ ∘ ψ' v + φ' v ∘ ψ` on the right with `φ z`.
  have h' := congrArg (· ∘L φ z) h
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, hr, ContinuousLinearMap.comp_id] at h'
  exact eq_neg_of_add_eq_zero_right h'.symm

end InverseFamily

variable {t₀ : 𝕜} {A : 𝕜 → E →L[𝕜] F} {A' : E →L[𝕜] F} {w : 𝕜 → F} {w' : F}

/-- The derivative of an inverse family of continuous linear maps, assuming the family is
invertible at the base point and the inverse family is differentiable there. -/
theorem HasDerivAt.clm_inverse (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  have hl : ∀ᶠ t in 𝓝 t₀, (A t).inverse ∘L A t = .id 𝕜 E := by
    filter_upwards [hA0Inv.eventually_of_tendsto_inverse hInvDiff.continuousAt] with t ht
    exact ht.inverse_comp_self
  have h := TauCeti.fderiv_eq_neg_comp_of_comp_eq_id hInvDiff hA.differentiableAt hl
    hA0Inv.self_comp_inverse 1
  rw [fderiv_apply_one_eq_deriv, fderiv_apply_one_eq_deriv, hA.deriv] at h
  exact h ▸ hInvDiff.hasDerivAt

/-- The derivative of an inverse family of continuous linear maps acting on a differentiable
vector curve, assuming the family is invertible at the base point and the inverse family is
differentiable there. -/
theorem HasDerivAt.clm_inverse_apply (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀)
    (hw : HasDerivAt w w' t₀) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A t₀).inverse w' - (A t₀).inverse (A' ((A t₀).inverse (w t₀)))) t₀ := by
  simpa only [neg_apply, ContinuousLinearMap.comp_apply, sub_eq_neg_add] using
    (hA.clm_inverse hA0Inv hInvDiff).clm_apply hw

/-- In a Banach space, the inverse of a differentiable family is differentiable at an invertible
base point. -/
theorem DifferentiableAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : DifferentiableAt 𝕜 A t₀) (hA0Inv : (A t₀).IsInvertible) :
    DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀ :=
  (hA0Inv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero |>.comp t₀ hA

/-- The derivative of an inverse family of continuous linear maps between Banach spaces. -/
theorem HasDerivAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  apply hA.clm_inverse hA0Inv
  exact DifferentiableAt.clm_inverse_of_completeSpace hA.differentiableAt hA0Inv

/-- The derivative of an inverse family of continuous linear maps between Banach spaces, acting
on a differentiable vector curve. -/
theorem HasDerivAt.clm_inverse_apply_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) (hw : HasDerivAt w w' t₀) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A t₀).inverse w' - (A t₀).inverse (A' ((A t₀).inverse (w t₀)))) t₀ := by
  exact hA.clm_inverse_apply hA0Inv
    (DifferentiableAt.clm_inverse_of_completeSpace hA.differentiableAt hA0Inv) hw

section RingInverse

variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {n : WithTop ℕ∞}

/-- The ring inverse of a `C^n` family is `C^n` at a point where the family takes a unit value. -/
theorem ContDiffAt.inverse {f : X → R} {x : X} (hf : ContDiffAt 𝕜 n f x)
    (hfx : IsUnit (f x)) : ContDiffAt 𝕜 n (fun y => Ring.inverse (f y)) x := by
  obtain ⟨u, hu⟩ := hfx
  have hi := contDiffAt_ringInverse (n := n) 𝕜 u
  rw [hu] at hi
  exact hi.comp x hf

/-- The ring inverse of a `C^n` family of units is `C^n`. -/
theorem ContDiff.inverse {f : X → R} (hf : ContDiff 𝕜 n f) (hfu : ∀ x, IsUnit (f x)) :
    ContDiff 𝕜 n (fun y => Ring.inverse (f y)) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.inverse (hfu x)

omit [HasSummableGeomSeries R] in
/-- If `K t * P t = P t * C` for all `t`, `P t₀ = 1`, `P` has derivative `Z` at `t₀` and `K` is
differentiable at `t₀`, then `K` has derivative `Z * C - C * Z` at `t₀`. -/
theorem DifferentiableAt.deriv_eq_mul_sub_mul_of_mul_eq_mul {P K : 𝕜 → R} {Z C : R} {t₀ : 𝕜}
    (hK : DifferentiableAt 𝕜 K t₀) (hP : HasDerivAt P Z t₀) (hKP : ∀ t, K t * P t = P t * C)
    (hP0 : P t₀ = 1) : deriv K t₀ = Z * C - C * Z := by
  have hK0 : K t₀ = C := by simpa [hP0] using hKP t₀
  have hL : HasDerivAt (fun t => K t * P t) (deriv K t₀ * P t₀ + K t₀ * Z) t₀ :=
    hK.hasDerivAt.mul hP
  have heq := hL.unique ((hP.mul (hasDerivAt_const t₀ C)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hKP))
  simp only [hP0, hK0, mul_one, mul_zero, add_zero] at heq
  exact eq_sub_of_add_eq heq

end RingInverse
