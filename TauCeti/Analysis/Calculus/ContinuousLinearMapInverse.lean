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
analytic input for differentiating a vector-field pullback along a parametric family. For families
on a general domain, with values in the `𝕜'`-linear maps and differentiated over a subfield `𝕜`, it
gives the smoothness of the inverse family and the derivative formula `∂ᵥ(f⁻¹) = -f⁻¹ (∂ᵥ f) f⁻¹`.
The last part works in an arbitrary normed algebra: it shows that the ring inverse of a `C^n`
family of units is `C^n`, and computes the velocity `Z * C - C * Z` of a family that intertwines a
curve through `1` with the constant `C`; the latter involves no inversion.

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
* `ContDiffWithinAt.clm_inverse`, `ContDiffAt.clm_inverse`, `ContDiffOn.clm_inverse`: the
  inverse of a `C^n` family of maps between Banach spaces, on any domain, is `C^n` where the
  family is invertible.
* `HasFDerivAt.clm_inverse`, `DifferentiableAt.fderiv_clm_inverse`: the derivative
  `∂ᵥ(f⁻¹) = -f⁻¹ (∂ᵥ f) f⁻¹` of such an inverse family along a direction.
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

variable {t₀ : 𝕜} {A : 𝕜 → E →L[𝕜] F} {A' : E →L[𝕜] F} {w : 𝕜 → F} {w' : F}

/-- The derivative of an inverse family of continuous linear maps, assuming the family is
invertible at the base point and the inverse family is differentiable there. -/
theorem HasDerivAt.clm_inverse (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  have hAInv : ∀ᶠ t in 𝓝 t₀, (A t).IsInvertible :=
    hA0Inv.eventually_of_tendsto_inverse hInvDiff.continuousAt
  let B' : F →L[𝕜] E := _root_.deriv (fun t => (A t).inverse) t₀
  have hInvRaw : HasDerivAt (fun t => (A t).inverse) B' t₀ := hInvDiff.hasDerivAt
  have hB'eq : B' = -((A t₀).inverse.comp (A'.comp (A t₀).inverse)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hconst : HasDerivAt (fun _ : 𝕜 => v) 0 t₀ := hasDerivAt_const t₀ v
    have hBv := hInvRaw.clm_apply hconst
    have hABv := hA.clm_apply hBv
    have heq : (fun t => A t ((A t).inverse v)) =ᶠ[𝓝 t₀] fun _ => v := by
      filter_upwards [hAInv] with t ht
      exact ht.self_apply_inverse v
    have hzero : HasDerivAt (fun t => A t ((A t).inverse v)) 0 t₀ := by
      exact hconst.congr_of_eventuallyEq heq
    have hderivZero := hABv.unique hzero
    simp only [map_zero, add_zero] at hderivZero
    apply hA0Inv.injective
    simp only [neg_apply, ContinuousLinearMap.comp_apply]
    rw [map_neg, hA0Inv.self_apply_inverse]
    exact eq_neg_of_add_eq_zero_right hderivZero
  rw [hB'eq] at hInvRaw
  exact hInvRaw

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

/-- The derivative of an inverse family of continuous linear maps between Banach spaces, acting
on a differentiable vector curve. -/
theorem HasDerivAt.clm_inverse_apply_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) (hw : HasDerivAt w w' t₀) :
    HasDerivAt (fun t => (A t).inverse (w t))
      ((A t₀).inverse w' - (A t₀).inverse (A' ((A t₀).inverse (w t₀)))) t₀ := by
  exact hA.clm_inverse_apply hA0Inv
    (DifferentiableAt.clm_inverse_of_completeSpace hA.differentiableAt hA0Inv) hw

section ScalarTower

/-! ### Inverse families on a general domain

Here the family takes values in the `𝕜'`-linear maps `G →L[𝕜'] H` and is differentiated over a
subfield `𝕜`, for instance the complex-linear maps between complex Banach spaces differentiated
over `ℝ`. -/

variable {𝕜' G H : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]
  [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace 𝕜' H] [NormedSpace 𝕜 H] [IsScalarTower 𝕜 𝕜' H]
  {f : E → G →L[𝕜'] H} {s : Set E} {x : E} {n : WithTop ℕ∞}

/-- The inverse of a `C^n` family of continuous linear maps between Banach spaces is `C^n` within
any set at an invertible base point. -/
theorem ContDiffWithinAt.clm_inverse (hf : ContDiffWithinAt 𝕜 n f s x)
    (hx : (f x).IsInvertible) : ContDiffWithinAt 𝕜 n (fun y => (f y).inverse) s x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).comp_contDiffWithinAt x hf

/-- The inverse of a `C^n` family of continuous linear maps between Banach spaces is `C^n` at an
invertible base point. -/
theorem ContDiffAt.clm_inverse (hf : ContDiffAt 𝕜 n f x) (hx : (f x).IsInvertible) :
    ContDiffAt 𝕜 n (fun y => (f y).inverse) x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).comp x hf

/-- The inverse of a family of continuous linear maps between Banach spaces is `C^n` on every
set on which the family is `C^n` and invertible. -/
theorem ContDiffOn.clm_inverse (hf : ContDiffOn 𝕜 n f s) (hinv : ∀ y ∈ s, (f y).IsInvertible) :
    ContDiffOn 𝕜 n (fun y => (f y).inverse) s :=
  fun y hy => (hf y hy).clm_inverse (hinv y hy)

/-- The derivative of the inverse of a family of continuous linear maps between Banach spaces at
an invertible base point: `D(f⁻¹)(v) = -f⁻¹ (f' v) f⁻¹`. -/
theorem HasFDerivAt.clm_inverse {f' : E →L[𝕜] G →L[𝕜'] H} (hf : HasFDerivAt f f' x)
    (hx : (f x).IsInvertible) :
    HasFDerivAt (fun y => (f y).inverse)
      (-(((ContinuousLinearMap.compL 𝕜' H H G).bilinearRestrictScalars 𝕜 (f x).inverse).comp
        ((((ContinuousLinearMap.compL 𝕜' H G H).bilinearRestrictScalars 𝕜).flip
          (f x).inverse).comp f'))) x := by
  let B : (G →L[𝕜'] H) →L[𝕜] (H →L[𝕜'] G) →L[𝕜] (H →L[𝕜'] H) :=
    (ContinuousLinearMap.compL 𝕜' H G H).bilinearRestrictScalars 𝕜
  have hinvx : DifferentiableAt 𝕜 (fun y => (f y).inverse) x :=
    (((hx.contDiffAt_map_inverse (𝕜 := 𝕜') (n := 1)).differentiableAt one_ne_zero).restrictScalars
      𝕜).comp x hf.differentiableAt
  have hev : (fun y => B (f y) (f y).inverse) =ᶠ[𝓝 x] fun _ => ContinuousLinearMap.id 𝕜' H := by
    filter_upwards [hf.continuousAt.eventually hx.eventually_nhds] with y hy
    exact hy.self_comp_inverse
  convert hinvx.hasFDerivAt using 1
  ext1 v
  have h0 := congrArg (fun L => L v) (hev.fderiv_eq (𝕜 := 𝕜))
  rw [B.fderiv_of_bilinear hf.differentiableAt hinvx, hf.fderiv] at h0
  have h1 : (f x).comp (fderiv 𝕜 (fun y => (f y).inverse) x v) =
      -((f' v).comp (f x).inverse) :=
    eq_neg_of_add_eq_zero_left (by simpa [B] using h0)
  calc _ = -((f x).inverse.comp ((f' v).comp (f x).inverse)) := by simp
    _ = ((f x).inverse.comp (f x)).comp (fderiv 𝕜 (fun y => (f y).inverse) x v) := by
        rw [ContinuousLinearMap.comp_assoc, h1, ContinuousLinearMap.comp_neg]
    _ = _ := by rw [hx.inverse_comp_self, ContinuousLinearMap.id_comp]

/-- The derivative of the inverse of a family of continuous linear maps between Banach spaces at
an invertible base point, along a direction `v`: `∂ᵥ(f⁻¹) = -f⁻¹ (∂ᵥ f) f⁻¹`. -/
theorem DifferentiableAt.fderiv_clm_inverse (hf : DifferentiableAt 𝕜 f x)
    (hx : (f x).IsInvertible) (v : E) :
    fderiv 𝕜 (fun y => (f y).inverse) x v =
      -((f x).inverse.comp ((fderiv 𝕜 f x v).comp (f x).inverse)) := by
  simp [(hf.hasFDerivAt.clm_inverse hx).fderiv]

end ScalarTower

/-- The derivative of an inverse family of continuous linear maps between Banach spaces. -/
theorem HasDerivAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  simpa using (hA.hasFDerivAt.clm_inverse hA0Inv).hasDerivAt

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
