/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Algebra.Ring.Invertible
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
* `ContinuousLinearMap.IsInvertible.of_mul_norm_sub_lt` and
  `ContinuousLinearMap.IsInvertible.norm_inverse_le_of_mul_norm_sub_lt`: if `‖A⁻¹‖ ≤ M` and
  `M * ‖B - A‖ < 1`, then `B` is invertible with `‖B⁻¹‖ ≤ M / (1 - M * ‖B - A‖)`.
* `HasStrictFDerivAt.exists_continuousLinearEquiv_id_add`: `y ↦ y + f y` has an invertible strict
  derivative where `f` has a strict derivative of norm less than one.
* `HasDerivAt.clm_inverse`: differentiates `(A t)⁻¹`.
* `HasDerivAt.clm_inverse_apply`: differentiates `(A t)⁻¹ (w t)`.
* `ContDiffWithinAt.clm_inverse`, `ContDiffAt.clm_inverse`, `ContDiffOn.clm_inverse`,
  `ContDiff.clm_inverse`: the inverse of a `C^n` family of maps between Banach spaces, on any
  domain, is `C^n` where the family is invertible.
* `DifferentiableAt.clm_inverse_of_completeSpace`: the inverse of a differentiable family between
  Banach spaces, on any domain, is differentiable at an invertible base point.
* `HasFDerivAt.clm_inverse`, `HasFDerivAt.clm_inverse_of_completeSpace`,
  `DifferentiableAt.fderiv_clm_inverse`: the derivative `∂ᵥ(f⁻¹) = -f⁻¹ (∂ᵥ f) f⁻¹` of an inverse
  family along a direction.
* `HasDerivAt.clm_inverse_of_completeSpace`: the Banach-space specialization for a one-variable
  inverse family.
* `HasDerivAt.clm_inverse_apply_of_completeSpace`: the Banach-space specialization acting on a
  vector curve.
* `ContDiffAt.inverse` and `ContDiff.inverse`: the ring inverse of a `C^n` family of units
  is `C^n`; `ContinuousAt.ringInverse` is the continuous version, on any topological domain.
* `TauCeti.iteratedDeriv_ringInverse_add_smul`: all derivatives of the ring inverse of an
  affine pencil, at any parameter where the pencil is a unit;
  `TauCeti.iteratedDeriv_ringInverse_one_sub_smul` is the commutative form for `1 - r • P`, and
  `TauCeti.iteratedDeriv_succ_smul_ringInverse_one_sub_smul` gives those of `r • (1 - r • P)⁻¹`.
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
  · rw [h0, zero_div, nonpos_iff_eq_zero, nnNorm_eq_zero, sub_eq_zero] at h
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

/-- A continuous linear map `B` with `M * ‖B - A‖ < 1`, where `M` bounds the inverse of an
invertible `A`, is invertible. -/
theorem ContinuousLinearMap.IsInvertible.of_mul_norm_sub_lt [CompleteSpace E] {A B : E →L[𝕜] F}
    (hA : A.IsInvertible) {M : ℝ} (hM : ‖A.inverse‖ ≤ M) (h : M * ‖B - A‖ < 1) :
    B.IsInvertible := by
  obtain ⟨e, rfl⟩ := hA
  refine isInvertible_of_mul_norm_sub_lt e.surjective (fun x ↦ ?_) h
  rw [inverse_equiv] at hM
  calc ‖x‖ = ‖(e.symm : F →L[𝕜] E) (e x)‖ := by simp
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖e x‖ := le_opNorm _ _
    _ ≤ M * ‖e x‖ := by gcongr

/-- **The Neumann bound for the inverse of a perturbation.** If `‖A⁻¹‖ ≤ M` for an invertible
`A` and `M * ‖B - A‖ < 1`, then `B` is invertible
(`ContinuousLinearMap.IsInvertible.of_mul_norm_sub_lt`) and
`‖B⁻¹‖ ≤ M / (1 - M * ‖B - A‖)`. -/
theorem ContinuousLinearMap.IsInvertible.norm_inverse_le_of_mul_norm_sub_lt [CompleteSpace E]
    {A B : E →L[𝕜] F} (hA : A.IsInvertible) {M : ℝ} (hM : ‖A.inverse‖ ≤ M)
    (h : M * ‖B - A‖ < 1) : ‖B.inverse‖ ≤ M / (1 - M * ‖B - A‖) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hδ : 0 < 1 - M * ‖B - A‖ := sub_pos.2 h
  obtain ⟨f, rfl⟩ := hA.of_mul_norm_sub_lt hM h
  rw [inverse_equiv]
  refine opNorm_le_bound _ (div_nonneg hM0 hδ.le) fun y ↦ ?_
  -- With `x = B⁻¹ y`, `‖x‖ ≤ M ‖A x‖ ≤ M ‖y‖ + M ‖B - A‖ ‖x‖`.
  set x := (f.symm : F →L[𝕜] E) y
  have hy : (f : E →L[𝕜] F) x = y := by simp [x]
  have hAx : ‖A x‖ ≤ ‖y‖ + ‖(f : E →L[𝕜] F) - A‖ * ‖x‖ := by
    calc ‖A x‖ = ‖y - ((f : E →L[𝕜] F) - A) x‖ := by simp [hy]
      _ ≤ ‖y‖ + ‖((f : E →L[𝕜] F) - A) x‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖(f : E →L[𝕜] F) - A‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
  have hx : ‖x‖ ≤ M * ‖A x‖ := by
    calc ‖x‖ ≤ ‖A.inverse‖ * ‖A x‖ := hA.norm_le_norm_inverse_mul_norm x
      _ ≤ M * ‖A x‖ := by gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left hAx hM0]

/-- A strict derivative of norm less than one is a small perturbation of the identity: if `f` has
strict derivative `f'` at `x` with `‖f'‖ < 1`, then `y ↦ y + f y` has an invertible strict
derivative at `x`, namely `1 + f'`. -/
theorem HasStrictFDerivAt.exists_continuousLinearEquiv_id_add [CompleteSpace E] {f : E → E}
    {f' : E →L[𝕜] E} {x : E} (hf : HasStrictFDerivAt f f' x) (hf' : ‖f'‖ < 1) :
    ∃ L : E ≃L[𝕜] E, HasStrictFDerivAt (fun y ↦ y + f y) (L : E →L[𝕜] E) x := by
  set L := ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub (-f') (by rwa [norm_neg]))
  have hL : (L : E →L[𝕜] E) = ContinuousLinearMap.id 𝕜 E + f' := by
    ext v
    simp [L, ContinuousLinearEquiv.unitsEquiv_apply]
  exact ⟨L, hL ▸ (hasStrictFDerivAt_id x).add hf⟩

end Perturbation

section ScalarTower

/-! ### Inverse families on a general domain

Here the family takes values in the `𝕜'`-linear maps `G →L[𝕜'] H` and is differentiated over a
subfield `𝕜`, for instance the complex-linear maps between complex Banach spaces differentiated
over `ℝ`. -/

variable {𝕜' G H : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]
  [NormedAddCommGroup H] [NormedSpace 𝕜' H] [NormedSpace 𝕜 H] [IsScalarTower 𝕜 𝕜' H]
  {f : E → G →L[𝕜'] H} {s : Set E} {x : E} {n : WithTop ℕ∞}

/-- The inverse of a `C^n` family of continuous linear maps between Banach spaces is `C^n` within
any set at an invertible base point. -/
theorem ContDiffWithinAt.clm_inverse [CompleteSpace G] (hf : ContDiffWithinAt 𝕜 n f s x)
    (hx : (f x).IsInvertible) : ContDiffWithinAt 𝕜 n (fun y => (f y).inverse) s x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).comp_contDiffWithinAt x hf

/-- The inverse of a `C^n` family of continuous linear maps between Banach spaces is `C^n` at an
invertible base point. -/
theorem ContDiffAt.clm_inverse [CompleteSpace G] (hf : ContDiffAt 𝕜 n f x)
    (hx : (f x).IsInvertible) :
    ContDiffAt 𝕜 n (fun y => (f y).inverse) x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜')).restrict_scalars 𝕜).comp x hf

/-- The inverse of a family of continuous linear maps between Banach spaces is `C^n` on every
set on which the family is `C^n` and invertible. -/
theorem ContDiffOn.clm_inverse [CompleteSpace G] (hf : ContDiffOn 𝕜 n f s)
    (hinv : ∀ y ∈ s, (f y).IsInvertible) :
    ContDiffOn 𝕜 n (fun y => (f y).inverse) s :=
  fun y hy => (hf y hy).clm_inverse (hinv y hy)

/-- The inverse of a `C^n` family of continuous linear maps between Banach spaces that is invertible
everywhere is `C^n`. -/
theorem ContDiff.clm_inverse [CompleteSpace G] (hf : ContDiff 𝕜 n f)
    (hinv : ∀ y, (f y).IsInvertible) :
    ContDiff 𝕜 n (fun y => (f y).inverse) :=
  contDiff_iff_contDiffAt.2 fun y => hf.contDiffAt.clm_inverse (hinv y)

/-- The derivative of an inverse family of continuous linear maps, assuming the family is
invertible at the base point and the inverse family is differentiable there:
`D(f⁻¹)(v) = -f⁻¹ (f' v) f⁻¹`. -/
theorem HasFDerivAt.clm_inverse {f' : E →L[𝕜] G →L[𝕜'] H} (hf : HasFDerivAt f f' x)
    (hx : (f x).IsInvertible) (hinvx : DifferentiableAt 𝕜 (fun y => (f y).inverse) x) :
    HasFDerivAt (fun y => (f y).inverse)
      (-(((ContinuousLinearMap.compL 𝕜' H H G).bilinearRestrictScalars 𝕜 (f x).inverse).comp
        ((((ContinuousLinearMap.compL 𝕜' H G H).bilinearRestrictScalars 𝕜).flip
          (f x).inverse).comp f'))) x := by
  let B : (G →L[𝕜'] H) →L[𝕜] (H →L[𝕜'] G) →L[𝕜] (H →L[𝕜'] H) :=
    (ContinuousLinearMap.compL 𝕜' H G H).bilinearRestrictScalars 𝕜
  have hev : (fun y => B (f y) (f y).inverse) =ᶠ[𝓝 x] fun _ => ContinuousLinearMap.id 𝕜' H := by
    filter_upwards [hx.eventually_of_tendsto_inverse hinvx.continuousAt] with y hy
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

/-- The inverse of a differentiable family of continuous linear maps between Banach spaces is
differentiable at an invertible base point. -/
theorem DifferentiableAt.clm_inverse_of_completeSpace [CompleteSpace G]
    (hf : DifferentiableAt 𝕜 f x) (hx : (f x).IsInvertible) :
    DifferentiableAt 𝕜 (fun y => (f y).inverse) x :=
  ((hx.contDiffAt_map_inverse (𝕜 := 𝕜') (n := 1)).differentiableAt one_ne_zero).restrictScalars 𝕜
    |>.comp x hf

/-- The derivative of the inverse of a differentiable family of continuous linear maps between
Banach spaces at an invertible base point: `D(f⁻¹)(v) = -f⁻¹ (f' v) f⁻¹`. -/
theorem HasFDerivAt.clm_inverse_of_completeSpace [CompleteSpace G] {f' : E →L[𝕜] G →L[𝕜'] H}
    (hf : HasFDerivAt f f' x) (hx : (f x).IsInvertible) :
    HasFDerivAt (fun y => (f y).inverse)
      (-(((ContinuousLinearMap.compL 𝕜' H H G).bilinearRestrictScalars 𝕜 (f x).inverse).comp
        ((((ContinuousLinearMap.compL 𝕜' H G H).bilinearRestrictScalars 𝕜).flip
          (f x).inverse).comp f'))) x :=
  hf.clm_inverse hx (hf.differentiableAt.clm_inverse_of_completeSpace hx)

/-- The derivative of the inverse of a family of continuous linear maps between Banach spaces at
an invertible base point, along a direction `v`: `∂ᵥ(f⁻¹) = -f⁻¹ (∂ᵥ f) f⁻¹`. -/
theorem DifferentiableAt.fderiv_clm_inverse [CompleteSpace G] (hf : DifferentiableAt 𝕜 f x)
    (hx : (f x).IsInvertible) (v : E) :
    fderiv 𝕜 (fun y => (f y).inverse) x v =
      -((f x).inverse.comp ((fderiv 𝕜 f x v).comp (f x).inverse)) := by
  simp [(hf.hasFDerivAt.clm_inverse_of_completeSpace hx).fderiv]

end ScalarTower

variable {t₀ : 𝕜} {A : 𝕜 → E →L[𝕜] F} {A' : E →L[𝕜] F} {w : 𝕜 → F} {w' : F}

/-- The derivative of an inverse family of continuous linear maps, assuming the family is
invertible at the base point and the inverse family is differentiable there. -/
theorem HasDerivAt.clm_inverse (hA : HasDerivAt A A' t₀)
    (hA0Inv : (A t₀).IsInvertible)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (A t).inverse) t₀) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  simpa using (hA.hasFDerivAt.clm_inverse hA0Inv hInvDiff).hasDerivAt

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

/-- The derivative of an inverse family of continuous linear maps between Banach spaces. -/
theorem HasDerivAt.clm_inverse_of_completeSpace [CompleteSpace E]
    (hA : HasDerivAt A A' t₀) (hA0Inv : (A t₀).IsInvertible) :
    HasDerivAt (fun t => (A t).inverse)
      (-((A t₀).inverse.comp (A'.comp (A t₀).inverse))) t₀ := by
  simpa using (hA.hasFDerivAt.clm_inverse_of_completeSpace hA0Inv).hasDerivAt

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

/-- The ring inverse of a family continuous at a point where it takes a unit value is continuous
there. -/
theorem ContinuousAt.ringInverse {Y : Type*} [TopologicalSpace Y] {f : Y → R} {y : Y}
    (hf : ContinuousAt f y) (hfy : IsUnit (f y)) :
    ContinuousAt (fun y' => Ring.inverse (f y')) y :=
  (NormedRing.inverse_continuousAt hfy.unit).comp_of_eq hf hfy.unit_spec.symm

/-- The ring inverse of a `C^n` family of units is `C^n`. -/
theorem ContDiff.inverse {f : X → R} (hf : ContDiff 𝕜 n f) (hfu : ∀ x, IsUnit (f x)) :
    ContDiff 𝕜 n (fun y => Ring.inverse (f y)) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.inverse (hfu x)

/-- All derivatives of the ring inverse of an affine pencil at a unit value, with the
noncommutative product order preserved. No invertibility away from the evaluation point is
required. -/
theorem TauCeti.iteratedDeriv_ringInverse_add_smul (a b : R) (k : ℕ) {t : 𝕜}
    (ht : IsUnit (a + t • b)) :
    iteratedDeriv k (fun s : 𝕜 ↦ Ring.inverse (a + s • b)) t =
      ((-1 : 𝕜) ^ k * (Nat.factorial k : 𝕜)) •
        (Ring.inverse (a + t • b) * (b * Ring.inverse (a + t • b)) ^ k) := by
  have hR (t : 𝕜) (ht : IsUnit (a + t • b)) :
      HasDerivAt (fun s : 𝕜 ↦ Ring.inverse (a + s • b))
      (-(Ring.inverse (a + t • b) * b * Ring.inverse (a + t • b))) t := by
    obtain ⟨u, hu⟩ := ht
    have hd : HasDerivAt (fun s : 𝕜 ↦ a + s • b) b t := by
      simpa only [one_smul, id_eq] using! ((hasDerivAt_id t).smul_const b).const_add a
    simpa only [Function.comp_def, ← hu, Ring.inverse_unit,
      neg_apply, ContinuousLinearMap.mulLeftRight_apply] using!
      (hasFDerivAt_ringInverse (𝕜 := 𝕜) u).comp_hasDerivAt_of_eq t hd hu
  have hword (t : 𝕜) (ht : IsUnit (a + t • b)) (j : ℕ) : HasDerivAt
      (fun s : 𝕜 ↦ Ring.inverse (a + s • b) * (b * Ring.inverse (a + s • b)) ^ j)
      (-((j + 1 : ℕ) : 𝕜) •
        (Ring.inverse (a + t • b) * (b * Ring.inverse (a + t • b)) ^ (j + 1))) t := by
    have hR := hR t ht
    induction j with
    | zero => simpa [pow_one, mul_assoc] using hR
    | succ j ih =>
      have hd := ih.fun_mul (hR.const_mul b)
      simp only [pow_succ, ← mul_assoc] at hd ⊢
      refine hd.congr_deriv ?_
      simp only [smul_mul_assoc, mul_neg, mul_assoc, Nat.cast_add, Nat.cast_one,
        neg_add, add_smul, neg_one_smul, add_mul, neg_mul]
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hu : ∀ᶠ s in 𝓝 t, IsUnit (a + s • b) :=
      (Units.isOpen.preimage (by fun_prop : Continuous (fun s : 𝕜 ↦ a + s • b))).mem_nhds ht
    have heq : iteratedDeriv k (fun s : 𝕜 ↦ Ring.inverse (a + s • b)) =ᶠ[𝓝 t]
        fun s ↦ ((-1 : 𝕜) ^ k * (Nat.factorial k : 𝕜)) •
          (Ring.inverse (a + s • b) * (b * Ring.inverse (a + s • b)) ^ k) :=
      hu.mono fun s hs ↦ ih hs
    rw [iteratedDeriv_succ, heq.deriv_eq,
      ((hword t ht k).fun_const_smul ((-1 : 𝕜) ^ k * (Nat.factorial k : 𝕜))).deriv, smul_smul]
    congr 1
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- `∂_r^j (1 - r P)⁻¹ = j! P ^ j ((1 - r P)⁻¹) ^ (j + 1)` where `1 - r P` is a unit: the
commutative form of `TauCeti.iteratedDeriv_ringInverse_add_smul`, as `P` commutes with
`(1 - r P)⁻¹`. -/
theorem TauCeti.iteratedDeriv_ringInverse_one_sub_smul (P : R) (j : ℕ) {r : 𝕜}
    (hr : IsUnit (1 - r • P)) :
    iteratedDeriv j (fun s : 𝕜 => Ring.inverse (1 - s • P)) r =
      (Nat.factorial j : 𝕜) • (P ^ j * Ring.inverse (1 - r • P) ^ (j + 1)) := by
  have h1 (s : 𝕜) : 1 - s • P = 1 + s • -P := by rw [smul_neg, sub_eq_add_neg]
  have hc := ((Commute.one_right P).sub_right ((Commute.refl P).smul_right r)).ringInverse_right
  simp only [h1] at hr hc ⊢
  have hI : Ring.inverse (1 + r • -P) * (P * Ring.inverse (1 + r • -P)) ^ j =
      P ^ j * Ring.inverse (1 + r • -P) ^ (j + 1) := by
    rw [hc.mul_pow, ← mul_assoc, ← (hc.pow_left j).eq, mul_assoc, ← pow_succ']
  rw [iteratedDeriv_ringInverse_add_smul 1 (-P) j hr, neg_mul, ← hI]
  rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow, h.neg_pow]

/-- `∂_r^(j + 1) (r (1 - r P)⁻¹) = (j + 1)! P ^ j ((1 - r P)⁻¹) ^ (j + 2)` where `1 - r P` is a
unit. By Leibniz's rule it is `r ∂_r^(j + 1) (1 - r P)⁻¹ + (j + 1) ∂_r^j (1 - r P)⁻¹`, and
`1 + r P (1 - r P)⁻¹ = (1 - r P)⁻¹`; for `j = 0` the derivative is `((1 - r P)⁻¹) ^ 2`. -/
theorem TauCeti.iteratedDeriv_succ_smul_ringInverse_one_sub_smul (P : R) (j : ℕ) {r : 𝕜}
    (hr : IsUnit (1 - r • P)) :
    iteratedDeriv (j + 1) (fun s : 𝕜 => s • Ring.inverse (1 - s • P)) r =
      (Nat.factorial (j + 1) : 𝕜) • (P ^ j * Ring.inverse (1 - r • P) ^ (j + 2)) := by
  set I := Ring.inverse (1 - r • P)
  have hI : ContDiffAt 𝕜 (j + 1) (fun s : 𝕜 => Ring.inverse (1 - s • P)) r :=
    ContDiffAt.inverse (by fun_prop) hr
  have hid (i : ℕ) : iteratedDeriv i (fun s : 𝕜 => s • (1 : R)) r =
      iteratedDeriv i (fun s : 𝕜 => s) r • (1 : R) :=
    iteratedDeriv_smul_const (f := fun s : 𝕜 => s) (by fun_prop) 1
  -- Leibniz's rule for `r • (1 - r P)⁻¹ = (r • 1) (1 - r P)⁻¹`: only two terms survive.
  have hsum : iteratedDeriv (j + 1) (fun s : 𝕜 => s • Ring.inverse (1 - s • P)) r =
      (Nat.factorial j : 𝕜) • (((j : R) + 1) * (P ^ j * I ^ (j + 1))) +
        (Nat.factorial (j + 1) : 𝕜) • r • (P ^ (j + 1) * I ^ (j + 1 + 1)) := by
    have hmul : (fun s : 𝕜 => s • Ring.inverse (1 - s • P)) =
        fun s => (s • (1 : R)) * Ring.inverse (1 - s • P) := by
      funext s
      rw [smul_one_mul]
    rw [hmul, iteratedDeriv_fun_mul (by fun_prop) hI, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp [hid, iteratedDeriv_fun_id, iteratedDeriv_ringInverse_one_sub_smul P _ hr, I]
  have hcomm : Commute P I :=
    ((Commute.one_right P).sub_right ((Commute.refl P).smul_right r)).ringInverse_right
  have hI1 : I = 1 + r • (P * I) := by
    have h := Ring.mul_inverse_cancel _ hr
    rw [sub_mul, one_mul, smul_mul_assoc] at h
    rw [← h, sub_add_cancel]
  have hPI : P ^ j * I ^ (j + 1) * (P * I) = P ^ (j + 1) * I ^ (j + 2) := by
    calc P ^ j * I ^ (j + 1) * (P * I) = P ^ j * (I ^ (j + 1) * P) * I := by
          simp only [mul_assoc]
      _ = P ^ j * P * (I ^ (j + 1) * I) := by
          rw [← (hcomm.pow_right _).eq]
          simp only [mul_assoc]
      _ = P ^ (j + 1) * I ^ (j + 2) := by rw [← pow_succ, ← pow_succ]
  -- since `(1 - r P)⁻¹ = 1 + r P (1 - r P)⁻¹`
  have key : P ^ j * I ^ (j + 2) = P ^ j * I ^ (j + 1) + r • (P ^ (j + 1) * I ^ (j + 2)) := by
    calc P ^ j * I ^ (j + 2) = P ^ j * I ^ (j + 1) * (1 + r • (P * I)) := by
          rw [← hI1, pow_succ I (j + 1), mul_assoc]
      _ = _ := by rw [mul_add, mul_one, mul_smul_comm, hPI]
  have hcast : ((j : R) + 1) * (P ^ j * I ^ (j + 1)) = ((j : 𝕜) + 1) • (P ^ j * I ^ (j + 1)) := by
    rw [Algebra.smul_def]
    simp
  rw [hsum, hcast, key, Nat.factorial_succ]
  push_cast
  module

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
