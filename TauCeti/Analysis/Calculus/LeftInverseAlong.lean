/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.Analysis.Normed.Operator.Splitting.RangeComplement

/-!
# Derivatives of the Lyapunov–Schmidt projections of a family of operators

Let `L(σ) : E →L[𝕜] F` and `P(σ) : F →L[𝕜] Y` be families of continuous linear maps between
normed spaces, depending on a parameter `σ` in a normed space, with `E` complete. At a parameter
where `A(σ) = P(σ) L(σ)` is invertible, the left inverse `K = A⁻¹ P`
(`ContinuousLinearMap.leftInverseAlong`) of `L` along `ker P` is differentiable when the families
are (`DifferentiableAt.leftInverseAlong`, with `WithinAt`, `On` and global variants). So is
`Π = 1 - L K`, the projection onto `ker P` along the range of `L`
(`DifferentiableAt.id_sub_comp_leftInverseAlong` and its variants). The derivatives along a
direction `v` are

`∂ᵥ K = A⁻¹ (∂ᵥ P) Π - K (∂ᵥ L) K` (`HasFDerivWithinAt.leftInverseAlong`,
`HasFDerivAt.leftInverseAlong`, `DifferentiableAt.fderiv_leftInverseAlong`),

`∂ᵥ Π = -Π (∂ᵥ L) K - L A⁻¹ (∂ᵥ P) Π` (`HasFDerivWithinAt.id_sub_comp_leftInverseAlong`,
`HasFDerivAt.id_sub_comp_leftInverseAlong`, `DifferentiableAt.fderiv_id_sub_comp_leftInverseAlong`).
The differentiability lemmas for `K` are `fun_prop` rules.

In a perturbative construction, `P` and its kernel `W` are often chosen once near a base parameter
and then held fixed. Then `∂ᵥ P = 0` and the terms containing it vanish, and for a family of
equations `L(σ) f + S(σ) = 0` the reduced section `σ ↦ Π_σ S(σ)` takes values in the fixed space
`W`; its zeros are the parameters at which the equation is solvable
(`ContinuousLinearMap.apply_add_eq_zero_iff`).

## References

* S. N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, Chapter 2.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open ContinuousLinearMap

variable {𝕜 X E F Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {L : X → E →L[𝕜] F} {P : X → F →L[𝕜] Y} {s : Set X} {x : X}
  {L' : X →L[𝕜] E →L[𝕜] F} {P' : X →L[𝕜] F →L[𝕜] Y}

/-- The left inverse along `ker (P x)` of a family `L x` is differentiable within a set at every
parameter where both families are and `P x ∘ L x` is invertible. -/
@[fun_prop]
theorem DifferentiableWithinAt.leftInverseAlong (hL : DifferentiableWithinAt 𝕜 L s x)
    (hP : DifferentiableWithinAt 𝕜 P s x) (h : (P x ∘L L x).IsInvertible) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (L y).leftInverseAlong (P y)) s x :=
  ((contDiffAt_leftInverseAlong (n := 1) h).differentiableAt one_ne_zero)
    |>.comp_differentiableWithinAt (f := fun y ↦ (L y, P y)) x (hL.prodMk hP)

/-- The left inverse along `ker (P x)` of a family `L x` is differentiable at every parameter
where both families are and `P x ∘ L x` is invertible. -/
@[fun_prop]
theorem DifferentiableAt.leftInverseAlong (hL : DifferentiableAt 𝕜 L x)
    (hP : DifferentiableAt 𝕜 P x) (h : (P x ∘L L x).IsInvertible) :
    DifferentiableAt 𝕜 (fun y ↦ (L y).leftInverseAlong (P y)) x :=
  differentiableWithinAt_univ.1 <|
    hL.differentiableWithinAt.leftInverseAlong hP.differentiableWithinAt h

/-- The left inverse along `ker (P x)` of a family `L x` is differentiable on a set on which both
families are differentiable and every `P x ∘ L x` is invertible. -/
@[fun_prop]
theorem DifferentiableOn.leftInverseAlong (hL : DifferentiableOn 𝕜 L s)
    (hP : DifferentiableOn 𝕜 P s) (h : ∀ x ∈ s, (P x ∘L L x).IsInvertible) :
    DifferentiableOn 𝕜 (fun y ↦ (L y).leftInverseAlong (P y)) s :=
  fun x hx ↦ (hL x hx).leftInverseAlong (hP x hx) (h x hx)

/-- The left inverse along `ker (P x)` of a differentiable family `L x` is differentiable when `P`
is differentiable and every `P x ∘ L x` is invertible. -/
@[fun_prop]
theorem Differentiable.leftInverseAlong (hL : Differentiable 𝕜 L) (hP : Differentiable 𝕜 P)
    (h : ∀ x, (P x ∘L L x).IsInvertible) :
    Differentiable 𝕜 (fun y ↦ (L y).leftInverseAlong (P y)) :=
  fun x ↦ (hL x).leftInverseAlong (hP x) (h x)

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` are
differentiable within a set at every parameter where both families are and `P x ∘ L x` is
invertible. -/
theorem DifferentiableWithinAt.id_sub_comp_leftInverseAlong
    (hL : DifferentiableWithinAt 𝕜 L s x) (hP : DifferentiableWithinAt 𝕜 P s x)
    (h : (P x ∘L L x).IsInvertible) :
    DifferentiableWithinAt 𝕜
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y)) s x :=
  (differentiableWithinAt_const _).sub (hL.clm_comp (hL.leftInverseAlong hP h))

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` are
differentiable at every parameter where both families are and `P x ∘ L x` is invertible. -/
theorem DifferentiableAt.id_sub_comp_leftInverseAlong (hL : DifferentiableAt 𝕜 L x)
    (hP : DifferentiableAt 𝕜 P x) (h : (P x ∘L L x).IsInvertible) :
    DifferentiableAt 𝕜
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y)) x :=
  (differentiableAt_const _).sub (hL.clm_comp (hL.leftInverseAlong hP h))

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` are
differentiable on a set on which both families are differentiable and every `P x ∘ L x` is
invertible. -/
theorem DifferentiableOn.id_sub_comp_leftInverseAlong (hL : DifferentiableOn 𝕜 L s)
    (hP : DifferentiableOn 𝕜 P s) (h : ∀ x ∈ s, (P x ∘L L x).IsInvertible) :
    DifferentiableOn 𝕜
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y)) s :=
  fun x hx ↦ (hL x hx).id_sub_comp_leftInverseAlong (hP x hx) (h x hx)

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` are
differentiable when both families are differentiable and every `P x ∘ L x` is invertible. -/
theorem Differentiable.id_sub_comp_leftInverseAlong (hL : Differentiable 𝕜 L)
    (hP : Differentiable 𝕜 P) (h : ∀ x, (P x ∘L L x).IsInvertible) :
    Differentiable 𝕜
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y)) :=
  fun x ↦ (hL x).id_sub_comp_leftInverseAlong (hP x) (h x)

/-- The derivative within a set of the left inverse `K = A⁻¹ P`, `A = P L`, of `L` along `ker P`
at a parameter where `A` is invertible: along a direction `v`, it is
`A⁻¹ (∂ᵥ P) (1 - L K) - K (∂ᵥ L) K`. -/
theorem HasFDerivWithinAt.leftInverseAlong (hL : HasFDerivWithinAt L L' s x)
    (hP : HasFDerivWithinAt P P' s x) (h : (P x ∘L L x).IsInvertible) :
    HasFDerivWithinAt (fun y ↦ (L y).leftInverseAlong (P y))
      ((compL 𝕜 F Y E (P x ∘L L x).inverse ∘L
          (compL 𝕜 F F Y).flip (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x))) ∘L P' -
        (compL 𝕜 F F E ((L x).leftInverseAlong (P x)) ∘L
          (compL 𝕜 F E F).flip ((L x).leftInverseAlong (P x))) ∘L L') s x := by
  have hA := (hasFDerivAt_id (P x ∘L L x)).clm_inverse_of_completeSpace (𝕜 := 𝕜) h
  simp only [leftInverseAlong_def]
  refine ((hA.comp_hasFDerivWithinAt x (hP.clm_comp hL)).clm_comp hP).congr_fderiv ?_
  ext v f
  simp only [add_apply, sub_apply, neg_apply, coe_comp, Function.comp_apply, compL_apply,
    flip_apply, id_apply, map_sub, map_add, bilinearRestrictScalars_apply_apply, _root_.id_eq]
  abel

/-- The derivative of the left inverse `K = A⁻¹ P`, `A = P L`, of `L` along `ker P` at a
parameter where `A` is invertible: along a direction `v`, it is
`A⁻¹ (∂ᵥ P) (1 - L K) - K (∂ᵥ L) K`. -/
theorem HasFDerivAt.leftInverseAlong (hL : HasFDerivAt L L' x) (hP : HasFDerivAt P P' x)
    (h : (P x ∘L L x).IsInvertible) :
    HasFDerivAt (fun y ↦ (L y).leftInverseAlong (P y))
      ((compL 𝕜 F Y E (P x ∘L L x).inverse ∘L
          (compL 𝕜 F F Y).flip (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x))) ∘L P' -
        (compL 𝕜 F F E ((L x).leftInverseAlong (P x)) ∘L
          (compL 𝕜 F E F).flip ((L x).leftInverseAlong (P x))) ∘L L') x :=
  hasFDerivWithinAt_univ.1 <| hL.hasFDerivWithinAt.leftInverseAlong hP.hasFDerivWithinAt h

/-- The derivative within a set of the Lyapunov–Schmidt projections `Π = 1 - L A⁻¹ P`, `A = P L`,
at a parameter where `A` is invertible: along a direction `v`, it is
`-Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`. -/
theorem HasFDerivWithinAt.id_sub_comp_leftInverseAlong (hL : HasFDerivWithinAt L L' s x)
    (hP : HasFDerivWithinAt P P' s x) (h : (P x ∘L L x).IsInvertible) :
    HasFDerivWithinAt
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y))
      (-((compL 𝕜 F F F (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x)) ∘L
          (compL 𝕜 F E F).flip ((L x).leftInverseAlong (P x))) ∘L L') -
        (compL 𝕜 F E F (L x) ∘L compL 𝕜 F Y E (P x ∘L L x).inverse ∘L
          (compL 𝕜 F F Y).flip (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x))) ∘L P') s x := by
  refine ((hL.clm_comp (hL.leftInverseAlong hP h)).const_sub (.id 𝕜 F)).congr_fderiv ?_
  ext v f
  simp only [add_apply, sub_apply, neg_apply, coe_comp, Function.comp_apply, compL_apply,
    flip_apply, id_apply, map_sub]
  abel

/-- The derivative of the Lyapunov–Schmidt projections `Π = 1 - L A⁻¹ P`, `A = P L`, at a
parameter where `A` is invertible: along a direction `v`, it is
`-Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`. -/
theorem HasFDerivAt.id_sub_comp_leftInverseAlong (hL : HasFDerivAt L L' x)
    (hP : HasFDerivAt P P' x) (h : (P x ∘L L x).IsInvertible) :
    HasFDerivAt
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y))
      (-((compL 𝕜 F F F (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x)) ∘L
          (compL 𝕜 F E F).flip ((L x).leftInverseAlong (P x))) ∘L L') -
        (compL 𝕜 F E F (L x) ∘L compL 𝕜 F Y E (P x ∘L L x).inverse ∘L
          (compL 𝕜 F F Y).flip (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x))) ∘L P') x :=
  hasFDerivWithinAt_univ.1 <|
    hL.hasFDerivWithinAt.id_sub_comp_leftInverseAlong hP.hasFDerivWithinAt h

/-- The derivative of the left inverse `K = A⁻¹ P`, `A = P L`, of `L` along `ker P` for
differentiable families, along a direction `v`, at a parameter where `A` is invertible:
`∂ᵥ K = A⁻¹ (∂ᵥ P) (1 - L K) - K (∂ᵥ L) K`. -/
theorem DifferentiableAt.fderiv_leftInverseAlong (hL : DifferentiableAt 𝕜 L x)
    (hP : DifferentiableAt 𝕜 P x) (h : (P x ∘L L x).IsInvertible) (v : X) :
    fderiv 𝕜 (fun y ↦ (L y).leftInverseAlong (P y)) x v =
      (P x ∘L L x).inverse ∘L fderiv 𝕜 P x v ∘L (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x)) -
        (L x).leftInverseAlong (P x) ∘L fderiv 𝕜 L x v ∘L (L x).leftInverseAlong (P x) := by
  rw [(hL.hasFDerivAt.leftInverseAlong hP.hasFDerivAt h).fderiv]
  simp only [sub_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply]

/-- The derivative of the Lyapunov–Schmidt projections `Π = 1 - L A⁻¹ P`, `A = P L`, of
differentiable families along a direction `v`, at a parameter where `A` is invertible:
`∂ᵥ Π = -Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`. -/
theorem DifferentiableAt.fderiv_id_sub_comp_leftInverseAlong (hL : DifferentiableAt 𝕜 L x)
    (hP : DifferentiableAt 𝕜 P x) (h : (P x ∘L L x).IsInvertible) (v : X) :
    fderiv 𝕜 (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L (L y).leftInverseAlong (P y)) x v =
      -((.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x)) ∘L fderiv 𝕜 L x v ∘L
          (L x).leftInverseAlong (P x)) -
        L x ∘L (P x ∘L L x).inverse ∘L fderiv 𝕜 P x v ∘L
          (.id 𝕜 F - L x ∘L (L x).leftInverseAlong (P x)) := by
  rw [(hL.hasFDerivAt.id_sub_comp_leftInverseAlong hP.hasFDerivAt h).fderiv]
  simp only [sub_apply, neg_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply]
