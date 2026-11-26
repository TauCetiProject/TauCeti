/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.BilinearMap.Splitting

/-!
# Contact lifts of conformally symplectic linear maps

Let `V` be a real inner product space and let `α = dz - ⟪p, dq⟫` be the standard contact form
`TauCeti.innerProductContactForm` on `V × V × ℝ`, with coordinates `(q, p, z)`. Its exterior
derivative is the standard symplectic form `ω` of the `(q, p)` coordinates
(`TauCeti.stdSymplecticForm`). A linear map `A` of `V × V` is *conformally symplectic with
multiplier `c`* when `ω(A u, A w) = c ω(u, w)` for all `u` and `w`.

Every such map lifts to a polynomial contactomorphism of `V × V × ℝ` fixing the origin. Writing
`w = (q, p)`, the **contact lift** (`TauCeti.conformalContactLift A c`) is

`(q, p, z) ↦ (A w, c z + (⟪(A w).2, (A w).1⟫ - c ⟪p, q⟫) / 2)`,

and it pulls the standard contact form back to `c α`
(`TauCeti.mpullback_conformalContactLift_innerProductContactForm`). The quadratic correction in
the `z` coordinate is what makes this exact: without it the pullback would be
`c dz - ⟪(A w).2, d(A w).1⟫`, which differs from `c α` by a nonzero exact form in general. The lift
fixes the origin, and its differential there is `A` on the
contact hyperplane `V × V × {0}` and multiplication by `c` on the `z`-axis
(`TauCeti.fderiv_conformalContactLift_zero_apply`). So for `c ≠ 0` the differential at the origin
of a contactomorphism of the standard contact structure can be any conformally symplectic map of
the contact hyperplane, with any multiplier on the contact line.

The lifts compose like the linear maps they lift: the lift of `A ∘ B` with multiplier `c d` is the
lift of `A` with `c` after the lift of `B` with `d` (`TauCeti.conformalContactLift_comp`), and the
identity with multiplier `1` lifts to the identity. Hence the lift of a continuous linear
equivalence with nonzero multiplier is a diffeomorphism
(`TauCeti.conformalContactLiftDiffeomorph`), with inverse the lift of the inverse map; it is a
contactomorphism when `A` is conformally symplectic
(`TauCeti.isContactomorphism_conformalContactLiftDiffeomorph`). A conformally symplectic map with
nonzero multiplier is injective (`TauCeti.injective_of_stdSymplecticForm_map_eq_mul`), so in finite
dimension it is a linear equivalence.

## Main definitions

* `TauCeti.conformalContactLift A c`: the contact lift of `A` with multiplier `c`.
* `TauCeti.conformalContactLiftDiffeomorph A hc`: the lift of a continuous linear equivalence with
  nonzero multiplier, as a diffeomorphism.

## Main results

* `TauCeti.mpullback_conformalContactLift_innerProductContactForm`: the lift of a conformally
  symplectic map with multiplier `c` pulls `α` back to `c α`.
* `TauCeti.fderiv_conformalContactLift_zero_apply`: the differential of the lift at the origin.
* `TauCeti.conformalContactLift_comp`: lifts compose.
* `TauCeti.isContactomorphism_conformalContactLiftDiffeomorph`: the lift is a contactomorphism.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the linear conformal symplectic data of the contact neighbourhood
  theorems).
-/

public section

noncomputable section

open scoped RealInnerProductSpace ContDiff Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **contact lift** of a linear map `A` of `V × V` with multiplier `c`: the map
`(q, p, z) ↦ (A w, c z + (⟪(A w).2, (A w).1⟫ - c ⟪p, q⟫) / 2)` of the standard contact space,
where `w = (q, p)`. When `A` is conformally symplectic with multiplier `c`, it pulls the standard
contact form back to `c` times itself
(`TauCeti.mpullback_conformalContactLift_innerProductContactForm`). -/
def conformalContactLift (A : V × V →L[ℝ] V × V) (c : ℝ) (x : V × V × ℝ) : V × V × ℝ :=
  ((A (x.1, x.2.1)).1, (A (x.1, x.2.1)).2,
    c * x.2.2 + (⟪(A (x.1, x.2.1)).2, (A (x.1, x.2.1)).1⟫ - c * ⟪x.2.1, x.1⟫) / 2)

variable {A B : V × V →L[ℝ] V × V} {c d : ℝ}

/-- The defining formula of the contact lift. -/
theorem conformalContactLift_apply (A : V × V →L[ℝ] V × V) (c : ℝ) (x : V × V × ℝ) :
    conformalContactLift A c x = ((A (x.1, x.2.1)).1, (A (x.1, x.2.1)).2,
      c * x.2.2 + (⟪(A (x.1, x.2.1)).2, (A (x.1, x.2.1)).1⟫ - c * ⟪x.2.1, x.1⟫) / 2) :=
  (rfl)

/-- The `q` coordinate of the contact lift is the first component of `A (q, p)`. -/
@[simp]
theorem conformalContactLift_fst (A : V × V →L[ℝ] V × V) (c : ℝ) (x : V × V × ℝ) :
    (conformalContactLift A c x).1 = (A (x.1, x.2.1)).1 :=
  (rfl)

/-- The `p` coordinate of the contact lift is the second component of `A (q, p)`. -/
@[simp]
theorem conformalContactLift_snd_fst (A : V × V →L[ℝ] V × V) (c : ℝ) (x : V × V × ℝ) :
    (conformalContactLift A c x).2.1 = (A (x.1, x.2.1)).2 :=
  (rfl)

/-- The `z` coordinate of the contact lift. -/
@[simp]
theorem conformalContactLift_snd_snd (A : V × V →L[ℝ] V × V) (c : ℝ) (x : V × V × ℝ) :
    (conformalContactLift A c x).2.2 =
      c * x.2.2 + (⟪(A (x.1, x.2.1)).2, (A (x.1, x.2.1)).1⟫ - c * ⟪x.2.1, x.1⟫) / 2 :=
  (rfl)

/-- The contact lift fixes the origin. -/
@[simp]
theorem conformalContactLift_zero (A : V × V →L[ℝ] V × V) (c : ℝ) :
    conformalContactLift A c 0 = 0 := by
  have h : (((0 : V × V × ℝ).1, (0 : V × V × ℝ).2.1) : V × V) = 0 := rfl
  rw [conformalContactLift_apply, h, map_zero]
  simp

/-- The identity with multiplier `1` lifts to the identity. -/
@[simp]
theorem conformalContactLift_id :
    conformalContactLift (ContinuousLinearMap.id ℝ (V × V)) 1 = id := by
  funext x
  simp [conformalContactLift_apply, real_inner_comm x.1 x.2.1]

/-- **Contact lifts compose like the linear maps they lift**: the lift of `A ∘ B` with multiplier
`c d` is the lift of `A` with multiplier `c` after the lift of `B` with multiplier `d`. -/
theorem conformalContactLift_comp (A B : V × V →L[ℝ] V × V) (c d : ℝ) :
    conformalContactLift A c ∘ conformalContactLift B d =
      conformalContactLift (A ∘L B) (c * d) := by
  funext x
  simp only [Function.comp_apply, conformalContactLift_apply, ContinuousLinearMap.comp_apply,
    Prod.mk.injEq, true_and]
  ring

/-- The linear map `(q, p, z) ↦ (q, p)` onto the `(q, p)` coordinates. -/
private def qpProj : V × V × ℝ →L[ℝ] V × V :=
  (ContinuousLinearMap.fst ℝ V (V × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ)))

private theorem qpProj_apply (x : V × V × ℝ) : qpProj x = (x.1, x.2.1) :=
  (rfl)

/-- The contact lift has the derivative obtained by differentiating its defining formula. -/
private theorem hasFDerivAt_conformalContactLift (A : V × V →L[ℝ] V × V) (c : ℝ)
    (x : V × V × ℝ) :
    ∃ L : V × V × ℝ →L[ℝ] V × V × ℝ, HasFDerivAt (conformalContactLift A c) L x ∧
      ∀ v, L v = ((A (v.1, v.2.1)).1, (A (v.1, v.2.1)).2,
        c * v.2.2 + (⟪(A (x.1, x.2.1)).2, (A (v.1, v.2.1)).1⟫ +
          ⟪(A (v.1, v.2.1)).2, (A (x.1, x.2.1)).1⟫ -
            c * (⟪x.2.1, v.1⟫ + ⟪v.2.1, x.1⟫)) / 2) := by
  have hL : HasFDerivAt (fun y : V × V × ℝ ↦ A (y.1, y.2.1)) (A ∘L qpProj) x :=
    (A ∘L qpProj).hasFDerivAt
  have h₁ := (ContinuousLinearMap.fst ℝ V V).hasFDerivAt.comp x hL
  have h₂ := (ContinuousLinearMap.snd ℝ V V).hasFDerivAt.comp x hL
  have hq := (ContinuousLinearMap.fst ℝ V (V × ℝ)).hasFDerivAt (x := x)
  have hp := ((ContinuousLinearMap.fst ℝ V ℝ).comp
    (ContinuousLinearMap.snd ℝ V (V × ℝ))).hasFDerivAt (x := x)
  have hz := ((ContinuousLinearMap.snd ℝ V ℝ).comp
    (ContinuousLinearMap.snd ℝ V (V × ℝ))).hasFDerivAt (x := x)
  have h₃ := (hz.const_mul c).add
    (((h₂.inner ℝ h₁).sub ((hp.inner ℝ hq).const_mul c)).mul_const (2⁻¹ : ℝ))
  have hF : conformalContactLift A c = fun y : V × V × ℝ ↦ ((A (y.1, y.2.1)).1,
      (A (y.1, y.2.1)).2, c * y.2.2 +
        (⟪(A (y.1, y.2.1)).2, (A (y.1, y.2.1)).1⟫ - c * ⟪y.2.1, y.1⟫) * 2⁻¹) := by
    funext y
    simp [conformalContactLift_apply, div_eq_mul_inv]
  rw [hF]
  refine ⟨_, h₁.prodMk (h₂.prodMk h₃), fun v ↦ ?_⟩
  simp [qpProj_apply, fderivInnerCLM_apply, div_eq_mul_inv]
  ring

/-- The contact lift is smooth. -/
theorem contDiff_conformalContactLift (A : V × V →L[ℝ] V × V) (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (conformalContactLift A c) := by
  have hL : ContDiff ℝ n (fun y : V × V × ℝ ↦ A (y.1, y.2.1)) := (A ∘L qpProj).contDiff
  exact (contDiff_fst.comp hL).prodMk ((contDiff_snd.comp hL).prodMk
    ((contDiff_const.mul (contDiff_snd.comp contDiff_snd)).add
      ((((contDiff_snd.comp hL).inner ℝ (contDiff_fst.comp hL)).sub
        (contDiff_const.mul ((contDiff_fst.comp contDiff_snd).inner ℝ contDiff_fst))).div_const
          2)))

/-- **The differential of the contact lift at the origin** is `A` on the `(q, p)` coordinates and
multiplication by `c` on the `z` coordinate. -/
theorem fderiv_conformalContactLift_zero_apply (A : V × V →L[ℝ] V × V) (c : ℝ)
    (v : V × V × ℝ) :
    fderiv ℝ (conformalContactLift A c) 0 v =
      ((A (v.1, v.2.1)).1, (A (v.1, v.2.1)).2, c * v.2.2) := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_conformalContactLift A c 0
  have h₀ : (((0 : V × V × ℝ).1, (0 : V × V × ℝ).2.1) : V × V) = 0 := rfl
  rw [hL.fderiv, hLv, h₀, map_zero]
  simp

/-- **The contact lift of a conformally symplectic map is a conformal contactomorphism.** If
`ω(A u, A w) = c ω(u, w)` for the standard symplectic form `ω` of `V × V`, then the contact lift
of `A` with multiplier `c` pulls the standard contact form `α = dz - ⟪p, dq⟫` back to `c α`. -/
theorem mpullback_conformalContactLift_innerProductContactForm
    (hA : ∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) :
    mpullback 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (conformalContactLift A c)
      (innerProductContactForm V).val = (c • innerProductContactForm V).val := by
  funext x
  ext v
  -- A one-form only sees the single entry `v 0` of `v`.
  have hv : v = ![v 0] := by
    ext i
    fin_cases i
    rfl
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_conformalContactLift A c x
  have hAv := hA (x.1, x.2.1) ((v 0).1, (v 0).2.1)
  rw [stdSymplecticForm_apply, stdSymplecticForm_apply] at hAv
  have hdv : (fun i ↦ mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (conformalContactLift A c) x
      (v i)) = ![mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (conformalContactLift A c) x (v 0)] := by
    ext i
    fin_cases i
    rfl
  -- The casts between tangent spaces and the model space in `mfderiv_eq_fderiv` are the identity
  -- by definition.
  have hm : @Eq (V × V × ℝ)
      (mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) (conformalContactLift A c) x (v 0))
      ((A ((v 0).1, (v 0).2.1)).1, (A ((v 0).1, (v 0).2.1)).2,
        c * (v 0).2.2 + (⟪(A (x.1, x.2.1)).2, (A ((v 0).1, (v 0).2.1)).1⟫ +
          ⟪(A ((v 0).1, (v 0).2.1)).2, (A (x.1, x.2.1)).1⟫ -
            c * (⟪x.2.1, (v 0).1⟫ + ⟪(v 0).2.1, x.1⟫)) / 2) := by
    rw [mfderiv_eq_fderiv, hL.fderiv]
    exact hLv (v 0)
  rw [mpullback_apply, hdv, SmoothForm.smul_toRoughForm, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  conv_rhs => rw [hv]
  rw [innerProductContactForm_apply, innerProductContactForm_apply, hm]
  simp only [conformalContactLift_snd_fst, smul_eq_mul] at hAv ⊢
  rw [real_inner_comm (A (x.1, x.2.1)).1, real_inner_comm x.1 (v 0).2.1]
  linear_combination (1 / 2 : ℝ) * hAv

/-- A linear map of `V × V` that is conformally symplectic with nonzero multiplier is injective,
since the standard symplectic form is nondegenerate. -/
theorem injective_of_stdSymplecticForm_map_eq_mul (hc : c ≠ 0)
    (hA : ∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) :
    Function.Injective A := by
  have hB : Function.Injective (stdSymplecticForm (V := V)).toBilinForm := LinearMap.ker_eq_bot.1
    (LinearMap.separatingLeft_iff_ker_eq_bot.1 (stdSymplecticForm (V := V)).nondegenerate.1)
  refine LinearMap.injective_left_of_compl₁₂_eq_compr₂
    (q := (stdSymplecticForm (V := V)).toBilinForm) (b := (A : V × V →ₗ[ℝ] V × V))
    (φ := c • LinearMap.id) ?_ hB (smul_right_injective ℝ hc)
  refine LinearMap.ext₂ fun u w ↦ ?_
  simpa using hA u w

/-- The contact lift of a continuous linear equivalence `A` of `V × V` with a nonzero multiplier
`c`, as a diffeomorphism of `V × V × ℝ`. Its inverse is the lift of `A⁻¹` with multiplier
`c⁻¹`. -/
def conformalContactLiftDiffeomorph (A : (V × V) ≃L[ℝ] V × V) (hc : c ≠ 0) :
    (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ) where
  toFun := conformalContactLift A c
  invFun := conformalContactLift (A.symm : V × V →L[ℝ] V × V) c⁻¹
  left_inv x := by
    rw [← Function.comp_apply (f := conformalContactLift _ c⁻¹), conformalContactLift_comp]
    simp [inv_mul_cancel₀ hc]
  right_inv x := by
    rw [← Function.comp_apply (f := conformalContactLift _ c), conformalContactLift_comp]
    simp [mul_inv_cancel₀ hc]
  contMDiff_toFun := (contDiff_conformalContactLift _ _).contMDiff
  contMDiff_invFun := (contDiff_conformalContactLift _ _).contMDiff

/-- The diffeomorphism `TauCeti.conformalContactLiftDiffeomorph A hc` is the contact lift of
`A`. -/
@[simp]
theorem coe_conformalContactLiftDiffeomorph (A : (V × V) ≃L[ℝ] V × V) (hc : c ≠ 0) :
    ⇑(conformalContactLiftDiffeomorph A hc) = conformalContactLift (A : V × V →L[ℝ] V × V) c :=
  (rfl)

/-- The inverse of `TauCeti.conformalContactLiftDiffeomorph A hc` is the contact lift of `A⁻¹`
with multiplier `c⁻¹`. -/
@[simp]
theorem coe_conformalContactLiftDiffeomorph_symm (A : (V × V) ≃L[ℝ] V × V) (hc : c ≠ 0) :
    ⇑(conformalContactLiftDiffeomorph A hc).symm =
      conformalContactLift (A.symm : V × V →L[ℝ] V × V) c⁻¹ :=
  (rfl)

/-- The contact lift of a conformally symplectic linear equivalence with multiplier `c ≠ 0` pulls
the standard contact form back to `c` times itself. -/
theorem mpullback_conformalContactLiftDiffeomorph (A : (V × V) ≃L[ℝ] V × V) (hc : c ≠ 0)
    (hA : ∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) :
    SmoothForm.mpullback (conformalContactLiftDiffeomorph A hc)
        (conformalContactLiftDiffeomorph A hc).contMDiff (innerProductContactForm V) =
      c • innerProductContactForm V := by
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, coe_conformalContactLiftDiffeomorph]
  exact mpullback_conformalContactLift_innerProductContactForm hA

/-- The contact lift of a conformally symplectic linear equivalence with multiplier `c ≠ 0` is a
contactomorphism of the standard contact structure. -/
theorem isContactomorphism_conformalContactLiftDiffeomorph (A : (V × V) ≃L[ℝ] V × V)
    (hc : c ≠ 0) (hA : ∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) :
    (conformalContactLiftDiffeomorph A hc).IsContactomorphism (innerProductContactForm V)
      (innerProductContactForm V) := by
  rw [Diffeomorph.isContactomorphism_def, mpullback_conformalContactLiftDiffeomorph A hc hA]
  exact SmoothForm.kerDistribution_smul hc

end TauCeti
