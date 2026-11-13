/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Translation diffeotopies of a torus

For a finite family of positive periods `p i`, the torus `Tⁿ = ∀ i, AddCircle (p i)` is a smooth
manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)`, with tangent space `ι → ℝ` at every
point. A real vector `v : ι → ℝ` moves `Tⁿ` by the linear translation flow

`φ_t (x) = x + [t v]`,  `t ∈ [0, 1]`,

where `[t v]` is the image of `t v` under the covering map `(ι → ℝ) → Tⁿ`
(`TauCeti.torusTranslationDiffeotopy p v`). It starts at the identity, its final diffeomorphism is
translation by `[v]`, and it is a loop, that is its final diffeomorphism is the identity, exactly
when `v` lies in the period lattice: `v i ∈ p i ℤ` for every `i`
(`TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`).

Every translation of `Tⁿ` has derivative the identity of `ι → ℝ`
(`AddCircle.mfderiv_pi_add_right`). The motion `(x, t) ↦ x + [t v]` on `Tⁿ × [0, 1]` therefore
has derivative `(w, τ) ↦ w + τ' • v`, where `τ'` is the image of the time vector `τ` under the
derivative of the inclusion `[0, 1] → ℝ`
(`TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply`). On the unit time vector this is
the velocity `v`, at every time including the two ends, and on spatial vectors it is the identity.
These are the inputs for computing the flux of the translations of a torus.

## Main definitions

* `TauCeti.torusTranslationDiffeotopy p v`: the diffeotopy `t ↦ (x ↦ x + [t v])` of the torus.

## Main results

* `TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`: the translation diffeotopy is a loop
  exactly when `v` lies in the period lattice.
* `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply`: the derivative of its motion;
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one` and
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl` are its velocity `v` and its
  identity spatial derivative.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (translations of the torus as symplectic loops).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)] (v : ι → ℝ) {n : ℕ∞ω}

/-- The point `[s v]` of the torus, the image of `s v` under the covering map. -/
private def shift (s : ℝ) : ∀ i, AddCircle (p i) := fun i ↦ ((s * v i : ℝ) : AddCircle (p i))

/-- The curve `s ↦ [s v]` of the torus is smooth. -/
private theorem contMDiff_shift :
    ContMDiff 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (shift p v) :=
  contMDiff_pi_iff.2 fun i ↦
    (AddCircle.contMDiff_coe (p i) n).comp (contDiff_id.mul contDiff_const).contMDiff

/-- The motion `(t, x) ↦ x + [t v]` of `[0, 1] × Tⁿ` is smooth in both variables. -/
private theorem contMDiff_add_shift :
    ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      fun q : unitInterval × ∀ i, AddCircle (p i) ↦ q.2 + shift p v q.1 :=
  contMDiff_pi_iff.2 fun _ ↦ (contMDiff_apply.comp contMDiff_snd).add
    (contMDiff_apply.comp ((contMDiff_shift p v).comp
      (contMDiff_subtypeVal_Icc.comp contMDiff_fst)))

/-- The **translation diffeotopy** of the torus `Tⁿ = ∀ i, AddCircle (p i)` along a real vector
`v : ι → ℝ`: at time `t ∈ [0, 1]` it is the translation `x ↦ x + [t v]` by the image of `t v`
under the covering map `(ι → ℝ) → Tⁿ`. -/
def torusTranslationDiffeotopy :
    Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (∀ i, AddCircle (p i)) where
  toDiffeomorph :=
    { toFun := fun q ↦ (q.1, q.2 + shift p v q.1)
      invFun := fun q ↦ (q.1, q.2 + shift p (-v) q.1)
      left_inv := fun q ↦ by
        refine Prod.ext rfl (funext fun i ↦ ?_)
        simp only [shift, Pi.add_apply, Pi.neg_apply, mul_neg, AddCircle.coe_neg,
          add_neg_cancel_right]
      right_inv := fun q ↦ by
        refine Prod.ext rfl (funext fun i ↦ ?_)
        simp only [shift, Pi.add_apply, Pi.neg_apply, mul_neg, AddCircle.coe_neg,
          neg_add_cancel_right]
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_add_shift p v)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_add_shift p (-v)) }
  fst_apply _ := rfl
  snd_apply_zero' x := (congrArg (x + ·) (funext fun i ↦ by simp [shift])).trans (add_zero x)

/-- At time `t`, the translation diffeotopy is the translation `x ↦ x + [t v]`. -/
@[simp]
theorem torusTranslationDiffeotopy_apply (q : unitInterval × ∀ i, AddCircle (p i)) :
    torusTranslationDiffeotopy (n := n) p v q =
      q.2 + fun i ↦ (((q.1 : ℝ) * v i : ℝ) : AddCircle (p i)) :=
  (rfl)

/-- The final diffeomorphism of the translation diffeotopy is the translation by `[v]`. -/
theorem final_torusTranslationDiffeotopy_apply (x : ∀ i, AddCircle (p i)) :
    (torusTranslationDiffeotopy (n := n) p v).final x = x + fun i ↦ (v i : AddCircle (p i)) := by
  simp

/-- **Translation loops.** The translation diffeotopy along `v` is a loop, its final
diffeomorphism being the identity, exactly when `v` lies in the period lattice: every `v i` is an
integer multiple of `p i`. -/
theorem final_torusTranslationDiffeotopy_eq_refl_iff :
    (torusTranslationDiffeotopy (n := n) p v).final = Diffeomorph.refl _ _ n ↔
      ∀ i, v i ∈ AddSubgroup.zmultiples (p i) := by
  simp only [AddSubgroup.mem_zmultiples_iff, ← AddCircle.coe_eq_zero_iff]
  constructor
  · intro h i
    have h0 := congrArg (fun f ↦ f 0 i) h
    simpa [final_torusTranslationDiffeotopy_apply] using h0
  · intro h
    refine Diffeomorph.ext fun x ↦ funext fun i ↦ ?_
    simp [h i]

/-- Through a fixed point `x`, the motion `s ↦ x + [s v]` has velocity `v` at every time, read
through the derivative of the inclusion `[0, 1] → ℝ`. -/
private theorem hasMFDerivAt_add_shift_time (x : ∀ i, AddCircle (p i)) (t : unitInterval) :
    HasMFDerivAt (𝓡∂ 1) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun s : unitInterval ↦ x + shift p v s) t
      ((ContinuousLinearMap.toSpanSingleton ℝ v).comp
        (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t)) := by
  have hval : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t) :=
    (contMDiff_subtypeVal_Icc.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt
  have h (i : ι) : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (fun s : unitInterval ↦ (x + shift p v s) i) t
      (((1 : ℝ →L[ℝ] ℝ).smulRight (v i)).comp
        (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t)) :=
    (AddCircle.hasMFDerivAt_add_coe_comp (hasDerivAt_mul_const (v i)) (x i)).comp t hval
  refine (TauCeti.hasMFDerivAt_pi h).congr_mfderiv ?_
  -- Both sides send `τ` to `τ' • v`, for the image `τ'` of `τ` in the tangent line of `ℝ`.
  ext τ i
  have key (r : ℝ) :
      (1 : ℝ →L[ℝ] ℝ).smulRight (v i) r = ContinuousLinearMap.toSpanSingleton ℝ v r i := by
    simp
  -- The tangent spaces are type synonyms of `ℝ`, so `comp_apply` matches the goal only up to
  -- unfolding them, which `exact` does and `rw` and `simp` do not.
  exact key _

/-- **The derivative of the motion of a translation diffeotopy.** The motion
`(x, t) ↦ x + [t v]` of the torus has derivative `(w, τ) ↦ w + τ' • v`, where `τ'` is the image of
the time vector `τ` under the derivative of the inclusion `[0, 1] → ℝ`. -/
theorem mfderiv_cylinderMap_torusTranslationDiffeotopy_apply (x : ∀ i, AddCircle (p i))
    (t : unitInterval) (w : ι → ℝ) (τ : TangentSpace (𝓡∂ 1) t) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusTranslationDiffeotopy (n := n) p v).cylinderMap (x, t) (w, τ) =
      w + ContinuousLinearMap.toSpanSingleton ℝ v
        (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t τ) := by
  -- The motion is `(x, t) ↦ x + [t v]`, whatever the smoothness exponent of the diffeotopy.
  have hcyl : (torusTranslationDiffeotopy (n := n) p v).cylinderMap =
      fun q ↦ q.1 + shift p v q.2 :=
    funext fun q ↦ Diffeotopy.cylinderMap_apply _ q
  have hd : MDifferentiableAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun q ↦ q.1 + shift p v q.2) (x, t) :=
    ((contMDiff_add_shift (n := 1) p v).comp
      (contMDiff_snd.prodMk contMDiff_fst)).mdifferentiableAt one_ne_zero
  rw [hcyl]
  refine (mfderiv_prod_eq_add_apply hd).trans ?_
  -- The spatial slice is a translation and the time slice has velocity `v`.
  dsimp only
  rw [AddCircle.mfderiv_pi_add_right, (hasMFDerivAt_add_shift_time p v x t).mfderiv]
  -- The tangent spaces are type synonyms of `ι → ℝ`, so `id_apply` and `comp_apply` match the goal
  -- only up to unfolding them, which `exact` does and `rw` does not.
  exact congrArg₂ (· + ·) (ContinuousLinearMap.id_apply (R₁ := ℝ) w)
    (ContinuousLinearMap.comp_apply (ContinuousLinearMap.toSpanSingleton ℝ v)
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t) τ)

/-- **The velocity of a translation diffeotopy.** On the unit time vector of `[0, 1]`, the
derivative of the motion `(x, t) ↦ x + [t v]` is `v`: at every time, including the two ends, the
velocity of the translation diffeotopy is the constant vector `v`. -/
@[simp]
theorem mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one (x : ∀ i, AddCircle (p i))
    (t : unitInterval) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusTranslationDiffeotopy (n := n) p v).cylinderMap (x, t)
        ((0 : ι → ℝ), (1 : TangentSpace (𝓡∂ 1) t)) = v := by
  rw [mfderiv_cylinderMap_torusTranslationDiffeotopy_apply, mfderiv_subtypeVal_Icc_one]
  -- The unit tangent vector of `ℝ` is the real number `1`.
  exact (zero_add _).trans (ContinuousLinearMap.toSpanSingleton_apply_one ℝ v)

/-- **The spatial derivative of a translation diffeotopy.** Restricted to spatial tangent
vectors, the derivative of the motion `(x, t) ↦ x + [t v]` is the identity: every slice of the
translation diffeotopy is a translation. -/
@[simp]
theorem mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl (x : ∀ i, AddCircle (p i))
    (t : unitInterval) :
    (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusTranslationDiffeotopy (n := n) p v).cylinderMap (x, t) :
          (ι → ℝ) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ι → ℝ).comp
        (.inl ℝ (ι → ℝ) (EuclideanSpace ℝ (Fin 1))) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  ext w : 1
  refine (mfderiv_cylinderMap_torusTranslationDiffeotopy_apply p v x t w 0).trans ?_
  rw [map_zero]
  -- The tangent vector `0` of `ℝ` is the real number `0`.
  exact (congrArg (w + ·) (map_zero (ContinuousLinearMap.toSpanSingleton ℝ v))).trans (add_zero w)

end TauCeti
