/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Shear diffeotopies of a cylinder

For a positive period `p`, the cylinder `ℝ × AddCircle p` has coordinates `(r, θ)`, a real
coordinate `r` and an angle `θ`, and its tangent spaces are `ℝ × ℝ`. A smooth function
`g : ℝ → ℝ`, given as a bundled smooth map, turns each circle `{r} × AddCircle p` by the angle
`[g r]`. Doing this gradually gives the **shear diffeotopy**

`φ_t (r, θ) = (r, θ + [t g(r)])`,  `t ∈ [0, 1]`

(`TauCeti.cylinderShearDiffeotopy p g`), which starts at the identity. Every map `φ_t` is the
identity on the circles over the zeros of `g`; so when `g` has compact support, the whole motion
is the identity outside the compact band `tsupport g × AddCircle p`
(`TauCeti.cylinderShearDiffeotopy_eqOn_compl`,
`TauCeti.cylinderShearDiffeotopy_eqOn_compl_tsupport`).

The motion `((r, θ), t) ↦ φ_t (r, θ)` has derivative

`(w, τ) ↦ (w₁, w₂ + t g'(r) w₁ + τ' g(r))`,

where `τ'` is the image of the time vector `τ` under the derivative of the inclusion
`[0, 1] → ℝ`: its derivative is the sum of the derivative of the time `t` map, the shear by
`t g` (`TauCeti.mfderiv_cylinderShear_apply`), and the velocity of the time slice. So the
velocity of the shear is the vertical vector `(0, g r)` at every time
(`TauCeti.mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_one`), and its spatial derivative
`w ↦ (w₁, w₂ + t g'(r) w₁)` (`TauCeti.mfderiv_cylinderMap_cylinderShearDiffeotopy_space`) is
a unipotent shear matrix, which preserves the area form `dr ∧ dθ`. These are the inputs for
computing the flux of the shear. The derivative computation follows the torus translation
diffeotopy `TauCeti.torusTranslationDiffeotopy`.

## Main definitions

* `TauCeti.cylinderShearDiffeotopy p g`: the diffeotopy `t ↦ ((r, θ) ↦ (r, θ + [t g(r)]))`.

## Main results

* `TauCeti.cylinderShearDiffeotopy_eqOn_compl`: if `g` vanishes outside a set `A`, the motion
  is the identity outside `A × AddCircle p`; `TauCeti.cylinderShearDiffeotopy_eqOn_compl_tsupport`
  is the case `A = tsupport g`.
* `TauCeti.hasMFDerivAt_cylinderShear`, `TauCeti.mfderiv_cylinderShear_apply`: the derivative of
  the shear `(r, θ) ↦ (r, θ + [h r])`.
* `TauCeti.mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_one`,
  `TauCeti.mfderiv_cylinderMap_cylinderShearDiffeotopy_space`: the velocity and the spatial
  derivative of the motion of the shear diffeotopy.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism on open manifolds).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-! ### The shear of the cylinder by a function -/

/-- The shear `(r, θ) ↦ (r, θ + [h r])` of the cylinder by a `C^n` function `h` is `C^n`. -/
theorem contMDiff_cylinderShear {n : ℕ∞} {h : ℝ → ℝ} (hh : ContDiff ℝ n h) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n
      fun y : ℝ × AddCircle p ↦ (y.1, y.2 + (h y.1 : AddCircle p)) :=
  contMDiff_fst.prodMk (contMDiff_snd.add
    ((AddCircle.contMDiff_coe p n).comp (hh.contMDiff.comp contMDiff_fst)))

/-- **The derivative of a shear of the cylinder.** For a function `h` differentiable at `r`, the
shear `(r, θ) ↦ (r, θ + [h r])` of `ℝ × AddCircle p` has derivative
`(w₁, w₂) ↦ (w₁, w₂ + h'(r) w₁)` at `(r, θ)`. -/
theorem hasMFDerivAt_cylinderShear {h : ℝ → ℝ} (y : ℝ × AddCircle p)
    (hh : DifferentiableAt ℝ h y.1) :
    HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun y : ℝ × AddCircle p ↦ (y.1, y.2 + (h y.1 : AddCircle p))) y
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ + deriv h y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) := by
  -- The angle component is the sum `θ + [h r]`, differentiable at `y` as a composite of smooth
  -- addition on the circle with a map differentiable at `y`.
  have h₂ : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun y : ℝ × AddCircle p ↦ y.2 + (h y.1 : AddCircle p)) y :=
    ((contMDiff_add 𝓘(ℝ) 1).mdifferentiableAt one_ne_zero).comp y
      (mdifferentiableAt_snd.prodMk (((AddCircle.contMDiff_coe p 1).mdifferentiableAt
        one_ne_zero).comp y (hh.mdifferentiableAt.comp y mdifferentiableAt_fst)))
  refine (hasMFDerivAt_fst y).prodMk (h₂.hasMFDerivAt.congr_mfderiv
    (ContinuousLinearMap.ext fun w ↦ ?_))
  rw [mfderiv_prod_eq_add_apply h₂]
  -- In `r` the angle moves with velocity `h'(r)`; in `θ` the map is a translation of the circle.
  have hr := (AddCircle.hasMFDerivAt_add_coe_comp hh.hasDerivAt y.2).mfderiv
  simp only [hr, AddCircle.mfderiv_add_right]
  -- The tangent spaces are type synonyms of `ℝ`, on which both sides are real expressions in
  -- `w₁` and `w₂`; the linear maps unfold to multiplication by `h'(r)` and the identity.
  change w.1 * deriv h y.1 + w.2 = w.2 + deriv h y.1 * w.1
  ring

/-- **The derivative of a shear of the cylinder**, evaluated: for a function `h` differentiable
at `r`, the shear `(r, θ) ↦ (r, θ + [h r])` sends the tangent vector `(w₁, w₂)` at `(r, θ)` to
`(w₁, w₂ + h'(r) w₁)`. -/
theorem mfderiv_cylinderShear_apply {h : ℝ → ℝ} (y : ℝ × AddCircle p)
    (hh : DifferentiableAt ℝ h y.1) (w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
        (fun y : ℝ × AddCircle p ↦ (y.1, y.2 + (h y.1 : AddCircle p))) y w =
      (w.1, w.2 + deriv h y.1 * w.1) := by
  rw [(hasMFDerivAt_cylinderShear p y hh).mfderiv]
  -- The tangent spaces are type synonyms of `ℝ × ℝ`, so `simp` cannot see the linear map as a map
  -- of `ℝ × ℝ`; by definition its components are `w₁` and `w₂ + h'(r) • w₁ = w₂ + h'(r) * w₁`.
  rfl

/-! ### The shear diffeotopy -/

variable (g : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯)

/-- The motion `(t, (r, θ)) ↦ (r, θ + [t g(r)])` of `[0, 1] × (ℝ × AddCircle p)` is smooth. -/
private theorem contMDiff_shearMotion {g : ℝ → ℝ} (hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ g) :
    ContMDiff ((𝓡∂ 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      fun q : unitInterval × (ℝ × AddCircle p) ↦
        (q.2.1, q.2.2 + (((q.1 : ℝ) * g q.2.1 : ℝ) : AddCircle p)) :=
  (contMDiff_fst.comp contMDiff_snd).prodMk ((contMDiff_snd.comp contMDiff_snd).add
    ((AddCircle.contMDiff_coe p ∞).comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).smul
      (hg.comp (contMDiff_fst.comp contMDiff_snd)))))

/-- The **shear diffeotopy** of the cylinder `ℝ × AddCircle p` along a smooth function
`g : ℝ → ℝ`: at time `t ∈ [0, 1]` it turns the circle over `r` by the angle `[t g(r)]`,
`(r, θ) ↦ (r, θ + [t g(r)])`. -/
def cylinderShearDiffeotopy :
    Diffeotopy (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (ℝ × AddCircle p) where
  toDiffeomorph :=
    { toFun := fun q ↦ (q.1, (q.2.1, q.2.2 + (((q.1 : ℝ) * g q.2.1 : ℝ) : AddCircle p)))
      invFun := fun q ↦ (q.1, (q.2.1, q.2.2 + (((q.1 : ℝ) * -g q.2.1 : ℝ) : AddCircle p)))
      left_inv := fun q ↦ by
        refine Prod.ext rfl (Prod.ext rfl ?_)
        simp only [mul_neg, AddCircle.coe_neg, add_neg_cancel_right]
      right_inv := fun q ↦ by
        refine Prod.ext rfl (Prod.ext rfl ?_)
        simp only [mul_neg, AddCircle.coe_neg, neg_add_cancel_right]
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_shearMotion p g.contMDiff)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_shearMotion p g.contMDiff.neg) }
  fst_apply _ := rfl
  snd_apply_zero' x := Prod.ext rfl ((congrArg (x.2 + ·)
    (by simp : ((((0 : unitInterval) : ℝ) * g x.1 : ℝ) : AddCircle p) = 0)).trans (add_zero _))

/-- At time `t`, the shear diffeotopy turns the circle over `r` by the angle `[t g(r)]`. -/
@[simp]
theorem cylinderShearDiffeotopy_apply (q : unitInterval × (ℝ × AddCircle p)) :
    cylinderShearDiffeotopy p g q =
      (q.2.1, q.2.2 + (((q.1 : ℝ) * g q.2.1 : ℝ) : AddCircle p)) :=
  (rfl)

/-- The shear diffeotopy fixes every point over a zero of `g` throughout the motion. -/
theorem cylinderShearDiffeotopy_apply_of_eq_zero {y : ℝ × AddCircle p} (hy : g y.1 = 0)
    (t : unitInterval) : cylinderShearDiffeotopy p g (t, y) = y :=
  Prod.ext rfl (by simp [hy])

/-- **Support of the shear diffeotopy.** If `g` vanishes outside a set `A`, every map of the shear
diffeotopy is the identity outside the band `A × AddCircle p`. -/
theorem cylinderShearDiffeotopy_eqOn_compl {A : Set ℝ} (hA : ∀ r ∉ A, g r = 0)
    (t : unitInterval) :
    EqOn (fun y ↦ cylinderShearDiffeotopy p g (t, y)) id (A ×ˢ (univ : Set (AddCircle p)))ᶜ :=
  fun y hy ↦ cylinderShearDiffeotopy_apply_of_eq_zero p g
    (hA y.1 fun h ↦ hy ⟨h, mem_univ _⟩) t

/-- The shear by a compactly supported `g` is the identity outside the compact band
`tsupport g × AddCircle p`. -/
theorem cylinderShearDiffeotopy_eqOn_compl_tsupport (t : unitInterval) :
    EqOn (fun y ↦ cylinderShearDiffeotopy p g (t, y)) id
      (tsupport g ×ˢ (univ : Set (AddCircle p)))ᶜ :=
  cylinderShearDiffeotopy_eqOn_compl p g (fun _ hr ↦ image_eq_zero_of_notMem_tsupport hr) t

/-- The final diffeomorphism of the shear diffeotopy turns the circle over `r` by `[g(r)]`. -/
theorem final_cylinderShearDiffeotopy_apply (y : ℝ × AddCircle p) :
    (cylinderShearDiffeotopy p g).final y = (y.1, y.2 + (g y.1 : AddCircle p)) := by
  simp

/-- The final diffeomorphism of the shear diffeotopy is the shear `(r, θ) ↦ (r, θ + [g(r)])`. -/
theorem coe_final_cylinderShearDiffeotopy :
    ⇑(cylinderShearDiffeotopy p g).final =
      fun y : ℝ × AddCircle p ↦ (y.1, y.2 + (g y.1 : AddCircle p)) :=
  funext (final_cylinderShearDiffeotopy_apply p g)

/-- Through a fixed point `(r, θ)`, the motion `s ↦ (r, θ + [s g(r)])` has velocity `(0, g r)` at
every time, read through the derivative of the inclusion `[0, 1] → ℝ`. -/
private theorem hasMFDerivAt_shearMotion_time (y : ℝ × AddCircle p) (t : unitInterval) :
    HasMFDerivAt (𝓡∂ 1) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun s : unitInterval ↦ (y.1, y.2 + (((s : ℝ) * g y.1 : ℝ) : AddCircle p))) t
      ((0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).prod
        (((1 : ℝ →L[ℝ] ℝ).smulRight (g y.1)).comp
          (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t))) := by
  have hval : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t) :=
    (contMDiff_subtypeVal_Icc.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt
  exact (hasMFDerivAt_const y.1 t).prodMk
    ((AddCircle.hasMFDerivAt_add_coe_comp (hasDerivAt_mul_const (g y.1)) y.2).comp t hval)

/-- The derivative of the motion of a shear diffeotopy is the sum of the derivative of its time
`t` slice, the shear by `t g`, and of the velocity of the time slice through `(r, θ)`. -/
private theorem mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_eq_add (y : ℝ × AddCircle p)
    (t : unitInterval) (w : ℝ × ℝ) (τ : TangentSpace (𝓡∂ 1) t) :
    mfderiv ((𝓘(ℝ).prod 𝓘(ℝ)).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ))
        (cylinderShearDiffeotopy p g).cylinderMap (y, t) (w, τ) =
      mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
          (fun z : ℝ × AddCircle p ↦ (z.1, z.2 + (((t : ℝ) * g z.1 : ℝ) : AddCircle p))) y w +
        mfderiv (𝓡∂ 1) (𝓘(ℝ).prod 𝓘(ℝ))
          (fun s : unitInterval ↦ (y.1, y.2 + (((s : ℝ) * g y.1 : ℝ) : AddCircle p))) t τ := by
  have hcyl : (cylinderShearDiffeotopy p g).cylinderMap =
      fun q ↦ (q.1.1, q.1.2 + (((q.2 : ℝ) * g q.1.1 : ℝ) : AddCircle p)) :=
    funext fun q ↦ Diffeotopy.cylinderMap_apply _ q
  have hd : MDifferentiableAt ((𝓘(ℝ).prod 𝓘(ℝ)).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun q : (ℝ × AddCircle p) × unitInterval ↦
        (q.1.1, q.1.2 + (((q.2 : ℝ) * g q.1.1 : ℝ) : AddCircle p))) (y, t) :=
    ((contMDiff_shearMotion p g.contMDiff).comp
      (contMDiff_snd.prodMk contMDiff_fst)).mdifferentiableAt
      (by simp)
  rw [hcyl]
  exact mfderiv_prod_eq_add_apply hd

/-- **The velocity of a shear diffeotopy.** On the unit time vector of `[0, 1]`, the derivative of
the motion `((r, θ), t) ↦ (r, θ + [t g(r)])` is the vertical vector `(0, g r)`, at every time. -/
@[simp]
theorem mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_one (y : ℝ × AddCircle p)
    (t : unitInterval) :
    mfderiv ((𝓘(ℝ).prod 𝓘(ℝ)).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ))
        (cylinderShearDiffeotopy p g).cylinderMap (y, t)
        ((0 : ℝ × ℝ), (1 : TangentSpace (𝓡∂ 1) t)) = (0, g y.1) := by
  have hA : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun z : ℝ × AddCircle p ↦ (z.1, z.2 + (((t : ℝ) * g z.1 : ℝ) : AddCircle p))) y
      (0 : ℝ × ℝ) = (0 : ℝ × ℝ) := map_zero _
  rw [mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_eq_add, hA,
    (hasMFDerivAt_shearMotion_time p g y t).mfderiv]
  -- The time component is `τ' g(r)` for the image `τ' = 1` of the unit time vector; the sums and
  -- linear maps are computed in the type synonyms `ℝ × ℝ` and `ℝ` of the tangent spaces.
  refine (zero_add _).trans (Prod.ext rfl ?_)
  exact (congrArg (fun a : ℝ ↦ a * g y.1) (mfderiv_subtypeVal_Icc_one t)).trans (one_mul _)

/-- **The spatial derivative of a shear diffeotopy.** On spatial tangent vectors, the derivative of
the motion of the shear diffeotopy at time `t` is the shear `w ↦ (w₁, w₂ + t g'(r) w₁)`. -/
@[simp]
theorem mfderiv_cylinderMap_cylinderShearDiffeotopy_space (y : ℝ × AddCircle p)
    (t : unitInterval) (w : ℝ × ℝ) :
    mfderiv ((𝓘(ℝ).prod 𝓘(ℝ)).prod (𝓡∂ 1)) (𝓘(ℝ).prod 𝓘(ℝ))
        (cylinderShearDiffeotopy p g).cylinderMap (y, t)
        (w, (0 : EuclideanSpace ℝ (Fin 1))) = (w.1, w.2 + (t : ℝ) * deriv g y.1 * w.1) := by
  have hB : mfderiv (𝓡∂ 1) (𝓘(ℝ).prod 𝓘(ℝ))
      (fun s : unitInterval ↦ (y.1, y.2 + (((s : ℝ) * g y.1 : ℝ) : AddCircle p))) t
      (0 : TangentSpace (𝓡∂ 1) t) = (0 : ℝ × ℝ) := map_zero _
  refine (mfderiv_cylinderMap_cylinderShearDiffeotopy_apply_eq_add p g y t w 0).trans ?_
  rw [hB]
  refine (add_zero _).trans ((mfderiv_cylinderShear_apply p y
    (((g.contMDiff.contDiff.differentiable (by simp)) y.1).const_mul _) w).trans ?_)
  rw [deriv_const_mul _ ((g.contMDiff.contDiff.differentiable (by simp)) y.1)]

end TauCeti
