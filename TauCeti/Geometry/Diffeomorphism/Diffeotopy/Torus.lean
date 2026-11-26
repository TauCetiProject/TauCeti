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
# Translation and shear diffeotopies of a torus

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

A real vector `v` with `v i = 0` and a smooth function `g` on the `i`-th circle give the shear
flow

`φ_t (x) = x + [t g(x i) v]`,  `t ∈ [0, 1]`

(`TauCeti.torusShearDiffeotopy p v hv g`), which translates each level set of the `i`-th coordinate
along `v` and leaves that coordinate unchanged. On the two-torus with `i = 0` and `v = (0, 1)` it
is the shear `(x, y) ↦ (x, y + [t g(x)])`. Its motion has derivative
`(w, τ) ↦ w + (t g'(x i) w i + g(x i) τ') • v`
(`TauCeti.mfderiv_cylinderMap_torusShearDiffeotopy_apply`): its velocity is `g(x i) • v` and its
spatial derivative is the shear `w ↦ w + (t g'(x i) w i) • v`.

## Main definitions

* `TauCeti.torusTranslationDiffeotopy p v`: the diffeotopy `t ↦ (x ↦ x + [t v])` of the torus.
* `TauCeti.torusShearDiffeotopy p v hv g`: the diffeotopy `t ↦ (x ↦ x + [t g(x i) v])` of the
  torus.

## Main results

* `TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`: the translation diffeotopy is a loop
  exactly when `v` lies in the period lattice.
* `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply`: the derivative of its motion;
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one` and
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl` are its velocity `v` and its
  identity spatial derivative.
* `TauCeti.mfderiv_cylinderMap_torusShearDiffeotopy_apply`: the derivative of the motion of a
  shear; `TauCeti.mfderiv_cylinderMap_torusShearDiffeotopy_apply_one` and
  `TauCeti.mfderiv_cylinderMap_torusShearDiffeotopy_space` are its velocity and its spatial
  derivative.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (translations and shears of the torus as symplectic
  isotopies).
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

omit [Fintype ι] [∀ i, Fact (0 < p i)] in
/-- Translating by `[s (-v)]` undoes translating by `[s v]`. -/
private theorem shift_neg (s : ℝ) : shift p (-v) s = -shift p v s :=
  funext fun k ↦ by simp [shift]

/-- The map `(x, s) ↦ x + [s v]` of `Tⁿ × ℝ` is smooth. -/
private theorem contMDiff_add_shift_prod :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      fun y : (∀ i, AddCircle (p i)) × ℝ ↦ y.1 + shift p v y.2 :=
  contMDiff_pi_iff.2 fun _ ↦ (contMDiff_apply.comp contMDiff_fst).add
    (contMDiff_apply.comp ((contMDiff_shift p v).comp contMDiff_snd))

/-- Through a fixed point `x`, the curve `s ↦ x + [s v]` of the torus, for real `s`, has
velocity `v`. -/
private theorem hasMFDerivAt_add_shift_real (x : ∀ i, AddCircle (p i)) (s : ℝ) :
    HasMFDerivAt 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun s : ℝ ↦ x + shift p v s) s (ContinuousLinearMap.toSpanSingleton ℝ v) := by
  have h (i : ι) : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ ↦ (x + shift p v s) i) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v i)) :=
    AddCircle.hasMFDerivAt_add_coe_comp (hasDerivAt_mul_const (v i)) (x i)
  refine (TauCeti.hasMFDerivAt_pi h).congr_mfderiv ?_
  -- Both sides send `1` to `v`.
  ext i
  exact (one_smul ℝ (v i)).trans (one_smul ℝ (v i)).symm

/-- The map `(x, s) ↦ x + [s v]` of `Tⁿ × ℝ` has derivative `(w, σ) ↦ w + σ • v`. -/
private theorem hasMFDerivAt_add_shift_prod (y : (∀ i, AddCircle (p i)) × ℝ) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ y.1 + shift p v y.2) y
      (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ +
        (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ)) := by
  have hd := (contMDiff_add_shift_prod (n := 1) p v).mdifferentiableAt one_ne_zero (x := y)
  refine hd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext fun w ↦ ?_)
  rw [mfderiv_prod_eq_add_apply hd]
  -- In `x` the map is a translation, and in `s` the curve `s ↦ x + [s v]` of velocity `v`.
  dsimp only
  rw [AddCircle.mfderiv_pi_add_right, (hasMFDerivAt_add_shift_real p v y.1 y.2).mfderiv]
  -- Both sides are `w.1 + w.2 • v`. The tangent spaces at `y.1` and `y.2` are type synonyms of
  -- `ι → ℝ` and `ℝ`, so the evaluation lemmas for `+`, `id` and `comp` of continuous linear maps
  -- match the two sides only up to unfolding them, which `rfl` does and `rw` and `simp` do not.
  rfl

/-- The motion `(t, x) ↦ x + [t v]` of `[0, 1] × Tⁿ` is smooth in both variables. -/
private theorem contMDiff_add_shift :
    ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      fun q : unitInterval × ∀ i, AddCircle (p i) ↦ q.2 + shift p v q.1 :=
  (contMDiff_add_shift_prod p v).comp (contMDiff_snd.prodMk
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst))

/-- The **translation diffeotopy** of the torus `Tⁿ = ∀ i, AddCircle (p i)` along a real vector
`v : ι → ℝ`: at time `t ∈ [0, 1]` it is the translation `x ↦ x + [t v]` by the image of `t v`
under the covering map `(ι → ℝ) → Tⁿ`. -/
def torusTranslationDiffeotopy :
    Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (∀ i, AddCircle (p i)) where
  toDiffeomorph :=
    { toFun := fun q ↦ (q.1, q.2 + shift p v q.1)
      invFun := fun q ↦ (q.1, q.2 + shift p (-v) q.1)
      left_inv := fun q ↦ Prod.ext rfl (by simp only [shift_neg, add_neg_cancel_right])
      right_inv := fun q ↦ Prod.ext rfl (by simp only [shift_neg, neg_add_cancel_right])
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
  -- The motion is `(x, s) ↦ x + [s v]` after `(x, t) ↦ (x, t)`, whatever the smoothness exponent
  -- of the diffeotopy.
  have hcyl : (torusTranslationDiffeotopy (n := n) p v).cylinderMap =
      (fun y : (∀ i, AddCircle (p i)) × ℝ ↦ y.1 + shift p v y.2) ∘
        fun q : (∀ i, AddCircle (p i)) × unitInterval ↦ (q.1, (q.2 : ℝ)) :=
    funext fun q ↦ Diffeotopy.cylinderMap_apply _ q
  have hval : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t) :=
    (contMDiff_subtypeVal_Icc.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt
  have hΨ := (hasMFDerivAt_add_shift_prod p v (x, (t : ℝ))).comp (x, t)
    ((hasMFDerivAt_fst (x, t)).prodMk (hval.comp (x, t) (hasMFDerivAt_snd (x, t))))
  rw [hcyl]
  -- Both sides are `w + τ' • v`. The tangent spaces are type synonyms of the model spaces, so the
  -- evaluation lemmas of `simp` for `comp`, `prod`, `fst` and `snd` do not fire on the composite;
  -- `exact` matches it with the goal by unfolding the synonyms.
  exact DFunLike.congr_fun hΨ.mfderiv (w, τ)

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

/-! ### Shear diffeotopies -/

section Shear

variable {v} {i : ι}

omit [Fintype ι] [∀ i, Fact (0 < p i)] in
/-- Translating by `[s v]` does not move the `i`-th coordinate when `v i = 0`. -/
private theorem add_shift_apply_of_eq_zero (hv : v i = 0) (x : ∀ k, AddCircle (p k)) (s : ℝ) :
    (x + shift p v s) i = x i := by
  simp [shift, hv]

/-- The motion `(t, x) ↦ x + [t g(x i) v]` of `[0, 1] × Tⁿ` is smooth. -/
private theorem contMDiff_shearMotion (g : C^∞⟮𝓘(ℝ), AddCircle (p i); ℝ⟯) (w : ι → ℝ) :
    ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      fun q : unitInterval × ∀ k, AddCircle (p k) ↦ q.2 + shift p w ((q.1 : ℝ) * g (q.2 i)) :=
  (contMDiff_add_shift_prod p w).comp (contMDiff_snd.prodMk
    ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).smul
      (g.contMDiff.comp (contMDiff_apply.comp contMDiff_snd))))

variable (v) in
/-- The **shear diffeotopy** of the torus `Tⁿ = ∀ k, AddCircle (p k)` along a real vector `v` with
`v i = 0`, by a smooth function `g` of the `i`-th coordinate: at time `t ∈ [0, 1]` it is the shear
`x ↦ x + [t g(x i) v]`, which translates each level set of the `i`-th coordinate along `v`. -/
def torusShearDiffeotopy (hv : v i = 0) (g : C^∞⟮𝓘(ℝ), AddCircle (p i); ℝ⟯) :
    Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (∀ k, AddCircle (p k)) where
  toDiffeomorph :=
    { toFun := fun q ↦ (q.1, q.2 + shift p v ((q.1 : ℝ) * g (q.2 i)))
      invFun := fun q ↦ (q.1, q.2 + shift p (-v) ((q.1 : ℝ) * g (q.2 i)))
      left_inv := fun q ↦ Prod.ext rfl (by
        simp only [add_shift_apply_of_eq_zero p hv, shift_neg, add_neg_cancel_right])
      right_inv := fun q ↦ Prod.ext rfl (by
        simp only [add_shift_apply_of_eq_zero p (v := -v) (show (-v) i = 0 by simp [hv])]
        rw [shift_neg, neg_add_cancel_right])
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_shearMotion p g v)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_shearMotion p g (-v)) }
  fst_apply _ := rfl
  snd_apply_zero' x := (congrArg (x + ·) (funext fun k ↦ by simp [shift])).trans (add_zero x)

variable (hv : v i = 0) (g : C^∞⟮𝓘(ℝ), AddCircle (p i); ℝ⟯)

/-- At time `t`, the shear diffeotopy is the shear `x ↦ x + [t g(x i) v]`. -/
@[simp]
theorem torusShearDiffeotopy_apply (q : unitInterval × ∀ k, AddCircle (p k)) :
    torusShearDiffeotopy p v hv g q =
      q.2 + fun k ↦ (((q.1 : ℝ) * g (q.2 i) * v k : ℝ) : AddCircle (p k)) :=
  (rfl)

/-- The shear diffeotopy does not move the `i`-th coordinate. -/
theorem torusShearDiffeotopy_apply_self (q : unitInterval × ∀ k, AddCircle (p k)) :
    torusShearDiffeotopy p v hv g q i = q.2 i :=
  add_shift_apply_of_eq_zero p hv q.2 _

/-- The final diffeomorphism of the shear diffeotopy is the shear `x ↦ x + [g(x i) v]`. -/
theorem final_torusShearDiffeotopy_apply (x : ∀ k, AddCircle (p k)) :
    (torusShearDiffeotopy p v hv g).final x =
      x + fun k ↦ ((g (x i) * v k : ℝ) : AddCircle (p k)) := by
  simp

/-- **The derivative of the motion of a shear diffeotopy.** The motion `(x, t) ↦ x + [t g(x i) v]`
of the torus has derivative `(w, τ) ↦ w + (t g'(x i) w i + g(x i) τ') • v`, where `g'(x i)` is the
derivative of `g` and `τ'` is the image of the time vector `τ` under the derivative of the
inclusion `[0, 1] → ℝ`. -/
theorem mfderiv_cylinderMap_torusShearDiffeotopy_apply (x : ∀ k, AddCircle (p k))
    (t : unitInterval) (w : ι → ℝ) (τ : TangentSpace (𝓡∂ 1) t) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusShearDiffeotopy p v hv g).cylinderMap (x, t) (w, τ) =
      w + ((t : ℝ) * mvfderiv 𝓘(ℝ) g (x i) (w i) +
        g (x i) * mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) t τ) • v := by
  -- The motion is `(x, s) ↦ x + [s v]` after `(x, t) ↦ (x, t g(x i))`.
  have hcyl : (torusShearDiffeotopy p v hv g).cylinderMap =
      (fun y : (∀ k, AddCircle (p k)) × ℝ ↦ y.1 + shift p v y.2) ∘
        fun q : (∀ k, AddCircle (p k)) × unitInterval ↦ (q.1, (q.2 : ℝ) * g (q.1 i)) :=
    funext fun q ↦ Diffeotopy.cylinderMap_apply _ q
  have hval : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) t) :=
    (contMDiff_subtypeVal_Icc.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt
  have hg : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) g (x i) (mfderiv 𝓘(ℝ) 𝓘(ℝ) g (x i)) :=
    (g.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have happ := TauCeti.hasMFDerivAt_apply (I := fun _ : ι ↦ 𝓘(ℝ)) (M := fun k ↦ AddCircle (p k)) i x
  have hmul := (hval.comp (x, t) (hasMFDerivAt_snd (x, t))).mul
    ((hg.comp x happ).comp (x, t) (hasMFDerivAt_fst (x, t)))
  have hΨ := (hasMFDerivAt_add_shift_prod p v (x, (t : ℝ) * g (x i))).comp (x, t)
    ((hasMFDerivAt_fst (x, t)).prodMk hmul)
  rw [hcyl]
  -- The composite differs from that of `hΨ` only by unfolding the pointwise product.
  refine (DFunLike.congr_fun hΨ.mfderiv (w, τ)).trans ?_
  -- Both sides evaluate the same composite of continuous linear maps on `(w, τ)`.
  rfl

/-- **The velocity of a shear diffeotopy.** On the unit time vector of `[0, 1]`, the derivative of
the motion `(x, t) ↦ x + [t g(x i) v]` is `g(x i) • v`, at every time. -/
@[simp]
theorem mfderiv_cylinderMap_torusShearDiffeotopy_apply_one (x : ∀ k, AddCircle (p k))
    (t : unitInterval) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusShearDiffeotopy p v hv g).cylinderMap (x, t)
        ((0 : ι → ℝ), (1 : TangentSpace (𝓡∂ 1) t)) = g (x i) • v := by
  have h0 : mvfderiv 𝓘(ℝ) g (x i) ((0 : ι → ℝ) i) = 0 := map_zero (mvfderiv 𝓘(ℝ) g (x i))
  have h1 : mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) t 1 = 1 :=
    mfderiv_subtypeVal_Icc_one t
  rw [mfderiv_cylinderMap_torusShearDiffeotopy_apply, h0, h1, mul_zero, zero_add, mul_one,
    zero_add]

/-- **The spatial derivative of a shear diffeotopy.** On spatial tangent vectors, the derivative of
the motion of the shear diffeotopy at time `t` is the shear `w ↦ w + (t g'(x i) w i) • v`. -/
@[simp]
theorem mfderiv_cylinderMap_torusShearDiffeotopy_space (x : ∀ k, AddCircle (p k))
    (t : unitInterval) (w : ι → ℝ) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (torusShearDiffeotopy p v hv g).cylinderMap (x, t)
        (w, (0 : EuclideanSpace ℝ (Fin 1))) =
      w + ((t : ℝ) * mvfderiv 𝓘(ℝ) g (x i) (w i)) • v :=
  (mfderiv_cylinderMap_torusShearDiffeotopy_apply p hv g x t w 0).trans <| by
    rw [map_zero (mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) t), mul_zero, add_zero]

end Shear

end TauCeti
