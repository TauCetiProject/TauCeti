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
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Translation diffeotopies and displacements of a torus

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

Every diffeotopy `Φ` of `Tⁿ` is described by its **displacement**
`D : [0, 1] × Tⁿ → ι → ℝ` (`TauCeti.Diffeotopy.torusDisplacement`), the vector by which a point has
moved, measured in the universal cover: `Φ (t, x) = x + [D (t, x)]`. It is the continuous lift of
the motion `(t, x) ↦ Φ (t, x) - x` through the covering map `(ι → ℝ) → Tⁿ` which vanishes at time
`0`, and is unique as such (`TauCeti.Diffeotopy.eq_torusDisplacement_iff`); it is as smooth as `Φ`,
since the covering map is a local diffeomorphism. The translation along `v` has displacement
`t • v`. If `Φ` is a loop, then at time `1` every point has been displaced by one and the same
vector `v` of the period lattice, by connectedness of the torus
(`TauCeti.Diffeotopy.exists_torusDisplacement_one_eq`). The straight-line homotopy
`x + [(1 - s) D (t, x) + s t v]` then joins the motion of `Φ` to that of the translation loop along
`v`, fixing both time ends
(`TauCeti.Diffeotopy.exists_homotopy_cylinderMap_torusTranslationDiffeotopy`). So every loop of
diffeomorphisms of the torus is homotopic, with its ends fixed, to a translation loop; this is what
reduces the flux of an arbitrary loop to the flux of a translation.

## Main definitions

* `TauCeti.torusTranslationDiffeotopy p v`: the diffeotopy `t ↦ (x ↦ x + [t v])` of the torus.
* `TauCeti.Diffeotopy.torusDisplacement`: the displacement of a diffeotopy of the torus, lifted to
  the universal cover.

## Main results

* `TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`: the translation diffeotopy is a loop
  exactly when `v` lies in the period lattice.
* `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply`: the derivative of its motion;
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one` and
  `TauCeti.mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl` are its velocity `v` and its
  identity spatial derivative.
* `TauCeti.Diffeotopy.eq_torusDisplacement_iff`: the displacement is the unique continuous lift of
  `(t, x) ↦ Φ (t, x) - x` vanishing at time `0`.
* `TauCeti.Diffeotopy.contMDiff_torusDisplacement`: it is as smooth as the diffeotopy.
* `TauCeti.Diffeotopy.exists_torusDisplacement_one_eq`: the displacement of a loop at time `1` is a
  constant lattice vector.
* `TauCeti.Diffeotopy.exists_homotopy_cylinderMap_torusTranslationDiffeotopy`: a loop of the torus
  is homotopic, with both time ends fixed, to the translation loop along that vector.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (translations of the torus as symplectic loops).
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.30 (the
  homotopy lifting property of covering spaces).
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

/-! ### The displacement of a diffeotopy -/

namespace Diffeotopy

variable {p} (Φ : Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (∀ i, AddCircle (p i)))

/-- The **displacement** of a diffeotopy `Φ` of the torus `Tⁿ = ∀ i, AddCircle (p i)`: the vector
`D (t, x) : ι → ℝ` by which the point `x` has moved at time `t`, measured in the universal cover
`ι → ℝ`. It is the continuous lift, vanishing at time `0`, of the motion `(t, x) ↦ Φ (t, x) - x`
through the covering maps `ℝ → AddCircle (p i)` (`TauCeti.Diffeotopy.eq_torusDisplacement_iff`),
so that `Φ (t, x) = x + [D (t, x)]`. -/
def torusDisplacement (q : unitInterval × ∀ i, AddCircle (p i)) : ι → ℝ := fun i ↦
  (AddCircle.isCoveringMap_coe (p i)).liftHomotopy
    ⟨fun q ↦ Φ q i - q.2 i, ((continuous_apply i).comp Φ.contMDiff.continuous).sub
      ((continuous_apply i).comp continuous_snd)⟩
    (ContinuousMap.const _ 0) (fun x ↦ by simp [Φ.apply_zero]) q

/-- The displacement of a diffeotopy of the torus lifts the motion of each point relative to its
starting point. -/
@[simp]
theorem coe_torusDisplacement_apply (q : unitInterval × ∀ i, AddCircle (p i)) (i : ι) :
    (Φ.torusDisplacement q i : AddCircle (p i)) = Φ q i - q.2 i :=
  congrFun ((AddCircle.isCoveringMap_coe (p i)).liftHomotopy_lifts _ _ _) q

/-- A diffeotopy of the torus moves each point by its displacement: `Φ (t, x) = x + [D (t, x)]`. -/
theorem apply_eq_add_torusDisplacement (q : unitInterval × ∀ i, AddCircle (p i)) :
    Φ q = q.2 + fun i ↦ (Φ.torusDisplacement q i : AddCircle (p i)) :=
  funext fun i ↦ by simp

/-- The displacement of a diffeotopy of the torus vanishes at time `0`. -/
@[simp]
theorem torusDisplacement_zero (x : ∀ i, AddCircle (p i)) : Φ.torusDisplacement (0, x) = 0 :=
  funext fun i ↦ (AddCircle.isCoveringMap_coe (p i)).liftHomotopy_zero _ _ _ x

/-- The displacement of a diffeotopy of the torus is continuous. -/
@[fun_prop]
theorem continuous_torusDisplacement : Continuous Φ.torusDisplacement :=
  continuous_pi fun i ↦ ContinuousMap.continuous
    ((AddCircle.isCoveringMap_coe (p i)).liftHomotopy _ (ContinuousMap.const _ 0) _)

/-- **Characterization of the displacement.** The displacement of a diffeotopy `Φ` of the torus
is the unique continuous map `D` to `ι → ℝ` which lifts the motion `(t, x) ↦ Φ (t, x) - x` and
vanishes at time `0`. -/
theorem eq_torusDisplacement_iff {D : unitInterval × (∀ i, AddCircle (p i)) → ι → ℝ} :
    D = Φ.torusDisplacement ↔ Continuous D ∧
      (∀ q i, (D q i : AddCircle (p i)) = Φ q i - q.2 i) ∧ ∀ x, D (0, x) = 0 := by
  refine ⟨?_, fun ⟨hc, hl, h0⟩ ↦ funext fun q ↦ funext fun i ↦ ?_⟩
  · rintro rfl
    exact ⟨Φ.continuous_torusDisplacement, Φ.coe_torusDisplacement_apply, Φ.torusDisplacement_zero⟩
  · -- The `i`-th coordinates of `D` and of the displacement are continuous lifts of the same map
    -- on the connected space `[0, 1] × Tⁿ` which agree at `(0, 0)`, so they coincide.
    refine congrFun ((AddCircle.isCoveringMap_coe (p i)).eq_of_comp_eq
      ((continuous_apply i).comp hc) ((continuous_apply i).comp Φ.continuous_torusDisplacement)
      (funext fun q ↦ (hl q i).trans (Φ.coe_torusDisplacement_apply q i).symm) (0, 0) ?_) q
    exact (congrFun (h0 0) i).trans (congrFun (Φ.torusDisplacement_zero 0) i).symm

/-- The displacement of the translation diffeotopy along `v` is `t • v` at time `t`. -/
@[simp]
theorem torusDisplacement_torusTranslationDiffeotopy (q : unitInterval × ∀ i, AddCircle (p i)) :
    (torusTranslationDiffeotopy (n := n) p v).torusDisplacement q = (q.1 : ℝ) • v := by
  refine (congrFun ((eq_torusDisplacement_iff _ (D := fun q ↦ (q.1 : ℝ) • v)).2
    ⟨?_, fun q i ↦ ?_, fun x ↦ ?_⟩) q).symm
  · fun_prop
  · simp
  · simp

/-- The displacement of a `C^n` diffeotopy of the torus is `C^n`: locally it is the motion
`(t, x) ↦ Φ (t, x) - x` read through a local inverse of the covering map. -/
theorem contMDiff_torusDisplacement :
    ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) 𝓘(ℝ, ι → ℝ) n
      Φ.torusDisplacement := by
  refine contMDiff_pi_module_iff.2 fun i ↦ ContMDiff.of_comp_isLocalDiffeomorph
    (AddCircle.isLocalDiffeomorph_coe (p i) n)
    ((continuous_apply i).comp Φ.continuous_torusDisplacement) ?_
  have h : ((↑) : ℝ → AddCircle (p i)) ∘ (fun q ↦ Φ.torusDisplacement q i) =
      fun q ↦ Φ q i - q.2 i :=
    funext fun q ↦ Φ.coe_torusDisplacement_apply q i
  rw [h]
  exact (contMDiff_apply.comp Φ.contMDiff).sub (contMDiff_apply.comp contMDiff_snd)

/-- **The displacement of a loop is a lattice vector.** If the final diffeomorphism of a
diffeotopy `Φ` of the torus is the identity, then at time `1` every point has been displaced by
the same vector `v`, and `v` lies in the period lattice: `v i ∈ p i ℤ` for every `i`. -/
theorem exists_torusDisplacement_one_eq (hΦ : Φ.final = Diffeomorph.refl _ _ n) :
    ∃ v : ι → ℝ, (∀ i, v i ∈ AddSubgroup.zmultiples (p i)) ∧
      ∀ x, Φ.torusDisplacement (1, x) = v := by
  -- Each coordinate is a continuous function of `x` with values in the discrete set `p i ℤ`, on
  -- the connected torus, hence constant.
  have h (i : ι) : ∃ c ∈ AddSubgroup.zmultiples (p i), ∀ x, Φ.torusDisplacement (1, x) i = c := by
    have hmaps : Set.MapsTo (fun x ↦ Φ.torusDisplacement (1, x) i) Set.univ
        (AddSubgroup.zmultiples (p i) : Set ℝ) := fun x _ ↦ by
      have h := Φ.coe_torusDisplacement_apply (1, x) i
      rw [← Φ.final_apply, hΦ, Diffeomorph.coe_refl, id, sub_self,
        AddCircle.coe_eq_zero_iff] at h
      exact AddSubgroup.mem_zmultiples_iff.2 h
    obtain ⟨c, hc, h⟩ := isPreconnected_univ.eqOn_const_of_mapsTo
      (isDiscrete_iff_discreteTopology.2
        (inferInstanceAs (DiscreteTopology (AddSubgroup.zmultiples (p i)))))
      (by fun_prop : Continuous fun x ↦ Φ.torusDisplacement (1, x) i).continuousOn hmaps
      ⟨0, zero_mem _⟩
    exact ⟨c, hc, fun x ↦ h (Set.mem_univ x)⟩
  choose v hv hx using h
  exact ⟨v, hv, fun x ↦ funext fun i ↦ hx i x⟩

/-- **A loop of the torus is homotopic to a translation loop.** Let `Φ` be a `C^n` diffeotopy of
the torus whose final diffeomorphism is the identity. Then there is a vector `v` of the period
lattice and a `C^n` homotopy `G` from the motion of `Φ` to the motion of the translation loop
along `v` which fixes both time ends: `G ((x, 0), s) = G ((x, 1), s) = x`. The proof takes for `v`
the common displacement of all points at time `1` (`exists_torusDisplacement_one_eq`) and for `G`
the straight-line homotopy `G ((x, t), s) = x + [(1 - s) D (t, x) + s t v]` between the
displacements in the universal cover. -/
theorem exists_homotopy_cylinderMap_torusTranslationDiffeotopy
    (hΦ : Φ.final = Diffeomorph.refl _ _ n) :
    ∃ v : ι → ℝ, (∀ i, v i ∈ AddSubgroup.zmultiples (p i)) ∧
      ∃ G : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval → ∀ i, AddCircle (p i),
        ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
          (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n G ∧
        (∀ q, G (q, 0) = Φ.cylinderMap q) ∧
        (∀ q, G (q, 1) = (torusTranslationDiffeotopy (n := n) p v).cylinderMap q) ∧
        (∀ x s, G ((x, 0), s) = x) ∧ ∀ x s, G ((x, 1), s) = x := by
  obtain ⟨v, hv, hD⟩ := Φ.exists_torusDisplacement_one_eq hΦ
  refine ⟨v, hv, fun q ↦ q.1.1 + fun i ↦
    (((1 - (q.2 : ℝ)) * Φ.torusDisplacement (q.1.2, q.1.1) i + q.2 * (q.1.2 * v i) : ℝ) :
      AddCircle (p i)), ?_, fun q ↦ ?_, fun q ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_⟩
  · have hs : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
        𝓘(ℝ) n fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦ (q.2 : ℝ) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_snd
    have ht : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
        𝓘(ℝ) n fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦ (q.1.2 : ℝ) :=
      contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)
    have hD' : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
        𝓘(ℝ, ι → ℝ) n fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦
          Φ.torusDisplacement (q.1.2, q.1.1) := Φ.contMDiff_torusDisplacement.comp
      ((contMDiff_snd.comp contMDiff_fst).prodMk (contMDiff_fst.comp contMDiff_fst))
    refine contMDiff_pi_iff.2 fun i ↦
      (contMDiff_apply.comp (contMDiff_fst.comp contMDiff_fst)).add
        ((AddCircle.contMDiff_coe (p i) n).comp ?_)
    have hpoly : ContDiff ℝ n fun r : ℝ × ℝ × ℝ ↦ (1 - r.1) * r.2.1 + r.1 * (r.2.2 * v i) := by
      fun_prop
    exact hpoly.contMDiff.comp
      (hs.prodMk_space (((contMDiff_pi_module_iff.1 hD') i).prodMk_space ht))
  · rw [Diffeotopy.cylinderMap_apply, Φ.apply_eq_add_torusDisplacement (q.2, q.1)]
    simp
  · simp [Diffeotopy.cylinderMap_apply]
  · simp only [torusDisplacement_zero, Pi.zero_apply, Set.Icc.coe_zero, zero_mul, mul_zero,
      add_zero, AddCircle.coe_zero]
    exact add_zero x
  · -- At time `1` both displacements are the lattice vector `v`, whose image in the torus is `0`.
    funext i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (hv i)
    simp only [hD, Set.Icc.coe_one, one_mul, Pi.add_apply]
    rw [show (1 - (s : ℝ)) * v i + s * v i = v i by ring, ← hk,
      (AddCircle.coe_eq_zero_iff (p i)).2 ⟨k, rfl⟩, add_zero]

end Diffeotopy

end TauCeti
