/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Dynamics.Billiard.GeneratingFunction
public import TauCeti.Dynamics.Billiard.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.JointImplicitFunction
import TauCeti.Dynamics.Billiard.Continuous

/-!
# Smoothness of the billiard map

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)` (`TauCeti.StrictConvexBilliardTable.nextCollision`).
If `χ` is `C^(n+1)`, then `B` is `C^n` on the strip
(`TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`), and so is its inverse: `B` is a
`C^n` diffeomorphism of the strip onto itself
(`TauCeti.StrictConvexBilliardTable.nextCollisionPartialDiffeomorph`). One derivative is lost
because the tangential components are inner products with the derivative `χ'`. That `B` and the
billiard map `β` on `AddCircle L × (-1, 1)` are homeomorphisms needs no smoothness at all; see
`TauCeti.Dynamics.Billiard.Homeomorph`.

For `n ≠ 0` the proof is the implicit function theorem for the generating function
`S(s, t) = -‖χ(t) - χ(s)‖` (`TauCeti.StrictConvexBilliardTable.generatingFunction`). On the domain
`s < t < s + L` of chords between distinct boundary points, the derivative

`∂_s S(s, t) = ⟪χ'(s), u⟫`,

where `u` is the unit vector along the chord, is `C^n`
(`TauCeti.StrictConvexBilliardTable.contDiffAt_inner_deriv_chordDir`), and the next collision
parameter `t(s, v)` solves `∂_s S(s, t) = v`: the generating function generates the next-collision
map. The partial derivative `∂_t ∂_s S` is negative by the twist condition
(`TauCeti.StrictConvexBilliardTable.deriv_deriv_generatingFunction_left_neg`). So the joint
implicit function theorem (`HasStrictFDerivAt.jointImplicitFunctionOfProdDomain`) applies at every
point, and its `C^n` solutions agree with `t(s, v)` because chords of the window are determined by
their tangential components. For `n = 0` it is the continuity of `B`, which needs no smoothness
(`TauCeti.StrictConvexBilliardTable.continuousAt_nextParam`). The next tangential component
`w = ⟪u, χ'(t)⟫` is then `C^n` too. These statements are pointwise: at a state `(s, v)` they only
need `χ` to be `C^(n+1)` at `s` and at `t`
(`TauCeti.StrictConvexBilliardTable.contDiffAt_nextCollision`).

The inverse of `B` is `τ⁻¹ ∘ ι ∘ B ∘ ι`, where `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`
(`TauCeti.StrictConvexBilliardTable.nextCollisionEquiv_symm_apply`), so it is `C^n` as well.

## Main results

* `TauCeti.StrictConvexBilliardTable.contDiffAt_chordDir`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_inner_deriv_chordDir`: smoothness of the chord
  direction and of `∂_s S`, jointly in both endpoints.
* `TauCeti.StrictConvexBilliardTable.contDiffAt_nextParam`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_nextTangential`,
  `TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_nextCollision`: the next-collision map is `C^n`
  at a state `(s, v)` of the strip when `χ` is `C^(n+1)` at `s` and at `t`, hence on the whole
  strip when `χ` is `C^(n+1)`.
* `TauCeti.StrictConvexBilliardTable.nextCollisionPartialDiffeomorph`: the next-collision map as a
  `C^n` diffeomorphism of the strip, with inverse `τ⁻¹ ∘ ι ∘ B ∘ ι`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module
open scoped RealInnerProductSpace ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o) {n : WithTop ℕ∞}

/-! ### Smoothness of the chord data -/

/-- The chord direction `u = (χ(t) - χ(s)) / ‖χ(t) - χ(s)‖` is as smooth as `χ` is at both
endpoints, jointly in the endpoints, at every chord between distinct boundary points. -/
theorem contDiffAt_chordDir {s t : ℝ} (hs : ContDiffAt ℝ n χ s) (ht : ContDiffAt ℝ n χ t)
    (h : χ t ≠ χ s) : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ χ.chordDir p.1 p.2) (s, t) := by
  have hd : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ χ p.2 - χ p.1) (s, t) :=
    (ht.comp (s, t) contDiffAt_snd).sub (hs.comp (s, t) contDiffAt_fst)
  have h0 : χ t - χ s ≠ 0 := sub_ne_zero.2 h
  simp only [chordDir_def, NormedSpace.normalize]
  exact (((contDiffAt_norm ℝ h0).comp (s, t) hd).inv (norm_ne_zero_iff.2 h0)).smul hd

/-- The derivative `∂_s S(s, t) = ⟪χ'(s), u⟫` of the generating function in its first argument is
`C^n`, jointly in both endpoints, at every chord between distinct boundary points, when `χ` is
`C^(n+1)` at `s` and `C^n` at `t`. -/
theorem contDiffAt_inner_deriv_chordDir {s t : ℝ} (hs : ContDiffAt ℝ (n + 1) χ s)
    (ht : ContDiffAt ℝ n χ t) (h : χ t ≠ χ s) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫) (s, t) :=
  (ContDiffAt.comp (g := deriv χ) (s, t) (hs.derivWithin le_rfl) contDiffAt_fst).inner ℝ
    (χ.contDiffAt_chordDir (hs.of_le le_self_add) ht h)

/-! ### Smoothness of the next-collision map -/

/-- The partial derivative in `t` of `∂_s S(s, t) = ⟪χ'(s), u⟫` at a chord between distinct
boundary points is invertible, when `χ` is `C^(n+1)` at `s` and `C^n` at `t` with `n ≠ 0`: it is
the mixed partial derivative `∂_t ∂_s S`, which is negative by the twist condition. -/
private theorem isInvertible_fderiv_inner_deriv_chordDir_comp_inr (hn : n ≠ 0) {s t : ℝ}
    (hs : ContDiffAt ℝ (n + 1) χ s) (ht : ContDiffAt ℝ n χ t) (hst : χ t ≠ χ s) :
    (fderiv ℝ (fun p : ℝ × ℝ ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫) (s, t) ∘L
      .inr ℝ ℝ ℝ).IsInvertible := by
  set G : ℝ × ℝ → ℝ := fun p ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫
  have hG1 : HasFDerivAt G (fderiv ℝ G (s, t)) (s, t) :=
    ((χ.contDiffAt_inner_deriv_chordDir hs ht hst).differentiableAt hn).hasFDerivAt
  set c := (fderiv ℝ G (s, t) ∘L .inr ℝ ℝ ℝ) 1
  -- The derivative of `G` along `t` is the mixed partial derivative `∂_t ∂_s S < 0`.
  have hc : c ≠ 0 := by
    have h1 : HasDerivAt (fun t' ↦ G (s, t')) c t :=
      (hG1.comp t (hasFDerivAt_prodMk_right s t)).hasDerivAt
    have heq : (fun t' ↦ deriv (fun s' ↦ χ.generatingFunction s' t') s) =ᶠ[𝓝 t]
        fun t' ↦ G (s, t') := by
      filter_upwards [χ.continuous.continuousAt.eventually_ne hst] with t' ht'
      exact (χ.hasDerivAt_generatingFunction_left ht').deriv
    have h2 := χ.deriv_deriv_generatingFunction_left_neg hst
    rw [heq.deriv_eq, h1.deriv] at h2
    exact h2.ne
  -- A linear map `ℝ →L[ℝ] ℝ` is multiplication by its value `c` at `1`.
  rw [ContinuousLinearMap.ext_ring (ContinuousLinearMap.toSpanSingleton_apply_one ℝ c).symm]
  exact ContinuousLinearMap.isInvertible_toSpanSingleton_iff.2 hc

/-- **Smoothness of the next collision parameter.** If `χ` is `C^(n+1)` at `s` and `C^n` at the
next collision parameter `t(s, v)`, then `t` is `C^n`, jointly in `s` and `v`, at the state
`(s, v)` of the strip `ℝ × (-1, 1)`. For `n ≠ 0` it is the joint implicit function of
`(s, t) ↦ ∂_s S(s, t)`, given by the implicit function theorem and the twist condition. -/
theorem contDiffAt_nextParam {s v : ℝ} (hs : ContDiffAt ℝ (n + 1) χ s)
    (ht : ContDiffAt ℝ n χ (χ.nextParam s v)) (hv : v ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) (s, v) := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- `C^0`: continuity at every nearby state of the strip.
    exact contDiffAt_zero.2 ⟨_, prod_mem_nhds univ_mem (Ioo_mem_nhds hv.1 hv.2),
      fun x hx ↦ (χ.continuousAt_nextParam hx.2).continuousWithinAt⟩
  set t := χ.nextParam s v
  have hst : χ t ≠ χ s := χ.apply_nextParam_ne hv
  set G : ℝ × ℝ → ℝ := fun p ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫
  have hG : ContDiffAt ℝ n G (s, t) := χ.contDiffAt_inner_deriv_chordDir hs ht hst
  have hG' := hG.hasStrictFDerivAt (hG.differentiableAt hn).hasFDerivAt hn
  have hinv := χ.isInvertible_fderiv_inner_deriv_chordDir_comp_inr hn hs ht hst
  have hψ := hG'.contDiffAt_jointImplicitFunctionOfProdDomain hinv hG
  -- On the window of chords between distinct boundary points, `t(s', ·)` inverts `G (s', ·)`,
  -- since the generating function generates the next-collision map.
  have heq := hG'.eventuallyEq_jointImplicitFunctionOfProdDomain hinv
    (φ := fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) (by
      filter_upwards [((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd (continuous_fst.add continuous_const))).mem_nhds
          (χ.nextParam_mem_Ioo hv)] with p hp
      exact χ.nextParam_inner_deriv_chordDir hp)
  have hpt : ((s, t).1, G (s, t)) = (s, v) := by
    simp only [G, t, χ.inner_deriv_chordDir_nextParam hv]
  rw [hpt] at hψ heq
  exact hψ.congr_of_eventuallyEq heq

/-- **Smoothness of the next tangential component.** If `χ` is `C^(n+1)` at `s` and at the next
collision parameter `t(s, v)`, then the next tangential component `w(s, v)` is `C^n`, jointly in
`s` and `v`, at the state `(s, v)` of the strip `ℝ × (-1, 1)`. -/
theorem contDiffAt_nextTangential {s v : ℝ} (hs : ContDiffAt ℝ (n + 1) χ s)
    (ht : ContDiffAt ℝ (n + 1) χ (χ.nextParam s v)) (hv : v ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.nextTangential x.1 x.2) (s, v) := by
  have hds : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ deriv χ x.1) (s, v) :=
    ContDiffAt.comp (g := deriv χ) (s, v) (hs.derivWithin le_rfl) contDiffAt_fst
  have hsq : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ √(1 - x.2 ^ 2)) (s, v) :=
    (contDiffAt_const.sub (contDiffAt_snd.pow 2)).sqrt (by nlinarith [hv.1, hv.2])
  have hout : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.outgoingDir x.1 x.2) (s, v) := by
    simp only [outgoingDir_def]
    exact (contDiffAt_snd.smul hds).add
      (hsq.smul (o.rightAngleRotation.contDiff.contDiffAt.comp (s, v) hds))
  simp only [nextTangential_def]
  exact hout.inner ℝ (ContDiffAt.comp (g := deriv χ) (s, v) (ht.derivWithin le_rfl)
    (χ.contDiffAt_nextParam hs (ht.of_le le_self_add) hv))

/-- **Smoothness of the billiard map at a state.** If `χ` is `C^(n+1)` at `s` and at the next
collision parameter `t(s, v)`, then the next-collision map `(s, v) ↦ (t, w)` is `C^n` at the state
`x = (s, v)` of the open strip `ℝ × (-1, 1)`. -/
theorem contDiffAt_nextCollision {x : ℝ × ℝ} (hs : ContDiffAt ℝ (n + 1) χ x.1)
    (ht : ContDiffAt ℝ (n + 1) χ (χ.nextParam x.1 x.2)) (hx : x.2 ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n χ.nextCollision x := by
  exact ((χ.contDiffAt_nextParam hs (ht.of_le le_self_add) hx).prodMk
    (χ.contDiffAt_nextTangential hs ht hx)).congr_of_eventuallyEq
      (.of_forall χ.nextCollision_apply)

/-- **Smoothness of the billiard map.** If `χ` is `C^(n+1)`, the next-collision map
`(s, v) ↦ (t, w)` is `C^n` on the strip `ℝ × (-1, 1)`. -/
theorem contDiffOn_nextCollision (hχ : ContDiff ℝ (n + 1) χ) :
    ContDiffOn ℝ n χ.nextCollision (univ ×ˢ Ioo (-1) 1) :=
  fun _ hx ↦ (χ.contDiffAt_nextCollision hχ.contDiffAt hχ.contDiffAt hx.2).contDiffWithinAt

/-- The inverse `(t, w) ↦ (s - L, -v)` of the next-collision map, where `(s, v)` is the next
collision of `(t, -w)`, is `C^n` on the strip when `χ` is `C^(n+1)`. -/
private theorem contDiffOn_nextCollision_inv (hχ : ContDiff ℝ (n + 1) χ) :
    ContDiffOn ℝ n (fun x : ℝ × ℝ ↦ (χ.nextParam x.1 (-x.2) - χ.period,
      -χ.nextTangential x.1 (-x.2))) (univ ×ˢ Ioo (-1) 1) := by
  have hι : ContDiff ℝ n (fun x : ℝ × ℝ ↦ (x.1, -x.2)) := contDiff_fst.prodMk contDiff_snd.neg
  have h := (χ.contDiffOn_nextCollision hχ).comp hι.contDiffOn
    fun (x : ℝ × ℝ) (hx : x ∈ univ ×ˢ Ioo (-1 : ℝ) 1) ↦
      ⟨mem_univ _, show -x.2 ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hx.2.2], by linarith [hx.2.1]⟩⟩
  simpa [comp_def] using
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd.neg).comp_contDiffOn h

/-! ### The next-collision map as a diffeomorphism of the strip -/

/-- **The billiard map is a diffeomorphism of the strip.** If `χ` is `C^(n+1)`, the next-collision
map `B` is a `C^n` diffeomorphism of the strip `ℝ × (-1, 1)` onto itself. Its inverse
`τ⁻¹ ∘ ι ∘ B ∘ ι` sends `(t, w)` to `(s - L, -v)`, where `(s, v)` is the next collision of
`(t, -w)`. -/
def nextCollisionPartialDiffeomorph (hχ : ContDiff ℝ (n + 1) χ) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) n where
  toFun := χ.nextCollision
  invFun x := (χ.nextParam x.1 (-x.2) - χ.period, -χ.nextTangential x.1 (-x.2))
  source := univ ×ˢ Ioo (-1) 1
  target := univ ×ˢ Ioo (-1) 1
  map_source' x hx := ⟨mem_univ _, by rw [nextCollision_apply]; exact χ.nextTangential_mem_Ioo hx.2⟩
  map_target' x hx := ⟨mem_univ _, χ.neg_nextTangential_neg_mem_Ioo x.1 ⟨x.2, hx.2⟩⟩
  left_inv' x hx := by
    simpa [Prod.ext_iff, Subtype.ext_iff] using
      χ.nextCollisionEquiv.symm_apply_apply (x.1, ⟨x.2, hx.2⟩)
  right_inv' x hx := by
    simpa [Prod.ext_iff, Subtype.ext_iff] using
      χ.nextCollisionEquiv.apply_symm_apply (x.1, ⟨x.2, hx.2⟩)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := isOpen_univ.prod isOpen_Ioo
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 (χ.contDiffOn_nextCollision hχ)
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 (χ.contDiffOn_nextCollision_inv hχ)

/-- The partial diffeomorphism `nextCollisionPartialDiffeomorph` acts as the next-collision map. -/
@[simp]
theorem coe_nextCollisionPartialDiffeomorph (hχ : ContDiff ℝ (n + 1) χ) :
    ⇑(χ.nextCollisionPartialDiffeomorph hχ) = χ.nextCollision :=
  (rfl)

/-- The inverse of the next-collision map on the strip is `τ⁻¹ ∘ ι ∘ B ∘ ι`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_symm_apply (hχ : ContDiff ℝ (n + 1) χ)
    (x : ℝ × ℝ) :
    (χ.nextCollisionPartialDiffeomorph hχ).toPartialEquiv.symm x =
      (χ.nextParam x.1 (-x.2) - χ.period, -χ.nextTangential x.1 (-x.2)) :=
  (rfl)

/-- The source of the next-collision diffeomorphism is the strip `ℝ × (-1, 1)`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_source (hχ : ContDiff ℝ (n + 1) χ) :
    (χ.nextCollisionPartialDiffeomorph hχ).source = univ ×ˢ Ioo (-1) 1 :=
  (rfl)

/-- The target of the next-collision diffeomorphism is the strip `ℝ × (-1, 1)`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_target (hχ : ContDiff ℝ (n + 1) χ) :
    (χ.nextCollisionPartialDiffeomorph hχ).target = univ ×ˢ Ioo (-1) 1 :=
  (rfl)

end StrictConvexBilliardTable

end TauCeti
