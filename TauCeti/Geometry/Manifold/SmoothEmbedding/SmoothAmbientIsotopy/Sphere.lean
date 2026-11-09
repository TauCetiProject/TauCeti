/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Rotation
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.SphereBoost
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Diffeomorph

/-!
# Matching two circles in a sphere to first order by an ambient isotopy

Let `K` be a smooth embedding of the circle into the unit sphere `Sⁿ` of a real inner product
space `E`, with `n ≥ 2`, and let `L` be a loop in `Sⁿ` which is differentiable with injective
derivative at a point `z₀` of the circle, for instance another embedding. Then `K` is smoothly
ambient isotopic to an embedding `K'` which agrees with `L` to first order at `z₀`: `K'` and `L`
take the same value and have the same derivative at `z₀`
(`TauCeti.SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq`). For knots in `S³` and `L` a
great circle, this makes a knot tangent to the standard unknot at a point, the first step in
making it standard near that point, as the connected sum of knots requires.

The isotopy is a rotation followed by a boost. Read the two circles along `Circle.exp` in `E`, and
write `x`, `y` for the points of `K` and `L` over `z₀ = exp (t i)` and `v`, `w` for their
velocities there. Each velocity is tangent to the sphere
(`TauCeti.inner_deriv_coe_comp_circleExp_eq_zero`) and nonzero, since both loops have injective
derivative at `z₀` (`TauCeti.deriv_coe_comp_circleExp_ne_zero`). A rotation diffeotopy carries
`x` to `y` and the direction of `v` to that of `w`
(`TauCeti.exists_diffeotopy_final_apply_eq_and_apply_eq`); this is where `n ≥ 2` is used. The
boost of rapidity `log (‖w‖ / ‖v‖)` toward `-y` then fixes `y` and multiplies the tangent vectors
at `y` by `‖w‖ / ‖v‖` (`TauCeti.fderiv_sphereBoost_neg_self_apply`), which corrects the speed.
Since the velocity read along `Circle.exp` determines the derivative
(`TauCeti.mfderiv_eq_of_deriv_coe_comp_circleExp_eq`), the moved embedding agrees with `L` to first
order.

For `n = 1` the statement is false: an isotopy of the circle cannot reverse the orientation of an
embedding of the circle into itself.

More coarsely, an embedding of any manifold into `Sⁿ` moved by two linear isometries of the same
determinant gives smoothly ambient isotopic embeddings
(`TauCeti.SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph`), since an
isometry of determinant `1` restricts to the final map of a rotation diffeotopy
(`TauCeti.exists_diffeotopy_final_apply_eq_of_det_eq_one`). For knots in `S³` this says that the
mirror image does not depend on the reflection used to form it.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq`: a smooth embedding of the
  circle into a sphere of dimension at least two is smoothly ambient isotopic to one agreeing to
  first order at a given point with any loop that has injective derivative there.
* `TauCeti.SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph`: moving
  an embedding into a sphere by two linear isometries of the same determinant gives smoothly
  ambient isotopic embeddings.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for diffeotopies
  and ambient isotopy.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  the connected sum of knots.
-/

public section

noncomputable section

open Function Metric Module Real
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {k : ℕ∞ω}

/-- **Matching two circles in a sphere to first order.** In the unit sphere `Sⁿ` of a real inner
product space, `n ≥ 2`, a `C^k` embedding `K` of the circle, `k ≠ 0`, is smoothly ambient isotopic
to an embedding `K'` which agrees to first order at a given point `z₀` with a given loop `L`,
differentiable with injective derivative at `z₀`: `K' z₀ = L z₀`, and `K'` and `L` have the same
derivative at `z₀`. -/
theorem exists_smoothAmbientIsotopic_mfderiv_eq (hn : 2 ≤ n) (hk : k ≠ 0)
    (K : SmoothEmbedding (𝓡 1) (𝓡 n) k Circle (sphere (0 : E) 1))
    {L : Circle → sphere (0 : E) 1} {z₀ : Circle} (hLd : MDifferentiableAt (𝓡 1) (𝓡 n) L z₀)
    (hL : Injective (mfderiv (𝓡 1) (𝓡 n) L z₀)) :
    ∃ K' : SmoothEmbedding (𝓡 1) (𝓡 n) k Circle (sphere (0 : E) 1),
      K.SmoothAmbientIsotopic K' ∧ K' z₀ = L z₀ ∧
        mfderiv (𝓡 1) (𝓡 n) K' z₀ = mfderiv (𝓡 1) (𝓡 n) L z₀ := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z₀
  -- The points `x`, `y` and velocities `v`, `w` of `K` and `L` over `exp (t i)`, read in `E`.
  set γ : ℝ → E := fun s => (K (Circle.exp s) : E)
  set x : E := (K (Circle.exp t) : E)
  set y : E := (L (Circle.exp t) : E)
  set v := deriv γ t
  set w := deriv (fun s => (L (Circle.exp s) : E)) t
  have hKd : MDifferentiableAt (𝓡 1) (𝓡 n) K (Circle.exp t) := K.contMDiff.mdifferentiableAt hk
  have hv : v ≠ 0 := deriv_coe_comp_circleExp_ne_zero hKd (K.isImmersion.mfderiv_injective hk _)
  have hw : w ≠ 0 := deriv_coe_comp_circleExp_ne_zero hLd hL
  have hxv : ⟪x, v⟫ = 0 := inner_deriv_coe_comp_circleExp_eq_zero hKd
  have hyw : ⟪y, w⟫ = 0 := inner_deriv_coe_comp_circleExp_eq_zero hLd
  have hy : ‖-y‖ = 1 := by rw [norm_neg]; exact norm_eq_of_mem_sphere _
  -- Rotate `(x, v / ‖v‖)` to `(y, w / ‖w‖)`.
  obtain ⟨Φ, e, hΦ, hex, hev⟩ := exists_diffeotopy_final_apply_eq_and_apply_eq (m := k) hn
    (norm_eq_of_mem_sphere _) (norm_smul_inv_norm hv)
    (by rw [real_inner_smul_right, hxv, mul_zero]) (norm_eq_of_mem_sphere _)
    (norm_smul_inv_norm hw) (by rw [real_inner_smul_right, hyw, mul_zero])
  -- `x` and `y` abbreviate the points that `hex` mentions.
  replace hex : e x = y := hex
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hev
  -- Then boost toward `-y` to correct the speed.
  set a := log (‖w‖ / ‖v‖)
  let Ψ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1) := sphereBoostDiffeotopy hy a
  refine ⟨K.transDiffeomorph (Φ.trans Ψ).final, K.smoothAmbientIsotopic_transDiffeomorph_final _,
    ?_⟩
  have hK' (s : ℝ) : (K.transDiffeomorph (Φ.trans Ψ).final (Circle.exp s) : E) =
      sphereBoost (-y) a (e (γ s)) := by
    rw [transDiffeomorph_apply, Diffeotopy.final_trans, _root_.Diffeomorph.coe_trans,
      Function.comp_apply, coe_sphereBoostDiffeotopy_final_apply, hΦ]
  have h₀ : K.transDiffeomorph (Φ.trans Ψ).final (Circle.exp t) = L (Circle.exp t) := by
    refine Subtype.ext ((hK' t).trans ?_)
    -- `γ t` is `x` by definition, and `y = -(-y)` is the fixed point of the boost toward `-y`.
    change sphereBoost (-y) a (e x) = y
    simpa [hex] using sphereBoost_neg_self hy a
  refine ⟨h₀, mfderiv_eq_of_deriv_coe_comp_circleExp_eq
    ((K.transDiffeomorph _).contMDiff.mdifferentiableAt hk) hLd h₀ ?_⟩
  -- The velocity of the moved embedding is `eᵃ • e v = (‖w‖ / ‖v‖) • ‖v‖ • (w / ‖w‖) = w`.
  have hγ : HasDerivAt γ v t := by
    refine (mdifferentiableAt_iff_differentiableAt.1 ?_).hasDerivAt
    exact ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero).comp t
      (hKd.comp t ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero))
  have hB := ((differentiableAt_sphereBoost (cosh_add_sinh_mul_inner_pos hy
    (by simp [γ]) a).ne').hasFDerivAt.comp_hasDerivAt t
      (e.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hγ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall hK')
  rw [hB.deriv]
  -- `hB` reads `e` through the continuous linear map it induces and the point as `(e ∘ γ) t`;
  -- these are `e v` and `e x` by definition.
  change fderiv ℝ (sphereBoost (-y) a) (e x) (e v) = w
  exact e.toLinearIsometry.fderiv_sphereBoost_log_apply_eq hy hv hw hex hxv hev

/-- **Isometries of the same determinant give ambient isotopic embeddings.** Moving a `C^k`
embedding into the unit sphere `Sⁿ` by two linear isometries of `E` with the same determinant gives
smoothly ambient isotopic embeddings. The second isometry is the first followed by an isometry of
determinant `1`, the final map of a rotation diffeotopy of the sphere. -/
theorem smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph {EM HM M : Type*}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    (f : SmoothEmbedding I (𝓡 n) k M (sphere (0 : E) 1)) {e₁ e₂ : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e₁.toLinearEquiv : ℝ) = LinearEquiv.det e₂.toLinearEquiv) :
    (f.transDiffeomorph (e₁.unitSphereDiffeomorph k)).SmoothAmbientIsotopic
      (f.transDiffeomorph (e₂.unitSphereDiffeomorph k)) := by
  have hdet : (LinearEquiv.det (e₁.symm.trans e₂).toLinearEquiv : ℝ) = 1 := by
    simp [Units.ext he]
  obtain ⟨Φ, hΦ⟩ := exists_diffeotopy_final_apply_eq_of_det_eq_one (n := n) (m := k) hdet
  refine SmoothAmbientIsotopic.of_diffeotopy Φ fun x => Subtype.ext ?_
  rw [hΦ]
  simp

end TauCeti.SmoothEmbedding
