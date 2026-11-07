/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.InnerProductSpace.Sphere.Boost
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Geometry.Manifold.Diffeomorph.Sphere
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.TimeShear
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Making a concordance standard to first order along an arc

Let `F : S¹ × ℝ → Sⁿ × ℝ` be a smooth concordance between circle embeddings `K` and `K'` into the
unit sphere `Sⁿ` of a real inner product space, with `n ≥ 3`, and let `L : S¹ → Sⁿ` be a loop with
which `K` and `K'` agree to first order at a point `z₀`. If `F` is the straight line over `z₀`
level by level, that is `F (z₀, t) = (L z₀, t)` for every `t`, then `F` can be replaced by a
concordance `G` from `K` to `K'` which still satisfies `G (z₀, t) = (L z₀, t)` for every `t`, and
agrees with the strip `L × id` to first order along that line
(`TauCeti.SmoothEmbedding.Concordance.exists_mfderiv_eq_prodMap`). For knots in connected-sum
position and `L` the great circle, this is the first-order normalization of a concordance along the
arc `{-i} × ℝ`, after which the concordance can be made the standard strip near that arc.

Along the line, the derivative of `F` sends the time direction to the time direction, and the
circle direction to a vector `(A t, b t)` of `T_v Sⁿ × ℝ`, where `v = L z₀`, while the strip sends
it to `(W, 0)`. Three moves correct this, and none of them changes `F` near its two ends.

* A smooth family of linear isometries `Q t` fixing `v` turns the direction of `A t` into that of
  `W` (`TauCeti.exists_contDiff_linearIsometryEquiv_apply_eq`). Each `Q t` is a product of four
  hyperplane reflections, through an auxiliary unit vector orthogonal to `v` which avoids the
  antipodes of the directions of all the `A t`. Such a vector exists because the cone over a curve
  misses a point of a space of dimension at least three; this is where `n ≥ 3` is used.
* A smooth family of boosts toward `-v` (`TauCeti.sphereBoost`) fixes `v` and rescales the
  tangent vectors at `v` by `‖W‖ / ‖A t‖`. Applying `Q t` and then this boost at level `t` is a
  diffeomorphism of `Sⁿ × ℝ` preserving the levels (`TauCeti.boostRotateDiffeomorph`).
* The time shear `(z, t) ↦ (z, t - b t * h z)` of the source (`TauCeti.timeShear`), where `h` is a
  small function on the circle vanishing at `z₀` with velocity `1` there
  (`TauCeti.exists_shear_circle`), cancels the time component `b t`.

The derivatives of the result and of `L × id` along the line are compared slice by slice along
`Circle.exp` (`TauCeti.mfderiv_eq_of_deriv_comp_circleExp_eq_prod`).

## Main results

* `TauCeti.SmoothEmbedding.Concordance.exists_mfderiv_eq_prodMap`: a concordance with
  `F (z₀, t) = (L z₀, t)` for every `t` can be made to agree with `L × id` to first order along
  the line `{z₀} × ℝ`, keeping `G (z₀, t) = (L z₀, t)` for every `t`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, for concordances and isotopies of embeddings.
* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapter 1, for the connected sum of knots.
-/

public section

noncomputable section

open Set Function Filter Manifold Topology Metric
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Making a concordance standard to first order along an arc -/

section FirstOrder

open Module Real
open scoped RealInnerProductSpace

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

namespace SmoothEmbedding.Concordance

variable {K K' : SmoothEmbedding (𝓡 1) (𝓡 n) ∞ Circle (sphere (0 : E) 1)}

/-- A concordance between circle embeddings into `Sⁿ`, read in the coordinates
`(θ, t) ↦ (exp (θ i), t)` of the cylinder and in `E × ℝ`. -/
private def track (F : Concordance K K') (q : ℝ × ℝ) : E × ℝ :=
  (((F (Circle.exp q.1, q.2)).1 : E), (F (Circle.exp q.1, q.2)).2)

private theorem track_apply (F : Concordance K K') (θ s : ℝ) :
    track F (θ, s) = (((F (Circle.exp θ, s)).1 : E), (F (Circle.exp θ, s)).2) :=
  (rfl)

private theorem contDiff_track (F : Concordance K K') : ContDiff ℝ ∞ (track F) := by
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ)) ∞ fun q : ℝ × ℝ => (Circle.exp q.1, q.2) :=
    (contMDiff_circleExp.comp contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff
  have hι : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞
      fun p : sphere (0 : E) 1 × ℝ => ((p.1 : E), p.2) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd
  exact contMDiff_iff_contDiff.1 (hι.comp (F.toSmoothEmbedding.contMDiff.comp hc))

/-- The partial derivative of the track in the circle direction is the velocity of its slice. -/
private theorem hasDerivAt_track_left (F : Concordance K K') (θ t : ℝ) :
    HasDerivAt (fun θ' => track F (θ', t)) (fderiv ℝ (track F) (θ, t) (1, 0)) θ := by
  have h := ((contDiff_track F).differentiable (by simp) (θ, t)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_id' θ).prodMk (hasDerivAt_const θ t))
  exact h

/-- The partial derivative of the track in the time direction. -/
private theorem hasDerivAt_track_right (F : Concordance K K') (θ t : ℝ) :
    HasDerivAt (fun s => track F (θ, s)) (fderiv ℝ (track F) (θ, t) (0, 1)) t := by
  have h := ((contDiff_track F).differentiable (by simp) (θ, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t θ).prodMk (hasDerivAt_id' t))
  exact h

/-- **Making a concordance standard to first order along an arc.** Let `F` be a concordance
between smooth circle embeddings `K` and `K'` into the unit sphere `Sⁿ`, `n ≥ 3`, which is the
straight line over `z₀` level by level, `F (z₀, t) = (L z₀, t)` for every `t`, where `K` and `K'`
have the same derivative at `z₀` as the loop `L`. Then some concordance `G` from `K` to `K'` also
satisfies `G (z₀, t) = (L z₀, t)` for every `t`, and has the same derivative as the strip `L × id`
at every point `(z₀, t)`. -/
theorem exists_mfderiv_eq_prodMap (hn : 3 ≤ n) (F : Concordance K K')
    {L : Circle → sphere (0 : E) 1} {z₀ : Circle}
    (hK : mfderiv (𝓡 1) (𝓡 n) K z₀ = mfderiv (𝓡 1) (𝓡 n) L z₀)
    (hK' : mfderiv (𝓡 1) (𝓡 n) K' z₀ = mfderiv (𝓡 1) (𝓡 n) L z₀)
    (h₀ : ∀ t, F (z₀, t) = (L z₀, t)) :
    ∃ G : Concordance K K', (∀ t, G (z₀, t) = (L z₀, t)) ∧
      ∀ t, mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) G (z₀, t) =
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) (Prod.map L _root_.id) (z₀, t) := by
  -- Read `F` along the line `{exp (θ₀ i)} × ℝ`: there its circle velocity is `(A t, b t)`. A
  -- level-preserving rotation followed by a boost, `Ψ`, turns `A t` into the velocity `W` of `L`,
  -- and a time shear `φ` of the source cancels `b t`, so `G = Ψ ∘ F ∘ φ` is the concordance.
  obtain ⟨θ₀, rfl⟩ := Circle.exp_surjective z₀
  obtain ⟨εl, hεl, hFl⟩ := F.isCollaredTrack.exists_pos_apply_eq_left
  obtain ⟨εr, hεr, hFr⟩ := F.isCollaredTrack.exists_pos_apply_eq_right
  set v : E := (L (Circle.exp θ₀) : E) with hv_def
  have hv : ‖v‖ = 1 := norm_eq_of_mem_sphere _
  -- `K` and `K'` pass through `L (exp θ₀)`, and `L` is differentiable there.
  have hKL : K (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 0
    rw [hFl _ 0 hεl.le] at h
    exact congrArg Prod.fst h
  have hK'L : K' (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 1
    rw [hFr _ 1 (by linarith)] at h
    exact congrArg Prod.fst h
  have hu₁ : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ₀ 1 ≠ 0 := fun h =>
    one_ne_zero (show (1 : ℝ) = 0 from injective_mfderiv_circleExp θ₀ (h.trans (map_zero _).symm))
  have hLd : MDifferentiableAt (𝓡 1) (𝓡 n) L (Circle.exp θ₀) := by
    by_contra hnd
    have hinj := (K.isImmersion.isDiffImmersionAt (by simp) (Circle.exp θ₀)).mfderiv_injective
    have h0 := congrArg (fun D : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      D (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ₀ 1)) hK
    simp only [mfderiv_zero_of_not_mdifferentiableAt hnd] at h0
    exact hu₁ (hinj (h0.trans (map_zero _).symm))
  -- The velocity `W` of `L` at `θ₀` is that of `K` and of `K'`.
  have hKW : deriv (fun θ => (K (Circle.exp θ) : E)) θ₀ =
      deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ :=
    deriv_coe_comp_circleExp_eq_of_mfderiv_eq (K.contMDiff.mdifferentiableAt (by simp)) hLd hKL hK
  have hK'W : deriv (fun θ => (K' (Circle.exp θ) : E)) θ₀ =
      deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ :=
    deriv_coe_comp_circleExp_eq_of_mfderiv_eq (K'.contMDiff.mdifferentiableAt (by simp)) hLd hK'L
      hK'
  set W : E := deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ with hW_def
  -- The velocity `(A t, b t)` of the slice of `F` at time `t`, read in `E × ℝ`.
  set A : ℝ → E := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).1 with hA_def
  set b : ℝ → ℝ := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).2 with hb_def
  have hAb : ContDiff ℝ ∞ fun t => fderiv ℝ (track F) (θ₀, t) (1, 0) :=
    ((contDiff_infty_iff_fderiv.1 (contDiff_track F)).2.comp
      (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hA : ContDiff ℝ ∞ A := contDiff_fst.comp hAb
  have hb : ContDiff ℝ ∞ b := contDiff_snd.comp hAb
  have hAslice (t : ℝ) : A t = deriv (fun θ => ((F (Circle.exp θ, t)).1 : E)) θ₀ :=
    ((ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀
      (hasDerivAt_track_left F θ₀ t)).deriv.symm
  have hbslice (t : ℝ) : b t = deriv (fun θ => (F (Circle.exp θ, t)).2) θ₀ :=
    ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀
      (hasDerivAt_track_left F θ₀ t)).deriv.symm
  -- On the collars, the slices are those of `K` and `K'`.
  have hAl (t : ℝ) (ht : t ≤ εl) : A t = W := by
    rw [hAslice, ← hKW]
    congr 1
    funext θ
    rw [hFl _ t ht]
  have hbl (t : ℝ) (ht : t ≤ εl) : b t = 0 := by
    rw [hbslice]
    simp only [hFl _ t ht, deriv_const]
  have hAr (t : ℝ) (ht : 1 - εr ≤ t) : A t = W := by
    rw [hAslice, ← hK'W]
    congr 1
    funext θ
    rw [hFr _ t ht]
  have hbr (t : ℝ) (ht : 1 - εr ≤ t) : b t = 0 := by
    rw [hbslice]
    simp only [hFr _ t ht, deriv_const]
  -- Along the line, the track is `s ↦ (v, s)`.
  have htrack_line (s : ℝ) : track F (θ₀, s) = (v, s) := by
    simp only [track, h₀ s, hv_def]
  have hτ (t : ℝ) : fderiv ℝ (track F) (θ₀, t) (0, 1) = (0, 1) := by
    refine (hasDerivAt_track_right F θ₀ t).unique ?_
    rw [show (fun s => track F (θ₀, s)) = fun s => (v, s) from funext htrack_line]
    exact (hasDerivAt_const t v).prodMk (hasDerivAt_id' t)
  have hA0 (t : ℝ) : A t ≠ 0 := by
    rw [hAslice]
    exact deriv_coe_fst_comp_circleExp_ne_zero
      (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
      ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) _).mfderiv_injective) h₀
  have hAv (t : ℝ) : ⟪A t, v⟫ = 0 := by
    have hmd : MDifferentiableAt (𝓡 1) (𝓡 n) (fun z => (F (z, t)).1) (Circle.exp θ₀) :=
      (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)).fst.comp (Circle.exp θ₀)
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    have h := inner_deriv_coe_comp_circleExp_eq_zero hmd
    rw [h₀ t] at h
    rw [hAslice, real_inner_comm]
    exact h
  have hW : W ≠ 0 := hAl 0 hεl.le ▸ hA0 0
  -- A smooth family of rotations fixing `v` turns the direction of `A t` into that of `W`.
  set u : ℝ → E := fun t => ‖A t‖⁻¹ • A t with hu_def
  have hu : ContDiff ℝ ∞ u :=
    ((hA.norm ℝ hA0).inv fun t => norm_ne_zero_iff.2 (hA0 t)).smul hA
  have hu0 : u 0 = ‖W‖⁻¹ • W := by simp only [hu_def, hAl 0 hεl.le]
  have hfin : 2 < finrank ℝ (ℝ ∙ v)ᗮ := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n)
      (norm_ne_zero_iff.1 (hv.symm ▸ one_ne_zero))]
    omega
  obtain ⟨Q, hQ, hQv, hQu, hQ1⟩ := exists_contDiff_linearIsometryEquiv_apply_eq (k := ∞)
    (by simp) hfin hu (fun t => norm_smul_inv_norm (hA0 t))
    (fun t => by rw [hu_def, real_inner_smul_left, hAv, mul_zero]) 0
  -- A smooth family of boosts toward `-v` then corrects the speed.
  set α : ℝ → ℝ := fun t => Real.log (‖W‖ / ‖A t‖) with hα_def
  have hα : ContDiff ℝ ∞ α :=
    (contDiff_const.div (hA.norm ℝ hA0) fun t => norm_ne_zero_iff.2 (hA0 t)).log fun t =>
      (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 (hA0 t))).ne'
  have hv' : ‖-v‖ = 1 := by rw [norm_neg, hv]
  set Ψ := boostRotateDiffeomorph (n := n) hv' hα hQ
  have hΨ₁ (p : sphere (0 : E) 1 × ℝ) : ((Ψ p).1 : E) = boostRotate (-v) α Q (p.2, p.1) :=
    coe_boostRotateDiffeomorph_apply_fst hv' hα hQ p
  have hΨ₂ (p : sphere (0 : E) 1 × ℝ) : (Ψ p).2 = p.2 :=
    boostRotateDiffeomorph_apply_snd hv' hα hQ p
  have hΨid (t : ℝ) (hAt : A t = W) (y : sphere (0 : E) 1) : Ψ (y, t) = (y, t) := by
    have hut : u t = u 0 := by simp only [hu_def, hAt, hAl 0 hεl.le]
    refine Prod.ext (Subtype.ext ?_) (hΨ₂ _)
    simp only [hΨ₁, boostRotate_apply, hQ1 t hut, hα_def, hAt, div_self (norm_ne_zero_iff.2 hW),
      Real.log_one, sphereBoost_zero, _root_.id]
  have hΨv (t : ℝ) : Ψ (L (Circle.exp θ₀), t) = (L (Circle.exp θ₀), t) := by
    refine Prod.ext (Subtype.ext ?_) (hΨ₂ _)
    rw [hΨ₁]
    have h := sphereBoost_neg_self hv' (α t)
    rw [neg_neg] at h
    simp only [boostRotate_apply]
    rw [← hv_def, hQv, h]
  -- A time shear by `β = -b` removes the time component of the slice velocity.
  set β : ℝ → ℝ := fun t => -b t with hβ_def
  have hβ : ContDiff ℝ ∞ β := hb.neg
  have hβ0 (t : ℝ) (ht : t ∉ Icc εl (1 - εr)) : β t = 0 := by
    rcases not_and_or.1 ht with ht | ht
    · simp only [hβ_def, hbl t (not_le.1 ht).le, neg_zero]
    · simp only [hβ_def, hbr t (not_le.1 ht).le, neg_zero]
  have hcs : HasCompactSupport β := HasCompactSupport.intro isCompact_Icc hβ0
  set ε := min εl εr
  have hε : 0 < ε := lt_min hεl hεr
  obtain ⟨h, hh, hh0, hhd, hsmall⟩ := TauCeti.exists_shear_circle θ₀ hβ hcs hε
  have hpos (x : Circle) (t : ℝ) : 0 < 1 + deriv β t * h x := (hsmall x t).2
  -- The sheared track `F ∘ φ` is a smooth embedding.
  set φ := timeShear β h with hφ_def
  have hφinj := injective_timeShear (hβ.differentiable (by simp)) hpos
  have hφprop : IsProperMap φ :=
    isProperMap_timeShear hβ.continuous hh.continuous fun x t => (hsmall x t).1.le
  have hφimm := isImmersion_timeShear hβ hh fun x t => (hpos x t).ne'
  have hFinj : Injective F := F.toSmoothEmbedding.isEmbedding.injective
  have hFφ : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (F ∘ φ) := by
    refine IsImmersion.isSmoothEmbedding_of_isProperMap ?_ (hFinj.comp hφinj)
      ((F.isCollaredTrack.isClosedEmbedding F.toSmoothEmbedding.contMDiff.continuous
        hFinj).isProperMap.comp hφprop)
    refine isImmersion_iff_forall_isImmersionAt.2 fun p => ?_
    refine (F.toSmoothEmbedding.contMDiff.comp (contMDiff_timeShear hβ hh)).contMDiffOn
      |>.isImmersionAt_of_hasLeftInverse_mfderiv isOpen_univ (mem_univ p) (by simp) ?_
    exact isDiffImmersionAt_iff.1 ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt
      (by simp) _).comp (hφimm.isDiffImmersionAt (by simp) p))
  -- The new concordance applies `Ψ` after the sheared track.
  set G₀ := (SmoothEmbedding.ofIsSmoothEmbedding _ hFφ).transDiffeomorph Ψ with hG₀_def
  have hG₀ (p : Circle × ℝ) : G₀ p = Ψ (F (φ p)) := by
    simp only [hG₀_def, SmoothEmbedding.transDiffeomorph_apply,
      SmoothEmbedding.ofIsSmoothEmbedding_apply, Function.comp_apply]
  have hcol : IsCollaredTrack K K' G₀ := by
    refine ⟨⟨ε, hε, fun x t ht => ?_⟩, ⟨ε, hε, fun x t ht => ?_⟩, fun x t ht => ?_⟩
    · have htl : t ≤ εl := ht.trans (min_le_left _ _)
      rw [hG₀, hφ_def, timeShear_apply,
        show β t = 0 by simp only [hβ_def, hbl t htl, neg_zero], zero_mul, add_zero,
        hFl x t htl, hΨid t (hAl t htl)]
    · have htr : 1 - εr ≤ t := le_trans (by linarith [min_le_right εl εr]) ht
      rw [hG₀, hφ_def, timeShear_apply,
        show β t = 0 by simp only [hβ_def, hbr t htr, neg_zero], zero_mul, add_zero,
        hFr x t htr, hΨid t (hAr t htr)]
    · rw [hG₀, hΨ₂, hφ_def, timeShear_apply]
      refine F.isCollaredTrack.snd_apply_mem_Ioo x _ ?_
      by_cases hβt : β t = 0
      · rw [hβt, zero_mul, add_zero]
        exact ht
      · have hI : t ∈ Icc εl (1 - εr) := by
          by_contra hI
          exact hβt (hβ0 t hI)
        have hb := abs_lt.1 (hsmall x t).1
        constructor <;> linarith [min_le_left εl εr, min_le_right εl εr, hI.1, hI.2]
  let G : Concordance K K' := ⟨G₀, hcol⟩
  have hG (p : Circle × ℝ) : G p = Ψ (F (φ p)) := hG₀ p
  have hGline (s : ℝ) : G (Circle.exp θ₀, s) = (L (Circle.exp θ₀), s) := by
    rw [hG, hφ_def, timeShear_apply, hh0, mul_zero, add_zero, h₀, hΨv]
  refine ⟨G, hGline, fun t => ?_⟩
  -- Along the slice at time `t`, the shear moves the time by `σ θ = t + β t * h (exp θ)`.
  set σ : ℝ → ℝ := fun θ => t + β t * h (Circle.exp θ) with hσ_def
  have hσ : HasDerivAt σ (β t * 1) θ₀ := (hhd.const_mul (β t)).const_add t
  have hσ₀ : σ θ₀ = t := by simp only [hσ_def, hh0, mul_zero, add_zero]
  have hY : HasDerivAt (fun θ => track F (θ, σ θ)) (A t, 0) θ₀ := by
    have h₁ : HasDerivAt (fun θ => track F (θ, σ θ)) (fderiv ℝ (track F) (θ₀, t) (1, β t * 1))
        θ₀ :=
      ((contDiff_track F).differentiable (by simp) (θ₀, t)).hasFDerivAt.comp_hasDerivAt_of_eq
        θ₀ ((hasDerivAt_id' θ₀).prodMk hσ) (by rw [hσ₀])
    convert h₁ using 1
    have hsplit : ((1 : ℝ), β t * 1) = ((1 : ℝ), (0 : ℝ)) + β t • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hτ]
    ext
    · simp [hA_def]
    · simp [hb_def, hβ_def]
  have hfst : HasDerivAt (fun θ => (track F (θ, σ θ)).1) (A t) θ₀ :=
    (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY
  have hsnd : HasDerivAt (fun θ => (track F (θ, σ θ)).2) 0 θ₀ :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY
  refine mfderiv_eq_of_deriv_comp_circleExp_eq_prod
    (G.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hLd.prodMap mdifferentiableAt_id) hGline ?_ ?_
  · -- The sphere component: the rotation and boost turn `A t` into `W`.
    have hBR : HasFDerivAt (boostRotate (-v) α Q) (fderiv ℝ (boostRotate (-v) α Q) (t, v))
        (t, v) :=
      ((contDiffAt_boostRotate hv' hα hQ t hv).differentiableAt (by simp)).hasFDerivAt
    have hD : HasDerivAt
        (fun θ => boostRotate (-v) α Q ((track F (θ, σ θ)).2, (track F (θ, σ θ)).1))
        (fderiv ℝ (boostRotate (-v) α Q) (t, v) (0, A t)) θ₀ :=
      hBR.comp_hasDerivAt_of_eq θ₀ (hsnd.prodMk hfst) (by rw [hσ₀, htrack_line])
    have hval := fderiv_boostRotate_apply_zero hv' hα hQ t (by rw [neg_neg, hQv])
      (ξ := A t) (by rw [inner_neg_right, ← hQv t, LinearIsometryEquiv.inner_map_map, hAv,
        neg_zero])
    rw [neg_neg] at hval
    -- `Q t` turns the direction `u t` of `A t` into the direction `u 0` of `W`.
    have hdir : ‖A t‖⁻¹ • Q t (A t) = ‖W‖⁻¹ • W := by
      rw [← map_smul, show ‖A t‖⁻¹ • A t = u t by rw [hu_def], hQu, hu0]
    have hslice : (fun θ => ((G (Circle.exp θ, t)).1 : E)) =
        fun θ => boostRotate (-v) α Q ((track F (θ, σ θ)).2, (track F (θ, σ θ)).1) :=
      funext fun θ => by simp only [hG, hΨ₁, hφ_def, timeShear_apply, track_apply, hσ_def]
    have hLslice : (fun θ => ((Prod.map L _root_.id (Circle.exp θ, t)).1 : E)) =
        fun θ => (L (Circle.exp θ) : E) :=
      funext fun θ => by rw [Prod.map_apply]
    rw [hslice, hD.deriv, hval, hLslice, ← hW_def]
    rw [hα_def, Real.exp_log (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 (hA0 t)))]
    exact norm_div_norm_smul_eq_of_inv_norm_smul_eq_normalize hdir
  · -- The time component: the shear cancels the time velocity `b t`.
    have hslice : (fun θ => (G (Circle.exp θ, t)).2) = fun θ => (track F (θ, σ θ)).2 :=
      funext fun θ => by simp only [hG, hΨ₂, hφ_def, timeShear_apply, track_apply, hσ_def]
    rw [hslice, hsnd.deriv]
    simp

end SmoothEmbedding.Concordance

end FirstOrder

end TauCeti
