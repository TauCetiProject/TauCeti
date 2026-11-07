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

/-- A concordance `F` which is the straight line over `exp (θ₀ i)` and whose ends `K` and `K'` have
the same derivative there as a loop `L` makes `L` differentiable at `exp (θ₀ i)`, with the same
velocity there as `K` and `K'`. -/
private theorem mdifferentiableAt_and_deriv_eq_of_collars (F : Concordance K K')
    {L : Circle → sphere (0 : E) 1} {θ₀ εl εr : ℝ}
    (hK : mfderiv (𝓡 1) (𝓡 n) K (Circle.exp θ₀) = mfderiv (𝓡 1) (𝓡 n) L (Circle.exp θ₀))
    (hK' : mfderiv (𝓡 1) (𝓡 n) K' (Circle.exp θ₀) = mfderiv (𝓡 1) (𝓡 n) L (Circle.exp θ₀))
    (h₀ : ∀ t, F (Circle.exp θ₀, t) = (L (Circle.exp θ₀), t))
    (hFl : ∀ x t, t ≤ εl → F (x, t) = (K x, t)) (hFr : ∀ x t, 1 - εr ≤ t → F (x, t) = (K' x, t))
    (hεl : 0 < εl) (hεr : 0 < εr) :
    MDifferentiableAt (𝓡 1) (𝓡 n) L (Circle.exp θ₀) ∧
      deriv (fun θ => (K (Circle.exp θ) : E)) θ₀ = deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ ∧
      deriv (fun θ => (K' (Circle.exp θ) : E)) θ₀ = deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ := by
  have hKL : K (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 0
    rw [hFl _ 0 hεl.le] at h
    exact congrArg Prod.fst h
  have hK'L : K' (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 1
    rw [hFr _ 1 (by linarith)] at h
    exact congrArg Prod.fst h
  have hLd : MDifferentiableAt (𝓡 1) (𝓡 n) L (Circle.exp θ₀) :=
    mdifferentiableAt_of_mfderiv_injective <| by
      rw [← hK]
      exact (K.isImmersion.isDiffImmersionAt (by simp) (Circle.exp θ₀)).mfderiv_injective
  exact ⟨hLd, deriv_coe_comp_circleExp_eq_of_mfderiv_eq
    (K.contMDiff.mdifferentiableAt (by simp)) hLd hKL hK,
    deriv_coe_comp_circleExp_eq_of_mfderiv_eq
    (K'.contMDiff.mdifferentiableAt (by simp)) hLd hK'L hK'⟩

/-- The circle velocity of the track at time `t` is the pair of velocities of the two components
of its slice. -/
private theorem fderiv_track_left_apply (F : Concordance K K') (θ t : ℝ) :
    fderiv ℝ (track F) (θ, t) (1, 0) = (deriv (fun θ' => ((F (Circle.exp θ', t)).1 : E)) θ,
      deriv (fun θ' => (F (Circle.exp θ', t)).2) θ) :=
  Prod.ext
    ((ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_track_left F θ t)).deriv.symm
    ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_track_left F θ t)).deriv.symm

/-- Where the slice of `F` at time `t` is the slice of an embedding `g`, the circle velocity of
the track is the velocity of `g`, with no time component. -/
private theorem fderiv_track_left_eq_of_slice (F : Concordance K K') {g : Circle → sphere (0 : E) 1}
    {θ₀ t : ℝ} (hg : ∀ x, F (x, t) = (g x, t)) :
    fderiv ℝ (track F) (θ₀, t) (1, 0) = (deriv (fun θ => (g (Circle.exp θ) : E)) θ₀, 0) := by
  rw [fderiv_track_left_apply]
  simp only [hg, deriv_const]

/-- The circle velocity of the track depends smoothly on the time. -/
private theorem contDiff_fderiv_track_left (F : Concordance K K') (θ₀ : ℝ) :
    ContDiff ℝ ∞ fun t => fderiv ℝ (track F) (θ₀, t) (1, 0) :=
  ((contDiff_infty_iff_fderiv.1 (contDiff_track F)).2.comp
    (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

/-- If `F` is the straight line over `exp (θ₀ i)`, its track runs along the line `s ↦ (v, s)`. -/
private theorem track_line (F : Concordance K K') {L : Circle → sphere (0 : E) 1} {θ₀ : ℝ}
    (h₀ : ∀ t, F (Circle.exp θ₀, t) = (L (Circle.exp θ₀), t)) (s : ℝ) :
    track F (θ₀, s) = ((L (Circle.exp θ₀) : E), s) := by
  simp only [track, h₀ s]

/-- Along the straight line over `exp (θ₀ i)`, the derivative of the track sends the time
direction to itself. -/
private theorem fderiv_track_right_line (F : Concordance K K') {L : Circle → sphere (0 : E) 1}
    {θ₀ : ℝ} (h₀ : ∀ t, F (Circle.exp θ₀, t) = (L (Circle.exp θ₀), t)) (t : ℝ) :
    fderiv ℝ (track F) (θ₀, t) (0, 1) = (0, 1) := by
  refine (hasDerivAt_track_right F θ₀ t).unique ?_
  have hfun : (fun s => track F (θ₀, s)) = fun s => ((L (Circle.exp θ₀) : E), s) :=
    funext (track_line F h₀)
  rw [hfun]
  exact (hasDerivAt_const t _).prodMk (hasDerivAt_id' t)

/-- The circle velocity of the straight line over `exp (θ₀ i)`, at any time, is nonzero. -/
private theorem fderiv_track_left_fst_ne_zero (F : Concordance K K')
    {L : Circle → sphere (0 : E) 1} {θ₀ : ℝ}
    (h₀ : ∀ t, F (Circle.exp θ₀, t) = (L (Circle.exp θ₀), t)) (t : ℝ) :
    (fderiv ℝ (track F) (θ₀, t) (1, 0)).1 ≠ 0 := by
  rw [fderiv_track_left_apply]
  exact deriv_coe_fst_comp_circleExp_ne_zero
    (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) _).mfderiv_injective) h₀

/-- The circle velocity of the straight line over `exp (θ₀ i)` is orthogonal to the point `v`. -/
private theorem inner_fderiv_track_left_fst (F : Concordance K K')
    {L : Circle → sphere (0 : E) 1} {θ₀ : ℝ}
    (h₀ : ∀ t, F (Circle.exp θ₀, t) = (L (Circle.exp θ₀), t)) (t : ℝ) :
    ⟪(fderiv ℝ (track F) (θ₀, t) (1, 0)).1, (L (Circle.exp θ₀) : E)⟫ = 0 := by
  have hmd : MDifferentiableAt (𝓡 1) (𝓡 n) (fun z => (F (z, t)).1) (Circle.exp θ₀) :=
    (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)).fst.comp (Circle.exp θ₀)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have h := inner_deriv_coe_comp_circleExp_eq_zero hmd
  rw [h₀ t] at h
  rw [fderiv_track_left_apply, real_inner_comm]
  exact h

/-- Along the line `{exp (θ₀ i)} × ℝ`, the track of `F` sheared in time by `β` with `β t` minus the
time component of the circle velocity of the track has the circle velocity of the track, with
its time component removed. -/
private theorem hasDerivAt_track_timeShear (F : Concordance K K') {θ₀ t : ℝ} (β : ℝ → ℝ)
    {h : Circle → ℝ} (hh0 : h (Circle.exp θ₀) = 0)
    (hhd : HasDerivAt (fun θ => h (Circle.exp θ)) 1 θ₀)
    (hβ : β t = -(fderiv ℝ (track F) (θ₀, t) (1, 0)).2)
    (hτ : fderiv ℝ (track F) (θ₀, t) (0, 1) = (0, 1)) :
    HasDerivAt (fun θ => track F (θ, t + β t * h (Circle.exp θ)))
      ((fderiv ℝ (track F) (θ₀, t) (1, 0)).1, 0) θ₀ := by
  have hσ : HasDerivAt (fun θ => t + β t * h (Circle.exp θ)) (β t * 1) θ₀ :=
    (hhd.const_mul (β t)).const_add t
  have h₁ := ((contDiff_track F).differentiable (by simp) (θ₀, t)).hasFDerivAt.comp_hasDerivAt_of_eq
    θ₀ ((hasDerivAt_id' θ₀).prodMk hσ) (by rw [hh0, mul_zero, add_zero])
  refine h₁.congr_deriv ?_
  have hsplit : ((1 : ℝ), β t * 1) = ((1 : ℝ), (0 : ℝ)) + β t • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hτ, hβ]
  ext <;> simp

/-- Composing a smooth concordance with a time shear with small displacement and positive time
derivative gives a smooth embedding. -/
private theorem isSmoothEmbedding_comp_timeShear (F : Concordance K K') {β : ℝ → ℝ}
    {h : Circle → ℝ} (hβ : ContDiff ℝ ∞ β) (hh : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h) {C : ℝ}
    (hC : ∀ x t, |β t * h x| ≤ C) (hpos : ∀ x t, 0 < 1 + deriv β t * h x) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (F ∘ timeShear β h) := by
  have hφinj := injective_timeShear (hβ.differentiable (by simp)) hpos
  have hφprop : IsProperMap (timeShear β h) :=
    isProperMap_timeShear hβ.continuous hh.continuous hC
  have hφimm := isImmersion_timeShear hβ hh fun x t => (hpos x t).ne'
  have hFinj : Injective F := F.toSmoothEmbedding.isEmbedding.injective
  refine IsImmersion.isSmoothEmbedding_of_isProperMap ?_ (hFinj.comp hφinj)
    ((F.isCollaredTrack.isClosedEmbedding F.toSmoothEmbedding.contMDiff.continuous
      hFinj).isProperMap.comp hφprop)
  refine isImmersion_iff_forall_isImmersionAt.2 fun p => ?_
  refine (F.toSmoothEmbedding.contMDiff.comp (contMDiff_timeShear hβ hh)).contMDiffOn
    |>.isImmersionAt_of_hasLeftInverse_mfderiv isOpen_univ (mem_univ p) (by simp) ?_
  exact isDiffImmersionAt_iff.1 ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt
    (by simp) _).comp (hφimm.isDiffImmersionAt (by simp) p))

/-- Applying a level-preserving diffeomorphism `Ψ` of `Sⁿ × ℝ` after a concordance `F` composed
with a time shear gives a concordance from `K` to `K'`, provided `Ψ` and the shear are trivial on
the collars of `F`, and the shear moves times by less than the collars. -/
private theorem exists_apply_eq_diffeomorph_comp_timeShear (F : Concordance K K')
    (Ψ : (sphere (0 : E) 1 × ℝ) ≃ₘ^∞⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯ (sphere (0 : E) 1 × ℝ))
    (hΨ : ∀ p, (Ψ p).2 = p.2) {β : ℝ → ℝ} {h : Circle → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h) {εl εr : ℝ} (hεl : 0 < εl) (hεr : 0 < εr)
    (hFl : ∀ x t, t ≤ εl → F (x, t) = (K x, t))
    (hFr : ∀ x t, 1 - εr ≤ t → F (x, t) = (K' x, t))
    (hΨl : ∀ t, t ≤ εl → ∀ y, Ψ (y, t) = (y, t))
    (hΨr : ∀ t, 1 - εr ≤ t → ∀ y, Ψ (y, t) = (y, t))
    (hβl : ∀ t, t ≤ εl → β t = 0) (hβr : ∀ t, 1 - εr ≤ t → β t = 0)
    (hsmall : ∀ x t, |β t * h x| < min εl εr ∧ 0 < 1 + deriv β t * h x) :
    ∃ G : Concordance K K', ∀ p, G p = Ψ (F (timeShear β h p)) := by
  have hε : 0 < min εl εr := lt_min hεl hεr
  have hFφ := isSmoothEmbedding_comp_timeShear F hβ hh (fun x t => (hsmall x t).1.le)
    fun x t => (hsmall x t).2
  set G₀ := (SmoothEmbedding.ofIsSmoothEmbedding _ hFφ).transDiffeomorph Ψ with hG₀_def
  have hG₀ (p : Circle × ℝ) : G₀ p = Ψ (F (timeShear β h p)) := by
    simp only [hG₀_def, SmoothEmbedding.transDiffeomorph_apply,
      SmoothEmbedding.ofIsSmoothEmbedding_apply, Function.comp_apply]
  have hcol : IsCollaredTrack K K' G₀ := by
    refine ⟨⟨min εl εr, hε, fun x t ht => ?_⟩, ⟨min εl εr, hε, fun x t ht => ?_⟩, fun x t ht => ?_⟩
    · have htl : t ≤ εl := ht.trans (min_le_left _ _)
      rw [hG₀, timeShear_apply, hβl t htl, zero_mul, add_zero, hFl x t htl, hΨl t htl]
    · have htr : 1 - εr ≤ t := le_trans (by linarith [min_le_right εl εr]) ht
      rw [hG₀, timeShear_apply, hβr t htr, zero_mul, add_zero, hFr x t htr, hΨr t htr]
    · rw [hG₀, hΨ, timeShear_apply]
      refine F.isCollaredTrack.snd_apply_mem_Ioo x _ ?_
      by_cases hβt : β t = 0
      · rw [hβt, zero_mul, add_zero]
        exact ht
      · have hI : t ∈ Icc εl (1 - εr) := by
          by_contra hI
          rcases not_and_or.1 hI with hI | hI
          · exact hβt (hβl t (not_le.1 hI).le)
          · exact hβt (hβr t (not_le.1 hI).le)
        have hb := abs_lt.1 (hsmall x t).1
        constructor <;> linarith [min_le_left εl εr, min_le_right εl εr, hI.1, hI.2]
  exact ⟨⟨G₀, hcol⟩, hG₀⟩

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
  -- `L` is differentiable at `exp θ₀`, and its velocity there is that of `K` and of `K'`.
  obtain ⟨hLd, hKW, hK'W⟩ := mdifferentiableAt_and_deriv_eq_of_collars F hK hK' h₀ hFl hFr hεl hεr
  set W : E := deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ with hW_def
  -- The velocity `(A t, b t)` of the slice of `F` at time `t`, read in `E × ℝ`.
  set A : ℝ → E := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).1 with hA_def
  set b : ℝ → ℝ := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).2 with hb_def
  have hAb := contDiff_fderiv_track_left F θ₀
  -- On the collars, the slices are those of `K` and `K'`.
  have hAl (t : ℝ) (ht : t ≤ εl) : A t = W :=
    (congrArg Prod.fst (fderiv_track_left_eq_of_slice F fun x => hFl x t ht)).trans hKW
  have hAr (t : ℝ) (ht : 1 - εr ≤ t) : A t = W :=
    (congrArg Prod.fst (fderiv_track_left_eq_of_slice F fun x => hFr x t ht)).trans hK'W
  obtain ⟨Ψ, hΨ₂, hΨid, hΨv, hΨd⟩ := exists_diffeomorph_apply_eq (A := A) hn
    (norm_eq_of_mem_sphere _) (contDiff_fst.comp hAb) (fderiv_track_left_fst_ne_zero F h₀)
    (inner_fderiv_track_left_fst F h₀) (hAl 0 hεl.le)
  -- A time shear by `β = -b` removes the time component of the slice velocity.
  set β : ℝ → ℝ := fun t => -b t with hβ_def
  have hβ : ContDiff ℝ ∞ β := (contDiff_snd.comp hAb).neg
  have hβl (t : ℝ) (ht : t ≤ εl) : β t = 0 :=
    neg_eq_zero.2 (congrArg Prod.snd (fderiv_track_left_eq_of_slice F fun x => hFl x t ht))
  have hβr (t : ℝ) (ht : 1 - εr ≤ t) : β t = 0 :=
    neg_eq_zero.2 (congrArg Prod.snd (fderiv_track_left_eq_of_slice F fun x => hFr x t ht))
  have hcs : HasCompactSupport β := HasCompactSupport.intro isCompact_Icc fun t ht => by
    rcases not_and_or.1 ht with ht | ht
    · exact hβl t (not_le.1 ht).le
    · exact hβr t (not_le.1 ht).le
  obtain ⟨h, hh, hh0, hhd, hsmall⟩ :=
    TauCeti.exists_shear_circle θ₀ hβ hcs (lt_min hεl hεr)
  obtain ⟨G, hG⟩ := exists_apply_eq_diffeomorph_comp_timeShear F Ψ hΨ₂ hβ hh hεl hεr hFl hFr
    (fun t ht => hΨid t (hAl t ht)) (fun t ht => hΨid t (hAr t ht)) hβl hβr hsmall
  have hFσ (t : ℝ) : F (Circle.exp θ₀, t + β t * h (Circle.exp θ₀)) = (L (Circle.exp θ₀), t) := by
    rw [hh0, mul_zero, add_zero, h₀]
  have hGline (s : ℝ) : G (Circle.exp θ₀, s) = (L (Circle.exp θ₀), s) := by
    rw [hG, timeShear_apply, hFσ, hΨv _ _ rfl]
  refine ⟨G, hGline, fun t => ?_⟩
  -- Along the slice at time `t`, the shear cancels the time velocity `b t`.
  have hY : HasDerivAt (fun θ => track F (θ, t + β t * h (Circle.exp θ))) (A t, 0) θ₀ :=
    hasDerivAt_track_timeShear F β hh0 hhd rfl (fderiv_track_right_line F h₀ t)
  have hsnd : HasDerivAt (fun θ => (track F (θ, t + β t * h (Circle.exp θ))).2) 0 θ₀ :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY
  refine mfderiv_eq_of_deriv_comp_circleExp_eq_prod
    (G.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hLd.prodMap mdifferentiableAt_id) hGline ?_ ?_
  · -- The sphere component: the rotation and boost turn `A t` into `W`.
    have hd := hΨd t _ _ θ₀ (congrArg (fun p => ((p.1 : sphere (0 : E) 1) : E)) (hFσ t))
      (congrArg Prod.snd (hFσ t))
      ((ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY) hsnd
    simp only [hG, timeShear_apply, Prod.map_apply]
    exact hd.deriv
  · -- The time component: the shear cancels the time velocity `b t`.
    simp only [hG, hΨ₂, timeShear_apply]
    exact hsnd.deriv.trans (by simp)

end SmoothEmbedding.Concordance

end FirstOrder

end TauCeti
