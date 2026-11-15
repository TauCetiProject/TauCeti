/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Twist coordinates of a map of the strip

Let `F = (X, Y)` be a map of the plane `ℝ × ℝ`, with coordinates `(x, y)`, for instance a lift
of a diffeomorphism of the annulus `(ℝ / ℤ) × [0, 1]` to a neighbourhood of the strip
`ℝ × [0, 1]`. Its **twist coordinates** are

`(x, y) ↦ (x, X(x, y))`

(`TauCeti.twistCoordinates F`): a point is recorded by its first coordinate and the first
coordinate of its image. They are the coordinates `(x, X)` in which a twist map is described by a
generating function.

The Jacobian determinant of the twist coordinates is the *twist* `∂_y X`
(`TauCeti.det_fderiv_twistCoordinates`). Let `I` be an open interval, more generally an open
order-connected set, and suppose that `F` is `C^n`, `1 ≤ n`, on the open strip `ℝ × I` and twists
everywhere there, `∂_y X ≠ 0`. Then:

* the twist coordinates are injective on `ℝ × I`
  (`TauCeti.injOn_twistCoordinates`): on each vertical line `x = const`, two heights with the same
  value of `X` would give, by Rolle's theorem, a height where `∂_y X` vanishes;
* by the inverse function theorem they are a `C^n` local diffeomorphism at every point of
  `ℝ × I` (`TauCeti.isLocalDiffeomorphOn_twistCoordinates`), so they are a `C^n` diffeomorphism
  from `ℝ × I` onto an open subset of the plane
  (`TauCeti.twistCoordinatesPartialDiffeomorph`), whose inverse `Function.invFunOn` is `C^n`
  (`TauCeti.contDiffOn_invFunOn_twistCoordinates`);
* they carry each closed strip `ℝ × [c, d]` with `c, d ∈ I` onto the band between the graphs of
  `x ↦ X(x, c)` and `x ↦ X(x, d)`
  (`TauCeti.image_twistCoordinates_univ_prod_uIcc`). For the strip `ℝ × [0, 1]` of a map
  preserving both boundary lines this is the band bounded by the images of the two boundary lines.

The twist may have either sign, and no compactness of the strip is used. If `F` commutes with the
translation `(x, y) ↦ (x + a, y)`, the twist coordinates intertwine it with the diagonal
translation `(x, X) ↦ (x + a, X + a)` (`TauCeti.twistCoordinates_add_fst`). For a lift of a map of
the annulus, commuting with `(x, y) ↦ (x + 1, y)`, a twist that vanishes nowhere on a closed strip
`ℝ × [c, d]` vanishes nowhere on an open strip `ℝ × (c - ε, d + ε)`
(`TauCeti.exists_pos_twist_ne_zero_univ_prod_Ioo`), so the results above apply on an open
neighbourhood of the closed strip.

These coordinates carry the generating functions of the twist maps of the generating-function
proof of the Poincaré–Birkhoff theorem, `TauCeti.twistGeneratingFunction`.

## Main definitions

* `TauCeti.twistCoordinates F`: the map `(x, y) ↦ (x, X(x, y))`.
* `TauCeti.twistCoordinatesPartialDiffeomorph`: the twist coordinates of a twist map on an open
  strip `ℝ × I`, as a partial diffeomorphism with source `ℝ × I`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology Interval

namespace TauCeti

/-- The **twist coordinates** `(x, y) ↦ (x, X(x, y))` of a map `F = (X, Y)` of the plane. -/
def twistCoordinates (F : ℝ × ℝ → ℝ × ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1, (F q).1)

variable {F : ℝ × ℝ → ℝ × ℝ} {q : ℝ × ℝ}

@[simp]
theorem twistCoordinates_apply (q : ℝ × ℝ) : twistCoordinates F q = (q.1, (F q).1) :=
  (rfl)

/-- If `F` commutes with the translation `(x, y) ↦ (x + a, y)`, its twist coordinates intertwine
that translation with the diagonal translation `(x, X) ↦ (x + a, X + a)`. -/
theorem twistCoordinates_add_fst {a : ℝ} (hF : ∀ q, F (q + (a, 0)) = F q + (a, 0))
    (q : ℝ × ℝ) : twistCoordinates F (q + (a, 0)) = twistCoordinates F q + (a, a) := by
  simp [hF]

/-! ### Regularity and derivative -/

/-- The twist coordinates of a map are `C^n` where the map is. -/
theorem contDiffAt_twistCoordinates {n : WithTop ℕ∞} (hF : ContDiffAt ℝ n F q) :
    ContDiffAt ℝ n (twistCoordinates F) q :=
  contDiffAt_fst.prodMk (contDiffAt_fst.comp q hF)

/-- The twist coordinates of a map are `C^n` on a set where the map is. -/
theorem contDiffOn_twistCoordinates {n : WithTop ℕ∞} {s : Set (ℝ × ℝ)}
    (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (twistCoordinates F) s :=
  contDiffOn_fst.prodMk (contDiff_fst.comp_contDiffOn hF)

/-- The derivative of the twist coordinates is `(u, v) ↦ (u, dX(u, v))`. -/
theorem hasFDerivAt_twistCoordinates (hF : DifferentiableAt ℝ F q) :
    HasFDerivAt (twistCoordinates F)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ F q))) q :=
  hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp q hF.hasFDerivAt)

/-- The Jacobian determinant of the twist coordinates is the twist `∂_y X`. -/
theorem det_fderiv_twistCoordinates (hF : DifferentiableAt ℝ F q) :
    (fderiv ℝ (twistCoordinates F) q).det = (fderiv ℝ F q (0, 1)).1 := by
  simp [(hasFDerivAt_twistCoordinates hF).fderiv, ContinuousLinearMap.det,
    LinearMap.det_finTwoProd]

/-! ### Injectivity on a strip -/

/-- **The twist coordinates are injective on a twisting strip.** If `F` is differentiable on the
strip `ℝ × I` over an order-connected set `I`, and its twist `∂_y X` vanishes nowhere there, then
`(x, y) ↦ (x, X(x, y))` is injective on `ℝ × I`. -/
theorem injOn_twistCoordinates {I : Set ℝ} (hI : I.OrdConnected)
    (hF : ∀ q ∈ (univ : Set ℝ) ×ˢ I, DifferentiableAt ℝ F q)
    (htwist : ∀ q ∈ (univ : Set ℝ) ×ˢ I, (fderiv ℝ F q (0, 1)).1 ≠ 0) :
    InjOn (twistCoordinates F) ((univ : Set ℝ) ×ˢ I) := by
  -- On each vertical line, `X` takes distinct values at distinct heights, by Rolle's theorem.
  have key (x s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) : (F (x, s)).1 ≠ (F (x, t)).1 := by
    intro hX
    have hIcc : Icc s t ⊆ I := hI.out hs ht
    have hd (u : ℝ) (hu : u ∈ Icc s t) :
        HasDerivAt (fun u ↦ (F (x, u)).1) (fderiv ℝ F (x, u) (0, 1)).1 u :=
      (hasFDerivAt_fst.comp_hasDerivAt u
        (hasDerivAt_slice_right (a := x) (hF (x, u) ⟨mem_univ _, hIcc hu⟩)) :)
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hst
      (fun u hu ↦ (hd u hu).continuousAt.continuousWithinAt) hX
      fun u hu ↦ hd u (Ioo_subset_Icc_self hu)
    exact htwist _ ⟨mem_univ _, hIcc (Ioo_subset_Icc_self hc)⟩ hc0
  rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨x', t⟩ ⟨-, ht⟩ hst
  simp only [twistCoordinates_apply, Prod.mk.injEq] at hst
  obtain ⟨rfl, hX⟩ := hst
  rcases lt_trichotomy s t with h | rfl | h
  · exact absurd hX (key x s t hs ht h)
  · rfl
  · exact absurd hX.symm (key x t s ht hs h)

/-! ### The twist coordinates as a diffeomorphism onto an open set -/

section OpenStrip

variable {I : Set ℝ} (hIo : IsOpen I) {n : WithTop ℕ∞} (hn : 1 ≤ n)
  (hF : ContDiffOn ℝ n F ((univ : Set ℝ) ×ˢ I))
  (htwist : ∀ q ∈ (univ : Set ℝ) ×ˢ I, (fderiv ℝ F q (0, 1)).1 ≠ 0)
include hIo hn hF htwist

/-- On an open strip where `F` is `C^n`, `1 ≤ n`, and twists, the twist coordinates are a `C^n`
local diffeomorphism at every point. -/
theorem isLocalDiffeomorphOn_twistCoordinates :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n (twistCoordinates F)
      ((univ : Set ℝ) ×ˢ I) := fun ⟨q, hq⟩ ↦
  have hFq : ContDiffAt ℝ n F q := hF.contDiffAt ((isOpen_univ.prod hIo).mem_nhds hq)
  isLocalDiffeomorphAt_of_fderiv_eq (contDiffOn_twistCoordinates hF) (isOpen_univ.prod hIo) hq hn
    (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _
      ((det_fderiv_twistCoordinates (hFq.differentiableAt (zero_lt_one.trans_le hn).ne')).trans_ne
        (htwist q hq)))

variable (hI : I.OrdConnected)
include hI

omit hn in
/-- The injectivity of the twist coordinates on an open strip where `F` is `C^n`, `n ≠ 0`. -/
private theorem injOn_twistCoordinates_of_contDiffOn (hn : n ≠ 0) :
    InjOn (twistCoordinates F) ((univ : Set ℝ) ×ˢ I) :=
  injOn_twistCoordinates hI (fun _ hq ↦ (hF.contDiffAt
    ((isOpen_univ.prod hIo).mem_nhds hq)).differentiableAt hn) htwist

/-- **The twist coordinates of a twist map.** If `F` is `C^n`, `1 ≤ n`, on an open strip `ℝ × I`,
with `I` order-connected, and its twist `∂_y X` vanishes nowhere there, then
`(x, y) ↦ (x, X(x, y))` is a `C^n` diffeomorphism from `ℝ × I` onto its image, an open subset of
the plane. -/
def twistCoordinatesPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) n :=
  (isLocalDiffeomorphOn_twistCoordinates hIo hn hF htwist).partialDiffeomorphOfInjOn
    (isOpen_univ.prod hIo)
    (injOn_twistCoordinates_of_contDiffOn hIo hF htwist hI (zero_lt_one.trans_le hn).ne')

@[simp]
theorem coe_twistCoordinatesPartialDiffeomorph :
    ⇑(twistCoordinatesPartialDiffeomorph hIo hn hF htwist hI) = twistCoordinates F :=
  IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn _ _ _

@[simp]
theorem twistCoordinatesPartialDiffeomorph_source :
    (twistCoordinatesPartialDiffeomorph hIo hn hF htwist hI).source = (univ : Set ℝ) ×ˢ I :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source _ _ _

@[simp]
theorem twistCoordinatesPartialDiffeomorph_target :
    (twistCoordinatesPartialDiffeomorph hIo hn hF htwist hI).target =
      twistCoordinates F '' ((univ : Set ℝ) ×ˢ I) :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target _ _ _

/-- The inverse of the twist coordinates of a `C^n` twist map on an open strip, `1 ≤ n`, is `C^n`
on the image of the strip. -/
theorem contDiffOn_invFunOn_twistCoordinates :
    ContDiffOn ℝ n (Function.invFunOn (twistCoordinates F) ((univ : Set ℝ) ×ˢ I))
      (twistCoordinates F '' ((univ : Set ℝ) ×ˢ I)) :=
  contMDiffOn_iff_contDiffOn.1 <|
    (isLocalDiffeomorphOn_twistCoordinates hIo hn hF htwist).contMDiffOn_invFunOn
      (isOpen_univ.prod hIo)
      (injOn_twistCoordinates_of_contDiffOn hIo hF htwist hI (zero_lt_one.trans_le hn).ne')

end OpenStrip

/-! ### The band of a closed strip -/

/-- **The band of a closed strip.** If `F` is differentiable and twists on the strip `ℝ × I`, with
`I` order-connected, then for `c, d ∈ I` the twist coordinates map the closed strip
`ℝ × [c, d]` onto the band of the points `(x, X)` with `X` between `X(x, c)` and `X(x, d)`. -/
theorem image_twistCoordinates_univ_prod_uIcc {I : Set ℝ} (hI : I.OrdConnected)
    (hF : ∀ q ∈ (univ : Set ℝ) ×ˢ I, DifferentiableAt ℝ F q)
    (htwist : ∀ q ∈ (univ : Set ℝ) ×ˢ I, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c d : ℝ} (hc : c ∈ I)
    (hd : d ∈ I) :
    twistCoordinates F '' ((univ : Set ℝ) ×ˢ [[c, d]]) =
      {z | z.2 ∈ [[(F (z.1, c)).1, (F (z.1, d)).1]]} := by
  have hcd : [[c, d]] ⊆ I := hI.uIcc_subset hc hd
  have hinj := injOn_twistCoordinates hI hF htwist
  ext ⟨x, X⟩
  -- On the vertical line through `x`, `X` is continuous and injective on `[[c, d]]`, hence
  -- monotone or antitone, so its image is the interval between its values at the ends.
  set g : ℝ → ℝ := fun t ↦ (F (x, t)).1
  have hgc : ContinuousOn g [[c, d]] := fun t ht ↦
    (continuous_fst.continuousAt.comp ((hF _ ⟨mem_univ _, hcd ht⟩).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt)).continuousWithinAt
  have hgi : InjOn g [[c, d]] := fun s hs t ht hst ↦
    congrArg Prod.snd <| hinj (x₁ := (x, s)) (x₂ := (x, t)) ⟨mem_univ x, hcd hs⟩
      ⟨mem_univ x, hcd ht⟩ (Prod.ext rfl hst)
  have himage : g '' [[c, d]] = [[g c, g d]] := by
    rcases hgc.strictMonoOn_of_injOn_Icc' inf_le_sup hgi with h | h
    · exact hgc.image_uIcc_of_monotoneOn h.monotoneOn
    · exact hgc.image_uIcc_of_antitoneOn h.antitoneOn
  -- By definition of `g`, the band condition at `(x, X)` says `X ∈ [[g c, g d]]`.
  change _ ↔ X ∈ [[g c, g d]]
  rw [← himage]
  simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, twistCoordinates_apply,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x', t, ht, rfl, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x, t, ht, rfl, rfl⟩

/-! ### A twisting open strip around a closed strip -/

/-- **Twisting near a closed strip.** Let `F` be `C¹` and commute with the translation
`(x, y) ↦ (x + 1, y)`, for instance a lift of a map of the annulus. If its twist `∂_y X` vanishes
nowhere on the closed strip `ℝ × [c, d]`, then it vanishes nowhere on some open strip
`ℝ × (c - ε, d + ε)` with `ε > 0`. -/
theorem exists_pos_twist_ne_zero_univ_prod_Ioo (hF : ContDiff ℝ 1 F)
    (hper : ∀ q, F (q + (1, 0)) = F q + (1, 0)) {c d : ℝ} (hcd : c ≤ d)
    (htwist : ∀ q ∈ (univ : Set ℝ) ×ˢ Icc c d, (fderiv ℝ F q (0, 1)).1 ≠ 0) :
    ∃ ε > 0, ∀ q ∈ (univ : Set ℝ) ×ˢ Ioo (c - ε) (d + ε), (fderiv ℝ F q (0, 1)).1 ≠ 0 := by
  set g : ℝ × ℝ → ℝ := fun q ↦ (fderiv ℝ F q (0, 1)).1
  have hg : Continuous g :=
    continuous_fst.comp ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  -- The twist is periodic in `x`, since `F` commutes with the translation.
  have hgper (y : ℝ) : Function.Periodic (fun x ↦ g (x, y)) 1 := fun x ↦ by
    have h : fderiv ℝ F ((x, y) + (1, 0)) = fderiv ℝ F (x, y) := by
      rw [← fderiv_comp_add_right, funext hper, fderiv_add_const]
    have hxy : ((x + 1, y) : ℝ × ℝ) = (x, y) + (1, 0) := by simp
    simp only [g, hxy, h]
  -- A uniform thickening of the compact rectangle `[0, 1] × [c, d]` keeps the twist nonzero.
  obtain ⟨ε, hε, hεU⟩ := (isCompact_Icc.prod isCompact_Icc).exists_thickening_subset_open
    (isOpen_ne_fun hg continuous_const) (s := Icc (0 : ℝ) 1 ×ˢ Icc c d)
    fun q hq ↦ htwist q ⟨mem_univ _, hq.2⟩
  refine ⟨ε, hε, ?_⟩
  rintro ⟨x, y⟩ ⟨-, hy⟩
  -- Move `x` into `[0, 1)` by periodicity, and compare `y` with its nearest point of `[c, d]`.
  have hfract : g (x, y) = g (Int.fract x, y) := by
    have h := (hgper y).sub_int_mul_eq (x := x) ⌊x⌋
    simp only [mul_one, Int.self_sub_floor] at h
    exact h.symm
  set p := max c (min y d)
  have hp : dist y p < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have hpc : p ≤ max c y := max_le_max le_rfl (min_le_left _ _)
      rcases le_total c y with h | h
      · rw [max_eq_right h] at hpc
        linarith
      · rw [max_eq_left h] at hpc
        linarith [hy.1]
    · have hpy : min y d ≤ p := le_max_right _ _
      rcases le_total y d with h | h
      · rw [min_eq_left h] at hpy
        linarith
      · rw [min_eq_right h] at hpy
        linarith [hy.2]
  have hmem : (Int.fract x, y) ∈ Metric.thickening ε (Icc (0 : ℝ) 1 ×ˢ Icc c d) :=
    Metric.mem_thickening_iff.2 ⟨(Int.fract x, p),
      ⟨⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, le_max_left _ _,
        max_le hcd (min_le_right _ _)⟩,
      by simpa [Prod.dist_eq] using hp⟩
  have hne : g (Int.fract x, y) ≠ 0 := hεU hmem
  rwa [← hfract] at hne

end TauCeti
