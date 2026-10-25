/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
public import TauCeti.Analysis.Complex.Conformal.Removability.Basic

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The Schwarz reflection principle across the real axis

This file proves the summit of the conformal-mapping roadmap's Schwarz-reflection layer (L4 in
`ConformalMapping/README.md`, the `sorry`-goal stated in `ConformalMapping/Suggested.lean`): on a
conjugation-symmetric open set `Ω`, a function that is continuous on the closed upper part,
holomorphic on the open upper part, and real on `Ω ∩ ℝ` extends *holomorphically* across the real
axis. The extension is the explicit witness `schwarzReflection f` from `Reflection/Basic.lean`,
whose gluing calculus (continuity on all of `Ω`, holomorphy off the axis, the derivative formulas
and the conjugation symmetry) is already established there. What remains — and is proved here — is
holomorphy *at* the axis — and that is exactly Painlevé removability of the real axis,
`TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero` from
`Conformal/Removability/Basic.lean`, where the Morera argument that supplies it is proved. So the
reflection principle is now a two-line consequence of the two halves of its input: continuity of
the extension across the axis, and holomorphy off it.

Combined with the principle of isolated zeros for the holomorphic extension, it also shows that
the zeros on the real axis of such a function, zero-free in the upper half-plane, are isolated:
`TauCeti.eventually_ne_zero_of_real_on_axis`. Consequently a function continuous up to the axis
and holomorphic and zero-free in the upper half-plane cannot vanish on a whole boundary interval,
`TauCeti.exists_mem_Ioo_ne_zero_of_ne_zero`, so it is nonzero at real points on both sides of any
real point, `TauCeti.exists_lt_lt_ne_zero_of_ne_zero`.

Combined with the identity theorem, it gives boundary uniqueness: a function continuous up to
the real axis, holomorphic above it and vanishing on it vanishes identically,
`TauCeti.eqOn_zero_of_zero_on_real_axis`. The horizontal-strip form
`TauCeti.eqOn_zero_im_preimage_uIcc_of_zero_on_real_axis`, for strips on either side of the
axis, determines a bounded holomorphic function on a strip by its values on one edge, as for
the KMS functions of C⋆-algebra dynamics.

As with the rest of the L0–L3/L4 conformal-mapping material, this is coordinated with the upstream
Mathlib Riemann-mapping effort leanprover-community/mathlib4#33505; L4 (reflection) is not part of
that draft, so this is genuinely new Lean formalization, but any shared foundational API should be
refactored to Mathlib's once it lands.
-/

public section

namespace TauCeti

open Complex Filter Set Topology
open scoped ComplexConjugate

variable {f : ℂ → ℂ}

/-- **Schwarz reflection principle (real axis).** On a conjugation-symmetric open set `Ω`, if `f`
is continuous on the closed upper part, holomorphic on the open upper part, and real-valued on
the real axis of `Ω`, then the explicit reflection extension `schwarzReflection f` is holomorphic
on all of `Ω` — in particular across the real axis.

The gluing calculus (continuity everywhere, holomorphy off the axis, the conjugation symmetry) is
`Reflection/Basic.lean`; the missing holomorphy at the axis is Painlevé removability,
`differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero`. -/
theorem differentiableOn_schwarzReflection_of_symmetric {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    DifferentiableOn ℂ (schwarzReflection f) Ω :=
  differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩopen
    (continuousOn_schwarzReflection_of_symmetric hΩ hcont hreal)
    (differentiableOn_schwarzReflection_inter_im_ne_zero_of_symmetric hΩ hholo)

/-- **Schwarz reflection principle**, packaged existential form (the L4 milestone of
`ConformalMapping/Suggested.lean`). On a conjugation-symmetric open `Ω`, a function continuous on
the closed upper part, holomorphic on the open upper part, and real on the real axis extends to a
function holomorphic on all of `Ω` that agrees with `f` on the closed upper part and satisfies the
reflection symmetry `F (conj z) = conj (F z)`. The explicit witness is `schwarzReflection f`. -/
theorem exists_differentiableOn_eqOn_conj_of_symmetric {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ Set.EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∧
      ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z) := by
  refine ⟨schwarzReflection f, differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont
    hholo hreal, ?_, ?_⟩
  · exact eqOn_schwarzReflection_of_subset_im_nonneg fun _ hz => hz.2
  · exact fun z hz => schwarzReflection_conj_of_real_on_axis hreal hz

/-- **Boundary zeros of a function real on the axis are isolated.** Let `f` be continuous on the
closed upper half of a disc about a real point `x`, holomorphic and zero-free on its open upper
half, and real on its diameter. Then `f` has no zeros in the closed upper half-plane near `x`,
except possibly at `x` itself. -/
theorem eventually_ne_zero_of_real_on_axis {x r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → (f z).im = 0)
    (hne : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → f z ≠ 0) :
    ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ), f z ≠ 0 := by
  -- reflect `f` across the diameter and use isolated zeros of the holomorphic extension
  obtain ⟨F, hFd, hFf, -⟩ := exists_differentiableOn_eqOn_conj_of_symmetric Metric.isOpen_ball
    (fun z hz => by rwa [Metric.mem_ball, ← Complex.conj_ofReal, Complex.dist_conj_conj]) hcont
    hholo hreal
  have hxr : Metric.ball (x : ℂ) r ∈ 𝓝 (x : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  rcases (hFd.analyticAt hxr).eventually_eq_zero_or_eventually_ne_zero with h | h
  · -- an extension vanishing near `x` would vanish somewhere in the upper half-plane
    have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
    obtain ⟨z, ⟨hz0, hzr⟩, hzH⟩ :=
      (((h.and hxr).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := {z : ℂ | 0 < z.im}))).exists
    exact absurd (hFf ⟨hzr, le_of_lt hzH⟩ ▸ hz0) (hne z hzr hzH)
  · have hsub : {z : ℂ | 0 ≤ z.im} \ {(x : ℂ)} ⊆ {(x : ℂ)}ᶜ := fun z hz => hz.2
    filter_upwards [h.filter_mono (nhdsWithin_mono _ hsub), mem_nhdsWithin_of_mem_nhds hxr,
      self_mem_nhdsWithin] with z hz hzr hzH
    rwa [← hFf ⟨hzr, hzH.1⟩]

/-- **A zero-free function does not vanish on a whole boundary interval.** Let `f` be continuous
on the closed upper half of a disc about a real point `x`, and holomorphic and zero-free on its
open upper half. Then `f` is nonzero somewhere on the diameter `(x - r, x + r)`. -/
theorem exists_mem_Ioo_ne_zero_of_ne_zero {x r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hne : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → f z ≠ 0) :
    ∃ y ∈ Ioo (x - r) (x + r), f y ≠ 0 := by
  by_contra! h
  -- a function vanishing on the diameter is real there, so its zero at `x` would be isolated
  have hreal (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) r) (hz0 : z.im = 0) : (f z).im = 0 := by
    have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    rw [Metric.mem_ball, dist_of_im_eq (by simp [hz0]), ofReal_re, Real.dist_eq,
      abs_sub_lt_iff] at hz
    rw [← hzx, h _ ⟨by linarith, by linarith⟩, zero_im]
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_ne_zero_of_real_on_axis hr hcont hholo hreal hne)
  have ht : 0 < min ε r / 2 := by positivity
  have htε : min ε r / 2 < ε := by linarith [min_le_left ε r]
  have htr : min ε r / 2 < r := by linarith [min_le_right ε r]
  refine hsub ⟨?_, ?_, ?_⟩ (h (x + min ε r / 2) ⟨by linarith, by linarith⟩)
  · simpa [dist_of_im_eq, Real.dist_eq, abs_of_pos (lt_min hε hr)] using htε
  · simp
  · simpa using ht.ne'

/-- **Boundary non-zeros on both sides of a point.** Let `f` be continuous on the closed upper half
of a disc of radius `r` about a real point `x`, and holomorphic and zero-free on its open upper
half. Then `f` is nonzero at a real point of `(x - r, x)` and at a real point of `(x, x + r)`. -/
theorem exists_lt_lt_ne_zero_of_ne_zero {x r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hne : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → f z ≠ 0) :
    ∃ y₁ y₂ : ℝ, x - r < y₁ ∧ y₁ < x ∧ x < y₂ ∧ y₂ < x + r ∧ f y₁ ≠ 0 ∧ f y₂ ≠ 0 := by
  -- apply `exists_mem_Ioo_ne_zero_of_ne_zero` to the half-radius discs about `x ± r / 2`
  have h (c : ℝ) (hc : |c - x| = r / 2) : ∃ y ∈ Ioo (c - r / 2) (c + r / 2), f y ≠ 0 := by
    have hsub : Metric.ball (c : ℂ) (r / 2) ⊆ Metric.ball (x : ℂ) r :=
      Metric.ball_subset_ball' (by rw [dist_of_im_eq (by simp)]; simp [Real.dist_eq, hc])
    exact exists_mem_Ioo_ne_zero_of_ne_zero (half_pos hr)
      (hcont.mono (inter_subset_inter_left _ hsub))
      (hholo.mono (inter_subset_inter_left _ hsub)) fun z hz => hne z (hsub hz)
  obtain ⟨y₁, ⟨h₁, h₁'⟩, hy₁⟩ := h (x - r / 2) (by rw [sub_sub_cancel_left, abs_neg,
    abs_of_pos (half_pos hr)])
  obtain ⟨y₂, ⟨h₂, h₂'⟩, hy₂⟩ := h (x + r / 2) (by rw [add_sub_cancel_left,
    abs_of_pos (half_pos hr)])
  exact ⟨y₁, y₂, by linarith, by linarith, by linarith, by linarith, hy₁, hy₂⟩

/-- **Boundary uniqueness on the real axis.** On a preconnected conjugation-symmetric open set
`Ω` meeting the real axis, a function continuous on the closed upper part, holomorphic on the
open upper part and vanishing on the real axis vanishes on the whole closed upper part. -/
theorem eqOn_zero_of_zero_on_real_axis {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω) {x : ℝ} (hx : (x : ℂ) ∈ Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hzero : ∀ z ∈ Ω, z.im = 0 → f z = 0) :
    EqOn f 0 (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
  obtain ⟨F, hFd, hFf, -⟩ := exists_differentiableOn_eqOn_conj_of_symmetric hΩopen hΩ hcont
    hholo fun z hz hz0 => by rw [hzero z hz hz0, zero_im]
  -- the extension vanishes at the real points of `Ω` accumulating at `x`
  have hreal : ∀ᶠ t : ℝ in 𝓝[≠] x, F t = 0 := by
    filter_upwards [nhdsWithin_le_nhds <| continuous_ofReal.continuousAt.preimage_mem_nhds
      (hΩopen.mem_nhds hx)] with t ht
    rw [hFf ⟨ht, by simp⟩, hzero _ ht (ofReal_im t)]
  have hmap : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_ofReal.tendsto x |>.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by simpa using ht)
  have hF0 := (hFd.analyticOnNhd hΩopen).eqOn_zero_of_preconnected_of_frequently_eq_zero hΩconn
    hx (hmap.frequently hreal.frequently)
  exact fun z hz => (hFf hz).symm.trans (hF0 hz.1)

/-- **Boundary uniqueness on an upper horizontal strip.** For `0 < c`, a function continuous
on the closed strip `0 ≤ im z ≤ c`, holomorphic on the open strip and vanishing on the real axis
vanishes on the closed strip. -/
theorem eqOn_zero_im_preimage_Icc_of_zero_on_real_axis {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn f (im ⁻¹' Icc 0 c)) (hholo : DifferentiableOn ℂ f (im ⁻¹' Ioo 0 c))
    (hzero : ∀ t : ℝ, f t = 0) : EqOn f 0 (im ⁻¹' Icc 0 c) := by
  -- reflect across the real axis inside the symmetric strip `-c < im z < c`
  have hsub : im ⁻¹' Ioo (-c) c ∩ {z : ℂ | 0 ≤ z.im} = im ⁻¹' Ico 0 c := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_Ioo, mem_Ico, mem_ofPred_eq]
    grind
  have hsub' : im ⁻¹' Ioo (-c) c ∩ {z : ℂ | 0 < z.im} = im ⁻¹' Ioo 0 c := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_Ioo, mem_ofPred_eq]
    grind
  have hlow := eqOn_zero_of_zero_on_real_axis (isOpen_Ioo.preimage continuous_im)
    ((convex_Ioo (-c) c).linear_preimage imLm).isPreconnected
    (fun z hz => by simpa [and_comm, neg_lt, lt_neg] using hz) (x := 0) (by simp [hc])
    (hsub ▸ hcont.mono (preimage_mono Ico_subset_Icc_self)) (hsub' ▸ hholo)
    fun z _ hz => by rw [← re_add_im z, hz, ofReal_zero, zero_mul, add_zero, hzero]
  -- the top edge `im z = c` lies in the closure of `0 ≤ im z < c`
  refine (hsub ▸ hlow).of_subset_closure hcont continuousOn_const
    (preimage_mono Ico_subset_Icc_self) ?_
  rw [closure_preimage_im, closure_Ico hc.ne]

/-- **Boundary uniqueness on a horizontal strip.** A function continuous on the closed strip
between the real axis and the line `im z = c`, holomorphic on the open strip and vanishing on
the real axis vanishes on the closed strip. Both signs of `c` are allowed; for `c = 0` the strip
is the real axis. -/
theorem eqOn_zero_im_preimage_uIcc_of_zero_on_real_axis {c : ℝ}
    (hcont : ContinuousOn f (im ⁻¹' uIcc 0 c)) (hholo : DifferentiableOn ℂ f (im ⁻¹' uIoo 0 c))
    (hzero : ∀ t : ℝ, f t = 0) : EqOn f 0 (im ⁻¹' uIcc 0 c) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · -- reflect the lower strip through the origin
    have hg := eqOn_zero_im_preimage_Icc_of_zero_on_real_axis (f := fun z => f (-z))
      (neg_pos.mpr hc)
      (hcont.comp continuous_neg.continuousOn fun z hz => by
        simp only [mem_preimage, mem_Icc, uIcc_of_ge hc.le, neg_im] at hz ⊢
        constructor <;> linarith [hz.1, hz.2])
      (hholo.comp differentiable_neg.differentiableOn fun z hz => by
        simp only [mem_preimage, mem_Ioo, uIoo_of_ge hc.le, neg_im] at hz ⊢
        constructor <;> linarith [hz.1, hz.2])
      fun t => by simpa using hzero (-t)
    intro z hz
    simpa using hg (x := -z) (by simpa [uIcc_of_ge hc.le, and_comm, le_neg] using hz)
  · intro z hz
    rw [mem_preimage, uIcc_self, mem_singleton_iff] at hz
    rw [← re_add_im z, hz, ofReal_zero, zero_mul, add_zero, hzero, Pi.zero_apply]
  · simpa [uIcc_of_le hc.le, uIoo_of_le hc.le] using
      eqOn_zero_im_preimage_Icc_of_zero_on_real_axis hc (by simpa [uIcc_of_le hc.le] using hcont)
        (by simpa [uIoo_of_le hc.le] using hholo) hzero

end TauCeti
