/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Coordinate
public import TauCeti.Analysis.Complex.UpperHalfPlane.Log
import TauCeti.Analysis.Complex.Conformal.Reflection.LocalImage
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Half-strip images at logarithmic Schwarz--Christoffel ends

Near a finite real prevertex of total exponent `-1`, a translated primitive divided by its
prevertex coefficient maps a small upper half-disc into the strip `0 < im w < π`.
Sufficiently far to the left, it maps bijectively onto the whole half-strip. In particular,
this identifies the interior geometry of an individual parallel-sided end, without global
univalence or assumptions on the other prevertices.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private theorem exists_log_coordinate (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) {R : ℝ} (hR : 0 < R) :
    ∃ (c : ℂ) (G : ℂ → ℂ) (r : ℝ), r ∈ Ioo 0 R ∧
      InjOn G (ball (p : ℂ) r) ∧
      MapsTo G (ball (p : ℂ) r ∩ upperHalfPlaneSet) upperHalfPlaneSet ∧
      EqOn (fun z => (schwarzChristoffelPrimitive a e z₀ z - c) /
        schwarzChristoffelPrevertexCoefficient a e p) (fun z => log (G z))
        (ball (p : ℂ) r ∩ upperHalfPlaneSet) ∧
      ∃ δ : ℝ, 0 < δ ∧
        (G '' (ball (p : ℂ) r ∩ upperHalfPlaneSet)) ∩ ball 0 δ =
          ball 0 δ ∩ upperHalfPlaneSet := by
  obtain ⟨c, G, s, hs, hGan, _, hGp, hGder, hGsym, hGexp⟩ :=
    exists_analyticOnNhd_injOn_exp_schwarzChristoffelPrimitive_of_sum_eq_neg_one a e z₀ p he
  have hstrict : HasStrictDerivAt G (1 : ℂ) (p : ℂ) := by
    simpa only [hGder.deriv] using (hGan _ (mem_ball_self hs)).hasStrictDerivAt
  have hsym : ∀ᶠ z in 𝓝 (p : ℂ), G (conj z) = conj (G z) :=
    eventually_nhds_iff_ball.mpr ⟨s, hs, hGsym⟩
  obtain ⟨t, ht, hsign⟩ := Metric.eventually_nhds_iff.mp
    (hstrict.eventually_im_pos_iff_of_conj (by norm_num) hsym)
  have hsmall : 0 < min R (min s t) := lt_min hR (lt_min hs ht)
  obtain ⟨r, hr, hinj, δ, hδ, himage⟩ :=
    hstrict.exists_ball_image_inter_upperHalfPlane_of_conj (by norm_num) hsym hsmall
  have hrs : r ≤ s := hr.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt : r ≤ t := hr.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmaps : MapsTo G (ball (p : ℂ) r ∩ upperHalfPlaneSet) upperHalfPlaneSet :=
    fun z hz => (hsign (ball_subset_ball hrt hz.1)).mpr hz.2
  let U := ball (p : ℂ) r ∩ upperHalfPlaneSet
  let C := schwarzChristoffelPrevertexCoefficient a e p
  let N : ℂ → ℂ := fun z => (schwarzChristoffelPrimitive a e z₀ z - c) / C
  have hC : C ≠ 0 := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
  have hopen : IsOpen U := isOpen_ball.inter isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected U :=
    ((convex_ball (p : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hexp : EqOn G (fun z => exp (N z)) U :=
    fun z hz => hGexp z ⟨ball_subset_ball hrs hz.1, hz.2⟩
  have hNd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt N (schwarzChristoffelIntegrand a e z / C) z :=
    ((hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz.2).sub_const c).div_const C
  have hLd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun z => log (G z)) (schwarzChristoffelIntegrand a e z / C) z := by
    have hd := ((hNd z hz).cexp.congr_of_eventuallyEq
      (hexp.eventuallyEq_of_mem (hopen.mem_nhds hz))).clog
        (UpperHalfPlane.mem_slitPlane ⟨G z, hmaps hz⟩)
    apply hd.congr_deriv
    rw [hexp hz]
    field_simp [exp_ne_zero]
  -- The principal logarithm differs from the original normalized primitive by a constant.
  -- Absorb it into the target translation, rather than choosing a logarithm branch by hand.
  obtain ⟨k, hk⟩ := hopen.exists_eq_add_of_deriv_eq hconn
    (fun z hz => (hNd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hNd z hz).deriv, (hLd z hz).deriv])
  refine ⟨c + C * k, G, r, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩,
    hinj, hmaps, ?_, δ, hδ, ?_⟩
  · intro z hz
    have h := hk hz
    dsimp only [N, C] at h
    dsimp only [C] at hC ⊢
    field_simp [hC] at h ⊢
    linear_combination h
  · simpa only [hGp] using himage

/-- **The interior of a logarithmic Schwarz--Christoffel end is an exact half-strip.**
For any prescribed source radius, a smaller upper half-disc maps into the strip of height
`π` after translation and division by the prevertex coefficient. Restricting to points
whose normalized image has sufficiently negative real part gives a bijection onto the
entire corresponding half-strip. Other prevertices may be nonintegrable, repeated, or
logarithmic, and global injectivity is not assumed. -/
theorem exists_bijOn_normalized_schwarzChristoffelPrimitive_halfStrip_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) {R : ℝ} (hR : 0 < R) :
    ∃ (c : ℂ) (r M : ℝ), r ∈ Ioo 0 R ∧
      MapsTo (fun z => (schwarzChristoffelPrimitive a e z₀ z - c) /
        schwarzChristoffelPrevertexCoefficient a e p)
        (ball (p : ℂ) r ∩ upperHalfPlaneSet) {w : ℂ | w.im ∈ Ioo 0 Real.pi} ∧
      BijOn (fun z => (schwarzChristoffelPrimitive a e z₀ z - c) /
        schwarzChristoffelPrevertexCoefficient a e p)
        ((ball (p : ℂ) r ∩ upperHalfPlaneSet) ∩
          {z | ((schwarzChristoffelPrimitive a e z₀ z - c) /
            schwarzChristoffelPrevertexCoefficient a e p).re < M})
        {w : ℂ | w.re < M ∧ w.im ∈ Ioo 0 Real.pi} := by
  obtain ⟨c, G, r, hr, hinj, hmaps, hlog, δ, hδ, himage⟩ :=
    exists_log_coordinate a e z₀ p he hR
  let N : ℂ → ℂ := fun z => (schwarzChristoffelPrimitive a e z₀ z - c) /
    schwarzChristoffelPrevertexCoefficient a e p
  have hNlog : EqOn N (fun z => log (G z))
      (ball (p : ℂ) r ∩ upperHalfPlaneSet) := hlog
  have hstrip : MapsTo N (ball (p : ℂ) r ∩ upperHalfPlaneSet)
      {w : ℂ | w.im ∈ Ioo 0 Real.pi} := by
    intro z hz
    rw [hNlog hz]
    exact bijOn_log_upperHalfPlaneSet.mapsTo (hmaps hz)
  refine ⟨c, r, Real.log δ, hr, hstrip, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨hz.2, hstrip hz.1⟩
  · intro z hz w hw hzw
    apply hinj hz.1.1 hw.1.1
    have h := congrArg exp hzw
    simpa only [hlog hz.1, hlog hw.1,
      exp_log (UpperHalfPlane.ne_zero ⟨G z, hmaps hz.1⟩),
      exp_log (UpperHalfPlane.ne_zero ⟨G w, hmaps hw.1⟩)] using h
  · intro w hw
    obtain ⟨u, hu, hlu⟩ := bijOn_log_upperHalfPlaneSet.surjOn hw.2
    have huexp : u = exp w := by
      rw [← hlu, exp_log (UpperHalfPlane.ne_zero ⟨u, hu⟩)]
    have huball : u ∈ ball (0 : ℂ) δ := by
      rw [huexp, mem_ball_zero_iff, norm_exp]
      exact (Real.exp_lt_exp.mpr hw.1).trans_eq (Real.exp_log hδ)
    have huimage : u ∈ G '' (ball (p : ℂ) r ∩ upperHalfPlaneSet) := by
      have hmem : u ∈ ball (0 : ℂ) δ ∩ upperHalfPlaneSet := ⟨huball, hu⟩
      rw [← himage] at hmem
      exact hmem.1
    obtain ⟨z, hz, hGz⟩ := huimage
    have hNz : N z = w := by
      rw [hNlog hz]
      simpa only [hGz] using hlu
    refine ⟨z, ⟨hz, ?_⟩, hNz⟩
    simpa only [mem_ofPred_eq, ← hNz, N] using hw.1

end TauCeti
