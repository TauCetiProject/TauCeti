/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Convex
import TauCeti.Topology.Frontier

/-!
# Horizontal strips

Positive real scalings and complex translations map horizontal strips bijectively
onto the strips whose endpoints undergo the corresponding real affine map. These
maps rescale logarithmic strip coordinates to arbitrary boundary heights.

A map recovered up to integer multiples of `i`, such as an exponential end lift of a
cylindrical end, is injective on every set whose imaginary parts vary by less than one, such as a
horizontal strip of height one (`TauCeti.Complex.injOn_of_exists_eq_add_intCast_mul_I`).

An open set of the plane whose frontier is, to the right of some `R`, exactly the two horizontal
lines bounding a strip, and which misses a point of the strip to the right of `R`, agrees to the
right of `R` with the complement of the closed strip.
-/

public section

namespace TauCeti

open Complex Set

/-- A positive real scaling followed by a complex translation maps a horizontal strip
bijectively onto the strip with the transformed imaginary endpoints. -/
theorem bijOn_ofReal_mul_add_horizontalStrip {s : ℝ} (hs : 0 < s) (c : ℂ) (l h : ℝ) :
    BijOn (fun w : ℂ => (s : ℂ) * w + c)
      {w : ℂ | w.im ∈ Ioo l h} {w : ℂ | w.im ∈ Ioo (s * l + c.im) (s * h + c.im)} :=
  ((Equiv.mulLeft₀ (s : ℂ) (ofReal_ne_zero.mpr hs.ne')).trans (Equiv.addRight c)).bijOn
    fun w => by simp [hs]

end TauCeti

namespace TauCeti.Complex

open Set

/-- A map `f` on `ℂ` whose composite with some `g` recovers every point of a set `s` up to an
integer multiple of `i` is injective on `s` if the imaginary parts of any two points of `s` differ
by less than one: two points with the same image differ by an integer multiple of `i`. This is the
injectivity of the exponential end lifts of cylindrical ends on horizontal strips of height one,
with `g` a logarithmic end coordinate. -/
theorem injOn_of_exists_eq_add_intCast_mul_I {α : Type*} {f : ℂ → α} {g : α → ℂ} {s : Set ℂ}
    (h : ∀ z ∈ s, ∃ k : ℤ, g (f z) = z + k * Complex.I)
    (hs : ∀ a ∈ s, ∀ b ∈ s, a.im - b.im ∈ Ioo (-1) 1) :
    InjOn f s := by
  intro a ha b hb hab
  obtain ⟨hlo, hhi⟩ := hs a ha b hb
  obtain ⟨k, hk⟩ := h a ha
  obtain ⟨l, hl⟩ := h b hb
  rw [hab, hl] at hk
  -- The real parts agree, and the imaginary parts differ by the integer `l - k`.
  have hre := congrArg Complex.re hk
  have him := congrArg Complex.im hk
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im] at hre him
  have hlt : |((l - k : ℤ) : ℝ)| < 1 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, sub_eq_zero] at hlt
  subst hlt
  exact Complex.ext (by linarith) (by linarith)

end TauCeti.Complex

namespace IsPreconnected

open Complex Set

/-- If, to the right of `R`, the frontier of a set `U ⊆ ℂ` lies on the two horizontal lines at
heights `a` and `b`, then a preconnected set `s` lying to the right of `R` and avoiding both lines
is contained in `U` as soon as it meets `U`. -/
theorem subset_of_forall_mem_frontier_im_eq_or_eq {U s : Set ℂ} {R a b : ℝ}
    (hs : IsPreconnected s) (hfr : ∀ w ∈ frontier U, R < w.re → w.im = a ∨ w.im = b)
    (havoid : ∀ w ∈ s, R < w.re ∧ w.im ≠ a ∧ w.im ≠ b) (hmeet : (s ∩ U).Nonempty) : s ⊆ U :=
  hs.subset_of_disjoint_frontier (Set.disjoint_left.mpr fun w hw hwfr =>
    let h := havoid w hw
    (hfr w hwfr h.1).elim h.2.1 h.2.2) hmeet

end IsPreconnected

namespace IsOpen

open Complex Set

/-- If the frontier of an open set `U ⊆ ℂ` is, to the right of `R`, exactly the two horizontal
lines at heights `lo` and `hi`, and a point `z` of the band between them to the right of `R` is not
in `U`, then every point of `U` to the right of `R` lies strictly below or strictly above the
band. -/
private theorem im_lt_or_lt_im_of_mem_of_mem_frontier_iff_im_eq_or_eq {U : Set ℂ}
    (hUo : IsOpen U) {R hi lo : ℝ}
    (hline : ∀ w : ℂ, R < w.re → (w ∈ frontier U ↔ w.im = hi ∨ w.im = lo)) {z : ℂ}
    (hzR : R < z.re) (hzlo : lo < z.im) (hzhi : z.im < hi) (hz : z ∉ U) {w : ℂ} (hwR : R < w.re)
    (hwU : w ∈ U) : w.im < lo ∨ hi < w.im := by
  have hne : w ∉ frontier U := by
    rw [hUo.frontier_eq]
    exact fun h => h.2 hwU
  rw [hline w hwR, not_or] at hne
  by_contra! hw
  have hS := (convex_halfSpace_re_gt R).inter ((convex_halfSpace_im_gt lo).inter
    (convex_halfSpace_im_lt hi)) |>.isPreconnected.subset_of_forall_mem_frontier_im_eq_or_eq
    (fun v hv hvR => (hline v hvR).mp hv) (fun v hv => ⟨hv.1, hv.2.2.ne, hv.2.1.ne'⟩)
    ⟨w, ⟨hwR, lt_of_le_of_ne hw.1 (Ne.symm hne.2), lt_of_le_of_ne hw.2 hne.1⟩, hwU⟩
  exact hz (hS ⟨hzR, hzlo, hzhi⟩)

/-- If the frontier of an open set `U ⊆ ℂ` is, to the right of `R`, exactly the two horizontal
lines at heights `lo` and `hi`, and a point `z` of the band between them to the right of `R` is
not in `U`, then to the right of `R` the set `U` is exactly the set of points strictly below or
strictly above the band. -/
theorem mem_iff_im_lt_or_lt_im_of_mem_frontier_iff_im_eq_or_eq {U : Set ℂ} (hUo : IsOpen U)
    {R hi lo : ℝ} (hline : ∀ w : ℂ, R < w.re → (w ∈ frontier U ↔ w.im = hi ∨ w.im = lo))
    {z : ℂ} (hzR : R < z.re) (hzlo : lo < z.im) (hzhi : z.im < hi) (hz : z ∉ U) {w : ℂ}
    (hwR : R < w.re) : w ∈ U ↔ w.im < lo ∨ hi < w.im := by
  have hgap : lo < hi := hzlo.trans hzhi
  have hfr (v : ℂ) (hv : v ∈ frontier U) (hvR : R < v.re) : v.im = hi ∨ v.im = lo :=
    (hline v hvR).mp hv
  have hout {w : ℂ} (hwR : R < w.re) (hwU : w ∈ U) : w.im < lo ∨ hi < w.im :=
    im_lt_or_lt_im_of_mem_of_mem_frontier_iff_im_eq_or_eq hUo hline hzR hzlo hzhi hz hwR hwU
  -- Each line lies in the closure of `U`, so `U` meets every open set around a point of it.
  have hcl (h : ℝ) (hh : h = hi ∨ h = lo) : (⟨R + 1, h⟩ : ℂ) ∈ closure U :=
    frontier_subset_closure ((hline _ (lt_add_one R)).mpr hh)
  have habove : {w : ℂ | R < w.re ∧ hi < w.im} ⊆ U := by
    obtain ⟨u, ⟨huR, hulo⟩, huU⟩ := mem_closure_iff.mp (hcl hi (Or.inl rfl)) _
      ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im))
      ⟨lt_add_one R, hgap⟩
    exact ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_gt hi)).isPreconnected.subset_of_forall_mem_frontier_im_eq_or_eq hfr
      (fun v hv => ⟨hv.1, hv.2.ne', (hgap.trans hv.2).ne'⟩)
      ⟨u, ⟨huR, (hout huR huU).resolve_left hulo.not_gt⟩, huU⟩
  have hbelow : {w : ℂ | R < w.re ∧ w.im < lo} ⊆ U := by
    obtain ⟨u, ⟨huR, huhi⟩, huU⟩ := mem_closure_iff.mp (hcl lo (Or.inr rfl)) _
      ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const))
      ⟨lt_add_one R, hgap⟩
    exact ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_lt lo)).isPreconnected.subset_of_forall_mem_frontier_im_eq_or_eq hfr
      (fun v hv => ⟨hv.1, (hv.2.trans hgap).ne, hv.2.ne⟩)
      ⟨u, ⟨huR, (hout huR huU).resolve_right huhi.not_gt⟩, huU⟩
  exact ⟨hout hwR, fun hw => hw.elim (fun h => hbelow ⟨hwR, h⟩) (fun h => habove ⟨hwR, h⟩)⟩

end IsOpen
