/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Horizontal strips

Positive real scalings and complex translations map horizontal strips bijectively
onto the strips whose endpoints undergo the corresponding real affine map. These
maps rescale logarithmic strip coordinates to arbitrary boundary heights.

A map recovered up to integer multiples of `i`, such as an exponential end lift of a
cylindrical end, is injective on every horizontal strip of height one
(`TauCeti.Complex.injOn_of_exists_eq_add_intCast_mul_I`).
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

/-- A map `f` on `ℂ` whose composite with some `g` recovers every point up to an integer multiple
of `i` is injective on every horizontal strip `t₀ ≤ Im z < t₀ + 1` of height one: two points with
the same image differ by an integer multiple of `i`. This is the injectivity of the exponential
end lifts of cylindrical ends, with `g` a logarithmic end coordinate. -/
theorem injOn_of_exists_eq_add_intCast_mul_I {α : Type*} {f : ℂ → α} {g : α → ℂ}
    (h : ∀ z, ∃ k : ℤ, g (f z) = z + k * Complex.I) (t₀ : ℝ) :
    InjOn f {z | z.im ∈ Ico t₀ (t₀ + 1)} := by
  intro a ha b hb hab
  replace ha : t₀ ≤ a.im ∧ a.im < t₀ + 1 := ha
  replace hb : t₀ ≤ b.im ∧ b.im < t₀ + 1 := hb
  obtain ⟨k, hk⟩ := h a
  obtain ⟨l, hl⟩ := h b
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
