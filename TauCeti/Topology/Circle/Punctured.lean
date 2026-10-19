/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Basic

/-!
# The punctured circle contracts onto a point

The circle with the point `-1` removed deformation retracts onto `1`: for `z ≠ -1` the chord from
`z` to `1` never meets the closed negative real axis, in particular never meets `0`, so its radial
projection back to the circle is a path from `z` to `1` avoiding `-1`.  These paths depend
continuously on `z` and are constant at `z = 1`, which gives a homotopy relative to `{1}` from the
identity of `Circle ∖ {-1}` to the constant map at `1`.

A deformation retraction of a neighbourhood of the base point onto it is what the computation of
the fundamental group of a wedge of circles needs from each circle.

## Main declarations

* `TauCeti.circleChordHomotopy`: the deformation retraction of `Circle ∖ {-1}` onto `1`, with
  `TauCeti.coe_circleChordHomotopy_apply` its formula.
-/

public section

noncomputable section

namespace TauCeti

open unitInterval

/-- For `z ≠ -1` on the unit circle, the chord from `z` to `1` avoids the closed negative real
axis. -/
private lemma chord_mem_slitPlane {z : Circle} (hz : z ≠ -1) (t : I) :
    ((1 - t : ℝ) : ℂ) * z + (t : ℝ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra! h
  obtain ⟨hre, him⟩ := h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_im, Complex.mul_im, add_zero] at hre him
  have hn : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using Circle.normSq_coe z
  have ht0 := t.2.1
  have ht1 := t.2.2
  rcases mul_eq_zero.1 him with h1 | h1
  · rw [h1, zero_mul, zero_add] at hre
    linarith
  · have hre1 : (z : ℂ).re = -1 := by nlinarith
    exact hz (Circle.ext (Complex.ext (by simp [hre1]) (by simp [h1])))

/-- The radial projection of the chord from `z ≠ -1` to `1`, at time `t`. -/
private def chord (p : I × {z : Circle | z ≠ -1}) : Circle :=
  ⟨NormedSpace.normalize (((1 - p.1 : ℝ) : ℂ) * p.2.1 + (p.1 : ℝ)),
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize
      (Complex.slitPlane_ne_zero (chord_mem_slitPlane p.2.2 p.1)))⟩

private lemma chord_ne_neg_one (p : I × {z : Circle | z ≠ -1}) : chord p ≠ -1 := by
  intro h
  have hmem := chord_mem_slitPlane p.2.2 p.1
  set w := ((1 - p.1 : ℝ) : ℂ) * p.2.1 + (p.1 : ℝ)
  have hw : w = -(‖w‖ : ℂ) := by
    rw [← NormedSpace.norm_smul_normalize w]
    have h' := congrArg Subtype.val h
    simp only [chord, Circle.coe_neg, Circle.coe_one] at h'
    rw [h']
    simp [Complex.real_smul]
  rw [hw, Complex.neg_ofReal_mem_slitPlane] at hmem
  exact (norm_nonneg w).not_gt hmem

/-- **`Circle ∖ {-1}` deformation retracts onto `1`**: at time `t` a point `z ≠ -1` is moved to
the radial projection of the point `(1 - t) z + t` of the chord from `z` to `1`
(`TauCeti.coe_circleChordHomotopy_apply`).  The homotopy fixes `1` throughout. -/
def circleChordHomotopy :
    (ContinuousMap.id {z : Circle | z ≠ -1}).HomotopyRel
      (.const _ ⟨1, (Circle.neg_ne_self 1).symm⟩) {⟨1, (Circle.neg_ne_self 1).symm⟩} where
  toFun p := ⟨chord p, chord_ne_neg_one p⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have hc : Continuous fun p : I × {z : Circle | z ≠ -1} =>
        ((1 - p.1 : ℝ) : ℂ) * p.2.1 + (p.1 : ℝ) := by fun_prop
    have h0 (p : I × {z : Circle | z ≠ -1}) : ((1 - p.1 : ℝ) : ℂ) * p.2.1 + (p.1 : ℝ) ≠ 0 :=
      Complex.slitPlane_ne_zero (chord_mem_slitPlane p.2.2 p.1)
    exact (continuous_subtype_val.comp (normalizeToSphere _ hc h0).continuous).congr fun p =>
      coe_normalizeToSphere_apply _ hc h0 p
  map_zero_left z := by
    refine Subtype.ext (Circle.ext ?_)
    simp [chord, NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe z.1)]
  map_one_left z := by
    refine Subtype.ext (Circle.ext ?_)
    simp [chord, NormedSpace.normalize_eq_self_of_norm_eq_one (norm_one (α := ℂ))]
  prop' t z hz := by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine Subtype.ext (Circle.ext ?_)
    simp [chord, NormedSpace.normalize_eq_self_of_norm_eq_one (norm_one (α := ℂ))]

@[simp]
lemma coe_circleChordHomotopy_apply (t : I) (z : {z : Circle | z ≠ -1}) :
    ((circleChordHomotopy (t, z) : Circle) : ℂ) =
      NormedSpace.normalize (((1 - t : ℝ) : ℂ) * z.1 + (t : ℝ)) :=
  (rfl)

end TauCeti
