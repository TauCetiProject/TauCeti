/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Holomorphy
import TauCeti.Analysis.Complex.CutPlaneIdentity
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Continuing Euler's integral by a fixed number of contiguous shifts

Euler's integral `Complex.eulerIntegral a b c z` (DLMF 15.6.1) represents the regularized Gauss
function `𝐅(a, b; c; z)` only where `0 < re b < re c`. The two regularized contiguous relations

* `𝐅(a, b; c; z) = (c - a) 𝐅(a, b; c + 1; z) + a 𝐅(a + 1, b; c + 1; z)` (DLMF 15.5.15),
* `𝐅(a, b; c; z) = 𝐅(a, b + 1; c; z) - a z 𝐅(a + 1, b + 1; c + 1; z)` (DLMF 15.5.16_5),

raise `re (c - b)`, respectively `re b`, by one on their right-hand sides. Applying the shift in `b`
`p` times and the shift in `c` `q` times to Euler's integral gives a function
`Complex.eulerIntegralShift p q` of `(a, b, c, z)`, defined by structural recursion with fixed
counts `p` and `q`. It is holomorphic on the open region `Complex.eulerIntegralShiftRegion p q`
where `-p < re b`, `p - q < re (c - b)` and `1 - z ∈ slitPlane`.

On the part of its region inside the unit disk, each `eulerIntegralShift p q` is the series
`Complex.regularizedGaussHGFun`, by induction from Euler's integral representation and the two
contiguous relations of the series.
The identity principle in `z` on the cut plane then shows that `eulerIntegralShift p q` agrees
with Euler's integral where `0 < re b < re c`, and that two such functions with different counts
agree where both regions contain the point. Every point of `ℂ × ℂ × ℂ × {1 - z ∈ slitPlane}` lies
in some region `eulerIntegralShiftRegion p q`. These are the ingredients for gluing the
`eulerIntegralShift p q` into the regularized Gauss function on the cut plane.

The construction is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
files `DLMF/Hypergeometric/Basic/CutPlane.lean` and
`DLMF/Hypergeometric/Basic/PrincipalBranch.lean`,
where the number of shifts is chosen from the parameters. Here the counts are fixed, which makes
the joint holomorphy in all four variables an induction.

## Main definitions

* `Complex.eulerIntegralShift p q`: Euler's integral continued by `p` shifts in `b` and `q` shifts
  in `c`.
* `Complex.eulerIntegralShiftRegion p q`: the open region of `ℂ × ℂ × ℂ × ℂ` on which it is
  holomorphic.

## Main results

* `Complex.eulerIntegralShift_succ_left`, `Complex.eulerIntegralShift_succ_right`: the shift
  relations in `b` and in `c`, for all counts and all arguments.
* `Complex.analyticOnNhd_eulerIntegralShift`: joint holomorphy on `eulerIntegralShiftRegion p q`.
* `Complex.eulerIntegralShift_eq_regularizedGaussHGFun`: agreement with the series on the region,
  inside the unit disk.
* `Complex.eulerIntegralShift_eq_eulerIntegral`: agreement with Euler's integral.
* `Complex.eulerIntegralShift_eq_eulerIntegralShift`: compatibility of different counts.
* `Complex.exists_mem_eulerIntegralShiftRegion`: the regions cover `ℂ³ × {1 - z ∈ slitPlane}`.

## References

* NIST Digital Library of Mathematical Functions, §15.5 and §15.6, equations 15.5.15, 15.5.16_5
  and 15.6.1.
-/

public section

open Set

namespace Complex

/-- Euler's integral continued by contiguous shifts with fixed counts: `p` shifts in `b`
(DLMF 15.5.16_5) and `q` shifts in `c` (DLMF 15.5.15), in the regularized form. The function
`eulerIntegralShift p q` is holomorphic on `eulerIntegralShiftRegion p q`, where it continues
`eulerIntegral` (see `Complex.eulerIntegralShift_eq_eulerIntegral`). -/
noncomputable def eulerIntegralShift : ℕ → ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 0, 0, a, b, c, z => eulerIntegral a b c z
  | 0, q + 1, a, b, c, z =>
    (c - a) * eulerIntegralShift 0 q a b (c + 1) z + a * eulerIntegralShift 0 q (a + 1) b (c + 1) z
  | p + 1, q, a, b, c, z =>
    eulerIntegralShift p q a (b + 1) c z - a * z * eulerIntegralShift p q (a + 1) (b + 1) (c + 1) z

/-- The region `-p < re b`, `p - q < re (c - b)`, `1 - z ∈ slitPlane` of points `(a, b, c, z)`
on which `eulerIntegralShift p q` is holomorphic. -/
def eulerIntegralShiftRegion (p q : ℕ) : Set (ℂ × ℂ × ℂ × ℂ) :=
  {x | -(p : ℝ) < x.2.1.re ∧ (p : ℝ) - q < x.2.2.1.re - x.2.1.re ∧ 1 - x.2.2.2 ∈ slitPlane}

/-- Membership in `eulerIntegralShiftRegion p q`, in terms of the coordinates of the point. -/
@[simp]
theorem mem_eulerIntegralShiftRegion {p q : ℕ} {x : ℂ × ℂ × ℂ × ℂ} :
    x ∈ eulerIntegralShiftRegion p q ↔
      -(p : ℝ) < x.2.1.re ∧ (p : ℝ) - q < x.2.2.1.re - x.2.1.re ∧ 1 - x.2.2.2 ∈ slitPlane :=
  Iff.rfl

/-- The region `eulerIntegralShiftRegion p q` is open. -/
theorem isOpen_eulerIntegralShiftRegion (p q : ℕ) : IsOpen (eulerIntegralShiftRegion p q) :=
  (isOpen_lt continuous_const (by fun_prop : Continuous fun x : ℂ × ℂ × ℂ × ℂ ↦ x.2.1.re)).inter
    ((isOpen_lt continuous_const
      (by fun_prop : Continuous fun x : ℂ × ℂ × ℂ × ℂ ↦ x.2.2.1.re - x.2.1.re)).inter
    (isOpen_slitPlane.preimage (by fun_prop : Continuous fun x : ℂ × ℂ × ℂ × ℂ ↦ 1 - x.2.2.2)))

/-- The regions grow with `p` as long as `p - q` does not increase. -/
theorem eulerIntegralShiftRegion_subset {p q p' q' : ℕ} (hp : p ≤ p') (hpq : p' + q ≤ p + q') :
    eulerIntegralShiftRegion p q ⊆ eulerIntegralShiftRegion p' q' := by
  rintro ⟨a, b, c, z⟩ ⟨hb, hcb, hz⟩
  have hp' : (p : ℝ) ≤ p' := by exact_mod_cast hp
  have hpq' : (p' : ℝ) + q ≤ p + q' := by exact_mod_cast hpq
  exact ⟨by linarith, by linarith, hz⟩

/-- Every point of `ℂ × ℂ × ℂ × {1 - z ∈ slitPlane}` lies in some region
`eulerIntegralShiftRegion p q`. -/
theorem exists_mem_eulerIntegralShiftRegion (a b c : ℂ) {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    ∃ p q : ℕ, (a, b, c, z) ∈ eulerIntegralShiftRegion p q := by
  refine ⟨⌈-b.re⌉₊ + 1, ⌈-b.re⌉₊ + 1 + ⌈b.re - c.re⌉₊ + 1, ?_, ?_, hz⟩
  · have := Nat.le_ceil (-b.re)
    push_cast
    linarith
  · have := Nat.le_ceil (b.re - c.re)
    push_cast
    linarith

/-- The shift in `c` reads `eulerIntegralShift p q` at a point of its region. -/
theorem mem_eulerIntegralShiftRegion_shift_c {p q : ℕ} {a b c z : ℂ} (a' : ℂ)
    (h : (a, b, c, z) ∈ eulerIntegralShiftRegion p (q + 1)) :
    (a', b, c + 1, z) ∈ eulerIntegralShiftRegion p q := by
  obtain ⟨hb, hcb, hz⟩ := h
  refine ⟨hb, ?_, hz⟩
  simp only [add_re, one_re]
  push_cast at hcb
  linarith

/-- The first term of the shift in `b` reads `eulerIntegralShift p q` at a point of its
region. -/
theorem mem_eulerIntegralShiftRegion_shift_b {p q : ℕ} {a b c z : ℂ} (a' : ℂ)
    (h : (a, b, c, z) ∈ eulerIntegralShiftRegion (p + 1) q) :
    (a', b + 1, c, z) ∈ eulerIntegralShiftRegion p q := by
  obtain ⟨hb, hcb, hz⟩ := h
  refine ⟨?_, ?_, hz⟩ <;> simp only [add_re, one_re] <;> push_cast at hb hcb <;> linarith

/-- The second term of the shift in `b` reads `eulerIntegralShift p q` at a point of its
region. -/
theorem mem_eulerIntegralShiftRegion_shift_bc {p q : ℕ} {a b c z : ℂ} (a' : ℂ)
    (h : (a, b, c, z) ∈ eulerIntegralShiftRegion (p + 1) q) :
    (a', b + 1, c + 1, z) ∈ eulerIntegralShiftRegion p q := by
  obtain ⟨hb, hcb, hz⟩ := h
  refine ⟨?_, ?_, hz⟩ <;> simp only [add_re, one_re] <;> push_cast at hb hcb <;> linarith

/-- With no shifts, `eulerIntegralShift 0 0` is Euler's integral. -/
@[simp]
theorem eulerIntegralShift_zero_zero (a b c z : ℂ) :
    eulerIntegralShift 0 0 a b c z = eulerIntegral a b c z := by
  rw [eulerIntegralShift]

/-- The shift relation in `b` (DLMF 15.5.16_5), which defines `eulerIntegralShift (p + 1) q`. -/
theorem eulerIntegralShift_succ_left (p q : ℕ) (a b c z : ℂ) :
    eulerIntegralShift (p + 1) q a b c z =
      eulerIntegralShift p q a (b + 1) c z -
        a * z * eulerIntegralShift p q (a + 1) (b + 1) (c + 1) z := by
  rw [eulerIntegralShift]

/-- The shift relation in `c` (DLMF 15.5.15). For `p = 0` it is the definition of
`eulerIntegralShift 0 (q + 1)`; for `p > 0` it holds because the shifts in `b` and in `c`
commute. -/
theorem eulerIntegralShift_succ_right (p q : ℕ) (a b c z : ℂ) :
    eulerIntegralShift p (q + 1) a b c z =
      (c - a) * eulerIntegralShift p q a b (c + 1) z +
        a * eulerIntegralShift p q (a + 1) b (c + 1) z := by
  induction p generalizing a b c with
  | zero => rw [eulerIntegralShift]
  | succ p ih =>
    simp only [eulerIntegralShift_succ_left, ih]
    ring

/-- `eulerIntegralShift p q` is holomorphic in `(a, b, c, z)` jointly on
`eulerIntegralShiftRegion p q`. -/
theorem analyticOnNhd_eulerIntegralShift (p q : ℕ) :
    AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ × ℂ ↦ eulerIntegralShift p q x.1 x.2.1 x.2.2.1 x.2.2.2)
      (eulerIntegralShiftRegion p q) := by
  induction p generalizing q with
  | zero =>
    induction q with
    | zero =>
      simp only [eulerIntegralShift_zero_zero]
      refine analyticOnNhd_eulerIntegral_joint.mono ?_
      rintro ⟨a, b, c, z⟩ ⟨hb, hcb, hz⟩
      simp only [CharP.cast_eq_zero, neg_zero, sub_zero] at hb hcb
      exact ⟨hb, by linarith, hz⟩
    | succ q ih =>
      have h₁ := ih.comp (f := fun x : ℂ × ℂ × ℂ × ℂ ↦ (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2))
        (Differentiable.analyticOnNhd_of_finiteDimensional (by fun_prop))
          fun x hx ↦ mem_eulerIntegralShiftRegion_shift_c x.1 hx
      have h₂ := ih.comp (f := fun x : ℂ × ℂ × ℂ × ℂ ↦ (x.1 + 1, x.2.1, x.2.2.1 + 1, x.2.2.2))
        (Differentiable.analyticOnNhd_of_finiteDimensional (by fun_prop))
          fun x hx ↦ mem_eulerIntegralShiftRegion_shift_c (x.1 + 1) hx
      simp only [eulerIntegralShift_succ_right]
      exact ((Differentiable.analyticOnNhd_of_finiteDimensional (f := fun x ↦ x.2.2.1 - x.1)
        (by fun_prop)).mul h₁).add
          ((Differentiable.analyticOnNhd_of_finiteDimensional (f := fun x ↦ x.1)
            (by fun_prop)).mul h₂)
  | succ p ih =>
    have h₁ := (ih q).comp (f := fun x : ℂ × ℂ × ℂ × ℂ ↦ (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2))
      (Differentiable.analyticOnNhd_of_finiteDimensional (by fun_prop))
        fun x hx ↦ mem_eulerIntegralShiftRegion_shift_b x.1 hx
    have h₂ := (ih q).comp
      (f := fun x : ℂ × ℂ × ℂ × ℂ ↦ (x.1 + 1, x.2.1 + 1, x.2.2.1 + 1, x.2.2.2))
      (Differentiable.analyticOnNhd_of_finiteDimensional (by fun_prop))
        fun x hx ↦ mem_eulerIntegralShiftRegion_shift_bc (x.1 + 1) hx
    simp only [eulerIntegralShift_succ_left]
    exact h₁.sub ((Differentiable.analyticOnNhd_of_finiteDimensional
      (f := fun x ↦ x.1 * x.2.2.2) (by fun_prop)).mul h₂)

/-- On its region `eulerIntegralShiftRegion p q`, inside the unit disk, `eulerIntegralShift p q`
is the regularized Gauss series. -/
theorem eulerIntegralShift_eq_regularizedGaussHGFun {p q : ℕ} {a b c z : ℂ}
    (hb : -(p : ℝ) < b.re) (hcb : (p : ℝ) - q < c.re - b.re) (hz : ‖z‖ < 1) :
    eulerIntegralShift p q a b c z = regularizedGaussHGFun a b c z := by
  have hzs : 1 - z ∈ slitPlane := by
    simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)
  suffices h : ∀ {p q : ℕ} {a b c : ℂ}, (a, b, c, z) ∈ eulerIntegralShiftRegion p q →
      eulerIntegralShift p q a b c z = regularizedGaussHGFun a b c z from h ⟨hb, hcb, hzs⟩
  intro p q a b c hx
  induction p generalizing q a b c with
  | zero =>
    induction q generalizing a b c with
    | zero =>
      obtain ⟨hb, hcb, -⟩ := hx
      simp only [CharP.cast_eq_zero, neg_zero, sub_zero] at hb hcb
      rw [eulerIntegralShift_zero_zero,
        regularizedGaussHGFun_eq_eulerIntegral a hb (by linarith) hz]
    | succ q ih =>
      rw [eulerIntegralShift_succ_right, ih (mem_eulerIntegralShiftRegion_shift_c a hx),
        ih (mem_eulerIntegralShiftRegion_shift_c (a + 1) hx),
        ← regularizedGaussHGFun_eq_sub_mul_add_mul a b c hz]
  | succ p ih =>
    rw [eulerIntegralShift_succ_left, ih (mem_eulerIntegralShiftRegion_shift_b a hx),
      ih (mem_eulerIntegralShiftRegion_shift_bc (a + 1) hx),
      ← regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b c hz]

/-- On its region, `eulerIntegralShift p q` agrees with Euler's integral where
`0 < re b < re c`. -/
theorem eulerIntegralShift_eq_eulerIntegral {p q : ℕ} {a b c z : ℂ}
    (hx : (a, b, c, z) ∈ eulerIntegralShiftRegion p q) (hb : 0 < b.re) (hbc : b.re < c.re) :
    eulerIntegralShift p q a b c z = eulerIntegral a b c z :=
  AnalyticOnNhd.comp_eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball (ι := fun w ↦ (a, b, c, w))
    (analyticOnNhd_eulerIntegralShift p q) analyticOnNhd_eulerIntegral_joint (by fun_prop)
    (fun _ hw ↦ ⟨hx.1, hx.2.1, hw⟩) (fun _ hw ↦ ⟨hb, hbc, hw⟩)
    (fun _ hw ↦ (eulerIntegralShift_eq_regularizedGaussHGFun hx.1 hx.2.1
      (mem_ball_zero_iff.mp hw)).trans
      (regularizedGaussHGFun_eq_eulerIntegral a hb hbc (mem_ball_zero_iff.mp hw))) hx.2.2

/-- Compatibility of different counts: `eulerIntegralShift p q` and `eulerIntegralShift p' q'`
agree where both regions contain the point. -/
theorem eulerIntegralShift_eq_eulerIntegralShift {p q p' q' : ℕ} {a b c z : ℂ}
    (hx : (a, b, c, z) ∈ eulerIntegralShiftRegion p q)
    (hx' : (a, b, c, z) ∈ eulerIntegralShiftRegion p' q') :
    eulerIntegralShift p q a b c z = eulerIntegralShift p' q' a b c z :=
  AnalyticOnNhd.comp_eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball (ι := fun w ↦ (a, b, c, w))
    (analyticOnNhd_eulerIntegralShift p q) (analyticOnNhd_eulerIntegralShift p' q') (by fun_prop)
    (fun _ hw ↦ ⟨hx.1, hx.2.1, hw⟩) (fun _ hw ↦ ⟨hx'.1, hx'.2.1, hw⟩)
    (fun _ hw ↦ (eulerIntegralShift_eq_regularizedGaussHGFun hx.1 hx.2.1
      (mem_ball_zero_iff.mp hw)).trans
      (eulerIntegralShift_eq_regularizedGaussHGFun hx'.1 hx'.2.1 (mem_ball_zero_iff.mp hw)).symm)
    hx.2.2

end Complex
