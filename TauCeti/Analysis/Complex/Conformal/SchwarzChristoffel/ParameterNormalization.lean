/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.AffineCovariance
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.JordanPolygon

/-!
# Normalized Schwarz--Christoffel parameters

Positive affine changes of the real line do not change the polygonal domain represented by a
Schwarz--Christoffel map.  This file uses that covariance to remove the two real affine degrees of
freedom from the prevertices: one chosen prevertex is placed at `0`, and the distance to a second
chosen prevertex is normalized to `1`.  Its sign is the remaining real-order choice under this
positive affine normalization.

The main theorem gives this normalization for the Schwarz--Christoffel representation of a
bounded polygonal Jordan domain.  Thus the remaining parameters live in a finite-dimensional
slice rather than carrying a redundant translation and positive scaling.

## Main results

* `TauCeti.exists_bijOn_normalized_schwarzChristoffelPrimitive_of_isJordanCurve_frontier` -- the
  Schwarz--Christoffel representation of a polygonal Jordan domain can be chosen with one
  prevertex equal to `0` and a second at distance `1`.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

noncomputable section

open Bornology Complex Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Normalized Schwarz--Christoffel parameters for a polygonal Jordan domain.**

Under the polygonal boundary hypotheses, choose two distinct labelled vertices `i` and `j`.
There is a Schwarz--Christoffel representation of the domain whose `i`-th prevertex is `0` and
whose `j`-th prevertex has absolute value `1`.  Its sign is the remaining real-order choice under
positive affine normalization. -/
theorem exists_bijOn_normalized_schwarzChristoffelPrimitive_of_isJordanCurve_frontier
    (e : ι → ℝ) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Function.Injective v)
    (hside : ∀ w ∈ frontier U, (∀ k, w ≠ v k) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ Metric.ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ k, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧
      ∀ z ∈ Metric.ball (v k) ρ, z ≠ v k →
        (z ∈ U ↔ |((z - v k) / b).arg| < (e k + 1) * Real.pi / 2))
    (i j : ι) (hij : i ≠ j) :
    ∃ a : ι → ℝ, Function.Injective a ∧ a i = 0 ∧ |a j| = 1 ∧
      ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
        BijOn (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
          upperHalfPlaneSet U ∧
        ∀ k, A * schwarzChristoffelVertex a e z₀ k + B = v k := by
  obtain ⟨a, ha, A, hA, B, hbij, hvertex⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
      e he z₀ hUo hUc hUb hUJ hv hside hcorner
  have hgap : a j - a i ≠ 0 := sub_ne_zero.mpr (ha.ne hij.symm)
  let c : ℝ := |a j - a i|⁻¹
  let d : ℝ := -c * a i
  have hc : 0 < c := inv_pos.mpr (abs_pos.mpr hgap)
  let a' : ι → ℝ := fun k ↦ c * a k + d
  have ha' : Function.Injective a' := fun k l hkl ↦ by
    dsimp only [a'] at hkl
    exact ha (mul_left_cancel₀ hc.ne' (add_right_cancel hkl))
  have hai : a' i = 0 := by
    dsimp only [a', d]
    ring
  have haj : |a' j| = 1 := by
    dsimp only [a', d]
    have habs : |c * a j + -c * a i| = c * |a j - a i| := by
      have h : c * a j + -c * a i = c * (a j - a i) := by ring
      rw [h, abs_mul, abs_of_pos hc]
    rw [habs]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr hgap)
  obtain ⟨A', hA', B', hbij', hvertex'⟩ :=
    exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices
      a e z₀ hc d hbij
  refine ⟨a', ha', hai, haj, A', hA', B', hbij', fun k ↦ ?_⟩
  have hsum : ∑ l with a l = a k, e l = e k := by
    classical
    rw [Finset.sum_eq_single_of_mem k (by simp) fun l hl hlk ↦
      absurd (ha (Finset.mem_filter.mp hl).2) hlk]
  rw [hvertex' k (by rw [hsum]; exact (he k).1), hvertex k]

end TauCeti

end
