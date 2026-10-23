/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompleteBernstein
import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Holomorphic
import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Pick

/-!
# Reciprocals of Stieltjes and complete Bernstein functions

A function is Stieltjes exactly when its reciprocal agrees on `(0, ∞)` with a complete Bernstein
function.  Equivalently, if `f` is complete Bernstein then so is its *conjugate*
`f*(t) = t / f(t)`.  This is the third correspondence between the two classes, alongside
`f ↦ t f(t)` and `f ↦ f(t⁻¹)`.

The proof is analytic.  A complete Bernstein function `f` with data `μ, a, b` is `t S(t)` for the
complex Stieltjes transform `S` of the same data, and `S` maps the upper half-plane into the
closed lower half-plane.  Unless the data vanish, `S` has no zero on the slit plane, so
`t / f(t) = S(t)⁻¹` extends holomorphically to the slit plane and maps the upper half-plane into
its closure.  The Pick characterization then produces the complete Bernstein function.

No nonvanishing hypothesis is needed: zero data represent the zero function, whose reciprocal
and conjugate are again zero because `0⁻¹ = 0`.  So the statements here generalize the classical
correspondence for nonzero functions to include the zero function, via Lean's convention
`0⁻¹ = 0`.  Since `t ↦ f(t)⁻¹` only sees `f` on `(0, ∞)`, recovering that `f` itself is complete
Bernstein also needs right-continuity at `0`, which pins down `f 0`.

## Main declarations

* `TauCeti.IsCompleteBernsteinFunction.exists_isCompleteBernsteinFunction_eqOn_div`: the
  conjugate `t ↦ t / f(t)` of a complete Bernstein function is complete Bernstein on `(0, ∞)`.
* `TauCeti.IsCompleteBernsteinFunction.isStieltjesFunction_inv`: the reciprocal of a complete
  Bernstein function is Stieltjes.
* `TauCeti.isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_inv`: `f` is Stieltjes
  exactly when `t ↦ f(t)⁻¹` on `(0, ∞)` extends to a complete Bernstein function.
* `TauCeti.isCompleteBernsteinFunction_iff_continuousWithinAt_isStieltjesFunction_inv`: `f` is
  complete Bernstein exactly when it is right-continuous at `0` and `t ↦ f(t)⁻¹` is Stieltjes.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Chapter 7.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped NNReal

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **The conjugate of a complete Bernstein function** (Schilling--Song--Vondraček,
Chapter 7).  If `f` is complete Bernstein, then `t ↦ t / f(t)` on `(0, ∞)` extends to a
complete Bernstein function on `[0, ∞)`. -/
theorem IsCompleteBernsteinFunction.exists_isCompleteBernsteinFunction_eqOn_div
    (hf : IsCompleteBernsteinFunction f) :
    ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g (fun t => t / f t) (Ioi 0) := by
  obtain ⟨a, b, μ, h⟩ := isCompleteBernsteinFunction_iff.mp hf
  have hμ := h.integrable_weight
  by_cases hdata : a = 0 ∧ b = 0 ∧ μ = 0
  · -- Zero data represent the zero function, whose conjugate is zero.
    obtain ⟨rfl, rfl, rfl⟩ := hdata
    refine ⟨fun _ => 0, isCompleteBernsteinFunction_const le_rfl, fun t ht => ?_⟩
    simp [h.eq_stieltjesBernsteinTransform (mem_Ioi.mp ht).le, stieltjesBernsteinTransform_apply]
  -- Otherwise `f(t) = t S(t)` with `S` zero-free on the slit plane, and `S⁻¹` is the extension.
  have hS : ∀ z ∈ slitPlane, stieltjesExtension μ a b z ≠ 0 := fun z hz h0 =>
    hdata ((stieltjesExtension_eq_zero_iff hμ hz).mp h0)
  have hSt (t : ℝ) (ht : 0 < t) : (stieltjesExtension μ a b t)⁻¹ = ((t / f t : ℝ) : ℂ) := by
    rw [ofReal_div, ← h.ofReal_mul_stieltjesExtension ht,
      div_mul_cancel_left₀ (ofReal_ne_zero.mpr ht.ne')]
  refine exists_isCompleteBernsteinFunction_eqOn_of_analyticOnNhd
    ((analyticOnNhd_stieltjesExtension hμ).inv hS) hSt (fun z hz => ?_)
    fun t ht => div_nonneg ht.le (hf.isBernsteinFunction.nonneg ht.le)
  have hz' : 0 < z.im := hz
  have hSim : (stieltjesExtension μ a b z).im ≤ 0 :=
    nonpos_of_mul_nonpos_right (im_mul_im_stieltjesExtension_nonpos hμ
      (mem_slitPlane_iff.mpr (Or.inr hz'.ne'))) hz'
  rw [Pi.inv_apply, inv_im]
  exact div_nonneg (neg_nonneg.mpr hSim) (normSq_nonneg _)

/-- **The reciprocal of a complete Bernstein function is Stieltjes.** -/
theorem IsCompleteBernsteinFunction.isStieltjesFunction_inv
    (hf : IsCompleteBernsteinFunction f) : IsStieltjesFunction (fun t => (f t)⁻¹) := by
  obtain ⟨g, hg, hgf⟩ := hf.exists_isCompleteBernsteinFunction_eqOn_div
  refine isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul.mpr
    ⟨g, hg, fun t ht => ?_⟩
  simp only [hgf ht, div_eq_mul_inv]

/-- **Stieltjes functions and complete Bernstein functions under reciprocals.**  A function `f`
is Stieltjes exactly when `t ↦ f(t)⁻¹` on `(0, ∞)` extends to a complete Bernstein function on
`[0, ∞)`. -/
theorem isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_inv :
    IsStieltjesFunction f ↔
      ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g (fun t => (f t)⁻¹) (Ioi 0) := by
  constructor
  · intro hf
    -- `f(t)⁻¹ = t / (t f(t))`, the conjugate of the complete Bernstein function `t f(t)`.
    obtain ⟨g, hg, hgf⟩ := isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul.mp hf
    obtain ⟨k, hk, hkg⟩ := hg.exists_isCompleteBernsteinFunction_eqOn_div
    refine ⟨k, hk, fun t ht => ?_⟩
    simp only [hkg ht, hgf ht, div_mul_cancel_left₀ (mem_Ioi.mp ht).ne']
  · rintro ⟨g, hg, hgf⟩
    refine hg.isStieltjesFunction_inv.congr fun t ht => ?_
    simp only [hgf ht, inv_inv]

/-- **Complete Bernstein functions are the reciprocals of Stieltjes functions**
(Schilling--Song--Vondraček, Chapter 7).  A function `f` is complete Bernstein exactly when it is
right-continuous at `0` and `t ↦ f(t)⁻¹` is Stieltjes.  The continuity condition recovers `f 0`,
which the reciprocal does not see; no nonvanishing hypothesis is needed, since for the zero
function both sides hold. -/
theorem isCompleteBernsteinFunction_iff_continuousWithinAt_isStieltjesFunction_inv (f : ℝ → ℝ) :
    IsCompleteBernsteinFunction f ↔
      ContinuousWithinAt f (Ici 0) 0 ∧ IsStieltjesFunction (fun t => (f t)⁻¹) := by
  refine ⟨fun hf => ⟨hf.isBernsteinFunction.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl),
    hf.isStieltjesFunction_inv⟩, fun ⟨hfc, hs⟩ => ?_⟩
  -- `f` agrees on `(0, ∞)` with a complete Bernstein `g`; transfer `g`'s Pick extension to `f`.
  obtain ⟨g, hg, hgf⟩ := isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_inv.mp hs
  have hgf' : EqOn g f (Ioi 0) := fun t ht => by simp only [hgf ht, inv_inv]
  obtain ⟨-, hpos, F, hF, hFf, him⟩ :=
    (isCompleteBernsteinFunction_iff_continuousWithinAt_nonneg_exists_analyticOnNhd g).mp hg
  refine (isCompleteBernsteinFunction_iff_continuousWithinAt_nonneg_exists_analyticOnNhd f).mpr
    ⟨hfc, fun t ht => hgf' ht ▸ hpos t ht, F, hF, fun t ht => by rw [hFf t ht, hgf' ht], him⟩

end TauCeti

end
