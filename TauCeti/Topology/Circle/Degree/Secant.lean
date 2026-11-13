/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.AddCircle
public import TauCeti.Topology.Circle.Degree

/-!
# Degrees of short forward secants

For an injective loop `q` parametrized by `AddCircle 1`, let `S` be a continuous complex-valued
function on pairs of points with no zeros off the diagonal near the diagonal. The directions of
`S (q τ, q (τ + r))` have the same degree as those of `S (q τ, q (τ + d τ))` when the constant
step `r` and continuous step `d` take values in the same sufficiently small positive interval.
This allows one to compare secant directions under a continuous change of forward displacement,
without choosing an ambient family of maps moving the loop.

## Main results

* `ContinuousMap.degree_secant_eq`: constant and variable short forward secants have equal
  degrees when their direction loops are specified pointwise by division by the norm.
-/

public section

open Set Function
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- The directions of the short forward secants `τ ↦ S (q τ, q (τ + r))` of an injective loop `q`
have the degree of the directions of `τ ↦ S (q τ, q (τ + d τ))`, for every continuous step `d`
with values in the same range `(0, δ)` as `r`, in which the secants are close to the diagonal. -/
theorem degree_secant_eq (q : C(AddCircle (1 : ℝ), X)) (hq : Injective q)
    {S : C(X × X, ℂ)} {U : Set (X × X)} (hzero : ∀ x y, (x, y) ∈ U → S (x, y) = 0 → x = y)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hsec : ∀ w : ℝ, |w| < δ → ∀ τ : AddCircle (1 : ℝ), (q τ, q (τ + w)) ∈ U)
    {d : AddCircle (1 : ℝ) → ℝ} (hdc : Continuous d) (hd : ∀ τ, d τ ∈ Ioo 0 δ)
    {r : ℝ} (hr : r ∈ Ioo 0 δ) {v w : Circle} (γ : Path v v) (η : Path w w)
    (hγ : ∀ t : I, (γ t : ℂ) =
      S (q (t : ℝ), q (((t : ℝ) + r : ℝ) : AddCircle (1 : ℝ))) /
        ‖S (q (t : ℝ), q (((t : ℝ) + r : ℝ) : AddCircle (1 : ℝ)))‖)
    (hη : ∀ t : I, (η t : ℂ) =
      S (q (t : ℝ), q ((t : ℝ) + d (t : ℝ))) / ‖S (q (t : ℝ), q ((t : ℝ) + d (t : ℝ)))‖) :
    Circle.degree γ = Circle.degree η := by
  let p : C(I, AddCircle (1 : ℝ)) := ⟨fun t ↦ ((t : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩
  let m : C(I × I, ℝ) := ⟨fun ut ↦ (1 - (ut.1 : ℝ)) * r + ut.1 * d (p ut.2), by fun_prop⟩
  have hm (ut : I × I) : m ut ∈ Ioo 0 δ := by
    simpa [m] using convex_Ioo (0 : ℝ) δ hr (hd (p ut.2)) (sub_nonneg.2 ut.1.2.2) ut.1.2.1
      (sub_add_cancel 1 _)
  let G : C(I × I, ℂ) := S.comp ⟨fun ut ↦ (q (p ut.2), q (p ut.2 + m ut)), by fun_prop⟩
  have hG (ut : I × I) : G ut = S (q (p ut.2), q (p ut.2 + m ut)) := rfl
  refine Circle.degree_eq_of_homotopy_div_norm γ η G (fun ut ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
    fun u ↦ ?_
  · rw [hG]
    exact q.secant_ne_zero hq hzero ⟨(hm ut).1, (hm ut).2.trans_le hδ⟩
      (hsec _ (abs_lt.2 ⟨by linarith [(hm ut).1, (hm ut).2], (hm ut).2⟩) _)
  · simp [hG, m, p, hγ]
  · simp [hG, m, p, hη]
  · have hp : p 1 = p 0 := by simp [p, AddCircle.coe_period]
    rw [hG, hG, hp]
    simp [m, hp]

end ContinuousMap
