/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.Circle

/-!
# The double loops of a sphere swept by circles tangent to two directions

Let `p` be a point of the unit sphere `S` of a real inner product space `E`, and `u` a unit
tangent vector of `S` at `p`, a unit vector of `p^⊥`. The *equator through `p` orthogonal to `u`*
is the unit sphere of `u^⊥`; it contains `p`. For a point `q` of this equator, the circle of `S`
through `p` and `q` tangent to `u` at `p` is

`z ↦ p + ((1 - Re z) / 2) • (q - p) + (Im z * ‖q - p‖ / 2) • u`, `z ∈ S¹ ⊆ ℂ`

(`TauCeti.tangentCircleMap`): its centre is `(p + q) / 2`, its radius `‖q - p‖ / 2`, it lies in
the plane through `p` spanned by `q - p` and `u`, it passes through `p` at `z = 1` and through `q`
at `z = -1`, and it degenerates to the point `p` when `q = p`. Run once from `p` it is the loop
`φ_u(q)` of Barraud–Damian–Humilière–Oancea (Example 6.20; `TauCeti.tangentCircleLoop`), and
`q ↦ φ_u(q)` is a continuous map from the equator to the loop space `Ω_p S`, sending `p` to the
constant loop.

These circles sweep the sphere exactly once: the map `(q, z) ↦ φ_u(q)(z)` collapses the set where
`q = p` or `z = 1` to `p`, and is a bijection from its complement onto `S ∖ {p}`
(`TauCeti.bijOn_tangentCircleMap`). Geometrically, stereographic projection from `p` turns the
circles into the lines parallel to `u`, one through each point of the projected equator. In other
words, the adjoint of `φ_u`, a map from the reduced suspension of the equator `S^{n-1}` to `Sⁿ`,
is a bijection away from the base point; the suspension and the adjunction themselves are not
constructed here.

Given a second unit vector `v` orthogonal to `p` and `u`, the same construction in the equator
`S(u^⊥)` gives loops of that equator, and applying `φ_u` to them gives the double loop
`σ_p(q) = Ω φ_u (φ_v(q))` at `p` (`TauCeti.tangentCircleDoubleLoop`), for `q` in the sphere `Σ_p`
of `u^⊥ ∩ v^⊥`, of dimension `n - 2` when `S = Sⁿ`. This is the family `σ_p : Σ_p → Ω²_p Sⁿ` of
Example 6.20. On the spheres `S^{4k-1}`, which carry pointwise orthonormal tangent vector fields
(`TauCeti.quaternionFrame`), the source lets `p` vary with `u = u(p)` and `v = v(p)` to obtain a
fibered family of 2-spheres. The evaluation `((q, z), w) ↦ σ_p(q)(z)(w)` is a bijection from the
complement of the collapsed set onto `S ∖ {p}`
(`TauCeti.bijOn_tangentCircleMap_tangentCircleMap`). This is the geometric input to
Proposition 6.21, which identifies the class of `σ_p` in `H_{n-2}(Ω²Sⁿ) ≅ ℤ` as a generator.

## Main declarations

* `TauCeti.tangentCircleBase`: `p` as a point of the equator orthogonal to `u`.
* `TauCeti.tangentCircleMap`: the circles through `p` tangent to `u`, as a map from the product of
  the equator and the unit circle to the sphere.
* `TauCeti.tangentCircleMap_eq_self_iff`: a point is sent to `p` exactly when `q = p` or `z = 1`.
* `TauCeti.bijOn_tangentCircleMap`: away from these points the map is a bijection onto the
  sphere minus `p`.
* `TauCeti.tangentCircleLoop`: the loop `φ_u(q)` at `p`, with
  `TauCeti.tangentCircleLoop_tangentCircleBase` and `TauCeti.continuous_tangentCircleLoop`.
* `TauCeti.tangentCircleDoubleLoop`: the double loop `σ_p(q)`, with
  `TauCeti.continuous_tangentCircleDoubleLoop`.
* `TauCeti.bijOn_tangentCircleMap_tangentCircleMap`: the double loops sweep the sphere once.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.20 and the proof of
  Proposition 6.21.
-/

public section

noncomputable section

open Metric Real
open scoped RealInnerProductSpace unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The circles through a point, on vectors -/

section Vector

variable {P Q Q' U Y : E} {x y x' y' : ℝ}

/-- The point at parameter `(x, y)` of the circle through `P` and `Q` tangent to `U` at `P`. -/
private def tangentCircleVec (P Q U : E) (x y : ℝ) : E :=
  P + ((1 - x) / 2) • (Q - P) + (y * (‖Q - P‖ / 2)) • U

private theorem norm_sub_div_two_sq (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) :
    (‖Q - P‖ / 2) ^ 2 = (1 - ⟪P, Q⟫) / 2 := by
  rw [div_pow, @norm_sub_sq_real, hP, hQ, real_inner_comm P Q]; ring

private theorem norm_tangentCircleVec (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hU : ‖U‖ = 1)
    (hPU : ⟪P, U⟫ = 0) (hQU : ⟪Q, U⟫ = 0) (hxy : x ^ 2 + y ^ 2 = 1) :
    ‖tangentCircleVec P Q U x y‖ = 1 := by
  have hUP : ⟪U, P⟫ = 0 := by rw [real_inner_comm]; exact hPU
  have hUQ : ⟪U, Q⟫ = 0 := by rw [real_inner_comm]; exact hQU
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
    tangentCircleVec]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, real_inner_self_eq_norm_sq, hP, hQ, hU, hPU, hQU, hUP, hUQ,
    RCLike.conj_to_real, real_inner_comm P Q]
  linear_combination y ^ 2 * norm_sub_div_two_sq hP hQ - ((⟪P, Q⟫ - 1) / 2) * hxy

/-- The component of the circle along `U` is `y` times the radius. -/
private theorem inner_tangentCircleVec_right (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0)
    (hQU : ⟪Q, U⟫ = 0) : ⟪tangentCircleVec P Q U x y, U⟫ = y * (‖Q - P‖ / 2) := by
  simp [tangentCircleVec, inner_add_left, inner_smul_left, inner_sub_left, hPU, hQU, hU]

/-- The component of the circle along `P` measures its distance to `P`. -/
private theorem inner_tangentCircleVec_left (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hPU : ⟪P, U⟫ = 0) :
    ⟪tangentCircleVec P Q U x y, P⟫ = 1 - (1 - x) * (‖Q - P‖ / 2) ^ 2 := by
  have hUP : ⟪U, P⟫ = 0 := by rw [real_inner_comm]; exact hPU
  rw [norm_sub_div_two_sq hP hQ]
  simp only [tangentCircleVec, inner_add_left, inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq, hP, hUP, RCLike.conj_to_real, real_inner_comm P Q]
  ring

private theorem tangentCircleVec_sub_smul (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0) (hQU : ⟪Q, U⟫ = 0) :
    tangentCircleVec P Q U x y - ⟪tangentCircleVec P Q U x y, U⟫ • U =
      P + ((1 - x) / 2) • (Q - P) := by
  rw [inner_tangentCircleVec_right hU hPU hQU, tangentCircleVec, add_sub_cancel_right]

/-- The circle meets `P` exactly at `x = 1`, or everywhere when `Q = P`. -/
private theorem tangentCircleVec_eq_left_iff (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hU : ‖U‖ = 1)
    (hPU : ⟪P, U⟫ = 0) (hQU : ⟪Q, U⟫ = 0) (hxy : x ^ 2 + y ^ 2 = 1) :
    tangentCircleVec P Q U x y = P ↔ Q = P ∨ x = 1 := by
  rw [← inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (norm_tangentCircleVec hP hQ hU hPU hQU hxy) hP,
    inner_tangentCircleVec_left hP hQ hPU]
  constructor
  · intro h
    rcases mul_eq_zero.1 (by linarith : (1 - x) * (‖Q - P‖ / 2) ^ 2 = 0) with h1 | h1
    · exact Or.inr (by linarith)
    · refine Or.inl (sub_eq_zero.1 (norm_eq_zero.1 ?_))
      linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h1]
  · rintro (h | h) <;> simp [h]

/-- Two pairs `(a, R)` and `(a', R')` with `a * R = a' * R' ≠ 0` and `a * R ^ 2 = a' * R' ^ 2` are
equal. -/
private theorem eq_and_eq_of_mul_sq_eq {a R a' R' : ℝ} (h₁ : a * R = a' * R') (h₀ : a * R ≠ 0)
    (h₂ : a * R ^ 2 = a' * R' ^ 2) : R = R' ∧ a = a' := by
  have hRR : R = R' := by
    refine mul_left_cancel₀ h₀ ?_
    calc a * R * R = a' * R' * R' := by linear_combination h₂
      _ = a * R * R' := by rw [h₁]
  have hR : R ≠ 0 := right_ne_zero_of_mul h₀
  refine ⟨hRR, mul_right_cancel₀ hR ?_⟩
  rw [h₁, hRR]

/-- Away from `P`, a point of the circles determines `Q` and the parameter. -/
private theorem eq_of_tangentCircleVec_eq (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hQ' : ‖Q'‖ = 1)
    (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0) (hQU : ⟪Q, U⟫ = 0) (hQ'U : ⟪Q', U⟫ = 0)
    (hxy : x ^ 2 + y ^ 2 = 1) (hxy' : x' ^ 2 + y' ^ 2 = 1)
    (hne : tangentCircleVec P Q U x y ≠ P)
    (h : tangentCircleVec P Q U x y = tangentCircleVec P Q' U x' y') :
    Q = Q' ∧ x = x' ∧ y = y' := by
  have hx : x ≤ 1 := by nlinarith
  have hx' : x' ≤ 1 := by nlinarith
  -- The components along `U` and along `P`, and the remaining part in the plane of `P` and `Q`.
  have hb : y * (‖Q - P‖ / 2) = y' * (‖Q' - P‖ / 2) := by
    rw [← inner_tangentCircleVec_right hU hPU hQU, h, inner_tangentCircleVec_right hU hPU hQ'U]
  have ha : (1 - x) * (‖Q - P‖ / 2) ^ 2 = (1 - x') * (‖Q' - P‖ / 2) ^ 2 := by
    have := congrArg (⟪·, P⟫) h
    simp only [inner_tangentCircleVec_left hP hQ hPU,
      inner_tangentCircleVec_left hP hQ' hPU] at this
    linarith
  have hlin : ((1 - x) / 2) • (Q - P) = ((1 - x') / 2) • (Q' - P) := by
    have := tangentCircleVec_sub_smul (x := x) (y := y) hU hPU hQU
    rw [h, tangentCircleVec_sub_smul hU hPU hQ'U] at this
    exact (add_left_cancel this).symm
  have hn : (1 - x) * (‖Q - P‖ / 2) = (1 - x') * (‖Q' - P‖ / 2) := by
    have := congrArg norm hlin
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)] at this
    linarith
  -- Away from `P`, both factors of `(1 - x) * (‖Q - P‖ / 2) ^ 2` are nonzero.
  have hne' : (1 - x) * (‖Q - P‖ / 2) ≠ 0 := by
    intro h0
    refine hne ((tangentCircleVec_eq_left_iff hP hQ hU hPU hQU hxy).2 ?_)
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact Or.inr (by linarith)
    · exact Or.inl (sub_eq_zero.1 (norm_eq_zero.1 (by linarith)))
  obtain ⟨hRR, hxx⟩ := eq_and_eq_of_mul_sq_eq hn hne' ha
  have hR : ‖Q - P‖ / 2 ≠ 0 := right_ne_zero_of_mul hne'
  refine ⟨?_, by linarith, mul_right_cancel₀ hR (hRR ▸ hb)⟩
  rw [← hxx] at hlin
  exact sub_left_injective
    (smul_right_injective E (div_ne_zero (left_ne_zero_of_mul hne') two_ne_zero) hlin)

/-- For a unit vector `Y` and orthonormal `P` and `U`, the squared distance from `P` of the part of
`Y` orthogonal to `U`. -/
private theorem norm_sub_smul_sub_sq (hP : ‖P‖ = 1) (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0)
    (hY : ‖Y‖ = 1) :
    ‖Y - ⟪Y, U⟫ • U - P‖ ^ 2 = 2 * (1 - ⟪Y, P⟫) - ⟪Y, U⟫ ^ 2 := by
  have hUP : ⟪U, P⟫ = 0 := by rw [real_inner_comm]; exact hPU
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hY, hU, hP, hUP, hPU, RCLike.conj_to_real,
    real_inner_comm Y U, real_inner_comm Y P]
  ring

/-- For a unit vector `Y ≠ P`, the part of `Y` orthogonal to `U` is not `P`. -/
private theorem norm_sub_smul_sub_pos (hP : ‖P‖ = 1) (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0)
    (hY : ‖Y‖ = 1) (hYP : Y ≠ P) : 0 < ‖Y - ⟪Y, U⟫ • U - P‖ := by
  refine (norm_nonneg _).lt_of_ne fun h0 ↦ hYP ?_
  have hY' : Y - ⟪Y, U⟫ • U = P := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
  -- Then `Y = P + ⟪Y, U⟫ • U`, a unit vector only if `⟪Y, U⟫ = 0`.
  have hw : ⟪Y, U⟫ = 0 := by
    have h1 := norm_sub_smul_sub_sq hP hU hPU hY
    rw [← h0] at h1
    have h2 := congrArg (⟪·, P⟫) hY'
    simp only [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hP,
      RCLike.conj_to_real, real_inner_comm P U, hPU] at h2
    nlinarith
  simpa [hw] using hY'

/-- Every point of the sphere other than `P` lies on one of the circles: for `Y ≠ P`, with
`Y' = Y - ⟪Y, U⟫ • U` and `κ = ‖Y' - P‖ ^ 2 / (1 - ⟪Y, P⟫)`, the point
`Q = P + (2 / κ) • (Y' - P)` and the parameter `(1 - κ, ⟪Y, U⟫ / (‖Y' - P‖ / κ))` work. -/
private theorem exists_tangentCircleVec_eq (hP : ‖P‖ = 1) (hU : ‖U‖ = 1) (hPU : ⟪P, U⟫ = 0)
    (hY : ‖Y‖ = 1) (hYP : Y ≠ P) :
    ∃ (Q : E) (x y : ℝ), ‖Q‖ = 1 ∧ ⟪Q, U⟫ = 0 ∧ x ^ 2 + y ^ 2 = 1 ∧
      tangentCircleVec P Q U x y = Y := by
  set w := ⟪Y, U⟫
  set δ := 1 - ⟪Y, P⟫
  have hδ : 0 < δ := sub_pos.2 ((inner_lt_one_iff_real_of_norm_eq_one hY hP).2 hYP)
  set N := ‖Y - w • U - P‖
  have hN : 0 < N := norm_sub_smul_sub_pos hP hU hPU hY hYP
  set κ := N ^ 2 / δ
  have hκ : 0 < κ := div_pos (pow_pos hN 2) hδ
  have hNκ : N ^ 2 = κ * δ := by simp only [κ]; field_simp
  have hw2 : w ^ 2 = (2 - κ) * δ := by
    linear_combination norm_sub_smul_sub_sq hP hU hPU hY - hNκ
  set Q := P + (2 / κ) • (Y - w • U - P)
  have hQU : ⟪Q, U⟫ = 0 := by
    simp only [Q, w, inner_add_left, inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, hU, hPU, RCLike.conj_to_real]
    ring
  have hQ : ‖Q‖ = 1 := by
    have hPY : ⟪P, Y - w • U - P⟫ = -δ := by
      simp only [δ, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hP, hPU,
        real_inner_comm P Y]
      ring
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq]
    simp only [Q, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hP, RCLike.conj_to_real, real_inner_comm P (Y - w • U - P), hPY]
    rw [show ‖Y - w • U - P‖ ^ 2 = κ * δ from hNκ]
    field_simp
    ring
  have hR : ‖Q - P‖ / 2 = N / κ := by
    simp only [Q, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_pos two_pos hκ).le, N]
    field_simp
  refine ⟨Q, 1 - κ, w / (N / κ), hQ, hQU, ?_, ?_⟩
  · have h1 : (w / (N / κ)) ^ 2 * δ = w ^ 2 * κ := by
      rw [div_div_eq_mul_div, div_pow, mul_pow, hNκ]
      field_simp
    have h2 : (w / (N / κ)) ^ 2 = (2 - κ) * κ := by
      refine mul_right_cancel₀ hδ.ne' ?_
      rw [h1, hw2]
      ring
    rw [h2]
    ring
  · rw [tangentCircleVec, hR, div_mul_cancel₀ _ (div_pos hN hκ).ne', sub_sub_cancel]
    simp only [Q, add_sub_cancel_left, smul_smul]
    rw [show κ / 2 * (2 / κ) = 1 by field_simp, one_smul]
    simp

end Vector

/-! ### The circles through a point tangent to a direction -/

variable (p : sphere (0 : E) 1) (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)

private theorem inner_coe_coe_sphere : ⟪(p : E), ((u : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.1 (u : (ℝ ∙ (p : E))ᗮ).2

private theorem inner_coe_coe_equator (q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1) :
    ⟪((q : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E), ((u : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1
    (q : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ).2

private theorem norm_coe_coe {K : Submodule ℝ E} (q : sphere (0 : K) 1) : ‖((q : K) : E)‖ = 1 := by
  rw [Submodule.norm_coe]
  exact norm_eq_of_mem_sphere q

/-- The point `p`, seen as a point of the equator through `p` orthogonal to the tangent vector
`u`, the unit sphere of `u^⊥`. -/
def tangentCircleBase : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1 :=
  ⟨⟨p, Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by
      rw [real_inner_comm]; exact inner_coe_coe_sphere p u)⟩, by simp⟩

@[simp]
theorem coe_tangentCircleBase :
    ((tangentCircleBase p u : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E) = p :=
  (rfl)

/-- The **circles through `p` tangent to `u`**. A point `q` of the equator through `p` orthogonal
to `u` and a point `z` of the unit circle of `ℂ` are sent to the point at parameter `z` of the
circle of the sphere through `p` and `q` tangent to `u` at `p`, with centre `(p + q) / 2` and
radius `‖q - p‖ / 2`:

`p + ((1 - Re z) / 2) • (q - p) + (Im z * (‖q - p‖ / 2)) • u`.

It is `p` at `z = 1` and `q` at `z = -1`. -/
def tangentCircleMap
    (x : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1 × Circle) : sphere (0 : E) 1 :=
  ⟨tangentCircleVec p ((x.1 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E)
      ((u : (ℝ ∙ (p : E))ᗮ) : E) (x.2 : ℂ).re (x.2 : ℂ).im,
    mem_sphere_zero_iff_norm.2 <| norm_tangentCircleVec (norm_eq_of_mem_sphere p)
      (norm_coe_coe x.1) (norm_coe_coe u) (inner_coe_coe_sphere p u)
      (inner_coe_coe_equator p u x.1) (Circle.re_sq_add_im_sq x.2)⟩

@[simp]
theorem coe_tangentCircleMap
    (x : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1 × Circle) :
    (tangentCircleMap p u x : E) =
      (p : E) + ((1 - (x.2 : ℂ).re) / 2) •
          (((x.1 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E) - p) +
        ((x.2 : ℂ).im * (‖((x.1 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E) - p‖ / 2)) •
          ((u : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

@[fun_prop]
theorem continuous_tangentCircleMap : Continuous (tangentCircleMap p u) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_tangentCircleMap]
  fun_prop

/-- The circles start at `p`. -/
@[simp]
theorem tangentCircleMap_one (q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1) :
    tangentCircleMap p u (q, 1) = p :=
  Subtype.ext (by simp)

/-- The circle through `p` and `q` passes through `q` at `z = -1`. -/
theorem coe_tangentCircleMap_neg_one
    (q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1) :
    (tangentCircleMap p u (q, -1) : E) = ((q : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) : E) := by
  simp

/-- The circle through `p` and `p` is the point `p`. -/
@[simp]
theorem tangentCircleMap_tangentCircleBase (z : Circle) :
    tangentCircleMap p u (tangentCircleBase p u, z) = p :=
  Subtype.ext (by simp)

private theorem eq_one_of_re_eq_one {z : Circle} (hz : (z : ℂ).re = 1) : z = 1 :=
  Circle.ext (Complex.ext (by simpa using hz)
    (by simpa using Complex.abs_re_eq_norm.1 (by simp [hz])))

/-- **The circles meet `p` exactly at their starting point**, except that the circle through `p`
and `p` is the point `p`. -/
theorem tangentCircleMap_eq_self_iff
    {x : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1 × Circle} :
    tangentCircleMap p u x = p ↔ x.1 = tangentCircleBase p u ∨ x.2 = 1 := by
  rw [← Subtype.coe_inj, tangentCircleMap, tangentCircleVec_eq_left_iff (norm_eq_of_mem_sphere p)
    (norm_coe_coe x.1) (norm_coe_coe u) (inner_coe_coe_sphere p u)
    (inner_coe_coe_equator p u x.1) (Circle.re_sq_add_im_sq x.2)]
  refine or_congr ⟨fun h ↦ Subtype.ext (Subtype.ext h), fun h ↦ by rw [h]; rfl⟩
    ⟨eq_one_of_re_eq_one, fun h ↦ by simp [h]⟩

/-- **The circles through `p` tangent to `u` sweep the sphere once**: away from the points with
`q = p` or `z = 1`, which are sent to `p`, the map `(q, z) ↦ φ_u(q)(z)` is a bijection onto the
sphere minus `p`. -/
theorem bijOn_tangentCircleMap :
    Set.BijOn (tangentCircleMap p u) ({tangentCircleBase p u}ᶜ ×ˢ {1}ᶜ) {p}ᶜ := by
  have hP := norm_eq_of_mem_sphere p
  have hU := norm_coe_coe u
  have hPU := inner_coe_coe_sphere p u
  have hmem : ∀ x, x ∈ ({tangentCircleBase p u}ᶜ ×ˢ {1}ᶜ : Set (_ × Circle)) ↔
      tangentCircleMap p u x ≠ p := fun x ↦ by
    simp [tangentCircleMap_eq_self_iff, not_or]
  refine ⟨fun x hx ↦ (hmem x).1 hx, fun x hx x' _ h ↦ ?_, fun Y hY ↦ ?_⟩
  · obtain ⟨hq, hre, him⟩ := eq_of_tangentCircleVec_eq hP (norm_coe_coe x.1) (norm_coe_coe x'.1)
      hU hPU (inner_coe_coe_equator p u x.1) (inner_coe_coe_equator p u x'.1)
      (Circle.re_sq_add_im_sq x.2) (Circle.re_sq_add_im_sq x'.2)
      (fun h' ↦ (hmem x).1 hx (Subtype.ext h')) (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (Subtype.ext hq)) (Circle.ext (Complex.ext hre him))
  · have hYP : (Y : E) ≠ p := fun h ↦ hY (Subtype.ext h)
    obtain ⟨Q, x, y, hQ, hQU, hxy, hQY⟩ :=
      exists_tangentCircleVec_eq hP hU hPU (norm_eq_of_mem_sphere Y) hYP
    let q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1 :=
      ⟨⟨Q, Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by
        rw [real_inner_comm]; exact hQU)⟩, by simpa using hQ⟩
    let z : Circle := ⟨⟨x, y⟩, mem_sphere_zero_iff_norm.2 (by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      simp only
      rw [hxy, Real.sqrt_one])⟩
    have hmap : tangentCircleMap p u (q, z) = Y := Subtype.ext hQY
    exact ⟨(q, z), (hmem _).2 (hmap ▸ hY), hmap⟩

/-! ### The loops `φ_u` -/

/-- The **loop `φ_u(q)`** at `p` of Barraud–Damian–Humilière–Oancea (Example 6.20): the circle of
the sphere through `p` and `q` tangent to `u` at `p`, run once from `p`, with constant speed. For
`q = p` it is the constant loop (`TauCeti.tangentCircleLoop_tangentCircleBase`). -/
def tangentCircleLoop (q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1) : Path p p where
  toFun t := tangentCircleMap p u (q, Circle.exp (2 * π * t))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem tangentCircleLoop_apply (q : sphere (0 : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ) 1) (t : I) :
    tangentCircleLoop p u q t = tangentCircleMap p u (q, Circle.exp (2 * π * t)) :=
  (rfl)

/-- The loop through `p` and `p` is the constant loop. -/
@[simp]
theorem tangentCircleLoop_tangentCircleBase :
    tangentCircleLoop p u (tangentCircleBase p u) = Path.refl p := by
  ext t
  simp

/-- The loops `φ_u(q)` depend continuously on `q`, as a map from the equator to the loop space. -/
@[fun_prop]
theorem continuous_tangentCircleLoop : Continuous (tangentCircleLoop p u) :=
  Path.continuous_uncurry_iff.mp
    (show Continuous fun x : _ × I ↦ tangentCircleMap p u (x.1, Circle.exp (2 * π * x.2)) by
      fun_prop)

/-! ### The double loops `σ_p` -/

variable (v : sphere (0 : (ℝ ∙ ((tangentCircleBase p u :
    (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ)))ᗮ) 1)

/-- The **double loop `σ_p(q)`** of Barraud–Damian–Humilière–Oancea (Example 6.20), for a unit
vector `v` orthogonal to `p` and `u` and a point `q` of the unit sphere `Σ_p` of `u^⊥ ∩ v^⊥`. The
circles through `p` tangent to `v` inside the equator `S(u^⊥)` give the loop `φ_v(q)` of that
equator, and applying `φ_u` to each of its points gives a loop of loops at the constant loop,
`σ_p(q) = Ω φ_u (φ_v(q))`. -/
def tangentCircleDoubleLoop
    (q : sphere (0 : (ℝ ∙ ((v : (ℝ ∙ ((tangentCircleBase p u :
      (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ)))ᗮ) : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ))ᗮ) 1) :
    Path (Path.refl p) (Path.refl p) :=
  ((tangentCircleLoop (tangentCircleBase p u) v q).map (continuous_tangentCircleLoop p u)).cast
    (tangentCircleLoop_tangentCircleBase p u).symm (tangentCircleLoop_tangentCircleBase p u).symm

/-- The double loop `σ_p(q)` at times `s` and `t` is the point at time `t` of the circle `φ_u`
through the point at time `s` of the circle `φ_v(q)`. -/
@[simp]
theorem tangentCircleDoubleLoop_apply_apply
    (q : sphere (0 : (ℝ ∙ ((v : (ℝ ∙ ((tangentCircleBase p u :
      (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ)))ᗮ) : (ℝ ∙ ((u : (ℝ ∙ (p : E))ᗮ) : E))ᗮ))ᗮ) 1)
    (s t : I) :
    tangentCircleDoubleLoop p u v q s t = tangentCircleMap p u
      (tangentCircleMap (tangentCircleBase p u) v (q, Circle.exp (2 * π * s)),
        Circle.exp (2 * π * t)) :=
  (rfl)

/-- The double loop at `q = p` is the constant double loop. -/
@[simp]
theorem tangentCircleDoubleLoop_tangentCircleBase :
    tangentCircleDoubleLoop p u v (tangentCircleBase (tangentCircleBase p u) v) =
      Path.refl (Path.refl p) := by
  ext s t
  simp

/-- The double loops `σ_p(q)` depend continuously on `q`. -/
theorem continuous_tangentCircleDoubleLoop : Continuous (tangentCircleDoubleLoop p u v) :=
  Path.continuous_uncurry_iff.mp
    (show Continuous fun x : _ × I ↦
        tangentCircleLoop p u (tangentCircleLoop (tangentCircleBase p u) v x.1 x.2) by
      fun_prop)

/-- **The double loops `σ_p` sweep the sphere once** (the geometric input to Proposition 6.21 of
Barraud–Damian–Humilière–Oancea): the evaluation `((q, z), w) ↦ σ_p(q)(z)(w)`, with the two circle
parameters `z` and `w`, is a bijection from the points with `q ≠ p`, `z ≠ 1` and `w ≠ 1` onto the
sphere minus `p`. It sends all other points to `p` (`TauCeti.tangentCircleMap_eq_self_iff`). -/
theorem bijOn_tangentCircleMap_tangentCircleMap :
    Set.BijOn (fun x ↦ tangentCircleMap p u (tangentCircleMap (tangentCircleBase p u) v x.1, x.2))
      (({tangentCircleBase (tangentCircleBase p u) v}ᶜ ×ˢ {1}ᶜ) ×ˢ {1}ᶜ) {p}ᶜ :=
  (bijOn_tangentCircleMap p u).comp
    ((bijOn_tangentCircleMap (tangentCircleBase p u) v).prodMap (Set.bijOn_id _))

end TauCeti
