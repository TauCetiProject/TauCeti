/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Manifold.Instances.Stiefel
import TauCeti.Analysis.Complex.Circle

/-!
# The rotation family over the unit tangent bundle of a sphere

Let `E` be a real inner product space of dimension `n + 2`, with unit sphere `Sⁿ⁺¹`, whose unit
tangent bundle is the Stiefel manifold `TauCeti.stiefel E 2` of orthonormal pairs `(u, v)`. The
**Stiefel rotation family** (`TauCeti.stiefelRotationFamily`)

`τ : V₂(E) × S¹ → Sⁿ⁺¹ × Sⁿ⁺¹`, `τ ((u, v), z) = (u, Re z • u + Im z • v)`,

with `S¹` the unit circle of `ℂ`, sends a unit tangent vector `v` at `u` and an angle to `u` and the
point reached by rotating `u` towards `v` by that angle. Over the point `u` of the first factor it
is the rotation family `TauCeti.sphereRotationFamily u` of the sphere at `u`.

This is the map `[(u, v), θ] ↦ (u, u cos θ + v sin θ)` of the proof of Proposition 6.17 of
Barraud–Damian–Humilière–Oancea. There, its degree, `±2` when the fibre sphere `Sⁿ` of the unit
tangent bundle has even dimension, shows that the class of the fibred family of two-spheres of an
even-dimensional sphere is nonzero in `H_*(Ω²Sⁿ⁺¹)`. The degree is a signed count of the
preimages described below, for the normal orientation `Orientation.stiefelTwoOrientation` of the
Stiefel manifold; this file constructs the map and its fibres.

Each point `(a, w)` with `w ≠ ±a` has exactly two preimages, `((a, v), z)` and `((a, -v), conj z)`
(`TauCeti.stiefelRotationFamily_eq_stiefelRotationFamily_iff`,
`TauCeti.exists_stiefelRotationFamily_eq`), and both have `Im z ≠ 0`
(`TauCeti.im_ne_zero_of_stiefelRotationFamily_eq`), while points with `Im z = 0` are sent to
`(u, ±u)`.

## Main declarations

* `TauCeti.stiefelRotationFamily`: the map `((u, v), z) ↦ (u, Re z • u + Im z • v)`.
* `TauCeti.contMDiff_stiefelRotationFamily`: it is smooth.
* `TauCeti.stiefelRotationFamily_eq_stiefelRotationFamily_iff`: two points, one with `Im z ≠ 0`,
  have the same image exactly when they are equal or exchanged by `((u, v), z) ↦ ((u, -v), conj z)`.
* `TauCeti.exists_stiefelRotationFamily_eq`: every `(a, w)` with `w ≠ ±a` is the image of a point
  with `Im z > 0`.
* `TauCeti.im_ne_zero_of_stiefelRotationFamily_eq`: every preimage of such a point has
  `Im z ≠ 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2 (Example 6.16 and the proof of
  Proposition 6.17).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Stiefel rotation family**: an orthonormal pair `(u, v)` and a point `z` of the unit
circle of `ℂ` are sent to `u` and to `Re z • u + Im z • v`, the point reached by rotating `u`
towards the unit tangent vector `v` by the angle of `z`. -/
def stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    sphere (0 : E) 1 × sphere (0 : E) 1 :=
  (stiefelProj E 2 0 x.1,
    ⟨(x.2 : ℂ).re • (x.1 : Fin 2 → E) 0 + (x.2 : ℂ).im • (x.1 : Fin 2 → E) 1, by
      -- `u` and `v` are orthonormal, and `Re z ^ 2 + Im z ^ 2 = ‖z‖ ^ 2 = 1`.
      obtain ⟨h₀, h₁, h₀₁⟩ := mem_stiefel_two_iff.1 x.1.2
      rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
      simp [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right, h₀, h₁, h₀₁]
      linarith [Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]⟩)

@[simp]
theorem coe_fst_stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelRotationFamily x).1 : E) = (x.1 : Fin 2 → E) 0 :=
  coe_stiefelProj 0 x.1

@[simp]
theorem coe_snd_stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelRotationFamily x).2 : E) =
      (x.2 : ℂ).re • (x.1 : Fin 2 → E) 0 + (x.2 : ℂ).im • (x.1 : Fin 2 → E) 1 :=
  (rfl)

/-- The Stiefel rotation family is smooth. -/
theorem contMDiff_stiefelRotationFamily [FiniteDimensional ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1 + 1)] :
    ContMDiff (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      ((𝓡 (n + 1)).prod (𝓡 (n + 1))) ∞ (stiefelRotationFamily (E := E)) := by
  have hv (i : Fin 2) : ContMDiff (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      𝓘(ℝ, E) ∞ fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (x.1 : Fin 2 → E) i :=
    ((contDiff_apply ℝ (fun _ : Fin 2 ↦ E) i).contMDiff.comp (contMDiff_coe_stiefel E 2)).comp
      contMDiff_fst
  have hz : ContMDiff (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      𝓘(ℝ, ℂ) ∞ fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (x.2 : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact ((contMDiff_stiefelProj E 2 0).comp contMDiff_fst).prodMk
    (ContMDiff.codRestrict_sphere
      (((Complex.reCLM.contDiff.contMDiff.comp hz).smul (hv 0)).add
        ((Complex.imCLM.contDiff.contMDiff.comp hz).smul (hv 1)))
      fun x ↦ (stiefelRotationFamily x).2.2)

/-! ### Fibres -/

/-- Two points of the domain, one of them with `Im z ≠ 0`, have the same image exactly when they
are equal or exchanged by the involution `((u, v), z) ↦ ((u, -v), conj z)`. -/
theorem stiefelRotationFamily_eq_stiefelRotationFamily_iff
    {x y : stiefel E 2 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    stiefelRotationFamily y = stiefelRotationFamily x ↔
      y = x ∨ ((y.1 : Fin 2 → E) 0 = (x.1 : Fin 2 → E) 0 ∧
        (y.1 : Fin 2 → E) 1 = -(x.1 : Fin 2 → E) 1 ∧
        (y.2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ)) := by
  obtain ⟨-, -, hx₀₁⟩ := mem_stiefel_two_iff.1 x.1.2
  obtain ⟨hx₀, -⟩ := mem_stiefel_two_iff.1 x.1.2
  constructor
  · intro h
    have hu : (y.1 : Fin 2 → E) 0 = (x.1 : Fin 2 → E) 0 := by
      simpa using congrArg Subtype.val (congrArg Prod.fst h)
    have hE := congrArg Subtype.val (congrArg Prod.snd h)
    simp only [coe_snd_stiefelRotationFamily, hu] at hE
    -- Pairing with `u` recovers the real parts.
    have hre : (y.2 : ℂ).re = (x.2 : ℂ).re := by
      have hy₀₁ := (mem_stiefel_two_iff.1 y.1.2).2.2
      rw [hu] at hy₀₁
      have h' := congrArg (fun w ↦ ⟪(x.1 : Fin 2 → E) 0, w⟫) hE
      simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx₀,
        hx₀₁, hy₀₁, mul_zero, add_zero, one_pow, mul_one] using h'
    have him : (y.2 : ℂ).im • (y.1 : Fin 2 → E) 1 = (x.2 : ℂ).im • (x.1 : Fin 2 → E) 1 := by
      rw [hre] at hE
      exact add_left_cancel hE
    have hsq : (y.2 : ℂ).im ^ 2 = (x.2 : ℂ).im ^ 2 := by
      linarith [congrArg (· ^ 2) hre, Complex.re_sq_add_im_sq_of_mem_sphere y.2.2,
        Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with him' | him'
    · left
      rw [him'] at him
      have hv := smul_right_injective E hx him
      refine Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (Subtype.ext (Complex.ext hre him'))
      fin_cases i
      exacts [hu, hv]
    · right
      rw [him', neg_smul, ← smul_neg] at him
      exact ⟨hu, neg_eq_iff_eq_neg.1 (smul_right_injective E hx him),
        Complex.ext (by simpa using hre) (by simpa using him')⟩
  · rintro (rfl | ⟨hu, hv, hz⟩)
    · rfl
    · refine Prod.ext (Subtype.ext (by simpa using hu)) (Subtype.ext ?_)
      simp only [coe_snd_stiefelRotationFamily, hu, hv, hz, Complex.conj_re, Complex.conj_im,
        neg_smul, smul_neg, neg_neg]

/-- A point with `Im z = 0` is sent to `(u, u)` or to `(u, -u)`. -/
theorem stiefelRotationFamily_snd_eq_or_eq_neg_of_im_eq_zero
    {x : stiefel E 2 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im = 0) :
    (stiefelRotationFamily x).2 = (stiefelRotationFamily x).1 ∨
      (stiefelRotationFamily x).2 = -(stiefelRotationFamily x).1 := by
  have hre : (x.2 : ℂ).re ^ 2 = 1 ^ 2 := by
    linarith [sq_eq_zero_iff.2 hx, Complex.re_sq_add_im_sq_of_mem_sphere x.2.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hre with h | h
  · exact .inl (Subtype.ext (by simp [h, hx]))
  · exact .inr (Subtype.ext (by simp [h, hx]))

/-- Every preimage of a point `(a, w)` with `w ≠ ±a` has `Im z ≠ 0`. -/
theorem im_ne_zero_of_stiefelRotationFamily_eq {a w : sphere (0 : E) 1} (hwa : w ≠ a)
    (hwa' : w ≠ -a) {x : stiefel E 2 × sphere (0 : ℂ) 1} (hx : stiefelRotationFamily x = (a, w)) :
    (x.2 : ℂ).im ≠ 0 := fun h ↦ by
  rcases stiefelRotationFamily_snd_eq_or_eq_neg_of_im_eq_zero h with h' | h' <;>
    rw [hx] at h'
  exacts [hwa h', hwa' h']

/-- Every point `(a, w)` with `w ≠ ±a` is the image of a point with `Im z > 0`. -/
theorem exists_stiefelRotationFamily_eq {a w : sphere (0 : E) 1} (hwa : w ≠ a) (hwa' : w ≠ -a) :
    ∃ x : stiefel E 2 × sphere (0 : ℂ) 1, 0 < (x.2 : ℂ).im ∧ stiefelRotationFamily x = (a, w) := by
  obtain ⟨⟨v, z⟩, hz, hvz⟩ := exists_sphereRotationFamily_eq a hwa hwa'
  have hv : ⟪(a : E), ((v : (ℝ ∙ (a : E))ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (a : E))ᗮ).2
  have hframe : ![(a : E), ((v : (ℝ ∙ (a : E))ᗮ) : E)] ∈ stiefel E 2 :=
    mem_stiefel_two_iff.2 ⟨norm_eq_of_mem_sphere a, norm_eq_of_mem_sphere v, hv⟩
  refine ⟨(⟨_, hframe⟩, z), hz, Prod.ext (Subtype.ext (coe_stiefelProj 0 _)) (Subtype.ext ?_)⟩
  rw [← hvz, coe_snd_stiefelRotationFamily, coe_sphereRotationFamily]
  -- The two vectors of the frame `![a, v]` are `a` and `v` by definition.
  rfl

end TauCeti
