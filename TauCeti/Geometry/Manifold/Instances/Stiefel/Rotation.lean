/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Manifold.Instances.Stiefel

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
tangent bundle has even dimension, shows that the class of the fibred family of two-spheres of the
even-dimensional sphere `Sⁿ⁺²` is nonzero in `H_{2n+1}(Ω²Sⁿ⁺²)` (the paper's `H_{2m−3}(Ω²Sᵐ)` for
`m = n + 2`, whose map has domain `T¹Sᵐ⁻¹ × S¹`). The degree is a signed count of the
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

/-- The second vector of an orthonormal pair `(u, v)` with `u = p`, as a unit vector of `p^⊥`, that
is a unit tangent vector of the sphere at `p`. -/
private def stiefelTangent (p : sphere (0 : E) 1) (x : stiefel E 2)
    (hx : (x : Fin 2 → E) 0 = p) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
  ⟨⟨(x : Fin 2 → E) 1, Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (hx ▸ (mem_stiefel_two_iff.1 x.2).2.2)⟩,
    mem_sphere_zero_iff_norm.2 (mem_stiefel_two_iff.1 x.2).2.1⟩

/-- The **Stiefel rotation family**: an orthonormal pair `(u, v)` and a point `z` of the unit
circle of `ℂ` are sent to `u` and to `Re z • u + Im z • v`, the point reached by rotating `u`
towards the unit tangent vector `v` by the angle of `z`, that is to `u` and to the image of `(v, z)`
under the rotation family `TauCeti.sphereRotationFamily u` of the sphere at `u`. -/
def stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    sphere (0 : E) 1 × sphere (0 : E) 1 :=
  (stiefelProj E 2 0 x.1,
    sphereRotationFamily (stiefelProj E 2 0 x.1)
      (stiefelTangent _ x.1 (coe_stiefelProj 0 x.1).symm, x.2))

/-- Over a point `p` of the sphere, the second component of the Stiefel rotation family is the
rotation family of the sphere at `p`. -/
private theorem snd_stiefelRotationFamily_eq {p : sphere (0 : E) 1}
    (x : stiefel E 2 × sphere (0 : ℂ) 1) (hx : (x.1 : Fin 2 → E) 0 = p) :
    (stiefelRotationFamily x).2 = sphereRotationFamily p (stiefelTangent p x.1 hx, x.2) := by
  obtain rfl : stiefelProj E 2 0 x.1 = p := Subtype.ext ((coe_stiefelProj 0 x.1).trans hx)
  rfl

@[simp]
theorem coe_fst_stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelRotationFamily x).1 : E) = (x.1 : Fin 2 → E) 0 :=
  coe_stiefelProj 0 x.1

@[simp]
theorem coe_snd_stiefelRotationFamily (x : stiefel E 2 × sphere (0 : ℂ) 1) :
    ((stiefelRotationFamily x).2 : E) =
      (x.2 : ℂ).re • (x.1 : Fin 2 → E) 0 + (x.2 : ℂ).im • (x.1 : Fin 2 → E) 1 := by
  rw [snd_stiefelRotationFamily_eq x (coe_stiefelProj 0 x.1).symm, coe_sphereRotationFamily]
  simp only [coe_stiefelProj]
  -- The vector of `p^⊥` underlying `stiefelTangent p x.1 hx` is `x.1 1` by definition.
  rfl

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
  have h₂ : ContMDiff (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      𝓘(ℝ, E) ∞ fun x : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelRotationFamily x).2 : E) := by
    simp only [coe_snd_stiefelRotationFamily]
    exact ((Complex.reCLM.contDiff.contMDiff.comp hz).smul (hv 0)).add
      ((Complex.imCLM.contDiff.contMDiff.comp hz).smul (hv 1))
  exact ((contMDiff_stiefelProj E 2 0).comp contMDiff_fst).prodMk
    (h₂.codRestrict_sphere fun x ↦ (stiefelRotationFamily x).2.2)

/-! ### Fibres -/

/-- Two points of the domain, one of them with `Im z ≠ 0`, have the same image exactly when they
are equal or exchanged by the involution `((u, v), z) ↦ ((u, -v), conj z)`. -/
theorem stiefelRotationFamily_eq_stiefelRotationFamily_iff
    {x y : stiefel E 2 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    stiefelRotationFamily y = stiefelRotationFamily x ↔
      y = x ∨ ((y.1 : Fin 2 → E) 0 = (x.1 : Fin 2 → E) 0 ∧
        (y.1 : Fin 2 → E) 1 = -(x.1 : Fin 2 → E) 1 ∧
        (y.2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ)) := by
  -- Over the common first vector `p = u`, transport the fibres of `sphereRotationFamily p`.
  have hx₀ : (x.1 : Fin 2 → E) 0 = (stiefelProj E 2 0 x.1 : E) := (coe_stiefelProj 0 x.1).symm
  constructor
  · intro h
    have hu : (y.1 : Fin 2 → E) 0 = (x.1 : Fin 2 → E) 0 := by
      simpa using congrArg Subtype.val (congrArg Prod.fst h)
    have h₂ := congrArg Prod.snd h
    rw [snd_stiefelRotationFamily_eq y (hu.trans hx₀), snd_stiefelRotationFamily_eq x hx₀,
      sphereRotationFamily_eq_sphereRotationFamily_iff _ (x := (_, x.2)) hx] at h₂
    rcases h₂ with h₂ | ⟨hv, hz⟩
    · refine .inl (Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (congrArg Prod.snd h₂ :))
      fin_cases i
      exacts [hu, congrArg (fun w ↦ ((w.1 : (ℝ ∙ (stiefelProj E 2 0 x.1 : E))ᗮ) : E)) h₂]
    · exact .inr ⟨hu, hv, hz⟩
  · rintro (rfl | ⟨hu, hv, hz⟩)
    · rfl
    · refine Prod.ext (Subtype.ext (by simpa using hu)) ?_
      rw [snd_stiefelRotationFamily_eq y (hu.trans hx₀), snd_stiefelRotationFamily_eq x hx₀,
        sphereRotationFamily_eq_sphereRotationFamily_iff _ (x := (_, x.2)) hx]
      exact .inr ⟨hv, hz⟩

/-- A point with `Im z = 0` is sent to `(u, u)` or to `(u, -u)`. -/
theorem stiefelRotationFamily_snd_eq_or_eq_neg_of_im_eq_zero
    {x : stiefel E 2 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im = 0) :
    (stiefelRotationFamily x).2 = (stiefelRotationFamily x).1 ∨
      (stiefelRotationFamily x).2 = -(stiefelRotationFamily x).1 :=
  sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero (stiefelProj E 2 0 x.1)
    (x := (stiefelTangent _ x.1 (coe_stiefelProj 0 x.1).symm, x.2)) hx

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
  -- The two vectors of the frame `![a, v]` are `a` and `v` by definition.
  exact ⟨(⟨_, hframe⟩, z), hz, Prod.ext (Subtype.ext (by simp))
    ((snd_stiefelRotationFamily_eq (p := a) _ rfl).trans hvz)⟩

end TauCeti
