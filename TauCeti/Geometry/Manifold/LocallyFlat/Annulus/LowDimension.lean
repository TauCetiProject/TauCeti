/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Annulus.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Annulus
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# The low-dimensional annulus theorem

This file proves the low-dimensional cases `n = 0` and `n = 1` (`ℝ¹` and `ℝ²`) of the annulus
conjecture without any local flatness hypothesis, in any real normed space of dimension `1` or `2`.

* In dimension `1` (`n = 0`), every pair of distinct points is a round sphere, so any two maps of
  the unit sphere `{±u}` with the inner one injective and nested images cobound an annulus
  (`TauCeti.coboundAnnulus_of_finrank_eq_one`), a pair of closed intervals.
* In dimension `2` (`n = 1`), continuous injections `S¹ → ℂ` trace nested Jordan curves, which
  cobound an annulus by the planar annulus theorem
  (`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`), and transport along
  `ContinuousLinearEquiv.ofFinrankEq` and `TauCeti.sphereHomeomorphOfFinrankEq` yields
  `TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`,
  `TauCeti.annulusConjecture_one`, and `TauCeti.annulusConjecture_of_le_one`.

## Main results

* `TauCeti.coboundAnnulus_of_finrank_eq_one`: on a line, two nested pairs of points cobound an
  annulus.
* `TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`: any two nested continuous
  injections `S¹ → E` in a two-dimensional real normed space cobound an annulus.
* `TauCeti.annulusConjecture_zero`, `TauCeti.annulusConjecture_one`,
  `TauCeti.annulusConjecture_of_le_one`: the annulus conjecture holds for `n ≤ 1`.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric Set

/-! ### Spheres of dimension zero -/

section DimensionZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a line, identified with `ℝ` by `φ`, the image of any map of the unit sphere `{±φ 1}` is a
round sphere, of positive radius when the map is injective. -/
private theorem exists_range_eq_sphere (hE : Module.finrank ℝ E = 1) (φ : ℝ ≃ₗᵢ[ℝ] E)
    (f : sphere (0 : E) 1 → E) :
    ∃ μ ρ : ℝ, 0 ≤ ρ ∧ (Function.Injective f → 0 < ρ) ∧ range f = sphere (φ μ) ρ := by
  have hu : φ 1 ∈ sphere (0 : E) 1 := by simp
  have hv : φ (-1) ∈ sphere (0 : E) 1 := by simp
  have hsph : ∀ x : sphere (0 : E) 1, x = ⟨φ 1, hu⟩ ∨ x = ⟨φ (-1), hv⟩ := fun x => by
    simpa [Subtype.ext_iff] using
      eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hE (x := (x : E)) (y := φ 1) (by simp)
  set α := φ.symm (f ⟨φ 1, hu⟩)
  set β := φ.symm (f ⟨φ (-1), hv⟩)
  refine ⟨(α + β) / 2, |α - β| / 2, by positivity, fun hf => ?_, ?_⟩
  · have hαβ : α ≠ β := fun h => by
      have := hf (φ.symm.injective h)
      simp only [Subtype.mk.injEq, φ.injective.eq_iff] at this
      norm_num at this
    exact half_pos (abs_pos.2 (sub_ne_zero.2 hαβ))
  ext y
  obtain ⟨s, rfl⟩ := φ.surjective y
  have hα : f ⟨φ 1, hu⟩ = φ α := (φ.apply_symm_apply _).symm
  have hβ : f ⟨φ (-1), hv⟩ = φ β := (φ.apply_symm_apply _).symm
  have hmem : φ s ∈ range f ↔ s = α ∨ s = β := by
    constructor
    · rintro ⟨x, hx⟩
      rcases hsph x with rfl | rfl
      · exact .inl (φ.injective (hx.symm.trans hα))
      · exact .inr (φ.injective (hx.symm.trans hβ))
    · rintro (rfl | rfl)
      · exact ⟨_, hα⟩
      · exact ⟨_, hβ⟩
  rw [hmem, mem_sphere, φ.dist_map, Real.dist_eq,
    show |α - β| / 2 = |(α - β) / 2| by rw [abs_div, abs_two], abs_eq_abs]
  constructor
  · rintro (rfl | rfl)
    · exact .inl (by ring)
    · exact .inr (by ring)
  · rintro (h | h)
    · exact .inl (by linarith)
    · exact .inr (by linarith)

/-- **The annulus theorem on a line:** in a one-dimensional real normed space, two maps `f` and `g`
of the unit sphere `{±u}`, with `g` injective and the image of `g` in the open region bounded by the
image of `f`, cobound an annulus. The two pairs of points are the endpoints of nested intervals,
and the annulus is the pair of closed intervals between them. Injectivity of `f` is not assumed: a
map with a single value bounds no region. -/
theorem coboundAnnulus_of_finrank_eq_one (hE : Module.finrank ℝ E = 1) {f g : sphere (0 : E) 1 → E}
    (hg : Function.Injective g) (hfg : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  -- identify the line with `ℝ` isometrically
  obtain ⟨φ⟩ := nonempty_linearIsometryEquiv_of_finrank_eq_one hE
  obtain ⟨μ, R, hR, -, hfR⟩ := exists_range_eq_sphere hE φ f
  obtain ⟨γ, r, -, hr, hgr⟩ := exists_range_eq_sphere hE φ g
  have hr := hr hg
  refine coboundAnnulus_of_range_eq_sphere hfR hgr hr ?_
  rw [hfR, hgr, filledHull_sphere _ hR] at hfg
  -- both points of the inner sphere lie strictly inside the outer one
  have hlt : ∀ s, |s - γ| = r → |s - μ| < R := fun s hs => by
    have hs' : φ s ∈ sphere (φ γ) r := by rwa [mem_sphere, φ.dist_map, Real.dist_eq]
    obtain ⟨h₁, h₂⟩ := hfg hs'
    rw [mem_closedBall, φ.dist_map, Real.dist_eq] at h₁
    rw [mem_sphere, φ.dist_map, Real.dist_eq] at h₂
    exact lt_of_le_of_ne h₁ h₂
  have h₁ := hlt (γ + r) (by rw [add_sub_cancel_left, abs_of_pos hr])
  have h₂ := hlt (γ - r) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr])
  rw [φ.dist_map, Real.dist_eq]
  rw [abs_lt] at h₁ h₂
  rcases le_total γ μ with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- **The annulus theorem for `0`-spheres:** two nested pairs of points on the real line cobound
an annulus, a pair of closed intervals. Local flatness enters only through the injectivity of the
inner pair. -/
theorem annulusConjecture_zero : AnnulusConjecture 0 := by
  rw [annulusConjecture_iff]
  exact fun _ _ _ hg hfg =>
    coboundAnnulus_of_finrank_eq_one (finrank_euclideanSpace_fin (𝕜 := ℝ)) hg.injective hfg

end DimensionZero

/-! ### Spheres of dimension one -/

section DimensionOne

open Function

private theorem coboundAnnulus_of_continuous_injective_complex {f g : sphere (0 : ℂ) 1 → ℂ}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have hC₁ : IsJordanCurve (range f) :=
    (sphereCircleHomeomorph 0 one_pos).isJordanCurve_range hfc hfi
  have hC₂ : IsJordanCurve (range g) :=
    (sphereCircleHomeomorph 0 one_pos).isJordanCurve_range hgc hgi
  rw [coboundAnnulus_iff_exists_homeomorph]
  exact hC₁.exists_homeomorph_sphere_prod_unitInterval hC₂ hsub

/-- **The two-dimensional annulus theorem in any two-dimensional real normed space.** Any two
continuous injections `f g : sphere (0 : E) 1 → E` with
`range g ⊆ filledHull (range f) \ range f` cobound an annulus. No local flatness hypothesis is
needed. -/
theorem coboundAnnulus_of_continuous_injective_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 2) {f g : sphere (0 : E) 1 → E}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have hEF : Module.finrank ℝ E = Module.finrank ℝ ℂ := by simp [hE]
  let e : E ≃ₜ ℂ := (ContinuousLinearEquiv.ofFinrankEq hEF).toHomeomorph
  let es : sphere (0 : E) 1 ≃ₜ sphere (0 : ℂ) 1 := sphereHomeomorphOfFinrankEq hEF
  have he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s := fun _ => e.isBounded_image_iff
  rw [← coboundAnnulus_homeomorph_comp_iff e he, ← coboundAnnulus_comp_homeomorph_iff es.symm]
  exact coboundAnnulus_of_continuous_injective_complex
    (e.continuous.comp (hfc.comp es.symm.continuous))
    (e.injective.comp (hfi.comp es.symm.injective))
    (e.continuous.comp (hgc.comp es.symm.continuous))
    (e.injective.comp (hgi.comp es.symm.injective))
    (by simpa only [range_comp, es.symm.surjective.range_comp] using
      (e.image_subset_filledHull_sdiff_iff he (range g) (range f)).mpr hsub)

/-- **The annulus conjecture holds in dimension `2` (`n = 1`).** -/
theorem annulusConjecture_one : AnnulusConjecture 1 := by
  rw [annulusConjecture_iff]
  exact fun _ _ hf hg hsub =>
    coboundAnnulus_of_continuous_injective_of_finrank_eq_two (by simp)
      hf.continuous hf.injective hg.continuous hg.injective hsub

/-- **The annulus conjecture holds in dimensions `1` and `2` (`n ≤ 1`).** -/
theorem annulusConjecture_of_le_one {n : ℕ} (hn : n ≤ 1) : AnnulusConjecture n := by
  match n with
  | 0 => exact annulusConjecture_zero
  | 1 => exact annulusConjecture_one

end DimensionOne

end TauCeti
