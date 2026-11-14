/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Vertical-strip asymptotic combinators

Asymptotics on vertical strips in the complex plane are stated in two standard filter forms:

* in real coordinates `(σ, t) : ℝ × ℝ` along the product filter `𝓟 s ×ˢ cocompact ℝ`, expressing
  uniformity in `σ ∈ s` as `|t| → ∞`;
* directly on `z : ℂ` along `cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Set.Icc a b)`, where bounded real
  part forces `|z.im| → ∞` along `cocompact ℂ`.

This module packages explicit height-threshold inequalities `‖g p‖ ≤ C * ‖u p‖` (for `T ≤ |p.2|`)
and `‖f z‖ ≤ C * ‖u z‖` (for `T ≤ |z.im|`) into both `IsBigO` forms, provides the `O(1)` and
`O(|t|⁻¹)` specializations, and restricts `𝓟 s ×ˢ cocompact ℝ` bounds to individual vertical lines
`Re z = σ` (`σ ∈ s`) along `cocompact ℝ`.

## Main results

* `Asymptotics.isBigO_vertical_of_exists`, `Asymptotics.isBigO_vertical_strip_of_exists`:
  scale-polymorphic `IsBigO` packaging from explicit height thresholds.
* `Asymptotics.isBigO_one_vertical_of_exists`, `Asymptotics.isBigO_one_vertical_strip_of_exists`,
  `Asymptotics.isBigO_inv_vertical_of_exists`, `Asymptotics.isBigO_inv_vertical_strip_of_exists`:
  `O(1)` and `O(|t|⁻¹)` specializations.
* `Asymptotics.IsBigO.cocompact_of_vertical`: restrict a uniform vertical-set bound to a single
  vertical line `σ ∈ s`.
-/

public section

open Filter Set

namespace Asymptotics

/-- Package a uniform bound `‖g p‖ ≤ C * ‖u p‖` for `p.1 ∈ s` and `T ≤ |p.2|` into
`g =O[𝓟 s ×ˢ cocompact ℝ] u`. -/
theorem isBigO_vertical_of_exists {E F : Type*} [Norm E] [Norm F] {s : Set ℝ}
    {g : ℝ × ℝ → E} {u : ℝ × ℝ → F}
    (h : ∃ C T : ℝ, ∀ p : ℝ × ℝ, p.1 ∈ s → T ≤ |p.2| → ‖g p‖ ≤ C * ‖u p‖) :
    g =O[𝓟 s ×ˢ cocompact ℝ] u := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  exact hCT p hp.1 hp.2

/-- Package a uniform bound `‖f z‖ ≤ C * ‖u z‖` on a compact vertical strip `z.re ∈ Icc a b` for
`T ≤ |z.im|` into `f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] u`. -/
theorem isBigO_vertical_strip_of_exists {E F : Type*} [Norm E] [Norm F] {a b : ℝ}
    {f : ℂ → E} {u : ℂ → F}
    (h : ∃ C T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖f z‖ ≤ C * ‖u z‖) :
    f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] u := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ z : ℂ in cocompact ℂ, T + max |a| |b| ≤ ‖z‖ :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop _
  filter_upwards [hT.filter_mono inf_le_left,
    (eventually_principal.2 fun _ hz ↦ hz).filter_mono inf_le_right] with z hz hre
  have hM : |z.re| ≤ max |a| |b| := abs_le_max_abs_abs hre.1 hre.2
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  exact hCT z hre (by linarith)

/-- Package a uniform bound `‖g p‖ ≤ C` for `p.1 ∈ s` and `T ≤ |p.2|` into
`g =O[𝓟 s ×ˢ cocompact ℝ] 1`. -/
theorem isBigO_one_vertical_of_exists {E : Type*} [Norm E] {s : Set ℝ} {g : ℝ × ℝ → E}
    (h : ∃ C T : ℝ, ∀ p : ℝ × ℝ, p.1 ∈ s → T ≤ |p.2| → ‖g p‖ ≤ C) :
    g =O[𝓟 s ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, T, hCT⟩ := h
  exact isBigO_vertical_of_exists ⟨C, T, fun p hp ht ↦ by simpa using hCT p hp ht⟩

/-- Package a uniform bound `‖f z‖ ≤ C` on `z.re ∈ Icc a b` for `T ≤ |z.im|` into
`f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] 1`. -/
theorem isBigO_one_vertical_strip_of_exists {E : Type*} [Norm E] {a b : ℝ} {f : ℂ → E}
    (h : ∃ C T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖f z‖ ≤ C) :
    f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, T, hCT⟩ := h
  exact isBigO_vertical_strip_of_exists ⟨C, T, fun z hre ht ↦ by simpa using hCT z hre ht⟩

/-- Package a uniform bound `‖g p‖ ≤ C / |p.2|` for `p.1 ∈ s` and `T ≤ |p.2|` into
`g =O[𝓟 s ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹`. -/
theorem isBigO_inv_vertical_of_exists {E : Type*} [Norm E] {s : Set ℝ} {g : ℝ × ℝ → E}
    (h : ∃ C T : ℝ, ∀ p : ℝ × ℝ, p.1 ∈ s → T ≤ |p.2| → ‖g p‖ ≤ C / |p.2|) :
    g =O[𝓟 s ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, hCT⟩ := h
  refine isBigO_vertical_of_exists ⟨C, T, fun p hp ht ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact hCT p hp ht

/-- Package a uniform bound `‖f z‖ ≤ C / |z.im|` on `z.re ∈ Icc a b` for `T ≤ |z.im|` into
`f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ |z.im|⁻¹`. -/
theorem isBigO_inv_vertical_strip_of_exists {E : Type*} [Norm E] {a b : ℝ} {f : ℂ → E}
    (h : ∃ C T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖f z‖ ≤ C / |z.im|) :
    f =O[cocompact ℂ ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ |z.im|⁻¹ := by
  obtain ⟨C, T, hCT⟩ := h
  refine isBigO_vertical_strip_of_exists ⟨C, T, fun z hre ht ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact hCT z hre ht

/-- Restrict a vertical-strip asymptotic along `𝓟 s ×ˢ cocompact ℝ` to the vertical line
`Re z = σ` (`σ ∈ s`) along `cocompact ℝ`. -/
theorem IsBigO.cocompact_of_vertical {E F : Type*} [Norm E] [Norm F] {s : Set ℝ} {σ : ℝ}
    {g : ℝ × ℝ → E} {u : ℝ × ℝ → F} (hg : g =O[𝓟 s ×ˢ cocompact ℝ] u) (hσ : σ ∈ s) :
    (fun t : ℝ ↦ g (σ, t)) =O[cocompact ℝ] fun t ↦ u (σ, t) :=
  hg.comp_tendsto ((tendsto_principal.2 (Eventually.of_forall fun _ ↦ hσ)).prodMk tendsto_id)

end Asymptotics
