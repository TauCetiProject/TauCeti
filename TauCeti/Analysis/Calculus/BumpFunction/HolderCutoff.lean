/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Smooth cutoffs with uniform Hölder bounds

A smooth compactly supported function `ζ` has one constant `Z` which bounds it, its first and
second derivatives along finitely many directions `e i`, and the `α`-Hölder constants of all of
these, for every `α ≤ 1` (`TauCeti.exists_holderWith_and_abs_le_of_hasCompactSupport`).
Translation keeps these bounds (`TauCeti.holderWith_translate_cutoff`), so the translates of one
cutoff about the origin give cutoffs about every centre with a single constant
(`TauCeti.exists_forall_exists_cutoff`). This uniformity is what localization arguments over
infinitely many balls at once, such as the Schauder estimates, need.
-/

public section

noncomputable section

open Metric Set
open scoped NNReal ContDiff

namespace TauCeti

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translating a cutoff keeps the global Hölder constant and the uniform bound of the cutoff and
of its first and second derivatives in the directions `e i`. -/
theorem holderWith_translate_cutoff (e : ι → E) {α Z : ℝ≥0} {ζ₀ : E → ℝ} (x₀ : E)
    (hZ0 : HolderWith Z α ζ₀ ∧ ∀ x, |ζ₀ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ₀ x (e i)) ∧ ∀ x, |fderiv ℝ ζ₀ x (e i)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ ζ₀) x (e i) (e j)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ₀) x (e i) (e j)| ≤ Z) :
    (HolderWith Z α (fun x => ζ₀ (x - x₀)) ∧ ∀ x, |ζ₀ (x - x₀)| ≤ Z) ∧
    (∀ i, HolderWith Z α (fun x => fderiv ℝ (fun x => ζ₀ (x - x₀)) x (e i)) ∧
      ∀ x, |fderiv ℝ (fun x => ζ₀ (x - x₀)) x (e i)| ≤ Z) ∧
    ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) x (e i) (e j)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) x (e i) (e j)| ≤ Z := by
  have hD1 : fderiv ℝ (fun x => ζ₀ (x - x₀)) = fun x => fderiv ℝ ζ₀ (x - x₀) :=
    funext fun _ => fderiv_comp_sub x₀
  have hD2 : fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) =
      fun x => fderiv ℝ (fderiv ℝ ζ₀) (x - x₀) := by
    rw [hD1]
    exact funext fun _ => fderiv_comp_sub x₀
  have htr {g : E → ℝ} (h : HolderWith Z α g ∧ ∀ x, |g x| ≤ Z) :
      HolderWith Z α (fun x => g (x - x₀)) ∧ ∀ x, |g (x - x₀)| ≤ Z :=
    ⟨fun x y => by simpa only [edist_sub_right] using h.1 (x - x₀) (y - x₀), fun x => h.2 _⟩
  refine ⟨htr hZ0, fun i => ?_, fun i j => ?_⟩
  · rw [hD1]
    exact htr (hZ1 i)
  · rw [hD2]
    exact htr (hZ2 i j)

/-- A smooth function with compact support has one constant `Z` which bounds it, its first and
second derivatives along finitely many directions `e i`, and the `α`-Hölder constants of all of
these. -/
theorem exists_holderWith_and_abs_le_of_hasCompactSupport [Finite ι] (e : ι → E) {α : ℝ≥0}
    (hα : α ≤ 1) {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) :
    ∃ Z : ℝ≥0, (HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z) ∧
      (∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (e i)) ∧ ∀ x, |fderiv ℝ ζ x (e i)| ≤ Z) ∧
      ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ ζ) x (e i) (e j)) ∧
        ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (e i) (e j)| ≤ Z := by
  have := Fintype.ofFinite ι
  have key : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∃ C : ℝ≥0, HolderWith C α φ ∧ ∀ x, |φ x| ≤ C := fun φ hφ hφc => by
    simpa only [Real.norm_eq_abs] using hφ.exists_holderWith_and_norm_le_of_hasCompactSupport hφc hα
  obtain ⟨C₀, hC₀, hM₀⟩ := key ζ (hζ.of_le (by norm_cast)) hc
  choose C₁ hC₁ hM₁ using fun i : ι =>
    key (fun x => fderiv ℝ ζ x (e i))
      ((hζ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const)
      (hc.fderiv_apply (𝕜 := ℝ) _)
  choose C₂ hC₂ hM₂ using fun i j : ι =>
    key (fun x => fderiv ℝ (fderiv ℝ ζ) x (e i) (e j))
      ((((hζ.fderiv_right (m := 2) (by norm_cast)).fderiv_right (m := 1)
        le_rfl).clm_apply contDiff_const).clm_apply contDiff_const)
      (((hc.fderiv (𝕜 := ℝ)).fderiv_apply (𝕜 := ℝ) _).comp_left
        (g := fun L : E →L[ℝ] ℝ => L (e j)) rfl)
  set Z : ℝ≥0 := C₀ + ∑ i, C₁ i + ∑ i, ∑ j, C₂ i j
  have h₀ : C₀ ≤ Z := le_add_right (le_add_right le_rfl)
  have h₁ (i : ι) : C₁ i ≤ Z :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (le_add_right (le_add_self))
  have h₂ (i j : ι) : C₂ i j ≤ Z :=
    ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, C₂ i j) (fun _ _ => zero_le)
        (Finset.mem_univ i))).trans le_add_self
  exact ⟨Z, ⟨hC₀.mono h₀, fun x => (hM₀ x).trans (by exact_mod_cast h₀)⟩,
    fun i => ⟨(hC₁ i).mono (h₁ i), fun x => (hM₁ i x).trans (by exact_mod_cast h₁ i)⟩,
    fun i j => ⟨(hC₂ i j).mono (h₂ i j), fun x => (hM₂ i j x).trans (by exact_mod_cast h₂ i j)⟩⟩

/-- **Uniform cutoffs.** For `ρ < R`, `α ≤ 1` and finitely many directions `e i` there is one
constant `Z` such that about every centre `x₀` some smooth cutoff `ζ`, equal to one near
`closedBall x₀ ρ` and supported in `ball x₀ R`, is bounded by `Z` together with its first and
second derivatives along the directions `e i`, all of which are `α`-Hölder with constant `Z`. The
cutoffs are the translates of one cutoff about the origin. -/
theorem exists_forall_exists_cutoff [FiniteDimensional ℝ E] [Finite ι] (e : ι → E) {α : ℝ≥0}
    (hα : α ≤ 1) {ρ R : ℝ} (hρR : ρ < R) :
    ∃ Z : ℝ≥0, ∀ x₀ : E, ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧
      closedBall x₀ ρ ⊆ interior (ζ ⁻¹' {1}) ∧ tsupport ζ ⊆ ball x₀ R ∧
      (HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z) ∧
      (∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (e i)) ∧ ∀ x, |fderiv ℝ ζ x (e i)| ≤ Z) ∧
      ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ ζ) x (e i) (e j)) ∧
        ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (e i) (e j)| ≤ Z := by
  obtain ⟨ζ₀, hζ₀, -, hζ₀1, hζ₀c, hζ₀s⟩ :=
    (isCompact_closedBall (0 : E) ρ).exists_contDiff_cutoff isOpen_ball
      (closedBall_subset_ball hρR)
  obtain ⟨Z, hZ0, hZ1, hZ2⟩ := exists_holderWith_and_abs_le_of_hasCompactSupport e hα hζ₀ hζ₀c
  refine ⟨Z, fun x₀ => ⟨fun x => ζ₀ (x - x₀), hζ₀.comp (contDiff_id.sub contDiff_const),
    fun x hx => ?_, fun x hx => ?_, holderWith_translate_cutoff e x₀ hZ0 hZ1 hZ2⟩⟩
  · exact preimage_interior_subset_interior_preimage (continuous_id.sub continuous_const)
      (hζ₀1 (by simpa [dist_eq_norm] using hx))
  · simpa [dist_eq_norm] using hζ₀s (tsupport_comp_subset_preimage ζ₀
      (continuous_id.sub continuous_const) hx)

end TauCeti
