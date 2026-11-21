/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Analysis.Complex.Inversion
import TauCeti.Analysis.Complex.Runge.Rational
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Riemann-sphere rational Runge approximation

Let `K ⊆ ℂ` be a compact set and `A ⊆ ℂ` a prescribed set of poles meeting every connected
component of `Kᶜ`, including the unbounded component. Choosing `a₀ ∈ A \ filledHull K`, the
Möbius inversion `z ↦ (z - a₀)⁻¹` sends `a₀` to `∞` and `∞` to `0`, keeping `0` outside the filled
hull of the inverted compact set (`IsClosed.notMem_filledHull_inv_sub_image`). Applying finite-pole
rational Runge approximation (`IsCompact.exists_rational_norm_sub_lt`) on the inverted domain and
homogenizing the resulting rational function in `(z - a₀)` yields a uniform rational approximant
`p / q` with `p.natDegree ≤ q.natDegree` and all finite poles in `A \ K`.

## Main results

* `IsCompact.exists_rational_natDegree_le_norm_sub_lt`: uniform approximation by rational functions
  bounded at `∞` (`p.natDegree ≤ q.natDegree`) with finite poles in `A \ K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.7, p. 29.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6.
-/

public section

open Bornology Polynomial Set

namespace TauCeti

/-- If `A` meets every connected component of `Kᶜ` and `a₀ ∈ A \ filledHull K`, then under
`z ↦ (z - a₀)⁻¹` the set `(fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀})` meets every bounded component of
`((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`. -/
private theorem inv_sub_image_meets_bounded_components {K A : Set ℂ} {a₀ : ℂ} (hK : IsCompact K)
    (ha₀ : a₀ ∉ filledHull K) (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty) :
    ∀ w ∈ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) \ ((fun z ↦ (z - a₀)⁻¹) '' K),
      ((fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀}) ∩
        connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ w).Nonempty := by
  let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  have hφ_inj : Function.Injective φ := inv_injective.comp (sub_left_injective (b := a₀))
  have hφ_cont : ContinuousOn φ {a₀}ᶜ :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦ hz (sub_eq_zero.mp h)
  obtain ⟨h0_not, hD_sub⟩ := hK.isClosed.notMem_filledHull_inv_sub_image ha₀
  rintro w ⟨hwH, hwK'⟩
  have hw0 : w ≠ 0 := fun h ↦ h0_not (h ▸ hwH)
  set x : ℂ := a₀ + w⁻¹
  have hxa₀ : x ≠ a₀ := fun h ↦ inv_ne_zero hw0 (by simpa [x] using h)
  have hφx : φ x = w := by simp [φ, x]
  have hxK : x ∈ Kᶜ := fun hxK ↦ hwK' ⟨x, hxK, hφx⟩
  have ha₀_not_comp : a₀ ∉ connectedComponentIn Kᶜ x := by
    intro hmem
    have hxD : x ∈ connectedComponentIn Kᶜ a₀ :=
      (connectedComponentIn_eq hmem).symm ▸ mem_connectedComponentIn hxK
    have hw0c : w ∈ connectedComponentIn (φ '' K)ᶜ 0 := hD_sub ⟨x, ⟨hxD, hxa₀⟩, hφx⟩
    exact h0_not (mem_filledHull_iff.mpr <|
      (connectedComponentIn_eq hw0c).symm ▸ mem_filledHull_iff.mp hwH)
  obtain ⟨b, hbA, hbc⟩ := hA x hxK
  have hba₀ : b ≠ a₀ := fun h ↦ ha₀_not_comp (h ▸ hbc)
  have himg_sub : φ '' connectedComponentIn Kᶜ x ⊆ (φ '' K)ᶜ :=
    Set.subset_compl_iff_disjoint_right.mpr <| (Set.disjoint_image_iff hφ_inj).mpr <|
      Set.subset_compl_iff_disjoint_right.mp (connectedComponentIn_subset Kᶜ x)
  have hcomp_sub : φ '' connectedComponentIn Kᶜ x ⊆ connectedComponentIn (φ '' K)ᶜ w :=
    (isPreconnected_connectedComponentIn.image φ
      (hφ_cont.mono fun _ hz hza ↦ ha₀_not_comp (hza ▸ hz))).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxK, hφx⟩ himg_sub
  exact ⟨φ b, ⟨b, ⟨hbA, hba₀⟩, rfl⟩, hcomp_sub ⟨b, hbc, rfl⟩⟩

/-- Pulling back a holomorphic function `f` on `U ⊇ K` along the Möbius inversion
`w ↦ a₀ + w⁻¹` yields a holomorphic function on the open neighbourhood
`{0}ᶜ ∩ (fun w ↦ a₀ + w⁻¹) ⁻¹' U` of the compact set `(fun z ↦ (z - a₀)⁻¹) '' K`. -/
private theorem inv_sub_pullback_data {K U : Set ℂ} {a₀ : ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (ha₀K : a₀ ∉ K) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    IsCompact ((fun z ↦ (z - a₀)⁻¹) '' K) ∧
      IsOpen (({0}ᶜ : Set ℂ) ∩ (fun w ↦ a₀ + w⁻¹) ⁻¹' U) ∧
      (fun z ↦ (z - a₀)⁻¹) '' K ⊆ ({0}ᶜ : Set ℂ) ∩ (fun w ↦ a₀ + w⁻¹) ⁻¹' U ∧
      DifferentiableOn ℂ (fun w ↦ f (a₀ + w⁻¹)) (({0}ᶜ : Set ℂ) ∩ (fun w ↦ a₀ + w⁻¹) ⁻¹' U) := by
  have hφ_cont : ContinuousOn (fun z ↦ (z - a₀)⁻¹) K :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦ by
      have hza : z = a₀ := sub_eq_zero.mp h
      exact ha₀K (hza ▸ hz)
  have hψ_diff : DifferentiableOn ℂ (fun w ↦ a₀ + w⁻¹) {0}ᶜ :=
    DifferentiableOn.add (differentiableOn_const a₀)
      (DifferentiableOn.inv differentiableOn_id fun _ hw ↦ hw)
  refine ⟨hK.image_of_continuousOn hφ_cont,
    hψ_diff.continuousOn.isOpen_inter_preimage isOpen_compl_singleton hU, ?_,
    DifferentiableOn.comp hf (hψ_diff.mono inter_subset_left) inter_subset_right⟩
  rintro _ ⟨z, hzK, rfl⟩
  exact ⟨inv_ne_zero (sub_ne_zero.mpr fun h ↦ ha₀K (h ▸ hzK)), by simpa using hKU hzK⟩

/-- **Riemann-sphere rational Runge approximation.** Let `K ⊆ ℂ` be compact and `A ⊆ ℂ` meet every
connected component of `Kᶜ`, including the unbounded component. Then every function holomorphic on
an open neighbourhood `U` of `K` can be uniformly approximated on `K` by rational functions `p / q`
with `p.natDegree ≤ q.natDegree` (hence bounded at `∞`) and all finite poles in `A \ K`. -/
theorem _root_.IsCompact.exists_rational_natDegree_le_norm_sub_lt {K U A : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ p.natDegree ≤ q.natDegree ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  obtain ⟨x₀, hx₀⟩ := nonempty_compl_filledHull hK.isBounded
  obtain ⟨a₀, ha₀A, ha₀c⟩ := hA x₀ fun hxK ↦ hx₀ (subset_filledHull hxK)
  have ha₀ : a₀ ∉ filledHull K := by
    rwa [← mem_compl_iff,
      compl_filledHull_eq_connectedComponentIn Complex.one_lt_rank_real hK.isBounded hx₀]
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  set φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  obtain ⟨hK', hU', hK'U', hf'⟩ := inv_sub_pullback_data hK hU hKU ha₀K hf
  obtain ⟨P, Q, -, hQA', happrox⟩ := hK'.exists_rational_norm_sub_lt hU' hK'U'
    (inv_sub_image_meets_bounded_components hK ha₀ hA) hf' hε
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro h0
    obtain ⟨b, ⟨-, hba⟩, hb0⟩ := (hQA' 0 h0).1
    exact inv_ne_zero (sub_ne_zero.mpr hba) hb0
  set d := max P.natDegree Q.natDegree
  refine ⟨(P.reflect d).comp (X - C a₀), (Q.reflect d).comp (X - C a₀),
    ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · intro hq0
    exact hQ0 (by
      rw [← coeff_reflect_comp_X_sub_C a₀ (le_max_right _ _), hq0, coeff_zero])
  · exact (natDegree_reflect_comp_X_sub_C_le a₀ (le_max_left _ _)).trans
      (le_natDegree_of_ne_zero (by rwa [coeff_reflect_comp_X_sub_C a₀ (le_max_right _ _)]))
  · by_cases hza : z = a₀
    · exact hza ▸ ⟨ha₀A, ha₀K⟩
    · rw [eval_reflect_comp_X_sub_C (le_max_right _ _) hza, mul_eq_zero] at hz
      have hQz : Q.eval (φ z) = 0 := hz.resolve_left (pow_ne_zero d (sub_ne_zero.mpr hza))
      obtain ⟨⟨b, ⟨hbA, -⟩, hbz⟩, hzK'⟩ := hQA' (φ z) hQz
      exact ⟨sub_left_injective (inv_injective hbz) ▸ hbA, fun hzK ↦ hzK' ⟨z, hzK, rfl⟩⟩
  · have hza : z ≠ a₀ := fun h ↦ ha₀K (h ▸ hz)
    rw [eval_reflect_comp_X_sub_C (le_max_left _ _) hza,
      eval_reflect_comp_X_sub_C (le_max_right _ _) hza,
      mul_div_mul_left _ _ (pow_ne_zero d (sub_ne_zero.mpr hza))]
    simpa [φ] using happrox (φ z) ⟨z, hz, rfl⟩

end TauCeti
