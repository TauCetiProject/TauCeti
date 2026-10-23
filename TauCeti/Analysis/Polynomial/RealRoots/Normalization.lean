/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.Normalization
public import TauCeti.Analysis.Analytic.FiniteFamily
import Mathlib.Analysis.Analytic.Constructions

/-!
# Descending analytic roots of integral normalizations

An analytic enumeration of the distinct real roots of an integral normalization descends to
an ordered analytic enumeration of the original family's roots near a nonzero fiber. Divide
the normalized branches by the leading coefficient and choose one fixed ordering on a common
neighborhood. The number of distinct roots and all multiplicities are preserved.

Only the leading coefficient needs to be analytic for this transport. No regularity of the
other coefficients, degree constancy, or positivity of the leading coefficient is required.
The label equivalence records that no normalized root is discarded. Constants and empty
root lists are included.

This supplies the descent from monic analytic preparation to nonmonic real root sections,
including preparation of formal reflections whose degree exceeds that of the original fiber.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3 (monic preparation and analytic delineability).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-- Descend distinct analytic roots of an integral normalization by dividing by the leading
coefficient. A fixed equivalence of labels orders the original roots on an open neighborhood,
and every positive root multiplicity is retained. -/
theorem exists_analyticOnNhd_ordered_roots_of_integralNormalization
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
    {F : E → ℝ[X]} {r : ι → E → ℝ} {x₀ : E}
    (hlc : AnalyticAt ℝ (fun x ↦ (F x).leadingCoeff) x₀) (hF : F x₀ ≠ 0)
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀) (hinj : Injective (fun i ↦ r i x₀))
    (hroots : ∀ᶠ x in 𝓝 x₀, ∀ t,
      (F x).integralNormalization.IsRoot t ↔ ∃ i, r i x = t)
    (hmult : ∀ᶠ x in 𝓝 x₀, ∀ i,
      (F x).integralNormalization.rootMultiplicity (r i x) =
        (F x₀).integralNormalization.rootMultiplicity (r i x₀)) :
    ∃ k : ℕ, ∃ e : Fin k ≃ ι, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (fun x ↦ r (e i) x / (F x).leadingCoeff) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ r (e i) x / (F x).leadingCoeff)) ∧
      (∀ x ∈ U, ∀ t, (F x).IsRoot t ↔ ∃ i, r (e i) x / (F x).leadingCoeff = t) ∧
      (∀ i, 0 < (F x₀).rootMultiplicity (r (e i) x₀ / (F x₀).leadingCoeff)) ∧
      ∀ x ∈ U, ∀ i,
        (F x).rootMultiplicity (r (e i) x / (F x).leadingCoeff) =
          (F x₀).rootMultiplicity (r (e i) x₀ / (F x₀).leadingCoeff) := by
  classical
  let f : ι → E → ℝ := fun i x ↦ r i x / (F x).leadingCoeff
  have hlc0 := leadingCoeff_ne_zero.2 hF
  have hf (i : ι) : AnalyticAt ℝ (f i) x₀ := (hr i).div hlc hlc0
  have hfi : Injective (fun i ↦ f i x₀) := fun i j hij ↦
    hinj ((div_left_inj' hlc0).mp hij)
  obtain ⟨k, e, V, hV, hxV, ha, horder⟩ :=
    exists_analyticOnNhd_strictMono_range_eq hf
      (fun i j hij ↦ by obtain rfl := hfi hij; exact .rfl)
  -- Range equality at the center makes the selected labels a bijection: division
  -- by a nonzero coefficient cannot merge or discard any distinct root.
  have he : Surjective e := by
    intro j
    obtain ⟨i, hi⟩ := (horder x₀ hxV).2.symm ▸ mem_range_self j
    exact ⟨i, hfi hi⟩
  let e' : Fin k ≃ ι := Equiv.ofBijective e ⟨e.injective, he⟩
  have hne : ∀ᶠ x in 𝓝 x₀, (F x).leadingCoeff ≠ 0 := hlc.continuousAt.eventually_ne hlc0
  have htransport (x : E) (hx : (F x).leadingCoeff ≠ 0) (i : ι) :
      (F x).rootMultiplicity (f i x) =
        (F x).integralNormalization.rootMultiplicity (r i x) := by
    rw [← (F x).rootMultiplicity_integralNormalization_mul]
    simp only [f, mul_div_cancel₀ _ hx]
  have hcover : ∀ᶠ x in 𝓝 x₀, ∀ t, (F x).IsRoot t ↔ ∃ i : ι, f i x = t := by
    filter_upwards [hne, hroots] with x hx hxr t
    rw [← (F x).isRoot_integralNormalization_mul_iff, hxr]
    exact exists_congr fun i ↦ by simp only [f, div_eq_iff hx, mul_comm]
  have hm : ∀ᶠ x in 𝓝 x₀, ∀ i, (F x).rootMultiplicity (f i x) =
      (F x₀).rootMultiplicity (f i x₀) := by
    filter_upwards [hne, hmult] with x hx hmx i
    rw [htransport x hx i, htransport x₀ hlc0 i]
    exact hmx i
  obtain ⟨U, hU, hopen, hxU⟩ := eventually_nhds_iff.1
    (Filter.Eventually.and (hV.mem_nhds hxV) (hcover.and hm))
  refine ⟨k, e', U, hopen, hxU,
    fun i ↦ (ha i).mono (fun x hx ↦ (hU x hx).1),
    fun x hx ↦ (horder x (hU x hx).1).1, ?_, ?_,
    fun x hx i ↦ (hU x hx).2.2 (e' i)⟩
  · intro x hx t
    rw [(hU x hx).2.1 t]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨e'.symm j, by simpa only [e'.apply_symm_apply] using hj⟩,
      fun ⟨i, hi⟩ ↦ ⟨e' i, hi⟩⟩
  · intro i
    apply (rootMultiplicity_pos hF).2
    exact hcover.self_of_nhds _ |>.2 ⟨e' i, rfl⟩

end TauCeti
