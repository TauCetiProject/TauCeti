/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Null-homotopic loops at the ends of the pair of pants

This file transports null-homotopy of loops `AddCircle 1 → X` along the end charts `endChart` and
`positiveEndChart` of the pair of pants `S = ℂ ∖ {0, 1}`.

## Main results

* `TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul_iff`: reparametrizing by `t ↦ ±t` with the
  sign of an end preserves descending to a null-homotopic map `AddCircle 1 → X`.
* `TauCeti.Floer.forall_exists_nullhomotopic_positiveEndChart`: if `u` is continuous on `S` and
  one end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic, then every positive-end loop
  `t ↦ (u ∘ φ'_q)(s, t)` (`s > 0`) is null-homotopic.
-/

public section

open Set Function Topology TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

/-- Reparametrizing a curve by `t ↦ ±t`, with the sign of the end `q`, preserves descending to a
null-homotopic map `AddCircle 1 → X`. -/
theorem exists_nullhomotopic_comp_endSign_mul_iff {X : Type*} [TopologicalSpace X]
    {q : Puncture} {γ : ℝ → X} :
    (∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ (q.endSign * t)) ↔
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  have fwd {δ : ℝ → X}
      (h : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t) :
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ (q.endSign * t) := by
    obtain ⟨g, hg, hgδ⟩ := h
    have hex := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
    rw [abs_endSign, div_one] at hex
    obtain ⟨g', hg', hg'g⟩ := hex
    exact ⟨g', hg', fun t ↦ (hg'g t).trans (by rw [mul_comm, hgδ])⟩
  refine ⟨fun h ↦ ?_, fwd⟩
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using fwd h

/-- If `u` is continuous on `S = ℂ ∖ {0, 1}` and one end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is
null-homotopic in `X`, then every positive-end loop `t ↦ (u ∘ φ'_q)(s, t)` (`s > 0`) is
null-homotopic in `X`. -/
theorem forall_exists_nullhomotopic_positiveEndChart {X : Type*} [TopologicalSpace X]
    {u : ℝ × ℝ → X} (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture}
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t))) :
    ∀ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s, t) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨s₀, hs₀, hg₀⟩ := hnull
  obtain ⟨g₀, hg₀_null, hg₀_eq⟩ := exists_nullhomotopic_comp_endSign_mul_iff.2 hg₀
  have hg₀_eq' (t : ℝ) : g₀ t = (u ∘ positiveEndChart q) (s₀, t) := by
    simpa only [comp_apply, positiveEndChart_mk] using hg₀_eq t
  intro s hs
  have hper : Function.Periodic (fun t ↦ (u ∘ positiveEndChart q) (s, t)) 1 := fun t ↦ by
    simp only [comp_apply, positiveEndChart_add_one]
  have hcont_s : Continuous fun t ↦ (u ∘ positiveEndChart q) (s, t) :=
    hu.comp_continuous ((contDiff_positiveEndChart q 0).continuous.comp
      (continuous_const.prodMk continuous_id))
      fun t ↦ positiveEndChart_mem_thricePuncturedSphereReal hs
  let g₁ : C(AddCircle (1 : ℝ), X) := ⟨hper.lift, hcont_s.quotient_liftOn' _⟩
  have hg₁_eq (t : ℝ) : g₁ t = (u ∘ positiveEndChart q) (s, t) := hper.lift_coe t
  -- Build the radial homotopy from `g₁` (`τ = 0`) to `g₀` (`τ = 1`) by descending
  -- `(τ, t) ↦ u (φ'_q ((1 - τ) s + τ s₀, t))` along `id × AddCircle.ofUnitInterval 1`.
  let qmap : C(unitInterval × unitInterval, unitInterval × AddCircle (1 : ℝ)) :=
    (ContinuousMap.id unitInterval).prodMap (AddCircle.ofUnitInterval 1)
  have hsurj : Function.Surjective qmap :=
    Function.surjective_id.prodMap AddCircle.surjective_ofUnitInterval
  have hq : IsQuotientMap qmap := qmap.continuous.isClosedMap.isQuotientMap qmap.continuous hsurj
  let rad (τ : unitInterval) : ℝ := (1 - (τ : ℝ)) * s + (τ : ℝ) * s₀
  have hrad_pos (τ : unitInterval) : 0 < rad τ := by
    rcases eq_or_lt_of_le τ.property.1 with h0 | h0
    · simp [rad, ← h0, hs]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 τ.property.2) hs.le)
        (mul_pos h0 hs₀)
  have hcont_rad : Continuous fun p : unitInterval × unitInterval ↦
      (u ∘ positiveEndChart q) (rad p.1, (p.2 : ℝ)) :=
    hu.comp_continuous ((contDiff_positiveEndChart q 0).continuous.comp
      (((Continuous.add ((continuous_const.sub continuous_subtypeVal).mul continuous_const)
        (continuous_subtypeVal.mul continuous_const)).comp continuous_fst).prodMk
        (continuous_subtypeVal.comp continuous_snd)))
      fun p ↦ positiveEndChart_mem_thricePuncturedSphereReal (hrad_pos p.1)
  have hfactors : Function.FactorsThrough
      (fun p : unitInterval × unitInterval ↦ (u ∘ positiveEndChart q) (rad p.1, (p.2 : ℝ)))
      qmap := by
    rintro ⟨τ, t⟩ ⟨τ', t'⟩ h
    change (τ, AddCircle.ofUnitInterval 1 t) = (τ', AddCircle.ofUnitInterval 1 t') at h
    obtain ⟨rfl, ht⟩ := Prod.ext_iff.1 h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := AddCircle.ofUnitInterval_eq_ofUnitInterval_iff.1 ht
    · rfl
    · have h01 := positiveEndChart_add_one q (rad τ) 0
      rw [zero_add] at h01
      simp only [comp_apply, Set.Icc.coe_zero, Set.Icc.coe_one, h01]
    · have h01 := positiveEndChart_add_one q (rad τ) 0
      rw [zero_add] at h01
      simp only [comp_apply, Set.Icc.coe_zero, Set.Icc.coe_one, h01]
  let H : ContinuousMap.Homotopy g₁ g₀ :=
    { toContinuousMap := hq.lift ⟨_, hcont_rad⟩ hfactors
      map_zero_left θ := by
        obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := (1 : ℝ)) θ
        change ((hq.lift ⟨_, hcont_rad⟩ hfactors).comp qmap) (0, t) = _
        rw [DFunLike.congr_fun (hq.lift_comp ⟨_, hcont_rad⟩ hfactors) (0, t)]
        simp [rad, hg₁_eq, AddCircle.ofUnitInterval_apply]
      map_one_left θ := by
        obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := (1 : ℝ)) θ
        change ((hq.lift ⟨_, hcont_rad⟩ hfactors).comp qmap) (1, t) = _
        rw [DFunLike.congr_fun (hq.lift_comp ⟨_, hcont_rad⟩ hfactors) (1, t)]
        simp [rad, hg₀_eq', AddCircle.ofUnitInterval_apply] }
  obtain ⟨c, ⟨H₀⟩⟩ := hg₀_null
  exact ⟨g₁, ⟨c, ⟨H.trans H₀⟩⟩, hg₁_eq⟩

end TauCeti.Floer
