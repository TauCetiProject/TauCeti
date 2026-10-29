/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.CountableLevels
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Derivatives of real projections

A constant projection has zero projected derivative without regularity assumptions.
Prescribed projected derivatives also hold almost everywhere across exceptional levels.
-/

public section

open MeasureTheory Set
open scoped Topology

/-- A real projection has the prescribed derivative if the curve is differentiable, or if
the derivative of the projected curve vanishes. -/
theorem ContinuousLinearMap.apply_deriv_eq_of_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (π : E →L[ℝ] ℝ) {θ : ℝ → ℝ} {γ : ℝ → E} {θ' t : ℝ}
    (hπ : π ∘ γ = θ) (hθ : HasDerivAt θ θ' t)
    (hγ : DifferentiableAt ℝ γ t ∨ deriv θ t = 0) : π (deriv γ t) = θ' := by
  by_cases hdγ : DifferentiableAt ℝ γ t
  · have hproj := π.hasFDerivAt.comp_hasDerivAt t hdγ.hasDerivAt
    rw [hπ] at hproj
    exact hproj.unique hθ
  · have hzero : θ' = 0 := hθ.deriv.symm.trans (hγ.resolve_left hdγ)
    rw [deriv_zero_of_not_differentiableAt hdγ, map_zero, hzero]

/-- A constant real projection has zero projected derivative, including where the curve
is not differentiable and its total derivative is defined to be zero. -/
theorem ContinuousLinearMap.apply_deriv_eq_zero_of_forall_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) {γ : ℝ → E} {c : ℝ}
    (hγ : ∀ t, L (γ t) = c) (t : ℝ) : L (deriv γ t) = 0 :=
  L.apply_deriv_eq_of_comp (funext hγ) (hasDerivAt_const t c) (Or.inr (deriv_const t c))

/-- A real projection of a curve has the prescribed derivative almost everywhere, even when
exceptional projection levels have uncountable preimages. -/
theorem ContinuousLinearMap.apply_deriv_ae_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {θ θ' : ℝ → ℝ} {γ : ℝ → E}
    (π : E →L[ℝ] ℝ) (hπ : π ∘ γ = θ) {s S : Set ℝ} (hs : s.Countable) (hS : S.Countable)
    (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hdγ : ∀ t ∈ Ioo a b \ s, θ t ∉ S → DifferentiableAt ℝ γ t) :
    (fun t ↦ π (deriv γ t)) =ᵐ[volume.restrict (Ioc a b)] θ' := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((hs.union (Set.toFinite ({a, b} : Set ℝ)).countable).ae_notMem volume),
    hS.ae_deriv_eq_zero_on_preimage θ (volume.restrict (Ioc a b))]
    with t ht hts hlevel
  have htb : t ≠ b := fun h ↦ hts (Or.inr (by simp [h]))
  have ht' : t ∈ Ioo a b \ s :=
    ⟨⟨ht.1, lt_of_le_of_ne ht.2 htb⟩, fun h ↦ hts (Or.inl h)⟩
  apply π.apply_deriv_eq_of_comp hπ (hdθ t ht')
  by_cases hγ : DifferentiableAt ℝ γ t
  · exact Or.inl hγ
  · have hmem : θ t ∈ S := by
      by_contra h
      exact hγ (hdγ t ht' h)
    exact Or.inr (hlevel hmem)
