/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Regularity estimates from qualitative regularity

Let `N` be a closed subspace of a finite product of `Lᵖ(Ω)` spaces, and `U ⊆ Ω` open. If every
component of every element of `N` is, on `U`, the value of a `W^{k,p}(U)` function, then by the
closed graph theorem this representation is bounded: there is a constant `C` with
`‖v‖_{W^{k,p}(U)} ≤ C ‖θ‖` for the representative `v` of every component of every `θ ∈ N`
(`TauCeti.Wkp.exists_norm_le_of_isClosed`). This turns qualitative interior regularity of the
solutions of a linear equation into an a priori estimate, without tracking constants through the
regularity proof.

## Main results

* `TauCeti.Wkp.exists_norm_le_of_isClosed`: the closed graph estimate.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology

namespace TauCeti.Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Ω U : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {k : ℕ}

/-- **The closed graph estimate.** Let `N` be a closed subspace of `(Lᵖ(Ω))^ι` for a finite
index set `ι`, and `U ≤ Ω` open. If every component `θ c` of every `θ ∈ N` agrees almost everywhere
on `U` with the value of an element of `W^{k,p}(U)`, then there is a constant `C` such that every
such component is represented on `U` by an element `v` with `‖v‖ ≤ C ‖θ‖`. -/
theorem exists_norm_le_of_isClosed {ι : Type*} [Fintype ι] (hUΩ : U ≤ Ω)
    (N : Submodule ℝ (ι → Lp ℝ p (mu.restrict (Ω : Set E))))
    (hN : IsClosed (N : Set (ι → Lp ℝ p (mu.restrict (Ω : Set E)))))
    (h : ∀ θ ∈ N, ∀ c, ∃ v : Wkp mu U p k,
      (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] θ c) :
    ∃ C : ℝ, ∀ θ ∈ N, ∀ c, ∃ v : Wkp mu U p k,
      (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] θ c ∧ ‖v‖ ≤ C * ‖θ‖ := by
  have hU : (U : Set E) ⊆ Ω := hUΩ
  -- An element of `W^{k,p}(U)` is determined by its value.
  have huniq {f : E → ℝ} {v v' : Wkp mu U p k}
      (hv : (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] f)
      (hv' : (value k v' : E → ℝ) =ᵐ[mu.restrict (U : Set E)] f) : v = v' :=
    valueL_injective k (by simpa only [valueL_apply] using Lp.ext (hv.trans hv'.symm))
  choose Φ hΦ using h
  let g : N →ₗ[ℝ] (ι → Wkp mu U p k) :=
    { toFun := fun θ c ↦ Φ θ θ.prop c
      map_add' := fun θ θ' ↦ funext fun c ↦ huniq (hΦ _ (θ + θ').prop c) <| by
        filter_upwards [Lp.coeFn_add (value k (Φ θ θ.prop c)) (value k (Φ θ' θ'.prop c)),
          hΦ θ θ.prop c, hΦ θ' θ'.prop c,
          ae_restrict_of_ae_restrict_of_subset hU (Lp.coeFn_add (θ.val c) (θ'.val c))]
          with x h₁ h₂ h₃ h₄
        simp only [Pi.add_apply, value_add, h₁, h₂, h₃, Submodule.coe_add, h₄]
      map_smul' := fun a θ ↦ funext fun c ↦ huniq (hΦ _ (a • θ).prop c) <| by
        filter_upwards [Lp.coeFn_smul a (value k (Φ θ θ.prop c)), hΦ θ θ.prop c,
          ae_restrict_of_ae_restrict_of_subset hU (Lp.coeFn_smul a (θ.val c))] with x h₁ h₂ h₃
        simp only [RingHom.id_apply, Pi.smul_apply, value_smul, h₁, h₂, Submodule.coe_smul, h₃] }
  have : CompleteSpace N := hN.completeSpace_coe
  -- The value of the representative is the restriction of the component to `U`.
  have hval (θ : N) (c : ι) :
      valueL k (g θ c) = restrictL (mu := mu) (p := p) hUΩ 0 (θ.val c) :=
    Lp.ext <| by
      have h := value_restrictL_ae (mu := mu) (p := p) hUΩ 0 (θ.val c)
      rw [value_zero, value_zero] at h
      rw [valueL_apply]
      exact (hΦ _ θ.prop c).trans h.symm
  have hg : Continuous g := g.continuous_of_seq_closed_graph fun u θ y hu hy ↦ funext fun c ↦ by
    refine valueL_injective k (tendsto_nhds_unique
      (((valueL k).continuous.tendsto _).comp ((continuous_apply c).tendsto _ |>.comp hy)) ?_)
    simp only [Function.comp_def, hval]
    exact ((restrictL hUΩ 0).continuous.tendsto _).comp
      (((continuous_apply c).comp continuous_subtypeVal).tendsto _ |>.comp hu)
  let G : N →L[ℝ] (ι → Wkp mu U p k) := ⟨g, hg⟩
  refine ⟨‖G‖, fun θ hθ c ↦ ⟨Φ θ hθ c, hΦ θ hθ c, ?_⟩⟩
  calc ‖Φ θ hθ c‖ = ‖G ⟨θ, hθ⟩ c‖ := rfl
    _ ≤ ‖G ⟨θ, hθ⟩‖ := norm_le_pi_norm _ c
    _ ≤ ‖G‖ * ‖(⟨θ, hθ⟩ : N)‖ := G.le_opNorm _
    _ = ‖G‖ * ‖θ‖ := rfl

end TauCeti.Wkp
