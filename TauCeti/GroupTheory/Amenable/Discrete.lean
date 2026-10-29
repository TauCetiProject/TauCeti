/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Discrete invariant means

On a discrete group, means on `TauCeti.UCB G` correspond bijectively to positive real linear
functionals on all bounded functions which take the value one at the constant one. The
correspondence preserves left invariance. This gives a bounded-function characterization of
amenability suitable for constructing finitely additive probabilities from indicator functions.
Amenability with the discrete topology also implies amenability with any group topology.

A mean on a discrete group `G` also pushes forward along an arbitrary map `r : G → H`, by
`f ↦ m (f ∘ r)` (`TauCeti.Mean.mapOfDiscrete`). When `r (φ h * x) = h * r x` for a homomorphism
`φ : H →* G`, the pushforward of a left-invariant mean is left invariant.

The function-space identification is `TauCeti.UCB.discreteAlgEquiv`; the normalization and
positivity use Mathlib's `PositiveLinearMap`, without an additional continuity assumption.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 1.12–1.13 and Theorem 1.15
  (for discrete groups).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

section Discrete

variable [DiscreteTopology G]

namespace Mean

variable (G) in
/-- Means on a discrete group correspond to normalized positive linear functionals on all
bounded functions. -/
def boundedContinuousFunctionEquiv :
    Mean G ≃ {m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1} where
  toFun m := ⟨{
    toLinearMap :=
      m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.discreteAlgEquiv G).symm.toLinearMap
    monotone' := fun _ _ h => OrderHomClass.mono m
      (UCB.discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff.2 h) },
    (congrArg m ((UCB.discreteAlgEquiv G).symm.map_one)).trans m.map_one⟩
  invFun m := mk₀ (m.1.toLinearMap ∘ₗ (UCB.discreteAlgEquiv G).toLinearMap)
    (fun f hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m.1 (by
        simpa only [UCB.discreteAlgEquiv_apply, ZeroMemClass.coe_zero] using
          (Subtype.coe_le_coe.2 hf)))
    (by simpa using m.2)
  left_inv m := by
    ext f
    rw [mk₀_apply]
    exact congrArg m ((UCB.discreteAlgEquiv G).symm_apply_apply f)
  right_inv m := by
    apply Subtype.ext
    apply PositiveLinearMap.toLinearMap_injective
    ext f
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap, mk₀_apply,
      AlgEquiv.apply_symm_apply]

@[simp]
theorem boundedContinuousFunctionEquiv_apply (m : Mean G) (f : G →ᵇ ℝ) :
    (boundedContinuousFunctionEquiv G m).1 f = m ((UCB.discreteAlgEquiv G).symm f) :=
  (rfl)

@[simp]
theorem boundedContinuousFunctionEquiv_symm_apply
    (m : {m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1}) (f : UCB G) :
    (boundedContinuousFunctionEquiv G).symm m f = m.1 (f : G →ᵇ ℝ) := by
  simp [boundedContinuousFunctionEquiv]

/-- The correspondence of means preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_boundedContinuousFunction (m : Mean G) :
    m.IsLeftInvariant ↔ ∀ (g : G) (f : G →ᵇ ℝ),
      (boundedContinuousFunctionEquiv G m).1
          (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) =
        (boundedContinuousFunctionEquiv G m).1 f := by
  rw [isLeftInvariant_iff]
  constructor
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeft] using
      hm g ((UCB.discreteAlgEquiv G).symm f)
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeft, AlgEquiv.symm_apply_apply] using
      hm g (UCB.discreteAlgEquiv G f)

section MapOfDiscrete

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The pushforward `f ↦ m (f ∘ r)` of a mean `m` on a discrete group `G` along an arbitrary map
`r : G → H` into a topological group, as a mean on `UCB H`. -/
def mapOfDiscrete (r : G → H) (m : Mean G) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.compRightAlgHomOfDiscrete r).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using UCB.monotone_compRightAlgHomOfDiscrete r hf))
    (by simp)

@[simp]
theorem mapOfDiscrete_apply (r : G → H) (m : Mean G) (f : UCB H) :
    m.mapOfDiscrete r f = m (UCB.compRightAlgHomOfDiscrete r f) :=
  mk₀_apply _ _ _ f

/-- Along a continuous homomorphism, the pushforward out of a discrete group is the pushforward
`TauCeti.Mean.map`. -/
theorem mapOfDiscrete_coe (φ : G →ₜ* H) (m : Mean G) : m.mapOfDiscrete (φ : G → H) = m.map φ :=
  ext fun f => by simp [UCB.compRightAlgHomOfDiscrete_coe]

/-- If `r (φ h * x) = h * r x` for a homomorphism `φ : H →* G`, then the pushforward of a
left-invariant mean along `r` is left invariant. -/
theorem IsLeftInvariant.mapOfDiscrete {m : Mean G} (hm : m.IsLeftInvariant) (φ : H →* G)
    {r : G → H} (hr : ∀ h x, r (φ h * x) = h * r x) : (m.mapOfDiscrete r).IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun h f => ?_
  rw [mapOfDiscrete_apply, mapOfDiscrete_apply,
    UCB.compRightAlgHomOfDiscrete_leftTranslation φ hr, hm.apply_leftTranslation]

end MapOfDiscrete

end Mean

variable (G) in
/-- A discrete group is amenable exactly when all bounded functions admit a normalized positive
left-invariant real linear functional. -/
theorem amenable_iff_exists_boundedContinuousFunction_mean :
    Amenable G ↔ ∃ m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ, m 1 = 1 ∧
      ∀ (g : G) (f : G →ᵇ ℝ),
        m (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) = m f := by
  rw [amenable_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(Mean.boundedContinuousFunctionEquiv G m).1,
      (Mean.boundedContinuousFunctionEquiv G m).2,
      (m.isLeftInvariant_iff_boundedContinuousFunction).1 hm⟩
  · rintro ⟨m, h₁, hm⟩
    refine ⟨(Mean.boundedContinuousFunctionEquiv G).symm ⟨m, h₁⟩, ?_⟩
    rw [Mean.isLeftInvariant_iff_boundedContinuousFunction]
    simpa using hm

end Discrete

/-- An abstract group which is amenable with the discrete topology is amenable with any
group topology. -/
theorem Amenable.of_discrete [IsTopologicalGroup G]
    (h : letI : TopologicalSpace G := ⊥;
      letI := discreteTopology_bot G; Amenable G) :
    Amenable G := by
  let : @DiscreteTopology G ⊥ := discreteTopology_bot G
  exact Amenable.of_le (t₁ := ⊥) bot_le h

end TauCeti
