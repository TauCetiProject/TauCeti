/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant orbit maps of topological Lie actions

When a Lie ring `L` carrying a topology acts on an additive group `M` regarded as discrete,
continuity of the orbit map `⁅·, m⁆ : L → M` of an element `m : M` is local constancy
(`IsLocallyConstant (⁅·, m⁆)`), a condition requiring no `TopologicalSpace` instance on `M`.

For a trivial action (`LieModule.IsTrivial L M`), every orbit map vanishes identically and is
therefore locally constant (`TauCeti.isLocallyConstant_lie_of_isTrivial`). When addition on `L` is
separately continuous, additivity in the Lie-ring variable reduces local constancy everywhere on `L`
to vanishing on a neighbourhood of zero (`TauCeti.isLocallyConstant_lie_iff`), the smoothness
condition characterizing discrete (smooth) modules over topological Lie algebras such as formal
current and loop algebras.

## Main results

* `TauCeti.isLocallyConstant_lie_of_isTrivial`: every orbit map `⁅·, m⁆ : L → M` of a trivial
  action is locally constant.
* `TauCeti.isLocallyConstant_lie_iff`: when addition on `L` is separately continuous, the orbit map
  `⁅·, m⁆ : L → M` is locally constant if and only if `m` is annihilated by a neighbourhood of zero
  in `L`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge University Press, 2007, §1.3.
-/

public section

open Filter Topology

namespace TauCeti

/-- Every orbit map `⁅·, m⁆ : L → M` of a trivial action is locally constant. -/
@[simp]
theorem isLocallyConstant_lie_of_isTrivial {L M : Type*} [TopologicalSpace L] [Bracket L M]
    [Zero M] [LieModule.IsTrivial L M] (m : M) :
    IsLocallyConstant (⁅·, m⁆ : L → M) := by
  have h : (⁅·, m⁆ : L → M) = Function.const L 0 := funext fun x ↦ trivial_lie_zero L M x m
  rw [h]
  exact IsLocallyConstant.const 0

/-- When addition on `L` is separately continuous, the orbit map `⁅·, m⁆ : L → M` is locally
constant if and only if `m` is annihilated by a neighbourhood of zero in `L`. -/
theorem isLocallyConstant_lie_iff {L M : Type*} [LieRing L] [TopologicalSpace L]
    [SeparatelyContinuousAdd L] [AddCommGroup M] [LieRingModule L M] {m : M} :
    IsLocallyConstant (⁅·, m⁆ : L → M) ↔ ∀ᶠ x in 𝓝 (0 : L), ⁅x, m⁆ = 0 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  refine ⟨fun h ↦ by simpa using h 0, fun h x₀ ↦ ?_⟩
  have hsub : Tendsto (fun x : L ↦ -x₀ + x) (𝓝 x₀) (𝓝 0) := by
    simpa using (continuous_id.const_add (-x₀)).tendsto x₀
  refine (hsub.eventually h).mono fun x (hx : ⁅-x₀ + x, m⁆ = 0) ↦ ?_
  rw [add_lie, neg_lie, neg_add_eq_zero] at hx
  exact hx.symm

end TauCeti
