/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Periodic Tietze extension

Let `e : X₁ → X` be a closed embedding into a pseudo-metrizable space and `f : ℝ → X₁ → Y` a jointly
continuous family, `T`-periodic in the real variable, with values in a space `Y` satisfying the
Tietze extension property, such as a finite-dimensional real normed space. Then `f` extends along
`e` to a jointly continuous family `g : ℝ → X → Y`, still `T`-periodic in the real variable
(`Topology.IsClosedEmbedding.exists_continuous_periodic_extension`).

A periodic family is a continuous function on `AddCircle T × X₁`, because the quotient map
`ℝ × X₁ → AddCircle T × X₁` is an open quotient map. The Tietze extension theorem extends it along
the closed embedding `AddCircle T × X₁ → AddCircle T × X`, whose target is metrizable and hence
normal.

A typical use is a time-dependent vector field on a closed submanifold of a vector space, pushed
forward to the ambient space: extending it to a continuous periodic field on the whole space
lets the theory of ordinary differential equations in vector spaces apply to curves which are
only known to lie in the submanifold in the limit.
-/

public section

open Function Topology

namespace Topology.IsClosedEmbedding

universe u v

variable {X₁ : Type*} {X : Type u} {Y : Type v} [TopologicalSpace X₁] [TopologicalSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace Y] [TietzeExtension.{u} Y]
  {e : X₁ → X} {T : ℝ}

/-- **Periodic Tietze extension.** A jointly continuous family `f t x`, `T`-periodic in `t`, with
values in a `TietzeExtension` space `Y`, on a closed subspace of a pseudo-metrizable space,
embedded by `e`, extends to a jointly continuous family on the whole space, still `T`-periodic in
`t`. -/
theorem exists_continuous_periodic_extension (he : IsClosedEmbedding e) {f : ℝ → X₁ → Y}
    (hf : Continuous (uncurry f)) (hper : ∀ x, Periodic (fun t ↦ f t x) T) :
    ∃ g : ℝ → X → Y, Continuous (uncurry g) ∧ (∀ v, Periodic (fun t ↦ g t v) T) ∧
      ∀ t x, g t (e x) = f t x := by
  -- The family descends to a continuous function on `AddCircle T × X₁`.
  have hq : IsOpenQuotientMap (Prod.map ((↑) : ℝ → AddCircle T) (id : X₁ → X₁)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  let f₀ : AddCircle T × X₁ → Y := fun p ↦ (hper p.2).lift p.1
  have hf₀ : f₀ ∘ Prod.map (↑) id = uncurry f := by
    ext ⟨t, x⟩
    simp [f₀]
  have hc : Continuous f₀ := hq.isQuotientMap.continuous_iff.2 (hf₀ ▸ hf)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_extension' (IsClosedEmbedding.id.prodMap he) ⟨f₀, hc⟩
  refine ⟨fun t v ↦ G ((t : AddCircle T), v),
    G.continuous.comp ((QuotientAddGroup.continuous_mk.comp continuous_fst).prodMk continuous_snd),
    fun v t ↦ ?_, fun t x ↦ by simpa [f₀] using congrFun hG ((t : AddCircle T), x)⟩
  simp only [AddCircle.coe_add_period]

end Topology.IsClosedEmbedding
