/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.Group.UCB.Translation

/-!
# Pullback of bounded uniformly continuous functions along continuous homomorphisms

For a continuous homomorphism `φ : G →ₜ* H` of topological groups, precomposition `f ↦ f ∘ φ` maps
`TauCeti.UCB H` to `TauCeti.UCB G`: if `f (u * y)` is uniformly close to `f y` for all `u` near
`1` in `H`, then `f (φ u * φ x)` is uniformly close to `f (φ x)` for all `u` near `1` in `G`, by
continuity of `φ` at `1`. This file bundles the pullback as a unital algebra homomorphism

```text
TauCeti.UCB.compRightAlgHom φ : UCB H →ₐ[ℝ] UCB G,
```

which preserves the pointwise order, does not increase the supremum norm and intertwines the left
translation `L_(φ g)` of `UCB H` with the left translation `L_g` of `UCB G`. It is an isometry
when `φ` is surjective. Dually, a mean on `UCB G` pushes forward to a mean on `UCB H`, which is how
amenability is transported along surjective continuous homomorphisms.

## Main definitions

* `TauCeti.UCB.compRightAlgHom φ`: the pullback `f ↦ f ∘ φ` along `φ : G →ₜ* H`.

## Main results

* `TauCeti.compContinuous_mem_ucb`: `ucb H` pulls back into `ucb G`.
* `TauCeti.UCB.monotone_compRightAlgHom`: the pullback preserves the pointwise order.
* `TauCeti.UCB.norm_compRightAlgHom_apply_le`, `TauCeti.UCB.norm_compRightAlgHom_apply`: the
  pullback does not increase the supremum norm, and preserves it when `φ` is surjective.
* `TauCeti.UCB.compRightAlgHom_leftTranslation`: `(L_(φ g) f) ∘ φ = L_g (f ∘ φ)`; likewise for
  right translations.
* `TauCeti.UCB.compRightAlgHom_id`, `TauCeti.UCB.compRightAlgHom_comp`: compatibility with the
  identity and with composition of homomorphisms.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The pullback `x ↦ f (φ x)` of a function in `ucb H` along a continuous homomorphism
`φ : G →ₜ* H` lies in `ucb G`. -/
theorem compContinuous_mem_ucb {f : H →ᵇ ℝ} (hf : f ∈ ucb H) (φ : G →ₜ* H) :
    f.compContinuous (φ : C(G, H)) ∈ ucb G := by
  have hφ : Tendsto φ (𝓝 1) (𝓝 1) := by
    simpa using φ.continuous.tendsto (1 : G)
  rw [mem_ucb_iff] at hf ⊢
  intro ε hε
  filter_upwards [hφ.eventually (hf ε hε)] with u hu x
  simpa using hu (φ x)

namespace UCB

/-- The pullback `f ↦ f ∘ φ` along a continuous homomorphism `φ : G →ₜ* H`, as a unital algebra
homomorphism from `UCB H` to `UCB G`. -/
def compRightAlgHom (φ : G →ₜ* H) : UCB H →ₐ[ℝ] UCB G where
  toFun f := ⟨(f : H →ᵇ ℝ).compContinuous (φ : C(G, H)), compContinuous_mem_ucb f.2 φ⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The pullback `f ∘ φ` is the precomposition of `f` with `φ`. -/
theorem coe_compRightAlgHom (φ : G →ₜ* H) (f : UCB H) :
    (compRightAlgHom φ f : G →ᵇ ℝ) = (f : H →ᵇ ℝ).compContinuous (φ : C(G, H)) :=
  (rfl)

@[simp]
theorem compRightAlgHom_apply (φ : G →ₜ* H) (f : UCB H) (x : G) :
    (compRightAlgHom φ f : G →ᵇ ℝ) x = (f : H →ᵇ ℝ) (φ x) :=
  (rfl)

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compRightAlgHom_id : compRightAlgHom (ContinuousMonoidHom.id G) = AlgHom.id ℝ (UCB G) :=
  (rfl)

/-- Pulling back along `ψ ∘ φ` is pulling back along `ψ` and then along `φ`. -/
theorem compRightAlgHom_comp (ψ : H →ₜ* K) (φ : G →ₜ* H) :
    compRightAlgHom (ψ.comp φ) = (compRightAlgHom φ).comp (compRightAlgHom ψ) :=
  (rfl)

/-- The pullback preserves the pointwise order. -/
theorem monotone_compRightAlgHom (φ : G →ₜ* H) : Monotone (compRightAlgHom φ) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (φ x)

/-- Along a surjective homomorphism, the pullback preserves and reflects the pointwise order. -/
@[simp]
theorem compRightAlgHom_le_compRightAlgHom_iff {φ : G →ₜ* H} (hφ : Function.Surjective φ)
    {f f' : UCB H} : compRightAlgHom φ f ≤ compRightAlgHom φ f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun y => ?_, fun h => monotone_compRightAlgHom φ h⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact le_def.1 h x

/-- The pullback does not increase the supremum norm. -/
theorem norm_compRightAlgHom_apply_le (φ : G →ₜ* H) (f : UCB H) :
    ‖compRightAlgHom φ f‖ ≤ ‖f‖ :=
  (f : H →ᵇ ℝ).norm_compContinuous_le _

/-- Along a surjective homomorphism, the pullback preserves the supremum norm. -/
theorem norm_compRightAlgHom_apply {φ : G →ₜ* H} (hφ : Function.Surjective φ) (f : UCB H) :
    ‖compRightAlgHom φ f‖ = ‖f‖ := by
  refine le_antisymm (norm_compRightAlgHom_apply_le φ f) ?_
  rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun y => ?_
  obtain ⟨x, rfl⟩ := hφ y
  exact (compRightAlgHom φ f : G →ᵇ ℝ).norm_coe_le_norm x

/-- The pullback intertwines left translation by `φ g` with left translation by `g`. -/
theorem compRightAlgHom_leftTranslation (φ : G →ₜ* H) (g : G) (f : UCB H) :
    compRightAlgHom φ (leftTranslation (φ g) f) = leftTranslation g (compRightAlgHom φ f) := by
  ext
  simp

/-- The pullback intertwines right translation by `φ g` with right translation by `g`. -/
theorem compRightAlgHom_rightTranslation (φ : G →ₜ* H) (g : G) (f : UCB H) :
    compRightAlgHom φ (rightTranslation (φ g) f) = rightTranslation g (compRightAlgHom φ f) := by
  ext
  simp

end UCB

end TauCeti
