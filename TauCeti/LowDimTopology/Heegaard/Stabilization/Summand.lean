/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Stabilization
public import TauCeti.LowDimTopology.Heegaard.Summand

/-!
# Stabilization and the `ε`-classes

Stabilization does not change which generators are joined by domains, so it identifies the
`ε`-classes (`TauCeti.HeegaardRegionSystem.EpsilonClass`) of a diagram with those of its
stabilization (`TauCeti.HeegaardRegionSystem.stabilizeEpsilonClassEquiv`), and its identification
of the hat chain groups carries each summand `TauCeti.HeegaardRegionSystem.epsilonSummand` onto the
corresponding summand (`TauCeti.HeegaardRegionSystem.map_stabilizeChainEquiv_epsilonSummand`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.stabilizeEpsilonClassEquiv`: the identification of the
  `ε`-classes of a diagram with those of its stabilization.

## Main results

* `TauCeti.HeegaardRegionSystem.epsilonClass_stabilizeGenerator_eq_iff`: stabilization preserves
  and reflects lying in the same `ε`-class.
* `TauCeti.HeegaardRegionSystem.map_stabilizeChainEquiv_epsilonSummand`: the identification of
  the hat chain groups carries summands onto summands.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 and §10 (stabilization).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section Stabilization

variable (r₀ : Region)

/-- Stabilization does not change the `ε`-classes: `x ∪ {x₀}` and `y ∪ {x₀}` lie in the same
class of the stabilized diagram exactly when `x` and `y` lie in the same class. -/
@[simp]
theorem epsilonClass_stabilizeGenerator_eq_iff {x y : H.Generator} :
    (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ x) =
        (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ y) ↔
      H.epsilonClass x = H.epsilonClass y := by
  simp only [epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween, isDomainBetween_stabilize_iff]

/-- The identification of the `ε`-classes of a diagram with those of its stabilization, sending
the class of `x` to the class of `x ∪ {x₀}`. -/
noncomputable def stabilizeEpsilonClassEquiv : H.EpsilonClass ≃ (H.stabilize r₀).EpsilonClass :=
  EpsilonClass.equivOfSurjective (H.stabilizeGenerator r₀)
    (fun _ _ => H.epsilonClass_stabilizeGenerator_eq_iff r₀)
    ((epsilonClass_surjective _).comp (H.stabilizeGenerator_surjective r₀))

/-- The identification sends the class of `x` to the class of `x ∪ {x₀}`. -/
@[simp]
theorem stabilizeEpsilonClassEquiv_epsilonClass (x : H.Generator) :
    H.stabilizeEpsilonClassEquiv r₀ (H.epsilonClass x) =
      (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ x) :=
  EpsilonClass.equivOfSurjective_epsilonClass _ _ _ x

/-- The identification of the hat chain groups by stabilization carries the summand of each
`ε`-class onto the summand of the corresponding class of the stabilized diagram. -/
theorem map_stabilizeChainEquiv_epsilonSummand (c : H.EpsilonClass) :
    (H.epsilonSummand (ZMod 2) c).map (H.stabilizeChainEquiv r₀).toLinearMap =
      (H.stabilize r₀).epsilonSummand (ZMod 2) (H.stabilizeEpsilonClassEquiv r₀ c) := by
  induction c using EpsilonClass.ind with
  | h z =>
    simp only [epsilonSummand_eq_supported, Finsupp.supported_eq_span_single, Submodule.map_span,
      ← Set.image_comp]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply, LinearEquiv.coe_coe,
      stabilizeChainEquiv_single, stabilizeEpsilonClassEquiv_epsilonClass]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, (H.epsilonClass_stabilizeGenerator_eq_iff r₀).mpr hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
      rw [stabilizeGeneratorEquiv_apply] at hg ⊢
      exact ⟨x, (H.epsilonClass_stabilizeGenerator_eq_iff r₀).mp hg, rfl⟩

end Stabilization

end HeegaardRegionSystem

end TauCeti
