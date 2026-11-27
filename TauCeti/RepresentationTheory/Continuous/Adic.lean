/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Module

/-!
# Continuous actions on adic modules

A linear action on an `I`-adic module is jointly continuous precisely when the induced
representations on all reductions `V / I^n V` are smooth. This is the continuity condition
in the definition of an adically admissible representation. The module need not be finite,
complete or separated, and the coefficient ring need not be local or noetherian.

The quotients use Mathlib's `Representation.quotient`; the topology on each reduction is
discrete. The proof uses the initial topology of these reductions and the open quotient
property of the reduction maps, so it establishes joint continuity, rather than only
continuity of individual orbit maps.

## References

* M. Emerton, *Local-global compatibility in the p-adic Langlands programme for GL₂/ℚ*,
  draft of 23 March 2011, Definition 3.1.13(2).
-/

public section

open scoped Topology

namespace Representation

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [ContinuousConstSMul Gᵐᵒᵖ G] [AddCommGroup V] [Module A V]

/-- A linear action on the `I`-adic module `V` is jointly continuous if and only if its
reductions modulo every `I^n V` are smooth. Neither completeness nor separatedness is needed. -/
theorem continuous_adicModuleTopology_iff (ρ : Representation A G V) (I : Ideal A) :
    (letI := I.adicModuleTopology V;
      Continuous (fun p : G × V ↦ ρ p.1 p.2)) ↔
      ∀ n : ℕ, IsSmooth (ρ.quotient (I ^ n • ⊤)
        (fun g ↦ Submodule.smul_top_le_comap_smul_top (I ^ n) (ρ g))) := by
  let := I.adicModuleTopology V
  have hcont : Continuous (fun p : G × V ↦ ρ p.1 p.2) ↔
      ∀ n : ℕ, Continuous[inferInstance, ⊥]
        (fun p : G × V ↦ (I ^ n • (⊤ : Submodule A V)).mkQ (ρ p.1 p.2)) := by
    calc
      _ ↔ Continuous[inferInstance, ⨅ n : ℕ,
          TopologicalSpace.induced (I ^ n • (⊤ : Submodule A V)).mkQ ⊥]
          (fun p : G × V ↦ ρ p.1 p.2) := by
        rw [← I.adicModuleTopology_eq_iInf_induced]
      _ ↔ _ := by simp only [continuous_iInf_rng, continuous_induced_rng, Function.comp_def]
  rw [hcont]
  apply forall_congr'
  intro n
  let P : Submodule A V := I ^ n • ⊤
  let : TopologicalSpace (V ⧸ P) := ⊥
  have : DiscreteTopology (V ⧸ P) := ⟨rfl⟩
  have hq : IsOpenQuotientMap P.mkQ := I.isOpenQuotientMap_mkQ_pow_smul_top n
  have hprod := IsOpenQuotientMap.id.prodMap (X := G) hq
  -- The quotient action composed with `(id, mkQ)` is the reduction of the original action.
  exact (hprod.continuous_comp_iff (g := fun p : G × (V ⧸ P) ↦
    ρ.quotient P (fun g ↦ Submodule.smul_top_le_comap_smul_top (I ^ n) (ρ g)) p.1 p.2)).trans
      (continuous_iff_isSmooth _)

end Representation
