/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.BalancedProduct.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Orbitwise decomposition of balanced products

For a discrete `G`-set `A`, the balanced product `E ×_G A` is the topological disjoint union
of `E ×_G o.orbit`, indexed by the label orbits `o`. The comparison includes each orbit's
labels into `A` and keeps the point of `E` fixed. It commutes with every invariant projection
from `E`, so it decomposes associated covering spaces over their base, not just their total
spaces. Neither freeness nor transitivity is needed.

The algebraic construction uses Mathlib's `MulAction.selfEquivSigmaOrbits'` and Tau Ceti's
`MulAction.orbitRelQuotientSigmaEquiv` and `MulAction.orbitRelQuotientCongr`.
-/

public section

namespace TauCeti.BalancedProduct

open Topology

variable {G E A : Type*} [Group G] [MulAction G E] [MulAction G A]

/-- Forget the orbit index of a label, retaining the point of `E`. -/
private def orbitPairsEquiv :
    (Σ o : MulAction.orbitRel.Quotient G A, E × o.orbit) ≃ E × A :=
  ((Equiv.sigmaCongrRight fun o : MulAction.orbitRel.Quotient G A =>
      Equiv.prodComm E o.orbit).trans
    (Equiv.sigmaProdDistrib (fun o : MulAction.orbitRel.Quotient G A => o.orbit) E).symm).trans
    ((Equiv.prodCongr (MulAction.selfEquivSigmaOrbits' G A).symm (Equiv.refl E)).trans
      (Equiv.prodComm A E))

omit [MulAction G E] in
@[simp]
private theorem orbitPairsEquiv_apply (o : MulAction.orbitRel.Quotient G A)
    (e : E) (a : o.orbit) : orbitPairsEquiv (G := G) ⟨o, e, a⟩ = (e, (a : A)) :=
  (rfl)

private theorem orbitPairsEquiv_smul (g : G)
    (p : Σ o : MulAction.orbitRel.Quotient G A, E × o.orbit) :
    orbitPairsEquiv (g • p) = (MulEquiv.refl G) g • orbitPairsEquiv p := by
  obtain ⟨o, e, a⟩ := p
  rfl

/-- A balanced product is the disjoint union of the balanced products of its label orbits.
The map on each summand is induced by inclusion of the orbit into `A`. -/
def orbitEquiv : (Σ o : MulAction.orbitRel.Quotient G A, BalancedProduct G E o.orbit) ≃
    BalancedProduct G E A :=
  MulAction.orbitRelQuotientSigmaEquiv.symm.trans
    (MulAction.orbitRelQuotientCongr (MulEquiv.refl G)
      (orbitPairsEquiv (G := G) (E := E) (A := A))
      (orbitPairsEquiv_smul (G := G) (E := E) (A := A)))

/-- On representatives, the orbit decomposition simply forgets orbit membership. -/
@[simp]
theorem orbitEquiv_mk (o : MulAction.orbitRel.Quotient G A) (e : E) (a : o.orbit) :
    orbitEquiv ⟨o, mk G e a⟩ = mk G e (a : A) := by
  simp only [orbitEquiv, mk, ← Quotient.mk''_eq_mk, Equiv.trans_apply,
    MulAction.orbitRelQuotientSigmaEquiv_symm_mk]
  exact (MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl G)
    (orbitPairsEquiv (G := G) (E := E) (A := A))
    (orbitPairsEquiv_smul (G := G) (E := E) (A := A)) ⟨o, e, a⟩).trans
      (congrArg Quotient.mk'' (orbitPairsEquiv_apply o e a))

/-- The inverse comparison places a representative in the summand of its label orbit. -/
@[simp]
theorem orbitEquiv_symm_mk (e : E) (a : A) :
    (orbitEquiv (G := G)).symm (mk G e a) =
      ⟨Quotient.mk'' a, mk G e ⟨a, MulAction.mem_orbit_self a⟩⟩ := by
  apply (orbitEquiv (G := G)).injective
  rw [Equiv.apply_symm_apply, orbitEquiv_mk]

/-- On an arbitrary summand, the orbit comparison is the map induced by label inclusion. -/
theorem orbitEquiv_apply (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    orbitEquiv ⟨o, z⟩ =
      mapRight Subtype.val (fun _ _ => MulAction.orbitRel.Quotient.orbit.coe_smul) z := by
  induction z using Quotient.inductionOn with
  | h p =>
    rw [mapRight_mk]
    exact orbitEquiv_mk o p.1 p.2

section Topology

variable [TopologicalSpace E] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousConstSMul G E]

/-- The orbitwise comparison is a homeomorphism for discrete labels. -/
def orbitHomeomorph : (Σ o : MulAction.orbitRel.Quotient G A, BalancedProduct G E o.orbit) ≃ₜ
    BalancedProduct G E A :=
  orbitEquiv.toHomeomorphOfContinuousOpen
    (continuous_sigma_iff.mpr fun o => by
      simp only [orbitEquiv_apply]
      exact continuous_mapRight _ _ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun o => by
      simp only [orbitEquiv_apply]
      let _ : ContinuousConstSMul G A := ⟨fun _ => continuous_of_discreteTopology⟩
      exact isOpenMap_mapRight _ _ (fun s _ => isOpen_discrete _))

/-- The topological orbit decomposition has underlying equivalence `orbitEquiv`. -/
@[simp]
theorem orbitHomeomorph_toEquiv :
    (orbitHomeomorph (G := G) (E := E) (A := A)).toEquiv = orbitEquiv :=
  (rfl)

/-- Each orbit summand is included by the equivariant inclusion of labels. -/
theorem orbitHomeomorph_apply (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    orbitHomeomorph ⟨o, z⟩ =
      mapRight Subtype.val (fun _ _ => MulAction.orbitRel.Quotient.orbit.coe_smul) z :=
  orbitEquiv_apply o z

/-- The topological comparison keeps the point of `E` and forgets orbit membership. -/
@[simp]
theorem orbitHomeomorph_mk (o : MulAction.orbitRel.Quotient G A) (e : E) (a : o.orbit) :
    orbitHomeomorph ⟨o, mk G e a⟩ = mk G e (a : A) :=
  orbitEquiv_mk o e a

/-- The inverse comparison places a representative in the summand of its label orbit. -/
@[simp]
theorem orbitHomeomorph_symm_mk (e : E) (a : A) :
    (orbitHomeomorph (G := G)).symm (mk G e a) =
      ⟨Quotient.mk'' a, mk G e ⟨a, MulAction.mem_orbit_self a⟩⟩ :=
  orbitEquiv_symm_mk e a

end Topology

variable {X : Type*} {q : E → X} (hq : ∀ (g : G) (e : E), q (g • e) = q e)

/-- The orbit decomposition commutes with the invariant projection from `E`. -/
@[simp]
theorem proj_orbitEquiv (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    proj A hq (orbitEquiv ⟨o, z⟩) = proj o.orbit hq z := by
  rw [orbitEquiv_apply]
  exact proj_mapRight hq _ _ z

/-- The topological decomposition is over the base of the invariant projection. -/
@[simp]
theorem proj_orbitHomeomorph [TopologicalSpace E] [TopologicalSpace A] [DiscreteTopology A]
    [ContinuousConstSMul G E] (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    proj A hq (orbitHomeomorph ⟨o, z⟩) = proj o.orbit hq z := by
  rw [orbitHomeomorph_apply]
  exact proj_mapRight hq _ _ z

end TauCeti.BalancedProduct
