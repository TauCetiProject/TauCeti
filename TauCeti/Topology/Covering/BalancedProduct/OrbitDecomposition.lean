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

When every label orbit in `A` is open, the balanced product `E ×_G A` is the topological
disjoint union of `E ×_G o.orbit`, indexed by the label orbits `o`. This holds in particular
for discrete labels. The comparison includes each orbit's labels into `A` and keeps the point
of `E` fixed. It commutes with every invariant projection
from `E`, so it decomposes associated covering spaces over their base, not just their total
spaces. Neither freeness, transitivity, nor continuity of the actions is needed.

The algebraic construction uses Mathlib's `MulAction.selfEquivSigmaOrbits'` and Tau Ceti's
`MulAction.orbitRelQuotientSigmaEquiv` and `MulAction.orbitRelQuotientCongr`.
-/

public section

namespace TauCeti.BalancedProduct

open Topology

variable {G E A : Type*} [Group G] [MulAction G A]

/-- Forget the orbit index of a label, retaining the point of `E`. -/
private def orbitPairsEquiv :
    (Σ o : MulAction.orbitRel.Quotient G A, E × o.orbit) ≃ E × A :=
  ((Equiv.sigmaCongrRight fun o : MulAction.orbitRel.Quotient G A =>
      Equiv.prodComm E o.orbit).trans
    (Equiv.sigmaProdDistrib (fun o : MulAction.orbitRel.Quotient G A => o.orbit) E).symm).trans
    ((Equiv.prodCongr (MulAction.selfEquivSigmaOrbits' G A).symm (Equiv.refl E)).trans
      (Equiv.prodComm A E))

@[simp]
private theorem orbitPairsEquiv_apply (o : MulAction.orbitRel.Quotient G A)
    (e : E) (a : o.orbit) : orbitPairsEquiv (G := G) ⟨o, e, a⟩ = (e, (a : A)) :=
  (rfl)

private theorem orbitPairsEquiv_smul [SMul G E] (g : G)
    (p : Σ o : MulAction.orbitRel.Quotient G A, E × o.orbit) :
    orbitPairsEquiv (g • p) = (MulEquiv.refl G) g • orbitPairsEquiv p := by
  obtain ⟨o, e, a⟩ := p
  rfl

variable [MulAction G E]

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

variable [TopologicalSpace E] [TopologicalSpace A]
  (hopen : ∀ o : MulAction.orbitRel.Quotient G A, IsOpen o.orbit)

/-- The orbitwise comparison is a homeomorphism when every label orbit is open.
No continuity of either action is needed. -/
def orbitHomeomorph : (Σ o : MulAction.orbitRel.Quotient G A, BalancedProduct G E o.orbit) ≃ₜ
    BalancedProduct G E A where
  toEquiv := orbitEquiv
  continuous_toFun := by
    apply continuous_sigma
    intro o
    exact (continuous_mapRight _ _ continuous_subtype_val).congr
      (fun z => (orbitEquiv_apply o z).symm)
  continuous_invFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    -- Open orbit inclusions make the decomposition of representatives a homeomorphism.
    have hp : Continuous (orbitPairsEquiv (G := G) (E := E) (A := A)).symm :=
      (orbitPairsEquiv.toHomeomorphOfContinuousOpen
        (continuous_sigma fun _ => continuous_fst.prodMk continuous_snd.subtype_val)
        (isOpenMap_sigma.mpr fun o =>
          IsOpenMap.id.prodMap (hopen o).isOpenMap_subtype_val)).symm.continuous
    have hm : Continuous (fun p : Σ o : MulAction.orbitRel.Quotient G A, E × o.orbit =>
        (⟨p.1, @Quotient.mk' (E × p.1.orbit) (MulAction.orbitRel G _) p.2⟩ :
          Σ o : MulAction.orbitRel.Quotient G A, BalancedProduct G E o.orbit)) :=
      continuous_sigma fun o => continuous_sigmaMk.comp
        (continuous_quotient_mk' : Continuous
          (@Quotient.mk' (E × o.orbit) (MulAction.orbitRel G _)))
    -- The inverse on quotient classes is induced by the inverse on representatives.
    convert hm.comp hp using 1
    funext p
    obtain ⟨⟨o, e, a⟩, rfl⟩ := (orbitPairsEquiv (G := G) (E := E) (A := A)).surjective p
    simp only [Function.comp_apply, Equiv.invFun_as_coe]
    rw [Equiv.symm_apply_apply]
    apply orbitEquiv.injective
    simpa only [Equiv.apply_symm_apply, orbitPairsEquiv_apply, mk, Quotient.mk'] using
      (orbitEquiv_mk o e a).symm

/-- The topological orbit decomposition has underlying equivalence `orbitEquiv`. -/
@[simp]
theorem orbitHomeomorph_toEquiv :
    (orbitHomeomorph (E := E) hopen).toEquiv = orbitEquiv :=
  (rfl)

/-- Each orbit summand is included by the equivariant inclusion of labels. -/
theorem orbitHomeomorph_apply (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    orbitHomeomorph hopen ⟨o, z⟩ =
      mapRight Subtype.val (fun _ _ => MulAction.orbitRel.Quotient.orbit.coe_smul) z :=
  orbitEquiv_apply o z

/-- The topological comparison keeps the point of `E` and forgets orbit membership. -/
@[simp]
theorem orbitHomeomorph_mk (o : MulAction.orbitRel.Quotient G A) (e : E) (a : o.orbit) :
    orbitHomeomorph hopen ⟨o, mk G e a⟩ = mk G e (a : A) :=
  orbitEquiv_mk o e a

/-- The inverse comparison places a representative in the summand of its label orbit. -/
@[simp]
theorem orbitHomeomorph_symm_mk (e : E) (a : A) :
    (orbitHomeomorph hopen).symm (mk G e a) =
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
theorem proj_orbitHomeomorph [TopologicalSpace E] [TopologicalSpace A]
    (hopen : ∀ o : MulAction.orbitRel.Quotient G A, IsOpen o.orbit)
    (o : MulAction.orbitRel.Quotient G A)
    (z : BalancedProduct G E o.orbit) :
    proj A hq (orbitHomeomorph hopen ⟨o, z⟩) = proj o.orbit hq z := by
  rw [orbitHomeomorph_apply]
  exact proj_mapRight hq _ _ z

end TauCeti.BalancedProduct
