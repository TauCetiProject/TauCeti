/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.GroupTheory.Subgroup.NormalizerOrbit

/-!
# Conjugacy in topological groups

For a compact Hausdorff topological group, conjugacy is a closed relation on the product.
The binary form allows both elements to vary, as needed when imposing conjugacy conditions
on a family of group elements. It makes the conjugation orbit space Hausdorff, which is the target
of the continuous map from the normalizer orbits on a subgroup.

Conjugation by an element of the normalizer of a subgroup `H` is a homeomorphism of `H`
(`Subgroup.normalizerConjHomeomorph`), for any group whose multiplication is separately continuous.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- In a compact Hausdorff topological group, the set of conjugate pairs is closed. -/
theorem isClosed_isConj_prod : IsClosed {q : G × G | IsConj q.1 q.2} := by
  have h : {q : G × G | IsConj q.1 q.2} = Set.range fun p : G × G ↦ (p.2, p.1 * p.2 * p.1⁻¹) := by
    ext ⟨a, b⟩
    simp [isConj_iff]
  rw [h]
  exact (isCompact_range (continuous_snd.prodMk IsTopologicalGroup.continuous_conj_prod)).isClosed

/-- The space of conjugacy classes of a compact Hausdorff topological group, with the quotient
topology, is Hausdorff. -/
instance : T2Space (MulAction.orbitRel.Quotient (ConjAct G) G) := by
  rw [t2Space_iff_of_isOpenQuotientMap MulAction.isOpenQuotientMap_quotientMk]
  simpa only [ConjAct.mk_eq_mk_iff_isConj] using isClosed_isConj_prod (G := G)

end TauCeti

/-- The map from `N(H)`-orbits on `H` to conjugation orbits on `G` is continuous for the quotient
topologies. -/
theorem Subgroup.continuous_normalizerOrbitMap {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : Continuous H.normalizerOrbitMap := by
  refine isQuotientMap_quotient_mk'.continuous_iff.mpr ?_
  have h : Continuous fun t : H ↦
      (Quotient.mk'' (t : G) : MulAction.orbitRel.Quotient (ConjAct G) G) :=
    continuous_quot_mk.comp continuous_subtypeVal
  exact h.congr fun t ↦ (H.normalizerOrbitMap_mk t).symm

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Conjugation by an element of the normalizer of `H` is continuous on `H`. -/
theorem continuous_normalizerMonoidHom (H : Subgroup G) (g : normalizer (H : Set G)) :
    Continuous (H.normalizerMonoidHom g) :=
  ((IsTopologicalGroup.continuous_conj (g : G)).comp continuous_subtypeVal).subtype_mk _

/-- Conjugation `h ↦ g * h * g⁻¹` by an element `g` of the normalizer of `H`, as a homeomorphism of
`H` with the subspace topology. Its underlying equivalence is `H.normalizerMonoidHom g`. -/
def normalizerConjHomeomorph (H : Subgroup G) (g : normalizer (H : Set G)) : H ≃ₜ H where
  toEquiv := (H.normalizerMonoidHom g).toEquiv
  continuous_toFun := H.continuous_normalizerMonoidHom g
  continuous_invFun := by
    simpa [MulAut.inv_def] using H.continuous_normalizerMonoidHom g⁻¹

@[simp]
theorem coe_normalizerConjHomeomorph_apply (H : Subgroup G) (g : normalizer (H : Set G)) (h : H) :
    (H.normalizerConjHomeomorph g h : G) = g * h * g⁻¹ :=
  (rfl)

@[simp]
theorem coe_normalizerConjHomeomorph_symm_apply (H : Subgroup G) (g : normalizer (H : Set G))
    (h : H) : ((H.normalizerConjHomeomorph g).symm h : G) = g⁻¹ * h * g := by
  simp [normalizerConjHomeomorph]

end Subgroup
