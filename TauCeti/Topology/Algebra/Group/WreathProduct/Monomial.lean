/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
public import TauCeti.Topology.Algebra.Group.WreathProduct
public import TauCeti.Topology.Algebra.Group.TransversalWord
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuity of the monomial homomorphism

For an open subgroup the transversal-dependent monomial homomorphism is continuous in the
coordinate topology of the permutation wreath product. The finite-coordinate form is continuous
after relabeling the cosets by `Fin U.index`.
-/

public section

namespace TauCeti

universe u

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism is continuous when `U` is open. Continuity is coordinatewise:
the transversal word is locally continuous, and the coset permutation varies continuously at
each coset. -/
theorem continuous_monomialHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialHom U t ht) := by
  apply continuous_induced_rng.mpr
  exact (continuous_pi fun x =>
    (continuous_lWord U t hU x).subtype_mk _).prodMk
      (continuous_pi fun x => continuous_id.smul continuous_const)

/-- The continuous monomial homomorphism for an open subgroup and a chosen transversal. -/
def monomialContinuousHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (G ⧸ U) :=
  ⟨monomialHom U t ht, continuous_monomialHom U hU t ht⟩

/-- The continuous monomial homomorphism has the same underlying homomorphism. -/
@[simp] theorem monomialContinuousHom_apply [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialContinuousHom U hU t ht g = monomialHom U t ht g := by
  rfl

section FiniteIndex

variable [U.FiniteIndex]

/-- The finite-coordinate monomial homomorphism is continuous for an open subgroup. -/
theorem continuous_monomialFinHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialFinHom U t ht) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  change Continuous (fun g => WreathProduct.congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm) (monomialHom U t ht g))
  exact (WreathProduct.continuous_congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)
    continuous_of_discreteTopology).comp (continuous_monomialHom U hU t ht)

/-- The finite-coordinate continuous monomial homomorphism for an open subgroup. -/
noncomputable def monomialFinContinuousHom [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G] (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (Fin U.index) :=
  ⟨monomialFinHom U t ht, continuous_monomialFinHom U hU t ht⟩

/-- The finite-coordinate continuous map has the finite-coordinate monomial homomorphism as
its underlying map. -/
@[simp] theorem monomialFinContinuousHom_apply [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G] (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialFinContinuousHom U hU t ht g = monomialFinHom U t ht g := by
  rfl

end FiniteIndex

end TauCeti
