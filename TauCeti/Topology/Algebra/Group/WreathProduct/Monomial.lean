/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
public import TauCeti.Topology.Algebra.Group.WreathProduct.Basic
public import TauCeti.Topology.Algebra.Group.TransversalWord
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuity of the monomial homomorphism

For an open subgroup the transversal-dependent monomial homomorphism is continuous in the
coordinate topology of the permutation wreath product when multiplication on the source is
separately continuous. The finite-coordinate form is continuous after relabeling the cosets by
`Fin U.index`.
-/

public section

namespace TauCeti

universe u

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism is continuous when `U` is open. -/
theorem continuous_monomialHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialHom U t ht) := by
  apply WreathProduct.continuous_iff.mpr
  constructor
  · intro x
    have h : Continuous (fun g : G =>
        (⟨lWord U t x g, lWord_mem U t ht x g⟩ : U)) :=
      (continuous_lWord U t hU x).subtype_mk _
    exact h.congr fun g => by
      apply Subtype.ext
      exact (monomialHom_left U t ht g x).symm
  · intro x
    have h : Continuous (fun g : G => g • x) := by
      convert QuotientGroup.continuous_mk.comp (continuous_mul_const x.out) using 1
      ext g
      exact (MulAction.Quotient.mk_smul_out U g x).symm
    exact h.congr fun g => (monomialHom_right U t ht g x).symm

/-- The continuous monomial homomorphism for an open subgroup and a chosen transversal. -/
def monomialContinuousHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (G ⧸ U) :=
  ⟨monomialHom U t ht, continuous_monomialHom U hU t ht⟩

/-- The continuous monomial homomorphism has the same underlying homomorphism. -/
@[simp] theorem monomialContinuousHom_apply [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialContinuousHom U hU t ht g = monomialHom U t ht g := by
  rfl

section FiniteIndex

variable [U.FiniteIndex]

/-- The finite-coordinate monomial homomorphism is continuous for an open subgroup. -/
theorem continuous_monomialFinHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialFinHom U t ht) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h := (WreathProduct.continuous_congr
      (Finite.equivFinOfCardEq U.index_eq_card.symm)
      continuous_of_discreteTopology).comp (continuous_monomialHom U hU t ht)
  exact h.congr fun g => (monomialFinHom_apply U t ht g).symm

/-- The finite-coordinate continuous monomial homomorphism for an open subgroup. -/
noncomputable def monomialFinContinuousHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (Fin U.index) :=
  ⟨monomialFinHom U t ht, continuous_monomialFinHom U hU t ht⟩

/-- The finite-coordinate continuous map has the finite-coordinate monomial homomorphism as
its underlying map. -/
@[simp] theorem monomialFinContinuousHom_apply [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialFinContinuousHom U hU t ht g = monomialFinHom U t ht g := by
  rfl

end FiniteIndex

end TauCeti
