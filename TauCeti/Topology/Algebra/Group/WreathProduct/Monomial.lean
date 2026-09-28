/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
public import TauCeti.Topology.Algebra.Group.WreathProduct.Basic
public import TauCeti.Topology.Algebra.Group.Quotient.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuity of the monomial homomorphism

For an open subgroup the transversal-dependent monomial homomorphism is continuous in the
coordinate topology of the permutation wreath product when multiplication on the source is
separately continuous.
The finite-coordinate form is continuous after relabeling the cosets by
`Fin U.index`.
The public continuous maps are `TauCeti.monomialContinuousHom` and
`TauCeti.monomialFinContinuousHom`, with `U` as their first explicit argument.
-/

public section

namespace TauCeti

universe u

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism is continuous when `U` is open and multiplication on `G` is
separately continuous. -/
theorem continuous_monomialHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) :
    Continuous (monomialHom U t) := by
  apply WreathProduct.continuous_iff.mpr
  constructor
  · intro x
    have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
    have hinv : Continuous (fun g : G => g⁻¹ • x) := by
      rw [continuous_discrete_rng]
      intro y
      have heq : (fun g : G => g⁻¹ • x) ⁻¹' {y} =
          (fun g : G => g • y) ⁻¹' {x} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h
          calc
            g • y = g • (g⁻¹ • x) := by rw [h]
            _ = x := by simp [smul_smul]
        · intro h
          calc
            g⁻¹ • x = g⁻¹ • (g • y) := by rw [h]
            _ = y := by simp [smul_smul]
      rw [heq]
      exact (isOpen_discrete _).preimage (QuotientGroup.continuous_smul_const U y)
    have hmul : Continuous (fun p : G × (G ⧸ U) => ((fun x => (t.2.leftQuotientEquiv x : G)) x)⁻¹ *
        p.1 * (fun x => (t.2.leftQuotientEquiv x : G)) p.2) :=
      continuous_prod_of_discrete_right.mpr fun y => by
        simpa using (continuous_const_mul (((fun x => (t.2.leftQuotientEquiv x : G))
            x)⁻¹)).mul_const ((fun x => (t.2.leftQuotientEquiv x : G)) y)
    have hword : Continuous (lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x) := by
      have h := hmul.comp (continuous_id.prodMk hinv)
      exact h.congr fun g => (lWord_def U (fun x => (t.2.leftQuotientEquiv x : G)) x g).symm
    have h : Continuous (fun g : G =>
        (⟨lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g, lWord_mem U (fun x =>
            (t.2.leftQuotientEquiv x : G)) (fun x => t.2.quotientGroupMk_leftQuotientEquiv x) x g⟩
            : U)) :=
      hword.subtype_mk _
    exact h.congr fun g => by
      apply Subtype.ext
      exact (coe_monomialHom_left U t g x).symm
  · intro x
    exact (QuotientGroup.continuous_smul_const U x).congr fun g =>
      (monomialHom_right U t g x).symm

/-- The continuous monomial homomorphism for an open subgroup and a chosen transversal. -/
noncomputable def monomialContinuousHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) :
    G →ₜ* WreathProduct U (G ⧸ U) :=
  ⟨monomialHom U t, continuous_monomialHom U hU t⟩

/-- The continuous monomial homomorphism has the same underlying homomorphism. -/
@[simp] theorem monomialContinuousHom_apply [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) (g : G) :
    monomialContinuousHom U hU t g = monomialHom U t g := by
  rfl

section FiniteIndex

variable [U.FiniteIndex]

/-- The finite-coordinate monomial homomorphism is continuous for an open subgroup. -/
theorem continuous_monomialFinHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) :
    Continuous (monomialFinHom U t) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h := (WreathProduct.continuous_congr
      (Finite.equivFinOfCardEq U.index_eq_card.symm)
      continuous_of_discreteTopology).comp (continuous_monomialHom U hU t)
  exact h.congr fun g => (monomialFinHom_apply U t g).symm

/-- The finite-coordinate continuous monomial homomorphism for an open subgroup. -/
noncomputable def monomialFinContinuousHom [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) :
    G →ₜ* WreathProduct U (Fin U.index) :=
  ⟨monomialFinHom U t, continuous_monomialFinHom U hU t⟩

/-- The finite-coordinate continuous map has the finite-coordinate monomial homomorphism as
its underlying map. -/
@[simp] theorem monomialFinContinuousHom_apply [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hU : IsOpen (U : Set G)) (t : U.LeftTransversal) (g : G) :
    monomialFinContinuousHom U hU t g = monomialFinHom U t g := by
  rfl

end FiniteIndex

end TauCeti
