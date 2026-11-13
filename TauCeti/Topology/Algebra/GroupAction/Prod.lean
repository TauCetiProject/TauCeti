/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Algebra.GroupAction.Prod

/-!
# Orbit spaces of independent product actions

The independent product of actions by homeomorphisms has orbit space homeomorphic to the product
of the orbit spaces. The inverse is continuous because the product of the two open orbit
projections is a quotient map. Proper discontinuity is also preserved by independent products.

Use `open scoped TauCeti.IndependentProd` for the coordinatewise action and its topological
instances.
-/

public section

open scoped TauCeti.IndependentProd

namespace TauCeti.IndependentProd

variable {G K X Y : Type*} [Monoid G] [Monoid K] [MulAction G X] [MulAction K Y]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Independent products of continuous action maps are continuous. -/
@[to_additive /-- Independent products of continuous additive action maps are continuous. -/]
scoped instance continuousConstSMul [ContinuousConstSMul G X] [ContinuousConstSMul K Y] :
    ContinuousConstSMul (G × K) (X × Y) where
  continuous_const_smul g := (continuous_const_smul g.1).prodMap (continuous_const_smul g.2)

/-- Independent products of properly discontinuous actions are properly discontinuous. -/
@[to_additive /-- Independent products of properly discontinuous additive actions are properly
 discontinuous. -/]
scoped instance properlyDiscontinuousSMul [ProperlyDiscontinuousSMul G X]
    [ProperlyDiscontinuousSMul K Y] : ProperlyDiscontinuousSMul (G × K) (X × Y) where
  finite_disjoint_inter_image {A B} hA hB := by
    refine ((ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G)
      (hA.image continuous_fst) (hB.image continuous_fst)).prod
      (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := K)
        (hA.image continuous_snd) (hB.image continuous_snd))).subset ?_
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨⟨g.1 • x.1, ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩, ⟨g • x, hgx, rfl⟩⟩,
      ⟨g.2 • x.2, ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩, ⟨g • x, hgx, rfl⟩⟩⟩

end TauCeti.IndependentProd

namespace TauCeti

variable {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]
  [TopologicalSpace X] [TopologicalSpace Y] [ContinuousConstSMul G X] [ContinuousConstSMul K Y]

/-- The orbit space of the independent product action is homeomorphic to the product of the
orbit spaces. No freeness, separation, or proper discontinuity is required. -/
@[to_additive AddAction.orbitRelQuotientProdHomeomorph /-- The orbit space of the independent
product additive action is homeomorphic to the product of the orbit spaces. -/]
def MulAction.orbitRelQuotientProdHomeomorph :
    MulAction.orbitRel.Quotient (G × K) (X × Y) ≃ₜ
      MulAction.orbitRel.Quotient G X × MulAction.orbitRel.Quotient K Y where
  toEquiv := MulAction.orbitRelQuotientProdEquiv
  continuous_toFun := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    apply ((continuous_quotient_mk' (s := MulAction.orbitRel G X)).prodMap
      (continuous_quotient_mk' (s := MulAction.orbitRel K Y))).congr
    intro x
    exact (MulAction.orbitRelQuotientProdEquiv_mk x).symm
  continuous_invFun := by
    rw [(MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)).prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := K) (T := Y)) |>.isQuotientMap.continuous_iff]
    apply (continuous_quotient_mk' (s := MulAction.orbitRel (G × K) (X × Y))).congr
    intro x
    exact (MulAction.orbitRelQuotientProdEquiv_symm_mk x.1 x.2).symm

/-- The homeomorphism sends the orbit of a pair to the pair of component orbits. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdHomeomorph_mk /-- The homeomorphism
sends the orbit of a pair to the pair of component orbits. -/]
theorem MulAction.orbitRelQuotientProdHomeomorph_mk (x : X × Y) :
    MulAction.orbitRelQuotientProdHomeomorph (G := G) (K := K) (Quotient.mk _ x) =
      (Quotient.mk _ x.1, Quotient.mk _ x.2) :=
  MulAction.orbitRelQuotientProdEquiv_mk x

/-- The inverse homeomorphism sends a pair of orbits to the orbit of a pair. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdHomeomorph_symm_mk /-- The inverse
homeomorphism sends a pair of orbits to the orbit of a pair. -/]
theorem MulAction.orbitRelQuotientProdHomeomorph_symm_mk (x : X) (y : Y) :
    (MulAction.orbitRelQuotientProdHomeomorph (G := G) (K := K)).symm
      (Quotient.mk _ x, Quotient.mk _ y) = Quotient.mk _ (x, y) :=
  MulAction.orbitRelQuotientProdEquiv_symm_mk x y

end TauCeti
