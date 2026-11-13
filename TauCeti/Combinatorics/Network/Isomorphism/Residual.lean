/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Basic

/-!
# Residual networks under network isomorphisms

A bounded-network isomorphism induces an isomorphism of the residual networks of corresponding
feasible assignments. Forward copies remain forward copies and reverse copies remain reverse
copies, even for loops and antiparallel arrows. Transport commutes with residual net changes,
updates, and canonical differences. Thus relabelling a bounded problem before making a residual
adjustment gives the same assignment as relabelling afterwards.

The arrowwise identities require no finite vertex or arrow types. Excess and conservation can
then be transported using the existing network-isomorphism API.
-/

public section

namespace TauCeti.Network.Iso

universe u u' v v' w w'

variable {V : Type u} {W : Type u'} {K : Type w} [AddGroup K] [Preorder K]
  [AddRightMono K] {N : Network.{u, v, w} K V} {M : Network.{u', v', w} K W}

/-- An isomorphism induces an isomorphism of the residual networks at corresponding feasible
assignments. The sum tags, and therefore the underlying original arrow identities, are retained.

Reducibility lets the transported endpoints compute to the original vertex equivalence when
applying the dependent arrow and assignment APIs. -/
@[expose, reducible]
def residual (e : N ≃ₙ M) (f : N.Assignment K) (hf : f ∈ Set.Icc N.lower N.upper) :
    N.residual f hf ≃ₙ
      M.residual (e.assignmentEquiv K f) ((e.assignmentEquiv_mem_Icc_iff f).2 hf) where
  vertexEquiv := e.vertexEquiv
  homEquiv x y := Equiv.sumCongr (e.homEquiv x y) (e.homEquiv y x)
  map_lower _ := rfl
  map_upper a := by
    rcases a with a | a <;> simp [e.map_lower, e.map_upper]

/-- Residual transport uses the original vertex equivalence. -/
@[simp]
theorem residual_vertexEquiv (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) : (e.residual f hf).vertexEquiv = e.vertexEquiv :=
  (rfl)

/- Forward and reverse arrow formulas simplify using `Equiv.sumCongr_apply` and the
`Sum.map` constructor lemmas, without additional simp registrations. -/

/-- Relabelling commutes with reversing a residual arrow to its other tagged copy. -/
theorem residual_homEquiv_swap (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) {x y : V} (a : ResidualHom N.Hom x y) :
    (e.residual f hf).homEquiv y x a.swap = ((e.residual f hf).homEquiv x y a).swap := by
  cases a <;> rfl

/-- A transported residual assignment has its original value on each transported forward copy. -/
@[simp]
theorem residual_assignmentEquiv_inl {R : Type w'} (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) (r : TauCeti.Assignment (ResidualHom N.Hom) R)
    {x y : V} (a : N.Hom x y) :
    (e.residual f hf).assignmentEquiv R r (Sum.inl (e.homEquiv x y a)) = r (Sum.inl a) := by
  exact (e.residual f hf).assignmentEquiv_apply R r (Sum.inl a)

/-- A transported residual assignment has its original value on each transported reverse copy. -/
@[simp]
theorem residual_assignmentEquiv_inr {R : Type w'} (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) (r : TauCeti.Assignment (ResidualHom N.Hom) R)
    {x y : V} (a : N.Hom y x) :
    (e.residual f hf).assignmentEquiv R r (Sum.inr (e.homEquiv y x a)) = r (Sum.inr a) := by
  exact (e.residual f hf).assignmentEquiv_apply R r (Sum.inr a)

/-- The net change of a residual assignment commutes with network isomorphisms. Its coefficients
may be independent of those used for the network bounds. -/
theorem assignmentEquiv_residualNet {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (f : N.Assignment K) (hf : f ∈ Set.Icc N.lower N.upper)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualNet r) =
      residualNet ((e.residual f hf).assignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- Updating and then relabelling equals relabelling the original and residual assignments and
then updating. No conservation or residual feasibility hypothesis is needed. -/
theorem assignmentEquiv_residualUpdate {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (f : N.Assignment K) (hf : f ∈ Set.Icc N.lower N.upper)
    (g : N.Assignment R) (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualUpdate g r) =
      residualUpdate (e.assignmentEquiv R g) ((e.residual f hf).assignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- The canonical residual difference is invariant under relabelling. -/
theorem assignmentEquiv_residualDifference {R : Type w'} [AddCommGroup R] [Lattice R]
    (e : N ≃ₙ M) (f : N.Assignment K) (hf : f ∈ Set.Icc N.lower N.upper)
    (g h : N.Assignment R) :
    (e.residual f hf).assignmentEquiv R (residualDifference g h) =
      residualDifference (e.assignmentEquiv R g) (e.assignmentEquiv R h) := by
  apply ((e.residual f hf).assignmentEquiv R).symm.injective
  funext x y a
  cases a <;> simp

end TauCeti.Network.Iso
