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
copies, even for loops and antiparallel arrows. Transport commutes with residual capacities, net
changes, updates, and canonical differences. Thus relabelling a bounded problem before making a
residual adjustment gives the same assignment as relabelling afterwards.

The arrowwise identities require no finite vertex or arrow types. Excess and conservation can
then be transported using the existing network-isomorphism API.
-/

public section

namespace TauCeti.Network.Iso

universe u u' v v' w w'

variable {V : Type u} {W : Type u'} {K : Type w}

section Assignments

variable [LE K] {N : Network.{u, v, w} K V} {M : Network.{u', v', w} K W}

/-- Transport residual assignments by relabelling endpoints and retaining forward/reverse tags.
This depends only on the original isomorphism, not on any feasible assignment or its bounds. -/
def residualAssignmentEquiv (e : N ≃ₙ M) (R : Type w') :
    TauCeti.Assignment (ResidualHom N.Hom) R ≃ TauCeti.Assignment (ResidualHom M.Hom) R :=
  e.vertexEquiv.piCongr fun x ↦ e.vertexEquiv.piCongr fun y ↦
    (Equiv.sumCongr (e.homEquiv x y) (e.homEquiv y x)).arrowCongr (Equiv.refl R)

/-- A transported residual assignment evaluates on any transported residual arrow. -/
@[simp]
theorem residualAssignmentEquiv_apply {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V}
    (a : ResidualHom N.Hom x y) :
    e.residualAssignmentEquiv R r (Sum.map (e.homEquiv x y) (e.homEquiv y x) a) = r a := by
  simp [residualAssignmentEquiv]

/-- Pulling a residual assignment back evaluates by relabelling its arrow forward. -/
@[simp]
theorem residualAssignmentEquiv_symm_apply {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom M.Hom) R) {x y : V}
    (a : ResidualHom N.Hom x y) :
    (e.residualAssignmentEquiv R).symm r a =
      r (Sum.map (e.homEquiv x y) (e.homEquiv y x) a) := by
  simp [residualAssignmentEquiv]

/-- A transported residual assignment has its original value on each transported forward copy. -/
@[simp]
theorem residualAssignmentEquiv_inl {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V} (a : N.Hom x y) :
    e.residualAssignmentEquiv R r (Sum.inl (e.homEquiv x y a)) = r (Sum.inl a) := by
  exact e.residualAssignmentEquiv_apply r (Sum.inl a)

/-- A transported residual assignment has its original value on each transported reverse copy. -/
@[simp]
theorem residualAssignmentEquiv_inr {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V} (a : N.Hom y x) :
    e.residualAssignmentEquiv R r (Sum.inr (e.homEquiv y x a)) = r (Sum.inr a) := by
  exact e.residualAssignmentEquiv_apply r (Sum.inr a)

/-- Relabelling commutes with residual capacities, independently of feasibility. -/
@[simp]
theorem assignmentEquiv_residualCapacity {R : Type w'} [Sub R] (e : N ≃ₙ M)
    (lo hi g : N.Assignment R) :
    e.residualAssignmentEquiv R (residualCapacity lo hi g) =
      residualCapacity (e.assignmentEquiv R lo) (e.assignmentEquiv R hi)
        (e.assignmentEquiv R g) := by
  apply (e.residualAssignmentEquiv R).symm.injective
  funext x y a
  cases a <;> simp

/-- The net change of a residual assignment commutes with network isomorphisms. Its coefficients
may be independent of those used for the network bounds. -/
@[simp]
theorem assignmentEquiv_residualNet {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualNet r) = residualNet (e.residualAssignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- Updating and then relabelling equals relabelling the original and residual assignments and
then updating. No conservation or residual feasibility hypothesis is needed. -/
@[simp]
theorem assignmentEquiv_residualUpdate {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (g : N.Assignment R) (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualUpdate g r) =
      residualUpdate (e.assignmentEquiv R g) (e.residualAssignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- The canonical residual difference is invariant under relabelling. -/
@[simp]
theorem assignmentEquiv_residualDifference {R : Type w'} [AddCommGroup R] [Lattice R]
    (e : N ≃ₙ M) (g h : N.Assignment R) :
    e.residualAssignmentEquiv R (residualDifference g h) =
      residualDifference (e.assignmentEquiv R g) (e.assignmentEquiv R h) := by
  apply (e.residualAssignmentEquiv R).symm.injective
  funext x y a
  cases a <;> simp

end Assignments

variable [AddGroup K] [Preorder K] [AddRightMono K]
  {N : Network.{u, v, w} K V} {M : Network.{u', v', w} K W}

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

/-- Bundled residual transport agrees with assignment transport independent of feasibility. -/
@[simp]
theorem residual_assignmentEquiv (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) (R : Type w') :
    (e.residual f hf).assignmentEquiv R = e.residualAssignmentEquiv R := by
  apply Equiv.ext
  intro r
  apply (e.residualAssignmentEquiv R).symm.injective
  funext x y a
  simp only [residualAssignmentEquiv_symm_apply, residualAssignmentEquiv_apply]
  exact (e.residual f hf).assignmentEquiv_apply R r a

/- Forward and reverse arrow formulas simplify using `Equiv.sumCongr_apply` and the
`Sum.map` constructor lemmas, without additional simp registrations. -/

/-- Relabelling commutes with reversing a residual arrow to its other tagged copy. -/
theorem residual_homEquiv_swap (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) {x y : V} (a : ResidualHom N.Hom x y) :
    (e.residual f hf).homEquiv y x a.swap = ((e.residual f hf).homEquiv x y a).swap := by
  cases a <;> rfl

end TauCeti.Network.Iso
