/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Basic
-- The groupoid proofs compute the arrow maps of `Iso.refl`, `Iso.trans`, and `Iso.symm`.
import all TauCeti.Combinatorics.Network.Isomorphism.Basic

/-!
# Residual networks under network isomorphisms

A bounded-network isomorphism relabels the residual arrows. `Network.Iso.residualZero` packages
this relabelling using zero capacities, so that the existing `Network.Iso.assignmentEquiv` API
transports residual assignments without a feasible reference or additional assumptions on the
original bound coefficients. At corresponding feasible assignments, `Network.Iso.residual`
packages the same relabelling with the actual residual capacities.

Forward and reverse tags are preserved, even for loops and antiparallel arrows. Transport
commutes with capacities, net changes, updates, and canonical differences without finiteness.
The existing `Network.Iso` API also transports walks and, under finiteness, excess,
circulations, and flows.
-/

public section

namespace TauCeti.Network.Iso

universe u u' u'' v v' v'' w w'

variable {V : Type u} {W : Type u'} {K : Type w}

section Relabelling

variable [LE K] {N : Network.{u, v, w} K V} {M : Network.{u', v', w} K W}

/-- Relabel the residual arrow families independently of feasibility. The zero capacities are
only placeholders: assignment transport is independent of the bounds. Reducibility lets the
endpoints and tagged arrow families compute for the dependent assignment API. -/
@[expose, reducible]
def residualZero (e : N ≃ₙ M) :
    Network.ofCapacity (K := ℕ) (ResidualHom N.Hom) 0 (fun _ ↦ le_rfl) ≃ₙ
      Network.ofCapacity (K := ℕ) (ResidualHom M.Hom) 0 (fun _ ↦ le_rfl) where
  vertexEquiv := e.vertexEquiv
  homEquiv x y := Equiv.sumCongr (e.homEquiv x y) (e.homEquiv y x)
  map_lower _ := rfl
  map_upper _ := rfl

/-- Zero-capacity residual relabelling uses the original vertex equivalence. -/
@[simp]
theorem residualZero_vertexEquiv (e : N ≃ₙ M) : e.residualZero.vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- Zero-capacity residual relabelling retains the forward and reverse tags. -/
@[simp]
theorem residualZero_homEquiv (e : N ≃ₙ M) (x y : V) :
    e.residualZero.homEquiv x y = Equiv.sumCongr (e.homEquiv x y) (e.homEquiv y x) :=
  (rfl)

/-- The identity isomorphism induces the identity on zero-capacity residual networks. -/
@[simp]
theorem residualZero_refl (N : Network K V) : (refl N).residualZero = refl _ := by
  refine Iso.ext rfl (heq_of_eq ?_)
  funext x y
  exact Equiv.sumCongr_refl

/-- Zero-capacity residual relabelling respects composition. -/
@[simp]
theorem residualZero_trans {X : Type u''} {P : Network.{u'', v'', w} K X}
    (e : N ≃ₙ M) (f : M ≃ₙ P) :
    (e.trans f).residualZero = e.residualZero.trans f.residualZero := by
  refine Iso.ext rfl (heq_of_eq ?_)
  funext x y
  exact (Equiv.sumCongr_trans ..).symm

private theorem residual_homOfEq {Q : V → V → Type v} {x y x' y' : V}
    (hx : x = x') (hy : y = y') (a : ResidualHom Q x y) :
    @Quiver.homOfEq V ⟨ResidualHom Q⟩ _ _ _ _ a hx hy =
      a.map (fun b ↦ @Quiver.homOfEq V ⟨Q⟩ _ _ _ _ b hx hy)
        (fun b ↦ @Quiver.homOfEq V ⟨Q⟩ _ _ _ _ b hy hx) := by
  subst x' y'
  cases a <;> rfl

/-- Zero-capacity residual relabelling respects inversion. -/
@[simp]
theorem residualZero_symm (e : N ≃ₙ M) : e.symm.residualZero = e.residualZero.symm := by
  refine Iso.ext (symm_vertexEquiv e) (heq_of_eq ?_)
  funext x y
  apply Equiv.ext
  intro a
  -- Both inverse arrow maps transport endpoints to the original inverse vertex map.
  change Equiv.sumCongr (e.inverseHomEquiv x y) (e.inverseHomEquiv y x) a =
    e.residualZero.inverseHomEquiv x y a
  rw [inverseHomEquiv_apply e.residualZero, residualZero_homEquiv, Equiv.sumCongr_symm,
    residual_homOfEq]
  cases a <;> simp [inverseHomEquiv_apply]

/-- Assignment transport preserves evaluation on a relabelled residual arrow in `Sum.map`
normal form. -/
@[simp]
theorem assignmentEquiv_residualZero_apply {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V} (a : ResidualHom N.Hom x y) :
    e.residualZero.assignmentEquiv R r (Sum.map (e.homEquiv x y) (e.homEquiv y x) a) = r a :=
  e.residualZero.assignmentEquiv_apply R r a

/-- Assignment transport preserves evaluation on a relabelled forward copy. -/
@[simp]
theorem assignmentEquiv_residualZero_inl {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V} (a : N.Hom x y) :
    e.residualZero.assignmentEquiv R r (Sum.inl (e.homEquiv x y a)) = r (Sum.inl a) :=
  e.residualZero.assignmentEquiv_apply R r (Sum.inl a)

/-- Assignment transport preserves evaluation on a relabelled reverse copy. -/
@[simp]
theorem assignmentEquiv_residualZero_inr {R : Type w'} (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) {x y : V} (a : N.Hom y x) :
    e.residualZero.assignmentEquiv R r (Sum.inr (e.homEquiv y x a)) = r (Sum.inr a) :=
  e.residualZero.assignmentEquiv_apply R r (Sum.inr a)

-- These simp rules match goals whose arrow finiteness instances are inferred on `ResidualHom`,
-- rather than on the projections of the zero-capacity networks.

/-- Relabelling preserves excess on the residual arrow family. -/
@[simp]
theorem excessAt_assignmentEquiv_residualZero [Fintype V] [Fintype W]
    [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (M.Hom x y)]
    {R : Type w'} [AddCommGroup R] (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) (x : V) :
    TauCeti.excessAt (e.residualZero.assignmentEquiv R r) (e.vertexEquiv x) =
      TauCeti.excessAt r x :=
  e.residualZero.excessAt_assignmentEquiv r x

/-- Relabelling preserves and reflects circulation on the residual arrow family. -/
@[simp]
theorem isCirculation_assignmentEquiv_residualZero_iff [Fintype V] [Fintype W]
    [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (M.Hom x y)]
    {R : Type w'} [AddCommGroup R] (e : N ≃ₙ M)
    (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    IsCirculation (e.residualZero.assignmentEquiv R r) ↔ IsCirculation r :=
  e.residualZero.isCirculation_assignmentEquiv_iff r

/-- Relabelling commutes with residual capacities, independently of feasibility. -/
@[simp]
theorem assignmentEquiv_residualCapacity {R : Type w'} [Sub R] (e : N ≃ₙ M)
    (lo hi g : N.Assignment R) :
    e.residualZero.assignmentEquiv R (residualCapacity lo hi g) =
      residualCapacity (e.assignmentEquiv R lo) (e.assignmentEquiv R hi)
        (e.assignmentEquiv R g) := by
  apply (e.residualZero.assignmentEquiv R).symm.injective
  funext x y a
  cases a <;> simp

/-- The net change of a residual assignment commutes with network isomorphisms. Its coefficients
may be independent of those used for the network bounds. -/
@[simp]
theorem assignmentEquiv_residualNet {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualNet r) = residualNet (e.residualZero.assignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- Updating and then relabelling equals relabelling the original and residual assignments and
then updating. No conservation or residual feasibility hypothesis is needed. -/
@[simp]
theorem assignmentEquiv_residualUpdate {R : Type w'} [AddCommGroup R]
    (e : N ≃ₙ M) (g : N.Assignment R) (r : TauCeti.Assignment (ResidualHom N.Hom) R) :
    e.assignmentEquiv R (residualUpdate g r) =
      residualUpdate (e.assignmentEquiv R g) (e.residualZero.assignmentEquiv R r) := by
  apply (e.assignmentEquiv R).symm.injective
  funext x y a
  simp

/-- The canonical residual difference is invariant under relabelling. -/
@[simp]
theorem assignmentEquiv_residualDifference {R : Type w'} [AddCommGroup R] [Lattice R]
    (e : N ≃ₙ M) (g h : N.Assignment R) :
    e.residualZero.assignmentEquiv R (residualDifference g h) =
      residualDifference (e.assignmentEquiv R g) (e.assignmentEquiv R h) := by
  apply (e.residualZero.assignmentEquiv R).symm.injective
  funext x y a
  cases a <;> simp

end Relabelling

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
  vertexEquiv := e.residualZero.vertexEquiv
  homEquiv := e.residualZero.homEquiv
  map_lower _ := rfl
  map_upper a := by
    rcases a with a | a <;> simp [e.map_lower, e.map_upper]

/-- Residual transport uses the original vertex equivalence. -/
@[simp]
theorem residual_vertexEquiv (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) : (e.residual f hf).vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- Residual arrow transport retains the forward and reverse tags. -/
@[simp]
theorem residual_homEquiv (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) (x y : V) :
    (e.residual f hf).homEquiv x y = Equiv.sumCongr (e.homEquiv x y) (e.homEquiv y x) :=
  (rfl)

/-- Bundled residual transport agrees with assignment transport independent of feasibility. -/
@[simp]
theorem assignmentEquiv_residual (e : N ≃ₙ M) (f : N.Assignment K)
    (hf : f ∈ Set.Icc N.lower N.upper) (R : Type w') :
    (e.residual f hf).assignmentEquiv R = e.residualZero.assignmentEquiv R := by
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  intro r
  funext x y a
  simp

/- Forward and reverse arrow formulas simplify using `Equiv.sumCongr_apply` and the
`Sum.map` constructor lemmas, without additional simp registrations. -/

end TauCeti.Network.Iso
