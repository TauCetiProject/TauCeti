/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.SupClosed

/-!
# Submodular functions on lattices

This file defines submodularity for functions on lattices and establishes its elementary closure
properties. It also proves that the minimizers of a submodular function over a sublattice form a
sublattice. This is the order-theoretic input for lattices of minimum cuts, independently of any
particular graph or network representation.

## Main declarations

* `TauCeti.IsSubmodular`: the submodular inequality on a lattice.
* `TauCeti.IsSymmSubmodular`: a symmetric submodular function on a Boolean algebra.
* `TauCeti.IsSubmodular.add`: sums of submodular functions are submodular.
* `TauCeti.IsSubmodular.comp_latticeHom`: precomposition by a lattice homomorphism preserves
  submodularity.
* `TauCeti.isSubmodular_finsetSum`: summing fixed vertex weights over a finite set is submodular.
* `TauCeti.IsSubmodular.isSublattice_minimizers`: minimizers over a sublattice form a sublattice.
-/

public section

namespace TauCeti

variable {K L M : Type*}

/-- A function on a lattice is submodular if its values at a join and a meet sum to at most the
sum of its values at the original pair. -/
def IsSubmodular [Add K] [LE K] [Lattice L] (f : L → K) : Prop :=
  ∀ a b, f (a ⊔ b) + f (a ⊓ b) ≤ f a + f b

/-- A function on a Boolean algebra is symmetric submodular if it is invariant under taking
complements and is submodular. Symmetry is additional data: the submodular theory itself does not
require it. -/
structure IsSymmSubmodular [Add K] [LE K] [BooleanAlgebra L] (f : L → K) : Prop where
  /-- An element and its complement have the same value. -/
  symm (a : L) : f aᶜ = f a
  /-- The set function satisfies the submodular inequality. -/
  submodular : IsSubmodular f

/-- A function is submodular exactly when it satisfies the submodular inequality at every pair. -/
theorem isSubmodular_def [Add K] [LE K] [Lattice L] (f : L → K) :
    IsSubmodular f ↔ ∀ a b, f (a ⊔ b) + f (a ⊓ b) ≤ f a + f b := Iff.rfl

/-- A constant function on a lattice is submodular. -/
theorem isSubmodular_const [Add K] [Preorder K] [Lattice L] (c : K) :
    IsSubmodular (fun _ : L ↦ c) := by
  intro a b
  exact le_rfl

/-- The sum of fixed weights over a finite set is submodular. In fact, its submodular inequality
is always an equality. -/
theorem isSubmodular_finsetSum {V : Type*} [DecidableEq V] [AddCommMonoid K] [Preorder K]
    (f : V → K) : IsSubmodular (fun S : Finset V ↦ ∑ v ∈ S, f v) := by
  intro S T
  exact le_of_eq Finset.sum_union_inter

namespace IsSubmodular

/-- Extract the submodular inequality at a pair of lattice elements. -/
protected theorem apply [Add K] [LE K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    (a b : L) : f (a ⊔ b) + f (a ⊓ b) ≤ f a + f b :=
  (isSubmodular_def f).mp hf a b

/-- The pointwise sum of two submodular functions is submodular. -/
theorem add [AddCommMonoid K] [PartialOrder K] [IsOrderedAddMonoid K] [Lattice L]
    {f g : L → K} (hf : IsSubmodular f) (hg : IsSubmodular g) :
    IsSubmodular (fun a ↦ f a + g a) := by
  intro a b
  calc
    (f (a ⊔ b) + g (a ⊔ b)) + (f (a ⊓ b) + g (a ⊓ b)) =
        (f (a ⊔ b) + f (a ⊓ b)) + (g (a ⊔ b) + g (a ⊓ b)) := by
          ac_rfl
    _ ≤ (f a + f b) + (g a + g b) := add_le_add (hf a b) (hg a b)
    _ = (f a + g a) + (f b + g b) := by ac_rfl

/-- Precomposition with a lattice homomorphism preserves submodularity. -/
theorem comp_latticeHom [Add K] [LE K] [Lattice L] [Lattice M] {f : L → K}
    (hf : IsSubmodular f) (g : LatticeHom M L) : IsSubmodular (f ∘ g) := by
  intro a b
  simpa only [Function.comp_apply, map_sup, map_inf] using hf (g a) (g b)

/-- The join and meet of two minimizers of a submodular function are again minimizers, provided
the domain of minimization is closed under joins and meets. -/
theorem isMinOn_sup_inf [AddCommMonoid K] [PartialOrder K] [IsOrderedCancelAddMonoid K]
    [Lattice L] {f : L → K} (hf : IsSubmodular f) {s : Set L} (hs : IsSublattice s)
    {a b : L} (ha : a ∈ s) (hb : b ∈ s) (hamin : IsMinOn f s a) (hbmin : IsMinOn f s b) :
    IsMinOn f s (a ⊔ b) ∧ IsMinOn f s (a ⊓ b) := by
  rw [isMinOn_iff] at hamin hbmin ⊢
  have hab := hf a b
  have hsup : a ⊔ b ∈ s := hs.supClosed ha hb
  have hinf : a ⊓ b ∈ s := hs.infClosed ha hb
  have hsup_le : f (a ⊔ b) ≤ f a := by
    have h : f (a ⊔ b) + f b ≤ f a + f b :=
      (add_le_add_right (hbmin _ hinf) _).trans hab
    exact le_of_add_le_add_right h
  have hinf_le : f (a ⊓ b) ≤ f b := by
    have h : f a + f (a ⊓ b) ≤ f a + f b :=
      (add_le_add_left (hamin _ hsup) _).trans hab
    exact le_of_add_le_add_left h
  exact ⟨fun _ hc ↦ hsup_le.trans (hamin _ hc), fun _ hc ↦ hinf_le.trans (hbmin _ hc)⟩

/-- The minimizers of a submodular function over a sublattice form a sublattice. Membership in
this set records both membership in the original domain and minimality there. -/
theorem isSublattice_minimizers [AddCommMonoid K] [PartialOrder K]
    [IsOrderedCancelAddMonoid K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    {s : Set L} (hs : IsSublattice s) :
    IsSublattice {a | a ∈ s ∧ IsMinOn f s a} := by
  constructor
  · rintro a ⟨ha, hamin⟩ b ⟨hb, hbmin⟩
    exact ⟨hs.supClosed ha hb, (hf.isMinOn_sup_inf hs ha hb hamin hbmin).1⟩
  · rintro a ⟨ha, hamin⟩ b ⟨hb, hbmin⟩
    exact ⟨hs.infClosed ha hb, (hf.isMinOn_sup_inf hs ha hb hamin hbmin).2⟩

end IsSubmodular

end TauCeti
