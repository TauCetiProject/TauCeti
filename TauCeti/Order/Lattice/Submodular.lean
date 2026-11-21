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
sublattice, and that symmetric submodular functions are posimodular. These are the order-theoretic
inputs for lattices of minimum cuts and for uncrossing them, independently of any particular graph
or network representation.

## Main declarations

* `TauCeti.IsSubmodular`: the submodular inequality on a lattice.
* `TauCeti.IsSymmSubmodular`: a symmetric submodular function on a Boolean algebra.
* `TauCeti.IsSubmodular.add`: sums of submodular functions are submodular.
* `TauCeti.IsSubmodular.comp_latticeHom`: precomposition by a lattice homomorphism preserves
  submodularity.
* `TauCeti.isSubmodular_finsetSum`: summing fixed vertex weights over a finite set is submodular.
* `TauCeti.IsSubmodular.isMinOn_sup_inf`: uncrossing two minimizers by join and meet.
* `TauCeti.IsSubmodular.isSublattice_minimizers`: minimizers over a sublattice form a sublattice.
* `TauCeti.IsSymmSubmodular.sdiff_add_sdiff_le`: the posimodular inequality.
-/

public section

namespace TauCeti

variable {K L M F : Type*}

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
theorem isSubmodular_const [Add K] [LE K] [@Std.Refl K (· ≤ ·)] [Lattice L] (c : K) :
    IsSubmodular (fun _ : L ↦ c) :=
  fun _ _ ↦ Std.le_refl _

/-- The sum of fixed weights over a finite set is submodular. In fact, its submodular inequality
is always an equality. -/
theorem isSubmodular_finsetSum {V : Type*} [DecidableEq V] [AddCommMonoid K] [LE K]
    [@Std.Refl K (· ≤ ·)] (f : V → K) : IsSubmodular (fun S : Finset V ↦ ∑ v ∈ S, f v) :=
  fun _ _ ↦ by rw [Finset.sum_union_inter]; exact Std.le_refl _

namespace IsSubmodular

/-- Extract the submodular inequality at a pair of lattice elements. -/
protected theorem apply [Add K] [LE K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    (a b : L) : f (a ⊔ b) + f (a ⊓ b) ≤ f a + f b :=
  (isSubmodular_def f).mp hf a b

/-- The pointwise sum of two submodular functions is submodular. The order need only be
transitive, not reflexive: the two submodular inequalities are added one side at a time. -/
theorem add [AddCommSemigroup K] [LE K] [IsTrans K (· ≤ ·)] [AddLeftMono K] [Lattice L]
    {f g : L → K} (hf : IsSubmodular f) (hg : IsSubmodular g) :
    IsSubmodular (fun a ↦ f a + g a) := fun a b ↦
  calc
    (f (a ⊔ b) + g (a ⊔ b)) + (f (a ⊓ b) + g (a ⊓ b)) =
        (f (a ⊔ b) + f (a ⊓ b)) + (g (a ⊔ b) + g (a ⊓ b)) := add_add_add_comm ..
    _ ≤ (f a + f b) + (g (a ⊔ b) + g (a ⊓ b)) := add_le_add_left (hf a b) _
    _ ≤ (f a + f b) + (g a + g b) := add_le_add_right (hg a b) _
    _ = (f a + g a) + (f b + g b) := add_add_add_comm ..

/-- Precomposition with a lattice homomorphism (any map in a `LatticeHomClass`, such as an order
isomorphism) preserves submodularity. -/
theorem comp_latticeHom [Add K] [LE K] [Lattice L] [Lattice M] [FunLike F M L]
    [LatticeHomClass F M L] {f : L → K} (hf : IsSubmodular f) (g : F) :
    IsSubmodular (f ∘ g) := by
  intro a b
  simpa only [Function.comp_apply, map_sup, map_inf] using hf (g a) (g b)

/-- Let `a` minimize a submodular function over `s` and `b` minimize it over `t`. If the meet
lies in `s` and the join lies in `t`, then the join minimizes over `t` and the meet minimizes
over `s`. Addition need not be commutative: it must preserve and reflect the order on both
sides, and the submodular inequality at `b` and `a` puts the summands in the order that each
cancellation needs. -/
theorem isMinOn_sup_inf [Add K] [Preorder K] [AddLeftMono K] [AddRightMono K]
    [AddLeftReflectLE K] [AddRightReflectLE K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    {s t : Set L} {a b : L} (hamin : IsMinOn f s a) (hbmin : IsMinOn f t b) (hsup : a ⊔ b ∈ t)
    (hinf : a ⊓ b ∈ s) : IsMinOn f t (a ⊔ b) ∧ IsMinOn f s (a ⊓ b) := by
  rw [isMinOn_iff] at hamin hbmin ⊢
  have hba : f (a ⊔ b) + f (a ⊓ b) ≤ f b + f a := by
    simpa only [sup_comm b a, inf_comm b a] using hf.apply b a
  have hsup_le : f (a ⊔ b) ≤ f b :=
    le_of_add_le_add_right ((add_le_add_right (hamin _ hinf) _).trans hba)
  have hinf_le : f (a ⊓ b) ≤ f a :=
    le_of_add_le_add_left ((add_le_add_left (hbmin _ hsup) _).trans hba)
  exact ⟨fun _ hc ↦ hsup_le.trans (hbmin _ hc), fun _ hc ↦ hinf_le.trans (hamin _ hc)⟩

/-- The minimizers of a submodular function over a sublattice form a sublattice. Membership in
this set records both membership in the original domain and minimality there. Addition need not
be commutative, but must preserve and reflect the order on both sides. -/
theorem isSublattice_minimizers [Add K] [Preorder K] [AddLeftMono K] [AddRightMono K]
    [AddLeftReflectLE K] [AddRightReflectLE K] [Lattice L] {f : L → K} (hf : IsSubmodular f)
    {s : Set L} (hs : IsSublattice s) :
    IsSublattice {a | a ∈ s ∧ IsMinOn f s a} := by
  constructor
  · rintro a ⟨ha, hamin⟩ b ⟨hb, hbmin⟩
    exact ⟨hs.supClosed ha hb,
      (hf.isMinOn_sup_inf hamin hbmin (hs.supClosed ha hb) (hs.infClosed ha hb)).1⟩
  · rintro a ⟨ha, hamin⟩ b ⟨hb, hbmin⟩
    exact ⟨hs.infClosed ha hb,
      (hf.isMinOn_sup_inf hamin hbmin (hs.supClosed ha hb) (hs.infClosed ha hb)).2⟩

end IsSubmodular

namespace IsSymmSubmodular

/-- The posimodular inequality: a symmetric submodular function also satisfies the submodular
inequality with the two differences in place of the join and meet. -/
theorem sdiff_add_sdiff_le [Add K] [LE K] [BooleanAlgebra L] {f : L → K}
    (hf : IsSymmSubmodular f) (a b : L) : f (a \ b) + f (b \ a) ≤ f a + f b := by
  have h := hf.submodular.apply aᶜ b
  rw [← hf.symm (aᶜ ⊔ b), hf.symm a] at h
  simpa only [sdiff_eq, compl_sup, compl_compl, inf_comm] using h

end IsSymmSubmodular

end TauCeti
