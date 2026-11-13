/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Cover

/-!
# Checking double-coset transitions using subgroup normal forms

A proposed double-coset cover `H wᵢ H` can be certified without enumerating the ambient group.
Supply a finite normal form `a : κ → H` covering the subgroup, and, for each signed generator,
normal form and cell, a target cell and two correction elements of `H`. The checker verifies
` s a(t) wᵢ = l wⱼ r ` in the actual group and checks that the distinguished representative is
one. Its soundness theorem proves coverage; the intersection-index bounds of
`Subgroup.index_le_sum_of_doubleCoset_cover` then give the subgroup index.

The normal form need not be injective. Its surjectivity must be proved independently, for example
by collection in a power-conjugate presentation. Neither that surjectivity nor a transition
identity may be inferred from its validity in a finite image of a presented group. No finiteness
of the ambient group is assumed. The decidability-free equations are also exposed, so structured
normal forms may be handled symbolically rather than by evaluating the Boolean checker.

## References

* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*, Chapter 5
  (subgroup-based coset enumeration).
-/

public section

open scoped Pointwise

namespace Subgroup

variable {G α ι κ : Type*} [Group G]

/-- Check double-coset transitions on a finite subgroup normal form. The Boolean sign is `true`
for a generator and `false` for its inverse. A correction triple `(l, j, r)` certifies membership
in `H wⱼ H`, using Mathlib's multiplication order, including for permutation groups. -/
@[expose] def checkDoubleCosetTransitions [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq G]
    (H : Subgroup G) (g : α → G) (w : ι → G) (a : κ → H) (root : ι)
    (correction : α → Bool → κ → ι → H × ι × H) : Bool :=
  decide (w root = 1 ∧ ∀ s b t i,
    (if b then g s else (g s)⁻¹) * a t * w i =
      (correction s b t i).1 * w (correction s b t i).2.1 *
        (correction s b t i).2.2)

/-- Acceptance is precisely the root equation and the signed transition identities. -/
@[simp]
theorem checkDoubleCosetTransitions_eq_true [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq G]
    (H : Subgroup G) (g : α → G) (w : ι → G) (a : κ → H) (root : ι)
    (correction : α → Bool → κ → ι → H × ι × H) :
    H.checkDoubleCosetTransitions g w a root correction = true ↔
      w root = 1 ∧ ∀ s b t i,
        (if b then g s else (g s)⁻¹) * a t * w i =
          (correction s b t i).1 * w (correction s b t i).2.1 *
            (correction s b t i).2.2 := by
  simp [checkDoubleCosetTransitions]

/-- Signed transition identities on a surjective subgroup normal form prove that the proposed
cells cover the actual group. The normal form, generator family and cell family may be infinite
in this mathematical version of the checker's soundness theorem. -/
theorem exists_mem_doubleCoset_of_normalForm_transitions (H : Subgroup G) (g : α → G) (w : ι → G)
    (a : κ → H) (root : ι) (correction : α → Bool → κ → ι → H × ι × H)
    (hg : Subgroup.closure (Set.range g) = ⊤) (ha : Function.Surjective a)
    (hroot : w root = 1)
    (hstep : ∀ s b t i, (if b then g s else (g s)⁻¹) * a t * w i =
      (correction s b t i).1 * w (correction s b t i).2.1 *
        (correction s b t i).2.2) :
    ∀ x : G, ∃ i, x ∈ _root_.DoubleCoset.doubleCoset (w i) H H := by
  apply H.exists_mem_doubleCoset_of_generator_transitions w (Set.range g) hg
  · exact ⟨root, _root_.DoubleCoset.mem_doubleCoset.mpr
      ⟨1, H.one_mem, 1, H.one_mem, by simp [hroot]⟩⟩
  · intro s hs i h
    obtain ⟨t, rfl⟩ := ha h
    have step (s : α) (b : Bool) :
        ∃ j, (if b then g s else (g s)⁻¹) * a t * w i ∈
          _root_.DoubleCoset.doubleCoset (w j) H H :=
      ⟨(correction s b t i).2.1, _root_.DoubleCoset.mem_doubleCoset.mpr
        ⟨_, (correction s b t i).1.property, _, (correction s b t i).2.2.property,
          hstep s b t i⟩⟩
    rcases hs with ⟨s, rfl⟩ | hs
    · exact step s true
    · have hs' : s⁻¹ ∈ Set.range g := hs
      obtain ⟨u, hu⟩ := hs'
      have hu' : (g u)⁻¹ = s := by rw [hu, inv_inv]
      simpa [hu'] using step u false

/-- An accepted transition check and a proved subgroup normal form certify double-coset
coverage. Equalities must be checked in `G`, not merely in a homomorphic image of `G`. -/
theorem exists_mem_doubleCoset_of_checkDoubleCosetTransitions
    [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq G]
    (H : Subgroup G) (g : α → G) (w : ι → G) (a : κ → H) (root : ι)
    (correction : α → Bool → κ → ι → H × ι × H)
    (hg : Subgroup.closure (Set.range g) = ⊤) (ha : Function.Surjective a)
    (hcheck : H.checkDoubleCosetTransitions g w a root correction = true) :
    ∀ x : G, ∃ i, x ∈ _root_.DoubleCoset.doubleCoset (w i) H H := by
  obtain ⟨hroot, hstep⟩ := (H.checkDoubleCosetTransitions_eq_true g w a root correction).mp hcheck
  exact H.exists_mem_doubleCoset_of_normalForm_transitions g w a root correction hg ha hroot hstep

/-- A checked double-coset cover bounds the index by the sum of the actual intersection indices.
Repeated cells and redundant subgroup normal forms are allowed. -/
theorem index_le_sum_of_checkDoubleCosetTransitions
    [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq G]
    (H : Subgroup G) (g : α → G) (w : ι → G) (a : κ → H) (root : ι)
    (correction : α → Bool → κ → ι → H × ι × H)
    (hg : Subgroup.closure (Set.range g) = ⊤) (ha : Function.Surjective a)
    (hcheck : H.checkDoubleCosetTransitions g w a root correction = true) :
    H.index ≤ ∑ i, (ConjAct.toConjAct (w i) • H).relIndex H :=
  H.index_le_sum_of_doubleCoset_cover w
    (H.exists_mem_doubleCoset_of_checkDoubleCosetTransitions g w a root correction hg ha hcheck)

/-- A checked double-coset cover with a finite subgroup normal form proves finite index.
This is stronger than a numerical index bound, since an infinite index has numerical value zero. -/
theorem finiteIndex_of_checkDoubleCosetTransitions
    [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq G]
    (H : Subgroup G) (g : α → G) (w : ι → G) (a : κ → H) (root : ι)
    (correction : α → Bool → κ → ι → H × ι × H)
    (hg : Subgroup.closure (Set.range g) = ⊤) (ha : Function.Surjective a)
    (hcheck : H.checkDoubleCosetTransitions g w a root correction = true) : H.FiniteIndex := by
  have : Finite H := Finite.of_surjective a ha
  have (i : ι) : (ConjAct.toConjAct (w i) • H).IsFiniteRelIndex H :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  exact H.finiteIndex_of_doubleCoset_cover w
    (H.exists_mem_doubleCoset_of_checkDoubleCosetTransitions g w a root correction hg ha hcheck)

end Subgroup
