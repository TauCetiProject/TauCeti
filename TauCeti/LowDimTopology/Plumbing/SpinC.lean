/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Characteristic

/-!
# Spin-c structures of a plumbing lattice

For a plumbed three-manifold, a spin-c structure is represented by a characteristic covector of
the plumbing intersection lattice, with two representatives identified when they differ by twice
the image of an integral lattice vector under the intersection matrix. This file packages that
quotient. It gives the missing carrier on which the lattice-homology invariant is indexed, rather
than treating every characteristic covector as a distinct spin-c structure.

The relation is deliberately stated using the intersection matrix acting on coordinate vectors:
this is the integral form of the usual quotient
`Char(P) / 2 PD(H₂(P))`. The existing weight-translation API then supplies the corresponding
comparison between representatives of one class.

## Main definitions

* `TauCeti.PlumbingGraph.IsSpinCEquivalent`: characteristic covectors differing by `2 * A x`.
* `TauCeti.PlumbingGraph.spinCStructures`: characteristic covectors modulo this relation.
* `TauCeti.PlumbingGraph.spinCClass`: the class represented by a characteristic covector.

## References

The identification of spin-c structures with characteristic covectors modulo twice the
intersection lattice is standard in plumbing calculus; see A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 2. It is the indexing convention for
the lattice homology in the Combinatorial Heegaard Floer roadmap, Lane L.
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- Two characteristic covectors represent the same spin-c structure when their difference is
twice an integral covector in the image of the plumbing intersection matrix. -/
def IsSpinCEquivalent (k l : P.characteristicVectors) : Prop :=
  ∃ x : V → ℤ, l.val = fun v => k.val v + 2 * (P.intersectionMatrix.mulVec x) v

/-- Every characteristic covector represents the same spin-c structure as itself. -/
@[refl]
theorem isSpinCEquivalent_refl (k : P.characteristicVectors) : P.IsSpinCEquivalent k k :=
  ⟨0, by funext v; simp⟩

/-- Reversing an integral translation reverses the represented spin-c equivalence. -/
@[symm]
theorem IsSpinCEquivalent.symm {k l : P.characteristicVectors}
    (h : P.IsSpinCEquivalent k l) : P.IsSpinCEquivalent l k := by
  rcases h with ⟨x, hx⟩
  refine ⟨-x, ?_⟩
  rw [hx]
  ext v
  simp only [Pi.neg_apply, Matrix.mulVec_neg]
  ring

/-- Integral translations compose by addition, so spin-c equivalence is transitive. -/
@[trans]
theorem IsSpinCEquivalent.trans {k l m : P.characteristicVectors}
    (h₁ : P.IsSpinCEquivalent k l) (h₂ : P.IsSpinCEquivalent l m) :
    P.IsSpinCEquivalent k m := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  refine ⟨x + y, ?_⟩
  rw [hy, hx]
  ext v
  rw [Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

/-- The setoid of characteristic covectors representing the same spin-c structure. -/
def spinCSetoid : Setoid P.characteristicVectors where
  r := P.IsSpinCEquivalent
  iseqv := {
    refl := fun k => P.isSpinCEquivalent_refl k
    symm := fun {_ _} h => IsSpinCEquivalent.symm P h
    trans := fun {_ _ _} h₁ h₂ => IsSpinCEquivalent.trans P h₁ h₂ }

/-- The spin-c structures represented by the plumbing lattice. -/
abbrev spinCStructures : Type _ := Quotient P.spinCSetoid

/-- The spin-c structure represented by a characteristic covector. -/
def spinCClass (k : P.characteristicVectors) : P.spinCStructures := Quotient.mk _ k

/-- Every spin-c structure has a characteristic-covector representative. -/
theorem spinCClass_surjective : Function.Surjective P.spinCClass := by
  intro s
  obtain ⟨k, rfl⟩ := Quotient.exists_rep s
  exact ⟨k, rfl⟩

/-- Two characteristic covectors have the same spin-c class exactly when they differ by twice an
intersection-matrix vector. -/
@[simp]
theorem spinCClass_eq_iff (k l : P.characteristicVectors) :
    P.spinCClass k = P.spinCClass l ↔ P.IsSpinCEquivalent k l :=
  Quotient.eq_iff_equiv

/-- Adding twice an intersection-matrix vector does not change the represented spin-c structure. -/
@[simp]
theorem spinCClass_add_two_mulVec (k : P.characteristicVectors) (x : V → ℤ) :
    P.spinCClass ⟨fun v => k.val v + 2 * (P.intersectionMatrix.mulVec x) v,
      k.property.add_two_mul⟩ = P.spinCClass k := by
  rw [P.spinCClass_eq_iff]
  exact ⟨-x, by
    ext v
    simp only [Pi.neg_apply, Matrix.mulVec_neg]
    ring⟩

end PlumbingGraph

end TauCeti
