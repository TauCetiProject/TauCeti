/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Characteristic

/-!
# Characteristic-covector orbits of a plumbing lattice

This file packages characteristic covectors of the plumbing intersection lattice modulo twice
the image of the integral lattice under the intersection matrix. For a negative-definite
plumbing, these orbits index the **torsion** spin-c structures of the boundary. If the plumbing
graph has cycles, the boundary may also have non-torsion spin-c structures, which this quotient
does not index. The definitions below apply to an arbitrary plumbing graph and assert only the
lattice quotient, without a topological identification for a degenerate intersection matrix.

The relation is deliberately stated using the intersection matrix acting on coordinate vectors:
this is the integral form of the usual quotient
`Char(P) / 2 PD(H₂(P))`. The existing weight-translation API then supplies the corresponding
comparison between representatives of one class.

## Main definitions

* `TauCeti.PlumbingGraph.IsSpinCEquivalent`: characteristic covectors differing by `2 * A x`.
* `TauCeti.PlumbingGraph.characteristicOrbits`: characteristic covectors modulo this relation.
* `TauCeti.PlumbingGraph.characteristicOrbit`: the orbit of a characteristic covector.

## References

For negative-definite plumbings, the identification of these orbits with torsion boundary
spin-c structures is given by A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 2.2.2. This is the indexing
convention for the lattice homology in the Combinatorial Heegaard Floer roadmap, Lane L.
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- Two characteristic covectors lie in the same lattice orbit when their difference is twice
an integral covector in the image of the plumbing intersection matrix. -/
def IsSpinCEquivalent (k l : P.characteristicVectors) : Prop :=
  ∃ x : V → ℤ, l.val = fun v => k.val v + 2 * (P.intersectionMatrix.mulVec x) v

/-- Every characteristic covector lies in its own lattice orbit. -/
@[refl]
theorem isSpinCEquivalent_refl (k : P.characteristicVectors) : P.IsSpinCEquivalent k k :=
  ⟨0, by funext v; simp⟩

/-- Reversing an integral translation reverses the lattice equivalence. -/
@[symm]
theorem IsSpinCEquivalent.symm {k l : P.characteristicVectors}
    (h : P.IsSpinCEquivalent k l) : P.IsSpinCEquivalent l k := by
  rcases h with ⟨x, hx⟩
  refine ⟨-x, ?_⟩
  rw [hx]
  ext v
  simp only [Pi.neg_apply, Matrix.mulVec_neg]
  ring

/-- Integral translations compose by addition, so lattice equivalence is transitive. -/
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

/-- The setoid of characteristic covectors in the same lattice orbit. -/
def spinCSetoid : Setoid P.characteristicVectors where
  r := P.IsSpinCEquivalent
  iseqv := {
    refl := fun k => P.isSpinCEquivalent_refl k
    symm := fun {_ _} h => IsSpinCEquivalent.symm P h
    trans := fun {_ _ _} h₁ h₂ => IsSpinCEquivalent.trans P h₁ h₂ }

/-- Characteristic covectors modulo twice the image of the plumbing intersection matrix. -/
abbrev characteristicOrbits : Type _ := Quotient P.spinCSetoid

/-- The lattice orbit of a characteristic covector. -/
def characteristicOrbit (k : P.characteristicVectors) : P.characteristicOrbits := Quotient.mk _ k

/-- Every lattice orbit has a characteristic-covector representative. -/
theorem characteristicOrbit_surjective : Function.Surjective P.characteristicOrbit := by
  intro s
  obtain ⟨k, rfl⟩ := Quotient.exists_rep s
  exact ⟨k, rfl⟩

/-- Two characteristic covectors have the same lattice orbit exactly when they differ by twice an
intersection-matrix vector. -/
@[simp]
theorem characteristicOrbit_eq_iff (k l : P.characteristicVectors) :
    P.characteristicOrbit k = P.characteristicOrbit l ↔ P.IsSpinCEquivalent k l :=
  Quotient.eq_iff_equiv

/-- Adding twice an intersection-matrix vector does not change the lattice orbit. -/
@[simp]
theorem characteristicOrbit_add_two_mulVec (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicOrbit ⟨fun v => k.val v + 2 * (P.intersectionMatrix.mulVec x) v,
      k.property.add_two_mul⟩ = P.characteristicOrbit k := by
  rw [P.characteristicOrbit_eq_iff]
  exact ⟨-x, by
    ext v
    simp only [Pi.neg_apply, Matrix.mulVec_neg]
    ring⟩

end PlumbingGraph

end TauCeti
