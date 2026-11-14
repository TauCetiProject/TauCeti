/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The isometry action on antipodal pairs

The full lattice isometry group permutes the antipodal pairs in each norm shell. Negation
acts trivially. A spanning collection of shell vectors all pairing nontrivially with one
shell vector forces every element of the kernel to be identity or negation: preservation
of the pairings forces all the signs to agree.

This criterion detects the kernel of projective lattice actions without assuming generation
of the isometry group by a proposed list of generators.
-/

public section

namespace TauCeti.IntegralLattice.Isometry

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- The permutation representation on unordered antipodal pairs in a norm shell. -/
def antipodalPairsHom (L : IntegralLattice V) (n : ℚ) :
    Isometry L L →* Equiv.Perm (L.antipodalPairs n) where
  toFun e := e.antipodalPairsEquiv n
  map_one' := antipodalPairsEquiv_refl L n
  map_mul' e f := antipodalPairsEquiv_trans f e n

/-- The pair representation is induced by the isometry's antipodal-pair equivalence. -/
theorem antipodalPairsHom_apply (e : Isometry L L) (n : ℚ) :
    antipodalPairsHom L n e = e.antipodalPairsEquiv n := (rfl)

/-- The pair permutation applies the isometry to both entries. -/
@[simp]
theorem coe_antipodalPairsHom_apply (e : Isometry L L) (n : ℚ)
    (p : L.antipodalPairs n) :
    (antipodalPairsHom L n e p : Sym2 L) = Sym2.map e.carrierEquiv p :=
  e.coe_antipodalPairsEquiv_apply n p

/-- The inverse pair permutation applies the inverse isometry to both entries. -/
@[simp]
theorem coe_antipodalPairsHom_symm_apply (e : Isometry L L) (n : ℚ)
    (p : L.antipodalPairs n) :
    ((antipodalPairsHom L n e).symm p : Sym2 L) = Sym2.map e.carrierEquiv.symm p :=
  e.coe_antipodalPairsEquiv_symm_apply n p

/-- Negation fixes every antipodal pair. -/
@[simp]
theorem antipodalPairsHom_neg (L : IntegralLattice V) (n : ℚ) :
    antipodalPairsHom L n (neg L) = 1 := by
  apply Equiv.ext
  intro p
  obtain ⟨x, _, hp⟩ := mem_antipodalPairs.mp p.2
  apply Subtype.ext
  simp [coe_antipodalPairsHom_apply, ← hp]

/-- An isometry acts trivially on antipodal pairs exactly when it sends each vector of the
shell to itself or its negative. -/
theorem mem_ker_antipodalPairsHom_iff (e : Isometry L L) (n : ℚ) :
    e ∈ (antipodalPairsHom L n).ker ↔
      ∀ x ∈ L.vectorsOfNorm n, e (x : V) = x ∨ e (x : V) = -(x : V) := by
  constructor
  · intro h x hx
    have hp := congrArg (fun f : Equiv.Perm (L.antipodalPairs n) ↦
      (f ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ : Sym2 L))
      (MonoidHom.mem_ker.mp h)
    simp only [coe_antipodalPairsHom_apply, Sym2.map_mk, map_neg,
      Equiv.Perm.one_apply, Sym2.eq_iff] at hp
    rcases hp with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h.1)
    · exact Or.inr (by simpa using congrArg Subtype.val h.1)
  · intro h
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro p
    obtain ⟨x, hx, hp⟩ := mem_antipodalPairs.mp p.2
    apply Subtype.ext
    simp only [coe_antipodalPairsHom_apply, Equiv.Perm.one_apply, ← hp, Sym2.map_mk, map_neg]
    rcases h x hx with hx | hx
    · have : e.carrierEquiv x = x := Subtype.ext (by simpa using hx)
      simp [this]
    · have : e.carrierEquiv x = -x := Subtype.ext (by simpa using hx)
      simp [this]

/-- An isometry sending each vector of a spanning set and a vector pairing nontrivially with
all of that set to itself or its negative is the identity or negation. This criterion does not
require positive definiteness or finiteness. -/
theorem eq_one_or_neg_of_span_of_form_ne_zero (e : Isometry L L) {S : Set V}
    (hspan : Submodule.span ℚ S = ⊤) {y : V} (hy : e y = y ∨ e y = -y)
    (hS : ∀ x ∈ S, e x = x ∨ e x = -x) (hpair : ∀ x ∈ S, L.form x y ≠ 0) :
    e = 1 ∨ e = neg L := by
  have hext (f : Isometry L L) (hf : ∀ x ∈ S, e x = f x) : e = f := by
    apply Isometry.ext
    exact LinearMap.congr_fun (LinearMap.ext_on hspan hf)
  rcases hy with hy | hy
  · left
    apply hext
    intro x hx
    rcases hS x hx with h | h
    · simpa using h
    · have hp := e.map_app x y
      rw [h, hy] at hp
      simp only [map_neg, LinearMap.neg_apply] at hp
      exfalso
      exact hpair x hx (by linarith)
  · right
    apply hext
    intro x hx
    rcases hS x hx with h | h
    · have hp := e.map_app x y
      rw [h, hy] at hp
      simp only [map_neg] at hp
      exfalso
      exact hpair x hx (by linarith)
    · simpa using h

end TauCeti.IntegralLattice.Isometry
