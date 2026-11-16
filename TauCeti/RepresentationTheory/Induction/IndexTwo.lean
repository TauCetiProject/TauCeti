/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Two
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
import Mathlib.GroupTheory.IndexNormal

/-!
# Inducing a linear character from an inverted subgroup of index two

Let `N` be a subgroup of index two in a finite group `G` -- so `N` is normal -- and suppose a
single element `s` outside `N` conjugates `N` by inversion, `s * x * s⁻¹ = x⁻¹`.  That hypothesis
already forces every element outside `N` to conjugate by inversion as well
(`TauCeti.conj_eq_inv_of_notMem_of_index_two`).  It is the shape of a dihedral group over its
rotations and of a dicyclic group over its cyclic subgroup, and it makes the character of the
representation induced from a linear character `ψ` of `N` completely explicit: it vanishes off `N`
(`TauCeti.character_indFDRep_eq_zero_of_notMem_of_index_two`, which needs neither the inversion
hypothesis nor linearity), and on `N` it is `ψ + ψ⁻¹`.

On `N` the division-free two-coset formula `TauCeti.character_indFDRep_eq_add_of_index_two` is the
one to use.  A linear character takes its values in the commutative group `kˣ`, and conjugating by
an element outside `N` inverts it, so the two coset terms are `ψ` and `ψ⁻¹`.

## Main statements

* `TauCeti.character_indFDRep_eq_add_of_index_two`: the division-free two-coset formula
  for an arbitrary representation induced from a subgroup of index two.
* `TauCeti.character_indFDRep_eq_zero_of_notMem_of_index_two`: **off a subgroup of index two, an
  induced character vanishes.**
* `TauCeti.character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv`: **on the
  subgroup, the character induced from a linear character is `ψ + ψ⁻¹`**.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.3 and §7.2.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [Finite G]

omit [Finite G] in
/-- For a subgroup of index two, the induced character has just two summands: those
at the identity representative and at any representative outside the subgroup.
No invertibility assumption on the subgroup order is needed. -/
theorem character_indFDRep_eq_add_of_index_two [N.FiniteIndex]
    (hindex : N.index = 2) {s : G} (hs : s ∉ N) (A : FDRep k N) (g : G) :
    (indFDRep A).character g =
      Function.indTerm A.character g 1 + Function.indTerm A.character g s := by
  classical
  let := Fintype.ofFinite (G ⧸ N)
  rw [character_indFDRep_sum_quotient]
  simp only [← Function.indTerm_apply]
  rw [sum_quotient_eq_add_of_index_two hindex hs]
  exact congrArg₂ (· + ·)
    (Function.indTerm_eq_of_mk_eq A.character (ClassFunction.mem_iff.mpr A.char_conj) g _ 1
      (Quotient.out_eq' _))
    (Function.indTerm_eq_of_mk_eq A.character (ClassFunction.mem_iff.mpr A.char_conj) g _ s
      (Quotient.out_eq' _))

/-- **Off a subgroup of index two, an induced character vanishes.**  A subgroup of index two is
normal, so this is `TauCeti.character_indFDRep_eq_zero_of_notMem` stated against the explicit
hypothesis `N.index = 2` that the formula on `N` below is stated against, rather than against a
`N.Normal` instance a user holding only that hypothesis cannot synthesize. -/
@[simp]
theorem character_indFDRep_eq_zero_of_notMem_of_index_two (hindex : N.index = 2) (A : FDRep k N)
    {g : G} (hg : g ∉ N) : (indFDRep (k := k) (G := G) A).character g = 0 := by
  have := Subgroup.normal_of_index_eq_two hindex
  exact character_indFDRep_eq_zero_of_notMem A hg

/-- **On an inverted subgroup of index two, the character induced from a linear character `ψ` is
`ψ + ψ⁻¹`.**  Together with `TauCeti.character_indFDRep_eq_zero_of_notMem_of_index_two`, which
gives the value `0` off `N` from the same hypothesis `hindex`, this determines the induced
character on all of `G`.  This holds over any field `k`, with no assumption on the
order of `N`. -/
theorem character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv
    (hindex : N.index = 2) {s : G} (hs : s ∉ N) (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹)
    (ψ : N →* kˣ) {g : G} (hg : g ∈ N) :
    (indFDRep (k := k) (G := G) (FDRep.ofLinearCharacter ψ)).character g =
      (ψ ⟨g, hg⟩ : k) + ((ψ ⟨g, hg⟩)⁻¹ : kˣ) := by
  classical
  have hsinv : s⁻¹ ∉ N := fun h => hs (by simpa using N.inv_mem h)
  have hconj : s⁻¹ * g * s ∈ N := by
    have := Subgroup.normal_of_index_eq_two hindex
    simpa using (inferInstance : N.Normal).conj_mem g hg s⁻¹
  have hsplit : (⟨s⁻¹ * g * s, hconj⟩ : N) = (⟨g, hg⟩ : N)⁻¹ :=
    Subtype.ext (by simpa using conj_eq_inv_of_notMem_of_index_two hindex hs hinv hsinv hg)
  rw [character_indFDRep_eq_add_of_index_two hindex hs, Function.indTerm_apply,
    Function.indTerm_apply, dite_eq_left (by simpa using hg), dite_eq_left hconj,
    FDRep.char_ofLinearCharacter, FDRep.char_ofLinearCharacter, hsplit, map_inv]
  simp

end TauCeti
