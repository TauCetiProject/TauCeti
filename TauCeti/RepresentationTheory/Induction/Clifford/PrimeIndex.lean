/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
public import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
public import TauCeti.RepresentationTheory.Induction.Inertia
import Mathlib.GroupTheory.IndexNormal
import TauCeti.RepresentationTheory.Induction.Mackey.Split
import TauCeti.SetTheory.Cardinal.Finite

/-!
# The induced branch of Clifford theory in prime index

If a normal subgroup has prime index, the inertia group of a representation is either the
subgroup or the entire group. Thus the Mackey criterion can be checked at a single element
outside the subgroup. An irreducible character moved by that element induces to the unique
irreducible character lying over it, and the induced character vanishes off the subgroup.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorems 5.6 and 6.11.
* L. Alpöge, [Lean formalization](https://github.com/leanprover-community/riemann-hypothesis),
  `GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter`, for the split case.
-/

public section

open CategoryTheory TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

namespace FDRep

/-- Over a splitting field in which the group order is invertible, induction from a maximal
normal subgroup is simple exactly when the original representation is simple and its
isomorphism class is moved by conjugation by an element outside that subgroup. Scalar Schur is
imposed only on simple representations of the ambient group. -/
theorem simple_indFDRep_iff_of_isCoatom_of_scalarSchur [Finite G] [N.FiniteIndex] (A : FDRep k N)
    (hG : IsUnit (Nat.card G : k))
    (hSplitG : ∀ W : FDRep k G, Simple W → Module.finrank k (W ⟶ W) = 1)
    (hN : IsCoatom N) {x : G} (hx : x ∉ N) :
    Simple (indFDRep A) ↔ Simple A ∧ x ∉ inertia A := by
  rw [A.simple_indFDRep_iff_of_normal_of_scalarSchur hG hSplitG]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h s hs ↦ ?_⟩
  · exact fun hxI ↦ (h x hx).false (mem_inertia_iff.mp hxI).some
  · have heq : inertia A = N := (hN.le_iff.mp (le_inertia A)).resolve_left (by
      intro htop
      exact h (htop ▸ Subgroup.mem_top x))
    exact ⟨fun e ↦ hs (heq ▸ mem_inertia_iff.mpr ⟨e⟩)⟩

/-- Over an algebraically closed field in which the group order is invertible, induction from
a maximal normal subgroup is simple exactly when the original representation is simple and
its isomorphism class is moved by conjugation by an element outside that subgroup. -/
theorem simple_indFDRep_iff_of_isCoatom [N.FiniteIndex] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (A : FDRep k N) (hN : IsCoatom N) {x : G} (hx : x ∉ N) :
    Simple (indFDRep A) ↔ Simple A ∧ x ∉ inertia A :=
  have := finite_of_natCast_card_ne_zero (NeZero.ne (Nat.card G : k))
  A.simple_indFDRep_iff_of_isCoatom_of_scalarSchur (isUnit_iff_ne_zero.mpr (NeZero.ne _))
    (fun W _ ↦ CategoryTheory.finrank_endomorphism_simple_eq_one k W) hN hx

end FDRep

namespace TauCeti

/-- If conjugation by `x` moves the irreducible character `θ` of a normal subgroup `N` of prime
index, induction gives the unique irreducible character of `G` lying over `θ`. The induced
character vanishes outside `N` by `character_indFDRep_eq_zero_of_notMem`. -/
theorem irreducibleCharactersOver_eq_singleton_indClassFun_of_index_prime
    [N.FiniteIndex] [IsAlgClosed k] [NeZero (Nat.card G : k)] (hN : N.index.Prime)
    {θ : N → k} (hθ : θ ∈ irreducibleCharacters k N) {x : G}
    (hmove : ∃ n : N, θ (MulAut.conjNormal x n) ≠ θ n) :
    irreducibleCharactersOver k N θ = {N.indClassFun θ} := by
  classical
  obtain ⟨d, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hθ
  let A : FDRep k N := FDRep.of ρ
  have hA : A.character = ρ.character := FDRep.character_of ρ
  have : Simple A := (FDRep.simple_iff_isIrreducible A).mpr (by simpa [A, FDRep.of_ρ'] using hρ)
  rw [← hA, Subgroup.indClassFun_ofFDRep_character]
  have hxI : x ∉ inertia A := by
    intro h
    obtain ⟨n, hn⟩ := hmove
    apply hn
    obtain ⟨e⟩ := mem_inertia_iff.mp ((inertia A).inv_mem h)
    simpa only [char_conjNormalFDRep, inv_inv, hA] using congrFun (FDRep.char_iso e) n
  have hx : x ∉ N := fun hx ↦ hxI (le_inertia A hx)
  have : Simple (indFDRep A) :=
    (A.simple_indFDRep_iff_of_isCoatom (Subgroup.isCoatom_of_index_prime hN) hx).mpr
      ⟨inferInstance, hxI⟩
  have := finite_of_natCast_card_ne_zero (NeZero.ne (Nat.card G : k))
  let := Fintype.ofFinite G
  have hG : IsUnit (Nat.card G : k) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
  have hN0 := (isUnit_natCard_subgroup N hG).ne_zero
  have hrec := frobenius_reciprocity_resFDRep hG A
  have hind := (indFDRep A).character_mem_irreducibleCharacters
  ext ψ
  rw [mem_irreducibleCharactersOver_iff_sum, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hψ, hpair⟩
    obtain ⟨e, σ, _, rfl⟩ := mem_irreducibleCharacters_iff.mp hψ
    by_contra hne
    -- Frobenius reciprocity turns ambient orthogonality into a zero pairing on `N`.
    have hz := sum_mul_inv_eq_zero_of_mem_irreducibleCharacters hψ hind hne
    have h := hrec (FDRep.of σ)
    rw [FDRep.character_of, hz, mul_zero] at h
    exact hpair ((mul_eq_zero.mp h).resolve_left (inv_ne_zero hN0))
  · rintro rfl
    refine ⟨hind, fun hzero ↦ ?_⟩
    have h := hrec (indFDRep A)
    rw [hzero, mul_zero, sum_mul_inv_self_of_mem_irreducibleCharacters hind,
      inv_mul_cancel₀ hG.ne_zero] at h
    exact zero_ne_one h

end TauCeti
