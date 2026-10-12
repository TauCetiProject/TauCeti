/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.Induction.IndexTwo
import Mathlib.RingTheory.IntegralDomain

/-!
# The Frobenius-Schur indicator of a character induced from an index-two subgroup

Let `N` be a subgroup of index two in a finite group `G` on which some element `s` outside `N` acts
by inversion, `s * x * s⁻¹ = x⁻¹`, and let `ψ` be a linear character of `N`, valued in a field `k`
in which the order of `G` is invertible, that is not its own inverse.  Inducing `ψ` gives a
two-dimensional representation of `G`, and this file computes its **Frobenius-Schur indicator**
under that invertibility hypothesis: it is `ψ (s ^ 2)`, the value of `ψ` on the common square of
the elements outside `N`.

This is the shape of a dihedral group over its rotations and of a dicyclic group over its cyclic
subgroup, so for such a group the indicator of an induced linear character is read off the square
of a single element outside the subgroup; the dihedral instance is in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Dihedral.lean`.

The computation reads the character formula
`TauCeti.character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv` against the two
elementary facts about the outside coset recorded in `TauCeti/GroupTheory/Index/Two.lean`: its
elements all have the same square (`TauCeti.sq_eq_sq_of_notMem_of_index_two`), and that square
squares to one (`TauCeti.sq_sq_eq_one_of_conj_eq_inv`).  Inside `N` the character of the induced
representation at `g ^ 2` is `ψ² (g) + (ψ²)⁻¹ (g)`, and `ψ ^ 2 ≠ 1` makes both of those characters
nontrivial, so their sums over `N` vanish (`sum_hom_units_eq_zero`).

## Main statements

* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv`: **the
  indicator of the representation induced from a linear character of an inverted subgroup of index
  two is the value of the character on the common square of the outside elements**, whenever the
  order of the group is invertible in the coefficient field.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

universe v

variable {G : Type v} [Group G] {N : Subgroup G} {k : Type} [Field k]

/-- Over an inverted subgroup `N` of index two, the character of the representation induced from
a linear character `ψ` of `N` that is not its own inverse sums to zero on squares. -/
private theorem sum_filter_mem_character_ρ_indFDRep_sq_eq_zero [Fintype G]
    [DecidablePred (· ∈ N)] (hindex : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) (hN : IsUnit (Nat.card N : k)) {ψ : N →* kˣ}
    (hψ : ψ ^ 2 ≠ 1) :
    ∑ x ∈ Finset.univ.filter (fun g : G => g ∈ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2) = 0 := by
  -- The sums over `N` of the nontrivial characters `ψ ^ 2` and `(ψ ^ 2)⁻¹` vanish.
  have hzeroSum : ∀ χ : N →* kˣ, χ ≠ 1 → ∑ x : N, (χ x : k) = 0 := fun χ hχ =>
    sum_hom_units_eq_zero ((Units.coeHom k).comp χ) fun h =>
      hχ <| MonoidHom.ext fun x => Units.ext (DFunLike.congr_fun h x)
  -- The `Inv` on `N →* kˣ` is `MonoidHom.instInv`, so `inv_ne_one` needs its argument
  -- pinned before the `DivisionMonoid` instance it is stated for can be found.
  have hinvψ : (ψ ^ 2)⁻¹ ≠ 1 := (inv_ne_one (a := ψ ^ 2)).mpr hψ
  have hstep (x : N) : Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ
      ((x : G) ^ 2) = (((ψ ^ 2) x : kˣ) : k) + ((((ψ ^ 2)⁻¹) x : kˣ) : k) := by
    rw [FDRep.character_ρ,
      character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv hindex hs hinv hN ψ
        (Subgroup.sq_mem_of_index_two hindex _)]
    simp [← SubmonoidClass.mk_pow]
  rw [Finset.sum_subtype (p := (· ∈ N)) _ (fun x => by simp) _,
    Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_add_distrib, hzeroSum _ hψ,
    hzeroSum _ hinvψ, add_zero]

/-- Off an inverted subgroup `N` of index two, the character of the representation induced from
a linear character `ψ` of `N` sums on squares to `|N|` copies of `2 ψ (s ^ 2)`. -/
private theorem sum_filter_notMem_character_ρ_indFDRep_sq [Fintype G] [DecidablePred (· ∈ N)]
    (hindex : N.index = 2) {s : G} (hs : s ∉ N) (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹)
    (hN : IsUnit (Nat.card N : k)) (ψ : N →* kˣ) :
    ∑ x ∈ Finset.univ.filter (fun g : G => g ∉ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2) =
        (Nat.card N : k) * (2 * (ψ ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ : k)) := by
  set z : N := ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ with hzdef
  -- `ψ z` is a square root of `1`, so the character is `2 ψ z` at every outside square.
  have hzsq : z ^ 2 = 1 :=
    Subtype.ext (by
      simpa using sq_sq_eq_one_of_conj_eq_inv (Subgroup.sq_mem_of_index_two hindex s) hinv)
  have hψz : (ψ z)⁻¹ = ψ z :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← map_pow, hzsq, map_one])
  have houterStep : ∀ x ∈ Finset.univ.filter (fun g : G => g ∉ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2) =
        2 * (ψ z : k) := by
    intro x hx
    rw [sq_eq_sq_of_notMem_of_index_two hindex hs hinv (Finset.mem_filter.mp hx).2]
    rw [FDRep.character_ρ,
      character_indFDRep_ofLinearCharacter_eq_add_inv_of_mem_of_conj_eq_inv hindex hs hinv hN ψ
        (Subgroup.sq_mem_of_index_two hindex s), ← hzdef, hψz, two_mul]
  rw [Finset.sum_congr rfl houterStep, Finset.sum_const, nsmul_eq_mul,
    card_filter_notMem_eq_card_of_index_two hindex]

/-- **The Frobenius-Schur indicator of a character induced from an inverted subgroup of index
two** is the value of the character on the common square `s ^ 2` of the elements outside the
subgroup.  The hypothesis `ψ ^ 2 ≠ 1` says that `ψ` is not its own inverse, and `hG` that the order
of `G` is invertible in `k`.  That `s` lies outside `N` need not be assumed, being already a
consequence of those two hypotheses. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv
    [Fintype G] (hindex : N.index = 2) {s : G} (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹)
    (hG : IsUnit (Nat.card G : k)) {ψ : N →* kˣ} (hψ : ψ ^ 2 ≠ 1) :
    FDRep.frobeniusSchurIndicator (indFDRep (FDRep.ofLinearCharacter ψ)) =
      (ψ ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ : k) := by
  classical
  -- `s` lies outside `N`: an inverting element inside `N` would force `ψ ^ 2 = 1`.
  have hs : s ∉ N := fun hsN => hψ (monoidHom_sq_eq_one_of_mem_of_conj_eq_inv hsN hinv ψ)
  have hcast : (Nat.card G : k) = (Nat.card N : k) * 2 := by
    rw [← Subgroup.card_mul_index N, hindex]; push_cast; ring
  have hNunit : IsUnit (Nat.card N : k) := isUnit_of_mul_isUnit_left (hcast ▸ hG)
  -- `|G| = 2 |N|` turns the two halves into a single multiple of `|G|`, which the average cancels.
  rw [FDRep.frobeniusSchurIndicator_def, Representation.frobeniusSchurIndicator_def,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : G => g ∈ N),
    sum_filter_mem_character_ρ_indFDRep_sq_eq_zero hindex hs hinv hNunit hψ,
    sum_filter_notMem_character_ρ_indFDRep_sq hindex hs hinv hNunit ψ, zero_add,
    inv_mul_eq_iff_eq_mul₀ hG.ne_zero, hcast, mul_assoc]

end TauCeti
