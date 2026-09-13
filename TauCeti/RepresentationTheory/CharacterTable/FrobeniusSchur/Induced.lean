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
by inversion, `s * x * s⁻¹ = x⁻¹`, and let `ψ` be a linear character of `N` that is not its own
inverse.  Inducing `ψ` gives a two-dimensional representation of `G`, and this file computes its
**Frobenius-Schur indicator**: it is `ψ (s ^ 2)`, the value of `ψ` on the common square of the
elements outside `N`.

This is the shape of a dihedral group over its rotations and of a dicyclic group over its cyclic
subgroup, so for such a group the indicator of an induced linear character is read off the square
of a single element outside the subgroup; the dihedral instance is in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Dihedral.lean`.

The computation reads the character formula
`TauCeti.character_indFDRep_ofLinearCharacter_of_conj_eq_inv` against the two elementary facts
about the outside coset recorded in `TauCeti/GroupTheory/IndexTwo.lean`: its elements all have the
same square (`TauCeti.sq_eq_sq_of_notMem_of_index_two`), and that square is an involution
(`TauCeti.sq_sq_eq_one_of_conj_eq_inv`).  Inside `N` the character of the induced representation
at `g ^ 2` is `ψ² (g) + (ψ²)⁻¹ (g)`, and `ψ ^ 2 ≠ 1` makes both of those characters nontrivial, so
their sums over `N` vanish (`sum_hom_units_eq_zero`).

## Main statements

* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv`: **the indicator of
  the representation induced from a linear character of an inverted subgroup of index two is the
  value of the character on the common square of the outside elements.**

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

universe v

variable {G : Type v} [Group G] {N : Subgroup G} {k : Type} [Field k]

/-- **The Frobenius-Schur indicator of a character induced from an inverted subgroup of index
two** is the value of the character on the common square `s ^ 2` of the elements outside the
subgroup.  The hypothesis `ψ ^ 2 ≠ 1` says that `ψ` is not its own inverse, and `hG` that the order
of `G` is invertible in `k`.  That `s` lies outside `N` need not be assumed: inside `N` the
inversion hypothesis would make `ψ` its own inverse. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv [Fintype G]
    (hindex : N.index = 2) {s : G} (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹)
    (hG : IsUnit (Nat.card G : k)) {ψ : N →* kˣ} (hψ : ψ ^ 2 ≠ 1) :
    FDRep.frobeniusSchurIndicator (indFDRep (FDRep.ofLinearCharacter ψ)) =
      (ψ ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ : k) := by
  classical
  -- `s` lies outside `N`: inside it, `hinv` would make `ψ` its own inverse, because `kˣ` is
  -- commutative, and that is what `hψ` forbids.
  have hs : s ∉ N := by
    intro hsN
    refine hψ (MonoidHom.ext fun x => ?_)
    have hconj : (⟨s, hsN⟩ : N) * x * (⟨s, hsN⟩ : N)⁻¹ = x⁻¹ :=
      Subtype.ext (by simpa using hinv (x : G) x.2)
    have hfix : ψ x = (ψ x)⁻¹ := by
      have h := congrArg ψ hconj
      simp only [map_mul, map_inv] at h
      rwa [mul_comm (ψ (⟨s, hsN⟩ : N)) (ψ x), mul_inv_cancel_right] at h
    have hsq : ψ x * ψ x = 1 := by
      have hrewrite : ψ x * ψ x = ψ x * (ψ x)⁻¹ := by rw [← hfix]
      rw [hrewrite, mul_inv_cancel]
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, pow_two, hsq]
  have hcast : (Nat.card G : k) = (Nat.card N : k) * 2 := by
    rw [← Subgroup.card_mul_index N, hindex]; push_cast; ring
  have hNunit : IsUnit (Nat.card N : k) := isUnit_of_mul_isUnit_left (hcast ▸ hG)
  set z : N := ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ with hzdef
  -- `ψ z` is a square root of `1`, so the character of the induced representation is `2 ψ z` off
  -- the subgroup.
  have hzsq : z ^ 2 = 1 :=
    Subtype.ext (by
      simpa using sq_sq_eq_one_of_conj_eq_inv (Subgroup.sq_mem_of_index_two hindex s) hinv)
  have hψz : (ψ z)⁻¹ = ψ z :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← map_pow, hzsq, map_one])
  have hval : ∀ (g : G) (hg : g ∈ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ g =
        (ψ ⟨g, hg⟩ : k) + ((ψ ⟨g, hg⟩)⁻¹ : kˣ) := fun g hg => by
    -- `FDRep.character_forget₂_obj` is the explicit bridge between the two character interfaces.
    -- It is stated for the representation carried by `forget₂`, the one `FDRep.forget₂_ρ`
    -- identifies with `V.ρ`; rewriting along that identification is not an option here, because
    -- the motive is ill-typed while `indFDRep` is not `@[expose]`d.
    have hbridge : Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ g =
        (indFDRep (FDRep.ofLinearCharacter ψ)).character g :=
      FDRep.character_forget₂_obj _ g
    rw [hbridge]
    exact character_indFDRep_ofLinearCharacter_of_conj_eq_inv hindex hs hinv hNunit ψ hg
  -- The half of `G` inside `N` contributes the sum of the nontrivial character `ψ ^ 2` and of its
  -- inverse, both of which vanish.
  have hzeroSum : ∀ χ : N →* kˣ, χ ≠ 1 → ∑ x : N, (χ x : k) = 0 := by
    intro χ hχ
    refine sum_hom_units_eq_zero ((Units.coeHom k).comp χ) fun hcontra => hχ ?_
    exact MonoidHom.ext fun x => Units.ext (congrFun (congrArg DFunLike.coe hcontra) x)
  -- The `Inv` on `N →* kˣ` is `MonoidHom.instInv`, so `inv_ne_one` needs its argument
  -- pinned before the `DivisionMonoid` instance it is stated for can be found.
  have hinvψ : (ψ ^ 2)⁻¹ ≠ 1 := (inv_ne_one (a := ψ ^ 2)).mpr hψ
  have hstep : ∀ x : N,
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ
          ((x : G) ^ 2) = (((ψ ^ 2) x : kˣ) : k) + ((((ψ ^ 2)⁻¹) x : kˣ) : k) := by
    intro x
    rw [hval ((x : G) ^ 2) (Subgroup.sq_mem_of_index_two hindex _)]
    have hx : (⟨(x : G) ^ 2, Subgroup.sq_mem_of_index_two hindex (x : G)⟩ : N) = x ^ 2 :=
      Subtype.ext (by simp)
    rw [hx]
    simp
  have hinner : ∑ x ∈ Finset.univ.filter (fun g : G => g ∈ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2)
        = 0 := by
    have hsub : ∑ x ∈ Finset.univ.filter (fun g : G => g ∈ N),
        Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2)
          = ∑ x : N, Representation.character
              (indFDRep (FDRep.ofLinearCharacter ψ)).ρ ((x : G) ^ 2) :=
      Finset.sum_subtype _ (fun x => by simp) _
    rw [hsub, Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_add_distrib,
      hzeroSum _ hψ, hzeroSum _ hinvψ, add_zero]
  -- The other half contributes `|N|` copies of `2 ψ z`.
  have houter : ∑ x ∈ Finset.univ.filter (fun g : G => ¬ g ∈ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2) =
        (Nat.card N : k) * (2 * (ψ z : k)) := by
    have houterStep : ∀ x ∈ Finset.univ.filter (fun g : G => ¬ g ∈ N),
        Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ (x ^ 2) =
          2 * (ψ z : k) := by
      intro x hx
      rw [sq_eq_sq_of_notMem_of_index_two hindex hs hinv (by simpa using hx),
        hval (s ^ 2) (Subgroup.sq_mem_of_index_two hindex s), ← hzdef, hψz]
      ring
    rw [Finset.sum_congr rfl houterStep, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x : G => x ∈ N)
    have hmemCard : (Finset.univ.filter (fun x : G => x ∈ N)).card = Nat.card N := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcard : (Finset.univ : Finset G).card = Nat.card N * 2 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.card_mul_index N, hindex]
    have : (Finset.univ.filter (fun x : G => ¬ x ∈ N)).card = Nat.card N := by omega
    rw [this]
  -- `|G| = 2 |N|` turns the two halves into a single multiple of `|G|`, which the average cancels.
  have hcollect : (Nat.card N : k) * (2 * (ψ z : k)) = (Nat.card G : k) * (ψ z : k) := by
    rw [hcast]; ring
  rw [FDRep.frobeniusSchurIndicator_def, Representation.frobeniusSchurIndicator_def,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : G => g ∈ N), hinner, houter,
    zero_add, hcollect, ← mul_assoc, inv_mul_cancel₀ hG.ne_zero, one_mul]

end TauCeti
