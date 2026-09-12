/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.Induction.IndexTwo
public import TauCeti.RepresentationTheory.Induction.Mackey.Dihedral

/-!
# The Frobenius-Schur indicator of a character induced from an index-two subgroup

Let `N` be a subgroup of index two in a finite group `G` on which every outside element acts by
inversion, `s * x * s⁻¹ = x⁻¹`, and let `ψ` be a linear character of `N` that is not its own
inverse.  Inducing `ψ` gives a two-dimensional representation of `G`, and this file computes its
**Frobenius-Schur indicator**: it is `ψ (s ^ 2)`, the value of `ψ` on the common square of the
elements outside `N`.

The computation is a one-line reading of the character formula
`TauCeti.character_indFDRep_ofLinearCharacter_of_conj_eq_inv`, once two elementary observations
about the outside coset are in place.  All the squares in `G` lie in `N`, since the index is two,
and every element outside `N` has the *same* square: writing an outside element as `s * n`, the
inversion property turns `n * s` into `s * n⁻¹` and the two copies of `n` cancel.  That common
square is moreover an involution -- conjugating it by `s` fixes it and inverts it at once -- so `ψ`
sends it to a square root of `1`, and the character of the induced representation takes the value
`2 ψ (s ^ 2)` at every element outside `N`.

The other half of the group contributes nothing: at `g ∈ N` the character of the induced
representation at `g ^ 2` is `ψ² (g) + (ψ²)⁻¹ (g)`, and `ψ² ≠ 1` is exactly the hypothesis that
makes `Ind ψ` irreducible, so both sums vanish by the orthogonality of a nontrivial character with
the trivial one (`sum_hom_units_eq_zero`).  What is left is `|N|` copies of `2 ψ (s ^ 2)`, and
`|G| = 2 |N|`.

The worked example at the end is the two-dimensional irreducible of `D₄`, induced from the faithful
character of the rotation subgroup sending `r 1` to `i` in
`TauCeti/RepresentationTheory/Induction/Mackey/Dihedral.lean`.  A reflection squares to the
identity, so its indicator is `1`: `D₄` is of **orthogonal** type, and its two-dimensional
irreducible carries a nonzero invariant symmetric form.  This is the half of the roadmap's
`D₄`/`Q₈` comparison that the dihedral machinery already in place makes available; the general
theorem below is what reads either group's indicator off the square of an outside element.

## Main statements

* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv`: **the indicator of
  the representation induced from a linear character of an inverted subgroup of index two is the
  value of the character on the common square of the outside elements.**
* `TauCeti.sq_eq_sq_of_notMem_of_index_two`: the elements outside such a subgroup all have the same
  square, and `TauCeti.sq_sq_eq_one_of_notMem_of_index_two`: that square is an involution.
* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`:
  **the two-dimensional irreducible of `D₄` has Frobenius-Schur indicator `1`**, so it is of
  orthogonal type.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7 and its worked example "Frobenius-Schur type".
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

universe v

variable {G : Type v} [Group G] {N : Subgroup G}

/-- **All the elements outside an inverted subgroup of index two have the same square.**  An
outside element is `s * n` with `n ∈ N`, the inversion property rewrites `n * s` as `s * n⁻¹`, and
the two copies of `n` cancel. -/
theorem sq_eq_sq_of_notMem_of_index_two (hindex : N.index = 2)
    (hinv : ∀ s : G, s ∉ N → ∀ x : G, x ∈ N → s * x * s⁻¹ = x⁻¹) {s g : G} (hs : s ∉ N)
    (hg : g ∉ N) : g ^ 2 = s ^ 2 := by
  have hsinv : s⁻¹ ∉ N := fun h => hs (by simpa using N.inv_mem h)
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ∈ N ∧ g = s * n :=
    ⟨s⁻¹ * g, by rw [Subgroup.mul_mem_iff_of_index_two hindex]; exact iff_of_false hsinv hg,
      by group⟩
  have hconj : s⁻¹ * n * s = n⁻¹ := by simpa using hinv s⁻¹ hsinv n hn
  have hns : n * s = s * n⁻¹ := by rw [← hconj]; group
  rw [pow_two, pow_two]
  calc s * n * (s * n) = s * (n * s) * n := by group
    _ = s * (s * n⁻¹) * n := by rw [hns]
    _ = s * s := by group

/-- **The common square of the elements outside an inverted subgroup of index two is an
involution.**  Conjugating `s ^ 2` by `s` leaves it fixed, and inverts it because `s` lies outside
the subgroup. -/
theorem sq_sq_eq_one_of_notMem_of_index_two (hindex : N.index = 2)
    (hinv : ∀ s : G, s ∉ N → ∀ x : G, x ∈ N → s * x * s⁻¹ = x⁻¹) {s : G} (hs : s ∉ N) :
    (s ^ 2) ^ 2 = 1 := by
  have hfix : s ^ 2 = (s ^ 2)⁻¹ := by
    rw [← hinv s hs (s ^ 2) (Subgroup.sq_mem_of_index_two hindex s)]
    group
  rw [pow_two]
  nth_rewrite 2 [hfix]
  exact mul_inv_cancel _

variable {k : Type} [Field k]

/-- **The Frobenius-Schur indicator of a character induced from an inverted subgroup of index
two** is the value of the character on the common square of the elements outside the
subgroup.  The hypothesis `ψ ^ 2 ≠ 1` is the Mackey irreducibility criterion for such a subgroup;
it is what makes the contribution of `N` itself vanish. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv [Fintype G]
    (hindex : N.index = 2) (hinv : ∀ s : G, s ∉ N → ∀ x : G, x ∈ N → s * x * s⁻¹ = x⁻¹)
    (hG : IsUnit (Nat.card G : k)) {ψ : N →* kˣ} (hψ : ψ ^ 2 ≠ 1) {s : G} (hs : s ∉ N) :
    FDRep.frobeniusSchurIndicator (indFDRep (FDRep.ofLinearCharacter ψ)) =
      (ψ ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ : k) := by
  classical
  have hcast : (Nat.card G : k) = (Nat.card N : k) * 2 := by
    rw [← Subgroup.card_mul_index N, hindex]; push_cast; ring
  have hNunit : IsUnit (Nat.card N : k) := isUnit_of_mul_isUnit_left (hcast ▸ hG)
  set z : N := ⟨s ^ 2, Subgroup.sq_mem_of_index_two hindex s⟩ with hzdef
  -- `ψ z` is a square root of `1`, so the character of the induced representation is `2 ψ z` off
  -- the subgroup.
  have hzsq : z ^ 2 = 1 :=
    Subtype.ext (by simpa using sq_sq_eq_one_of_notMem_of_index_two hindex hinv hs)
  have hψz : (ψ z)⁻¹ = ψ z :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← map_pow, hzsq, map_one])
  have hbridge : ∀ (V : FDRep k G) (g : G), Representation.character V.ρ g = V.character g :=
    fun _ _ => rfl
  have hval : ∀ (g : G) (hg : g ∈ N),
      Representation.character (indFDRep (FDRep.ofLinearCharacter ψ)).ρ g =
        (ψ ⟨g, hg⟩ : k) + ((ψ ⟨g, hg⟩)⁻¹ : kˣ) := fun g hg => by
    rw [hbridge]
    exact character_indFDRep_ofLinearCharacter_of_conj_eq_inv hindex hinv hNunit ψ hg
  -- The half of `G` inside `N` contributes the sum of the nontrivial character `ψ ^ 2` and of its
  -- inverse, both of which vanish.
  have hzeroSum : ∀ χ : N →* kˣ, χ ≠ 1 → ∑ x : N, (χ x : k) = 0 := by
    intro χ hχ
    refine sum_hom_units_eq_zero ((Units.coeHom k).comp χ) fun hcontra => hχ ?_
    exact MonoidHom.ext fun x => Units.ext (congrFun (congrArg DFunLike.coe hcontra) x)
  have hinvψ : (ψ ^ 2)⁻¹ ≠ 1 := by
    intro hc
    refine hψ (MonoidHom.ext fun x => ?_)
    have hx : ((ψ ^ 2) x)⁻¹ = 1 := congrFun (congrArg DFunLike.coe hc) x
    simpa using hx
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
      rw [sq_eq_sq_of_notMem_of_index_two hindex hinv hs (by simpa using hx),
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
  rw [FDRep.frobeniusSchurIndicator_def, Representation.frobeniusSchurIndicator_def,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : G => g ∈ N), hinner, houter,
    zero_add, show (Nat.card N : k) * (2 * (ψ z : k)) = (Nat.card G : k) * (ψ z : k) by
      rw [hcast]; ring,
    ← mul_assoc, inv_mul_cancel₀ hG.ne_zero, one_mul]

/-- **The two-dimensional irreducible representation of `D₄` has Frobenius-Schur indicator `1`.**
It is induced from the faithful character of the rotation subgroup sending `r 1` to `i`, and every
reflection squares to the identity, so the general formula returns the value of that character at
`1`.  `D₄` is therefore of orthogonal type: its two-dimensional irreducible carries a nonzero
invariant symmetric form. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar :
    FDRep.frobeniusSchurIndicator
      (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)) = 1 := by
  have hcard : (Nat.card (DihedralGroup 4) : ℂ) = 8 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]; norm_num
  have hψ : dihedralGroupFourRotationChar ^ 2 ≠ 1 := fun hcontra => by
    have h := congrFun (congrArg DFunLike.coe hcontra)
      (⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩ : dihedralRotations 4)
    rw [MonoidHom.one_apply] at h
    have hI : Complex.I ^ 2 = 1 := by
      rw [← coe_dihedralGroupFourRotationChar_r_one, ← Units.val_pow_eq_pow_val]
      simpa using congrArg (fun u : ℂˣ => (u : ℂ)) h
    rw [Complex.I_sq] at hI
    exact absurd hI (by norm_num)
  have hsq : (DihedralGroup.sr (0 : ZMod 4)) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr]; simp
  rw [frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv
    (index_dihedralRotations 4) (fun _ hs _ hx => conj_eq_inv_of_notMem_dihedralRotations hs hx)
    (isUnit_iff_ne_zero.mpr (by rw [hcard]; norm_num)) hψ (sr_notMem_dihedralRotations 0)]
  rw [show (⟨(DihedralGroup.sr (0 : ZMod 4)) ^ 2,
      Subgroup.sq_mem_of_index_two (index_dihedralRotations 4) _⟩ : dihedralRotations 4) = 1 from
    Subtype.ext hsq, map_one, Units.val_one]

end TauCeti
