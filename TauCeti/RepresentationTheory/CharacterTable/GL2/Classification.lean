/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Linear`, `TauCeti.GL2SteinbergTwist`, their values, their irreducibility and their
-- membership in `TauCeti.irreducibleCharacters`.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Boundary
-- `TauCeti.GL2PrincipalSeries`: irreducibility, membership in `TauCeti.irreducibleCharacters`, and
-- the parametrisation by unordered pairs.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Parameters
-- `TauCeti.GL2CuspidalVirtualCharacter`, its values and its irreducibility.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Irreducible
-- Non-public: `TauCeti.card_conjClasses_GL2` counts the conjugacy classes of `GL₂(𝔽_q)`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: `FDRep.nonempty_iso_of_character_eq` recovers an isomorphism from a character
-- identity.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- Non-public: the character group of a finite commutative group is a `Fintype`.
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
-- Non-public: `ℂ`, being algebraically closed, has enough roots of unity of every order, so the
-- character group of the unit group of a finite field has the order of the unit group.
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- Non-public: `Nat.card E = q ^ 2` for the degree-`2` extension `E/F`.
import Mathlib.FieldTheory.Finiteness
-- Non-public: at most `n - 1` characters of a finite cyclic group are fixed by the `n`-th power
-- map.
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Dual

/-!
# The irreducible characters of `GL₂(𝔽_q)`

Let `F` be a finite field with `q` elements and `E/F` a degree-`2` extension. This file proves
that the four families of irreducible characters of `GL₂(F)` constructed in the surrounding files
exhaust the irreducible characters of `GL₂(F)`:

* the `q - 1` **linear** characters `α ∘ det` (`TauCeti.GL2Linear`), of degree `1`;
* the `q - 1` **Steinberg twists** `(α ∘ det) ⊗ St` (`TauCeti.GL2SteinbergTwist`), of degree `q`;
* the **principal series** `Ind_B^{GL₂}(α ⊗ β)` with `α ≠ β` (`TauCeti.GL2PrincipalSeries`), of
  degree `q + 1`, parametrised by the unordered pairs `{α, β}`;
* the **cuspidal** characters attached to the characters `θ` of `Eˣ` with `θ^q ≠ θ`
  (`TauCeti.GL2CuspidalVirtualCharacter`), of degree `q - 1`, parametrised by the orbits
  `{θ, θ^q}`.

The proof is a count. The four families are pairwise disjoint, since their members differ in
degree or in their value at the unipotent Jordan block `!![1, 1; 0, 1]`, and the within-family
identifications (`TauCeti.GL2Linear_character_injective`,
`TauCeti.GL2SteinbergTwist_character_injective`, `TauCeti.nonempty_iso_GL2PrincipalSeries_iff`
and `TauCeti.GL2CuspidalVirtualCharacter_eq_iff`) give the four families exactly `q - 1`,
`q - 1` and `½ (q - 1) (q - 2)` members and at least `½ q (q - 1)` members respectively, whose
sum is `q² - 1`. That is the number of conjugacy classes of `GL₂(F)`
(`TauCeti.card_conjClasses_GL2`), hence the number of irreducible characters
(`TauCeti.card_irreducibleCharacters`), so nothing is missing; and the cuspidal family then has
exactly `½ q (q - 1)` members.

The cuspidal bound uses that at most `q - 1` characters of `Eˣ` are fixed by `θ ↦ θ^q`
(`IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le`, as `Eˣ` is cyclic), and that the character
group of `Eˣ` has order `q² - 1` (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`).

The membership of the four families in `TauCeti.irreducibleCharacters` is recorded beside their
irreducibility: `TauCeti.character_GL2Linear_mem_irreducibleCharacters`,
`TauCeti.character_GL2SteinbergTwist_mem_irreducibleCharacters`,
`TauCeti.character_GL2PrincipalSeries_mem_irreducibleCharacters` and
`TauCeti.GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`.

## Main results

* `TauCeti.character_GL2Linear_ne_character_GL2SteinbergTwist` and its five companions: the four
  families are pairwise disjoint.
* `TauCeti.ncard_range_character_GL2Linear`, `TauCeti.ncard_range_character_GL2SteinbergTwist`,
  `TauCeti.ncard_image_character_GL2PrincipalSeries` and
  `TauCeti.ncard_image_GL2CuspidalVirtualCharacter`: the four families have `q - 1`, `q - 1`,
  `½ (q - 1) (q - 2)` and `½ q (q - 1)` members.
* `TauCeti.irreducibleCharacters_GL2_eq_union`: **the irreducible characters of `GL₂(F)` are
  exactly the linear, Steinberg-twist, principal-series and cuspidal characters.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §§4–5.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

universe u

/-! ### The four families are pairwise disjoint

Three of the six comparisons are made at the unipotent Jordan block `!![1, 1; 0, 1]`, where the
linear characters take the value `1`, the Steinberg twists `0` and the cuspidal characters `-1`;
the other three, those involving the principal series, are made at the identity, where the degrees
`1`, `q`, `q + 1` and `q - 1` differ. -/

section Distinct

variable {F : Type u} [Field F] [Fintype F]

/-- A linear character is not a Steinberg twist: at the Jordan block they take the values `1`
and `0`. -/
theorem character_GL2Linear_ne_character_GL2SteinbergTwist (α β : Fˣ →* ℂˣ) :
    (GL2Linear F α).character ≠ (GL2SteinbergTwist F β).character := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2Linear_jordanGL, character_GL2SteinbergTwist_jordanGL β 1 one_ne_zero] at this
  simp at this

/-- A linear character is not a principal-series character: their degrees are `1` and `q + 1`. -/
theorem character_GL2Linear_ne_character_GL2PrincipalSeries (α β γ : Fˣ →* ℂˣ) :
    (GL2Linear F α).character ≠ (GL2PrincipalSeries F β γ).character := by
  intro h
  have h1 := congrFun h 1
  rw [FDRep.char_one, finrank_GL2Linear, character_one_GL2PrincipalSeries] at h1
  have := Fintype.card_pos (α := F)
  norm_cast at h1
  omega

/-- A Steinberg twist is not a principal-series character: their degrees are `q` and `q + 1`. -/
theorem character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries (α β γ : Fˣ →* ℂˣ) :
    (GL2SteinbergTwist F α).character ≠ (GL2PrincipalSeries F β γ).character := by
  intro h
  have := congrFun h 1
  rw [FDRep.char_one, finrank_GL2SteinbergTwist, character_one_GL2PrincipalSeries] at this
  norm_cast at this
  omega

variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- A linear character is not a cuspidal character: at the Jordan block they take the values `1`
and `-1`. -/
theorem character_GL2Linear_ne_GL2CuspidalVirtualCharacter (α : Fˣ →* ℂˣ) (θ : Eˣ →* ℂˣ)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (GL2Linear F α).character ≠ (GL2CuspidalVirtualCharacter F E θ ψ).1 := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2Linear_jordanGL,
    GL2CuspidalVirtualCharacter_apply_jordanGL θ hψ 1 one_ne_zero] at this
  norm_num at this

/-- A Steinberg twist is not a cuspidal character: at the Jordan block they take the values `0`
and `-1`. -/
theorem character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter (α : Fˣ →* ℂˣ)
    (θ : Eˣ →* ℂˣ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (GL2SteinbergTwist F α).character ≠ (GL2CuspidalVirtualCharacter F E θ ψ).1 := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2SteinbergTwist_jordanGL α 1 one_ne_zero,
    GL2CuspidalVirtualCharacter_apply_jordanGL θ hψ 1 one_ne_zero] at this
  norm_num at this

/-- A principal-series character is not a cuspidal character: their degrees are `q + 1` and
`q - 1`. -/
theorem character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter (α β : Fˣ →* ℂˣ)
    (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2PrincipalSeries F α β).character ≠ (GL2CuspidalVirtualCharacter F E θ ψ).1 := by
  intro h
  have := congrFun h 1
  rw [character_one_GL2PrincipalSeries, GL2CuspidalVirtualCharacter_apply_one] at this
  have h2 : (2 : ℂ) = 0 := by linear_combination this
  norm_num at h2

end Distinct

/-! ### The sizes of the four families

The linear characters and the Steinberg twists are counted by their parameters `α`, `q - 1` each.
The principal series are counted by the unordered pairs `{α, β}` with `α ≠ β`: the fibres of
`(α, β) ↦ χ(Ind_B(α ⊗ β))` on the off-diagonal pairs are exactly the two orders of a pair. The
cuspidal family is bounded below by the orbits `{θ, θ^q}` of the characters `θ` of `Eˣ` with
`θ^q ≠ θ`; its exact size is a consequence of the classification, recorded after it. -/

section Count

section Parameters

variable (F : Type u) [Field F] [Fintype F]

/-- **There are `q - 1` linear characters of `GL₂(F)`**, one for each `α : Fˣ →* ℂˣ`. -/
@[simp]
theorem ncard_range_character_GL2Linear :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character).ncard = Fintype.card F - 1 := by
  rw [Set.ncard_range_of_injective GL2Linear_character_injective,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units, Nat.card_eq_fintype_card]

/-- **There are `q - 1` Steinberg twists of `GL₂(F)`**, one for each `α : Fˣ →* ℂˣ`. -/
@[simp]
theorem ncard_range_character_GL2SteinbergTwist :
    (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character).ncard =
      Fintype.card F - 1 := by
  rw [Set.ncard_range_of_injective GL2SteinbergTwist_character_injective,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units, Nat.card_eq_fintype_card]

end Parameters

variable (F : Type) [Field F] [Fintype F]

open Classical in
/-- The fibre of `(α, β) ↦ χ(Ind_B(α ⊗ β))` on the off-diagonal pairs through `(α, β)` is exactly
`{(α, β), (β, α)}`: the two orders of a pair give isomorphic principal series, and nothing else
does. -/
private theorem filter_character_GL2PrincipalSeries_eq {α β : Fˣ →* ℂˣ} (hαβ : α ≠ β) :
    ((Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag.filter
      fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) =>
        (GL2PrincipalSeries F p.1 p.2).character = (GL2PrincipalSeries F α β).character) =
      {(α, β), (β, α)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨-, hp⟩
    obtain ⟨e⟩ := FDRep.nonempty_iso_of_character_eq _ _ hp
    rcases (nonempty_iso_GL2PrincipalSeries_iff F).mp ⟨e⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  · rintro (rfl | rfl)
    · exact ⟨hαβ, rfl⟩
    · refine ⟨hαβ.symm, FDRep.char_iso ?_⟩
      exact ((nonempty_iso_GL2PrincipalSeries_iff F).mpr (Or.inr ⟨rfl, rfl⟩)).some

/-- **There are `½ (q - 1) (q - 2)` principal-series characters of `GL₂(F)`**, one for each
unordered pair `{α, β}` of distinct characters of `Fˣ`. -/
@[simp]
theorem ncard_image_character_GL2PrincipalSeries :
    ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
      {p | p.1 ≠ p.2}).ncard = (Fintype.card F - 1) * (Fintype.card F - 2) / 2 := by
  classical
  set fP : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) → (GL (Fin 2) F → ℂ) :=
    fun p => (GL2PrincipalSeries F p.1 p.2).character
  -- the off-diagonal pairs as a finset
  have hoff : ({p | p.1 ≠ p.2} : Set ((Fˣ →* ℂˣ) × (Fˣ →* ℂˣ))) =
      ↑(Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag := by
    ext p
    simp
  rw [hoff, ← Finset.coe_image, Set.ncard_coe_finset]
  -- every fibre of `fP` on the off-diagonal pairs has exactly two elements
  set s : Finset ((Fˣ →* ℂˣ) × (Fˣ →* ℂˣ)) := (Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag with hs
  have hfib : ∀ f ∈ s.image fP, (s.filter (fP · = f)).card = 2 := by
    intro f hf
    obtain ⟨⟨α, β⟩, hαβ, rfl⟩ := Finset.mem_image.mp hf
    have hne : α ≠ β := (Finset.mem_offDiag.mp hαβ).2.2
    rw [hs, filter_character_GL2PrincipalSeries_eq F hne]
    exact Finset.card_pair fun h => hne (congrArg Prod.fst h)
  have hcard : s.card = (s.image fP).card * 2 := by
    rw [Finset.card_eq_sum_card_image fP, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  rw [hs] at hcard
  rw [Finset.offDiag_card, Finset.card_univ, ← Nat.card_eq_fintype_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units,
    Nat.card_eq_fintype_card] at hcard
  -- the arithmetic: `(q - 1) (q - 1) - (q - 1) = (q - 1) (q - 2)`
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 :=
    ⟨Fintype.card F - 2, by have := Fintype.one_lt_card (α := F); omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  have h3 : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hm, h1, h3] at hcard
  rw [hm, h1, h2, hcard, Nat.mul_div_cancel _ two_pos]

end Count

/-! ### The classification -/

section Classification

variable (F : Type) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

open Classical in
/-- Two cuspidal parameters giving the same character lie in one orbit `{θ, θ^q}`, so each fibre
of `θ ↦ χ_θ` has at most two elements. -/
private theorem card_filter_GL2CuspidalVirtualCharacter_le {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (s : Finset (Eˣ →* ℂˣ))
    {f : GL (Fin 2) F → ℂ}
    (hf : f ∈ s.image fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) :
    (s.filter fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1 = f).card ≤ 2 := by
  obtain ⟨θ₀, -, rfl⟩ := Finset.mem_image.mp hf
  refine (Finset.card_le_card ?_).trans
    (Finset.card_le_two (a := θ₀) (b := θ₀.comp (powMonoidHom (Fintype.card F))))
  intro θ hθ
  obtain ⟨-, hθ⟩ := Finset.mem_filter.mp hθ
  rcases (GL2CuspidalVirtualCharacter_eq_iff θ₀ θ hψ hψ).mp (Subtype.ext hθ).symm with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))

/-- **The cuspidal family has at least `½ q (q - 1)` members**, in the form
`q² - 1 ≤ 2 · #cuspidal + (q - 1)`: the character group of `Eˣ` has `q² - 1` elements, at most
`q - 1` of them are fixed by `θ ↦ θ^q`, and `θ ↦ χ_θ` is at most two-to-one on the rest. -/
private theorem le_two_mul_ncard_image_GL2CuspidalVirtualCharacter {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) :
    Fintype.card F ^ 2 - 1 ≤
      2 * ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
        {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard + (Fintype.card F - 1) := by
  classical
  have : Finite E := Module.finite_of_finite F
  set sC : Finset (Eˣ →* ℂˣ) :=
    Finset.univ.filter fun θ : Eˣ →* ℂˣ => ¬ θ.comp (powMonoidHom (Fintype.card F)) = θ with hsC
  have hs : ({θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ} : Set (Eˣ →* ℂˣ)) = ↑sC := by
    ext θ
    simp [hsC]
  rw [hs, ← Finset.coe_image, Set.ncard_coe_finset]
  have hcardC : sC.card ≤ 2 * (sC.image fun θ : Eˣ →* ℂˣ =>
      (GL2CuspidalVirtualCharacter F E θ ψ).1).card :=
    Finset.card_le_mul_card_image _ 2 fun f hf =>
      card_filter_GL2CuspidalVirtualCharacter_le F E hψ sC hf
  -- the character group of `Eˣ` has `q² - 1` elements
  have hsC' : (Finset.univ.filter fun θ : Eˣ →* ℂˣ =>
      θ.comp (powMonoidHom (Fintype.card F)) = θ).card + sC.card = Fintype.card F ^ 2 - 1 := by
    rw [hsC, Finset.card_filter_add_card_filter_not, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units,
      Module.natCard_eq_pow_finrank (K := F), Algebra.IsQuadraticExtension.finrank_eq_two F E,
      Nat.card_eq_fintype_card]
  -- at most `q - 1` of them are fixed by `θ ↦ θ^q`
  have hfix : (Finset.univ.filter fun θ : Eˣ →* ℂˣ =>
      θ.comp (powMonoidHom (Fintype.card F)) = θ).card ≤ Fintype.card F - 1 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le Eˣ ℂ Fintype.one_lt_card
  omega

/-- The arithmetic of the count, for `q ≥ 2`: the linear, Steinberg-twist and principal-series
families account for `2 (q - 1) + ½ (q - 1) (q - 2)` of the `q² - 1` irreducible characters, and
the `½ q (q - 1)` left for the cuspidal family equal `(q - 1) + ½ (q - 1) (q - 2)`, which is what
the lower bound `q² - 1 ≤ 2 · #cuspidal + (q - 1)` of
`TauCeti.le_two_mul_ncard_image_GL2CuspidalVirtualCharacter` compares against. -/
private theorem count_arith {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 - 1 = (q - 1) + (q - 1) + (q - 1) * (q - 2) / 2 + q * (q - 1) / 2 ∧
      q * (q - 1) / 2 = (q - 1) + (q - 1) * (q - 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  have hsq : (m + 2) ^ 2 = m * m + 4 * m + 3 + 1 := by ring
  have h3 : (m + 2) ^ 2 - 1 = m * m + 4 * m + 3 := by omega
  have h4 : (m + 1) * m = m * m + m := by ring
  have h5 : 2 ∣ m * m + m := by
    rw [← h4, mul_comm]
    exact (Nat.even_mul_succ_self m).two_dvd
  have h6 : (m + 2) * (m + 1) = m * m + 3 * m + 2 := by ring
  rw [h1, h2, h3, h4, h6]
  omega

/-- The four families are pairwise disjoint, so the size of their union is the sum of their
sizes. -/
private theorem ncard_union_eq_add {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (Set.range (fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) ∪
        Set.range (fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) ∪
        (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2} ∪
        (fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard =
      (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character).ncard +
        (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character).ncard +
        ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2}).ncard +
        ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard := by
  have : Finite E := Module.finite_of_finite F
  have hAB : Disjoint (Set.range fun α : Fˣ →* ℂˣ => (GL2Linear F α).character)
      (Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) := by
    rw [Set.disjoint_left]
    rintro f ⟨α, rfl⟩ ⟨β, hβ⟩
    exact character_GL2Linear_ne_character_GL2SteinbergTwist α β hβ.symm
  have hABP : Disjoint (Set.range (fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) ∪
      Set.range fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character)
      ((fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
        {p | p.1 ≠ p.2}) := by
    rw [Set.disjoint_left]
    rintro f (⟨α, rfl⟩ | ⟨α, rfl⟩) ⟨p, -, hp⟩
    · exact character_GL2Linear_ne_character_GL2PrincipalSeries α p.1 p.2 hp.symm
    · exact character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries α p.1 p.2 hp.symm
  have hABPC : Disjoint (Set.range (fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) ∪
      Set.range (fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) ∪
      (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
        {p | p.1 ≠ p.2})
      ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
        {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}) := by
    rw [Set.disjoint_left]
    rintro f ((⟨α, rfl⟩ | ⟨α, rfl⟩) | ⟨p, -, rfl⟩) ⟨θ, -, hθ⟩
    · exact character_GL2Linear_ne_GL2CuspidalVirtualCharacter α θ hψ hθ.symm
    · exact character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter α θ hψ hθ.symm
    · exact character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter p.1 p.2 θ ψ hθ.symm
  rw [Set.ncard_union_eq hABPC, Set.ncard_union_eq hABP, Set.ncard_union_eq hAB]

/-- **The irreducible characters of `GL₂(𝔽_q)`.** For a finite field `F` with `q` elements, a
degree-`2` extension `E/F` and a nontrivial additive character `ψ` of `F`, the irreducible
characters of `GL₂(F)` are exactly the linear characters `α ∘ det`, the Steinberg twists
`(α ∘ det) ⊗ St`, the principal series `Ind_B^{GL₂}(α ⊗ β)` with `α ≠ β`, and the cuspidal
characters attached to the characters `θ` of `Eˣ` with `θ^q ≠ θ`.

The four families are pairwise disjoint, and together they have at least `q² - 1` members, the
number of conjugacy classes of `GL₂(F)`; so they exhaust the irreducible characters. -/
theorem irreducibleCharacters_GL2_eq_union {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    irreducibleCharacters ℂ (GL (Fin 2) F) =
      Set.range (fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) ∪
        Set.range (fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) ∪
        (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2} ∪
        (fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ} := by
  have : Finite E := Module.finite_of_finite F
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · -- every member of the four families is an irreducible character
    rintro f (((⟨α, rfl⟩ | ⟨α, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨θ, hθ, rfl⟩)
    · exact character_GL2Linear_mem_irreducibleCharacters α
    · exact character_GL2SteinbergTwist_mem_irreducibleCharacters F α
    · exact character_GL2PrincipalSeries_mem_irreducibleCharacters F hp
    · exact GL2CuspidalVirtualCharacter_mem_irreducibleCharacters hθ hψ
  · -- the four families together have at least `q² - 1` members
    rw [← Nat.card_coe_set_eq, card_irreducibleCharacters, card_conjClasses_GL2,
      Nat.card_eq_fintype_card, ncard_union_eq_add F E hψ, ncard_range_character_GL2Linear,
      ncard_range_character_GL2SteinbergTwist, ncard_image_character_GL2PrincipalSeries]
    have hC := le_two_mul_ncard_image_GL2CuspidalVirtualCharacter F E hψ
    -- the arithmetic: `2 (q - 1) + ½ (q - 1) (q - 2) + ½ q (q - 1) = q² - 1`
    have := count_arith (Fintype.one_lt_card (α := F))
    omega

/-- **There are `½ q (q - 1)` cuspidal characters of `GL₂(F)`**, one for each orbit `{θ, θ^q}` of
the characters `θ` of `Eˣ` with `θ^q ≠ θ`: the other three families account for
`2 (q - 1) + ½ (q - 1) (q - 2)` of the `q² - 1` irreducible characters. -/
@[simp]
theorem ncard_image_GL2CuspidalVirtualCharacter {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ((fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E θ ψ).1) ''
      {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ}).ncard =
      Fintype.card F * (Fintype.card F - 1) / 2 := by
  have h := congrArg Set.ncard (irreducibleCharacters_GL2_eq_union F E hψ)
  rw [← Nat.card_coe_set_eq, card_irreducibleCharacters, card_conjClasses_GL2,
    Nat.card_eq_fintype_card, ncard_union_eq_add F E hψ, ncard_range_character_GL2Linear,
    ncard_range_character_GL2SteinbergTwist, ncard_image_character_GL2PrincipalSeries] at h
  -- the arithmetic: `q² - 1 - 2 (q - 1) - ½ (q - 1) (q - 2) = ½ q (q - 1)`
  have := (count_arith (Fintype.one_lt_card (α := F))).1
  omega

end Classification

end TauCeti
