/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.PiLex
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.OrderIsoNat
import TauCeti.Order.WellFounded.Set

/-!
# Well-foundedness of complement-counting functions of upper sets in lexicographic order

Let `α` be a well-quasi-ordered preorder equipped with a grading `deg : α → ℕ` whose sublevel sets
`{x : α | deg x ≤ d}` are finite. For an upper set `D ⊆ α`, its complement-counting function
`ℓ ↦ {x : α | x ∉ D ∧ deg x ≤ ℓ}.ncard` records the number of elements outside `D` up to degree
`ℓ`. This file proves that the set of such functions over all upper sets `D ⊆ α` is well-founded
under the lexicographic order on `ℕ → ℕ`
(`TauCeti.wellFoundedOn_range_toLex_ncard_compl_of_isUpperSet`), so every lexicographically
nonincreasing sequence of upper-set complement-counting functions is eventually constant
(`TauCeti.exists_forall_eq_of_antitone_toLex_ncard_compl_of_isUpperSet`).

The proof follows Bierstone–Milman's diagonalization argument: given a strictly lexicographically
decreasing sequence of upper sets `D j`, pigeonhole over the finite sublevel balls `{x | deg x ≤ d}`
produces a nested sequence of infinite index sets `S d` on which `D j` stabilizes on every element
of degree at most `d`. By well-quasi-ordering, the resulting limit set `E` admits a finite
generating set `V ⊆ E` (`Set.IsPWO.exists_finset_subset_le`). For indices in `S (V.sup deg)`, every
generator lies in `D j`, forcing `E ⊆ D j` and hence a pointwise upper bound by the counting
function of `E`; a strictly later index in `S d₀` drops strictly below `E` at some least degree
`ℓ`, contradicting agreement with `E` up to degree `ℓ` on the infinite set `S ℓ`.

## Main results

* `TauCeti.not_strictAnti_toLex_ncard_compl_of_isUpperSet`: no sequence of upper sets in a
  well-quasi-ordered graded preorder has strictly lexicographically decreasing complement counts.
* `TauCeti.wellFoundedOn_range_toLex_ncard_compl_of_isUpperSet`: the realized upper-set
  complement-counting functions form a well-founded set under the lexicographic order.
* `TauCeti.exists_forall_eq_of_antitone_toLex_ncard_compl_of_isUpperSet`: every lexicographically
  nonincreasing sequence of upper-set complement-counting functions stabilizes.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), no. 4, 801–836, Theorem 5.2.1, pp. 820–821.
-/

public section

namespace TauCeti

private theorem exists_infinite_subset_agree {α : Type*} (D : ℕ → Set α) (B : Finset α)
    {S : Set ℕ} (hS : S.Infinite) :
    ∃ (S' : Set ℕ) (E : Finset α), S' ⊆ S ∧ S'.Infinite ∧
      ∀ j ∈ S', ∀ x ∈ B, x ∈ D j ↔ x ∈ E := by
  classical
  have : Infinite S := hS.to_subtype
  let f : S → B.powerset := fun j ↦
    ⟨B.filter (· ∈ D j.1), Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  obtain ⟨E, hEinf⟩ := Finite.exists_infinite_fiber f
  refine ⟨Subtype.val '' (f ⁻¹' {E}), E.1, ?_,
    (Set.infinite_coe_iff.mp hEinf).image Subtype.val_injective.injOn, ?_⟩
  · rintro _ ⟨j, -, rfl⟩
    exact j.2
  · rintro _ ⟨j, hj, rfl⟩ x hxB
    have hEq : B.filter (· ∈ D j.1) = E.1 := congrArg Subtype.val hj
    rw [← hEq, Finset.mem_filter]
    exact ⟨fun hx ↦ ⟨hxB, hx⟩, fun hx ↦ hx.2⟩

private theorem exists_antitone_infinite_agree {α : Type*} {deg : α → ℕ}
    (hfin : ∀ d, {x : α | deg x ≤ d}.Finite) (D : ℕ → Set α) :
    ∃ (S : ℕ → Set ℕ) (E : Set α), (∀ d, (S d).Infinite) ∧
      ∀ d, ∀ j ∈ S d, ∀ x, deg x ≤ d → (x ∈ D j ↔ x ∈ E) := by
  classical
  let B : ℕ → Finset α := fun d ↦ (hfin d).toFinset
  have hmemB (d : ℕ) (x : α) : x ∈ B d ↔ deg x ≤ d := (hfin d).mem_toFinset
  choose nextS nextE hnextSub hnextInf hnextAgree using
    fun (d : ℕ) (S : Set ℕ) (hS : S.Infinite) ↦ exists_infinite_subset_agree D (B d) hS
  let SE : ℕ → {q : Set ℕ × Finset α // q.1.Infinite} :=
    Nat.rec
      ⟨(nextS 0 Set.univ Set.infinite_univ, nextE 0 Set.univ Set.infinite_univ),
        hnextInf 0 Set.univ Set.infinite_univ⟩
      fun d prev ↦
        ⟨(nextS (d + 1) prev.1.1 prev.2, nextE (d + 1) prev.1.1 prev.2),
          hnextInf (d + 1) prev.1.1 prev.2⟩
  let S : ℕ → Set ℕ := fun d ↦ (SE d).1.1
  let Efin : ℕ → Finset α := fun d ↦ (SE d).1.2
  have hSinf (d : ℕ) : (S d).Infinite := (SE d).2
  have hSanti : Antitone S :=
    antitone_nat_of_succ_le fun d ↦ hnextSub (d + 1) (SE d).1.1 (SE d).2
  have hAgree (d : ℕ) : ∀ j ∈ S d, ∀ x ∈ B d, x ∈ D j ↔ x ∈ Efin d := by
    cases d with
    | zero => exact hnextAgree 0 Set.univ Set.infinite_univ
    | succ d => exact hnextAgree (d + 1) (SE d).1.1 (SE d).2
  have hcohere {d₁ d₂ : ℕ} (hle : d₁ ≤ d₂) {x : α} (hx : deg x ≤ d₁) :
      x ∈ Efin d₁ ↔ x ∈ Efin d₂ := by
    obtain ⟨j, hj⟩ := (hSinf d₂).nonempty
    exact (hAgree d₁ j (hSanti hle hj) x ((hmemB d₁ x).mpr hx)).symm.trans
      (hAgree d₂ j hj x ((hmemB d₂ x).mpr (hx.trans hle)))
  refine ⟨S, {x : α | x ∈ Efin (deg x)}, hSinf, fun d j hj x hx ↦ ?_⟩
  exact (hAgree d j hj x ((hmemB d x).mpr hx)).trans (hcohere hx le_rfl).symm

/-- In a well-quasi-ordered preorder with finite degree sublevel sets, no sequence of upper sets
has strictly lexicographically decreasing complement-counting functions. -/
theorem not_strictAnti_toLex_ncard_compl_of_isUpperSet
    {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    {deg : α → ℕ} (hfin : ∀ d, {x : α | deg x ≤ d}.Finite)
    {D : ℕ → Set α} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti fun j ↦ toLex fun ℓ ↦ {x : α | x ∉ D j ∧ deg x ≤ ℓ}.ncard := by
  classical
  intro hstrict
  let h : Set α → ℕ → ℕ := fun U ℓ ↦ {x : α | x ∉ U ∧ deg x ≤ ℓ}.ncard
  obtain ⟨S, E, hSinf, hAgreeE⟩ := exists_antitone_infinite_agree hfin D
  have hCountEq {d j r : ℕ} (hj : j ∈ S d) (hr : r ≤ d) : h (D j) r = h E r := by
    refine congrArg Set.ncard ?_
    ext x
    simp only [Set.mem_ofPred_eq]
    exact and_congr_left fun hxr ↦ not_congr (hAgreeE d j hj x (hxr.trans hr))
  -- By well-quasi-ordering, `E` has a finite generating subset `V ⊆ E`.
  obtain ⟨V, hVE, hVgen⟩ := (Set.isPWO_of_wellQuasiOrderedLE E).exists_finset_subset_le
  let d₀ : ℕ := V.sup deg
  have hEsub (j : ℕ) (hj : j ∈ S d₀) : E ⊆ D j := by
    intro x hxE
    obtain ⟨v, hvV, hvx⟩ := hVgen x hxE
    have hvdeg : deg v ≤ d₀ := Finset.le_sup (f := deg) hvV
    exact hD j hvx ((hAgreeE d₀ j hj v hvdeg).mpr (hVE hvV))
  have hleE (j : ℕ) (hj : j ∈ S d₀) : toLex (h (D j)) ≤ toLex (h E) :=
    Pi.toLex_monotone fun r ↦
      Set.ncard_le_ncard (fun x ⟨hxD, hxr⟩ ↦ ⟨fun hxE ↦ hxD (hEsub j hj hxE), hxr⟩)
        ((hfin r).subset fun _ hx ↦ hx.2)
  -- Pick `j₁ ∈ S d₀`; then `j₁ + 1` drops strictly below `toLex (h E)`.
  obtain ⟨j₁, hj₁⟩ := (hSinf d₀).nonempty
  have hltE : toLex (h (D (j₁ + 1))) < toLex (h E) :=
    (hstrict (Nat.lt_succ_self j₁)).trans_le (hleE j₁ hj₁)
  -- At the first degree `ℓ` where `h (D (j₁ + 1))` drops below `h E`, pick `k ∈ S ℓ` past it.
  obtain ⟨ℓ, heq, hlt⟩ := hltE
  obtain ⟨k, hk, hjk⟩ := (hSinf ℓ).exists_gt (j₁ + 1)
  have hj_lt_k : toLex (h (D (j₁ + 1))) < toLex (h (D k)) :=
    ⟨ℓ, fun r hr ↦ (heq r hr).trans (hCountEq hk hr.le).symm, by
      rw [Pi.toLex_apply, Pi.toLex_apply, hCountEq hk le_rfl]
      exact hlt⟩
  exact (hstrict hjk).asymm hj_lt_k

/-- In a well-quasi-ordered preorder with finite degree sublevel sets, the set of
complement-counting functions of upper sets is well-founded under the lexicographic order. -/
theorem wellFoundedOn_range_toLex_ncard_compl_of_isUpperSet
    {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    {deg : α → ℕ} (hfin : ∀ d, {x : α | deg x ≤ d}.Finite) :
    Set.WellFoundedOn
      (Set.range fun D : {D : Set α // IsUpperSet D} ↦
        toLex fun ℓ ↦ {x : α | x ∉ D.1 ∧ deg x ≤ ℓ}.ncard)
      (· < ·) := by
  rw [Set.WellFoundedOn, wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  choose D hD using fun j ↦ (f j).2
  have hstrict : StrictAnti fun j ↦ toLex fun ℓ ↦ {x : α | x ∉ (D j).1 ∧ deg x ≤ ℓ}.ncard := by
    refine strictAnti_nat_of_succ_lt fun j ↦ ?_
    have hlt : (f (j + 1)).1 < (f j).1 := hf j
    rwa [← hD (j + 1), ← hD j] at hlt
  exact not_strictAnti_toLex_ncard_compl_of_isUpperSet hfin (fun j ↦ (D j).2) hstrict

/-- Every lexicographically nonincreasing sequence of complement-counting functions of upper sets in
a well-quasi-ordered preorder with finite degree sublevel sets is eventually constant. -/
theorem exists_forall_eq_of_antitone_toLex_ncard_compl_of_isUpperSet
    {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    {deg : α → ℕ} (hfin : ∀ d, {x : α | deg x ≤ d}.Finite)
    {D : ℕ → Set α} (hD : ∀ j, IsUpperSet (D j))
    (hanti : Antitone fun j ↦ toLex fun ℓ ↦ {x : α | x ∉ D j ∧ deg x ≤ ℓ}.ncard) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (fun ℓ ↦ {x : α | x ∉ D j ∧ deg x ≤ ℓ}.ncard) =
        (fun ℓ ↦ {x : α | x ∉ D j₀ ∧ deg x ≤ ℓ}.ncard) := by
  let S : Set (Lex (ℕ → ℕ)) := Set.range fun U : {U : Set α // IsUpperSet U} ↦
    toLex fun ℓ ↦ {x : α | x ∉ U.1 ∧ deg x ≤ ℓ}.ncard
  have : WellFoundedLT S :=
    WellFounded.mono (r := (· < ·)) (wellFoundedOn_range_toLex_ncard_compl_of_isUpperSet hfin)
      fun _ _ h ↦ h
  let g : ℕ → S := fun j ↦
    ⟨toLex fun ℓ ↦ {x : α | x ∉ D j ∧ deg x ≤ ℓ}.ncard, ⟨⟨D j, hD j⟩, rfl⟩⟩
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition (f := g) fun a b hab ↦ hanti hab
  exact ⟨j₀, fun j hj ↦ toLex.injective (congrArg Subtype.val (hj₀ j hj)).symm⟩

end TauCeti
