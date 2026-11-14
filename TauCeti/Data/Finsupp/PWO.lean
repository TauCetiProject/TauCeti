/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Order.PiLex
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.Antichain
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Minimal
import TauCeti.Order.PiLex

/-!
# Lexicographic stabilization of degree-bounded complement counts for upper sets in `σ →₀ ℕ`

In finitely many variables `σ`, Dickson's lemma (`Finsupp.wellQuasiOrderedLE`) implies that no
sequence of upward-closed subsets `D j ⊆ (σ →₀ ℕ)` can have strictly lexicographically decreasing
degree-bounded complement counts `n ↦ Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j}`. Indeed,
along a nonprincipal ultrafilter `𝓤` on `ℕ`, the limit upper set
`Dlim = {α | ∀ᶠ j in 𝓤, α ∈ D j}` has finitely many minimal elements by Dickson's lemma, so some
`D j₀` contains `Dlim`; a strict lexicographic drop from `j₀` to `j₀ + 1` at some least degree `n₁`
would then force a strict lexicographic increase between `j₀ + 1` and a later `j₂` agreeing with
`Dlim` up to degree `n₁`. Consequently, any sequence of upper sets whose degree-bounded complement
counts are lexicographically nonincreasing eventually stabilizes in those counts
(`TauCeti.exists_forall_ge_card_degree_le_notMem_eq_of_isUpperSet`).

## Main results

* `TauCeti.exists_forall_ge_card_degree_le_notMem_eq_of_isUpperSet`: for `[Finite σ]`, any sequence
  of upper sets `D : ℕ → Set (σ →₀ ℕ)` whose degree-bounded complement counts are nonincreasing in
  `Lex (ℕ → ℕ)` is eventually constant in those counts.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

namespace TauCeti

private noncomputable def diagramHilbert {σ : Type*} (D : Set (σ →₀ ℕ)) (n : ℕ) : ℕ :=
  Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D}

private theorem diagramHilbert_anti {σ : Type*} [Finite σ] {D₁ D₂ : Set (σ →₀ ℕ)}
    (h : D₁ ⊆ D₂) (n : ℕ) :
    diagramHilbert D₂ n ≤ diagramHilbert D₁ n := by
  have hsub : {α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ D₁} ⊆ {α : σ →₀ ℕ | α.degree ≤ n} :=
    fun _ hα ↦ hα.1
  have : Finite {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D₁} :=
    ((Finsupp.finite_of_degree_le n).subset hsub).to_subtype
  exact Nat.card_le_card_of_injective
    (fun α ↦ (⟨α.1, α.2.1, fun h₁ ↦ α.2.2 (h h₁)⟩ : {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D₁}))
    (fun _ _ hEq ↦ Subtype.ext (Subtype.mk.inj hEq))

private theorem diagramHilbert_congr_of_degree_le {σ : Type*} {D₁ D₂ : Set (σ →₀ ℕ)} {n m : ℕ}
    (hmn : m ≤ n) (h : ∀ α : σ →₀ ℕ, α.degree ≤ n → (α ∈ D₁ ↔ α ∈ D₂)) :
    diagramHilbert D₁ m = diagramHilbert D₂ m :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun α ↦
    and_congr_right fun hdeg ↦ not_congr (h α (hdeg.trans hmn))

/-- No sequence of upward-closed subsets `D j ⊆ (σ →₀ ℕ)` in finitely many variables can have
strictly lexicographically decreasing degree-bounded complement counts. -/
private theorem not_strictAnti_toLex_diagramHilbert {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti (fun j ↦ toLex (diagramHilbert (D j))) := by
  intro hanti
  let 𝓤 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let Dlim : Set (σ →₀ ℕ) := {α | ∀ᶠ j in (𝓤 : Filter ℕ), α ∈ D j}
  have hmem_iff : ∀ α : σ →₀ ℕ, ∀ᶠ j in (𝓤 : Filter ℕ), α ∈ D j ↔ α ∈ Dlim := fun α ↦ by
    rcases 𝓤.mem_or_compl_mem {j | α ∈ D j} with hmem | hcompl
    · exact Filter.Eventually.mono hmem fun _ hj ↦ ⟨fun _ ↦ hmem, fun _ ↦ hj⟩
    · have hnot : α ∉ Dlim := Ultrafilter.compl_mem_iff_notMem.mp hcompl
      exact Filter.Eventually.mono hcompl fun _ hj ↦ ⟨fun h ↦ False.elim (hj h),
        fun h ↦ False.elim (hnot h)⟩
  have hfin_deg : ∀ n : ℕ, ∀ᶠ j in (𝓤 : Filter ℕ),
      ∀ m ≤ n, diagramHilbert (D j) m = diagramHilbert Dlim m := fun n ↦ by
    have hall : ∀ᶠ j in (𝓤 : Filter ℕ), ∀ α ∈ {α : σ →₀ ℕ | α.degree ≤ n},
        α ∈ D j ↔ α ∈ Dlim :=
      (Finsupp.finite_of_degree_le n).eventually_all.mpr fun α _ ↦ hmem_iff α
    exact hall.mono fun j hj m hmn ↦ diagramHilbert_congr_of_degree_le hmn hj
  have hVfin : {α : σ →₀ ℕ | Minimal (· ∈ Dlim) α}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  have hVev : ∀ᶠ j in (𝓤 : Filter ℕ), ∀ v ∈ {α : σ →₀ ℕ | Minimal (· ∈ Dlim) α}, v ∈ D j :=
    hVfin.eventually_all.mpr fun v hv ↦ hv.prop
  obtain ⟨j₀, hj₀⟩ := hVev.exists
  have hsub : Dlim ⊆ D j₀ := fun γ hγ ↦ by
    obtain ⟨v, hvle, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ Dlim) γ hγ
    exact hD j₀ hvle (hj₀ v hvmin)
  have hle₀ : toLex (diagramHilbert (D j₀)) ≤ toLex (diagramHilbert Dlim) :=
    Pi.toLex_monotone (diagramHilbert_anti hsub)
  have hlt₁ : toLex (diagramHilbert (D (j₀ + 1))) < toLex (diagramHilbert Dlim) :=
    (hanti (Nat.lt_succ_self j₀)).trans_le hle₀
  obtain ⟨n₁, heq₁, hlt_n₁⟩ := Pi.Lex.toLex_lt_toLex.mp hlt₁
  have hgt_ev : ∀ᶠ j in (𝓤 : Filter ℕ), j₀ + 1 < j :=
    Ultrafilter.of_le Filter.atTop (Filter.eventually_gt_atTop (j₀ + 1))
  obtain ⟨j₂, hj₂_eq, hj₂_gt⟩ := (hfin_deg n₁ |>.and hgt_ev).exists
  have hlt₂ : toLex (diagramHilbert (D (j₀ + 1))) < toLex (diagramHilbert (D j₂)) :=
    Pi.Lex.toLex_lt_toLex.mpr ⟨n₁, fun m hm ↦ (heq₁ m hm).trans (hj₂_eq m hm.le).symm,
      lt_of_lt_of_eq hlt_n₁ (hj₂_eq n₁ le_rfl).symm⟩
  exact (hanti hj₂_gt).not_gt hlt₂

/-- For finitely many variables `σ`, any sequence of upward-closed subsets `D : ℕ → Set (σ →₀ ℕ)`
whose degree-bounded complement counts are lexicographically nonincreasing is eventually constant
in those counts. -/
theorem exists_forall_ge_card_degree_le_notMem_eq_of_isUpperSet {σ : Type*} [Finite σ]
    (D : ℕ → Set (σ →₀ ℕ)) (hD : ∀ j, IsUpperSet (D j))
    (hlex : ∀ j, toLex (fun n ↦ Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D (j + 1)}) ≤
      toLex (fun n ↦ Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j})) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (fun n ↦ Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j}) =
        (fun n ↦ Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j₀}) := by
  have hanti : Antitone (fun j ↦ toLex (diagramHilbert (D j))) :=
    antitone_nat_of_succ_le hlex
  by_contra! hnot
  have hstep : ∀ j₀, ∃ j, j₀ < j ∧
      toLex (diagramHilbert (D j)) < toLex (diagramHilbert (D j₀)) := fun j₀ ↦ by
    obtain ⟨j, hjle, hjne⟩ := hnot j₀
    have hjlt : j₀ < j := lt_of_le_of_ne hjle fun hEq ↦ hjne (hEq ▸ rfl)
    exact ⟨j, hjlt, lt_of_le_of_ne (hanti hjle) (toLex_inj.ne.mpr hjne)⟩
  let next (j : ℕ) : ℕ := Classical.choose (hstep j)
  have hnext : ∀ j, toLex (diagramHilbert (D (next j))) < toLex (diagramHilbert (D j)) :=
    fun j ↦ (Classical.choose_spec (hstep j)).2
  let subseq (k : ℕ) : ℕ := next^[k] 0
  have hstrict : StrictAnti (fun k ↦ toLex (diagramHilbert (D (subseq k)))) :=
    strictAnti_nat_of_succ_lt fun k ↦ by
      dsimp only [subseq]
      rw [Function.iterate_succ_apply']
      exact hnext (subseq k)
  exact not_strictAnti_toLex_diagramHilbert (fun k ↦ hD (subseq k)) hstrict

end TauCeti
