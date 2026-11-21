/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Order.PiLex
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Minimal

/-!
# Complement counts and lexicographic well-foundedness for upper sets in `σ →₀ ℕ`

For a finite variable type `σ` and an upper set `D : UpperSet (σ →₀ ℕ)` in the componentwise
order, the complement-counting function `ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D).ncard` records
how many exponents of degree at most `ℓ` lie outside `D`.

By diagonalization over finite bounded-degree balls, every sequence `E : ℕ → UpperSet (σ →₀ ℕ)`
admits an upper set `D` that agrees on `{α | α.degree ≤ ℓ}` with infinitely many terms `E j`
for every `ℓ` (`Finsupp.exists_upperSet_infinite_mem_iff`). By Dickson's lemma
(`Finsupp.wellQuasiOrderedLE`), every upper set `D` has a finite degree bound `d` such that any
upper set containing all elements of `D` of degree at most `d` contains all of `D`
(`Finsupp.exists_forall_subset_of_forall_degree_le`). Combining these two properties yields the
combinatorial core of Bierstone–Milman's stabilization theorem: the set of complement-counting
functions realized by upper sets in `σ →₀ ℕ` is well-founded in the lexicographic order on
`ℕ → ℕ` (`Finsupp.isWF_range_toLex_ncard_degree_le_sdiff`), so every lexicographically antitone
sequence of such functions stabilizes
(`Finsupp.exists_ncard_degree_le_sdiff_eq_of_antitone_lex`).

## Main results

* `Finsupp.exists_upperSet_infinite_mem_iff`: every sequence of upper sets in `σ →₀ ℕ` admits an
  upper set agreeing with infinitely many terms on every bounded-degree ball.
* `Finsupp.exists_forall_subset_of_forall_degree_le`: every upper set `D` in `σ →₀ ℕ` has a degree
  bound `d` such that containment on `{α | α.degree ≤ d}` implies `(D : Set (σ →₀ ℕ)) ⊆ E`.
* `Finsupp.isWF_range_toLex_ncard_degree_le_sdiff`: the range of complement-counting functions of
  upper sets in `σ →₀ ℕ` is well-founded in `Lex (ℕ → ℕ)`.
* `Finsupp.exists_ncard_degree_le_sdiff_eq_of_antitone_lex`: every lexicographically antitone
  sequence of complement-counting functions of upper sets in `σ →₀ ℕ` is eventually constant.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc. 2
  (1989), 801–836, Theorem 5.2.1 (pp. 820–821).
-/

public section

namespace Finsupp

/-- Pigeonhole extraction on a finite ball `B`: an infinite set of indices `S` contains an infinite
subset on which membership in `E j` is constant on `B`. -/
private theorem exists_infinite_subset_mem_iff {σ : Type*} (E : ℕ → UpperSet (σ →₀ ℕ))
    (B : Finset (σ →₀ ℕ)) {S : Set ℕ} (hS : S.Infinite) :
    ∃ S' ⊆ S, S'.Infinite ∧ ∃ A : Finset (σ →₀ ℕ),
      ∀ j ∈ S', ∀ α ∈ B, (α ∈ E j ↔ α ∈ A) := by
  classical
  have : Infinite S := Set.infinite_coe_iff.mpr hS
  let g : S → B.powerset := fun j ↦
    ⟨B.filter (· ∈ E j.val), Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  obtain ⟨⟨A, hA⟩, hfib⟩ := Finite.exists_infinite_fiber g
  refine ⟨Subtype.val '' (g ⁻¹' {⟨A, hA⟩}), Subtype.coe_image_subset S _,
    (Set.infinite_coe_iff.mp hfib).image Subtype.val_injective.injOn, A, ?_⟩
  rintro _ ⟨⟨j, hjS⟩, hjg, rfl⟩ α hα
  have hval : B.filter (· ∈ E j) = A := by
    simpa [g] using congrArg Subtype.val (Set.mem_singleton_iff.mp hjg)
  rw [← hval, Finset.mem_filter]
  exact ⟨fun h ↦ ⟨hα, h⟩, fun h ↦ h.2⟩

section UpperSetStabilization

variable {σ : Type*} [Finite σ]

/-- Diagonal compactness for upper sets in `σ →₀ ℕ`: every sequence `E : ℕ → UpperSet (σ →₀ ℕ)`
admits an upper set `D` and infinite index sets `S ℓ` such that for every `j ∈ S ℓ`, `D` and `E j`
agree on all exponents of degree at most `ℓ`. -/
theorem exists_upperSet_infinite_mem_iff (E : ℕ → UpperSet (σ →₀ ℕ)) :
    ∃ (D : UpperSet (σ →₀ ℕ)) (S : ℕ → Set ℕ),
      (∀ ℓ, (S ℓ).Infinite) ∧
      ∀ ℓ, ∀ j ∈ S ℓ, ∀ α : σ →₀ ℕ, α.degree ≤ ℓ → (α ∈ D ↔ α ∈ E j) := by
  let B : ℕ → Finset (σ →₀ ℕ) := fun ℓ ↦ (finite_of_degree_le ℓ).toFinset
  let State (ℓ : ℕ) := { p : Set ℕ × Finset (σ →₀ ℕ) //
    p.1.Infinite ∧ ∀ j ∈ p.1, ∀ α ∈ B ℓ, (α ∈ E j ↔ α ∈ p.2) }
  let step : (ℓ : ℕ) → (st : State ℓ) → { next : State (ℓ + 1) // next.val.1 ⊆ st.val.1 } :=
    fun ℓ st ↦
      have hex := exists_infinite_subset_mem_iff E (B (ℓ + 1)) st.property.1
      ⟨⟨(hex.choose, hex.choose_spec.2.2.choose), hex.choose_spec.2.1,
        hex.choose_spec.2.2.choose_spec⟩, hex.choose_spec.1⟩
  let init : State 0 :=
    have hex := exists_infinite_subset_mem_iff E (B 0) Set.infinite_univ
    ⟨(hex.choose, hex.choose_spec.2.2.choose), hex.choose_spec.2.1,
      hex.choose_spec.2.2.choose_spec⟩
  let seq : (ℓ : ℕ) → State ℓ := Nat.rec init fun ℓ st ↦ (step ℓ st).val
  let S : ℕ → Set ℕ := fun ℓ ↦ (seq ℓ).val.1
  let A : ℕ → Finset (σ →₀ ℕ) := fun ℓ ↦ (seq ℓ).val.2
  have hS_step (ℓ : ℕ) : S (ℓ + 1) ⊆ S ℓ := (step ℓ (seq ℓ)).property
  have hS_anti : Antitone S := antitone_nat_of_succ_le hS_step
  have hS_inf (ℓ : ℕ) : (S ℓ).Infinite := (seq ℓ).property.1
  have hA (ℓ : ℕ) {j : ℕ} (hj : j ∈ S ℓ) {α : σ →₀ ℕ} (hα : α ∈ B ℓ) :
      α ∈ E j ↔ α ∈ A ℓ := (seq ℓ).property.2 j hj α hα
  let Dset : Set (σ →₀ ℕ) := {α | α ∈ A α.degree}
  have hcons (ℓ : ℕ) {j : ℕ} (hj : j ∈ S ℓ) {α : σ →₀ ℕ} (hα : α.degree ≤ ℓ) :
      α ∈ Dset ↔ α ∈ E j := by
    have hj' : j ∈ S α.degree := hS_anti hα hj
    simp only [Dset, Set.mem_ofPred_eq]
    exact (hA α.degree hj' ((Set.Finite.mem_toFinset _).mpr (le_refl α.degree))).symm
  have hD_upper : IsUpperSet Dset := by
    intro α β hαβ hα
    obtain ⟨j, hj⟩ := (hS_inf β.degree).nonempty
    have hαE : α ∈ E j := (hcons β.degree hj (degree_mono hαβ)).mp hα
    exact (hcons β.degree hj le_rfl).mpr ((E j).upper hαβ hαE)
  exact ⟨⟨Dset, hD_upper⟩, S, hS_inf, fun ℓ j hj α hα ↦ hcons ℓ hj hα⟩

/-- By Dickson's lemma, every upper set `D` in `σ →₀ ℕ` (`[Finite σ]`) admits a degree bound `d`
such that any upper set `E` containing all elements of `D` of degree at most `d` satisfies
`(D : Set (σ →₀ ℕ)) ⊆ E`. -/
theorem exists_forall_subset_of_forall_degree_le (D : UpperSet (σ →₀ ℕ)) :
    ∃ d : ℕ, ∀ E : UpperSet (σ →₀ ℕ),
      (∀ α : σ →₀ ℕ, α.degree ≤ d → α ∈ D → α ∈ E) → (D : Set (σ →₀ ℕ)) ⊆ E := by
  classical
  have hmin_fin : {v : σ →₀ ℕ | Minimal (· ∈ (D : Set (σ →₀ ℕ))) v}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  refine ⟨hmin_fin.toFinset.sup degree, fun E hE α hα ↦ ?_⟩
  have : WellFoundedLT (σ →₀ ℕ) := WellQuasiOrderedLE.to_wellFoundedLT
  obtain ⟨v, hv_le, hv_min⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ (D : Set (σ →₀ ℕ))) α hα
  have hvd : v.degree ≤ hmin_fin.toFinset.sup degree :=
    Finset.le_sup (f := degree) (hmin_fin.mem_toFinset.mpr hv_min)
  exact E.upper hv_le (hE v hvd hv_min.prop)

/-- **Bierstone–Milman lexicographic well-foundedness**: in finitely many variables, the set of
complement-counting functions `ℓ ↦ ({α | α.degree ≤ ℓ} \ D).ncard` realized by upper sets
`D : UpperSet (σ →₀ ℕ)` is well-founded in the lexicographic order on `ℕ → ℕ`. -/
theorem isWF_range_toLex_ncard_degree_le_sdiff (σ : Type*) [Finite σ] :
    (Set.range fun D : UpperSet (σ →₀ ℕ) ↦
      toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (D : Set (σ →₀ ℕ))).ncard).IsWF := by
  classical
  let c (D : Set (σ →₀ ℕ)) (ℓ : ℕ) : ℕ := ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D).ncard
  refine Set.isWF_iff_no_descending_seq.mpr fun f hf hmem ↦ ?_
  choose E hE using hmem
  dsimp only at hE
  obtain ⟨D, S, hS_inf, hcons⟩ := exists_upperSet_infinite_mem_iff E
  obtain ⟨d, hd⟩ := exists_forall_subset_of_forall_degree_le D
  have hle_cD {j : ℕ} (hj : j ∈ S d) (m : ℕ) : c (E j) m ≤ c D m :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right (hd (E j) fun α hα ↦ (hcons d j hj α hα).mp))
      (finite_of_degree_le m).sdiff
  obtain ⟨j₁, hj₁⟩ := (hS_inf d).nonempty
  obtain ⟨j₂, hj₂, hj₁₂⟩ := (hS_inf d).exists_gt j₁
  have hne₁₂ : c (E j₁) ≠ c (E j₂) := fun heq ↦ (hf hj₁₂).ne' <| by
    rw [← hE j₁, ← hE j₂]
    exact congrArg toLex heq
  obtain ⟨j, hj, hne⟩ : ∃ j ∈ S d, c (E j) ≠ c D := by
    by_cases h₁ : c (E j₁) = c D
    · exact ⟨j₂, hj₂, fun h₂ ↦ hne₁₂ (h₁.trans h₂.symm)⟩
    · exact ⟨j₁, hj₁, h₁⟩
  have hex_diff : ∃ m, c (E j) m ≠ c D m := Function.ne_iff.mp hne
  let m₀ : ℕ := Nat.find hex_diff
  have hm₀_lt : c (E j) m₀ < c D m₀ :=
    lt_of_le_of_ne (hle_cD hj m₀) (Nat.find_spec hex_diff)
  have hm₀_eq {m : ℕ} (hm : m < m₀) : c (E j) m = c D m :=
    not_not.mp (Nat.find_min hex_diff hm)
  obtain ⟨k, hk, hjk⟩ := (hS_inf m₀).exists_gt j
  have hk_eq {m : ℕ} (hm : m ≤ m₀) : c (E k) m = c D m := by
    refine congrArg Set.ncard ?_
    ext α
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
    exact and_congr_right fun hα ↦ (hcons m₀ k hk α (hα.trans hm)).not.symm
  have hlt_jk : f j < f k := by
    rw [← hE j, ← hE k]
    exact ⟨m₀, fun m hm ↦ (hm₀_eq hm).trans (hk_eq hm.le).symm,
      lt_of_lt_of_eq hm₀_lt (hk_eq le_rfl).symm⟩
  exact lt_asymm hlt_jk (hf hjk)

/-- Any lexicographically antitone sequence of complement-counting functions realized by upper sets
in `σ →₀ ℕ` (`[Finite σ]`) is eventually constant. -/
theorem exists_ncard_degree_le_sdiff_eq_of_antitone_lex (E : ℕ → UpperSet (σ →₀ ℕ))
    (hE : Antitone fun j ↦
      toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (E j : Set (σ →₀ ℕ))).ncard) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      ∀ ℓ, ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (E j : Set (σ →₀ ℕ))).ncard =
        ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (E j₀ : Set (σ →₀ ℕ))).ncard := by
  have hwf := (isWF_range_toLex_ncard_degree_le_sdiff σ).mono
    (Set.range_subset_iff.mpr fun j ↦ ⟨E j, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := hwf.min_mem (Set.range_nonempty _)
  refine ⟨j₀, fun j hj ℓ ↦ ?_⟩
  have heq := eq_of_le_of_not_lt (hE hj)
    (hj₀ ▸ hwf.not_lt_min (Set.range_nonempty _) ⟨j, rfl⟩)
  exact congrArg (fun x : Lex (ℕ → ℕ) ↦ ofLex x ℓ) heq

end UpperSetStabilization

end Finsupp
