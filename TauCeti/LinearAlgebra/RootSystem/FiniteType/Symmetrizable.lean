/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.LacingNumber

/-!
# Symmetrizers of indecomposable finite-type Cartan matrices

For a `TauCeti.SymmetrizableDatum` on a finite index type, connectedness of its diagram graph is
equivalent to nonemptiness together with `Matrix.IsIndecomposable`
(`TauCeti.SymmetrizableDatum.connected_diagramGraph_iff`). Combined with the classification of
connected finite-type Cartan matrices (`TauCeti.IsFiniteType.existsUnique_dynkinType`) and the
uniqueness of the normalized symmetrizer of an indecomposable datum
(`TauCeti.SymmetrizableDatum.normalizeSymmetrizer_eq_of_isIndecomposable`), this identifies the
normalized symmetrizer of any nonempty indecomposable finite-type datum: its entries take values in
`{1, r}` for a lacing number `r ∈ {1, 2, 3}`, attaining both `1` and `r`
(`TauCeti.SymmetrizableDatum.exists_lacing_normalizeSymmetrizer_of_isFiniteType`).

## Main results

* `TauCeti.SymmetrizableDatum.connected_diagramGraph_iff`: on a finite index type, the diagram of
  `A.cartan` is connected if and only if the index type is nonempty and `A.cartan` is
  indecomposable.
* `TauCeti.SymmetrizableDatum.exists_lacing_normalizeSymmetrizer_of_isFiniteType`: the normalized
  symmetrizer of a nonempty indecomposable finite-type datum has range `{1, r}` with
  `r ∈ {1, 2, 3}`.
-/

public section

namespace TauCeti.SymmetrizableDatum

variable {I : Type*} (A : SymmetrizableDatum I)

/-- On a finite index type, the diagram of `A` is connected if and only if `I` is nonempty and
`A.cartan` is indecomposable. -/
theorem connected_diagramGraph_iff [Finite I] :
    (diagramGraph A.cartan).Connected ↔ Nonempty I ∧ A.cartan.IsIndecomposable := by
  rw [SimpleGraph.connected_iff, and_comm, Matrix.isIndecomposable_iff_reflTransGen]
  refine and_congr_right fun _ ↦ ⟨fun hpre i j ↦ ?_, fun hind i j ↦ ?_⟩
  · obtain ⟨w⟩ := hpre i j
    induction w with
    | nil => exact .refl
    | @cons u v z hadj _ ih =>
      exact Relation.ReflTransGen.head (diagramGraph_adj.mp hadj).2.1 ih
  · induction hind i j with
    | refl => exact .refl _
    | @tail k l _ hkl ih =>
      rcases eq_or_ne k l with rfl | hne
      · exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable
          (diagramGraph_adj.mpr ⟨hne, hkl, (A.zero_comm k l).not.mp hkl⟩))

/-- Explicit normalized symmetrizer of a datum reindexed from a valid `DynkinType`, given by
`r / rootLength` where `r` is the lacing number. -/
private theorem exists_symmetrizer_of_dynkinType (t : DynkinType) (ht : t.Valid)
    (e : I ≃ Fin t.rank) (he : ∀ i j, A.cartan i j = t.cartanMatrix (e i) (e j)) :
    ∃ (r : ℕ) (A₀ : SymmetrizableDatum I),
      (r = 1 ∨ r = 2 ∨ r = 3) ∧ A₀.cartan = A.cartan ∧
      (∃ i, A₀.symmetrizer i = 1) ∧ (∃ j, A₀.symmetrizer j = r) ∧
      ∀ k, A₀.symmetrizer k = 1 ∨ A₀.symmetrizer k = r := by
  let r : ℕ := t.lacingNumber.toNat
  have hr : (r = 1 ∨ r = 2 ∨ r = 3) ∧ (r : ℤ) = t.lacingNumber := by
    cases t <;> simp [r]
  have hr_pos : 0 < r := by rcases hr.1 with h | h | h <;> omega
  let p : I → ℕ := fun i ↦ if t.rootLength (e i) = 1 then r else 1
  have hp_mul (i : I) : (p i : ℤ) * t.rootLength (e i) = t.lacingNumber := by
    have hmem : t.rootLength (e i) = 1 ∨ t.rootLength (e i) = t.lacingNumber := by
      have hrange : t.rootLength (e i) ∈ ({1, t.lacingNumber} : Set ℤ) := by
        rw [← DynkinType.range_rootLength ht]; exact ⟨e i, rfl⟩
      simpa using hrange
    simp only [p]
    split_ifs with h1
    · simp [h1, hr.2]
    · simp [hmem.resolve_left h1]
  refine ⟨r, { A with
    symmetrizer := p
    symmetrizer_pos := fun i ↦ by simp only [p]; split_ifs <;> omega
    symmetrizes := fun i j ↦ by
      have hlen := t.cartanMatrix_mul_rootLength (e i) (e j)
      rw [← he i j, ← he j i] at hlen
      have hl_ne : t.lacingNumber ≠ 0 := by rw [← hr.2]; exact_mod_cast hr_pos.ne'
      refine mul_right_cancel₀ hl_ne ?_
      calc ((p i : ℤ) * A.cartan i j) * t.lacingNumber
          = (p i : ℤ) * A.cartan i j * ((p j : ℤ) * t.rootLength (e j)) := by rw [hp_mul j]
        _ = (p i : ℤ) * (p j : ℤ) * (A.cartan i j * t.rootLength (e j)) := by ring
        _ = (p i : ℤ) * (p j : ℤ) * (A.cartan j i * t.rootLength (e i)) := by rw [hlen]
        _ = (p j : ℤ) * A.cartan j i * ((p i : ℤ) * t.rootLength (e i)) := by ring
        _ = ((p j : ℤ) * A.cartan j i) * t.lacingNumber := by rw [hp_mul i] },
    hr.1, rfl, ?_, ?_, fun k ↦ by simp only [p]; split_ifs <;> simp⟩
  · have hl_in : t.lacingNumber ∈ Set.range t.rootLength := by
      rw [DynkinType.range_rootLength ht]; simp
    obtain ⟨k, hk⟩ := hl_in
    refine ⟨e.symm k, ?_⟩
    simp only [p, Equiv.apply_symm_apply]
    split_ifs with h1
    · rw [hk] at h1; exact_mod_cast hr.2.trans h1
    · rfl
  · obtain ⟨k, hk⟩ := DynkinType.exists_rootLength_eq_one ht
    exact ⟨e.symm k, by simp [p, hk]⟩

/-- **Normalized symmetrizer of an indecomposable finite-type datum.** On a nonempty index type, if
`A.cartan` is indecomposable of finite type, there is a lacing number `r ∈ {1, 2, 3}` such that
`A.normalizeSymmetrizer.symmetrizer` takes values in `{1, r}` and attains both `1` and `r`. -/
theorem exists_lacing_normalizeSymmetrizer_of_isFiniteType [Fintype I] [Nonempty I]
    (hft : IsFiniteType A.cartan) (hA : A.cartan.IsIndecomposable) :
    ∃ r ∈ ({1, 2, 3} : Set ℕ),
      (∃ i, A.normalizeSymmetrizer.symmetrizer i = 1) ∧
      (∃ j, A.normalizeSymmetrizer.symmetrizer j = r) ∧
      ∀ k, A.normalizeSymmetrizer.symmetrizer k ∈ ({1, r} : Set ℕ) := by
  have hconn : (diagramGraph A.cartan).Connected :=
    A.connected_diagramGraph_iff.mpr ⟨‹Nonempty I›, hA⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := hft.existsUnique_dynkinType hconn
  obtain ⟨r, A₀, hr, hcart, ⟨i₁, hi₁⟩, ⟨j₁, hj₁⟩, hp⟩ :=
    A.exists_symmetrizer_of_dynkinType t ht e he
  have hgcd : Finset.univ.gcd A₀.symmetrizer = 1 :=
    Nat.dvd_one.mp (hi₁ ▸ Finset.gcd_dvd (Finset.mem_univ i₁))
  have heq : A.normalizeSymmetrizer = A₀.normalizeSymmetrizer :=
    (A.normalizeSymmetrizer_eq_of_isIndecomposable hA hcart).symm
  have hval (k : I) : A.normalizeSymmetrizer.symmetrizer k = A₀.symmetrizer k := by
    rw [heq, normalizeSymmetrizer_symmetrizer, hgcd, Nat.div_one]
  refine ⟨r, by simpa using hr, ⟨i₁, by rw [hval, hi₁]⟩, ⟨j₁, by rw [hval, hj₁]⟩, fun k ↦ ?_⟩
  rw [hval]
  simpa using hp k

end TauCeti.SymmetrizableDatum
