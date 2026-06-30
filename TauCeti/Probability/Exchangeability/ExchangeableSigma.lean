module

public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.Probability.Process.Tail
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Exchangeable σ-algebra on path space

This file records the Layer 2 exchangeability-roadmap σ-algebra of path-space events invariant
under finitely supported permutations of the time coordinate.  It also relates the one-sided path
tail σ-algebra to this exchangeable σ-algebra: a tail event is fixed by every finitely supported
time permutation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*}

/-- Reindex a one-sided path by a permutation of time. -/
abbrev permReindex (π : Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  fun n => x (π n)

/-- Coordinates of a permutation-reindexed path. -/
@[simp]
theorem permReindex_apply (π : Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    permReindex π x n = x (π n) :=
  rfl

/-- A permutation of `ℕ` is finitely supported if it moves only finitely many indices. -/
def IsFinitelySupportedPerm (π : Equiv.Perm ℕ) : Prop :=
  Set.Finite {n : ℕ | π n ≠ n}

/-- Constructor for finitely supported permutations from an eventual fixedness bound. -/
theorem isFinitelySupportedPerm_of_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : ∃ N, ∀ n, N ≤ n → π n = n) : IsFinitelySupportedPerm π := by
  rcases hπ with ⟨N, hN⟩
  exact (Set.finite_Iio N).subset fun n hn => by
    by_contra hnN
    exact hn (hN n (not_lt.mp hnN))

/-- The identity permutation of `ℕ` is finitely supported. -/
theorem isFinitelySupportedPerm_one : IsFinitelySupportedPerm (1 : Equiv.Perm ℕ) := by
  rw [IsFinitelySupportedPerm]
  simp

/-- A finitely supported permutation fixes every sufficiently large index. -/
theorem IsFinitelySupportedPerm.eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : IsFinitelySupportedPerm π) : ∃ N, ∀ n, N ≤ n → π n = n := by
  rcases hπ.bddAbove with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hn_support : n ∈ {k : ℕ | π k ≠ k} := hne
  exact (not_lt_of_ge hn) (Nat.lt_succ_of_le (hN hn_support))

/-- A permutation of `ℕ` is finitely supported iff it fixes all sufficiently large indices. -/
theorem isFinitelySupportedPerm_iff_eventually_eq_self {π : Equiv.Perm ℕ} :
    IsFinitelySupportedPerm π ↔ ∃ N, ∀ n, N ≤ n → π n = n :=
  ⟨IsFinitelySupportedPerm.eventually_eq_self, isFinitelySupportedPerm_of_eventually_eq_self⟩

/-- A transposition of two natural-number indices is finitely supported. -/
theorem isFinitelySupportedPerm_swap (a b : ℕ) :
    IsFinitelySupportedPerm (Equiv.swap a b) := by
  rw [IsFinitelySupportedPerm]
  exact (Set.finite_singleton a).insert b |>.subset fun n hn => by
    by_cases hna : n = a
    · exact Or.inr hna
    by_cases hnb : n = b
    · exact Or.inl hnb
    exfalso
    exact hn (Equiv.swap_apply_of_ne_of_ne hna hnb)

/-- The product of finitely supported permutations is finitely supported. -/
theorem IsFinitelySupportedPerm.mul {π σ : Equiv.Perm ℕ}
    (hπ : IsFinitelySupportedPerm π) (hσ : IsFinitelySupportedPerm σ) :
    IsFinitelySupportedPerm (π * σ) := by
  rw [IsFinitelySupportedPerm] at hπ hσ ⊢
  refine (hσ.union (hπ.preimage (Equiv.injective σ).injOn)).subset ?_
  intro n hmove
  by_cases hσn : σ n = n
  · right
    by_contra hπσ
    exact hmove (by simpa [hσn] using hπσ)
  · exact Or.inl hσn

/-- The inverse of a finitely supported permutation is finitely supported. -/
theorem IsFinitelySupportedPerm.symm {π : Equiv.Perm ℕ}
    (hπ : IsFinitelySupportedPerm π) : IsFinitelySupportedPerm π.symm := by
  rw [IsFinitelySupportedPerm] at hπ ⊢
  exact (hπ.image π).subset fun n hn => by
    exact ⟨π.symm n, by simpa using hn.symm, by simp⟩

variable [MeasurableSpace α]

/-- Reindexing paths by a time permutation is measurable. -/
theorem measurable_permReindex (π : Equiv.Perm ℕ) :
    Measurable (permReindex (α := α) π) := by
  simpa [permReindex] using measurable_reindex (α := α) (φ := π)

/-- The exchangeable σ-algebra on path space: ambient-measurable events invariant under every
finitely supported permutation of the time coordinate. -/
@[implicit_reducible]
def exchangeableSigma (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  ⨅ π : {π : Equiv.Perm ℕ // IsFinitelySupportedPerm π},
    MeasurableSpace.invariants (permReindex (α := α) π.1)

/-- A set is measurable for `exchangeableSigma` iff it is ambient-measurable and fixed by every
finitely supported time permutation. -/
@[simp]
theorem mem_exchangeableSigma_iff {s : Set (ℕ → α)} :
    MeasurableSet[exchangeableSigma α] s ↔
      MeasurableSet s ∧
        ∀ π : Equiv.Perm ℕ, IsFinitelySupportedPerm π →
          permReindex (α := α) π ⁻¹' s = s := by
  rw [exchangeableSigma, MeasurableSpace.measurableSet_iInf]
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · exact (MeasurableSpace.invariants_le (permReindex (α := α) (1 : Equiv.Perm ℕ))) _
        (hs ⟨1, isFinitelySupportedPerm_one⟩)
    · intro π hπ
      exact (MeasurableSpace.measurableSet_invariants.mp (hs ⟨π, hπ⟩)).2
  · rintro ⟨hs_meas, hs_inv⟩ π
    exact MeasurableSpace.measurableSet_invariants.mpr ⟨hs_meas, hs_inv π.1 π.2⟩

/-- The exchangeable σ-algebra is a sub-σ-algebra of the ambient path-space σ-algebra. -/
theorem exchangeableSigma_le :
    exchangeableSigma α ≤ (inferInstance : MeasurableSpace (ℕ → α)) := by
  intro s hs
  exact (mem_exchangeableSigma_iff.mp hs).1

/-- An ambient-measurable event fixed by every finitely supported time permutation is measurable
for the exchangeable σ-algebra. -/
theorem measurableSet_exchangeableSigma_of_forall_permReindex {s : Set (ℕ → α)}
    (hs_meas : MeasurableSet s)
    (hs_inv : ∀ π : Equiv.Perm ℕ, IsFinitelySupportedPerm π →
      permReindex (α := α) π ⁻¹' s = s) :
    MeasurableSet[exchangeableSigma α] s :=
  mem_exchangeableSigma_iff.mpr ⟨hs_meas, hs_inv⟩

/-- An exchangeable event is fixed by any finitely supported time permutation. -/
theorem MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) {π : Equiv.Perm ℕ}
    (hπ : IsFinitelySupportedPerm π) :
    permReindex (α := α) π ⁻¹' s = s :=
  (mem_exchangeableSigma_iff.mp hs).2 π hπ

/-- If a set belongs to the future path σ-algebra from time `N` onward and `π` fixes every index
`k ≥ N`, then reindexing paths by `π` leaves the set fixed. -/
private theorem preimage_permReindex_eq_of_measurable_tailFamily
    {s : Set (ℕ → α)} {π : Equiv.Perm ℕ} {N : ℕ}
    (hs : MeasurableSet[tailFamily (fun k (x : ℕ → α) => x k) N] s)
    (hπ : ∀ k, N ≤ k → π k = k) :
    permReindex (α := α) π ⁻¹' s = s := by
  rw [tailFamily_eq_iSup_comap] at hs
  rw [MeasurableSpace.measurableSet_iSup] at hs
  induction hs with
  | basic u hu =>
      rcases hu with ⟨k, t, ht, rfl⟩
      ext x
      change x (π k.1) ∈ t ↔ x k.1 ∈ t
      rw [hπ k.1 k.2]
  | empty =>
      simp
  | compl t ht hpre =>
      rw [Set.preimage_compl, hpre]
  | iUnion f _ hf =>
      rw [Set.preimage_iUnion]
      simp [hf]

/-- The path-space tail σ-algebra is contained in the exchangeable σ-algebra: tail events are
fixed by every finitely supported permutation of the time coordinate. -/
theorem pathTail_le_exchangeableSigma :
    pathTail α ≤ exchangeableSigma α := by
  intro s hs
  refine mem_exchangeableSigma_iff.mpr ⟨?_, ?_⟩
  · exact tailProcess_le_ambient 0 (X := fun k (x : ℕ → α) => x k)
      (fun k _ => measurable_pi_apply k) s hs
  · intro π hπ
    rcases hπ.eventually_eq_self with ⟨N, hN⟩
    exact preimage_permReindex_eq_of_measurable_tailFamily
      ((pathTail_le_tailFamily (α := α) N) s hs) hN

end Probability

end TauCeti
