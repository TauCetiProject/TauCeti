/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Extracting independent vectors through field towers

An independent family after an `F`-linear map can lose independence over an extension `K/F`.
The degree of `K/F` bounds this loss: the number of independent images is at most
`[K : F]` times the dimension of the `K`-span of the original vectors.

We also select independent vectors from prescribed prefixes of a finite family. Combining
the two statements selects `k` independent original vectors from `[K : F] * k` independent
images, with the vector at position `j` selected by position `[K : F] * j`. These index bounds
allow estimates on an ordered family, such as a family of lattice minima, to survive extraction.

The statements follow Ralf Stephan's CC0 development in
[rwst/lean-code](https://github.com/rwst/lean-code), file
`ForMathlib/LinearAlgebra/LinearIndependentRestrictScalars.lean`
at commit `2eadabb0e181b894a4c49fb38b7e45daf6214b25`.
The proofs here use Mathlib's restriction of scalars, tower law, and finite-span API.
-/

public section

open Module Submodule

namespace LinearIndependent

variable {F K E V W ι : Type*} [Field F] [DivisionRing K] [DivisionRing E]
  [Algebra F K] [Algebra F E] [Module.Finite F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
  [Fintype ι] {f : V →ₗ[F] W} {u : ι → V}

/-- Independence of the images under an `F`-linear map bounds the size of a finite family
by the extension degree times the dimension of its `K`-span. Neither ambient vector space
is required to be finite-dimensional. -/
theorem card_le_finrank_mul (h : LinearIndependent E (f ∘ u)) :
    Fintype.card ι ≤ finrank F K * finrank K (span K (Set.range u)) := by
  let U := span K (Set.range u)
  let : Module.Finite K U := Module.Finite.span_of_finite K (Set.finite_range u)
  let : Module.Finite F U := Module.Finite.trans K U
  let v : ι → U := fun i ↦ ⟨u i, subset_span ⟨i, rfl⟩⟩
  have hv : LinearIndependent F v :=
    ((h.restrict_scalars' F).of_comp f).of_comp (U.subtype.restrictScalars F)
  rw [Module.finrank_mul_finrank F K U]
  exact hv.fintype_card_le_finrank

end LinearIndependent

namespace TauCeti

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If the prefix available at stage `j` spans more than `j` dimensions, one can select
an independent family within all the prescribed prefix bounds. The bounds need not be monotone. -/
theorem exists_linearIndependent_comp_of_lt_finrank_span {n k : ℕ} {u : Fin n → V}
    {m : Fin k → ℕ}
    (h : ∀ j : Fin k, (j : ℕ) < finrank K (span K (u '' {i | (i : ℕ) ≤ m j}))) :
    ∃ s : Fin k → Fin n, LinearIndependent K (u ∘ s) ∧ ∀ j, (s j : ℕ) ≤ m j := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs, hsm⟩ := ih (m := fun j ↦ m j.castSucc) (fun j ↦ h j.castSucc)
    have hex : ∃ i : Fin n, (i : ℕ) ≤ m (Fin.last k) ∧
        u i ∉ span K (Set.range (u ∘ s)) := by
      by_contra! hn
      have hle : span K (u '' {i | (i : ℕ) ≤ m (Fin.last k)}) ≤
          span K (Set.range (u ∘ s)) := by
        refine span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        exact hn i hi
      let := Module.Finite.span_of_finite K (Set.finite_range (u ∘ s))
      have hdim := Submodule.finrank_mono hle
      rw [finrank_span_eq_card hs, Fintype.card_fin] at hdim
      have := h (Fin.last k)
      simp only [Fin.val_last] at this
      omega
    obtain ⟨i, hi, hui⟩ := hex
    refine ⟨Fin.snoc s i, ?_, ?_⟩
    · simpa only [Fin.comp_snoc] using hs.finSnoc hui
    · intro j
      exact Fin.lastCases (by simpa using hi) (fun j ↦ by simpa using hsm j) j

section FieldTowers

variable {F E W : Type*} [Field F] [DivisionRing E] [Algebra F K] [Algebra F E]
  [Module.Finite F K] [Module F V] [IsScalarTower F K V]
  [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]

/-- From `[K : F] * k` vectors with independent images under an `F`-linear map, select
`k` vectors independent over `K`. With zero-based indices, the `j`-th selected vector
occurs no later than `[K : F] * j` in the original family. -/
theorem exists_linearIndependent_comp_finrank_mul {k : ℕ}
    {f : V →ₗ[F] W} {u : Fin (finrank F K * k) → V}
    (h : LinearIndependent E (f ∘ u)) :
    ∃ s : Fin k → Fin (finrank F K * k),
      LinearIndependent K (u ∘ s) ∧ ∀ j, (s j : ℕ) ≤ finrank F K * (j : ℕ) := by
  classical
  refine exists_linearIndependent_comp_of_lt_finrank_span ?_
  intro j
  have hD : 0 < finrank F K := Module.finrank_pos
  have hbound : finrank F K * (j : ℕ) + 1 ≤ finrank F K * k := by
    have := Nat.mul_le_mul_left (finrank F K) j.isLt
    nlinarith
  let e := Fin.castLEEmb hbound
  have hcount : finrank F K * (j : ℕ) + 1 ≤
      finrank F K * finrank K (span K (Set.range (u ∘ e))) := by
    simpa only [Fintype.card_fin] using
      (h.comp e e.injective).card_le_finrank_mul (K := K) (u := u ∘ e)
  have hle : span K (Set.range (u ∘ e)) ≤
      span K (u '' {i | (i : ℕ) ≤ finrank F K * (j : ℕ)}) := by
    refine span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, by simpa [e] using Nat.le_of_lt_succ i.isLt, rfl⟩
  let := Module.Finite.span_of_finite K
    ((Set.toFinite {i : Fin (finrank F K * k) | (i : ℕ) ≤ finrank F K * (j : ℕ)}).image u)
  have hdim := Submodule.finrank_mono hle
  by_contra! hj
  have := Nat.mul_le_mul_left (finrank F K) (hdim.trans hj)
  omega

end FieldTowers

end TauCeti
