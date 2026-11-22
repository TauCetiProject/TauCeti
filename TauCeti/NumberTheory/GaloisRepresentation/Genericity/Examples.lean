/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Genericity.DecomposedGeneric
public import Mathlib.Algebra.Field.ZMod
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# Examples of generic Frobenius eigenvalues

Concrete checks of `TauCeti.IsGenericEigenvalues`, `TauCeti.IsStronglyGenericEigenvalues` and
their matrix and representation forms over small prime fields. They separate the two conditions
from each other and from pairwise distinctness, and show that genericity depends on `q`.

* Over `𝔽₃` with `q = 2`, the repeated pair `(1, 1)` is generic but not strongly generic, so the
  identity matrix and the trivial representation of rank two are generic but not strongly
  generic.
* Over `𝔽₃` with `q = 1`, the same pair is not generic: changing the residue cardinality changes
  the answer.
* Over `𝔽₅` with `q = 2`, the distinct pair `(2, 1)` is not generic, since `2 = 2 · 1`.
* Over `𝔽₇` with `q = 2`, the pair `(1, 3)` is strongly generic: its two ratios are `5` and `3`.
* A nontrivial element in the image of `I` makes both representation conditions fail, whatever
  the eigenvalues of the Frobenius element.
* For `F = ℚ` and the trivial representation of rank two over `𝔽₃`, the prime `2` is decomposed
  generic but `7` is not: `7 ≡ 1 (mod 3)`, so the repeated eigenvalue `1` has ratio `7` with
  itself in `𝔽₃`. In particular this reducible representation is decomposed generic.
-/

public section

namespace TauCeti.GenericityExamples

open Matrix

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- Over `𝔽₃` with `q = 2`, the repeated pair `(1, 1)` is generic. -/
theorem isGenericEigenvalues_one_one : IsGenericEigenvalues (2 : ZMod 3) ![1, 1] := by
  rw [isGenericEigenvalues_iff]
  decide

/-- Over `𝔽₃` with `q = 2`, the repeated pair `(1, 1)` is not strongly generic. -/
theorem not_isStronglyGenericEigenvalues_one_one :
    ¬ IsStronglyGenericEigenvalues (2 : ZMod 3) ![1, 1] := by
  rw [isStronglyGenericEigenvalues_iff]
  decide

/-- Over `𝔽₃` with `q = 1`, the repeated pair `(1, 1)` is not generic. -/
theorem not_isGenericEigenvalues_one_one_of_q_eq_one :
    ¬ IsGenericEigenvalues (1 : ZMod 3) ![1, 1] := by
  rw [isGenericEigenvalues_iff]
  decide

/-- Over `𝔽₅` with `q = 2`, the distinct pair `(2, 1)` is not generic. -/
theorem not_isGenericEigenvalues_two_one : ¬ IsGenericEigenvalues (2 : ZMod 5) ![2, 1] := by
  rw [isGenericEigenvalues_iff]
  decide

/-- Over `𝔽₇` with `q = 2`, the pair `(1, 3)` is strongly generic. -/
theorem isStronglyGenericEigenvalues_one_three :
    IsStronglyGenericEigenvalues (2 : ZMod 7) ![1, 3] := by
  rw [isStronglyGenericEigenvalues_iff]
  decide

/-- The constant pair `(1, 1)` written as a vector. -/
private theorem one_one_eq : (![1, 1] : Fin 2 → ZMod 3) = fun _ ↦ 1 := by
  ext i
  fin_cases i <;> rfl

/-- Over `𝔽₃` with `q = 2`, the rank-two identity matrix is generic but not strongly generic. -/
theorem isGenericAt_one_and_not_isStronglyGenericAt_one :
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)).IsGenericAt 2 ∧
      ¬ (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)).IsStronglyGenericAt 2 := by
  rw [← diagonal_one, ← one_one_eq, isGenericAt_diagonal_iff, isStronglyGenericAt_diagonal_iff]
  exact ⟨isGenericEigenvalues_one_one, not_isStronglyGenericEigenvalues_one_one⟩

/-- Over `𝔽₅` with `q = 2`, the diagonal matrix `diag(2, 1)` is not generic, although its
eigenvalues are distinct. -/
theorem not_isGenericAt_diagonal_two_one :
    ¬ (diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)).IsGenericAt 2 := by
  rw [isGenericAt_diagonal_iff]
  exact not_isGenericEigenvalues_two_one

/-- Over `𝔽₇` with `q = 2`, the diagonal matrix `diag(1, 3)` is strongly generic. -/
theorem isStronglyGenericAt_diagonal_one_three :
    (diagonal ![1, 3] : Matrix (Fin 2) (Fin 2) (ZMod 7)).IsStronglyGenericAt 2 := by
  rw [isStronglyGenericAt_diagonal_iff]
  exact isStronglyGenericEigenvalues_one_three

/-- The trivial representation of rank two over `𝔽₃` is generic at `q = 2` but not at `q = 1`,
and is not strongly generic at `q = 2`, for every group `G`, subgroup `I` and element
`frob`. -/
theorem isGenericAt_one_and_not_isGenericAt_one_one_and_not_isStronglyGenericAt_one {G : Type*}
    [Group G] (I : Subgroup G) (frob : G) :
    (1 : G →* GL (Fin 2) (ZMod 3)).IsGenericAt I frob 2 ∧
      ¬ (1 : G →* GL (Fin 2) (ZMod 3)).IsGenericAt I frob 1 ∧
      ¬ (1 : G →* GL (Fin 2) (ZMod 3)).IsStronglyGenericAt I frob 2 := by
  have hdiag : ((1 : G →* GL (Fin 2) (ZMod 3)) frob : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      diagonal ![1, 1] := by
    rw [one_one_eq, diagonal_one, MonoidHom.one_apply, Units.val_one]
  have hker : I ≤ (1 : G →* GL (Fin 2) (ZMod 3)).ker := by simp
  rw [MonoidHom.isGenericAt_iff_of_coe_eq_diagonal hdiag,
    MonoidHom.isGenericAt_iff_of_coe_eq_diagonal hdiag,
    MonoidHom.isStronglyGenericAt_iff_of_coe_eq_diagonal hdiag]
  exact ⟨⟨hker, isGenericEigenvalues_one_one⟩,
    fun h ↦ not_isGenericEigenvalues_one_one_of_q_eq_one h.2,
    fun h ↦ not_isStronglyGenericEigenvalues_one_one h.2⟩

/-- An element of `I` acting nontrivially makes both representation conditions fail. -/
theorem not_isGenericAt_of_mem_of_ne_one {G n K : Type*} [Group G] [Fintype n] [DecidableEq n]
    [Field K] {ρ : G →* GL n K} {I : Subgroup G} {g : G} (hg : g ∈ I) (hρg : ρ g ≠ 1)
    (frob : G) (q : K) :
    ¬ ρ.IsGenericAt I frob q ∧ ¬ ρ.IsStronglyGenericAt I frob q :=
  ⟨fun h ↦ hρg (h.le_ker hg), fun h ↦ hρg (h.le_ker hg)⟩

section DecomposedGeneric

open Ideal Module
open scoped _root_.NumberField

/-- Every rational prime splits completely in `ℚ`: there is one prime of `𝓞 ℚ` above it. -/
private theorem ncard_primesOver_rat (p : ℕ) [Fact p.Prime] :
    ((span {(p : ℤ)}).primesOver (𝓞 ℚ)).ncard = finrank ℚ ℚ := by
  obtain ⟨Q, hQ⟩ : ((span {(p : ℤ)}).primesOver (𝓞 ℚ)).Nonempty :=
    Set.nonempty_coe_sort.mp inferInstance
  have := hQ.1
  have := hQ.2
  exact (_root_.NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot ℚ ℚ _ Q).mpr
    (Subsingleton.elim _ _)

/-- For `F = ℚ`, the prime `2` is decomposed generic for the trivial representation of rank two
over `𝔽₃`. -/
theorem isDecomposedGenericPrime_one_two :
    (1 : Gal(ℚ/ℚ) →* GL (Fin 2) (ZMod 3)).IsDecomposedGenericPrime 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine MonoidHom.isDecomposedGenericPrime_iff.mpr
    ⟨Nat.prime_two, by decide, ncard_primesOver_rat 2, fun Q _ _ σ _ ↦ ?_⟩
  exact_mod_cast (isGenericAt_one_and_not_isGenericAt_one_one_and_not_isStronglyGenericAt_one _
    σ).1

/-- For `F = ℚ`, the prime `7` is not decomposed generic for the trivial representation of rank
two over `𝔽₃`, although `2` is: `7 = 1` in `𝔽₃`. -/
theorem not_isDecomposedGenericPrime_one_seven :
    ¬ (1 : Gal(ℚ/ℚ) →* GL (Fin 2) (ZMod 3)).IsDecomposedGenericPrime 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro h
  obtain ⟨Q, hQ⟩ : ((span {((7 : ℕ) : ℤ)}).primesOver (𝓞 ℚ)).Nonempty :=
    Set.nonempty_coe_sort.mp inferInstance
  have := hQ.1
  have := hQ.2
  obtain ⟨σ, hσ⟩ := _root_.NumberField.exists_isArithFrobAt ℚ Q
    (ne_bot_of_liesOver_of_ne_bot (p := span {((7 : ℕ) : ℤ)}) (by simp) Q)
  have h7 := h.isGenericAt Q hσ
  rw [show ((7 : ℕ) : ZMod 3) = 1 by decide] at h7
  exact (isGenericAt_one_and_not_isGenericAt_one_one_and_not_isStronglyGenericAt_one _ σ).2.1 h7

end DecomposedGeneric

end TauCeti.GenericityExamples
