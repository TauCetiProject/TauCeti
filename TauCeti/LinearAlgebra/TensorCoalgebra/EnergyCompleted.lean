/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# Energy-completed words and deconcatenation

For letters with energies `E : S → ℝ`, `EnergyCompletedWords R S E` consists of formal
linear combinations of finite words, including the empty word, with only finitely many
nonzero terms below each total-energy cutoff. In particular only finitely many lengths
occur below each cutoff. This is an energy completion of the free module on words, not
the tensor-length product `CompletedTensorWords`.

The carrier and its complete separated topology are the existing `NovikovModule`, with
potential the negative total energy. Its finite combinations are dense and its energy
truncations converge by `NovikovModule.denseRange_ofFinsupp` and
`NovikovModule.tendsto_ofFinsupp_trunc`.

Deconcatenation takes values in the energy-completed module on pairs of words, not the
algebraic tensor square. Each word has finitely many cuts, and cutting preserves total
energy, so this map is continuous and commutes with energy truncation. Coassociativity
and the counit laws are given in coefficients, including empty blocks. These are the
coalgebra operations needed before extending energy-controlled word operators.

No positivity, discreteness, injectivity or finiteness assumption on the letter energies
is needed. The finite-word support condition is essential even when all energies vanish.

The deconcatenation convention is that of J.-L. Loday and B. Vallette,
*Algebraic Operads*, Chapters 9--10, also used by `TensorWords`.
-/

public section

noncomputable section

namespace TauCeti

/-- The total energy of a word is the sum of the energies of its letters. -/
def wordEnergy {S : Type*} (E : S → ℝ) (w : List S) : ℝ := (w.map E).sum

@[simp]
theorem wordEnergy_nil {S : Type*} (E : S → ℝ) : wordEnergy E [] = 0 := by
  simp [wordEnergy]

@[simp]
theorem wordEnergy_cons {S : Type*} (E : S → ℝ) (s : S) (w : List S) :
    wordEnergy E (s :: w) = E s + wordEnergy E w := by
  simp [wordEnergy]

@[simp]
theorem wordEnergy_append {S : Type*} (E : S → ℝ) (u v : List S) :
    wordEnergy E (u ++ v) = wordEnergy E u + wordEnergy E v := by
  simp [wordEnergy]

/-- Formal combinations of finite words, finite below every total-energy cutoff.
The empty word is retained. The topology is the potential topology of `NovikovModule`. -/
abbrev EnergyCompletedWords (R S : Type*) [Semiring R] (E : S → ℝ) :=
  NovikovModule R (fun w : List S => -wordEnergy E w)

namespace EnergyCompletedWords

variable {R S : Type*} {E : S → ℝ}

section Semiring

variable [Semiring R]

/-- Below an inclusive energy cutoff, only finitely many words have nonzero coefficients. -/
theorem finite_energy_le (a : EnergyCompletedWords R S E) (C : ℝ) :
    {w | a.val w ≠ 0 ∧ wordEnergy E w ≤ C}.Finite := by
  simpa only [neg_le_neg_iff] using NovikovModule.finite_ge a (-C)

/-- Only finitely many word lengths occur below each energy cutoff. -/
theorem finite_lengths_energy_le (a : EnergyCompletedWords R S E) (C : ℝ) :
    (List.length '' {w | a.val w ≠ 0 ∧ wordEnergy E w ≤ C}).Finite :=
  (finite_energy_le a C).image List.length

private def cutKernel (w : List S) (p : List S × List S) : R := by
  classical
  exact if p.1 ++ p.2 = w then 1 else 0

private theorem cutKernel_bound (w : List S) (p : List S × List S)
    (h : cutKernel (R := R) w p ≠ 0) :
    -(wordEnergy E p.1 + wordEnergy E p.2) ≤ -wordEnergy E w + 0 := by
  classical
  have hp : p.1 ++ p.2 = w := by
    by_contra hp
    simp [cutKernel, hp] at h
  simp [← hp]

private theorem cutKernel_mem (w : List S) :
    cutKernel (R := R) w ∈ NovikovModule R
      (fun p : List S × List S => -(wordEnergy E p.1 + wordEnergy E p.2)) := by
  classical
  apply NovikovModule.mem_of_finite_support
  apply (Set.toFinite (↑(Finset.range (w.length + 1)) : Set ℕ)).image
    (fun n => (w.take n, w.drop n)) |>.subset
  intro p hp
  have hw : p.1 ++ p.2 = w := by
    by_contra hw
    simp [cutKernel, hw] at hp
  refine ⟨p.1.length, ?_, ?_⟩
  · simp only [Finset.mem_coe, Finset.mem_range, ← hw, List.length_append]
    omega
  · simp [← hw]

/-- Deconcatenation into the energy-completed square. The coefficient of `(u,v)` is
exactly the coefficient of `u ++ v` in the input. -/
def deconcatenation : EnergyCompletedWords R S E →ₗ[R]
    NovikovModule R (fun p : List S × List S =>
      -(wordEnergy E p.1 + wordEnergy E p.2)) :=
  NovikovModule.kernelMap cutKernel_bound cutKernel_mem

/-- Each cut reads the coefficient of the concatenated word; no infinite sum is needed. -/
@[simp]
theorem deconcatenation_apply_val (a : EnergyCompletedWords R S E) (u v : List S) :
    (deconcatenation a).val (u, v) = a.val (u ++ v) := by
  classical
  rw [deconcatenation, NovikovModule.kernelMap_apply_val,
    finsum_eq_single _ (u ++ v)]
  · simp [cutKernel]
  · intro w hw
    simp [cutKernel, Ne.symm hw]

/-- The coefficient form of coassociativity: cutting the first block or the second
block gives the same coefficient at every triple of words. -/
theorem deconcatenation_coassoc (a : EnergyCompletedWords R S E) (u v w : List S) :
    (deconcatenation a).val (u ++ v, w) =
      (deconcatenation a).val (u, v ++ w) := by
  simp [List.append_assoc]

/-- Deconcatenation on a finite basis word is the sum of all its cuts, each with the
original coefficient. This formula includes both empty-block cuts. -/
@[simp↓]
theorem deconcatenation_single_apply_val [DecidableEq S] (w u v : List S) (r : R) :
    (deconcatenation (NovikovModule.single w r : EnergyCompletedWords R S E)).val (u, v) =
      if u ++ v = w then r else 0 := by
  simp only [deconcatenation_apply_val, NovikovModule.single_val, Pi.single_apply]

/-- The counit extracts the coefficient of the empty word. -/
def counit : EnergyCompletedWords R S E →ₗ[R] R :=
  (LinearMap.proj []) ∘ₗ (NovikovModule R (fun w : List S => -wordEnergy E w)).subtype

@[simp]
theorem counit_apply (a : EnergyCompletedWords R S E) : counit a = a.val [] :=
  (rfl)

/-- The left counit identity in coefficients. -/
@[simp↓]
theorem counit_left (a : EnergyCompletedWords R S E) (w : List S) :
    (deconcatenation a).val ([], w) = a.val w := by
  simp

/-- The right counit identity in coefficients. -/
@[simp↓]
theorem counit_right (a : EnergyCompletedWords R S E) (w : List S) :
    (deconcatenation a).val (w, []) = a.val w := by
  simp

/-- Coaugmentation includes a scalar as a multiple of the empty word. -/
def coaugmentation : R →ₗ[R] EnergyCompletedWords R S E :=
  (NovikovModule.ofFinsupp _) ∘ₗ Finsupp.lsingle []

@[simp]
theorem coaugmentation_apply_val (r : R) (w : List S) :
    (coaugmentation (E := E) r).val w = if w = [] then r else 0 := by
  classical
  simp [coaugmentation, Finsupp.single_apply, eq_comm]

/-- The counit is a retraction of the coaugmentation. -/
@[simp↓]
theorem counit_coaugmentation (r : R) : counit (coaugmentation (E := E) r) = r := by
  simp

/-- The empty word is group-like in the completed square. -/
@[simp↓]
theorem deconcatenation_coaugmentation_apply_val (r : R) (u v : List S) :
    (deconcatenation (coaugmentation (E := E) r)).val (u, v) =
      if u = [] ∧ v = [] then r else 0 := by
  simp

/-- Cutting commutes exactly with total-energy truncation. Native truncation at
potential `-C` keeps words of energy strictly less than `C`. -/
theorem deconcatenation_ofFinsupp_trunc (a : EnergyCompletedWords R S E) (C : ℝ) :
    deconcatenation (E := E) (NovikovModule.ofFinsupp _ (NovikovModule.trunc (-C) a)) =
      NovikovModule.ofFinsupp _ (NovikovModule.trunc (-C) (deconcatenation a)) := by
  ext ⟨u, v⟩
  simp [NovikovModule.trunc_apply]

end Semiring

section Ring

variable [Ring R]

/-- Deconcatenation preserves each total-energy neighbourhood, uniformly over all
word lengths. -/
theorem deconcatenation_mem_potentialFiltration {C : ℝ}
    {a : EnergyCompletedWords R S E}
    (ha : a ∈ NovikovModule.potentialFiltration R (fun w => -wordEnergy E w) C) :
    deconcatenation a ∈ NovikovModule.potentialFiltration R
      (fun p : List S × List S => -(wordEnergy E p.1 + wordEnergy E p.2)) C := by
  simpa only [deconcatenation, add_zero] using
    NovikovModule.kernelMap_mem_potentialFiltration cutKernel_bound cutKernel_mem ha

/-- Deconcatenation is continuous for energy completion, without a length bound. -/
@[continuity]
theorem continuous_deconcatenation : Continuous (deconcatenation (R := R) (E := E)) :=
  NovikovModule.continuous_kernelMap cutKernel_bound cutKernel_mem

end Ring

end EnergyCompletedWords

end TauCeti
