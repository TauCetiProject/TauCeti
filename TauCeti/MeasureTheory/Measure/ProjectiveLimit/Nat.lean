/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Projective limits on sequences

This file proves a sequence-indexed version of Kolmogorov's extension theorem when every
positive-indexed coordinate is standard Borel. Mathlib defines projective measure families and
proves uniqueness of their projective limits, while its Ionescu--Tulcea construction produces a
path law from a sequence of transition kernels. Here those kernels are the conditional
distributions of each next coordinate given the current prefix, taken under a coherent family of
finite-prefix laws.

## Main results

* `TauCeti.Measure.exists_map_frestrictLe_eq` constructs a probability measure on a dependent
  sequence whose finite-prefix laws are a prescribed coherent family.
* `TauCeti.Measure.exists_isProjectiveLimit_nat` realizes a projective family indexed by finite
  subsets of `ℕ`.

These results are the existence counterpart of Mathlib's `MeasureTheory.IsProjectiveLimit.unique`.
The construction follows the standard proof of Kolmogorov extension for countable products by
successive disintegration, combined with Mathlib's Ionescu--Tulcea theorem
(`ProbabilityTheory.Kernel.trajMeasure`).
-/

public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

/-- Split a trajectory through time `n + 1` into its prefix through time `n` and its last
coordinate. -/
private def prefixSuccEquiv (n : ℕ) :
    ((∀ i : Iic n, X i) × X (n + 1)) ≃ᵐ (∀ i : Iic (n + 1), X i) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n)).trans
    (MeasurableEquiv.IicProdIoc n.le_succ)

private theorem coe_prefixSuccEquiv_symm (n : ℕ) :
    ⇑(prefixSuccEquiv (X := X) n).symm =
      fun x ↦ (frestrictLe₂ n.le_succ x, x ⟨n + 1, mem_Iic.2 le_rfl⟩) := rfl

private theorem prefixSuccEquiv_symm_comp_frestrictLe (n : ℕ) :
    (prefixSuccEquiv (X := X) n).symm ∘ frestrictLe (n + 1) =
      fun x ↦ (frestrictLe n x, x (n + 1)) := rfl

/-- The Ionescu--Tulcea path law whose `n`-th transition kernel is the conditional law of
coordinate `n + 1` given the prefix through time `n` under the prescribed law `P (n + 1)`. -/
private def prefixLimit (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, StandardBorelSpace (X (n + 1))]
    [∀ n, Nonempty (X (n + 1))] : Measure (∀ n, X n) :=
  Kernel.trajMeasure ((P 0).map (MeasurableEquiv.piUnique _)) fun n ↦
    condDistrib (fun x ↦ x ⟨n + 1, mem_Iic.2 le_rfl⟩) (frestrictLe₂ n.le_succ) (P (n + 1))

private theorem map_frestrictLe_zero_prefixLimit
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))] :
    (prefixLimit P).map (frestrictLe 0) = P 0 := by
  -- Through time `0`, the path law is its initial law, transported back along `piUnique`.
  calc (prefixLimit P).map (frestrictLe 0)
      = ((P 0).map (MeasurableEquiv.piUnique _)).map (MeasurableEquiv.piUnique _).symm := by
        simp [prefixLimit, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
          Kernel.traj_map_frestrictLe]
    _ = P 0 := MeasurableEquiv.map_symm_map _

private theorem map_frestrictLe_succ_prefixLimit
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))]
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ n.le_succ) = P n) {n : ℕ}
    (hn : (prefixLimit P).map (frestrictLe n) = P n) :
    (prefixLimit P).map (frestrictLe (n + 1)) = P (n + 1) := by
  -- The `n`-th transition kernel of `prefixLimit P`.
  let κ :=
    condDistrib (fun x ↦ x ⟨n + 1, mem_Iic.2 le_rfl⟩) (frestrictLe₂ n.le_succ) (P (n + 1))
  -- Compare both laws after splitting off the last coordinate.
  apply (prefixSuccEquiv n).symm.map_measurableEquiv_injective
  calc ((prefixLimit P).map (frestrictLe (n + 1))).map (prefixSuccEquiv n).symm
      = (prefixLimit P).map fun x ↦ (frestrictLe n x, x (n + 1)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop), prefixSuccEquiv_symm_comp_frestrictLe]
    -- The path law is its prefix law through time `n` followed by the `n`-th kernel.
    _ = (prefixLimit P).map (frestrictLe n) ⊗ₘ κ := by
        rw [prefixLimit]; exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
    _ = (P (n + 1)).map (frestrictLe₂ n.le_succ) ⊗ₘ κ := by rw [hn, hP]
    -- Disintegrating `P (n + 1)` along its prefix through time `n` recovers it.
    _ = (P (n + 1)).map fun x ↦ (frestrictLe₂ n.le_succ x, x ⟨n + 1, mem_Iic.2 le_rfl⟩) :=
        compProd_map_condDistrib (by fun_prop) (measurable_pi_apply _).aemeasurable
    _ = (P (n + 1)).map (prefixSuccEquiv n).symm := by rw [coe_prefixSuccEquiv_symm]

/-- **Countable projective-family extension for coherent prefixes.** A coherent family of
probability laws on the prefixes `∀ i : Iic n, X i` of a dependent sequence of standard Borel
spaces, except that the zeroth coordinate need only be measurable, is realized by a probability
law on the whole sequence.

The result is stated directly in terms of prefix laws because this is the interface consumed by
countable gluing constructions. Together with Mathlib's
`MeasureTheory.isProjectiveMeasureFamily_inducedFamily` and
`MeasureTheory.isProjectiveLimit_nat_iff`, it gives the usual `Finset ℕ` formulation. -/
theorem exists_map_frestrictLe_eq [∀ n, StandardBorelSpace (X (n + 1))]
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ n.le_succ) = P n) :
    ∃ μ : Measure (∀ n, X n), IsProbabilityMeasure μ ∧
      ∀ n, μ.map (frestrictLe n) = P n := by
  have (n : ℕ) : Nonempty (X (n + 1)) :=
    (nonempty_of_isProbabilityMeasure (P (n + 1))).map fun x ↦ x ⟨n + 1, mem_Iic.2 le_rfl⟩
  refine ⟨prefixLimit P, by rw [prefixLimit]; infer_instance, fun n ↦ ?_⟩
  induction n with
  | zero => exact map_frestrictLe_zero_prefixLimit P
  | succ n hn => exact map_frestrictLe_succ_prefixLimit P hP hn

/-- **Kolmogorov extension for a sequence with standard Borel positive coordinates.** Every
projective family of probability laws indexed by the finite subsets of `ℕ` has a projective limit,
which is again a probability measure.

This is the existence counterpart of Mathlib's uniqueness theorem
`MeasureTheory.IsProjectiveLimit.unique`. -/
theorem exists_isProjectiveLimit_nat [∀ n, StandardBorelSpace (X (n + 1))]
    (P : ∀ I : Finset ℕ, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ n, X n), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  have hprefix : ∀ n, (P (Iic (n + 1))).map (frestrictLe₂ n.le_succ) = P (Iic n) :=
    fun n => (hP (Iic (n + 1)) (Iic n) (Iic_subset_Iic.mpr n.le_succ)).symm
  obtain ⟨μ, hμprob, hμ⟩ := exists_map_frestrictLe_eq (fun n => P (Iic n)) hprefix
  exact ⟨μ, hμprob, (isProjectiveLimit_nat_iff hP μ).mpr hμ⟩

end Measure

end TauCeti
