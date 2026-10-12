/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Trajectory measures with s-finite initial laws

The Ionescu--Tulcea trajectory measure can start from an s-finite measure. Its joint law of a
finite prefix and the following coordinate is the composition-product of the prefix law and the
next transition kernel. This identity lets finite transport plans be glued without normalization.

The result and proof generalize Mathlib's
`ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, which assumes
a probability initial law.
-/

public section

open Finset MeasureTheory Preorder
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)}

/-- An s-finite initial law gives an s-finite trajectory measure. -/
instance trajMeasure.instSFinite [SFinite μ₀] : SFinite (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  infer_instance

/-- A finite initial law gives a finite trajectory measure. -/
instance trajMeasure.instIsFiniteMeasure [IsFiniteMeasure μ₀] :
    IsFiniteMeasure (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  infer_instance

/-- For an s-finite initial law, the joint law of the prefix through time `n` and the next
coordinate is the composition-product of the prefix law and the transition kernel at `n`. -/
theorem map_frestrictLe_trajMeasure_compProd_of_sFinite [SFinite μ₀] (n : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe n) ⊗ₘ κ n =
      (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
  let ν : Measure ((i : Iic 0) → X i) := μ₀.map (MeasurableEquiv.piUnique _).symm
  have hproj : Measurable (fun x : (k : ℕ) → X k ↦ (frestrictLe n x, x (n + 1))) :=
    by fun_prop
  have hprefix : (trajMeasure μ₀ κ).map (frestrictLe n) = partialTraj κ 0 n ∘ₘ ν := by
    simp [trajMeasure, ν, Measure.map_comp _ _ (measurable_frestrictLe n), traj_map_frestrictLe]
  have hstep : (Kernel.id ×ₖ κ n) ∘ₖ partialTraj κ 0 n =
      (traj κ 0).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
    ext x₀ : 1
    simpa [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply _ hproj] using
      (partialTraj_compProd_eq_map_traj (κ := κ) (x₀ := x₀) (Nat.zero_le n))
  calc
    (trajMeasure μ₀ κ).map (frestrictLe n) ⊗ₘ κ n
        = (Kernel.id ×ₖ κ n) ∘ₘ (partialTraj κ 0 n ∘ₘ ν) := by
            simp [hprefix, Measure.compProd_eq_comp_prod]
    _ = ((Kernel.id ×ₖ κ n) ∘ₖ partialTraj κ 0 n) ∘ₘ ν := Measure.comp_assoc
    _ = (traj κ 0).map (fun x ↦ (frestrictLe n x, x (n + 1))) ∘ₘ ν := by rw [hstep]
    _ = (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
          simp [trajMeasure, ν, Measure.map_comp _ _ hproj]

end ProbabilityTheory.Kernel
