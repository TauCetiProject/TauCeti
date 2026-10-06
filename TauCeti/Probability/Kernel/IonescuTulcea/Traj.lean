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
  rw [Measure.compProd_eq_comp_prod, trajMeasure, Measure.map_comp _ _ (by fun_prop),
    traj_map_frestrictLe, Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply _ (by fun_prop),
    partialTraj_compProd_eq_map_traj zero_le]

end ProbabilityTheory.Kernel
