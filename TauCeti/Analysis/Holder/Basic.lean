/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.HolderNorm

import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder spaces

This file records the carrier and canonical norm estimates for the zeroth-order global Hölder
space. The carrier is a submodule of bounded continuous maps, using Mathlib's existing
`MemHolder` predicate and `nnHolderNorm` seminorm.

## Main declarations

* `TauCeti.holderNorm`: the supremum-plus-Hölder norm on bounded continuous maps;
* `TauCeti.holderSubmodule`: the `𝕜`-submodule of bounded continuous Hölder functions;
* `TauCeti.holderNorm_nonneg`, `TauCeti.norm_le_holderNorm`, and
  `TauCeti.nnHolderNorm_le_holderNorm`: basic bounds;
* `TauCeti.holderNorm_add_le`, `TauCeti.holderNorm_smul`, and
  `TauCeti.holderNorm_sub_le_holderNorm_sub_add_holderNorm_sub`: norm estimates.
-/

public section
noncomputable section

namespace TauCeti

open scoped NNReal BoundedContinuousFunction

universe u v

variable {X : Type u} {Y : Type v} [MetricSpace X] [NormedAddCommGroup Y]

/-- The supremum-plus-Hölder norm on bounded continuous maps. For a map that is not `α`-Hölder,
`nnHolderNorm` takes the junk value `0`, so this is then just the supremum norm. -/
def holderNorm (α : ℝ≥0) (f : X →ᵇ Y) : ℝ := ‖f‖ + nnHolderNorm α (f : X → Y)

/-- The defining formula for `holderNorm`. -/
theorem holderNorm_def (α : ℝ≥0) (f : X →ᵇ Y) :
    holderNorm α f = ‖f‖ + nnHolderNorm α (f : X → Y) := by
  rfl

/-- The zero function has zero supremum-plus-Hölder norm. -/
@[simp]
theorem holderNorm_zero (α : ℝ≥0) : holderNorm α (0 : X →ᵇ Y) = 0 := by
  simp [holderNorm_def]

/-- The supremum-plus-Hölder norm is nonnegative. -/
theorem holderNorm_nonneg {α : ℝ≥0} (f : X →ᵇ Y) : 0 ≤ holderNorm α f :=
  add_nonneg (norm_nonneg f) NNReal.zero_le_coe

/-- The supremum norm is bounded by the supremum-plus-Hölder norm. -/
theorem norm_le_holderNorm {α : ℝ≥0} (f : X →ᵇ Y) :
    ‖f‖ ≤ holderNorm α f :=
  le_add_of_nonneg_right NNReal.zero_le_coe

/-- The Hölder seminorm is bounded by the supremum-plus-Hölder norm. -/
theorem nnHolderNorm_le_holderNorm {α : ℝ≥0} (f : X →ᵇ Y) :
    (nnHolderNorm α (f : X → Y) : ℝ) ≤ holderNorm α f :=
  le_add_of_nonneg_left (norm_nonneg f)

/-- Subadditivity of the supremum-plus-Hölder norm for Hölder maps. -/
theorem holderNorm_add_le {α : ℝ≥0} (f g : X →ᵇ Y)
    (hf : MemHolder α (f : X → Y)) (hg : MemHolder α (g : X → Y)) :
    holderNorm α (f + g) ≤ holderNorm α f + holderNorm α g := by
  simp only [holderNorm_def, FunLike.coe_add]
  calc
    ‖f + g‖ + (nnHolderNorm α ((f : X → Y) + (g : X → Y)) : ℝ) ≤
        (‖f‖ + ‖g‖) + (nnHolderNorm α (f : X → Y) + nnHolderNorm α (g : X → Y)) :=
      add_le_add (norm_add_le _ _) (by exact_mod_cast hf.nnHolderNorm_add_le hg)
    _ = (‖f‖ + (nnHolderNorm α (f : X → Y) : ℝ)) +
          (‖g‖ + (nnHolderNorm α (g : X → Y) : ℝ)) := add_add_add_comm _ _ _ _

/-- Scalar homogeneity of the supremum-plus-Hölder norm, for every bounded continuous map, whether
or not it is `α`-Hölder. -/
@[simp]
theorem holderNorm_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
    {α : ℝ≥0} (c : 𝕜) (f : X →ᵇ Y) :
    holderNorm α (c • f) = ‖c‖ * holderNorm α f := by
  -- Mathlib's `NormedSpace` instance on `X →ᵇ Y` needs a normed field, so the homogeneity of the
  -- supremum norm over a normed ring is computed from its definition as a supremum.
  have hsup : ‖c • f‖ = ‖c‖ * ‖f‖ := by
    simp only [BoundedContinuousFunction.norm_eq_iSup_norm, smul_apply, norm_smul,
      ← Real.mul_iSup_of_nonneg (norm_nonneg c)]
  simp only [holderNorm_def, hsup, FunLike.coe_smul, nnHolderNorm_smul, NNReal.coe_mul,
    coe_nnNorm, mul_add]

/-- Triangle inequality for the supremum-plus-Hölder norm of a difference through an intermediate
map `g`. Only the two differences `f - g` and `g - h` need to be `α`-Hölder. -/
theorem holderNorm_sub_le_holderNorm_sub_add_holderNorm_sub {α : ℝ≥0} (f g h : X →ᵇ Y)
    (hfg : MemHolder α ((f - g : X →ᵇ Y) : X → Y))
    (hgh : MemHolder α ((g - h : X →ᵇ Y) : X → Y)) :
    holderNorm α (f - h) ≤ holderNorm α (f - g) + holderNorm α (g - h) := by
  rw [← sub_add_sub_cancel f g h]
  exact holderNorm_add_le _ _ hfg hgh

variable (𝕜 : Type*) [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]

/-- The `𝕜`-submodule of bounded continuous `α`-Hölder functions. -/
def holderSubmodule (α : ℝ≥0) : Submodule 𝕜 (X →ᵇ Y) where
  carrier := {f | MemHolder α (f : X → Y)}
  zero_mem' := memHolder_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun _ _ hf => hf.smul

variable {𝕜}

/-- Membership in `holderSubmodule` is exactly the global Hölder predicate. -/
@[simp]
theorem mem_holderSubmodule_iff {α : ℝ≥0} (f : X →ᵇ Y) :
    f ∈ holderSubmodule 𝕜 α ↔ MemHolder α (f : X → Y) := Iff.rfl

namespace holderSubmodule

variable {α : ℝ≥0}

/-- An element of `holderSubmodule 𝕜 α` satisfies the global `α`-Hölder condition. -/
theorem memHolder (f : holderSubmodule (X := X) (Y := Y) 𝕜 α) :
    MemHolder α (f : X → Y) := f.2

/-- An element of `holderSubmodule 𝕜 α` is `α`-Hölder with constant equal to its Hölder
seminorm. -/
theorem holderWith (f : holderSubmodule (X := X) (Y := Y) 𝕜 α) :
    HolderWith (nnHolderNorm α (f : X → Y)) α (f : X → Y) :=
  (holderSubmodule.memHolder f).holderWith

end holderSubmodule

end TauCeti
