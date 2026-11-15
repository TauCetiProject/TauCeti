/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Fibrewise radial compression

Radial compression in each real seminormed fibre sends the whole fibre bijectively onto
its open unit ball. These maps preserve base points, fix the zero section, and have explicit
square-root formulas and inverse identities. They are the fibre maps used to parametrize
bounded bundle neighbourhoods by an entire vector bundle.

The construction uses Mathlib's `OpenPartialHomeomorph.univUnitBall`, by Yury Kudryashov
and Oliver Nash, separately in each fibre. Regularity on a bundle total space additionally
requires regularity of the fibre norm.
-/

public noncomputable section

open Bundle Set Metric

namespace Bundle.TotalSpace

variable {B : Type*} {V : B → Type*} {F : Type*}

variable [∀ b, SeminormedAddCommGroup (V b)] [∀ b, NormedSpace ℝ (V b)]

/-- Compress each fibre into its open unit ball, preserving the base point. -/
def radialMap (p : TotalSpace F V) : TotalSpace F V :=
  ⟨p.proj, OpenPartialHomeomorph.univUnitBall p.2⟩

/-- Expand the open unit ball in each fibre to the whole fibre. The inverse identities
for this map hold on the open unit ball bundle. -/
def radialInverse (p : TotalSpace F V) : TotalSpace F V :=
  ⟨p.proj, OpenPartialHomeomorph.univUnitBall.symm p.2⟩

/-- Radial compression in fibre coordinates. -/
theorem radialMap_apply (p : TotalSpace F V) :
    radialMap p =
      ⟨p.proj, (Real.sqrt (1 + ‖p.2‖ ^ 2))⁻¹ • p.2⟩ := by
  simp [radialMap, OpenPartialHomeomorph.univUnitBall_apply]

/-- Radial expansion in fibre coordinates. -/
theorem radialInverse_apply (p : TotalSpace F V) :
    radialInverse p =
      ⟨p.proj, (Real.sqrt (1 - ‖p.2‖ ^ 2))⁻¹ • p.2⟩ := by
  simp [radialInverse, OpenPartialHomeomorph.univUnitBall_symm_apply]

/-- Every compressed vector lies in the open unit ball of its fibre. -/
@[simp] theorem norm_radialMap_lt_one (p : TotalSpace F V) : ‖(radialMap p).2‖ < 1 := by
  exact mem_ball_zero_iff.mp
    ((OpenPartialHomeomorph.univUnitBall (E := V p.proj)).map_source (mem_univ p.2))

/-- Radial compression preserves the bundle projection. -/
@[simp] theorem radialMap_proj (p : TotalSpace F V) :
    (radialMap p).proj = p.proj := (rfl)

/-- Radial expansion preserves the bundle projection. -/
@[simp] theorem radialInverse_proj (p : TotalSpace F V) :
    (radialInverse p).proj = p.proj := (rfl)

/-- Radial compression fixes the zero section. -/
@[simp] theorem radialMap_zeroSection (b : B) :
    radialMap (zeroSection F V b) = zeroSection F V b := by
  dsimp [radialMap, zeroSection]
  congr 1
  exact OpenPartialHomeomorph.univUnitBall_apply_zero

/-- Radial expansion fixes the zero section. -/
@[simp] theorem radialInverse_zeroSection (b : B) :
    radialInverse (zeroSection F V b) = zeroSection F V b := by
  dsimp [radialInverse, zeroSection]
  congr 1
  exact OpenPartialHomeomorph.univUnitBall_symm_apply_zero

/-- Expansion undoes compression on the entire total space. -/
@[simp] theorem radialInverse_map (p : TotalSpace F V) :
    radialInverse (radialMap p) = p := by
  rcases p with ⟨b, v⟩
  exact congrArg (fun w : V b => (⟨b, w⟩ : TotalSpace F V))
    ((OpenPartialHomeomorph.univUnitBall (E := V b)).left_inv (mem_univ v))

/-- Compression undoes expansion on the open unit ball bundle. -/
@[simp] theorem radialMap_inverse (p : TotalSpace F V) (hp : ‖p.2‖ < 1) :
    radialMap (radialInverse p) = p := by
  rcases p with ⟨b, v⟩
  exact congrArg (fun w : V b => (⟨b, w⟩ : TotalSpace F V))
    ((OpenPartialHomeomorph.univUnitBall (E := V b)).right_inv (mem_ball_zero_iff.mpr hp))

end Bundle.TotalSpace
