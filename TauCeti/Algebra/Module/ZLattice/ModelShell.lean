/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RealModel
public import TauCeti.Algebra.Module.ZLattice.Shell
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber

/-!
# Shells under rationalization and real scalar extension

The rational norm of an integral lattice is its self-pairing, so it becomes the squared real
norm under the comparison maps `ZLattice.ratModelMap` and
`TauCeti.IntegralLattice.realModelMap`. These maps therefore identify the rational norm shells
`IntegralLattice.vectorsOfNorm` with the real shells `ZLattice.shell`, and preserve their
cardinalities. The comparisons hold at every rational norm, including zero and negative norms,
in arbitrary rank.

The image descriptions retain the vectors themselves, while the representation-number
equalities allow counts computed in a rational lattice to be used as coefficients of the theta
series of its real model.

## Main results

* `ZLattice.shell_eq_image_vectorsOfNorm_ratModel`: rationalization identifies shells.
* `ZLattice.ncard_vectorsOfNorm_ratModel`: rational and real shell counts agree.
* `TauCeti.IntegralLattice.shell_realModel`: real scalar extension identifies shells.
* `TauCeti.IntegralLattice.representationNumber_realModel`: real scalar extension preserves
  representation numbers.

## References

* W. Ebeling, *Lattices and Codes*, Chapters 1–2.
-/

public section

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- A shell of a full integral real lattice is the image of the corresponding rational-model
norm shell under the canonical embedding. -/
theorem shell_eq_image_vectorsOfNorm_ratModel (hL : IsIntegral L) (q : ℚ) :
    shell L (q : ℝ) =
      (fun x : ratModel hL ↦ ratModelMap L x) '' (ratModel hL).vectorsOfNorm q := by
  ext x
  rw [mem_shell, Set.mem_image]
  constructor
  · rintro ⟨hx, hq⟩
    refine ⟨ratModelCarrierEquiv hL ⟨x, hx⟩, ?_, by simp⟩
    rw [TauCeti.IntegralLattice.mem_vectorsOfNorm,
      ← (Rat.cast_injective (α := ℝ)).eq_iff, ← norm_sq_ratModelMap hL]
    simpa using hq
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(mem_ratModel_carrier_iff hL y).mp y.property, ?_⟩
    rw [norm_sq_ratModelMap hL, TauCeti.IntegralLattice.mem_vectorsOfNorm.mp hy]

/-- The rational model and the original full integral real lattice have the same shell counts.
The rational norm is the squared real norm, with no factor of two. -/
theorem ncard_vectorsOfNorm_ratModel (hL : IsIntegral L) (q : ℚ) :
    ((ratModel hL).vectorsOfNorm q).ncard = representationNumber L (q : ℝ) := by
  rw [representationNumber_def, shell_eq_image_vectorsOfNorm_ratModel]
  exact (Set.ncard_image_of_injective _
    (ratModelMap_injective.comp Subtype.val_injective)).symm

end ZLattice

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (M : IntegralLattice V) (hM : M.IsPosDef)

/-- The shell of the real model is the image of the corresponding rational norm shell under
the scalar-extension map. -/
theorem shell_realModel (q : ℚ) :
    ZLattice.shell (M.realModel hM) (q : ℝ) =
      (fun x : M ↦ M.realModelMap hM x) '' M.vectorsOfNorm q := by
  ext y
  rw [ZLattice.mem_shell, Set.mem_image]
  constructor
  · rintro ⟨hy, hq⟩
    obtain ⟨x, hx, rfl⟩ := (M.mem_realModel_iff hM).mp hy
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [mem_vectorsOfNorm, ← (Rat.cast_injective (α := ℝ)).eq_iff]
    simpa using hq
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(M.realModelMap_mem_realModel_iff hM).mpr x.property,
      (M.norm_sq_realModelMap hM x).trans
        (congrArg (fun q : ℚ ↦ (q : ℝ)) (mem_vectorsOfNorm.mp hx))⟩

/-- A positive definite rational lattice and its real model have equal representation numbers
at every rational squared norm. -/
@[simp]
theorem representationNumber_realModel (q : ℚ) :
    ZLattice.representationNumber (M.realModel hM) (q : ℝ) = M.representationNumber q := by
  rw [ZLattice.representationNumber_def, shell_realModel, representationNumber_def]
  exact Set.ncard_image_of_injective _ ((M.realModelMap_injective hM).comp Subtype.val_injective)

end TauCeti.IntegralLattice
