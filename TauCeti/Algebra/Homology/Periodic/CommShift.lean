/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Suspension
public import TauCeti.CategoryTheory.Exact.Stable.Shift

/-!
# The periodic stable comparison commutes with integral shifts

The canonical equivalence from the componentwise split stable category of cyclic cochain
complexes to the homotopy category intertwines stable suspension with the signed shift by one.
This file extends that comparison coherently to every integer shift. The target keeps its
existing signed cyclic shift, including its addition constraints. This supplies the shift
compatibility required to transport the stable triangulation to the homotopy category.

The construction uses `stableSuspensionCompStableToHomotopyIso` and the sequence-model
comparison
`TauCeti.ExactStructure.IsFrobenius.commShiftOfIntertwiningStableSuspensionShift`.

## References

* B. Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (n : ℕ)

local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j => Exists.intro (j - 1) (sub_add_cancel j 1))
  (fun i => Exists.intro (i + 1) rfl)

/-- The stable-to-homotopy equivalence commutes coherently with the stable integral shift
and the signed cyclic shift already installed on the homotopy category. -/
@[instance_reducible]
noncomputable def stableToHomotopyCommShift :
    letI := (hE).stableHasShift
    (ExactStructure.homologicalComplexSplitStableToHomotopy C
      (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩)).CommShift ℤ := by
  exact (hE).commShiftOfIntertwiningStableSuspensionShift _
    (stableSuspensionCompStableToHomotopyIso C n)

/-- In degree one, the stable comparison identifies stable suspension with the signed
cyclic shift using the supplied suspension comparison. -/
theorem stableToHomotopyCommShift_iso_one :
    letI := (hE).stableHasShift
    letI := stableToHomotopyCommShift C n
    (ExactStructure.homologicalComplexSplitStableToHomotopy C
      (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩)).commShiftIso (1 : ℤ) =
      Functor.isoWhiskerRight (hE).stableShiftFunctorOneIso _ ≪≫
        stableSuspensionCompStableToHomotopyIso C n :=
  (hE).commShiftOfIntertwiningStableSuspensionShift_iso_one _
    (stableSuspensionCompStableToHomotopyIso C n)

end TauCeti.PeriodicComplex
