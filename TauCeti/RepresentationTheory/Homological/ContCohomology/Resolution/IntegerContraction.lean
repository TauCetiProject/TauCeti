/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.HomotopyEquiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Contraction

/-!
# The coinduced resolution contraction in integer degrees

The tensor product of cochain complexes uses total degrees and Koszul signs, for which the
standard Mathlib interface is indexed by `ℤ`.  The coinduced resolution is naturally indexed by
`ℕ`.  This file extends it by zero in negative degrees and transports its underlying contraction
to the resulting integer-indexed complex.

This is the form of the contraction consumed by tensor resolutions.  The inverse is still
evaluation at the identity in degree zero and vanishes in every other degree; evaluation at the
identity in positive degrees instead appears in the contracting homotopy.  All maps and
homotopies vanish in negative degrees.

## Main definitions

* `TopRep.resolutionModuleComplexInt`: the underlying coinduced resolution extended by zero.
* `TopRep.resolutionModuleHomotopyEquivInt`: its contraction onto the similarly extended
  coefficient complex.
-/

public section

noncomputable section

open HomologicalComplex

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- The underlying coinduced resolution, extended by zero to an integer-indexed cochain
complex. -/
noncomputable abbrev resolutionModuleComplexInt : CochainComplex (ModuleCat.{max v w} R) ℤ :=
  (resolutionModuleComplex X).extend ComplexShape.embeddingUpNat

/-- The coefficient module in degree zero, extended by zero to an integer-indexed cochain
complex. -/
noncomputable abbrev resolutionModuleCoeffComplexInt :
    CochainComplex (ModuleCat.{max v w} R) ℤ :=
  ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R X.V)).extend
    ComplexShape.embeddingUpNat

/-- Extending the contraction of the underlying coinduced resolution by zero gives a homotopy
equivalence of integer-indexed cochain complexes. -/
noncomputable def resolutionModuleHomotopyEquivInt :
    HomotopyEquiv (resolutionModuleCoeffComplexInt X) (resolutionModuleComplexInt X) :=
  (resolutionModuleHomotopyEquiv X).extend ComplexShape.embeddingUpNat

/-- The forward map of the integer-indexed contraction is the augmentation extended by zero. -/
@[simp] theorem resolutionModuleHomotopyEquivInt_hom :
    (resolutionModuleHomotopyEquivInt X).hom =
      extendMap (resolutionModuleIncl X) ComplexShape.embeddingUpNat :=
  by
    rw [resolutionModuleHomotopyEquivInt, HomotopyEquiv.extend_hom,
      resolutionModuleHomotopyEquiv_hom]

/-- The inverse map of the integer-indexed contraction is evaluation in degree zero extended by
zero. -/
@[simp] theorem resolutionModuleHomotopyEquivInt_inv :
    (resolutionModuleHomotopyEquivInt X).inv =
      extendMap (resolutionModuleProj X) ComplexShape.embeddingUpNat :=
  by
    rw [resolutionModuleHomotopyEquivInt, HomotopyEquiv.extend_inv,
      resolutionModuleHomotopyEquiv_inv]

end TopRep
