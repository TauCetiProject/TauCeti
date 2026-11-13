/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Colimit
public import TauCeti.Topology.Sheaves.CoverSystems

/-!
# Čech hypercohomology on a topological space

For a presheaf of integer-graded complexes on any topological space, Čech hypercohomology is
the colimit of the cohomology of total Čech complexes over the small directed preorder of
point-neighborhood covers. Every small open cover admits such a refinement. Transition maps
are independent of raw refinement functions by the total Čech prism, not because the raw
refinement category is filtered.

This is the direct-sum total convention `δ + (-1)^p d`, with nonnegative Čech degree `p`.
The construction itself makes sense without a lower bound on the coefficient complex.
Derived comparisons and convergence of spectral sequences require additional hypotheses
and are not asserted here. Hypercohomology vanishes on the empty space for every presheaf
of complexes, even one whose value on the empty open is nonzero.

The general structure maps and descent API are `TauCeti.CategoryTheory.cechHypercohomologyι`
and `TauCeti.CategoryTheory.cechHypercohomologyDesc`, specialized to
`PointOpenCover.toFormalCoproduct` and the refinement relation `fun _ _ h ↦ h`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25, equations (20.25.0.1)–(20.25.0.2),
  for total Čech complexes and refinement homotopies; §20.15 for the cover colimit.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe v' u u'

namespace TauCeti.Topology

variable (X : Type u) [TopologicalSpace X] (A : Type u') [Category.{v'} A] [Preadditive A]
  [HasZeroObject A] [HasProducts.{u} A] [HasCoproducts.{0} A] [CategoryWithHomology A]
  [HasColimitsOfShape (PointOpenCover X) A] (n : ℤ)

/-- Degree `n` Čech hypercohomology of presheaves of integer-graded complexes on `X`, as the
colimit of total Čech cohomology over point-neighborhood covers. Taking `A = ModuleCat R`
gives hypercohomology of presheaves of complexes of modules. -/
abbrev cechHypercohomology : ((Opens X)ᵒᵖ ⥤ CochainComplex A ℤ) ⥤ A :=
  TauCeti.CategoryTheory.cechHypercohomology A PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) n

/-- Čech hypercohomology of every presheaf of complexes on the empty space vanishes in every
integer degree, without requiring its value on the empty open to vanish. -/
lemma isZero_cechHypercohomology_obj_of_isEmpty [IsEmpty X]
    (P : (Opens X)ᵒᵖ ⥤ CochainComplex A ℤ) :
    IsZero ((cechHypercohomology X A n).obj P) :=
  TauCeti.CategoryTheory.isZero_cechHypercohomology_obj _ _ n
    (fun _ ↦ inferInstanceAs (IsEmpty X)) P

end TauCeti.Topology
