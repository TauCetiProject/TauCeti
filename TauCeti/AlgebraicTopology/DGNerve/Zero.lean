/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.InitialVertex
public import TauCeti.AlgebraicTopology.DGNerve.TerminalVertex
public import TauCeti.Algebra.Homology.LinearHomComplex.Zero
public import TauCeti.CategoryTheory.DG.CochainComplex.Basic

/-!
# Zero complexes are zero objects of the dg nerve

A zero cochain complex is both an initial and a terminal vertex of the dg nerve of
complexes in a linear preadditive category. This is a statement about the enhancement,
not just its homotopy category: all simplex boundaries with that vertex as first or last
vertex admit fillers. It supplies the zero objects needed for stability of the enhancement.

The Hom complexes with a zero argument vanish in every degree, so the initial and terminal
criteria apply directly. No abelian or boundedness hypothesis is needed.

## References

* J. Lurie, *Higher Algebra*, Definition 1.1.1.9 and §1.3.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti.dgNerve

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- A zero cochain complex is an initial vertex of the dg nerve of complexes. -/
theorem isInitialVertex_cochainComplex_of_isZero {K : CochainComplex C ℤ} (hK : IsZero K) :
    (dgNerve R (CochainComplex C ℤ)).IsInitialVertex
      ((dgNerveEquiv R (CochainComplex C ℤ)).symm K) :=
  isInitialVertex_of_isZero fun _ ↦
    isZero_linearHomComplex_of_isZero_left R hK

/-- A zero cochain complex is a terminal vertex of the dg nerve of complexes. -/
theorem isTerminalVertex_cochainComplex_of_isZero {K : CochainComplex C ℤ} (hK : IsZero K) :
    (dgNerve R (CochainComplex C ℤ)).IsTerminalVertex
      ((dgNerveEquiv R (CochainComplex C ℤ)).symm K) :=
  isTerminalVertex_of_isZero fun _ ↦
    isZero_linearHomComplex_of_isZero_right R hK

end TauCeti.dgNerve
