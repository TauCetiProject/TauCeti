/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import TauCeti.Algebra.Homology.Linear

/-!
# Homology on the homotopy category is linear

For an `R`-linear category `V`, Mathlib makes the homotopy category of complexes in `V` an
`R`-linear category and the quotient functor `R`-linear. Taking homology in a fixed degree on
the homotopy category is then an `R`-linear functor, since it is induced by the homology functor
on complexes, which is `R`-linear (`HomologicalComplex.homologyMap_smul`). This is what makes the
right derived functors of an `R`-linear functor `R`-linear.
-/

public section

open CategoryTheory

namespace HomotopyCategory

variable {R : Type*} [Semiring R] {V : Type*} [Category* V] [Preadditive V] [Linear R V]
  {ι : Type*} (c : ComplexShape ι) [CategoryWithHomology V]

/-- Taking homology in a fixed degree on the homotopy category is a linear functor. -/
instance (i : ι) : (homologyFunctor V c i).Linear R :=
  have := Functor.linear_of_iso R (homologyFunctorFactors V c i).symm
  (quotient V c).linear_of_full_essSurj_comp (homologyFunctor V c i)

end HomotopyCategory
