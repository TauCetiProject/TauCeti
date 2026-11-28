/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finiteness of group-like elements

Group-like elements in a finite torsion-free coalgebra over a domain form a finite type,
since they are linearly independent.
-/

public section

namespace GroupLike

/-- A finite torsion-free coalgebra over a domain has finitely many group-like elements. -/
instance finite {R A : Type*} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A]
    [Coalgebra R A] [Module.IsTorsionFree R A] [Module.Finite R A] : Finite (GroupLike R A) :=
  (linearIndep_groupLikeVal (R := R) (A := A)).finite

end GroupLike
