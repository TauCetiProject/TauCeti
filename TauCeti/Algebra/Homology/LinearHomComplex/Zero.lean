/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

/-!
# Hom complexes with a zero argument

The linear Hom complex vanishes if either argument is a zero complex. These statements
retain every cochain degree, not just closed degree-zero morphisms, and hence apply to
the mapping spaces in the dg nerve of complexes.
-/

public section

open CategoryTheory Limits CochainComplex

namespace TauCeti

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {F G : CochainComplex C ℤ}

/-- The linear Hom complex out of a zero complex is zero. -/
theorem isZero_linearHomComplex_of_isZero_left (hF : IsZero F) :
    IsZero (linearHomComplex R F G) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext n (z : ModuleCat.of R (HomComplex.Cochain F G n))
  apply HomComplex.Cochain.ext
  intro p q hpq
  exact ((HomologicalComplex.eval C (.up ℤ) p).map_isZero hF).eq_of_src _ _

/-- The linear Hom complex into a zero complex is zero. -/
theorem isZero_linearHomComplex_of_isZero_right (hG : IsZero G) :
    IsZero (linearHomComplex R F G) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext n (z : ModuleCat.of R (HomComplex.Cochain F G n))
  apply HomComplex.Cochain.ext
  intro p q hpq
  exact ((HomologicalComplex.eval C (.up ℤ) q).map_isZero hG).eq_of_tgt _ _

end TauCeti
