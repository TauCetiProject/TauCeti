/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import TauCeti.Algebra.Homology.Linear
import TauCeti.CategoryTheory.Localization.Linear

/-!
# Linearity of derived cohomology functors

When `R` is a ring and `C` is an `R`-linear abelian category,
`Mathlib.Algebra.Homology.DerivedCategory.Linear` equips `DerivedCategory C` with an `R`-linear
structure for which `DerivedCategory.Q` and `DerivedCategory.Qh` are `R`-linear, while
`TauCeti.Algebra.Homology.Linear` makes the cohomology functors on cochain complexes `R`-linear for
any semiring `R`.

This file descends that linearity across localization for any semiring `R` whenever
`DerivedCategory C` and `DerivedCategory.Q` carry compatible `R`-linear structures, showing that
`DerivedCategory.homologyFunctor C n : DerivedCategory C ⥤ C` is `R`-linear for every integer `n`.
When `R` is a ring, Mathlib's `Mathlib.Algebra.Homology.DerivedCategory.Linear` supplies the
`Linear R (DerivedCategory C)` and `Q.Linear R` instances automatically.

This allows endomorphisms in `DerivedCategory C` to induce `R`-algebra homomorphisms on
cohomology endomorphism algebras via `CategoryTheory.Functor.mapEndAlgHom` (used in
`TauCeti.Algebra.Homology.DerivedCategory.CohomologyAction`).
-/

public section

open CategoryTheory

universe t w v u

namespace DerivedCategory

variable (R : Type t) [Semiring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C] [Linear R (DerivedCategory C)] [(Q (C := C)).Linear R]

/-- The `n`-th cohomology functor on the derived category of an `R`-linear abelian category is
`R`-linear whenever `DerivedCategory C` and `DerivedCategory.Q` are `R`-linear. -/
instance (n : ℤ) : (homologyFunctor C n).Linear R := by
  have : Localization.Lifting Q (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.homologyFunctor C (.up ℤ) n) (homologyFunctor C n) :=
    ⟨homologyFunctorFactors C n⟩
  exact (TauCeti.CategoryTheory.Localization.functor_linear_iff Q
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (.up ℤ) n) (homologyFunctor C n)).mp inferInstance

end DerivedCategory
