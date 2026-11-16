/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import TauCeti.Algebra.Homology.Linear

/-!
# Linearity of derived cohomology functors

When `C` and `DerivedCategory C` are `R`-linear and `DerivedCategory.Q` is `R`-linear (in
particular whenever `R` is a ring and `C` is `R`-linear, via
`Mathlib.Algebra.Homology.DerivedCategory.Linear`), the cohomology functor on cochain complexes is
`R`-linear (`TauCeti.Algebra.Homology.Linear`). This file shows that the derived cohomology functor
`DerivedCategory.homologyFunctor C n : DerivedCategory C ⥤ C` is `R`-linear for every integer `n`.

This allows endomorphisms in `DerivedCategory C` to induce `R`-algebra homomorphisms on
cohomology endomorphism algebras via `CategoryTheory.Functor.mapEndAlgHom`.
-/

public section

open CategoryTheory

universe t w v u

namespace DerivedCategory

variable (R : Type t) [Semiring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C] [Linear R (DerivedCategory C)] [(Q (C := C)).Linear R]

/-- The `n`-th cohomology functor on the derived category of an `R`-linear abelian category is
`R`-linear whenever `DerivedCategory C` and `Q` are `R`-linear. -/
instance (n : ℤ) : (homologyFunctor C n).Linear R := by
  have : (Q ⋙ homologyFunctor C n).Linear R :=
    Functor.linear_of_iso R (homologyFunctorFactors C n).symm
  rw [Functor.linear_iff]
  intro X r
  let K := Q.objPreimage X
  let e : Q.obj K ≅ X := Q.objObjPreimageIso X
  have hX : r • 𝟙 X = e.inv ≫ Q.map (r • 𝟙 K) ≫ e.hom := by simp
  have hQ : (homologyFunctor C n).map (Q.map (r • 𝟙 K)) =
      r • 𝟙 ((homologyFunctor C n).obj (Q.obj K)) := by
    simpa using (Q ⋙ homologyFunctor C n).map_smul r (𝟙 K)
  rw [hX, Functor.map_comp, Functor.map_comp, hQ]
  simp [← Functor.map_comp]

end DerivedCategory
