/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Tensor-coinvariant complexes in the coefficient variable

For a fixed complex of representations, tensor coinvariants form an additive functor of the
coefficient representation. If the complex is degreewise projective, this functor preserves
short exact coefficient sequences, for any complex shape and without flatness assumptions
on the coefficients. This supplies the short exact sequences used to compute coefficient
connecting maps with projective resolutions.

The tensor-coinvariant construction is due to Amelia Livingston in Mathlib.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I.7 and III.1.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace HomologicalComplex

variable {k G : Type u} [CommRing k] [Group G]
  {ι : Type*} {c : ComplexShape ι}

/-- Tensor coinvariants of a fixed complex, as a functor of the coefficient representation.
This is an abbreviation so its objects compute to the existing tensor-coinvariant complexes. -/
abbrev coinvariantsTensorFunctor (P : HomologicalComplex (Rep.{u} k G) c) :
    Rep.{u} k G ⥤ HomologicalComplex (ModuleCat.{u} k) c where
  obj A := (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex c).obj P
  map f := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map f) c).app P
  map_id A := by ext n; simp
  map_comp f g := by ext n; simp

/-- On objects, the coefficient functor is the usual tensor-coinvariant complex. -/
@[simp]
theorem coinvariantsTensorFunctor_obj (P : HomologicalComplex (Rep.{u} k G) c)
    (A : Rep.{u} k G) :
    (P.coinvariantsTensorFunctor).obj A =
      (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex c).obj P :=
  (rfl)

instance (P : HomologicalComplex (Rep.{u} k G) c) :
    (P.coinvariantsTensorFunctor).Additive where
  map_add := by intros; ext n : 1; simp [HomologicalComplex.add_f_apply]

/-- For a complex of projective representations, tensor coinvariants preserve short exact
coefficient sequences, without flatness assumptions on the coefficients. -/
theorem shortExact_map_coinvariantsTensorFunctor
    (P : HomologicalComplex (Rep.{u} k G) c) [∀ n, Projective (P.X n)]
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    (S.map P.coinvariantsTensorFunctor).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact hS.map_coinvariantsTensor_projective (P.X n)

end HomologicalComplex
