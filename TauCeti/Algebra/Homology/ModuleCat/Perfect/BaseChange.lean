/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.BaseChange
public import TauCeti.Algebra.Homology.ModuleCat.Perfect.Basic

/-!
# Base change of perfect complexes

Let `f : R →+* S` be a homomorphism of commutative rings. Derived extension of scalars
`- ⊗^L_R S : D(R) ⥤ D(S)` carries perfect complexes to perfect complexes
(`TauCeti.DerivedDeRham.IsPerfect.baseChange`). A perfect complex `K` is represented by a bounded
complex `P` of finitely generated projective `R`-modules. Such a `P` is K-flat, so termwise
extension of scalars `S ⊗_R P` computes `K ⊗^L_R S`, and `S ⊗_R P` is again a bounded complex of
finitely generated projective `S`-modules. The statement holds for every left derived functor of
termwise scalar extension, in particular for `TauCeti.derivedExtendScalars f`.

Consequently, termwise extension of scalars of any K-flat model of a perfect complex, for
instance a bounded-above complex of flat modules
(`CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat`), is perfect
(`CochainComplex.isPerfect_Q_obj_complexBaseChange_obj`). Some flatness of the model is needed:
the acyclic complex of `ℤ/4`-modules with every term `ℤ/4` and every differential multiplication
by `2` is zero, hence perfect, in `D(ℤ/4)`, but its termwise reduction modulo `2` has zero
differentials and cohomology `ℤ/2` in every degree, so it is not perfect.

## Main results

* `TauCeti.DerivedDeRham.IsPerfect.baseChange`: every left derived functor of termwise scalar
  extension along `f` sends perfect complexes to perfect complexes.
* `CochainComplex.isPerfect_Q_obj_complexBaseChange_obj`: the termwise scalar extension of a
  K-flat complex representing a perfect complex is perfect.

## References

* [Stacks Project, Lemma 15.76.9 (Tag 066W)](https://stacks.math.columbia.edu/tag/066W).
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

universe w w' u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

namespace TauCeti.DerivedDeRham

/-- **Base change of perfect complexes.** For a homomorphism `f : R →+* S` of commutative rings,
every left derived functor `(G, α)` of termwise scalar extension along `f`, such as
`TauCeti.derivedExtendScalars f`, sends perfect complexes of `R`-modules to perfect complexes of
`S`-modules. -/
theorem IsPerfect.baseChange {K : DerivedCategory (ModuleCat.{u} R)} (hK : IsPerfect R K)
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : Q ⋙ G ⟶ complexBaseChange f ⋙ Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    IsPerfect S (G.obj K) := by
  obtain ⟨P, a, b, _, _, hfin, hproj, ⟨e⟩⟩ := (isPerfect_iff K).1 hK
  have := hfin
  have := hproj
  -- A bounded-above complex of projective, hence flat, modules is K-flat, so the derived
  -- functor is computed on `P` by termwise scalar extension.
  have : P.IsKFlat :=
    CochainComplex.isKFlat_of_boundedAbove_flat_moduleCat P b fun _ ↦ inferInstance
  -- The termwise scalar extension of `P` is again bounded, with finitely generated projective
  -- terms.
  exact ((isPerfect_iff _).2 ⟨_, a, b, inferInstance, inferInstance,
    fun i ↦ ModuleCat.finite_extendScalars_obj f (P.X i),
    fun i ↦ ModuleCat.projective_extendScalars_obj f (P.X i), ⟨Iso.refl _⟩⟩).of_iso
    ((asIso (α.app P)).symm ≪≫ G.mapIso e)

end TauCeti.DerivedDeRham

namespace CochainComplex

open TauCeti TauCeti.DerivedDeRham

/-- **Termwise base change of a K-flat model of a perfect complex.** If a K-flat complex `P` of
`R`-modules, for instance a bounded-above complex of flat modules, represents a perfect complex,
then its termwise scalar extension along `f : R →+* S` represents a perfect complex of
`S`-modules. -/
theorem isPerfect_Q_obj_complexBaseChange_obj (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [P.IsKFlat] (hP : IsPerfect R (Q.obj P)) :
    IsPerfect S (Q.obj ((complexBaseChange f).obj P)) :=
  (hP.baseChange f (derivedExtendScalars.{u, w, w'} f) (derivedExtendScalarsCounit f)).of_iso
    (derivedExtendScalarsKFlatIso f P)

end CochainComplex
