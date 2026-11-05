/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.ReducedFree
public import TauCeti.AlgebraicTopology.Spectra.SymmetricSpectrum
public import TauCeti.CategoryTheory.Monoidal.Mod.Algebra

/-!
# The Eilenberg–MacLane symmetric spectrum `HR`

For a commutative ring `R`, the Eilenberg–MacLane symmetric spectrum `HR` has as `n`-th level the
reduced free module `R~[Sⁿ]` on the simplicial sphere `Sⁿ = (S¹)^∧n`, with `Σ_n` permuting the
sphere coordinates. It is the composite of the sphere symmetric sequence `n ↦ Sⁿ` with the lax
braided functor `R~[-]`, so it is a commutative monoid for the Day convolution product
(`SymmetricSequence.eilenbergMacLane R`): its multiplication
`R~[S^p] ∧ R~[S^q] ⟶ R~[S^(p+q)]` is the bilinear extension of the concatenation of sphere
coordinates, `[x] ∧ [y] ↦ [x ∧ y]`, and its unit is the generator of the non-basepoint simplex
of `S⁰`.

Sending each simplex of `Sⁿ` to its generator is a morphism of commutative monoids from the sphere
symmetric sequence to `HR` (`SymmetricSequence.sphereToEilenbergMacLane R`). Restricting scalars
along it makes `HR` a symmetric spectrum (`SymmetricSpectrum.eilenbergMacLane R`). Its structure
maps `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` send `x ∧ Σ aᵢ yᵢ` to `Σ aᵢ (x ∧ yᵢ)`
(`SymmetricSpectrum.eilenbergMacLane_dayStructureMap_app_smashMk`). The multiplication of `HR`
descends to the smash product over the sphere, making `HR` a commutative ring spectrum, a
commutative monoid object of symmetric spectra (`Mod.monObjComapRegular`,
`Mod.isCommMonObjComapRegular`).

## Main definitions

* `SymmetricSequence.eilenbergMacLane R`: the commutative monoid `n ↦ R~[Sⁿ]` of symmetric
  sequences.
* `SymmetricSequence.sphereToEilenbergMacLane R`: the unit morphism of monoids `S ⟶ HR`.
* `SymmetricSpectrum.eilenbergMacLane R`: the Eilenberg–MacLane symmetric spectrum `HR`, a
  commutative ring spectrum.

## Main statements

* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap`: the structure maps of `HR` are the
  generator map followed by the multiplication of `HR`.
* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap_app_smashMk`: the structure maps on
  simplices.
* `SymmetricSpectrum.tensorπ_eilenbergMacLane_mul_hom`,
  `SymmetricSpectrum.eilenbergMacLane_one_hom`: the multiplication and unit of the ring spectrum
  `HR`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

open scoped DayFunctor

noncomputable section

variable (R : Type) [CommRing R]

namespace SymmetricSequence

/-- The Eilenberg–MacLane symmetric sequence `n ↦ R~[Sⁿ]` of reduced free `R`-modules on the
simplicial spheres, with `Σ_n` permuting the sphere coordinates. The bilinear extension of the
concatenation of coordinates `[x] ∧ [y] ↦ [x ∧ y]` makes it a commutative monoid for the Day
convolution product, through the instances `DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
abbrev eilenbergMacLane : SymmetricSequence.{0} :=
  .mk (PointedSSet.smashPowFunctor PointedSSet.circle ⋙ PointedSSet.reducedFree R)

/- The Eilenberg–MacLane symmetric sequence is a commutative monoid. -/
example : IsCommMonObj (eilenbergMacLane R) := inferInstance

/-- The unit morphism `S ⟶ HR` from the sphere symmetric sequence, sending each simplex of `Sⁿ` to
its generator in `R~[Sⁿ]`. It is a morphism of monoids, through the instance
`DayFunctor.isMonHom`. -/
def sphereToEilenbergMacLane : sphere ⟶ eilenbergMacLane R :=
  .mk ((PointedSSet.smashPowFunctor PointedSSet.circle).rightUnitor.inv ≫
    Functor.whiskerLeft _ (PointedSSet.toReducedFree R))

@[simp]
lemma sphereToEilenbergMacLane_natTrans_app (k : FiniteBijection) :
    (sphereToEilenbergMacLane R).natTrans.app k =
      PointedSSet.reducedFreeι R (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [sphereToEilenbergMacLane]

/-- The generator maps `Sⁿ ⟶ R~[Sⁿ]` form a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (sphereToEilenbergMacLane R).natTrans :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((PointedSSet.smashPowFunctor PointedSSet.circle).rightUnitor.inv ≫
      Functor.whiskerLeft _ (PointedSSet.toReducedFree R)))

/- The unit `S ⟶ HR` is a morphism of monoids. -/
example : IsMonHom (sphereToEilenbergMacLane R) := inferInstance

end SymmetricSequence

namespace SymmetricSpectrum

/-- The Eilenberg–MacLane symmetric spectrum `HR`: the commutative monoid `n ↦ R~[Sⁿ]` of
symmetric sequences, regarded as a module over the sphere by restricting scalars along the unit
`S ⟶ HR`. It is a commutative ring spectrum, a commutative monoid for the smash product over the
sphere, through the instances `Mod.monObjComapRegular` and `Mod.isCommMonObjComapRegular`. -/
-- An abbreviation, so that the monoid instances for `Mod.comapRegular` apply to it.
abbrev eilenbergMacLane : SymmetricSpectrum :=
  Mod.comapRegular (SymmetricSequence.sphereToEilenbergMacLane R)

/- The Eilenberg–MacLane spectrum is a commutative ring spectrum. -/
example : IsCommMonObj (eilenbergMacLane R) := inferInstance

/-- On representatives in `HR ⊗ HR`, the multiplication `HR ∧_S HR ⟶ HR` of the ring spectrum `HR`
is the multiplication of the symmetric sequence `n ↦ R~[Sⁿ]`. -/
lemma tensorπ_eilenbergMacLane_mul_hom :
    Mod.tensorπ _ _ ≫ (MonObj.mul : eilenbergMacLane R ⊗ eilenbergMacLane R ⟶ _).hom =
      (MonObj.mul : SymmetricSequence.eilenbergMacLane R ⊗ SymmetricSequence.eilenbergMacLane R ⟶
        _) :=
  Mod.tensorπ_comapRegular_mul_hom _

/-- The unit `S ⟶ HR` of the ring spectrum `HR` is the generator map
`SymmetricSequence.sphereToEilenbergMacLane R`. -/
lemma eilenbergMacLane_one_hom :
    (MonObj.one : 𝟙_ SymmetricSpectrum ⟶ eilenbergMacLane R).hom =
      SymmetricSequence.sphereToEilenbergMacLane R :=
  (rfl)

lemma eilenbergMacLane_eq_comap : eilenbergMacLane R =
    (Mod.comap (SymmetricSequence.sphereToEilenbergMacLane R)).obj
      (Mod.regular (SymmetricSequence.eilenbergMacLane R)) :=
  (rfl)

lemma eilenbergMacLane_X : (eilenbergMacLane R).X = SymmetricSequence.eilenbergMacLane R :=
  (rfl)

/-- The sphere acts on `HR` through the unit `S ⟶ HR` followed by the multiplication of `HR`. -/
lemma eilenbergMacLane_smul :
    ModObj.smul (M := SymmetricSequence.sphere) (X := (eilenbergMacLane R).X) =
      SymmetricSequence.sphereToEilenbergMacLane R ▷ SymmetricSequence.eilenbergMacLane R ≫
        MonObj.mul :=
  (rfl)

/-- The structure maps `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` of `HR` are the generator map on the sphere
factor followed by the multiplication of `HR`. -/
lemma eilenbergMacLane_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLane R).dayStructureMap p q =
      PointedSSet.reducedFreeι R _ ▷ _ ≫
        Functor.LaxMonoidal.μ (PointedSSet.smashPowFunctor PointedSSet.circle ⋙
          PointedSSet.reducedFree R) p q := by
  rw [Mod.dayStructureMap_def, eilenbergMacLane_smul, DayFunctor.comp_natTrans,
    NatTrans.comp_app]
  -- The Day convolution unit is that of `(eilenbergMacLane R).X`, which is the symmetric
  -- sequence `SymmetricSequence.eilenbergMacLane R` only up to unfolding, so the rewrite is
  -- applied by unification.
  refine (DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc
    (SymmetricSequence.sphereToEilenbergMacLane R) (SymmetricSequence.eilenbergMacLane R) p q
    _).trans ?_
  rw [DayFunctor.η_app_comp_mul_natTrans_app,
    SymmetricSequence.sphereToEilenbergMacLane_natTrans_app]

/-- The structure map `S^p ∧ R~[S^q] ⟶ R~[S^(p+q)]` of `HR` sends `x ∧ Σ aᵢ yᵢ` to
`Σ aᵢ (x ∧ yᵢ)`, where `x ∧ yᵢ ∈ S^(p+q)` concatenates the sphere coordinates. -/
@[simp]
lemma eilenbergMacLane_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : (PointedSSet.circle.smashPow (Fin p.len)).right.obj n)
    (v : ((PointedSSet.reducedFree R).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLane R).dayStructureMap p q).right.app n (PointedSSet.smashMk x v) =
      ReducedFreeModule.map R (fun y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp) v := by
  rw [eilenbergMacLane_dayStructureMap, Functor.LaxMonoidal.comp_μ, PointedSSet.reducedFree_μ,
    ← Category.assoc, PointedSSet.comp_right_app_apply, PointedSSet.reducedFree_map_app]
  simp

end SymmetricSpectrum

end

end TauCeti
