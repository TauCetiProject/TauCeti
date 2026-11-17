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
# The Eilenberg–MacLane symmetric spectra `HR` and `HM`

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
`Mod.isCommMonObjComapRegular`). A ring homomorphism `φ : R →+* S` induces a morphism of
commutative monoids `SymmetricSequence.eilenbergMacLaneMap φ` compatible with the sphere unit, and
hence a morphism of commutative ring spectra `SymmetricSpectrum.eilenbergMacLaneMap φ : HR ⟶ HS`.

For an `R`-module `M`, the Eilenberg–MacLane spectrum `HM` has as `n`-th level the reduced free
module `M~[Sⁿ] = R~[Sⁿ] ⊗_R M` with coefficients in `M`, with `Σ_n` permuting the sphere
coordinates. It is a module over the commutative monoid `HR` of symmetric sequences
(`SymmetricSequence.eilenbergMacLaneModule R M`), with structure maps
`R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` the bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`.
A linear map `M ⟶ N` induces a morphism of `HR`-modules `HM ⟶ HN`, functorially. Restricting
scalars along the unit `S ⟶ HR` makes `HM` a symmetric spectrum
(`SymmetricSpectrum.eilenbergMacLaneModule R M`), functorial in `M`, with structure maps
`S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` sending `x ∧ Σ yᵢ ⊗ mᵢ` to `Σ (x ∧ yᵢ) ⊗ mᵢ`. Because `S` is
central in `HR`, the `HR`-action descends across the balanced smash product `HR ∧_S HM` over the
sphere, upgrading `HM` to a module object over the ring spectrum `HR` in symmetric spectra
(`SymmetricSpectrum.eilenbergMacLaneMod R M`, via `Mod.comapRegularMod`). For `M = R`, right
tensoring with `R` identifies `eilenbergMacLaneMod R R` with the regular `HR`-module
(`SymmetricSpectrum.eilenbergMacLaneModSelfIso R`), and a `φ`-semilinear map `g : M →ₛₗ[φ] N`
induces an `HR`-module morphism into the scalar restriction of `HN` along `HR ⟶ HS`
(`SymmetricSpectrum.eilenbergMacLaneModSemilinearMap φ g`).

## Main definitions

* `SymmetricSequence.eilenbergMacLane R`: the commutative monoid `n ↦ R~[Sⁿ]` of symmetric
  sequences, and `SymmetricSequence.eilenbergMacLaneMap φ`: the monoid morphism induced by
  `φ : R →+* S`.
* `SymmetricSequence.sphereToEilenbergMacLane R`: the unit morphism of monoids `S ⟶ HR`.
* `SymmetricSpectrum.eilenbergMacLane R`: the Eilenberg–MacLane symmetric spectrum `HR`, a
  commutative ring spectrum, and `SymmetricSpectrum.eilenbergMacLaneMap φ`: the ring spectrum map
  `HR ⟶ HS` induced by `φ : R →+* S`.
* `SymmetricSequence.eilenbergMacLaneModule R M`: the `HR`-module `n ↦ M~[Sⁿ]` of an `R`-module
  `M`, `SymmetricSequence.eilenbergMacLaneModuleMap R g`, and
  `SymmetricSequence.eilenbergMacLaneModuleSemilinearMap φ g`.
* `SymmetricSpectrum.eilenbergMacLaneModule R M`: the Eilenberg–MacLane symmetric spectrum `HM`,
  with semilinear coefficient change `SymmetricSpectrum.eilenbergMacLaneModuleMap g`, and
  `SymmetricSpectrum.eilenbergMacLaneMod R M`: `HM` as a module over the ring spectrum `HR` for the
  smash product over `S`.
* `SymmetricSpectrum.eilenbergMacLaneModMap R g` and
  `SymmetricSpectrum.eilenbergMacLaneModSemilinearMap φ g`: linear and semilinear coefficient
  changes of `HR`-module spectra.
* `SymmetricSequence.eilenbergMacLaneModuleSelfIso R` and
  `SymmetricSpectrum.eilenbergMacLaneModSelfIso R`: the isomorphisms identifying `HM` for `M = R`
  with the regular `HR`-module.

## Main statements

* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap`: the structure maps of `HR` are the
  generator map followed by the multiplication of `HR`.
* `SymmetricSpectrum.eilenbergMacLane_dayStructureMap_app_smashMk`: the structure maps on
  simplices.
* `SymmetricSpectrum.tensorπ_eilenbergMacLane_mul_hom`,
  `SymmetricSpectrum.eilenbergMacLane_one_hom`: the multiplication and unit of the ring spectrum
  `HR`.
* `SymmetricSpectrum.tensorπ_eilenbergMacLaneMod_smul_hom`: on representatives in `HR ⊗ HM`, the
  `HR ∧_S HM ⟶ HM` action of `SymmetricSpectrum.eilenbergMacLaneMod R M` is the `HR`-action on
  symmetric sequences.
* `SymmetricSequence.eilenbergMacLaneModule_dayStructureMap_app_smashMk`,
  `SymmetricSpectrum.eilenbergMacLaneModule_dayStructureMap_app_smashMk`: the structure maps of
  `HM`, as an `HR`-module and as a symmetric spectrum, on simplices.
* `SymmetricSequence.eilenbergMacLaneModuleMap_id`,
  `SymmetricSequence.eilenbergMacLaneModuleMap_comp`,
  `SymmetricSpectrum.eilenbergMacLaneModMap_id`,
  `SymmetricSpectrum.eilenbergMacLaneModMap_comp`: functoriality of `HM` in `M`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

open scoped DayFunctor CategoryTheory.MonObj

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

section RingMap

variable {R} {S T : Type} [CommRing S] [CommRing T]

/-- The morphism of commutative monoids `HR ⟶ HS` of symmetric sequences induced by a ring
homomorphism `φ : R →+* S`, changing coefficients on every sphere level. -/
def eilenbergMacLaneMap (φ : R →+* S) : eilenbergMacLane R ⟶ eilenbergMacLane S :=
  .mk (Functor.whiskerLeft _ (PointedSSet.reducedFreeRingMap φ))

@[simp]
lemma eilenbergMacLaneMap_natTrans_app (φ : R →+* S) (k : FiniteBijection) :
    (eilenbergMacLaneMap φ).natTrans.app k =
      (PointedSSet.reducedFreeRingMap φ).app (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneMap]

/-- Changing coefficients along `φ : R →+* S` on every sphere level is a monoidal natural
transformation. -/
instance (φ : R →+* S) : NatTrans.IsMonoidal (eilenbergMacLaneMap φ).natTrans :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerLeft _ (PointedSSet.reducedFreeRingMap φ)))

/- `eilenbergMacLaneMap φ` is a morphism of monoids for the Day convolution product. -/
example (φ : R →+* S) : IsMonHom (eilenbergMacLaneMap φ) := inferInstance

@[simp]
lemma eilenbergMacLaneMap_id :
    eilenbergMacLaneMap (RingHom.id R) = 𝟙 (eilenbergMacLane R) := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp

lemma eilenbergMacLaneMap_comp (φ : R →+* S) (ψ : S →+* T) :
    eilenbergMacLaneMap (ψ.comp φ) = eilenbergMacLaneMap φ ≫ eilenbergMacLaneMap ψ := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp [PointedSSet.reducedFreeRingMap_comp]

/-- Changing coefficients along `φ : R →+* S` commutes with the sphere unit `S ⟶ HR`. -/
@[reassoc (attr := simp)]
lemma sphereToEilenbergMacLane_comp_eilenbergMacLaneMap (φ : R →+* S) :
    sphereToEilenbergMacLane R ≫ eilenbergMacLaneMap φ = sphereToEilenbergMacLane S := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp

end RingMap

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

section RingMap

variable {R} {S T : Type} [CommRing S] [CommRing T]

/-- The morphism of commutative ring spectra `HR ⟶ HS` induced by a ring homomorphism
`φ : R →+* S`. -/
def eilenbergMacLaneMap (φ : R →+* S) : eilenbergMacLane R ⟶ eilenbergMacLane S :=
  Mod.comapRegularMap (SymmetricSequence.sphereToEilenbergMacLane R)
    (SymmetricSequence.sphereToEilenbergMacLane S) (SymmetricSequence.eilenbergMacLaneMap φ)
    (SymmetricSequence.sphereToEilenbergMacLane_comp_eilenbergMacLaneMap φ)

instance (φ : R →+* S) : IsMonHom (eilenbergMacLaneMap φ) :=
  Mod.isMonHom_comapRegularMap _ _ _ _

@[simp]
lemma eilenbergMacLaneMap_hom (φ : R →+* S) :
    (eilenbergMacLaneMap φ).hom = SymmetricSequence.eilenbergMacLaneMap φ :=
  Mod.comapRegularMap_hom _ _ _ _

@[simp]
lemma eilenbergMacLaneMap_id :
    eilenbergMacLaneMap (RingHom.id R) = 𝟙 (eilenbergMacLane R) := by
  ext : 1
  simp [Mod.comapRegular]

lemma eilenbergMacLaneMap_comp (φ : R →+* S) (ψ : S →+* T) :
    eilenbergMacLaneMap (ψ.comp φ) = eilenbergMacLaneMap φ ≫ eilenbergMacLaneMap ψ := by
  ext : 1
  simp [SymmetricSequence.eilenbergMacLaneMap_comp]

end RingMap

end SymmetricSpectrum

section Module

variable (M : Type) [AddCommGroup M] [Module R M]

namespace SymmetricSequence

/-- The Eilenberg–MacLane symmetric sequence `n ↦ M~[Sⁿ] = R~[Sⁿ] ⊗_R M` of an `R`-module `M`,
with `Σ_n` permuting the sphere coordinates, as a module over the commutative monoid `HR`. Its
structure maps `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` are the bilinear extension of
`[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`, concatenating sphere coordinates
(`SymmetricSequence.eilenbergMacLaneModule_dayStructureMap_app_smashMk`). -/
-- An abbreviation, so that the levels of `HM` are the reduced free modules `M~[Sⁿ]`.
abbrev eilenbergMacLaneModule : Mod SymmetricSequence.{0} (eilenbergMacLane R) :=
  Mod.dayMk (.mk (PointedSSet.smashPowFunctor PointedSSet.circle ⋙
      PointedSSet.reducedFreeTensor R M))
    (PointedSSet.reducedFreeTensorCompAct R M _)
    (PointedSSet.reducedFreeTensorCompAct_unit _) (PointedSSet.reducedFreeTensorCompAct_assoc _)

/-- The structure maps `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` of the `HR`-module `HM` are the action
of reduced free `R`-modules followed by the concatenation of sphere coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLaneModule R M).dayStructureMap p q =
      PointedSSet.reducedFreeTensorAct R M _ _ ≫ (PointedSSet.reducedFreeTensor R M).map
        (Functor.LaxMonoidal.μ (PointedSSet.smashPowFunctor PointedSSet.circle) p q) :=
  (Mod.dayStructureMap_dayMk _ _ _ _ p q).trans (PointedSSet.reducedFreeTensorCompAct_app _ p q)

/-- The structure map `R~[S^p] ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` sends `v ∧ Σ yᵢ ⊗ mᵢ` to
`Σ (v ∧ yᵢ) ⊗ mᵢ`, where `x ∧ y ∈ S^(p+q)` concatenates the sphere coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (v : ((PointedSSet.reducedFree R).obj
      (PointedSSet.circle.smashPow (Fin p.len))).right.obj n)
    (t : ((PointedSSet.reducedFreeTensor R M).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLaneModule R M).dayStructureMap p q).right.app n (PointedSSet.smashMk v t) =
      LinearMap.rTensor M (ReducedFreeModule.map₂ R (fun x y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp) (by simp) v) t := by
  rw [Mod.dayStructureMap_dayMk, PointedSSet.reducedFreeTensorCompAct_app_app_smashMk]

variable {M} {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The morphism of `HR`-modules `HM ⟶ HN` induced by a linear map `g : M →ₗ[R] N`, applying `g`
to the coefficients in every level. -/
def eilenbergMacLaneModuleMap (g : M →ₗ[R] N) :
    eilenbergMacLaneModule R M ⟶ eilenbergMacLaneModule R N :=
  Mod.dayHomMk (.mk (Functor.whiskerLeft _ (PointedSSet.reducedFreeTensorMap g))) fun p q ↦ by
    rw [Mod.dayStructureMap_dayMk, Mod.dayStructureMap_dayMk]
    simp [PointedSSet.reducedFreeTensorCompAct_app,
      (PointedSSet.reducedFreeTensorMap g).naturality]

@[simp]
lemma eilenbergMacLaneModuleMap_hom_natTrans_app (g : M →ₗ[R] N) (k : FiniteBijection) :
    (eilenbergMacLaneModuleMap R g).hom.natTrans.app k =
      (PointedSSet.reducedFreeTensorMap g).app (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneModuleMap]

@[simp]
lemma eilenbergMacLaneModuleMap_id :
    eilenbergMacLaneModuleMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  apply Mod.Hom.ext
  apply DayFunctor.hom_ext
  ext k : 2
  simp

lemma eilenbergMacLaneModuleMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    eilenbergMacLaneModuleMap R (h ∘ₗ g) =
      eilenbergMacLaneModuleMap R g ≫ eilenbergMacLaneModuleMap R h := by
  apply Mod.Hom.ext
  apply DayFunctor.hom_ext
  ext k : 2
  simp [PointedSSet.reducedFreeTensorMap_comp]

section SemilinearMap

variable {R} {S T : Type} [CommRing S] [CommRing T]
  {Q : Type} [AddCommGroup Q] [Module S Q]
  {W : Type} [AddCommGroup W] [Module T W]

/-- A ring homomorphism `φ : R →+* S` and a `φ`-semilinear map `g : M →ₛₗ[φ] Q` induce a morphism
of `HR`-modules `HM ⟶ (Mod.comap (eilenbergMacLaneMap φ)).obj HQ`, changing rings and coefficients
on every sphere level. -/
def eilenbergMacLaneModuleSemilinearMap (φ : R →+* S) (g : M →ₛₗ[φ] Q) :
    eilenbergMacLaneModule R M ⟶
      (Mod.comap (eilenbergMacLaneMap φ)).obj (eilenbergMacLaneModule S Q) :=
  Mod.dayHomMk (.mk (Functor.whiskerLeft _ (PointedSSet.reducedFreeTensorMap g))) fun p q ↦ by
    rw [Mod.dayStructureMap_dayMk, Mod.dayStructureMap_comap, Mod.dayStructureMap_dayMk]
    simp [Mod.comap, (PointedSSet.reducedFreeTensorMap g).naturality, tensorHom_def']

@[simp]
lemma eilenbergMacLaneModuleSemilinearMap_hom_natTrans_app
    (φ : R →+* S) (g : M →ₛₗ[φ] Q) (k : FiniteBijection) :
    (eilenbergMacLaneModuleSemilinearMap φ g).hom.natTrans.app k =
      (PointedSSet.reducedFreeTensorMap g).app
        (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneModuleSemilinearMap, Mod.comap]

@[simp]
lemma eilenbergMacLaneModuleSemilinearMap_ringHomId_hom (g : M →ₗ[R] N) :
    (eilenbergMacLaneModuleSemilinearMap (RingHom.id R) g).hom =
      (eilenbergMacLaneModuleMap R g).hom := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp [Mod.comap]

lemma eilenbergMacLaneModuleSemilinearMap_comp_hom
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} [RingHomCompTriple φ ψ χ]
    (g : M →ₛₗ[φ] Q) (h : Q →ₛₗ[ψ] W) :
    (eilenbergMacLaneModuleSemilinearMap χ (h.comp g)).hom =
      (eilenbergMacLaneModuleSemilinearMap φ g).hom ≫
        (eilenbergMacLaneModuleSemilinearMap ψ h).hom := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp [DayFunctor.comp_natTrans, PointedSSet.reducedFreeTensorMap_comp, Mod.comap]

end SemilinearMap

section SelfIso

/-- For a commutative ring `R`, `eilenbergMacLaneModule R R` is isomorphic as an `HR`-module of
symmetric sequences to the regular `HR`-module `Mod.regular (eilenbergMacLane R)`, via
`reducedFreeTensorSelfIso R` on every sphere level. -/
def eilenbergMacLaneModuleSelfIso :
    eilenbergMacLaneModule R R ≅ Mod.regular (eilenbergMacLane R) :=
  Mod.mkIso
    ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse.mapIso
      (Functor.isoWhiskerLeft (PointedSSet.smashPowFunctor PointedSSet.circle)
        (PointedSSet.reducedFreeTensorSelfIso R))) <| by
    refine ((Mod.isModHom_iff_dayStructureMap (X := eilenbergMacLaneModule R R)
      (Y := Mod.regular (eilenbergMacLane R)) _).mpr fun p q ↦ ?_).smul_hom
    rw [Mod.dayStructureMap_dayMk, Mod.dayStructureMap_def]
    dsimp only [Mod.regular, ModObj.smul, ModObj.regular]
    simp [DayFunctor.η_app_comp_mul_natTrans_app]

@[simp]
lemma eilenbergMacLaneModuleSelfIso_hom_hom_natTrans_app (k : FiniteBijection) :
    (eilenbergMacLaneModuleSelfIso R).hom.hom.natTrans.app k =
      (PointedSSet.reducedFreeTensorSelfIso R).hom.app
        (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneModuleSelfIso, DayFunctor.equiv, Mod.regular]

@[simp]
lemma eilenbergMacLaneModuleSelfIso_inv_hom_natTrans_app (k : FiniteBijection) :
    (eilenbergMacLaneModuleSelfIso R).inv.hom.natTrans.app k =
      (PointedSSet.reducedFreeTensorSelfIso R).inv.app
        (PointedSSet.circle.smashPow (Fin k.len)) := by
  simp [eilenbergMacLaneModuleSelfIso, DayFunctor.equiv, Mod.regular]

variable {R} in
/-- Under `eilenbergMacLaneModuleSelfIso`, the semilinear map induced by `φ : R →+* S` agrees with
the monoid map `eilenbergMacLaneMap φ`. -/
@[reassoc]
lemma
  eilenbergMacLaneModuleSemilinearMap_toSemilinearMap_hom_comp_eilenbergMacLaneModuleSelfIso_hom_hom
    {S : Type} [CommRing S] (φ : R →+* S) :
    (eilenbergMacLaneModuleSemilinearMap φ φ.toSemilinearMap).hom ≫
        (eilenbergMacLaneModuleSelfIso S).hom.hom =
      (eilenbergMacLaneModuleSelfIso R).hom.hom ≫ eilenbergMacLaneMap φ := by
  apply DayFunctor.hom_ext
  ext k : 2
  simp [DayFunctor.comp_natTrans, Mod.comap, Mod.regular]

end SelfIso

end SymmetricSequence

namespace SymmetricSpectrum

/-- The Eilenberg–MacLane symmetric spectrum `HM` of an `R`-module `M`: the `HR`-module
`n ↦ M~[Sⁿ]` of symmetric sequences, regarded as a symmetric spectrum by restricting scalars along
the unit `S ⟶ HR`. -/
-- Written as a structure with an explicit underlying object, exposed and implicitly reducible, so
-- that its levels are those of the symmetric sequence `n ↦ M~[Sⁿ]`.
@[expose, implicit_reducible]
def eilenbergMacLaneModule : SymmetricSpectrum :=
  letI := (SymmetricSequence.eilenbergMacLaneModule R M).mod
  letI := Mod.scalarRestriction (SymmetricSequence.sphereToEilenbergMacLane R)
    (SymmetricSequence.eilenbergMacLaneModule R M).X
  ⟨(SymmetricSequence.eilenbergMacLaneModule R M).X⟩

/-- `HM` is the restriction of scalars of the `HR`-module `n ↦ M~[Sⁿ]` along the unit `S ⟶ HR`. -/
lemma eilenbergMacLaneModule_eq : eilenbergMacLaneModule R M =
    (Mod.comap (SymmetricSequence.sphereToEilenbergMacLane R)).obj
      (SymmetricSequence.eilenbergMacLaneModule R M) :=
  (rfl)

/-- The structure maps `S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` are the generator map on the sphere
factor followed by the action of reduced free `R`-modules and the concatenation of sphere
coordinates. -/
lemma eilenbergMacLaneModule_dayStructureMap (p q : FiniteBijection) :
    (eilenbergMacLaneModule R M).dayStructureMap p q =
      PointedSSet.reducedFreeι R ((PointedSSet.smashPowFunctor PointedSSet.circle).obj p) ▷
          (PointedSSet.reducedFreeTensor R M).obj
            ((PointedSSet.smashPowFunctor PointedSSet.circle).obj q) ≫
        (PointedSSet.reducedFreeTensorCompAct R M
          (PointedSSet.smashPowFunctor PointedSSet.circle)).app (p, q) := by
  refine (Mod.dayStructureMap_comap (SymmetricSequence.sphereToEilenbergMacLane R)
    (SymmetricSequence.eilenbergMacLaneModule R M) p q).trans ?_
  rw [SymmetricSequence.sphereToEilenbergMacLane_natTrans_app, Mod.dayStructureMap_dayMk]
  -- The two sides differ only in how the levels of the spheres and of `M~[S^q]` are written.
  rfl

/-- The structure map `S^p ∧ M~[S^q] ⟶ M~[S^(p+q)]` of `HM` sends `x ∧ Σ yᵢ ⊗ mᵢ` to
`Σ (x ∧ yᵢ) ⊗ mᵢ`, where `x ∧ yᵢ ∈ S^(p+q)` concatenates the sphere coordinates. -/
@[simp]
lemma eilenbergMacLaneModule_dayStructureMap_app_smashMk {p q : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : (PointedSSet.circle.smashPow (Fin p.len)).right.obj n)
    (t : ((PointedSSet.reducedFreeTensor R M).obj
      (PointedSSet.circle.smashPow (Fin q.len))).right.obj n) :
    ((eilenbergMacLaneModule R M).dayStructureMap p q).right.app n (PointedSSet.smashMk x t) =
      LinearMap.rTensor M (ReducedFreeModule.map R (fun y ↦ (Functor.LaxMonoidal.μ
        (PointedSSet.smashPowFunctor PointedSSet.circle) p q).right.app n
          (PointedSSet.smashMk x y)) (by simp)) t := by
  rw [eilenbergMacLaneModule_dayStructureMap,
    PointedSSet.reducedFreeι_whiskerRight_comp_reducedFreeTensorCompAct_app_app_smashMk
      (PointedSSet.smashPowFunctor PointedSSet.circle) p q]

/-- The Eilenberg–MacLane spectrum `HM` as a module object over the commutative ring spectrum `HR`
for the smash product over the sphere, obtained by descending the `HR`-action on symmetric
sequences via `Mod.comapRegularMod`. Its underlying symmetric spectrum is definitionally
`eilenbergMacLaneModule R M`. -/
@[expose]
def eilenbergMacLaneMod : Mod SymmetricSpectrum (eilenbergMacLane R) :=
  (Mod.comapRegularMod (SymmetricSequence.sphereToEilenbergMacLane R)).obj
    (SymmetricSequence.eilenbergMacLaneModule R M)

@[simp]
lemma eilenbergMacLaneMod_X :
    (eilenbergMacLaneMod R M).X = eilenbergMacLaneModule R M :=
  (rfl)

/-- On representatives in `HR ⊗ HM`, the `HR ∧_S HM ⟶ HM` action of `eilenbergMacLaneMod R M` is
the `HR`-action on symmetric sequences. -/
@[reassoc (attr := simp)]
lemma tensorπ_eilenbergMacLaneMod_smul_hom :
    Mod.tensorπ (eilenbergMacLane R) (eilenbergMacLaneMod R M).X ≫
        γ[eilenbergMacLane R, (eilenbergMacLaneMod R M).X].hom =
      (SymmetricSequence.eilenbergMacLaneModule R M).mod.smul :=
  Mod.tensorπ_comapRegularMod_obj_smul_hom _ _

section Map

variable {R M} {S T : Type} [CommRing S] [CommRing T]
  {Q : Type} [AddCommGroup Q] [Module S Q]
  {W : Type} [AddCommGroup W] [Module T W]

/-- A ring homomorphism `φ : R →+* S` and a `φ`-semilinear map `g : M →ₛₗ[φ] Q` induce a morphism
of `HR`-module spectra `HM ⟶ (Mod.comap (eilenbergMacLaneMap φ)).obj HQ`. -/
def eilenbergMacLaneModSemilinearMap (φ : R →+* S) (g : M →ₛₗ[φ] Q) :
    eilenbergMacLaneMod R M ⟶
      (Mod.comap (eilenbergMacLaneMap φ)).obj (eilenbergMacLaneMod S Q) :=
  (Mod.comapRegularMod (SymmetricSequence.sphereToEilenbergMacLane R)).map
    (SymmetricSequence.eilenbergMacLaneModuleSemilinearMap φ g) ≫
    (Mod.comapRegularModComapIso (SymmetricSequence.sphereToEilenbergMacLane R)
      (SymmetricSequence.sphereToEilenbergMacLane S)
      (SymmetricSequence.eilenbergMacLaneMap φ)
      (SymmetricSequence.sphereToEilenbergMacLane_comp_eilenbergMacLaneMap φ)).hom.app
      (SymmetricSequence.eilenbergMacLaneModule S Q)

/-- The map of symmetric spectra `HM ⟶ HQ` induced by a `φ`-semilinear map `g : M →ₛₗ[φ] Q`: the
map underlying `eilenbergMacLaneModSemilinearMap φ g`. For `φ = RingHom.id R` this is the change
of coefficients along an `R`-linear map `M →ₗ[R] N`. -/
def eilenbergMacLaneModuleMap {φ : R →+* S} (g : M →ₛₗ[φ] Q) :
    eilenbergMacLaneModule R M ⟶ eilenbergMacLaneModule S Q :=
  (eilenbergMacLaneModSemilinearMap φ g).hom

@[simp]
lemma eilenbergMacLaneModSemilinearMap_hom (φ : R →+* S) (g : M →ₛₗ[φ] Q) :
    (eilenbergMacLaneModSemilinearMap φ g).hom = eilenbergMacLaneModuleMap g :=
  (rfl)

@[simp]
lemma eilenbergMacLaneModuleMap_hom {φ : R →+* S} (g : M →ₛₗ[φ] Q) :
    (eilenbergMacLaneModuleMap g).hom =
      (SymmetricSequence.eilenbergMacLaneModuleSemilinearMap φ g).hom := by
  dsimp only [eilenbergMacLaneModuleMap, eilenbergMacLaneModSemilinearMap, eilenbergMacLaneMod,
    eilenbergMacLaneMap]
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comapRegularMod_map_hom, Mod.comap_map_hom,
    Mod.comapRegularModComapIso_hom_app_hom_hom]
  exact Category.comp_id _

@[simp]
lemma eilenbergMacLaneModuleMap_id :
    eilenbergMacLaneModuleMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  ext : 1
  simp [eilenbergMacLaneModule]

lemma eilenbergMacLaneModuleMap_comp
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} [RingHomCompTriple φ ψ χ]
    (g : M →ₛₗ[φ] Q) (h : Q →ₛₗ[ψ] W) :
    eilenbergMacLaneModuleMap (h.comp g) =
      eilenbergMacLaneModuleMap g ≫ eilenbergMacLaneModuleMap h := by
  ext : 1
  simp only [Mod.comp_hom', eilenbergMacLaneModuleMap_hom]
  exact SymmetricSequence.eilenbergMacLaneModuleSemilinearMap_comp_hom g h

end Map

variable {M} {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The morphism of `HR`-module spectra `HM ⟶ HN` induced by an `R`-linear map `g : M →ₗ[R] N`. -/
def eilenbergMacLaneModMap (g : M →ₗ[R] N) :
    eilenbergMacLaneMod R M ⟶ eilenbergMacLaneMod R N :=
  (Mod.comapRegularMod (SymmetricSequence.sphereToEilenbergMacLane R)).map
    (SymmetricSequence.eilenbergMacLaneModuleMap R g)

@[simp]
lemma eilenbergMacLaneModMap_hom (g : M →ₗ[R] N) :
    (eilenbergMacLaneModMap R g).hom = eilenbergMacLaneModuleMap g := by
  ext : 1
  simp only [eilenbergMacLaneModMap, Mod.comapRegularMod_map_hom, Mod.comap_map_hom,
    eilenbergMacLaneModuleMap_hom,
    SymmetricSequence.eilenbergMacLaneModuleSemilinearMap_ringHomId_hom]
  rfl

@[simp]
lemma eilenbergMacLaneModMap_id :
    eilenbergMacLaneModMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  ext : 1
  simp only [eilenbergMacLaneModMap_hom, eilenbergMacLaneModuleMap_id, Mod.id_hom']
  rfl

lemma eilenbergMacLaneModMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    eilenbergMacLaneModMap R (h ∘ₗ g) =
      eilenbergMacLaneModMap R g ≫ eilenbergMacLaneModMap R h := by
  ext : 1
  simp only [Mod.comp_hom', eilenbergMacLaneModMap_hom, eilenbergMacLaneModuleMap_comp]
  rfl

section SelfIso

/-- As an `HR`-module spectrum, `eilenbergMacLaneMod R R` is isomorphic to the regular `HR`-module
`Mod.regular (eilenbergMacLane R)`, via `reducedFreeTensorSelfIso R` on every sphere level. -/
def eilenbergMacLaneModSelfIso :
    eilenbergMacLaneMod R R ≅ Mod.regular (eilenbergMacLane R) :=
  (Mod.comapRegularMod (SymmetricSequence.sphereToEilenbergMacLane R)).mapIso
    (SymmetricSequence.eilenbergMacLaneModuleSelfIso R) ≪≫
    Mod.comapRegularModRegularIso (SymmetricSequence.sphereToEilenbergMacLane R)

/-- As a symmetric spectrum, `eilenbergMacLaneModule R R` is isomorphic to `eilenbergMacLane R`,
via `reducedFreeTensorSelfIso R` on every sphere level. -/
def eilenbergMacLaneModuleSelfIso :
    eilenbergMacLaneModule R R ≅ eilenbergMacLane R :=
  (Mod.forget (eilenbergMacLane R)).mapIso (eilenbergMacLaneModSelfIso R)

@[simp]
lemma eilenbergMacLaneModSelfIso_hom_hom :
    (eilenbergMacLaneModSelfIso R).hom.hom = (eilenbergMacLaneModuleSelfIso R).hom :=
  ((Functor.mapIso_hom (Mod.forget (eilenbergMacLane R)) (eilenbergMacLaneModSelfIso R)).trans
    (Mod.forget_map (eilenbergMacLane R) (eilenbergMacLaneModSelfIso R).hom)).symm

@[simp]
lemma eilenbergMacLaneModSelfIso_inv_hom :
    (eilenbergMacLaneModSelfIso R).inv.hom = (eilenbergMacLaneModuleSelfIso R).inv :=
  ((Functor.mapIso_inv (Mod.forget (eilenbergMacLane R)) (eilenbergMacLaneModSelfIso R)).trans
    (Mod.forget_map (eilenbergMacLane R) (eilenbergMacLaneModSelfIso R).inv)).symm

@[simp]
lemma eilenbergMacLaneModuleSelfIso_hom_hom :
    (eilenbergMacLaneModuleSelfIso R).hom.hom =
      (SymmetricSequence.eilenbergMacLaneModuleSelfIso R).hom.hom := by
  rw [← eilenbergMacLaneModSelfIso_hom_hom]
  dsimp only [eilenbergMacLaneModSelfIso, eilenbergMacLaneMod]
  rw [Iso.trans_hom, Mod.comp_hom', Mod.comp_hom', Functor.mapIso_hom,
    Mod.comapRegularMod_map_hom, Mod.comap_map_hom, Mod.comapRegularModRegularIso_hom_hom,
    Mod.id_hom']
  exact Category.comp_id _

@[simp]
lemma eilenbergMacLaneModuleSelfIso_inv_hom :
    (eilenbergMacLaneModuleSelfIso R).inv.hom =
      (SymmetricSequence.eilenbergMacLaneModuleSelfIso R).inv.hom := by
  rw [← eilenbergMacLaneModSelfIso_inv_hom]
  dsimp only [eilenbergMacLaneModSelfIso, eilenbergMacLaneMod]
  rw [Iso.trans_inv, Mod.comp_hom', Mod.comp_hom', Functor.mapIso_inv,
    Mod.comapRegularMod_map_hom, Mod.comap_map_hom, Mod.comapRegularModRegularIso_inv_hom,
    Mod.id_hom']
  exact Category.id_comp _

variable {R} in
/-- Under `eilenbergMacLaneModuleSelfIso`, the semilinear spectrum map induced by `φ : R →+* S`
agrees with the ring spectrum map `eilenbergMacLaneMap φ : HR ⟶ HS`. -/
@[reassoc]
lemma eilenbergMacLaneModuleMap_toSemilinearMap_comp_eilenbergMacLaneModuleSelfIso_hom
    {S : Type} [CommRing S] (φ : R →+* S) :
    eilenbergMacLaneModuleMap φ.toSemilinearMap ≫
        (eilenbergMacLaneModuleSelfIso S).hom =
      (eilenbergMacLaneModuleSelfIso R).hom ≫ eilenbergMacLaneMap φ := by
  ext : 1
  simp only [Mod.comp_hom', eilenbergMacLaneModuleMap_hom, eilenbergMacLaneModuleSelfIso_hom_hom,
    eilenbergMacLaneMap_hom]
  exact open SymmetricSequence in
  eilenbergMacLaneModuleSemilinearMap_toSemilinearMap_hom_comp_eilenbergMacLaneModuleSelfIso_hom_hom
    φ

end SelfIso

end SymmetricSpectrum

end Module

end

end TauCeti
