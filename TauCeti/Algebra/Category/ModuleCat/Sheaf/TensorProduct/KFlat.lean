/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat
public import TauCeti.Algebra.Homology.CochainComplex.ProjectiveResolution
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# K-flat resolutions of complexes of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. Every cochain complex `K` of sheaves of
`R`-modules, without any boundedness assumption, receives a quasi-isomorphism from a K-flat
complex of flat sheaves of modules (`CochainComplex.exists_quasiIso_isKFlat_sheafOfModules`). If
`K` is strictly bounded above by `n`, the resolution can be chosen strictly bounded above by `n`
as well (`CochainComplex.exists_quasiIso_isKFlat_sheafOfModules_of_isStrictlyLE`). No points of
the site are used.

In both cases the flat sheaves of modules are sheafifications of projective presheaves of modules
(`PresheafOfModules.preservesFiniteLimits_tensorLeft_sheafification_obj_of_projective`). In the
bounded above case, the underlying complex of presheaves of modules of `K` has a resolution by a
bounded above complex of projective presheaves of modules
(`CochainComplex.exists_quasiIso_projective`, since presheaves of modules have enough
projectives). Sheafification is exact, so it carries this resolution to a quasi-isomorphism onto
the sheafification of the underlying complex of `K`, which is `K` itself, and a bounded above
complex of flat objects is K-flat (`CochainComplex.isKFlat_of_boundedAbove_flat`).

In general, every sheaf of modules `X` is a quotient of the sheafification of a projective
presheaf of modules mapping onto the underlying presheaf of `X`. Since sequential colimits and
countable coproducts of sheaves of modules are exact and commute with tensor products, the cell
attachment construction `CochainComplex.kFlatResolution` along these quotient maps is a K-flat
resolution of `K` with flat terms.

The cover of a sheaf of modules by the sheafification of the free presheaf of modules on its
underlying presheaf of sets is functorial and flat
(`PresheafOfModules.preservesFiniteLimits_tensorLeft_sheafification_free_obj`), and it is the
counit of the composite of the free-forgetful adjunction of presheaves of modules with the
sheafification adjunction, hence an epimorphism. The functorial cell attachment construction
along it makes the inclusion of K-flat complexes a left derivability structure for
quasi-isomorphisms
(`CochainComplex.KFlat.instIsLeftDerivabilityStructureLocalizerMorphismSheafOfModules`).

These are the K-flat replacements from which derived tensor products of complexes of sheaves of
modules are computed (`TauCeti.derivedTensor`).

Since the free module sheaf on an object of the site is flat, tensoring with it preserves acyclic
complexes (`SheafOfModules.acyclic_tensorRight_freeYonedaFunctor_obj`).

## References

* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

open TauCeti.SheafOfModules

namespace CochainComplex

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

/-- Graded objects of sheaves of modules have the totalized tensor products of Mathlib's monoidal
structure on graded objects, since tensor products of sheaves of modules preserve coproducts.
This shortcut lets instance search find the family of these instances, indexed by all pairs of
graded objects, within its default size limit for the structure sheaf of a scheme. -/
instance
    (K L : GradedObject ℤ (SheafOfModules.{u} (ringCatSheaf R))) : GradedObject.HasTensor K L :=
  inferInstance

/-- Cochain complexes of sheaves of modules have totalized tensor products. This shortcut lets
instance search find the family of these instances, indexed by all pairs of complexes, within its
default size limit for the structure sheaf of a scheme. -/
instance (K L : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) :
    HomologicalComplex.HasTensor K L :=
  inferInstance

/-- A cochain complex of sheaves of modules over a sheaf of commutative rings which is strictly
bounded above by `n` receives a quasi-isomorphism from a K-flat complex of flat sheaves of modules
which is also strictly bounded above by `n`. -/
theorem exists_quasiIso_isKFlat_sheafOfModules_of_isStrictlyLE
    (K : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) (π : P ⟶ K) (_ : QuasiIso π)
      (_ : ∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) (_ : P.IsKFlat), P.IsStrictlyLE n := by
  let ι := (SheafOfModules.forget (ringCatSheaf R)).mapHomologicalComplex (.up ℤ)
  let a := PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)
  have : CochainComplex.IsStrictlyLE (ι.obj K) n :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K _ n).2 inferInstance
  obtain ⟨P, π, _, hP, _⟩ := CochainComplex.exists_quasiIso_projective (ι.obj K) n
  -- resolve the underlying complex of presheaves by projectives, then sheafify;
  -- sheafifying the underlying complex of `K` recovers `K`
  let e : (a.mapHomologicalComplex (.up ℤ)).obj (ι.obj K) ≅ K :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ sheafificationIso _ (K.X i))
      (fun _ _ _ ↦ (sheafificationIso_hom_naturality (K.d _ _)).symm)
  have hflat (i : ℤ) : PreservesFiniteLimits
      (tensorLeft (((a.mapHomologicalComplex (.up ℤ)).obj P).X i)) :=
    PresheafOfModules.preservesFiniteLimits_tensorLeft_sheafification_obj_of_projective (P.X i)
  have : CochainComplex.IsStrictlyLE ((a.mapHomologicalComplex (.up ℤ)).obj P) n :=
    (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi ↦
      a.map_isZero (P.isZero_of_isStrictlyLE n i hi)
  have : a.Additive := a.additive_of_preserves_binary_products
  have : QuasiIso ((a.mapHomologicalComplex (.up ℤ)).map π) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π a
  -- filtered colimits of sheaves of modules are exact, also for the small index category `ℕ`
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} (ringCatSheaf R)) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  exact ⟨_, (a.mapHomologicalComplex (.up ℤ)).map π ≫ e.hom, inferInstance, hflat,
    CochainComplex.isKFlat_of_boundedAbove_flat _ n, inferInstance⟩

/-- Every cochain complex of sheaves of modules over a sheaf of commutative rings, without any
boundedness assumption, receives a quasi-isomorphism from a K-flat complex of flat sheaves of
modules. -/
theorem exists_quasiIso_isKFlat_sheafOfModules
    (K : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) (π : P ⟶ K) (_ : QuasiIso π)
      (_ : ∀ i, PreservesFiniteLimits (tensorLeft (P.X i))), P.IsKFlat := by
  let F := SheafOfModules.forget (ringCatSheaf R)
  let a := PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)
  -- cover every sheaf of modules by the sheafification of a projective presheaf of modules
  -- mapping onto its underlying presheaf
  let E (X : SheafOfModules.{u} (ringCatSheaf R)) := a.obj (Projective.over (F.obj X))
  let p (X : SheafOfModules.{u} (ringCatSheaf R)) : E X ⟶ X :=
    a.map (Projective.π (F.obj X)) ≫ (sheafificationIso _ X).hom
  -- instance search does not find that the isomorphism `sheafificationIso _ X` is an
  -- epimorphism when it is composed after `a.map _`, so this is supplied explicitly
  have (X : SheafOfModules.{u} (ringCatSheaf R)) : Epi (p X) :=
    epi_comp' (a.map_epi _) (IsIso.epi_of_iso (sheafificationIso _ X).hom)
  -- filtered colimits of sheaves of modules are exact, also for the small index categories `ℕ`
  -- and `Discrete ℤ`
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} (ringCatSheaf R)) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  -- `CountableAB4.of_countableAB5` assumes finite biproducts, which abelian categories have by
  -- the theorem `Abelian.hasFiniteBiproducts`
  have : HasFiniteBiproducts (SheafOfModules.{u} (ringCatSheaf R)) := Abelian.hasFiniteBiproducts
  have : CountableAB4 (SheafOfModules.{u} (ringCatSheaf R)) := CountableAB4.of_countableAB5 _
  exact ⟨_, kFlatResolution.π E p K, inferInstance, inferInstance, inferInstance⟩

namespace KFlat

/-- **The K-flat left derivability structure on complexes of sheaves of modules.** Over a sheaf of
commutative rings on a small site, the inclusion of K-flat cochain complexes of sheaves of modules
into all cochain complexes is a left derivability structure with respect to quasi-isomorphisms. -/
instance instIsLeftDerivabilityStructureLocalizerMorphismSheafOfModules :
    (localizerMorphism (SheafOfModules.{u} (ringCatSheaf R))).IsLeftDerivabilityStructure := by
  -- the free sheaf of modules on a presheaf of sets is left adjoint to the underlying presheaf of
  -- sets, whose counit is the functorial flat cover
  let F := (SheafOfModules.forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)) ⋙
      PresheafOfModules.toPresheaf (ringCatSheaf R).obj ⋙
        (Functor.whiskeringRight Cᵒᵖ Ab (Type u)).obj (forget Ab)
  let adj : PresheafOfModules.free (ringCatSheaf R).obj ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj) ⊣ F :=
    (PresheafOfModules.freeAdjunction (ringCatSheaf R).obj).comp
      (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringCatSheaf R).obj))
  -- filtered colimits of sheaves of modules are exact, also for the small index categories `ℕ`
  -- and `Discrete ℤ`
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} (ringCatSheaf R)) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  -- `CountableAB4.of_countableAB5` assumes finite biproducts, which abelian categories have by
  -- the theorem `Abelian.hasFiniteBiproducts`
  have : HasFiniteBiproducts (SheafOfModules.{u} (ringCatSheaf R)) := Abelian.hasFiniteBiproducts
  have : CountableAB4 (SheafOfModules.{u} (ringCatSheaf R)) := CountableAB4.of_countableAB5 _
  -- the cover `(F ⋙ free ⋙ sheafification).obj X` unfolds to the sheafification of a free
  -- presheaf of modules only through `Functor.comp_obj`, which instance search does not unfold
  have (X : SheafOfModules.{u} (ringCatSheaf R)) : PreservesFiniteLimits (tensorLeft
      ((F ⋙ PresheafOfModules.free (ringCatSheaf R).obj ⋙
        PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj X)) :=
    PresheafOfModules.preservesFiniteLimits_tensorLeft_sheafification_free_obj (F.obj X)
  exact isLeftDerivabilityStructure_localizerMorphism _ adj.counit

end KFlat

end CochainComplex

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

/-- Tensoring on the right with the free module sheaf on an object `U` of the site preserves
acyclic complexes of sheaves of modules, since that sheaf is flat
(`SheafOfModules.preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj`). -/
theorem acyclic_tensorRight_freeYonedaFunctor_obj (U : C)
    {E : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ} (hE : E.Acyclic) :
    (((tensorRight ((freeYonedaFunctor (ringCatSheaf R)).obj U)).mapHomologicalComplex
      _).obj E).Acyclic := by
  let G := (freeYonedaFunctor (ringCatSheaf R)).obj U
  have : PreservesFiniteLimits (tensorRight G) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
  have : PreservesFiniteColimits (tensorRight G) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
  intro i
  have := hE i
  rw [HomologicalComplex.exactAt_iff] at this ⊢
  exact this.map (tensorRight G)

end SheafOfModules
