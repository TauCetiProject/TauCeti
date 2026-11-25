/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# Smooth representations form an abelian category

Let `A` be a ring and `G` a topological group with separately continuous multiplication. The
property "smooth" on `Rep A G` contains the zero representation and is closed under subobjects,
quotients and binary products, hence under kernels, cokernels and finite products. By Mathlib's
`CategoryTheory.ObjectProperty` results on subcategories of abelian categories
(`Mathlib.CategoryTheory.Abelian.Subcategory`), the full subcategory `SmoothRep A G` is abelian,
its kernels and cokernels are computed in `Rep A G`, and the inclusion `SmoothRep A G ⥤ Rep A G`
preserves them. A morphism of smooth representations is a monomorphism (epimorphism) exactly when
it is injective (surjective).

A subobject keeps open stabilizers because an injective intertwining map does not shrink the
stabilizer of a vector (`Representation.IsSmooth.of_injective`); a quotient does because the
stabilizer of the image of `v` contains that of `v` (`Representation.IsSmooth.of_surjective`, which
uses the separately continuous multiplication); and a vector of a binary product is fixed by the
intersection of the stabilizers of its two components (`Representation.instIsSmoothProd`).

## Main results

* `TauCeti.SmoothRep.isClosedUnderSubobjects`, `TauCeti.SmoothRep.isClosedUnderQuotients`,
  `TauCeti.SmoothRep.containsZero`, `TauCeti.SmoothRep.isClosedUnderFiniteProducts`: the closure
  properties of smoothness on `Rep A G`.
* `TauCeti.SmoothRep.abelian`: `SmoothRep A G` is an abelian category.
* `TauCeti.SmoothRep.mono_iff_injective`, `TauCeti.SmoothRep.epi_iff_surjective`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1 and §2.
-/

@[expose] public section

open CategoryTheory Limits Representation

universe w u v

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [Ring A] (G : Type v) [Group G] [TopologicalSpace G]

/-- The property "smooth" on `Rep A G`, the property cutting out `SmoothRep A G`. -/
abbrev isSmoothProperty : ObjectProperty (Rep.{w} A G) := fun V ↦ IsSmooth V.ρ

/-- **Smoothness passes to subobjects**: a representation with a monomorphism into a smooth
representation is smooth. -/
instance isClosedUnderSubobjects : (isSmoothProperty.{w} A G).IsClosedUnderSubobjects where
  prop_of_mono f _ hY :=
    haveI : IsSmooth _ := hY
    IsSmooth.of_injective f.hom ((Rep.mono_iff_injective f).1 inferInstance)

/-- The zero representation is smooth. -/
instance containsZero : (isSmoothProperty.{w} A G).ContainsZero where
  exists_zero := ⟨Rep.trivial A G PUnit, (Rep.isZero_iff _).2 inferInstance,
    show IsSmooth (trivial A G PUnit) from inferInstance⟩

variable [SeparatelyContinuousMul G]

/-- **Smoothness passes to quotients**: the target of an epimorphism from a smooth
representation is smooth. -/
instance isClosedUnderQuotients : (isSmoothProperty.{w} A G).IsClosedUnderQuotients where
  prop_of_epi f _ hX :=
    haveI : IsSmooth _ := hX
    IsSmooth.of_surjective f.hom ((Rep.epi_iff_surjective f).1 inferInstance)

/-- The cone over a functor from `Discrete WalkingPair` given by the concrete product
representation and its two projections. -/
noncomputable def concreteProdCone (F : Discrete WalkingPair ⥤ Rep.{w} A G) : Cone F where
  pt := (Rep.binaryBicone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)).pt
  π := Discrete.natTrans fun
    | ⟨.left⟩ => (Rep.binaryBicone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)).fst
    | ⟨.right⟩ => (Rep.binaryBicone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)).snd

/-- **Smoothness passes to binary products**: the limit point of a binary product diagram of
smooth representations is smooth, as it embeds into the concrete product representation. -/
instance isClosedUnderBinaryProducts : (isSmoothProperty.{w} A G).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let F := p.diag
    let B := Rep.binaryBicone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)
    let m : X ⟶ B.pt := (Rep.binaryBiconeIsBilimit _ _).isLimit.lift
      (BinaryFan.mk (p.π.app ⟨.left⟩) (p.π.app ⟨.right⟩))
    let u : B.pt ⟶ X := p.isLimit.lift (concreteProdCone A G F)
    have hmu : m ≫ u = 𝟙 X := p.isLimit.hom_ext fun j ↦ by
      rw [Category.assoc, Category.id_comp]
      refine (congrArg (m ≫ ·) (p.isLimit.fac (concreteProdCone A G F) j)).trans ?_
      rcases j with ⟨_ | _⟩
      · exact (Rep.binaryBiconeIsBilimit _ _).isLimit.fac
          (BinaryFan.mk (p.π.app ⟨.left⟩) (p.π.app ⟨.right⟩)) ⟨.left⟩
      · exact (Rep.binaryBiconeIsBilimit _ _).isLimit.fac
          (BinaryFan.mk (p.π.app ⟨.left⟩) (p.π.app ⟨.right⟩)) ⟨.right⟩
    have : Mono m := ⟨fun g h hgh ↦ by
      simpa [Category.assoc, hmu] using congrArg (· ≫ u) hgh⟩
    have : IsSmooth (F.obj ⟨.left⟩).ρ := p.prop_diag_obj _
    have : IsSmooth (F.obj ⟨.right⟩).ρ := p.prop_diag_obj _
    exact (isSmoothProperty A G).prop_of_mono m
      (show IsSmooth ((F.obj ⟨.left⟩).ρ.prod (F.obj ⟨.right⟩).ρ) from inferInstance)

/-- **Smoothness passes to finite products.** -/
instance isClosedUnderFiniteProducts : (isSmoothProperty.{w} A G).IsClosedUnderFiniteProducts :=
  .mk'

/-- **Smooth representations form an abelian category**, a full subcategory of `Rep A G` closed
under kernels, cokernels and finite products. -/
noncomputable instance abelian : Abelian (SmoothRep.{w} A G) :=
  inferInstanceAs (Abelian (isSmoothProperty.{w} A G).FullSubcategory)

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves kernels. -/
instance preservesKernels_ι {V W : SmoothRep.{w} A G} (f : V ⟶ W) :
    PreservesLimit (parallelPair f 0) (ι.{w} A G) :=
  (isSmoothProperty A G).preservesKernels_ι f

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves cokernels. -/
instance preservesCokernels_ι {V W : SmoothRep.{w} A G} (f : V ⟶ W) :
    PreservesColimit (parallelPair f 0) (ι.{w} A G) :=
  (isSmoothProperty A G).preservesCokernels_ι f

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves monomorphisms. -/
instance preservesMonomorphisms_ι : (ι.{w} A G).PreservesMonomorphisms :=
  (isSmoothProperty A G).preservesMonomorphisms_ι_of_isNormalEpiCategory

/-- The inclusion `SmoothRep A G ⥤ Rep A G` preserves epimorphisms. -/
instance preservesEpimorphisms_ι : (ι.{w} A G).PreservesEpimorphisms :=
  (isSmoothProperty A G).preservesEpimorphisms_ι_of_isNormalMonoCategory

variable {A G}

/-- A morphism of smooth representations is a monomorphism exactly when it is injective. -/
theorem mono_iff_injective {V W : SmoothRep.{w} A G} (f : V ⟶ W) :
    Mono f ↔ Function.Injective f.hom.hom :=
  ⟨fun _ ↦ (Rep.mono_iff_injective ((ι A G).map f)).1 inferInstance,
    fun h ↦ (ι A G).mono_of_mono_map ((Rep.mono_iff_injective _).2 h)⟩

/-- A morphism of smooth representations is an epimorphism exactly when it is surjective. -/
theorem epi_iff_surjective {V W : SmoothRep.{w} A G} (f : V ⟶ W) :
    Epi f ↔ Function.Surjective f.hom.hom :=
  ⟨fun _ ↦ (Rep.epi_iff_surjective ((ι A G).map f)).1 inferInstance,
    fun h ↦ (ι A G).epi_of_epi_map ((Rep.epi_iff_surjective _).2 h)⟩

end SmoothRep

end TauCeti
