/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Perfect
public import TauCeti.Algebra.Homology.Periodic.Compression.Derived
public import TauCeti.Algebra.Homology.Periodic.Compression.FullyFaithful
public import TauCeti.Algebra.Homology.Periodic.GlobalDimension

/-!
# The derived orbit functor in finite global dimension

Let `C` be an abelian category with enough projectives in which every object has projective
dimension `< d`, and let `n` be positive. Then the orbit functor
`TauCeti.PeriodicComplex.orbitDerivedCompressionFunctor n : D^b(C)/[n] ⥤ D_n(C)`, the descent of
compression `D^b(C) ⥤ D_n(C)` to the orbit category, is fully faithful
(`TauCeti.PeriodicComplex.fullyFaithfulOrbitDerivedCompressionFunctor`):

`⨁_{j : ℤ} Hom_{D^b(C)}(X, Y⟦n * j⟧) ≅ Hom_{D_n(C)}(Δₙ X, Δₙ Y)`.

For finitely generated modules over a finite-dimensional algebra of finite global dimension, this
is Stai's Lemma 3.12.

The proof reduces to the full faithfulness of the orbit functor `K^b(C)/[n] ⥤ K_n(C)` on homotopy
categories, which holds without any hypothesis on `C`
(`TauCeti.PeriodicComplex.full_orbitCompressionFunctor`). In finite global dimension:

* every object of `D^b(C)` is the image of a bounded complex of projectives
  (`DerivedCategory.Bounded.exists_projective_Qh_obj_iso_of_hasProjectiveDimensionLT`);
* the localization `K^b(C) ⥤ D^b(C)` is bijective on morphisms out of such a complex
  (`TauCeti.DerivedCategory.Bounded.Qh_map_bijective_of_projective`), hence so is the induced
  functor `K^b(C)/[n] ⥤ D^b(C)/[n]` on orbit morphisms
  (`TauCeti.OrbitCategory.map_map_bijective_iff`);
* the compression of a bounded complex of projectives is a periodic complex of projectives, so it
  is homotopically projective (`TauCeti.PeriodicComplex.isHomotopicallyProjective_of_projective`)
  and the localization `K_n(C) ⥤ D_n(C)` is bijective on morphisms out of it.

So, on the full subcategory of `K^b(C)/[n]` on the bounded complexes of projectives, the functor
to `D^b(C)/[n]` is an equivalence, and the composite with the derived orbit functor is the
homotopy orbit functor followed by `K_n(C) ⥤ D_n(C)`
(`TauCeti.PeriodicComplex.orbitDerivedCompressionFunctorFactors`), which is fully faithful there.

The finite global dimension hypothesis is used twice, for the bounded projective representatives
in `D^b(C)` and for the homotopical projectivity of their compressions. The positivity of `n` is
needed already for the homotopy orbit functor.

## Main results

* `TauCeti.PeriodicComplex.fullyFaithfulOrbitDerivedCompressionFunctor`: in finite global
  dimension, the orbit functor `D^b(C)/[n] ⥤ D_n(C)` is fully faithful.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3 and Lemma 3.12.
* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (n : ℕ)

/-- The bounded complexes of projective objects. -/
private abbrev BoundedProjective (C : Type u) [Category.{v} C] [Abelian C] :=
  {K : CochainComplex.Bounded C // ∀ i, Projective (K.obj.X i)}

/-- The class of a bounded complex of projective objects, as an object of `K^b(C)/[n]`. -/
private abbrev orbitObj (K : BoundedProjective C) :
    OrbitCategory (HomotopyCategory.Bounded C) n :=
  ⟨(HomotopyCategory.Bounded.quotient C).obj K.1⟩

/-- The compression of a bounded complex of projective objects is homotopically projective, in
finite global dimension. -/
private lemma leftOrthogonal_homotopyCompressionFunctor_obj [EnoughProjectives C] (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) (K : BoundedProjective C) :
    (subcategoryAcyclic C n).leftOrthogonal
      ((homotopyCompressionFunctor n).obj ((HomotopyCategory.Bounded.quotient C).obj K.1)) := by
  have := K.2
  have := isHomotopicallyProjective_of_projective d hd (compression n K.1.obj)
  refine (subcategoryAcyclic C n).leftOrthogonal.prop_of_iso
    ((quotientCompHomotopyCompressionFunctorIso n).app K.1).symm ?_
  rw [Functor.comp_obj, compressionFunctor_obj]
  exact IsHomotopicallyProjective.leftOrthogonal _

variable [HasDerivedCategory.{w} C]

open TauCeti.DerivedCategory.Bounded in
/-- The functor `K^b(C)/[n] ⥤ D^b(C)/[n]` is bijective on orbit morphisms between bounded
complexes of projective objects. -/
private lemma map_Qh_map_bijective (K L : BoundedProjective C) :
    Function.Bijective ((OrbitCategory.map (n := (n : ℤ)) (Qh C)).map :
      (orbitObj n K ⟶ orbitObj n L) → _) := by
  rw [OrbitCategory.map_map_bijective_iff]
  intro j
  have h := Qh_map_bijective_of_projective K.1 K.2
    (((HomotopyCategory.Bounded.quotient C).obj L.1)⟦(n : ℤ) * j⟧)
  refine ⟨fun f g hfg ↦ h.1 ((cancel_mono (((Qh C).commShiftIso _).hom.app _)).1
    (by simpa only [ShiftedHom.map] using hfg)), fun g ↦ ?_⟩
  obtain ⟨f, hf⟩ := h.2 (g ≫ ((Qh C).commShiftIso _).inv.app _)
  exact ⟨f, by simp [ShiftedHom.map, hf]⟩

/-- The functor from bounded complexes of projective objects to `D^b(C)/[n]`. -/
private noncomputable abbrev toOrbit :
    InducedCategory (OrbitCategory (HomotopyCategory.Bounded C) n) (orbitObj n) ⥤
      OrbitCategory (_root_.DerivedCategory.Bounded C) n :=
  inducedFunctor _ ⋙ OrbitCategory.map (TauCeti.DerivedCategory.Bounded.Qh C)

/-- The functor from bounded complexes of projective objects to `D^b(C)/[n]` is fully
faithful. -/
private noncomputable def fullyFaithfulToOrbit : (toOrbit (C := C) n).FullyFaithful :=
  Classical.choice <| (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 fun K L ↦
    (map_Qh_map_bijective n K L).comp InducedCategory.homEquiv.bijective

/-- In finite global dimension, every object of `D^b(C)/[n]` is the image of a bounded complex of
projective objects. -/
private lemma essSurj_toOrbit [EnoughProjectives C] (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) : (toOrbit (C := C) n).EssSurj where
  mem_essImage A := by
    obtain ⟨K, hK, ⟨e⟩⟩ :=
      DerivedCategory.Bounded.exists_projective_Qh_obj_iso_of_hasProjectiveDimensionLT d hd A.obj
    exact ⟨⟨K, hK⟩, ⟨OrbitCategory.projection.mapIso e⟩⟩

/-- On bounded complexes of projective objects, the derived orbit functor is fully faithful, in
finite global dimension: it is the homotopy orbit functor followed by the localization
`K_n(C) ⥤ D_n(C)`, which is bijective on morphisms out of compressions of complexes of
projectives. -/
private noncomputable def fullyFaithfulToOrbitComp [EnoughProjectives C] [NeZero n] (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (toOrbit (C := C) n ⋙ orbitDerivedCompressionFunctor n).FullyFaithful := by
  refine Functor.FullyFaithful.ofIso (F := inducedFunctor (orbitObj n) ⋙
    orbitCompressionFunctor n ⋙ DerivedCategory.Qh C n) ?_
    (Functor.isoWhiskerLeft _ (orbitDerivedCompressionFunctorFactors n).symm ≪≫
      (Functor.associator _ _ _).symm)
  refine Classical.choice <| (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 fun K L ↦ ?_
  exact ((leftOrthogonal_homotopyCompressionFunctor_obj n d hd K).map_bijective_of_isTriangulated
    (DerivedCategory.Qh C n) _).comp
      (((Functor.FullyFaithful.ofFullyFaithful (orbitCompressionFunctor (C := C) n)).map_bijective
        _ _).comp InducedCategory.homEquiv.bijective)

/-- **The derived orbit functor is fully faithful in finite global dimension** (Stai,
Lemma 3.12). Let `C` be an abelian category with enough projectives in which every object has
projective dimension `< d`, and let `n` be positive. Then the orbit functor
`D^b(C)/[n] ⥤ D_n(C)` induced by compression is fully faithful:
`⨁_{j : ℤ} Hom_{D^b(C)}(X, Y⟦n * j⟧) ≅ Hom_{D_n(C)}(Δₙ X, Δₙ Y)`. -/
noncomputable def fullyFaithfulOrbitDerivedCompressionFunctor [EnoughProjectives C] [NeZero n]
    (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (orbitDerivedCompressionFunctor (C := C) n).FullyFaithful :=
  have := (fullyFaithfulToOrbit (C := C) n).full
  have := (fullyFaithfulToOrbit (C := C) n).faithful
  have := essSurj_toOrbit (C := C) n d hd
  have : (toOrbit (C := C) n).IsEquivalence := {}
  let E := (toOrbit (C := C) n).asEquivalence
  (E.fullyFaithfulInverse.comp (fullyFaithfulToOrbitComp n d hd)).ofIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.counitIso _ ≪≫
      Functor.leftUnitor _)

end TauCeti.PeriodicComplex
