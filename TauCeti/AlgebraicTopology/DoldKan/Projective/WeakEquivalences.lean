/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy

/-!
# Weak equivalences between projective simplicial objects under non-additive functors

Building on `TauCeti.AlgebraicTopology.DoldKan.SimplicialHomotopy`, this file develops the
weak-equivalence layer of Albrecht Dold and Dieter Puppe's theory of derived non-additive
functors. Because levelwise postcomposition `(SimplicialObject.whiskering C D).obj F` by *any*
functor `F : C ⥤ D` preserves simplicial homotopies—even when `F` is non-additive—it sends weak
equivalences between degreewise projective simplicial objects to chain homotopy equivalences and
hence to quasi-isomorphisms.

## Main definitions and results

* `SimplicialObject.quasiIso_alternatingFaceMapComplex_map_iff_of_projective`,
  `SimplicialObject.homotopyEquivOfQuasiIso`: weak equivalences between degreewise projective
  simplicial objects in an abelian category coincide with simplicial homotopy equivalences.
* `SimplicialObject.quasiIso_whiskering_of_projective`,
  `SimplicialObject.quasiIso_whiskering_of_fullyFaithful_projective`,
  `SimplicialObject.quasiIso_whiskering_isProjective`: arbitrary (possibly non-additive) functors
  (including functors defined only on a full subcategory such as `(isProjective C).FullSubcategory`)
  preserve weak equivalences between degreewise projective simplicial objects.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §§4.4–4.7.
* D. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer-Verlag (1967), II.4.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994), §8.4.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

section WhiskeringProjective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For degreewise projective simplicial objects `X` and `Y` in an abelian category, a morphism
`f : X ⟶ Y` induces a quasi-isomorphism on alternating face map complexes if and only if `f` is a
simplicial homotopy equivalence. -/
theorem quasiIso_alternatingFaceMapComplex_map_iff_of_projective
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex C).map f) ↔ ∃ e : HomotopyEquiv X Y, e.hom = f := by
  have : ∀ n, Projective (((alternatingFaceMapComplex C).obj X).X n) :=
    fun n ↦ inferInstanceAs (Projective (X _⦋n⦌))
  have : ∀ n, Projective (((alternatingFaceMapComplex C).obj Y).X n) :=
    fun n ↦ inferInstanceAs (Projective (Y _⦋n⦌))
  rw [ChainComplex.quasiIso_iff_of_projective,
    homotopyEquivalences_alternatingFaceMapComplex_map_iff]

/-- Upgrade a morphism `f : X ⟶ Y` between degreewise projective simplicial objects in an abelian
category whose alternating face map complex morphism is a quasi-isomorphism to a simplicial homotopy
equivalence `HomotopyEquiv X Y` with forward morphism `f`. -/
def homotopyEquivOfQuasiIso {X Y : SimplicialObject C}
    [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)] (f : X ⟶ Y)
    [hf : QuasiIso ((alternatingFaceMapComplex C).map f)] : HomotopyEquiv X Y :=
  ((quasiIso_alternatingFaceMapComplex_map_iff_of_projective f).mp hf).choose

@[simp]
lemma homotopyEquivOfQuasiIso_hom {X Y : SimplicialObject C}
    [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)] (f : X ⟶ Y)
    [hf : QuasiIso ((alternatingFaceMapComplex C).map f)] :
    (homotopyEquivOfQuasiIso f).hom = f :=
  ((quasiIso_alternatingFaceMapComplex_map_iff_of_projective f).mp hf).choose_spec

/-- Any functor `F : C ⥤ D` (not necessarily additive) sends a weak equivalence `f : X ⟶ Y` between
degreewise projective simplicial objects in `C` to a simplicial homotopy equivalence in
`SimplicialObject D`. -/
theorem exists_homotopyEquiv_whiskering_map_of_projective
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    ∃ e : HomotopyEquiv (((whiskering C D).obj F).obj X) (((whiskering C D).obj F).obj Y),
      e.hom = ((whiskering C D).obj F).map f :=
  ⟨(homotopyEquivOfQuasiIso f).whiskerRight F, by simp⟩

/-- Any functor `F : C ⥤ D` into a preadditive category `D` (not necessarily additive) sends a weak
equivalence `f : X ⟶ Y` between degreewise projective simplicial objects in `C` to a chain homotopy
equivalence on alternating face map complexes. -/
theorem homotopyEquivalences_alternatingFaceMapComplex_whiskering_map_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    HomologicalComplex.homotopyEquivalences D (.down ℕ)
      ((alternatingFaceMapComplex D).map (((whiskering C D).obj F).map f)) := by
  obtain ⟨e, he⟩ := exists_homotopyEquiv_whiskering_map_of_projective F f
  rw [← he]
  simpa using e.toChainHomotopyEquiv.homotopyEquivalences_hom

/-- **Non-additive functors preserve weak equivalences of projective simplicial objects**
(Dold–Puppe, §§4.4–4.7): for *any* functor `F : C ⥤ D` (without any additivity assumption on `F`)
from an abelian category `C` to a preadditive category `D` with homology, if `X` and `Y` are
degreewise projective simplicial objects in `C` and `f : X ⟶ Y` induces a quasi-isomorphism on
alternating face map complexes, then `((whiskering C D).obj F).map f` also induces a
quasi-isomorphism on alternating face map complexes. -/
theorem quasiIso_whiskering_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    QuasiIso ((alternatingFaceMapComplex D).map (((whiskering C D).obj F).map f)) :=
  homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (homotopyEquivalences_alternatingFaceMapComplex_whiskering_map_of_projective F f)

/-- Normalized-chains variant of `quasiIso_whiskering_of_projective`: when `D` is also idempotent
complete with finite coproducts, `Idempotents.DoldKan.N.map (((whiskering C D).obj F).map f)` is a
quasi-isomorphism. -/
theorem quasiIso_N_whiskering_of_projective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteCoproducts D]
    [IsIdempotentComplete D] [CategoryWithHomology D] (F : C ⥤ D)
    {X Y : SimplicialObject C} [∀ n, Projective (X _⦋n⦌)] [∀ n, Projective (Y _⦋n⦌)]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map f)] :
    QuasiIso (Idempotents.DoldKan.N.map (((whiskering C D).obj F).map f)) := by
  obtain ⟨e, he⟩ := exists_homotopyEquiv_whiskering_map_of_projective F f
  rw [← he, ← e.toNHomotopyEquiv_hom]
  exact e.toNHomotopyEquiv.quasiIso_hom

/-- **Full-subcategory version of `quasiIso_whiskering_of_projective`**: if `ι : C₀ ⥤ C` is a fully
faithful functor into an abelian category `C` (for example `P.ι : P.FullSubcategory ⥤ C` for
`isProjective C` or finitely generated projective modules), `F : C₀ ⥤ D` is *any* functor defined
only on `C₀`, `X` and `Y` are simplicial objects in `C₀` whose images under `ι` are degreewise
projective in `C`, and `f : X ⟶ Y` becomes a weak equivalence after whiskering by `ι`, then
`((whiskering C₀ D).obj F).map f` induces a quasi-isomorphism on alternating face map complexes. -/
theorem quasiIso_whiskering_of_fullyFaithful_projective
    {C₀ : Type*} [Category* C₀] (ι : C₀ ⥤ C) [ι.Full] [ι.Faithful]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]
    (F : C₀ ⥤ D) {X Y : SimplicialObject C₀}
    [hX : ∀ n, Projective (ι.obj (X _⦋n⦌))] [hY : ∀ n, Projective (ι.obj (Y _⦋n⦌))]
    (f : X ⟶ Y) [QuasiIso ((alternatingFaceMapComplex C).map (((whiskering C₀ C).obj ι).map f))] :
    QuasiIso ((alternatingFaceMapComplex D).map (((whiskering C₀ D).obj F).map f)) := by
  have : ∀ n, Projective ((((whiskering C₀ C).obj ι).obj X) _⦋n⦌) := hX
  have : ∀ n, Projective ((((whiskering C₀ C).obj ι).obj Y) _⦋n⦌) := hY
  let e : HomotopyEquiv X Y :=
    (homotopyEquivOfQuasiIso (((whiskering C₀ C).obj ι).map f)).ofFullyFaithful ι
  have he : e.hom = f := ((whiskering C₀ C).obj ι).map_injective (by simp [e])
  rw [← he, ← e.whiskerRight_hom F]
  simpa using (e.whiskerRight F).toChainHomotopyEquiv.quasiIso_hom

/-- Specialization of `quasiIso_whiskering_of_fullyFaithful_projective` to functors
`F : (isProjective C).FullSubcategory ⥤ D` defined only on the full subcategory of projective
objects of `C`. -/
theorem quasiIso_whiskering_isProjective
    {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]
    (F : (isProjective C).FullSubcategory ⥤ D)
    {X Y : SimplicialObject (isProjective C).FullSubcategory} (f : X ⟶ Y)
    [QuasiIso ((alternatingFaceMapComplex C).map
      (((whiskering (isProjective C).FullSubcategory C).obj (isProjective C).ι).map f))] :
    QuasiIso ((alternatingFaceMapComplex D).map
      (((whiskering (isProjective C).FullSubcategory D).obj F).map f)) := by
  have : ∀ n, Projective ((isProjective C).ι.obj (X _⦋n⦌)) := fun n ↦ (X _⦋n⦌).property
  have : ∀ n, Projective ((isProjective C).ι.obj (Y _⦋n⦌)) := fun n ↦ (Y _⦋n⦌).property
  exact quasiIso_whiskering_of_fullyFaithful_projective (isProjective C).ι F f

end WhiskeringProjective

end CategoryTheory.SimplicialObject
