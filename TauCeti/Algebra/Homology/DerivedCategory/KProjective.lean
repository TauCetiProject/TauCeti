/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.CategoryTheory.Linear.Conj
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Chain maps and endomorphism algebras for K-projective complexes

A morphism in the derived category from a K-projective complex can be represented by a
chain map. This is the chain-level form of Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective`, and lets one form mapping cones of derived
morphisms using specified projective models.

In an `R`-linear setting, for a K-projective cochain complex `K`, the localization functor `Qh`
induces `R`-algebra equivalences from the homotopy endomorphism algebra of `K` to
`End (Qh.obj (quotient.obj K))` (`CochainComplex.IsKProjective.homotopyToDerivedEndEquiv`)
and, via `quotientCompQhIso`, to `End (Q.obj K)`
(`CochainComplex.IsKProjective.homotopyToDerivedEndEquivQ`), while `Q` induces a surjective
`R`-algebra homomorphism from chain endomorphisms `End K` onto `End (Q.obj K)`
(`CochainComplex.IsKProjective.Q_mapEndAlgHom_surjective`). For any chain-level `R`-algebra action
`α : H →ₐ[R] End K`, descending through `quotient` and `Q` gives surjective `R`-algebra
homomorphisms from `α.range` onto the descended action ranges (`TauCeti.quotientActionRangeMap`
and `TauCeti.derivedActionRangeMap`), and for K-projective `K` the homotopy-to-derived equivalences
restrict to `R`-algebra equivalences on the descended action ranges
(`CochainComplex.IsKProjective.homotopyToDerivedActionRangeEquiv` and
`CochainComplex.IsKProjective.homotopyToDerivedActionRangeEquivQ`).

A quasi-isomorphism between `ℕ`-graded chain complexes of projective objects is a chain homotopy
equivalence (Mathlib's `ChainComplex.quasiIso_iff_of_projective`). So the contravariant functor
`Hom(-, Y)` takes it to a cochain homotopy equivalence, and in particular to a quasi-isomorphism
(`ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`,
`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`). This is how a map of spaces
inducing isomorphisms on homology with projective chain coefficients is seen to induce
isomorphisms on cohomology with values in every coefficient object.
-/

public section

open CategoryTheory DerivedCategory

universe t' t w v u

namespace TauCeti

/-- Descending a chain-level endomorphism through `HomotopyCategory.quotient` and then
`DerivedCategory.Qh` agrees with descending directly through `DerivedCategory.Q`, up to conjugation
by `quotientCompQhIso`. -/
theorem conjAlgEquiv_comp_Qh_mapEndAlgHom_comp_quotient_mapEndAlgHom (R : Type t) [CommSemiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C]
    [Linear R (DerivedCategory C)] [(Qh (C := C)).Linear R] [(Q (C := C)).Linear R]
    (K : CochainComplex C ℤ) :
    (((quotientCompQhIso C).app K).conjAlgEquiv R).toAlgHom.comp
      ((Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)).comp
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K)) =
      Q.mapEndAlgHom R K := by
  ext f
  simp [Iso.conjAlgEquiv_apply, quotientCompQhIso_hom_naturality]

/-- Descending a chain-level `R`-algebra action `α : H →ₐ[R] End K` through
`HomotopyCategory.quotient` restricts to an `R`-algebra homomorphism from `α.range` onto the range
of the descended homotopy action. -/
noncomputable def quotientActionRangeMap (R : Type t) [CommSemiring R] {C : Type u}
    [Category.{v} C] [Abelian C] [Linear R C] (K : CochainComplex C ℤ) {H : Type t'} [Semiring H]
    [Algebra R H] (α : H →ₐ[R] End K) :
    α.range →ₐ[R]
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α _).symm).toAlgHom.comp
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).subalgebraMap α.range)

/-- Applying `quotientActionRangeMap` sends `x : α.range` to its homotopy class. -/
@[simp]
theorem quotientActionRangeMap_coe (R : Type t) [CommSemiring R] {C : Type u} [Category.{v} C]
    [Abelian C] [Linear R C] (K : CochainComplex C ℤ) {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K) (x : α.range) :
    (quotientActionRangeMap R K α x :
      End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K x.1 := by
  simp [quotientActionRangeMap]

/-- `quotientActionRangeMap` is surjective onto the range of the descended homotopy action. -/
theorem quotientActionRangeMap_surjective (R : Type t) [CommSemiring R] {C : Type u}
    [Category.{v} C] [Abelian C] [Linear R C] (K : CochainComplex C ℤ) {H : Type t'} [Semiring H]
    [Algebra R H] (α : H →ₐ[R] End K) :
    Function.Surjective (quotientActionRangeMap R K α) :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α _).symm).surjective.comp
    (AlgHom.subalgebraMap_surjective _ _)

/-- Descending a chain-level `R`-algebra action `α : H →ₐ[R] End K` through `DerivedCategory.Q`
restricts to an `R`-algebra homomorphism from `α.range` onto the range of the descended derived
action. -/
noncomputable def derivedActionRangeMap (R : Type t) [CommSemiring R] {C : Type u}
    [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C]
    [Linear R (DerivedCategory C)] [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) {H : Type t'}
    [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) :
    α.range →ₐ[R] ((Q.mapEndAlgHom R K).comp α).range :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α _).symm).toAlgHom.comp
    ((Q.mapEndAlgHom R K).subalgebraMap α.range)

/-- Applying `derivedActionRangeMap` sends `x : α.range` to `Q.mapEndAlgHom R K x.1`. -/
@[simp]
theorem derivedActionRangeMap_coe (R : Type t) [CommSemiring R] {C : Type u} [Category.{v} C]
    [Abelian C] [Linear R C] [HasDerivedCategory.{w} C] [Linear R (DerivedCategory C)]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K) (x : α.range) :
    (derivedActionRangeMap R K α x : End (Q.obj K)) = Q.mapEndAlgHom R K x.1 := by
  simp [derivedActionRangeMap]

/-- `derivedActionRangeMap` is surjective onto the range of the descended derived action. -/
theorem derivedActionRangeMap_surjective (R : Type t) [CommSemiring R] {C : Type u}
    [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C]
    [Linear R (DerivedCategory C)] [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) {H : Type t'}
    [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) :
    Function.Surjective (derivedActionRangeMap R K α) :=
  (Subalgebra.equivOfEq _ _ (AlgHom.range_comp α _).symm).surjective.comp
    (AlgHom.subalgebraMap_surjective _ _)

end TauCeti

namespace CochainComplex.IsKProjective

section Map

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every derived morphism from a K-projective complex is represented by a chain map. -/
theorem Q_map_surjective (K L : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro f
  obtain ⟨g, hg⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ f ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K),
    ← quotientCompQhIso_hom_naturality, hg]
  simp

end Map

section Endomorphism

variable (R : Type t) [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C] [Linear R (DerivedCategory C)]

/-- For a K-projective cochain complex `K`, the functor `Qh` induces a bijective `R`-algebra
homomorphism on endomorphisms. -/
theorem Qh_mapEndAlgHom_bijective [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Bijective
      (Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :=
  Qh.mapEndAlgHom_bijective R _
    (Qh_map_bijective K ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))

/-- For a K-projective cochain complex `K`, `Qh` induces an `R`-algebra equivalence between
homotopy endomorphisms and derived endomorphisms of `Qh.obj (quotient.obj K)`. -/
noncomputable def homotopyToDerivedEndEquiv [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[R]
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :=
  AlgEquiv.ofBijective _ (Qh_mapEndAlgHom_bijective R K)

/-- Applying `homotopyToDerivedEndEquiv` acts by `Qh.map`. -/
@[simp]
theorem homotopyToDerivedEndEquiv_apply_asHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective]
    (f : End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :
    (homotopyToDerivedEndEquiv R K f).asHom = Qh.map f.asHom := by
  simp [homotopyToDerivedEndEquiv]

/-- For a K-projective cochain complex `K`, homotopy endomorphisms of `K` are isomorphic as an
`R`-algebra to derived endomorphisms of `Q.obj K`. -/
noncomputable def homotopyToDerivedEndEquivQ [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[R] End (Q.obj K) :=
  (homotopyToDerivedEndEquiv R K).trans (((quotientCompQhIso C).app K).conjAlgEquiv R)

/-- Applying `homotopyToDerivedEndEquivQ` applies `Qh.map` and conjugates by `quotientCompQhIso`. -/
@[simp]
theorem homotopyToDerivedEndEquivQ_apply_asHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective]
    (f : End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :
    (homotopyToDerivedEndEquivQ R K f).asHom =
      ((quotientCompQhIso C).app K).inv ≫ Qh.map f.asHom ≫ ((quotientCompQhIso C).app K).hom := by
  simp [homotopyToDerivedEndEquivQ, Iso.conjAlgEquiv_apply]

/-- Applying `homotopyToDerivedEndEquivQ` to the homotopy class of a chain endomorphism `f : End K`
gives `Q.mapEndAlgHom R K f`. -/
@[simp]
theorem homotopyToDerivedEndEquivQ_apply_quotient_mapEndAlgHom [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective] (f : End K) :
    homotopyToDerivedEndEquivQ R K
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K f) =
      Q.mapEndAlgHom R K f := by
  apply End.ext
  simp [quotientCompQhIso_hom_naturality]

/-- For a K-projective cochain complex `K`, `Q` induces a surjective `R`-algebra homomorphism
from chain endomorphisms to derived endomorphisms. -/
theorem Q_mapEndAlgHom_surjective [(Q (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.mapEndAlgHom R K) := by
  intro g
  obtain ⟨f, hf⟩ := Q_map_surjective K K g.asHom
  exact ⟨End.of f, End.ext (by simpa using hf)⟩

/-- For a K-projective cochain complex `K` and a chain-level `R`-algebra action
`α : H →ₐ[R] End K`, `Qh` induces an `R`-algebra equivalence from the descended homotopy action
image onto the descended `Qh`-derived action image. -/
noncomputable def homotopyToDerivedActionRangeEquiv [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K) :
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range ≃ₐ[R]
      ((Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)).comp
        (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α)).range :=
  ((homotopyToDerivedEndEquiv R K).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ (by
      rw [← AlgHom.range_comp]
      rfl))

/-- Applying `homotopyToDerivedActionRangeEquiv` sends `x` to `Qh.mapEndAlgHom R _ x.1`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquiv_coe [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquiv R K α x :
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) =
      Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) x.1 := by
  apply End.ext
  simp [homotopyToDerivedActionRangeEquiv]

/-- Applying `homotopyToDerivedActionRangeEquiv` acts by `Qh.map` on underlying morphisms. -/
theorem homotopyToDerivedActionRangeEquiv_apply_asHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquiv R K α x :
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))).asHom =
      Qh.map x.1.asHom := by
  simp

/-- For a K-projective cochain complex `K` and a chain-level `R`-algebra action
`α : H →ₐ[R] End K`, `homotopyToDerivedEndEquivQ` restricts to an `R`-algebra equivalence from the
descended homotopy action image onto the descended derived action image on `Q.obj K`. -/
noncomputable def homotopyToDerivedActionRangeEquivQ [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) :
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range ≃ₐ[R]
      ((Q.mapEndAlgHom R K).comp α).range :=
  ((homotopyToDerivedEndEquivQ R K).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ (by
      rw [← AlgHom.range_comp]
      congr 1
      ext h
      simp))

/-- Applying `homotopyToDerivedActionRangeEquivQ` sends `x` to
`homotopyToDerivedEndEquivQ R K x.1`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquivQ_coe [(Qh (C := C)).Linear R] [(Q (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquivQ R K α x : End (Q.obj K)) =
      homotopyToDerivedEndEquivQ R K x.1 := by
  simp [homotopyToDerivedActionRangeEquivQ]

/-- Applying `homotopyToDerivedActionRangeEquivQ` applies `Qh.map` and conjugates by
`quotientCompQhIso`. -/
theorem homotopyToDerivedActionRangeEquivQ_apply_asHom [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquivQ R K α x : End (Q.obj K)).asHom =
      ((quotientCompQhIso C).app K).inv ≫ Qh.map x.1.asHom ≫ ((quotientCompQhIso C).app K).hom := by
  simp

/-- Applying `homotopyToDerivedActionRangeEquivQ` to the homotopy class of `x : α.range` gives
`TauCeti.derivedActionRangeMap R K α x`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquivQ_apply_quotientActionRangeMap
    [(Qh (C := C)).Linear R] [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) (x : α.range) :
    homotopyToDerivedActionRangeEquivQ R K α (TauCeti.quotientActionRangeMap R K α x) =
      TauCeti.derivedActionRangeMap R K α x := by
  apply Subtype.ext
  simp

end Endomorphism

end CochainComplex.IsKProjective

namespace ChainComplex

open HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : ChainComplex C ℕ}
  [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
cochain homotopy equivalence `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem homotopyEquivalences_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    homotopyEquivalences _ _ ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) := by
  obtain ⟨e, he⟩ := (quasiIso_iff_of_projective φ).1 ‹_›
  exact ⟨e.linearYonedaFunctorMap k Y, by rw [HomotopyEquiv.linearYonedaFunctorMap_hom, he]⟩

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
quasi-isomorphism `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_linearYonedaFunctor_map_of_projective φ k Y)

end ChainComplex
