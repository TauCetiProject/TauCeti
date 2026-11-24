/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.CategoryTheory.Linear.Conj
public import TauCeti.CategoryTheory.Linear.Endomorphism

import TauCeti.Algebra.Homology.Homotopy

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
`α : H →ₐ[R] End K`, descending through `quotient` and `Q` via `AlgHom.rangeMap` gives surjective
`R`-algebra homomorphisms from `α.range` onto the descended action ranges, and for K-projective
`K` the homotopy-to-derived equivalences restrict via `AlgEquiv.rangeMap` to `R`-algebra
equivalences on the descended action ranges
(`CochainComplex.IsKProjective.homotopyToDerivedActionRangeEquiv` and
`CochainComplex.IsKProjective.homotopyToDerivedActionRangeEquivQ`).

A quasi-isomorphism between `ℕ`-graded chain complexes of projective objects is a chain homotopy
equivalence (Mathlib's `ChainComplex.quasiIso_iff_of_projective`), with forward map the given
quasi-isomorphism (`HomotopyEquiv.ofQuasiIsoOfProjective`). So the contravariant functor
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

/-- Applying `homotopyToDerivedEndEquiv` acts by `Qh.mapEndAlgHom`. -/
theorem homotopyToDerivedEndEquiv_apply [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective]
    (f : End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :
    homotopyToDerivedEndEquiv R K f =
      Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) f :=
  End.ext (by simp)

/-- The underlying `R`-algebra homomorphism of `homotopyToDerivedEndEquiv R K` is
`Qh.mapEndAlgHom R _`. -/
@[simp]
theorem homotopyToDerivedEndEquiv_toAlgHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    (homotopyToDerivedEndEquiv R K :
        End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) →ₐ[R]
          End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) =
      Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
  AlgHom.ext (homotopyToDerivedEndEquiv_apply R K)

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

/-- Composing `homotopyToDerivedEndEquivQ` with `HomotopyCategory.quotient.mapEndAlgHom` gives
`Q.mapEndAlgHom`. -/
@[simp]
theorem homotopyToDerivedEndEquivQ_comp_quotient_mapEndAlgHom [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective] :
    (homotopyToDerivedEndEquivQ R K :
        End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) →ₐ[R] End (Q.obj K)).comp
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K) =
      Q.mapEndAlgHom R K :=
  AlgHom.ext fun _ ↦ homotopyToDerivedEndEquivQ_apply_quotient_mapEndAlgHom R K _

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
  ((homotopyToDerivedEndEquiv R K).rangeMap _).trans
    (Subalgebra.equivOfEq _ _ (by rw [homotopyToDerivedEndEquiv_toAlgHom]))

/-- Applying `homotopyToDerivedActionRangeEquiv` sends `x` to `Qh.mapEndAlgHom R _ x.val`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquiv_coe [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquiv R K α x :
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) =
      Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) x.val := by
  simp [homotopyToDerivedActionRangeEquiv, homotopyToDerivedEndEquiv_apply]

/-- Applying `homotopyToDerivedActionRangeEquiv` acts by `Qh.map` on underlying morphisms. -/
theorem homotopyToDerivedActionRangeEquiv_apply_asHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquiv R K α x :
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))).asHom =
      Qh.map x.val.asHom := by
  simp

/-- For a K-projective cochain complex `K` and a chain-level `R`-algebra action
`α : H →ₐ[R] End K`, `homotopyToDerivedEndEquivQ` restricts to an `R`-algebra equivalence from the
descended homotopy action image onto the descended derived action image on `Q.obj K`. -/
noncomputable def homotopyToDerivedActionRangeEquivQ [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) :
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range ≃ₐ[R]
      ((Q.mapEndAlgHom R K).comp α).range :=
  ((homotopyToDerivedEndEquivQ R K).rangeMap _).trans
    (Subalgebra.equivOfEq _ _ (by
      rw [← AlgHom.comp_assoc, homotopyToDerivedEndEquivQ_comp_quotient_mapEndAlgHom]))

/-- Applying `homotopyToDerivedActionRangeEquivQ` sends `x` to
`homotopyToDerivedEndEquivQ R K x.val`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquivQ_coe [(Qh (C := C)).Linear R] [(Q (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] {H : Type t'} [Semiring H] [Algebra R H]
    (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquivQ R K α x : End (Q.obj K)) =
      homotopyToDerivedEndEquivQ R K x.val := by
  simp [homotopyToDerivedActionRangeEquivQ]

/-- Applying `homotopyToDerivedActionRangeEquivQ` applies `Qh.map` and conjugates by
`quotientCompQhIso`. -/
theorem homotopyToDerivedActionRangeEquivQ_apply_asHom [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K)
    (x : (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).comp α).range) :
    (homotopyToDerivedActionRangeEquivQ R K α x : End (Q.obj K)).asHom =
      ((quotientCompQhIso C).app K).inv ≫ Qh.map x.val.asHom ≫
        ((quotientCompQhIso C).app K).hom := by
  simp

/-- Applying `homotopyToDerivedActionRangeEquivQ` to the homotopy class of `x : α.range` gives
`(Q.mapEndAlgHom R K).rangeMap α x`. -/
@[simp]
theorem homotopyToDerivedActionRangeEquivQ_apply_rangeMap
    [(Qh (C := C)).Linear R] [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective]
    {H : Type t'} [Semiring H] [Algebra R H] (α : H →ₐ[R] End K) (x : α.range) :
    homotopyToDerivedActionRangeEquivQ R K α
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K).rangeMap α x) =
      (Q.mapEndAlgHom R K).rangeMap α x := by
  apply Subtype.ext
  simp

end Endomorphism

end CochainComplex.IsKProjective

namespace ChainComplex

open HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : ChainComplex C ℕ}
  [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects, as a chain
homotopy equivalence with forward map `φ` (Mathlib's `ChainComplex.quasiIso_iff_of_projective`). -/
noncomputable def _root_.HomotopyEquiv.ofQuasiIsoOfProjective (φ : K ⟶ L) [QuasiIso φ] :
    HomotopyEquiv K L :=
  let h := (quasiIso_iff_of_projective φ).1 ‹_›
  h.choose.copy (Homotopy.ofEq h.choose_spec)

/-- The forward map of `HomotopyEquiv.ofQuasiIsoOfProjective φ` is `φ`. -/
@[simp]
theorem _root_.HomotopyEquiv.ofQuasiIsoOfProjective_hom (φ : K ⟶ L) [QuasiIso φ] :
    (HomotopyEquiv.ofQuasiIsoOfProjective φ).hom = φ := by
  rw [HomotopyEquiv.ofQuasiIsoOfProjective, HomotopyEquiv.copy_hom]

/-- The map induced on homology by the inverse of `HomotopyEquiv.ofQuasiIsoOfProjective φ` is the
inverse of the map induced by `φ`. -/
@[simp]
theorem _root_.HomotopyEquiv.homologyMap_ofQuasiIsoOfProjective_inv (φ : K ⟶ L) [QuasiIso φ]
    (n : ℕ) :
    homologyMap (HomotopyEquiv.ofQuasiIsoOfProjective φ).inv n = (asIso (homologyMap φ n)).inv := by
  simp only [HomotopyEquiv.homologyMap_inv, HomotopyEquiv.ofQuasiIsoOfProjective_hom, asIso_inv]

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
cochain homotopy equivalence `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem homotopyEquivalences_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    homotopyEquivalences _ _ ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k Y
    ((quasiIso_iff_of_projective φ).1 ‹_›)

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
quasi-isomorphism `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_linearYonedaFunctor_map_of_projective φ k Y)

end ChainComplex
