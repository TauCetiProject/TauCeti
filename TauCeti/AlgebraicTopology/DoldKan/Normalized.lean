/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import TauCeti.AlgebraicTopology.DoldKan.Retract

/-!
# Chain maps out of the normalized Moore complex

For a simplicial object `X` in an abelian category, the normalized Moore complex `N[X]` is a
retract of the alternating face map complex `K[X]`, cut out by the idempotent `PInfty`, whose
complementary idempotent `QInfty` has image spanned by the degeneracies. Hence chain maps
`N[X] ⟶ L` are the chain maps `K[X] ⟶ L` that vanish on degeneracies: precompose with the
projection `PInftyToNormalizedMooreComplex X`, and restrict along the inclusion
`inclusionOfMooreComplexMap X`. This is how chain maps out of normalized chains are computed in
practice, for instance through the free simplicial objects on standard simplices, whose
alternating face map complexes have the simplices as a basis.

## Main definitions and results

* `AlgebraicTopology.DoldKan.normalizedMooreComplexHomEquiv`: chain maps `N[X] ⟶ L` are the chain
  maps `K[X] ⟶ L` vanishing on degeneracies.
* `CategoryTheory.Abelian.DoldKan.N_eq_normalizedMooreComplex`: `Abelian.DoldKan.N` equals
  `AlgebraicTopology.normalizedMooreComplex A`.
* `CategoryTheory.SimplicialObject.quasiIso_normalizedMooreComplex_map_iff_N`,
  `CategoryTheory.SimplicialObject.quasiIso_normalizedMooreComplex_map_iff`: quasi-isomorphism
  comparisons between `normalizedMooreComplex`, `Idempotents.DoldKan.N`, and
  `alternatingFaceMapComplex`.
-/

public section

open CategoryTheory

namespace AlgebraicTopology.DoldKan

variable {A : Type*} [Category* A] [Abelian A]

/-- Chain maps out of the normalized Moore complex of a simplicial object `X` are the chain maps
out of its alternating face map complex that vanish on degeneracies. -/
noncomputable def normalizedMooreComplexHomEquiv (X : SimplicialObject A)
    (L : ChainComplex A ℕ) :
    ((normalizedMooreComplex A).obj X ⟶ L) ≃
      {f : (alternatingFaceMapComplex A).obj X ⟶ L //
        ∀ n, DegeneraciesVanish (X := X) (f.f n)} where
  toFun φ := ⟨PInftyToNormalizedMooreComplex X ≫ φ, fun n ↦ by
    have := (degeneraciesVanishPInfty_f X n).comp ((PInftyToNormalizedMooreComplex X ≫ φ).f n)
    rwa [← HomologicalComplex.comp_f,
      (Category.assoc _ _ _).symm.trans (PInfty_comp_PInftyToNormalizedMooreComplex X =≫ φ)]
      at this⟩
  invFun f := inclusionOfMooreComplexMap X ≫ f.val
  -- Mathlib states these identities with `N[X]`, which is not reducibly the source of `φ`, so
  -- they are composed as terms rather than rewritten.
  left_inv φ :=
    (Category.assoc _ _ _).symm.trans
      (((splitMonoInclusionOfMooreComplexMap X).id =≫ φ).trans (Category.id_comp φ))
  right_inv f := Subtype.ext <| (Category.assoc _ _ _).symm.trans <|
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X =≫ f.val).trans <| by
      ext n
      have h := PInfty_f_add_QInfty_f (X := X) n =≫ f.val.f n
      rw [Preadditive.add_comp, (degeneraciesVanish_iff_QInfty_f_comp _).1 (f.property n), add_zero,
        Category.id_comp] at h
      exact h

/-- A chain map out of the normalized Moore complex corresponds to its composite with the
projection `PInftyToNormalizedMooreComplex X`. -/
@[simp]
lemma normalizedMooreComplexHomEquiv_apply_coe (X : SimplicialObject A) (L : ChainComplex A ℕ)
    (φ : (normalizedMooreComplex A).obj X ⟶ L) :
    (normalizedMooreComplexHomEquiv X L φ).val = PInftyToNormalizedMooreComplex X ≫ φ :=
  (rfl)

/-- A chain map vanishing on degeneracies corresponds to its restriction to the normalized Moore
complex. -/
@[simp]
lemma normalizedMooreComplexHomEquiv_symm_apply (X : SimplicialObject A) (L : ChainComplex A ℕ)
    (f : {f : (alternatingFaceMapComplex A).obj X ⟶ L //
      ∀ n, DegeneraciesVanish (X := X) (f.f n)}) :
    (normalizedMooreComplexHomEquiv X L).symm f = inclusionOfMooreComplexMap X ≫ f.val :=
  (rfl)

/-- `AlgebraicTopology.DoldKan.normalizedMooreComplexHomEquiv` is natural in the simplicial
object. -/
lemma normalizedMooreComplexHomEquiv_naturality {X Y : SimplicialObject A} (g : X ⟶ Y)
    {L : ChainComplex A ℕ} (φ : (normalizedMooreComplex A).obj Y ⟶ L) :
    (normalizedMooreComplexHomEquiv X L ((normalizedMooreComplex A).map g ≫ φ)).val =
      (alternatingFaceMapComplex A).map g ≫ (normalizedMooreComplexHomEquiv Y L φ).val :=
  ((Category.assoc _ _ _).symm.trans (PInftyToNormalizedMooreComplex_naturality g =≫ φ).symm).trans
    (Category.assoc _ _ _)

end AlgebraicTopology.DoldKan

namespace CategoryTheory.Abelian.DoldKan

/-- The abelian Dold–Kan functor `Abelian.DoldKan.N` is
`AlgebraicTopology.normalizedMooreComplex A`. -/
lemma N_eq_normalizedMooreComplex {A : Type*} [Category* A] [Abelian A] :
    (N : SimplicialObject A ⥤ ChainComplex A ℕ) = AlgebraicTopology.normalizedMooreComplex A :=
  rfl

end CategoryTheory.Abelian.DoldKan

namespace CategoryTheory.SimplicialObject

open AlgebraicTopology

variable {A : Type*} [Category* A] [Abelian A]

/-- In an abelian category, a morphism `f : X ⟶ Y` of simplicial objects induces a quasi-isomorphism
on normalized Moore complexes if and only if it induces a quasi-isomorphism on pseudoabelian
normalized chains `Idempotents.DoldKan.N`. -/
theorem quasiIso_normalizedMooreComplex_map_iff_N {X Y : SimplicialObject A} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex A).map f) ↔ QuasiIso (Idempotents.DoldKan.N.map f) := by
  rw [← Abelian.DoldKan.N_eq_normalizedMooreComplex,
    ← NatIso.naturality_2 Abelian.DoldKan.comparisonN f,
    quasiIso_iff_comp_left (Abelian.DoldKan.comparisonN.hom.app X) _,
    quasiIso_iff_comp_right (Idempotents.DoldKan.N.map f)
      (Abelian.DoldKan.comparisonN.inv.app Y)]

/-- In an abelian category, a morphism `f : X ⟶ Y` of simplicial objects induces a quasi-isomorphism
on normalized Moore complexes if and only if it induces a quasi-isomorphism on alternating face map
complexes. -/
theorem quasiIso_normalizedMooreComplex_map_iff {X Y : SimplicialObject A} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex A).map f) ↔
      QuasiIso ((alternatingFaceMapComplex A).map f) :=
  (quasiIso_normalizedMooreComplex_map_iff_N f).trans (quasiIso_N_map_iff f)

end CategoryTheory.SimplicialObject
