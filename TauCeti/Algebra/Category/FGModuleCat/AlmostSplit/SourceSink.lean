/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Basic
public import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Sequence
public import TauCeti.CategoryTheory.AlmostSplit.Irreducible.Criterion
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt

/-!
# Source and sink maps over an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`. Every finitely generated
indecomposable `A`-module `M` has a **sink map**, a right minimal right almost split morphism
`Y ⟶ M` in `mod A`, and a **source map**, a left minimal left almost split morphism `M ⟶ Y'`. At a
projective `M` the sink map is the inclusion of the radical, and otherwise it is the final map of
the almost-split sequence ending at `M` (`FGModuleCat.exists_isAlmostSplit`); dually for source
maps. This discharges the existence hypotheses of `FGModuleCat.exists_isRightAlmostSplit_biproduct`
and `FGModuleCat.exists_isLeftAlmostSplit_biproduct`.

Through the categorical criterion of `TauCeti.CategoryTheory.AlmostSplit.Irreducible.Criterion`,
a morphism `h : X ⟶ M` from a nonzero module is then irreducible exactly when
`(h, h') : X ⊞ X' ⟶ M` is a sink map for some `h'`, and dually for morphisms out of `M`.

## Main results

* `FGModuleCat.exists_isRightAlmostSplit_biproduct_of_finite` and
  `FGModuleCat.exists_isLeftAlmostSplit_biproduct_of_finite`: sink and source maps out of and into
  finite biproducts of indecomposable modules, with irreducible components.
* `FGModuleCat.exists_right_minimal_isRightAlmostSplit` and
  `FGModuleCat.exists_left_minimal_isLeftAlmostSplit`: the existence of sink and source maps.
* `FGModuleCat.isIrreducibleMorphism_iff_exists_isRightAlmostSplit_biprod_desc` and
  `FGModuleCat.isIrreducibleMorphism_iff_exists_isLeftAlmostSplit_biprod_lift`: the
  irreducibility criterion.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections V.1 and V.5.
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v w

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A] [Small.{w} A]

include R

/-- **Sink maps with irreducible components.** Over an Artin algebra, every finitely generated
indecomposable module `M` has a right minimal right almost split morphism out of a finite biproduct
of finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isRightAlmostSplit_biproduct_of_finite {M : FGModuleCat.{w} A}
    (hM : Indecomposable M) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (p : ⨁ F ⟶ M),
      (∀ j, Indecomposable (F j)) ∧ IsRightAlmostSplit p ∧
        (∀ u : ⨁ F ⟶ ⨁ F, u ≫ p = p → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (biproduct.ι F j ≫ p) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨n, F, p, hF, hp⟩ := exists_isRightAlmostSplit_biproduct
    ((indecomposable_obj_iff M).mpr hM) fun hP ↦ by
      -- The final map of the almost-split sequence ending at `M`.
      obtain ⟨S, hS, ⟨e⟩⟩ := exists_isAlmostSplit R M hM hP
      exact ⟨S.X₂, S.g ≫ e.hom, hS.isRightAlmostSplit_g.comp_iso e.hom⟩
  exact ⟨n, F, p, fun j ↦ (indecomposable_obj_iff (F j)).mp (hF j), hp⟩

/-- **Source maps with irreducible components.** Over an Artin algebra, every finitely generated
indecomposable module `M` has a left minimal left almost split morphism into a finite biproduct of
finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isLeftAlmostSplit_biproduct_of_finite {M : FGModuleCat.{w} A}
    (hM : Indecomposable M) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (i : M ⟶ ⨁ F),
      (∀ j, Indecomposable (F j)) ∧ IsLeftAlmostSplit i ∧
        (∀ u : ⨁ F ⟶ ⨁ F, i ≫ u = i → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (i ≫ biproduct.π F j) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨n, F, i, hF, hi⟩ := exists_isLeftAlmostSplit_biproduct
    ((indecomposable_obj_iff M).mpr hM) fun hI ↦ by
      -- The initial map of the almost-split sequence starting at `M`.
      obtain ⟨S, hS, ⟨e⟩⟩ := exists_isAlmostSplit_of_not_injective R M hM hI
      exact ⟨S.X₂, e.inv ≫ S.f, hS.isLeftAlmostSplit_f.iso_comp e.inv⟩
  exact ⟨n, F, i, fun j ↦ (indecomposable_obj_iff (F j)).mp (hF j), hi⟩

/-- **Existence of sink maps.** Over an Artin algebra, every finitely generated indecomposable
module is the target of a right minimal right almost split morphism in `FGModuleCat`. -/
theorem exists_right_minimal_isRightAlmostSplit {M : FGModuleCat.{w} A} (hM : Indecomposable M) :
    ∃ (Y : FGModuleCat.{w} A) (g : Y ⟶ M), IsRightAlmostSplit g ∧
      ∀ φ : Y ⟶ Y, φ ≫ g = g → IsIso φ := by
  obtain ⟨_, _, g, -, hg, hmin, -⟩ := exists_isRightAlmostSplit_biproduct_of_finite R hM
  exact ⟨_, g, hg, hmin⟩

/-- **Existence of source maps.** Over an Artin algebra, every finitely generated indecomposable
module is the source of a left minimal left almost split morphism in `FGModuleCat`. -/
theorem exists_left_minimal_isLeftAlmostSplit {M : FGModuleCat.{w} A} (hM : Indecomposable M) :
    ∃ (Y : FGModuleCat.{w} A) (f : M ⟶ Y), IsLeftAlmostSplit f ∧
      ∀ φ : Y ⟶ Y, f ≫ φ = f → IsIso φ := by
  obtain ⟨_, _, f, -, hf, hmin, -⟩ := exists_isLeftAlmostSplit_biproduct_of_finite R hM
  exact ⟨_, f, hf, hmin⟩

/-- **Irreducible morphisms into an indecomposable module.** Over an Artin algebra, a morphism
`h : X ⟶ M` from a nonzero finitely generated module to an indecomposable one is irreducible
exactly when `(h, h') : X ⊞ X' ⟶ M` is right minimal right almost split for some `h'`. -/
theorem isIrreducibleMorphism_iff_exists_isRightAlmostSplit_biprod_desc
    {X M : FGModuleCat.{w} A} (hM : Indecomposable M) (hX : ¬ IsZero X) (h : X ⟶ M) :
    IsIrreducibleMorphism h ↔ ∃ (X' : FGModuleCat.{w} A) (h' : X' ⟶ M),
      IsRightAlmostSplit (biprod.desc h h') ∧
        ∀ u : X ⊞ X' ⟶ X ⊞ X', u ≫ biprod.desc h h' = biprod.desc h h' → IsIso u := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨Y, g, hg, hmin⟩ := exists_right_minimal_isRightAlmostSplit R hM
  exact hg.isIrreducibleMorphism_iff_exists_biprod_desc hmin hX h

/-- **Irreducible morphisms out of an indecomposable module.** Over an Artin algebra, a morphism
`h : M ⟶ X` from an indecomposable finitely generated module to a nonzero one is irreducible
exactly when `(h, h') : M ⟶ X ⊞ X'` is left minimal left almost split for some `h'`. -/
theorem isIrreducibleMorphism_iff_exists_isLeftAlmostSplit_biprod_lift
    {M X : FGModuleCat.{w} A} (hM : Indecomposable M) (hX : ¬ IsZero X) (h : M ⟶ X) :
    IsIrreducibleMorphism h ↔ ∃ (X' : FGModuleCat.{w} A) (h' : M ⟶ X'),
      IsLeftAlmostSplit (biprod.lift h h') ∧
        ∀ u : X ⊞ X' ⟶ X ⊞ X', biprod.lift h h' ≫ u = biprod.lift h h' → IsIso u := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨Y, f, hf, hmin⟩ := exists_left_minimal_isLeftAlmostSplit R hM
  exact hf.isIrreducibleMorphism_iff_exists_biprod_lift hmin hX h

end FGModuleCat
