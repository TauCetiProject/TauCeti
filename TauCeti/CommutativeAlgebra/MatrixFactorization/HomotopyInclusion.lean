/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# Finite matrix factorizations in the curved homotopy category

The inclusion of finite-projective matrix factorizations among curved duplexes descends to
homotopy categories. It is fully faithful: an odd homotopy between finite-projective
factorizations is exactly an odd homotopy between their underlying curved duplexes. Thus
the finite-projective homotopy category has precisely the same morphisms between its
objects as the ambient curved homotopy category.

This comparison uses the full-subcategory presentation of matrix factorizations and the
quotient-by-ideal construction. It is the homotopy-level form of the finite-projective
inclusion used in Orlov, *Triangulated categories of singularities and D-branes in
Landau–Ginzburg models*, Sections 1.2 and 3.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

variable {S : Type u} [CommRing S] {w : S}

private theorem nullHomotopic_le_comap :
    nullHomotopic (S := S) (w := w) ≤
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).comap inclusion := by
  intro X Y f hf
  rw [MorphismIdeal.mem_comap_hom, CurvedDuplex.mem_nullHomotopic_iff]
  exact (mem_nullHomotopic_iff f).1 hf

/-- The finite-projective matrix-factorization homotopy category embeds in the homotopy
category of all curved duplexes of finitely generated modules. -/
noncomputable def homotopyInclusion :
    HomotopyCategory (S := S) (w := w) ⥤
      CurvedDuplex.HomotopyCategory (FGModuleCat.{u} S) w :=
  (nullHomotopic (S := S) (w := w)).map
    (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap

/-- The embedding of homotopy categories agrees on objects with the inclusion of
matrix factorizations followed by the curved-duplex quotient. -/
@[simp]
theorem homotopyInclusion_obj (X : MatrixFactorization S w) :
    homotopyInclusion.obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).quotientFunctor.obj X.obj := by
  unfold homotopyInclusion
  exact MorphismIdeal.map_obj_quotientFunctor_obj
      (nullHomotopic (S := S) (w := w))
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap X

/-- On morphisms, the homotopy embedding sends a class to the class of the same
closed even map, viewed as a map of curved duplexes. -/
theorem homotopyInclusion_map (f : X ⟶ Y) :
    homotopyInclusion.map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map f) ≫
          eqToHom (homotopyInclusion_obj Y) =
      eqToHom (homotopyInclusion_obj X) ≫
        (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).quotientFunctor.map f.hom := by
  unfold homotopyInclusion
  exact MorphismIdeal.map_map_quotientFunctor_map
      (nullHomotopic (S := S) (w := w))
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap f

/-- A homotopy class of finite-projective factorizations is zero in the curved-duplex
homotopy category only if it was already zero in the matrix-factorization homotopy category. -/
instance : homotopyInclusion (S := S) (w := w) |>.Faithful := by
  unfold homotopyInclusion
  exact (MorphismIdeal.faithful_map_iff
    (nullHomotopic (S := S) (w := w))
    (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap).2
      (by
        intro X Y f hf
        rw [MorphismIdeal.mem_comap_hom, CurvedDuplex.mem_nullHomotopic_iff] at hf
        exact (mem_nullHomotopic_iff f).2 hf)

/-- Every homotopy class between two finite-projective factorizations in the ambient curved
homotopy category is represented by a map of finite-projective factorizations. -/
instance : homotopyInclusion (S := S) (w := w) |>.Full := by
  unfold homotopyInclusion
  infer_instance

end TauCeti.MatrixFactorization
