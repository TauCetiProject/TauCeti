/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Dimensions of boundaries of complexes of vector spaces

Let `C` be a homological complex of vector spaces over a field `F`. If `C.X j` is
finite-dimensional, `C` is exact in degree `j` exactly when the dimensions of the images of the
incoming and outgoing differentials add up to the dimension of `C.X j`
(`HomologicalComplex.exactAt_iff_finrank_add_finrank`).

Let `φ : F →+* K` be a homomorphism of fields and let `D` be a complex of vector spaces over `K`
of the same shape. If `C` and `D` have bases in which the matrices of the differentials of `D` are
the images under `φ` of those of `C`, then the images of the differentials have the same
dimensions (`HomologicalComplex.finrank_range_d_eq_of_toMatrix_eq`), since rank is invariant
under `φ` (`Matrix.rank_map`). Consequently `D` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_iff_of_toMatrix_eq`).
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] {ι : Type*} {s : ComplexShape ι}

/-- A complex of vector spaces with finite-dimensional term in degree `j` is exact in degree `j`
exactly when the dimensions of the images of the incoming and outgoing differentials add up to the
dimension of the term. -/
theorem exactAt_iff_finrank_add_finrank (C : HomologicalComplex (ModuleCat F) s) {i j k : ι}
    (hi : s.prev j = i) (hk : s.next j = k) [Module.Finite F (C.X j)] :
    C.ExactAt j ↔ finrank F (LinearMap.range (C.d i j).hom) +
      finrank F (LinearMap.range (C.d j k).hom) = finrank F (C.X j) := by
  have hex : C.ExactAt j ↔ LinearMap.ker (C.d j k).hom ≤ LinearMap.range (C.d i j).hom :=
    (C.exactAt_iff' _ _ _ hi hk).trans (ShortComplex.moduleCat_exact_iff_ker_sub_range _)
  have hle : LinearMap.range (C.d i j).hom ≤ LinearMap.ker (C.d j k).hom := by
    rintro _ ⟨x, rfl⟩
    exact d_comp_d_apply C _ _ _ x
  have hrk := LinearMap.finrank_range_add_finrank_ker (C.d j k).hom
  rw [hex]
  refine ⟨fun h ↦ ?_, fun h ↦ (Submodule.eq_of_le_of_finrank_le hle (by omega)).ge⟩
  have := Submodule.finrank_mono h
  have := Submodule.finrank_mono hle
  omega

variable {K : Type*} [Field K] (φ : F →+* K) {C : HomologicalComplex (ModuleCat F) s}
  {D : HomologicalComplex (ModuleCat K) s} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)] {c : ∀ i, Basis (κ i) F (C.X i)} {e : ∀ i, Basis (κ i) K (D.X i)}

/-- If the matrix of a differential of `D` is the image under a homomorphism of fields `φ` of the
matrix of the corresponding differential of `C`, then the images of the two differentials have the
same dimension. -/
theorem finrank_range_d_eq_of_toMatrix_eq {i j : ι}
    (hd : LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ) :
    finrank K (LinearMap.range (D.d i j).hom) = finrank F (LinearMap.range (C.d i j).hom) := by
  have hC := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (c i) (c j) (C.d i j).hom) (c j) (c i)
  have hD := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (e i) (e j) (D.d i j).hom) (e j) (e i)
  rw [Matrix.toLin_toMatrix] at hC hD
  rw [← hC, ← hD, hd, Matrix.rank_map]

/-- If, in bases indexed by the same types, the matrices of the differentials of `D` are the images
under a homomorphism of fields `φ` of the matrices of the differentials of `C`, then `D` is acyclic
exactly when `C` is. -/
theorem acyclic_iff_of_toMatrix_eq
    (hd : ∀ i j, s.Rel i j → LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ) :
    D.Acyclic ↔ C.Acyclic := by
  have hrk (i j : ι) :
      finrank K (LinearMap.range (D.d i j).hom) = finrank F (LinearMap.range (C.d i j).hom) := by
    by_cases hij : s.Rel i j
    · exact finrank_range_d_eq_of_toMatrix_eq φ (hd i j hij)
    · rw [D.shape i j hij, C.shape i j hij, ModuleCat.hom_zero, ModuleCat.hom_zero,
        LinearMap.range_zero, LinearMap.range_zero, finrank_bot, finrank_bot]
  refine forall_congr' fun j ↦ ?_
  have : Module.Finite F (C.X j) := .of_basis (c j)
  have : Module.Finite K (D.X j) := .of_basis (e j)
  rw [exactAt_iff_finrank_add_finrank D rfl rfl, exactAt_iff_finrank_add_finrank C rfl rfl,
    hrk, hrk, finrank_eq_card_basis (c j), finrank_eq_card_basis (e j)]

end HomologicalComplex
