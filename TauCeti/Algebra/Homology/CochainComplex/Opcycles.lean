/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Retract

/-!
# Opcycles as retracts of terms

Let `K` be a cochain complex indexed by `ℤ`, and `i + 1 = j`. If the projection
`K^i ⟶ K.opcycles i` factors as the differential `K^i ⟶ K^j` followed by some
`r : K^j ⟶ K.opcycles i`, then `K.opcycles j`, the cokernel of the differential into `K^j`, is a
retract of `K^j`. Such an `r` comes from a null-homotopy of the projection of `K` onto its
opcycles in degree `i`, seen as a chain map to the complex concentrated in degree `i`. In
particular, `K.opcycles j` is then projective when `K^j` is.

## Main definitions

* `CochainComplex.retractOpcycles`: `K.opcycles j` is a retract of `K^j`, given such an `r`.
* `CochainComplex.toSingleOpcycles`: the projection of `K` onto its opcycles in degree `i`, as a
  chain map to the complex concentrated in degree `i`.
* `CochainComplex.retractOpcyclesOfHomotopy`: `K.opcycles (i + 1)` is a retract of `K^(i + 1)`
  when `K.toSingleOpcycles i` is null-homotopic.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] (K : CochainComplex C ℤ)

/-- If the differential `K^i ⟶ K^j` followed by `r : K^j ⟶ K.opcycles i` is the projection
`K^i ⟶ K.opcycles i`, then `K.opcycles j` is a retract of `K^j`. -/
noncomputable def retractOpcycles {i j : ℤ} (hij : i + 1 = j) [K.HasHomology i] [K.HasHomology j]
    (r : K.X j ⟶ K.opcycles i) (hr : K.d i j ≫ r = K.pOpcycles i) :
    Retract (K.opcycles j) (K.X j) where
  i := K.descOpcycles (𝟙 _ - r ≫ K.fromOpcycles i j) i (by simp; lia) (by
    rw [Preadditive.comp_sub, Category.comp_id, reassoc_of% hr, K.p_fromOpcycles, sub_self])
  r := K.pOpcycles j
  retract := by
    have : K.fromOpcycles i j ≫ K.pOpcycles j = 0 := by
      rw [← cancel_epi (K.pOpcycles i), K.p_fromOpcycles_assoc, K.d_pOpcycles, comp_zero]
    rw [← cancel_epi (K.pOpcycles j), K.p_descOpcycles_assoc, Preadditive.sub_comp,
      Category.assoc, this, comp_zero, sub_zero, Category.id_comp, Category.comp_id]

variable [HasZeroObject C]

/-- The projection of `K` onto its opcycles in degree `i`, as a chain map to the complex
concentrated in degree `i`. -/
noncomputable def toSingleOpcycles (i : ℤ) [K.HasHomology i] :
    K ⟶ (HomologicalComplex.single C (.up ℤ) i).obj (K.opcycles i) :=
  HomologicalComplex.mkHomToSingle (K.pOpcycles i) fun k _ ↦ K.d_pOpcycles k i

/-- The component of `K.toSingleOpcycles i` in degree `i` is the projection onto the opcycles. -/
@[simp]
lemma toSingleOpcycles_f_self (i : ℤ) [K.HasHomology i] :
    (K.toSingleOpcycles i).f i =
      K.pOpcycles i ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) i _).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- If the projection of `K` onto its opcycles in degree `i` is null-homotopic as a chain map to
the complex concentrated in degree `i`, then `K.opcycles j` is a retract of `K^j`, where
`j = i + 1`. -/
noncomputable def retractOpcyclesOfHomotopy {i j : ℤ} (hij : i + 1 = j) [K.HasHomology i]
    [K.HasHomology j] (h : Homotopy (K.toSingleOpcycles i) 0) :
    Retract (K.opcycles j) (K.X j) :=
  K.retractOpcycles hij (h.hom j i ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) i _).hom) (by
    have := h.comm i
    rw [dNext_eq _ (ComplexShape.up_mk i j hij), prevD_eq _ (ComplexShape.up_mk (i - 1) i (by lia)),
      HomologicalComplex.single_obj_d, comp_zero, add_zero, HomologicalComplex.zero_f, add_zero,
      toSingleOpcycles_f_self] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.inv_hom_id, Category.comp_id])

end CochainComplex
