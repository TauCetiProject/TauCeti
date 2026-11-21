/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

import TauCeti.Geometry.Manifold.SmoothSingular.Circle

/-!
# Necessity of the homotopy hypothesis in smooth-chain transfer

In `ContMDiff.smoothSingularChainHomotopyEquivOfRetract`, a smooth-to-singular chain homotopy
equivalence on `N` transfers to `M` along smooth maps `j : N → M` and `r : M → N` together with
a smooth homotopy `j ∘ r ~ id_M`. This file shows that the homotopy `j ∘ r ~ id_M` cannot be
omitted.

For `N = PUnit`, `r : M → PUnit` constant, and `j = const c : PUnit → M`, for every chain map
`s` on `PUnit` the candidate `TauCeti.pointTransferCandidate` (`r_* ≫ s ≫ j_*`) induces zero on
positive-degree homology (`TauCeti.homologyMap_pointTransferCandidate_eq_zero`), so whenever `M` has
non-zero positive-degree smooth or continuous singular homology, no `s` makes it a left or right
chain homotopy inverse (`TauCeti.isEmpty_homotopy_pointTransferCandidate_hom_inv`,
`TauCeti.isEmpty_homotopy_pointTransferCandidate_inv_hom`). Instantiating on `M = Circle` with
`TauCeti.homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero` rules out both left and right
homotopy inverses (`Circle.isEmpty_homotopy_circle_pointTransfer_hom_inv`,
`Circle.isEmpty_homotopy_circle_pointTransfer_inv_hom`).

## Main definitions and results

* `TauCeti.pointTransferCandidate`: the candidate `r_* ≫ s ≫ j_*` factoring through `PUnit`.
* `TauCeti.homologyMap_pointTransferCandidate_eq_zero`,
  `TauCeti.isEmpty_homotopy_pointTransferCandidate_hom_inv`,
  `TauCeti.isEmpty_homotopy_pointTransferCandidate_inv_hom`: general obstruction for manifolds with
  nontrivial positive-degree homology.
* `Circle.isEmpty_homotopy_circle_pointTransfer_hom_inv`,
  `Circle.isEmpty_homotopy_circle_pointTransfer_inv_hom`: necessity of `j ∘ r ~ id_M` on `Circle`.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- The candidate chain map `r_* ≫ s ≫ j_*` from continuous singular chains of `M` to smooth
singular chains of `M` associated to the constant map `r : M → PUnit`, a point inclusion
`j = const c`, and an arbitrary chain map `s` on `PUnit`. -/
def pointTransferCandidate (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R)) :
    ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) ⟶
      ((smoothSingularSubcomplex I M : SSet).chainComplex R) :=
  SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const M PUnit.unit))) R ≫
    s ≫ SSet.chainComplexMap (smoothSingularSubcomplexMap (fun _ : PUnit.{u + 1} ↦ c)
      contMDiff_const) R

/-- Because `PUnit` has vanishing positive-degree singular homology, `pointTransferCandidate`
induces the zero map on homology in every positive degree `n ≠ 0`, for every choice of `s`. -/
theorem homologyMap_pointTransferCandidate_eq_zero [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0) :
    HomologicalComplex.homologyMap (pointTransferCandidate (I := I) c R s) n = 0 := by
  have hpt : IsZero
      (((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R).homology n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R
      (TopCat.of PUnit.{u + 1}) hn
  have hconst : HomologicalComplex.homologyMap
      (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const M PUnit.unit))) R) n = 0 :=
    hpt.eq_of_tgt _ 0
  rw [pointTransferCandidate, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, hconst, zero_comp]

/-- Whenever `M` has non-zero smooth singular homology in positive degree `n`, no chain map `s` on
`PUnit` can make `pointTransferCandidate c R s` a left homotopy inverse of the smooth-chain
inclusion on `M`. -/
theorem isEmpty_homotopy_pointTransferCandidate_hom_inv [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0)
    (hH : ¬ IsZero (((smoothSingularSubcomplex I M : SSet).chainComplex R).homology n)) :
    IsEmpty (Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        pointTransferCandidate (I := I) c R s) (𝟙 _)) := by
  refine ⟨fun h ↦ hH ?_⟩
  have hid := h.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp, homologyMap_pointTransferCandidate_eq_zero c R s hn,
    comp_zero, HomologicalComplex.homologyMap_id] at hid
  exact (IsZero.iff_id_eq_zero _).mpr hid.symm

/-- Whenever `M` has non-zero continuous singular homology in positive degree `n`, no chain map `s`
on `PUnit` can make `pointTransferCandidate c R s` a right homotopy inverse of the smooth-chain
inclusion on `M`. -/
theorem isEmpty_homotopy_pointTransferCandidate_inv_hom [CategoryWithHomology C] (c : M) (R : C)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).chainComplex R) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{u + 1}) PUnit.{u + 1} : SSet).chainComplex R))
    {n : ℕ} (hn : n ≠ 0)
    (hH : ¬ IsZero (((TopCat.toSSet.obj (TopCat.of M)).chainComplex R).homology n)) :
    IsEmpty (Homotopy
      (pointTransferCandidate (I := I) c R s ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) (𝟙 _)) := by
  refine ⟨fun h ↦ hH ?_⟩
  have hid := h.homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp, homologyMap_pointTransferCandidate_eq_zero c R s hn,
    zero_comp, HomologicalComplex.homologyMap_id] at hid
  exact (IsZero.iff_id_eq_zero _).mpr hid.symm

end TauCeti

namespace Circle

open TauCeti

/-- **Necessity of `j ∘ r ~ id_M` (left inverse).** On `Circle`, for any point `c` and any chain
map `s` on `PUnit`, the point-retract candidate `r_* ≫ s ≫ j_*` is not a left chain homotopy
inverse of the smooth-chain inclusion. -/
theorem isEmpty_homotopy_circle_pointTransfer_hom_inv (c : Circle)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{1})).chainComplex (ModuleCat.of ℤ ℤ)) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{1}) PUnit.{1} : SSet).chainComplex
        (ModuleCat.of ℤ ℤ))) :
    IsEmpty (Homotopy
      (SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ) ≫
        pointTransferCandidate (I := 𝓡 1) c (ModuleCat.of ℤ ℤ) s) (𝟙 _)) :=
  isEmpty_homotopy_pointTransferCandidate_hom_inv c (ModuleCat.of ℤ ℤ) s one_ne_zero fun hZ ↦
    homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero (hZ.eq_of_src _ _)

/-- **Necessity of `j ∘ r ~ id_M` (right inverse).** On `Circle`, for any point `c` and any chain
map `s` on `PUnit`, the point-retract candidate `r_* ≫ s ≫ j_*` is not a right chain homotopy
inverse of the smooth-chain inclusion. -/
theorem isEmpty_homotopy_circle_pointTransfer_inv_hom (c : Circle)
    (s : ((TopCat.toSSet.obj (TopCat.of PUnit.{1})).chainComplex (ModuleCat.of ℤ ℤ)) ⟶
      ((smoothSingularSubcomplex 𝓘(ℝ, PUnit.{1}) PUnit.{1} : SSet).chainComplex
        (ModuleCat.of ℤ ℤ))) :
    IsEmpty (Homotopy
      (pointTransferCandidate (I := 𝓡 1) c (ModuleCat.of ℤ ℤ) s ≫
        SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ))
      (𝟙 _)) :=
  isEmpty_homotopy_pointTransferCandidate_inv_hom c (ModuleCat.of ℤ ℤ) s one_ne_zero fun hZ ↦
    homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero (hZ.eq_of_tgt _ _)

end Circle
