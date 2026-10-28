/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Topology.Category.TopCat.GlueData.Double

/-!
# Regression examples: the plane with a doubled origin

These examples glue two copies of `ℂ` along `ℂ \ {0}` by the identity, as the double
`TauCeti.doubleGlueData ℂ U` with `U = {0}ᶜ`, and check from a downstream module that the
gluing API detects its failure to be Hausdorff:

* two points of the glued space are equal exactly when they come from the same complex number,
  which is nonzero if they come from different copies, so the two origins are distinct;
* the relation between the two copies, the diagonal of `ℂ \ {0}`, is not closed in `ℂ × ℂ`: the
  pair of origins lies in its closure but not in the relation;
* the two origins have no disjoint neighbourhoods;
* the Hausdorff criterion `TopCat.GlueData.t2Space_iff_isClosed_chartRel` rejects the glued
  space, which is therefore not Hausdorff, although each of its two charts is an open copy
  of `ℂ`.
-/

open Topology TauCeti

-- The gluing relation of the plane with a doubled origin.
example {i j : (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).J} {z w : ℂ} :
    (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι i z =
        (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι j w ↔
      z = w ∧ (i = j ∨ z ≠ 0) :=
  doubleGlueData_ι_eq_iff

-- The two origins are distinct points.
example :
    (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι ⟨false⟩ (0 : ℂ) ≠
      (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι ⟨true⟩ (0 : ℂ) := fun h ↦
  Bool.false_ne_true <| congrArg ULift.down <| (doubleGlueData_ι_eq_iff.1 h).2.resolve_right
    (by simp)

-- The relation between the two copies of `ℂ` is not closed at the pair of origins.
example :
    ((0, 0) : ℂ × ℂ) ∈
      closure ((doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartRel ⟨false⟩ ⟨true⟩) \
        (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartRel ⟨false⟩ ⟨true⟩ :=
  ⟨mk_mem_closure_doubleGlueData_chartRel (by simp) _ _, fun h ↦ Bool.false_ne_true <|
    congrArg ULift.down <| (mem_doubleGlueData_chartRel_iff.1 h).2.resolve_right (by simp)⟩

-- The two origins have no disjoint neighbourhoods.
example :
    ¬ Disjoint
      (𝓝 ((doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι ⟨false⟩ (0 : ℂ)))
      (𝓝 ((doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι ⟨true⟩ (0 : ℂ))) :=
  not_disjoint_nhds_doubleGlueData_ι (by simp) _ _

-- The Hausdorff criterion for glued spaces rejects the plane with a doubled origin.
example :
    ¬ ∀ i j, IsClosed ((doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartRel i j) :=
  fun h ↦ (mem_doubleGlueData_chartRel_iff.1 <| (h ⟨false⟩ ⟨true⟩).closure_subset <|
    mk_mem_closure_doubleGlueData_chartRel (x := (0 : ℂ)) (by simp) ⟨false⟩ ⟨true⟩).2.elim
      (fun h ↦ Bool.false_ne_true (congrArg ULift.down h)) (by simp)

-- Hence the plane with a doubled origin is not Hausdorff.
example : ¬ T2Space (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued := by
  simpa [t2Space_doubleGlueData_iff] using fun _ ↦ not_isOpen_singleton (0 : ℂ)
