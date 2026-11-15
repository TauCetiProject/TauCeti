/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The homology of a chain map from a single complex

A chain map `mkHomFromSingle φ hφ` from an object `A` placed in degree `j` to a complex `K` is
given by `φ : A ⟶ Kⱼ` with `d ∘ φ = 0`. If `g : A ⟶ Zⱼ(K)` is the factorization of `φ` through
the cycles, then the induced map on cycles in degree `j` is `g`
(`HomologicalComplex.singleObjCyclesSelfIso_inv_comp_cyclesMap_mkHomFromSingle`), and the induced
map on homology is `g` followed by `Zⱼ(K) ⟶ Hⱼ(K)`
(`HomologicalComplex.singleObjHomologySelfIso_inv_comp_homologyMap_mkHomFromSingle`), up to the
identifications of the cycles and homology of `A` placed in degree `j` with `A`.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] {c : ComplexShape ι} {K : HomologicalComplex C c} {j : ι} {A : C}
  (φ : A ⟶ K.X j) (hφ : ∀ k, c.Rel j k → φ ≫ K.d j k = 0)

/-- The map induced on cycles in degree `j` by the chain map from `A` placed in degree `j` given
by `φ : A ⟶ Kⱼ` is the factorization `g : A ⟶ Zⱼ(K)` of `φ` through the cycles. -/
@[reassoc]
theorem singleObjCyclesSelfIso_inv_comp_cyclesMap_mkHomFromSingle [K.HasHomology j]
    (g : A ⟶ K.cycles j) (hg : g ≫ K.iCycles j = φ) :
    (singleObjCyclesSelfIso c j A).inv ≫ cyclesMap (mkHomFromSingle φ hφ) j = g := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, cyclesMap_i, mkHomFromSingle_f,
    singleObjCyclesSelfIso_inv_iCycles_assoc, Iso.inv_hom_id_assoc, hg]

/-- The map induced on homology in degree `j` by the chain map from `A` placed in degree `j`
given by `φ : A ⟶ Kⱼ` is the factorization `g : A ⟶ Zⱼ(K)` of `φ` through the cycles, followed by
`Zⱼ(K) ⟶ Hⱼ(K)`. -/
@[reassoc]
theorem singleObjHomologySelfIso_inv_comp_homologyMap_mkHomFromSingle [K.HasHomology j]
    (g : A ⟶ K.cycles j) (hg : g ≫ K.iCycles j = φ) :
    (singleObjHomologySelfIso c j A).inv ≫ homologyMap (mkHomFromSingle φ hφ) j =
      g ≫ K.homologyπ j := by
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality,
    singleObjCyclesSelfIso_inv_comp_cyclesMap_mkHomFromSingle_assoc φ hφ g hg]

end HomologicalComplex
