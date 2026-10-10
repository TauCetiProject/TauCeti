/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Topology.Maps.OpenQuotient
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange

/-!
# Total spaces of quotients by varying operator ranges

For a family of linear operators `A x : E →L[R] F`, take the class of each ambient
vector in `F ⧸ (A x).range`. With the quotient topology on the total space, this
map is open whenever `x ↦ A x u` is continuous for every fixed `u`. No injectivity,
complement, or constant-rank assumption is needed for openness.

On a domain with a fixed complementary parametrization `B`, the fibre equivalences
`ContinuousLinearMap.quotientRangeEquiv` assemble into a homeomorphism with the
product of the base and the complement. These are the topological local coordinates
for quotient bundles such as intrinsic normal bundles. The topology is supplied as
an explicit quotient-map hypothesis, so this construction preserves an existing
total-space topology rather than introducing a competing instance.

The openness argument uses saturation by translations, as in Mathlib's
`isOpenMap_quotient_mk'_add`. The coordinate construction uses
`ContinuousLinearMap.quotientRangeEquiv` and its representative formulas.
Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

open Set Function Topology Bundle

namespace TauCeti

variable {R X E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]

/-- Taking ambient representatives to their classes in the quotients by a family of ranges. -/
def rangeQuotientMap (A : X → E →L[R] F) :
    X × F → TotalSpace G (fun x => F ⧸ (A x).range) :=
  fun p => ⟨p.1, Submodule.Quotient.mk p.2⟩

@[simp]
theorem rangeQuotientMap_apply (A : X → E →L[R] F) (x : X) (v : F) :
    rangeQuotientMap (G := G) A (x, v) = ⟨x, Submodule.Quotient.mk v⟩ := (rfl)

/-- Every range-quotient class has an ambient representative with the same base point. -/
theorem rangeQuotientMap_surjective (A : X → E →L[R] F) :
    Surjective (rangeQuotientMap (G := G) A) := by
  rintro ⟨x, v⟩
  obtain ⟨w, rfl⟩ := (A x).range.mkQ_surjective v
  exact ⟨(x, w), rfl⟩

/-- Saturation by range classes is the union of translations by range representatives. -/
theorem preimage_image_rangeQuotientMap (A : X → E →L[R] F) (U : Set (X × F)) :
    rangeQuotientMap (G := G) A ⁻¹' (rangeQuotientMap A '' U) =
      ⋃ u : E, (fun p : X × F => (p.1, p.2 - A p.1 u)) ⁻¹' U := by
  ext p
  constructor
  · rintro ⟨⟨x, v⟩, hv, he⟩
    have hx : x = p.1 := congrArg TotalSpace.proj he
    subst x
    have he' : Submodule.Quotient.mk v =
        (Submodule.Quotient.mk p.2 : F ⧸ (A p.1).range) :=
      TotalSpace.mk_injective p.1 he
    obtain ⟨u, hu⟩ := (Submodule.Quotient.eq _).mp he'.symm
    simp only [ContinuousLinearMap.coe_coe] at hu
    have hsub : p.2 - A p.1 u = v := by simp [hu]
    exact mem_iUnion.mpr ⟨u, by simpa only [mem_preimage, hsub] using hv⟩
  · intro hp
    obtain ⟨u, hu⟩ := mem_iUnion.mp hp
    refine ⟨(p.1, p.2 - A p.1 u), hu, ?_⟩
    apply congrArg (TotalSpace.mk p.1)
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨-u, by simp⟩

end TauCeti

namespace Topology.IsQuotientMap

open TauCeti

variable {R X E F G : Type*} [Ring R] [TopologicalSpace X]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [IsTopologicalAddGroup F]
  {A : X → E →L[R] F}
  [TopologicalSpace (TotalSpace G (fun x => F ⧸ (A x).range))]

/-- The quotient by continuously varying ranges is an open quotient, including when
the operators are not injective and their ranges have varying dimension. -/
theorem isOpenQuotientMap_rangeQuotientMap
    (hq : IsQuotientMap (rangeQuotientMap (G := G) A))
    (hA : ∀ u : E, Continuous (fun x => A x u)) :
    IsOpenQuotientMap (rangeQuotientMap (G := G) A) := by
  refine .of_isOpenMap_isQuotientMap (fun U hU => ?_) hq
  rw [← hq.isCoinducing.isOpen_preimage, preimage_image_rangeQuotientMap]
  exact isOpen_iUnion fun u => hU.preimage
    (continuous_fst.prodMk (continuous_snd.sub ((hA u).comp continuous_fst)))

end Topology.IsQuotientMap

namespace TauCeti

variable {R X E F G : Type*} [Ring R] [TopologicalSpace X]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]
  (A : X → E →L[R] F) (B : G →L[R] F)
  [TopologicalSpace (TotalSpace G (fun x => F ⧸ (A x).range))]

/-- A common complement identifies the total range-quotient space with a product.
Continuity of the complementary coordinate is tested on ambient representatives. -/
noncomputable def rangeQuotientHomeomorph
    (h : ∀ x, ((A x).coprod B).IsInvertible)
    (hq : IsQuotientMap (rangeQuotientMap (G := G) A))
    (hc : Continuous (fun p : X × F => (A p.1).quotientRangeCoordinate B p.2)) :
    TotalSpace G (fun x => F ⧸ (A x).range) ≃ₜ X × G where
  toFun p := (p.1, (A p.1).quotientRangeEquiv B (h p.1) p.2)
  invFun p := ⟨p.1, Submodule.Quotient.mk (B p.2)⟩
  left_inv p := by
    have hi := ((A p.1).quotientRangeEquiv B (h p.1)).symm_apply_apply p.2
    rw [ContinuousLinearMap.quotientRangeEquiv_symm_apply] at hi
    exact congrArg (TotalSpace.mk p.1) hi
  right_inv p := by simp [ContinuousLinearMap.quotientRangeCoordinate_apply_right (h p.1)]
  continuous_toFun := hq.continuous_iff.mpr (by
    dsimp only [Function.comp_def, rangeQuotientMap]
    exact (continuous_fst.prodMk hc).congr fun p =>
      congrArg (Prod.mk p.1)
        (ContinuousLinearMap.quotientRangeEquiv_apply_mk (h p.1) p.2).symm)
  continuous_invFun := hq.continuous.comp (continuous_fst.prodMk
    (B.continuous.comp continuous_snd))

/-- Complementary coordinates of a quotient class, with the base point retained. -/
@[simp]
theorem rangeQuotientHomeomorph_apply
    (h : ∀ x, ((A x).coprod B).IsInvertible)
    (hq : IsQuotientMap (rangeQuotientMap (G := G) A))
    (hc : Continuous (fun p : X × F => (A p.1).quotientRangeCoordinate B p.2))
    (p : TotalSpace G (fun x => F ⧸ (A x).range)) :
    rangeQuotientHomeomorph A B h hq hc p =
      (p.1, (A p.1).quotientRangeEquiv B (h p.1) p.2) := (rfl)

/-- Inverse total-space coordinates take the class of the complementary representative. -/
@[simp]
theorem rangeQuotientHomeomorph_symm_apply
    (h : ∀ x, ((A x).coprod B).IsInvertible)
    (hq : IsQuotientMap (rangeQuotientMap (G := G) A))
    (hc : Continuous (fun p : X × F => (A p.1).quotientRangeCoordinate B p.2))
    (p : X × G) :
    (rangeQuotientHomeomorph A B h hq hc).symm p =
      ⟨p.1, Submodule.Quotient.mk (B p.2)⟩ := (rfl)

end TauCeti
