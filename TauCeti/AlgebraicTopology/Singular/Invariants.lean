/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.Transfer.Relative
public import TauCeti.Topology.Category.TopPair.Action

/-!
# The transfer identifies the homology of the base of a finite quotient covering with invariants

Let a finite group `G` act on a space `E` so that `p : E ⟶ B` is the quotient covering map of the
action, in the sense of Mathlib's `IsQuotientCoveringMap`. The transfer
`t : C(B; R) ⟶ C(E; R)` of the finite covering `p` sends a singular simplex to the sum of its
lifts. Each `g : G` permutes those lifts, so `t ≫ g_* = t`: the transfer is a cone
`hG.transferCone R` over the action of `G` on `C(E; R)`.

This file shows that, when multiplication by `|G|` is invertible on the coefficients `R`, the
transfer exhibits `Hₙ(B; R)` as the invariants `Hₙ(E; R)^G`:

* `IsQuotientCoveringMap.isLimitMapConeTransferCone`: every additive functor out of chain
  complexes, and in particular homology, sends `hG.transferCone R` to a limit cone.
* `IsQuotientCoveringMap.isLimitHomologyMapConeTransferCone`: `Hₙ(B; R)` is the limit
  `Hₙ(E; R)^G` of the action of `G` on `Hₙ(E; R)`, with leg the transfer.

The same holds for relative homology. For a subset `A ⊆ B`, the preimage `p⁻¹ A` is invariant under
`G`, which therefore acts on the relative chains `C(E, p⁻¹ A; R)`, and the relative transfer
`C(B, A; R) ⟶ C(E, p⁻¹ A; R)` (`IsCoveringMap.singularPairTransfer`) is a cone over this action:

* `IsQuotientCoveringMap.isLimitMapConePairTransferCone`: every additive functor out of chain
  complexes sends `hG.pairTransferCone A R` to a limit cone.
* `IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`: `Hₙ(B, A; R)` is the limit
  `Hₙ(E, p⁻¹ A; R)^G` of the action of `G` on `Hₙ(E, p⁻¹ A; R)`, with leg the relative transfer.

The argument is the one for coinvariants
(`IsQuotientCoveringMap.isColimitMapCoconeSingularHomology`) read backwards: `t ≫ p_* = |G| • 𝟙`
and `p_* ≫ t = ∑_{g ∈ G} g_*`, so `|G|⁻¹ • p_*` retracts the transfer onto the invariants
(`CategoryTheory.Limits.SingleObj.isLimitOfTransfer`). Without the invertibility of `|G|` the
statement fails, already for the double cover of `ℝP²` by `S²` with coefficients `ℤ` in degree
zero, where the transfer is multiplication by `2` on `ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G (Proposition 3G.1), for the transfer and the averaging argument, stated there for
  cohomology with field coefficients and invariants; the homology form here is its dual.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B} {G : Type*} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (A : Set B)
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- **The transfer is invariant under the action.** For the quotient covering map `p : E ⟶ B` of
an action of a finite group `G`, the transfer `C(B; R) ⟶ C(E; R)` commutes with the action of `G`
on `C(E; R)` by the chain maps `g_*`, so it is a natural transformation from the constant functor
at `C(B; R)` to that action. -/
def transferπ [Finite G] :
    (Functor.const _).obj (((singularChainComplexFunctor C).obj R).obj B) ⟶
      @TopCat.actionFunctor E G _ _ hG.toContinuousConstSMul ⋙
        (singularChainComplexFunctor C).obj R where
  app _ := hG.isCoveringMap.singularTransfer hG.finite_fiber R
  naturality _ _ g := by
    have := hG.toContinuousConstSMul
    refine (Category.id_comp _).trans ?_
    exact (hG.isCoveringMap.singularTransfer_comp_chainComplexMap_of_comp_eq hG.finite_fiber
      R (f := TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩) (MulAction.bijective g)
      (by ext e; exact hG.map_smul g)).symm

/-- Each component of `hG.transferπ R` is the transfer `C(B; R) ⟶ C(E; R)`. -/
@[simp]
theorem transferπ_app [Finite G] (X : SingleObj G) :
    (hG.transferπ R).app X = hG.isCoveringMap.singularTransfer hG.finite_fiber R :=
  (rfl)

/-- **The transfer as a cone over the action.** For the quotient covering map `p : E ⟶ B` of an
action of a finite group `G`, the transfer `C(B; R) ⟶ C(E; R)` is a cone over the action of `G` on
`C(E; R)`, with point `C(B; R)` and legs `hG.transferπ R`.

Only this two-field wrapper is exposed, so that the cone point is `C(B; R)` by `dsimp`; the
transfer itself, `hG.transferπ R`, stays opaque. -/
@[expose, simps]
def transferCone [Finite G] :
    Cone (@TopCat.actionFunctor E G _ _ hG.toContinuousConstSMul ⋙
      (singularChainComplexFunctor C).obj R) where
  pt := ((singularChainComplexFunctor C).obj R).obj B
  π := hG.transferπ R

/-- **The transfer exhibits invariants.** For the quotient covering map `p : E ⟶ B` of an action of
a finite group `G`, and coefficients `R` on which multiplication by `|G|` is invertible, every
additive functor `F` out of chain complexes sends the transfer `C(B; R) ⟶ C(E; R)` to a limit cone:
`F(C(B; R))` is the object of invariants `F(C(E; R))^G`. -/
def isLimitMapConeTransferCone [Fintype G] [IsIso (Fintype.card G • 𝟙 R)] {D : Type*} [Category D]
    [Preadditive D] (F : ChainComplex C ℕ ⥤ D) [F.Additive] :
    IsLimit (F.mapCone (hG.transferCone R)) := by
  have := hG.toContinuousConstSMul
  -- Singular chains are additive in the coefficients, so `|G|` stays invertible on `C(E; R)` and
  -- `C(B; R)`, and the additive functor `F` keeps it invertible on their images. By
  -- `TopCat.actionFunctor_obj` and `transferCone_pt` (both `rfl`), these are the images of the
  -- acted-on object and of the cone point of `hG.transferCone R`.
  have : IsIso (Fintype.card G • 𝟙 (((E.actionFunctor G ⋙
      (singularChainComplexFunctor C).obj R) ⋙ F).obj (SingleObj.star G))) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj E ⋙ F).isIso_smul_id_obj _ R
  have : IsIso (Fintype.card G • 𝟙 (F.mapCone (hG.transferCone R)).pt) :=
    (singularChainComplexFunctor C ⋙ (evaluation _ _).obj B ⋙ F).isIso_smul_id_obj _ R
  refine SingleObj.isLimitMapConeOfTransfer (hG.transferCone R)
    (SSet.chainComplexMap (TopCat.toSSet.map p) R) F ?_ ?_
  · exact hG.isCoveringMap.singularTransfer_comp_chainComplexMap hG.finite_fiber R fun b ↦
      (hG.natCard_fiber b).trans Nat.card_eq_fintype_card
  -- The functor `(singularChainComplexFunctor C).obj R` sends the action of `g` to `(g • ·)_*`.
  · simp only [Functor.comp_map, TopCat.actionFunctor_map]
    exact hG.chainComplexMap_comp_singularTransfer R

/-- **The singular homology of the base of a finite quotient covering is invariants.** For the
quotient covering map `p : E ⟶ B` of an action of a finite group `G`, and coefficients `R` on
which multiplication by `|G|` is invertible, the transfer `Hₙ(B; R) ⟶ Hₙ(E; R)` exhibits
`Hₙ(B; R)` as the limit `Hₙ(E; R)^G` of the action of `G` on `Hₙ(E; R)`. -/
def isLimitHomologyMapConeTransferCone [Fintype G] [CategoryWithHomology C] (n : ℕ)
    [IsIso (Fintype.card G • 𝟙 R)] :
    IsLimit ((HomologicalComplex.homologyFunctor C _ n).mapCone (hG.transferCone R)) :=
  hG.isLimitMapConeTransferCone R _

/-- **The relative transfer is invariant under the action.** For the quotient covering map
`p : E ⟶ B` of an action of a finite group `G` and a subset `A ⊆ B`, the relative transfer
`C(B, A; R) ⟶ C(E, p⁻¹ A; R)` commutes with the action of `G` on `C(E, p⁻¹ A; R)` by the chain
maps `g_*`, so it is a natural transformation from the constant functor at `C(B, A; R)` to that
action. -/
def pairTransferπ [Finite G] :
    (Functor.const _).obj ((TopPair.ofSubset A).singularChainComplex R) ⟶
      @TopPair.ofSubsetActionFunctor E G _ _ hG.toContinuousConstSMul (p ⁻¹' A)
          (hG.mapsTo_smul_preimage A) ⋙
        TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor C).obj R where
  app _ := hG.isCoveringMap.singularPairTransfer hG.finite_fiber A R
  naturality _ _ g := by
    have := hG.toContinuousConstSMul
    -- The two sides match the lemma by definition: the constant functor sends `g` to `𝟙`
    -- (`Functor.const_obj_map`), and the action functor followed by relative chains sends `g` to
    -- `TopPair.singularChainComplexMap (ofSubsetMap (g • ·) _) R` (`Functor.comp_map` and
    -- `TopPair.ofSubsetActionFunctor_map`). These are not rewritten with `simp only`: even after
    -- specializing both objects to `SingleObj.star G`, the implicit objects of `≫` still read
    -- `((Functor.const _).obj _).obj _` and `(ofSubsetActionFunctor ..).obj _`, so neither
    -- `Category.id_comp` nor the inner `Functor.comp_map` matches syntactically.
    refine (Category.id_comp _).trans ?_
    exact (hG.isCoveringMap.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq
      hG.finite_fiber A R (f := TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩)
      (MulAction.bijective g) (by ext e; exact hG.map_smul g)).symm

/-- Each component of `hG.pairTransferπ A R` is the relative transfer
`C(B, A; R) ⟶ C(E, p⁻¹ A; R)`. -/
@[simp]
theorem pairTransferπ_app [Finite G] (X : SingleObj G) :
    (hG.pairTransferπ A R).app X = hG.isCoveringMap.singularPairTransfer hG.finite_fiber A R :=
  (rfl)

/-- **The relative transfer as a cone over the action.** For the quotient covering map
`p : E ⟶ B` of an action of a finite group `G` and a subset `A ⊆ B`, the relative transfer
`C(B, A; R) ⟶ C(E, p⁻¹ A; R)` is a cone over the action of `G` on `C(E, p⁻¹ A; R)`, with point
`C(B, A; R)` and legs `hG.pairTransferπ A R`. -/
@[expose, simps]
def pairTransferCone [Finite G] :
    Cone (@TopPair.ofSubsetActionFunctor E G _ _ hG.toContinuousConstSMul (p ⁻¹' A)
        (hG.mapsTo_smul_preimage A) ⋙
      TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor C).obj R) where
  pt := (TopPair.ofSubset A).singularChainComplex R
  π := hG.pairTransferπ A R

/-- **The relative transfer exhibits invariants.** For the quotient covering map `p : E ⟶ B` of an
action of a finite group `G`, a subset `A ⊆ B`, and coefficients `R` on which multiplication by
`|G|` is invertible, every additive functor `F` out of chain complexes sends the relative transfer
`C(B, A; R) ⟶ C(E, p⁻¹ A; R)` to a limit cone: `F(C(B, A; R))` is the object of invariants
`F(C(E, p⁻¹ A; R))^G`. -/
def isLimitMapConePairTransferCone [Fintype G] [IsIso (Fintype.card G • 𝟙 R)] {D : Type*}
    [Category D] [Preadditive D] (F : ChainComplex C ℕ ⥤ D) [F.Additive] :
    IsLimit (F.mapCone (hG.pairTransferCone A R)) := by
  have := hG.toContinuousConstSMul
  -- Multiplication by `|G|` is invertible on relative chains, and the additive functor `F` keeps it
  -- invertible on their images. By `TopPair.ofSubsetActionFunctor_obj` and
  -- `pairTransferCone_pt` (both `rfl`), these are the images of the acted-on object and of the
  -- cone point of `hG.pairTransferCone A R`.
  have : IsIso (Fintype.card G • 𝟙 ((TopPair.ofSubset (p ⁻¹' A)).singularChainComplex R)) :=
    SSetPair.isIso_smul_id_chainComplex _ R _
  have : IsIso (Fintype.card G • 𝟙 ((TopPair.ofSubset A).singularChainComplex R)) :=
    SSetPair.isIso_smul_id_chainComplex _ R _
  have : IsIso (Fintype.card G • 𝟙 (((@TopPair.ofSubsetActionFunctor E G _ _
      hG.toContinuousConstSMul (p ⁻¹' A) (hG.mapsTo_smul_preimage A) ⋙ TopPair.toSSetPair ⋙
        (SSetPair.chainComplexFunctor C).obj R) ⋙ F).obj (SingleObj.star G))) :=
    F.isIso_smul_id_obj _ ((TopPair.ofSubset (p ⁻¹' A)).singularChainComplex R)
  have : IsIso (Fintype.card G • 𝟙 (F.mapCone (hG.pairTransferCone A R)).pt) :=
    F.isIso_smul_id_obj _ ((TopPair.ofSubset A).singularChainComplex R)
  refine SingleObj.isLimitMapConeOfTransfer (hG.pairTransferCone A R)
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R) F ?_ ?_
  · exact hG.isCoveringMap.singularPairTransfer_comp_singularChainComplexMap hG.finite_fiber A R
      fun b ↦ (hG.natCard_fiber b).trans Nat.card_eq_fintype_card
  -- The action functor sends `g` to the map of pairs induced by `g • ·`. The composite is
  -- unfolded first so that `TopPair.ofSubsetActionFunctor_map` then matches the implicit objects.
  · simp only [Functor.comp_map]
    simp only [TopPair.ofSubsetActionFunctor_map]
    exact hG.singularChainComplexMap_comp_singularPairTransfer A R

/-- **The relative singular homology of the base of a finite quotient covering is invariants.** For
the quotient covering map `p : E ⟶ B` of an action of a finite group `G`, a subset `A ⊆ B`, and
coefficients `R` on which multiplication by `|G|` is invertible, the relative transfer
`Hₙ(B, A; R) ⟶ Hₙ(E, p⁻¹ A; R)` exhibits `Hₙ(B, A; R)` as the limit `Hₙ(E, p⁻¹ A; R)^G` of the
action of `G` on `Hₙ(E, p⁻¹ A; R)`. -/
def isLimitHomologyMapConePairTransferCone [Fintype G] [CategoryWithHomology C] (n : ℕ)
    [IsIso (Fintype.card G • 𝟙 R)] :
    IsLimit ((HomologicalComplex.homologyFunctor C _ n).mapCone (hG.pairTransferCone A R)) :=
  hG.isLimitMapConePairTransferCone A R _

end IsQuotientCoveringMap
