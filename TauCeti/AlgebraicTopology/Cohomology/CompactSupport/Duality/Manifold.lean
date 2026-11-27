/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.MayerVietoris
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Duality
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Manifold
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

import TauCeti.CategoryTheory.Linear.Int

/-!
# Poincaré duality for oriented manifolds

Let `M` be a Hausdorff topological manifold without boundary, charted on a real normed space `E`
of finite dimension `n`, and let `L` be an abelian group. This file proves Poincaré duality in
Hatcher's form (Theorem 3.35): for every homological orientation `o` of `M`, the duality map

`D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)`, `p + q = n`,

which caps a class with compact support with the fundamental classes of `o` along compact sets
(`TauCeti.HomologicalOrientation.dualityMap`), is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap`). No compactness, connectedness or
countability of `M` is assumed. For compact `M` this is the classical statement that the cap
product with the fundamental class `[M]` is a bijection `Hᵖ(M; L) → H_q(M; L)`
(`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`).

The proof is Hatcher's induction over the open subsets of `M` (Lemma 3.36), run through the
Mayer–Vietoris induction principle over convex chart domains
(`TauCeti.mayerVietoris_induction_extChartAt_of_directed`), for the property of an open subset `U`,
with the orientation restricted from `o`, that its duality map is bijective in every degree:

* on a convex chart domain, which the chart carries onto a convex open subset of `E`
  (`TauCeti.isOpenEmbedding_domRestrict_chartAt_and_convex_range`), it holds by duality for
  convex open subsets of `E` (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_convex`);
* it passes from `U`, `V` and `U ∩ V` to `U ∪ V`, by comparing the Mayer–Vietoris sequences of
  cohomology with compact supports and of homology
  (`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`); in the top degree this uses
  `Hⁿ⁺¹_c(U ∩ V) = 0`, the vanishing of cohomology with compact supports above the dimension
  (`TopCat.isZero_compactSupportCohomology_of_finrank_lt`);
* it passes to directed unions of open subsets
  (`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_monotone`).

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap`: **Poincaré duality**, the duality map of
  an oriented manifold is bijective, and `TauCeti.HomologicalOrientation.isIso_dualityMap` as an
  isomorphism.
* `TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`: for a closed
  oriented manifold, the cap product with the fundamental class is bijective.
* `TauCeti.IsFundamentalClass.bijective_singularCapAddHom`: the same for any integral fundamental
  class of a closed manifold, which orients it.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.35 and Lemma 3.36, and Theorem 3.30 for closed manifolds.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, §5, the Mayer–Vietoris argument for Poincaré duality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology Set
open scoped Manifold

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

/-- Poincaré duality for every open subset of `M`, with the orientation restricted from `o`. -/
private theorem bijective_dualityMap_comap (U : Opens M) (p q : ℕ) (h : p + q = n) :
    Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h) := by
  revert p q h
  refine mayerVietoris_induction_extChartAt_of_directed 𝓘(ℝ, E)
    (fun U : Opens M ↦ ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h)) ?_ ?_ ?_ ?_ U
  · intro p q h
    have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.property⟩
    exact (o.comap _).bijective_dualityMap_of_isEmpty hn L h
  · intro x C U hC hCc hCt hU _ p q h
    obtain ⟨hj, hjc⟩ := isOpenEmbedding_domRestrict_chartAt_and_convex_range hC hCc hCt hU
    exact (o.comap U.isOpenEmbedding').bijective_dualityMap_of_convex hn L h hj hjc
  · intro U V hU hV hUV p q h
    -- The top degree needs `Hⁿ⁺¹_c(U ∩ V) = 0`, the vanishing above the dimension on `U ∩ V`.
    -- It is stated with the `ℤ`-linear structure `ModuleCat.instLinear` of a category of modules,
    -- while the duality maps carry the structure `Linear.preadditiveIntLinear` of a preadditive
    -- category; `convert` identifies the two, as `Linear ℤ (ModuleCat ℤ)` is a subsingleton.
    have h0 := TopCat.isZero_compactSupportCohomology_of_finrank_lt
      (ModuleCat.of ℤ (ULift.{0} ℤ)) L (M := ↥(U ⊓ V)) (E := E) (m := n + 1) (by omega)
    exact o.bijective_dualityMap_comap_sup hn L h hU hV hUV
      (by convert h0 using 2; exact Subsingleton.elim _ _)
  · intro ι _ _ U hU hUD p q h
    exact o.bijective_dualityMap_comap_iSup_of_monotone hn L h hU fun i ↦ hUD i p q h

/-- **Poincaré duality.** For a homological orientation `o` of a Hausdorff manifold `M` without
boundary of dimension `n`, charted on a finite-dimensional real normed space, the duality map
`Hᵖ_c(M; L) ⟶ H_q(M; L)`, `p + q = n`, capping with the fundamental classes of `o` along compact
sets, is bijective, for every abelian group `L`. No compactness, connectedness or countability of
`M` is assumed. -/
theorem bijective_dualityMap (p q : ℕ) (h : p + q = n) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  have hrange : range (Subtype.val : (⊤ : Opens M) → M) = range (id : M → M) := by
    ext x
    simp
  have := (o.bijective_dualityMap_comap_iff_of_range_eq hn L h (⊤ : Opens M).isOpenEmbedding'
    IsOpenEmbedding.id hrange).1 (o.bijective_dualityMap_comap hn L ⊤ p q h)
  rwa [comap_id] at this

/-- **Poincaré duality**, as an isomorphism `Hᵖ_c(M; L) ≅ H_q(M; L)`. -/
instance isIso_dualityMap (p q : ℕ) (h : p + q = n) : IsIso (o.dualityMap hn L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (o.bijective_dualityMap hn L p q h)

/-- **Poincaré duality for a closed oriented manifold.** For a compact Hausdorff manifold `M`
without boundary of dimension `n` with a homological orientation, the cap product with the
fundamental class, `α ↦ [M] ⌢ α` (`TopCat.singularCapAddHom`), is a bijection
`Hᵖ(M; L) → H_q(M; L)` for `p + q = n`. -/
theorem bijective_singularCapAddHom_fundamentalClass [CompactSpace M] (p q : ℕ) (h : p + q = n) :
    Function.Bijective
      ((TopCat.of M).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom h (o.fundamentalClass hn)) := by
  have := (o.bijective_dualityMap hn L p q h).comp (ConcreteCategory.bijective_of_isIso
    (TopCat.compactSupportCohomologyIsoOfCompactSpace (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
      (M := L) (X := TopCat.of M) p).inv)
  convert this using 1
  funext α
  exact (TopCat.singularCapAddHom_apply ..).trans
    (o.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv hn L p q h α).symm

end HomologicalOrientation

/-- **Poincaré duality for an integral fundamental class.** For a compact Hausdorff manifold `M`
without boundary of dimension `n` and an integral fundamental class `μ` of `M`, the cap product
with `μ`, `α ↦ μ ⌢ α`, is a bijection `Hᵖ(M; L) → H_q(M; L)` for `p + q = n`. No orientation is
given: `μ` orients `M` (`TauCeti.HomologicalOrientation.ofIsFundamentalClass`). -/
theorem IsFundamentalClass.bijective_singularCapAddHom {M E : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ) (p q : ℕ) (h : p + q = n) :
    Function.Bijective ((TopCat.of M).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom h μ) := by
  have := (HomologicalOrientation.ofIsFundamentalClass (E := E) hμ)
    |>.bijective_singularCapAddHom_fundamentalClass hn L p q h
  rwa [HomologicalOrientation.fundamentalClass_ofIsFundamentalClass hn hμ] at this

end TauCeti
