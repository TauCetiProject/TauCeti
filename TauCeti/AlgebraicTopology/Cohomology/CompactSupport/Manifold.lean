/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Vanishing
public import TauCeti.Geometry.Manifold.MayerVietoris

/-!
# Cohomology with compact supports of a manifold vanishes above its dimension

Let `M` be a Hausdorff topological manifold without boundary, charted on a real normed space `E`
of finite dimension `n`. Its cohomology with compact supports vanishes above the dimension:
`Hᵐ_c(M) = 0` for `m > n` (`TopCat.isZero_compactSupportCohomology_of_finrank_lt`), for any
coefficients with projective chain coefficients, with no orientation and no compactness,
connectedness or countability of `M`. For compact `M`, cohomology with compact supports is singular
cohomology, so `Hᵐ(M) = 0` for `m > n` (`TopCat.isZero_singularCohomology_of_finrank_lt`).

The proof is Mayer–Vietoris induction over the open subsets of `M`
(`TauCeti.mayerVietoris_induction_extChartAt_of_directed`), for the property of an open subset `U`
that `Hᵐ_c(U) = 0` for every `m > n`:

* on a convex chart domain, which the chart carries onto a convex open subset of `E`
  (`TauCeti.isOpenEmbedding_domRestrict_chartAt_and_convex_range`), cohomology with compact
  supports is that of `E`, concentrated in degree `n`
  (`TopCat.isZero_compactSupportCohomology_of_convex`);
* it passes from `U`, `V` and `U ∩ V` to `U ∪ V` by the Mayer–Vietoris sequence, which needs the
  vanishing on `U ∩ V` one degree up (`TopCat.isZero_compactSupportCohomology_sup`);
* it passes to directed unions of open subsets
  (`TopCat.isZero_compactSupportCohomology_iSup_of_monotone`).

This vanishing is the top-degree input of Poincaré duality, whose Mayer–Vietoris step needs
`Hⁿ⁺¹_c(U ∩ V) = 0` (`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the proof of Lemma 3.36, which carries `Hⁱ_c(U) = 0` for `i > n` through the
  induction.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology Set
open scoped Manifold

universe v

namespace TopCat

variable {k : Type v} [CommRing k] (R N : ModuleCat.{v} k) [Module.Projective k R]
  {M E : Type v} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **Cohomology with compact supports vanishes above the dimension**: for a Hausdorff manifold
`M` charted on a finite-dimensional real normed space `E`, `Hᵐ_c(M; R, N) = 0` for every degree
`m > dim E`, for any coefficients with projective `R`. No orientation, compactness or countability
of `M` is assumed. -/
theorem isZero_compactSupportCohomology_of_finrank_lt {m : ℕ} (hm : finrank ℝ E < m) :
    IsZero ((TopCat.of M).compactSupportCohomology R k N m) := by
  -- The vanishing holds on every open subset of `M`, by Mayer–Vietoris induction.
  have key : ∀ U : Opens M, ∀ m, finrank ℝ E < m →
      IsZero (((Opens.toTopCat (TopCat.of M)).obj U).compactSupportCohomology R k N m) := by
    refine TauCeti.mayerVietoris_induction_extChartAt_of_directed 𝓘(ℝ, E) _ ?_ ?_ ?_ ?_
    · intro m _
      have : IsEmpty ((Opens.toTopCat (TopCat.of M)).obj ⊥) := ⟨fun x ↦ x.property⟩
      exact isZero_compactSupportCohomology_of_isEmpty R k N m
    · intro x C U hC hCc hCt hU _ m hm
      obtain ⟨hj, hjc⟩ := TauCeti.isOpenEmbedding_domRestrict_chartAt_and_convex_range hC hCc hCt hU
      exact isZero_compactSupportCohomology_of_convex R N (j := ofHom ⟨_, hj.continuous⟩) hj hjc
        hm.ne'
    · intro U V hU hV hUV m hm
      exact isZero_compactSupportCohomology_sup (hU m hm) (hV m hm) (hUV (m + 1) (by omega))
    · intro ι _ _ U hU hUm m hm
      exact isZero_compactSupportCohomology_iSup_of_monotone hU fun i ↦ hUm i m hm
  exact (key ⊤ m hm).of_iso (compactSupportCohomologyIsoOfHomeomorph R k N
    (homeoOfIso (Opens.inclusionTopIso (TopCat.of M))) m).symm

/-- **The cohomology of a compact manifold vanishes above the dimension**: for a compact Hausdorff
manifold `M` charted on a finite-dimensional real normed space `E`, `Hᵐ(M; R, N) = 0` for every
degree `m > dim E`, for any coefficients with projective `R`. No orientation is assumed. -/
theorem isZero_singularCohomology_of_finrank_lt [CompactSpace M] {m : ℕ} (hm : finrank ℝ E < m) :
    IsZero ((TopCat.of M).singularCohomology R k N m) :=
  (isZero_compactSupportCohomology_of_finrank_lt R N hm).of_iso
    (compactSupportCohomologyIsoOfCompactSpace m).symm

end TopCat
