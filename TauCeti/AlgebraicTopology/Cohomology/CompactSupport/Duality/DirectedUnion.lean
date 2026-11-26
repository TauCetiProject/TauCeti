/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.Topology.Sets.Opens

/-!
# Poincaré duality for a directed union of open sets

Let `M` be an `n`-manifold without boundary with an orientation `o`, and let `U i` be a directed
family of open subsets covering `M`, each carrying the orientation pulled back from `o`. If the
duality maps `D_{U i} : Hᵖ_c(U i; L) ⟶ H_q(U i; L)`, `p + q = n`, are all bijective, then so is the
duality map `D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`). This is the step of the
proof of Poincaré duality for noncompact manifolds that passes from the members of an increasing
open cover to their union, for instance from finite unions of convex open subsets of a chart to an
arbitrary open subset of the chart.

Both halves are compactness arguments, through the two colimit descriptions
`Hᵖ_c(M) = colim_i Hᵖ_c(U i)` (`TopCat.isColimitCompactSupportCohomologyOpensCocone`) and
`H_q(M) = colim_i H_q(U i)` (`TauCeti.isColimitMapCoconeSingularHomology`), and the naturality of
the duality maps along the inclusions of open sets
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap_apply`,
`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply`):

* **Surjectivity.** A class of `H_q(M)` comes from some `H_q(U i)`
  (`TauCeti.exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top`), hence from a class of
  `Hᵖ_c(U i)` under `D_{U i}`, whose extension to `M` is then a preimage under `D_M`
  (`TauCeti.HomologicalOrientation.surjective_dualityMap_of_iSup_eq_top`).
* **Injectivity.** A class of `Hᵖ_c(M)` is extended from some `Hᵖ_c(U i)`
  (`TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top`). If `D_M` kills it, the
  image under `D_{U i}` vanishes in `H_q(M)`, hence already in some larger `H_q(U j)`
  (`TauCeti.exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top`). That image is the
  value of `D_{U j}` on the extension of the class to `U j`, which therefore vanishes, and so does
  its extension to `M` (`TopCat.compactSupportCohomologyExtend_toTopCat_map_comp_apply`,
  `TauCeti.HomologicalOrientation.injective_dualityMap_of_iSup_eq_top`).

An empty family covers only the empty manifold (`TopologicalSpace.Opens.isEmpty_of_iSup_eq_top`),
whose duality map is bijective (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isEmpty`).

## Main results

* `TauCeti.HomologicalOrientation.injective_dualityMap_of_iSup_eq_top`,
  `TauCeti.HomologicalOrientation.surjective_dualityMap_of_iSup_eq_top`: injectivity and
  surjectivity of the duality maps of the members of a directed open cover pass to the union.
* Together they give `TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`
  (**Poincaré duality for a directed union of open sets**, in `Duality/Basic.lean`).

## Implementation notes

The coefficient and universe conventions are those of `TauCeti.HomologicalOrientation.dualityMap`.
An open set `V` of `M` is a manifold with the charts of `TopologicalSpace.Opens.instChartedSpace`
and is oriented by the pullback of `o` along the inclusion `TopologicalSpace.Opens.inclusion' V`,
an open embedding by `TopologicalSpace.Opens.isOpenEmbedding`, as for the Mayer–Vietoris
compatibilities of the duality maps.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.36 and the proof of Theorem 3.35: the duality map of an increasing union of
  open sets is an isomorphism if the duality maps of the members are.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

variable {J : Type} [Preorder J] [IsDirected J (· ≤ ·)] {U : J → Opens (TopCat.of M)}
  (hU : Monotone U) (hcover : ⨆ j, U j = ⊤) {p q : ℕ} (h : p + q = n)

include hU hcover

/-- **Surjectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are surjective, then the duality map of `M` is surjective. -/
theorem surjective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Surjective ((o.comap (U j).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun x ↦ by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have : IsEmpty M := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).2 x
  obtain ⟨j, y, rfl⟩ := exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top L q hU hcover x
  obtain ⟨z, rfl⟩ := hD j y
  exact ⟨_, o.compactSupportCohomologyExtend_inclusion'_dualityMap_apply hn L (U j) h z⟩

/-- **Injectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are injective, then the duality map of `M` is injective. -/
theorem injective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Injective ((o.comap (U j).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have : IsEmpty M := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).1
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨i, z, rfl⟩ :=
    TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
  -- `D_M` on the extension of `z` is the pushforward of `D_{U i} z`, which therefore vanishes in
  -- `H_q(M)`, hence in some `H_q(U j)`.
  rw [compactSupportCohomologyExtend_inclusion'_dualityMap_apply] at hx
  obtain ⟨j, hij, hj⟩ :=
    exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top L q hU hcover _ hx
  -- `D_{U j}` kills the extension of `z` to `U j`, which therefore vanishes.
  have hz : TopCat.compactSupportCohomologyExtend
      (Opens.isOpenEmbedding_toTopCat_map (homOfLE (hU hij))) p z = 0 :=
    (injective_iff_map_eq_zero _).1 (hD j) _
      ((o.compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply hn L (homOfLE (hU hij)) h
        z).trans hj)
  -- So does its extension to `M`, which is the extension of `z`.
  rw [← TopCat.compactSupportCohomologyExtend_toTopCat_map_comp_apply (homOfLE (hU hij)), hz,
    map_zero]

end HomologicalOrientation

end TauCeti
