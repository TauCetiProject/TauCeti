/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import Mathlib.Geometry.Manifold.HasGroupoid

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
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`):

* **Surjectivity.** A class of `H_q(M)` comes from some `H_q(U i)`
  (`TauCeti.exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top`), hence from a class of
  `Hᵖ_c(U i)` under `D_{U i}`, whose extension to `M` is then a preimage under `D_M`
  (`TauCeti.HomologicalOrientation.surjective_dualityMap_of_iSup_eq_top`).
* **Injectivity.** A class of `Hᵖ_c(M)` is extended from some `Hᵖ_c(U i)`
  (`TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top`). If `D_M` kills it, the
  image under `D_{U i}` vanishes in `H_q(M)`, hence already in some larger `H_q(U j)`
  (`TauCeti.exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top`). That image is the
  value of `D_{U j}` on the extension of the class to `U j`, which therefore vanishes, and so does
  its extension to `M` (`TauCeti.HomologicalOrientation.injective_dualityMap_of_iSup_eq_top`).

The orientation of `U i` pulled back from that of `U j` is the one pulled back from `M`
(`TauCeti.HomologicalOrientation.comap_comap_of_comp_eq`), so the duality maps of the members are
compared by the naturality of the duality maps of `U j`
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_comap_dualityMap`).

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_comap_dualityMap`: for open sets
  `V ⊆ W` of `M` with the pulled-back orientations, `D_W ∘ ι_! = ι_* ∘ D_V` for the inclusion
  `ι : V → W`.
* `TauCeti.HomologicalOrientation.injective_dualityMap_of_iSup_eq_top`,
  `TauCeti.HomologicalOrientation.surjective_dualityMap_of_iSup_eq_top`: injectivity and
  surjectivity of the duality maps of the members of a directed open cover pass to the union.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`: **Poincaré duality for a
  directed union of open sets**.

## Implementation notes

The coefficient and universe conventions are those of `TauCeti.HomologicalOrientation.dualityMap`.
An open set `V` of `M` is a manifold with the charts of `TopologicalSpace.Opens.instChartedSpace`
and is oriented by the pullback of `o` along the inclusion `Subtype.val : V → M`, an open embedding
by `TopologicalSpace.Opens.isOpenEmbedding'`.

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

section OpenSubset

variable {V W : Opens M} (hVW : V ≤ W) (p q : ℕ) (h : p + q = n)

/-- **Naturality of the duality maps of open sets**: for open sets `V ⊆ W` of `M`, oriented by the
pullbacks of `o`, the duality maps intertwine the extension `ι_! : Hᵖ_c(V; L) ⟶ Hᵖ_c(W; L)` and the
pushforward `ι_* : H_q(V; L) ⟶ H_q(W; L)` along the inclusion `ι : V → W`:
`D_W ∘ ι_! = ι_* ∘ D_V`. -/
theorem compactSupportCohomologyExtend_comap_dualityMap :
    TopCat.compactSupportCohomologyExtend
        (f := TopCat.ofHom ⟨Opens.inclusion hVW, (Opens.isOpenEmbedding_of_le hVW).continuous⟩)
        (Opens.isOpenEmbedding_of_le hVW) p ≫
        (o.comap W.isOpenEmbedding').dualityMap hn L p q h =
      (o.comap V.isOpenEmbedding').dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom ⟨Opens.inclusion hVW, (Opens.isOpenEmbedding_of_le hVW).continuous⟩) := by
  -- `Opens.isOpenEmbedding_of_le` is stated for the inclusion of the underlying sets; restate it
  -- for the subtypes `V` and `W`, which carry the charts of open subsets.
  have hι : IsOpenEmbedding (Opens.inclusion hVW) := Opens.isOpenEmbedding_of_le hVW
  rw [← o.comap_comap_of_comp_eq W.isOpenEmbedding' hι V.isOpenEmbedding' rfl]
  exact (o.comap W.isOpenEmbedding').compactSupportCohomologyExtend_dualityMap hn L
    (j := ⟨Opens.inclusion hVW, hι.continuous⟩) hι p q h

end OpenSubset

variable {J : Type} [Preorder J] [IsDirected J (· ≤ ·)] {U : J → Opens M}
  (hU : Monotone U) (hcover : ⨆ j, U j = ⊤) {p q : ℕ} (h : p + q = n)

include hU hcover

/-- **Surjectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are surjective, then the duality map of `M` is surjective. -/
theorem surjective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Surjective ((o.comap (U j).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun x ↦ by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · -- An empty family covers only the empty manifold.
    have : IsEmpty M := ⟨fun x ↦ isEmptyElim (Opens.mem_iSup.1 (hcover ▸ Opens.mem_top x)).choose⟩
    exact (o.bijective_dualityMap_of_isEmpty hn L h).2 x
  obtain ⟨j, y, rfl⟩ := exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top L q hU hcover x
  obtain ⟨z, rfl⟩ := hD j y
  refine ⟨TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom ⟨Subtype.val,
    continuous_subtype_val⟩) (U j).isOpenEmbedding' p z, ?_⟩
  rw [← ConcreteCategory.comp_apply, o.compactSupportCohomologyExtend_dualityMap hn L
    (U j).isOpenEmbedding' p q h, ConcreteCategory.comp_apply]
  -- The inclusion `Opens.inclusion' (U j)` is the subtype inclusion, by definition.
  rfl

/-- **Injectivity of the duality map passes to directed unions**: if `M` is covered by a directed
family of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are injective, then the duality map of `M` is injective. -/
theorem injective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Injective ((o.comap (U j).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · -- An empty family covers only the empty manifold.
    have : IsEmpty M := ⟨fun x ↦ isEmptyElim (Opens.mem_iSup.1 (hcover ▸ Opens.mem_top x)).choose⟩
    exact (o.bijective_dualityMap_of_isEmpty hn L h).1
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨i, z, hz⟩ :=
    TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top (X := TopCat.of M) hU hcover x
  -- The colimit descriptions are stated for the spaces `(Opens.toTopCat M).obj V`, which are the
  -- subtypes `V` by definition, while the duality maps are stated for the subtypes, which carry
  -- the charts of open subsets. The term-mode restatements below cross between the two.
  obtain ⟨z, rfl⟩ : ∃ z' : (TopCat.of (U i)).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p, TopCat.compactSupportCohomologyExtend
        (f := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (U i).isOpenEmbedding' p z' = x :=
    ⟨z, hz⟩
  -- `D_M` on the extension of `z` is the pushforward of `D_{U i} z`, which therefore vanishes in
  -- `H_q(M)`, hence in some `H_q(U j)`.
  rw [← ConcreteCategory.comp_apply, o.compactSupportCohomologyExtend_dualityMap hn L
    (U i).isOpenEmbedding' p q h, ConcreteCategory.comp_apply] at hx
  have hx' : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (Opens.inclusion' (X := TopCat.of M) (U i))
      ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) = 0 := hx
  obtain ⟨j, hij, hj⟩ := exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top L q hU
    hcover _ hx'
  have hj' : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopCat.ofHom ⟨Opens.inclusion (hU hij), (Opens.isOpenEmbedding_of_le (hU hij)).continuous⟩)
      ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) = 0 := hj
  -- `D_{U j}` kills the extension of `z` to `U j`, which therefore vanishes.
  have hz : TopCat.compactSupportCohomologyExtend
      (f := TopCat.ofHom ⟨Opens.inclusion (hU hij),
        (Opens.isOpenEmbedding_of_le (hU hij)).continuous⟩)
      (Opens.isOpenEmbedding_of_le (hU hij)) p z = 0 := by
    refine (injective_iff_map_eq_zero _).1 (hD j) _ ?_
    rw [← ConcreteCategory.comp_apply, o.compactSupportCohomologyExtend_comap_dualityMap hn L
      (hU hij) p q h, ConcreteCategory.comp_apply, hj']
  -- So does its extension to `M`, which is the extension of `z`.
  rw [TopCat.compactSupportCohomologyExtend_congr (g := TopCat.ofHom ⟨Opens.inclusion (hU hij),
      (Opens.isOpenEmbedding_of_le (hU hij)).continuous⟩ ≫ TopCat.ofHom ⟨Subtype.val,
      continuous_subtype_val⟩) rfl (U i).isOpenEmbedding'
      ((U j).isOpenEmbedding'.comp (Opens.isOpenEmbedding_of_le (hU hij))),
    TopCat.compactSupportCohomologyExtend_comp (Opens.isOpenEmbedding_of_le (hU hij))
      (U j).isOpenEmbedding' p ((U j).isOpenEmbedding'.comp (Opens.isOpenEmbedding_of_le (hU hij))),
    ConcreteCategory.comp_apply, hz, map_zero]

/-- **Poincaré duality for a directed union of open sets**: if `M` is covered by a directed family
of open sets `U j`, oriented by the pullbacks of `o`, whose duality maps
`Hᵖ_c(U j; L) ⟶ H_q(U j; L)` are bijective, then the duality map
`Hᵖ_c(M; L) ⟶ H_q(M; L)` of `M` is bijective. -/
theorem bijective_dualityMap_of_iSup_eq_top
    (hD : ∀ j, Function.Bijective ((o.comap (U j).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) :=
  ⟨o.injective_dualityMap_of_iSup_eq_top hn L hU hcover h fun j ↦ (hD j).1,
    o.surjective_dualityMap_of_iSup_eq_top hn L hU hcover h fun j ↦ (hD j).2⟩

end HomologicalOrientation

end TauCeti
