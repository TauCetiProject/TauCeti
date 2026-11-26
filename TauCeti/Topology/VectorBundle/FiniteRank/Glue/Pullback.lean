/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Glue
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong

/-!
# Gluing a pullback of a finite-rank core to the core

Let `C` be a point-indexed finite-rank core over `X`, `f : C(X, X)`, and `D : GluingData Φ` glue
the pullback `C.pullback f` near a closed set `K` to `C` along a morphism `Φ : C.pullback f ⟶ C`.
The two cores have the same rank by definition, so no coordinates are reindexed
(`GluingData.rankEquiv_pullback`). Between charts of the pullback the glued transitions are those of
`C` at the images under `f` (`GluingData.coordChange_glue_pullback`), and on `V` the comparison of
the glued core with `C` is `Φ` (`GluingData.fiberMap_glueIso_hom_pullback`).

Two consequences make the glued core a normal form of `C` near `K`:

* `GluingData.coordChange_glue_pullback_apply_eq`: on a subset of `K` which `f` maps into `V` and
  on which `f` is idempotent, the glued core is constant along the fibres of `f`;
* `GluingData.isRealAlong_glue_pullback`: if `C` is complex and real along a set `A ⊆ K` fixed
  pointwise by `f`, so is the glued core.

For a collar projection `f` of a Riemann surface with boundary these are the hypotheses of
`SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`, applied in
`SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`.
-/

public section

open Bundle CategoryTheory Set

namespace TauCeti.FiniteRankBundleCore.GluingData

section Pullback

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  {C : FiniteRankBundleCore 𝕜 X} {f : C(X, X)} {Φ : C.pullback f ⟶ C} (D : GluingData Φ)
  {i j x : X}

/-- Gluing a pullback of `C` to `C` needs no reindexing of coordinates. -/
theorem rankEquiv_pullback : D.rankEquiv = ContinuousLinearEquiv.refl 𝕜 (Fin C.rank → 𝕜) := by
  ext v l
  simp only [rankEquiv_apply, Fin.cast_eq_self]
  -- `v l` and `refl v l` agree by definition; `simp` does not see it, because `v` has coordinates
  -- indexed by `Fin (C.pullback f).rank`, which is `Fin C.rank` only by `rank_pullback`, a `rfl`.
  rfl

/-- The chart of the glued core labelled by a point of `V` is the chart of the pullback, inside
`V`. -/
theorem mem_baseSet_glue_pullback_iff (hi : i ∈ D.V) :
    x ∈ D.glue.core.baseSet i ↔ f x ∈ C.core.baseSet (f i) ∧ x ∈ D.V := by
  rw [baseSet_glue, D.baseSet_of_mem hi, mem_inter_iff, mem_baseSet_pullback]

/-- Between charts of the pullback, the transitions of the glued core are those of `C` at the
images under `f`. -/
theorem coordChange_glue_pullback (hi : i ∈ D.V) (hj : j ∈ D.V) :
    D.glue.core.coordChange i j x = C.core.coordChange (f i) (f j) (f x) := by
  rw [coordChange_glue, D.coordChange_of_mem_of_mem hi hj, rankEquiv_pullback]
  -- Composing with the identity reindexing; the coordinate types agree by `rank_pullback`, which
  -- holds by definition.
  rfl

/-- On `V`, the comparison of the glued core with `C` is `Φ`. -/
theorem fiberMap_glueIso_hom_pullback (hx : x ∈ D.V) :
    D.glueIso.hom.fiberMap x = Φ.fiberMap x := by
  rw [glueIso_hom, D.fiberMap_glueHom_of_mem hx, rankEquiv_pullback]
  -- Composing with the identity reindexing; the coordinate types agree by `rank_pullback`, which
  -- holds by definition.
  rfl

/-- **Constancy along the fibres of `f`.** On a subset `W` of `K` which `f` maps into `V` and on
which `f` is idempotent, the glued core is constant along the fibres of `f`: a chart containing
`x ∈ W` contains `f x`, and the transitions take the same value at `x` and `f x`. This is the
hypothesis `hCρ` of `SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`. -/
theorem coordChange_glue_pullback_apply_eq {W : Set X} (hWK : W ⊆ D.K) (hfV : MapsTo f W D.V)
    (hff : ∀ x ∈ W, f (f x) = f x) (hx : x ∈ W) (hi : x ∈ D.glue.core.baseSet i)
    (hj : x ∈ D.glue.core.baseSet j) :
    f x ∈ D.glue.core.baseSet i ∧ f x ∈ D.glue.core.baseSet j ∧
      D.glue.core.coordChange i j (f x) = D.glue.core.coordChange i j x := by
  have hiV := D.mem_V_of_mem_baseSet_glue (hWK hx) hi
  have hjV := D.mem_V_of_mem_baseSet_glue (hWK hx) hj
  rw [D.mem_baseSet_glue_pullback_iff hiV] at hi ⊢
  rw [D.mem_baseSet_glue_pullback_iff hjV] at hj ⊢
  rw [D.coordChange_glue_pullback hiV hjV, D.coordChange_glue_pullback hiV hjV, hff x hx]
  exact ⟨⟨hi.1, hfV hx⟩, ⟨hj.1, hfV hx⟩, rfl⟩

end Pullback

/-- **The glued core stays real.** Glue a pullback `C.pullback f` near `K` to a complex core `C`
which is real along `A ⊆ K`. If `f` fixes `A`, the glued core is real along `A`: over `A` its
transitions are those of `C`. -/
theorem isRealAlong_glue_pullback {X : Type*} [TopologicalSpace X] {C : FiniteRankBundleCore ℂ X}
    {f : C(X, X)} {Φ : C.pullback f ⟶ C} (D : GluingData Φ) {A : Set X} (hC : C.IsRealAlong A)
    (hfA : ∀ a ∈ A, f a = a) (hAK : A ⊆ D.K) : D.glue.IsRealAlong A := by
  refine isRealAlong_iff_coordChange_star.2 fun i j x hx hi hj v ↦ ?_
  have hiV := D.mem_V_of_mem_baseSet_glue (hAK hx) hi
  have hjV := D.mem_V_of_mem_baseSet_glue (hAK hx) hj
  rw [D.mem_baseSet_glue_pullback_iff hiV, hfA x hx] at hi
  rw [D.mem_baseSet_glue_pullback_iff hjV, hfA x hx] at hj
  rw [D.coordChange_glue_pullback hiV hjV, hfA x hx]
  exact hC.coordChange_star hx hi.1 hj.1 v

end TauCeti.FiniteRankBundleCore.GluingData
