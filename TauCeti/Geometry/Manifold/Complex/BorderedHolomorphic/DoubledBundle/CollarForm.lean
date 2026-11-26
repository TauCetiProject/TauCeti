/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.CollarProjection
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Glue
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Pullback.Comparison

/-!
# Every bundle pair has a smooth doubled bundle up to isomorphism

Let `M` be a Hausdorff, second-countable Riemann surface with compact boundary `A`, and `(C, F)` a
bundle pair over `M`: a complex core `C` real along `A`, with real `C^n` transitions. The doubled
bundle of `C` is smooth when `C` is constant along the fibres of a collar projection
(`TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`), which a general atlas is not.
This file replaces `C` by an isomorphic pair which is
(`TauCeti.SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`).

The replacement glues the pullback `C.pullback ρ` along a collar projection `ρ`
(`TauCeti.SchottkyDouble.exists_collarProjection`) to `C` itself, along the comparison
`C.pullback ρ ⟶ C` of `TauCeti.FiniteRankBundleCore.exists_pullbackComparison`, which is the
identity over `A` and invertible near `A`. Near `A` only charts of the pullback occur, and their
transitions `x ↦ C.coordChange (ρ i) (ρ j) (ρ x)` are constant along the fibres of `ρ` because
`ρ ∘ ρ = ρ` there. Over `A` they are transitions of `C`, since `ρ` fixes `A`, so the glued core is
again real along `A`; and the isomorphism with `C` is the identity over `A`, so it carries the
totally real subbundle of the glued pair to `F`.

## Main results

* `TauCeti.FiniteRankBundleCore.GluingData.coordChange_glue_pullback`: gluing a pullback
  `C.pullback f` to `C`, the transitions between charts of the pullback are those of `C` at the
  images under `f`.
* `TauCeti.FiniteRankBundleCore.GluingData.isRealAlong_glue_pullback`: if `f` fixes `A` and `C` is
  real along `A`, so is the glued core.
* `TauCeti.FiniteRankBundleCore.GluingData.coordChange_glue_pullback_apply_eq`: where `f` is
  idempotent, the glued core is constant along the fibres of `f`.
* `TauCeti.SchottkyDouble.exists_iso_contMDiffOn_coordChange_doubledBundleCore`: every bundle pair
  is isomorphic, by a real `C^n` isomorphism commuting with conjugation over the boundary, to a
  bundle pair with real `C^n` transitions whose doubled bundle has real `C^n` transitions.

Not treated here: independence of the doubled bundle of the choices made, up to isomorphism.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3.
-/

public section

open Bundle CategoryTheory Set
open scoped Manifold ContDiff

namespace TauCeti

namespace FiniteRankBundleCore.GluingData

section Pullback

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  {C : FiniteRankBundleCore 𝕜 X} {f : C(X, X)} {Φ : C.pullback f ⟶ C} (D : GluingData Φ)
  {i j x : X}

/-- Gluing a pullback of `C` to `C` needs no reindexing of coordinates. -/
theorem rankEquiv_pullback : D.rankEquiv = ContinuousLinearEquiv.refl 𝕜 (Fin C.rank → 𝕜) := by
  ext v l
  simp only [rankEquiv_apply, Fin.cast_eq_self]
  rfl

/-- The chart of the glued core labelled by a point of `V` is the chart of the pullback, inside
`V`. -/
theorem mem_baseSet_glue_pullback_iff (hi : i ∈ D.V) :
    x ∈ D.glue.core.baseSet i ↔ f x ∈ C.core.baseSet (f i) ∧ x ∈ D.V := by
  rw [baseSet_glue, D.baseSet_of_mem hi]
  exact Iff.rfl

/-- Between charts of the pullback, the transitions of the glued core are those of `C` at the
images under `f`. -/
theorem coordChange_glue_pullback (hi : i ∈ D.V) (hj : j ∈ D.V) :
    D.glue.core.coordChange i j x = C.core.coordChange (f i) (f j) (f x) := by
  rw [coordChange_glue, D.coordChange_of_mem_of_mem hi hj, rankEquiv_pullback]
  rfl

/-- On `V`, the comparison of the glued core with `C` is `Φ`. -/
theorem fiberMap_glueIso_hom_pullback (hx : x ∈ D.V) :
    D.glueIso.hom.fiberMap x = Φ.fiberMap x := by
  rw [glueIso_hom, D.fiberMap_glueHom_of_mem hx, rankEquiv_pullback]
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

end FiniteRankBundleCore.GluingData

namespace SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid] [T2Space M] [SecondCountableTopology M]

local notation "A" => (borderedInterior M : Set M)ᶜ

/-- **Every bundle pair has a smooth doubled bundle, up to isomorphism.** Let `M` be a Hausdorff,
second-countable Riemann surface with compact boundary, and `C` a complex core over `M` real along
the boundary, with real `C^n` transitions. Then there are a complex core `G` real along the
boundary and an isomorphism `e : G ≅ C` such that

* the transitions of `G` are real `C^n`;
* the chart operators of `e` and of its inverse are real `C^n`;
* over the boundary, `e` commutes with coordinatewise conjugation, so it carries the real
  subbundle of `G` onto that of `C`;
* the transitions of the doubled bundle of `G` are real `C^n` on the Schottky double. -/
theorem exists_iso_contMDiffOn_coordChange_doubledBundleCore (hA : IsCompact A)
    (C : FiniteRankBundleCore ℂ M) (hC : C.IsRealAlong A) {n : ℕ∞}
    (hg : ∀ i j, ContMDiffOn closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j)) :
    ∃ (G : FiniteRankBundleCore ℂ M) (hG : G.IsRealAlong A) (e : G ≅ C),
      (∀ i j, ContMDiffOn closedUpperHalfPlaneModel
        𝓘(ℝ, (Fin G.rank → ℂ) →L[ℂ] (Fin G.rank → ℂ)) n
        (G.core.coordChange i j) (G.core.baseSet i ∩ G.core.baseSet j)) ∧
      (∀ i k, ContMDiffOn closedUpperHalfPlaneModel
        𝓘(ℝ, (Fin G.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) n
        (fun x ↦ G.core.inChartCoordinates C.core i k x (e.hom.fiberMap x))
        (G.core.baseSet i ∩ C.core.baseSet k)) ∧
      (∀ k i, ContMDiffOn closedUpperHalfPlaneModel
        𝓘(ℝ, (Fin C.rank → ℂ) →L[ℂ] (Fin G.rank → ℂ)) n
        (fun x ↦ C.core.inChartCoordinates G.core k i x (e.inv.fiberMap x))
        (C.core.baseSet k ∩ G.core.baseSet i)) ∧
      (∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) ∧
      ∀ i j, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, (Fin (doubledBundleCore G hG).rank → ℂ) →L[ℂ]
        (Fin (doubledBundleCore G hG).rank → ℂ)) n
        ((doubledBundleCore G hG).core.coordChange i j)
        ((doubledBundleCore G hG).core.baseSet i ∩ (doubledBundleCore G hG).core.baseSet j) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ClosedUpperHalfPlane M
  obtain ⟨U, hU, hAU, ρ, hρc, hρA, hρfix, hρfold, hρU⟩ := exists_collarProjection hA
  replace hρU := hρU.of_le (m := n) (WithTop.coe_le_coe.2 le_top)
  set f : C(M, M) := ⟨ρ, hρc⟩
  obtain ⟨Φ, hΦ, hΦA, V, hV, hAV, hVU, hinv⟩ :=
    C.exists_pullbackComparison hg f hU hA.isClosed hAU hρU hρfix
  -- A compact neighbourhood `K` of the boundary inside `V`, over which only charts of the
  -- pullback occur.
  obtain ⟨K, hK, hAK, hKV⟩ := exists_compact_between hA hV hAV
  let D : FiniteRankBundleCore.GluingData Φ :=
    ⟨rfl, V, K, hV, hK.isClosed, hKV, hinv⟩
  -- The transitions of the pullback are `C^n` inside `V`, where `ρ` is.
  have hP (i j : M) : ContMDiffOn closedUpperHalfPlaneModel
      𝓘(ℝ, (Fin (C.pullback f).rank → ℂ) →L[ℂ] (Fin (C.pullback f).rank → ℂ)) n
      ((C.pullback f).core.coordChange i j)
      ((C.pullback f).core.baseSet i ∩ (C.pullback f).core.baseSet j ∩ D.V) :=
    (hg (ρ i) (ρ j)).comp (hρU.mono fun _ hx ↦ hVU hx.2) fun _ hx ↦ hx.1
  -- Near the boundary, `ρ` lands in the boundary, which it fixes, so `ρ ∘ ρ = ρ` there.
  set W := U ∩ interior K
  have hWU : W ⊆ U := inter_subset_left
  have hAW : A ⊆ W := subset_inter hAU hAK
  refine ⟨D.glue, D.isRealAlong_glue_pullback hC hρfix (hAK.trans interior_subset), D.glueIso,
    D.contMDiffOn_coordChange_glue hg hΦ hP, D.contMDiffOn_inChartCoordinates_glueIso_hom hg hΦ,
    D.contMDiffOn_inChartCoordinates_glueIso_inv hg hΦ, fun a ha v ↦ ?_, fun i j ↦ ?_⟩
  · rw [D.fiberMap_glueIso_hom_pullback (hAV ha), hΦA a ha]
    rfl
  · exact contMDiffOn_coordChange_doubledBundleCore _ _ (D.contMDiffOn_coordChange_glue hg hΦ hP)
      (hU.inter isOpen_interior) hAW (hρA.mono_left hWU)
      ((hρfold.of_le (WithTop.coe_le_coe.2 le_top)).mono (preimage_mono hWU))
      (fun i j x hx hi hj ↦ D.coordChange_glue_pullback_apply_eq (W := W)
        (fun y hy ↦ interior_subset hy.2) (fun y hy ↦ hAV (hρA hy.1))
        (fun y hy ↦ hρfix _ (hρA hy.1)) hx hi hj) i j

end SchottkyDouble

end TauCeti
