/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents
public import TauCeti.Topology.Covering.PuncturedDisc

import TauCeti.GroupTheory.Perm.Partition
import TauCeti.Topology.Covering.Finite
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The power-map charts of the components over infinity

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over the basepoint `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`, with monodromy triple `(σ0, σ1, σinf)`. The connected components of the
preimage `p ⁻¹' D∞*` of the standard punctured neighborhood `D∞* = {z | 2 < ‖z‖}` of infinity are
the cycles of `σinf` (`IsCoveringMap.sameCycleQuotientσinfEquivConnectedComponents`). This file
computes the degree of each of them, and with it the local model of the cover over `D∞*`:

* the component of the cycle of the sheet `i` has as many points over `pPlus ∈ D∞*` as the cycle
  of `i` has elements, namely `Function.minimalPeriod σinf i`;
* in the coordinate `z ↦ 2 / z`, which identifies `D∞*` with the punctured unit disc `𝔻*`, the
  restriction of `p` to that component is isomorphic over `𝔻*` to the power map `w ↦ w ^ e`
  exactly when `e` is the length of the cycle of `i`.

These isomorphisms are the charts along which the puncture of each component is filled in when
the cover is compactified to a branched cover of the Riemann sphere: the added point is `w = 0`,
and the compactified cover is `w ↦ w ^ e` near it, with `e` the length of the cycle. Each chart is
unique only up to a rotation by an `e`-th root of unity
(`TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`).

## Main declarations

* `IsCoveringMap.ncard_connectedComponent_inter_fiber_σinf`: the component of the cycle of `i`
  has `Function.minimalPeriod σinf i` points over `pPlus`.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σinf`: the restriction of
  `p` to that component is, in the coordinate `z ↦ 2 / z`, isomorphic to `w ↦ w ^ e` exactly when
  `e = Function.minimalPeriod σinf i`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (the components of the preimage of a punctured disc and their power-map charts) and
  §2.7 (the local degrees are the cycle lengths of the monodromy).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §5, Theorem 5.10, and §8, Theorem 8.4.
-/

public section

noncomputable section

namespace TauCeti

open ThricePuncturedSphere Equiv Equiv.Perm Function Metric Set

variable {n : ℕ} {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}
  (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

/-- **The degree of a component over infinity is the length of its cycle.** The connected
component of `p ⁻¹' D∞*` that corresponds to the cycle of the sheet `i` under
`IsCoveringMap.sameCycleQuotientσinfEquivConnectedComponents` contains exactly
`Function.minimalPeriod σinf i` points over `pPlus`: the endpoints of the lifts of `αPlus`
starting at the sheets of that cycle. -/
theorem _root_.IsCoveringMap.ncard_connectedComponent_inter_fiber_σinf (i : Fin n) :
    {y ∈ connectedComponent (⟨hp.monodromy (.mk αPlus) (ν.symm i),
        hp.monodromy_αPlus_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodInf) |
          p y = pPlus}.ncard =
      minimalPeriod (hp.monodromyTriple ν).σinf i := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (p ⁻¹' puncturedNeighborhoodInf) :=
    (isOpen_puncturedNeighborhoodInf.preimage hp.continuous).locallyPathConnectedSpace
  -- The point over `pPlus` of the sheet `j`.
  let x : Fin n → p ⁻¹' puncturedNeighborhoodInf := fun j ↦
    ⟨hp.monodromy (.mk αPlus) (ν.symm j), hp.monodromy_αPlus_mem_preimage (ν.symm j)⟩
  have hx : Injective x := fun j k hjk ↦ by
    have h : ((hp.monodromy (.mk αPlus) (ν.symm j) : p ⁻¹' {pPlus}) : E) =
        hp.monodromy (.mk αPlus) (ν.symm k) :=
      congrArg (fun y : p ⁻¹' puncturedNeighborhoodInf ↦ (y : E)) hjk
    rw [← coveringFiberEquiv_apply, ← coveringFiberEquiv_apply, ← Subtype.ext_iff,
      EmbeddingLike.apply_eq_iff_eq, EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  -- Two of these points lie in one component exactly when their sheets lie in one cycle.
  have hjoin (j : Fin n) : x j ∈ connectedComponent (x i) ↔
      (hp.monodromyTriple ν).σinf.SameCycle i j := by
    rw [← pathComponent_eq_connectedComponent, mem_pathComponent_iff,
      hp.sameCycle_monodromyTriple_σinf_iff_joinedIn, joinedIn_iff_joined (x i).2 (x j).2]
  have hset : {y ∈ connectedComponent (x i) | p y = pPlus} =
      x '' {j | (hp.monodromyTriple ν).σinf.SameCycle i j} := by
    ext y
    constructor
    · rintro ⟨hyC, hy⟩
      -- Every point over `pPlus` is the endpoint of the lift of `αPlus` from some sheet.
      let j := ν ((coveringFiberEquiv hp (.mk αPlus)).symm ⟨y, hy⟩)
      have hxj : x j = y := Subtype.ext <| by
        simp only [x, j, Equiv.symm_apply_apply, ← coveringFiberEquiv_apply,
          Equiv.apply_symm_apply]
      exact ⟨j, (hjoin j).1 (hxj ▸ hyC), hxj⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(hjoin j).2 hj, (hp.monodromy (.mk αPlus) (ν.symm j)).2⟩
  rw [hset, ncard_image_of_injective _ hx, ncard_setOf_sameCycle]

/-- The coordinate `z ↦ 2 / z` of the punctured neighborhood of infinity, valued in the punctured
unit disc. -/
local notation "κInf" =>
  puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.trans
    puncturedDiscOneHalfHomeomorphPuncturedDisc

/-- **The components over infinity are power maps.** In the coordinate `z ↦ 2 / z`, which
identifies the punctured neighborhood `D∞*` of infinity with the punctured unit disc `𝔻*`, the
restriction of `p` to the component of `p ⁻¹' D∞*` corresponding to the cycle of the sheet `i` is
isomorphic over `𝔻*` to the power map `w ↦ w ^ e`, for `e ≠ 0`, exactly when `e` is the length
`Function.minimalPeriod σinf i` of that cycle. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σinf
    (i : Fin n) {e : ℕ} (he : e ≠ 0) :
    (∃ h : connectedComponent (⟨hp.monodromy (.mk αPlus) (ν.symm i),
          hp.monodromy_αPlus_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodInf) ≃ₜ
            ↥(ball (0 : ℂ) 1 \ {0}),
        puncturedDiscPow he ∘ h =
          (connectedComponent (⟨hp.monodromy (.mk αPlus) (ν.symm i),
            hp.monodromy_αPlus_mem_preimage (ν.symm i)⟩ :
              p ⁻¹' puncturedNeighborhoodInf)).domRestrict
                (κInf ∘ puncturedNeighborhoodInf.restrictPreimage p)) ↔
      minimalPeriod (hp.monodromyTriple ν).σinf i = e := by
  have hq := (hp.restrictPreimage puncturedNeighborhoodInf).homeomorph_comp κInf
  -- The fibres of `p` are finite, being in bijection with the numbered fibre over `basePt`.
  have hfin (w : ↥(ball (0 : ℂ) 1 \ {0})) :
      ((κInf ∘ puncturedNeighborhoodInf.restrictPreimage p) ⁻¹' {w}).Finite := by
    have := finite_fiber_of_finite_fiber hp (Finite.of_equiv _ ν.symm)
      ((κInf).symm w : ThricePuncturedSphere)
    refine (Set.toFinite (p ⁻¹' {((κInf).symm w : ThricePuncturedSphere)})).preimage
      Subtype.val_injective.injOn |>.subset fun y hy ↦ ?_
    rw [mem_preimage, mem_singleton_iff, comp_apply, ← Homeomorph.eq_symm_apply] at hy
    exact congrArg Subtype.val hy
  rw [hq.exists_homeomorph_connectedComponent_puncturedDiscPow_comp_eq_iff hfin _ he
    (κInf infBasePt), ← hp.ncard_connectedComponent_inter_fiber_σinf ν i]
  simp only [comp_apply, (κInf).injective.eq_iff, Subtype.ext_iff, restrictPreimage_coe]

end TauCeti
