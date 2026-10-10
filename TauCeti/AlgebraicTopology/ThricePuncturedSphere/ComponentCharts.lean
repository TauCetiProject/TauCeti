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
# The power-map charts of the components over the punctures

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over the basepoint `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`, with monodromy triple `(σ0, σ1, σinf)`. For each puncture
`q ∈ {0, 1, ∞}` the connected components of the preimage `p ⁻¹' D_q*` of the standard punctured
neighborhood

* `D₀* = {z | ‖z‖ < 1/2}`, `D₁* = {z | ‖z - 1‖ < 1/2}`, `D∞* = {z | 2 < ‖z‖}`

are the cycles of `σ_q` (`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents` and its
analogues at `1` and `∞`). This file computes the degree of each of them, and with it the local
model of the cover over `D_q*`:

* the component of the cycle of the sheet `i` has as many points over the local basepoint
  (`zeroBasePt`, `oneBasePt`, `pPlus`) as the cycle of `i` under `σ_q` has elements, namely
  `Function.minimalPeriod σ_q i`;
* in the coordinates `z ↦ 2 * z`, `z ↦ 2 * (1 - z)` and `z ↦ 2 / z`, which identify `D₀*`, `D₁*`
  and `D∞*` with the punctured unit disc `𝔻*`, the restriction of `p` to that component is
  isomorphic over `𝔻*` to the power map `w ↦ w ^ e` exactly when `e` is the length of the cycle
  of `i`.

These isomorphisms are the charts along which the puncture of each component is filled in when
the cover is compactified to a branched cover of the Riemann sphere: the added point is `w = 0`,
and the compactified cover is `w ↦ w ^ e` near it, with `e` the length of the cycle. Each chart is
unique only up to a rotation by an `e`-th root of unity
(`TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`).

The three punctures share one argument: the lifts of the path `α_q` from `1/2` into `D_q*` number
the points of the fibre over the local basepoint, and two of them lie in one component exactly
when their sheets lie in one cycle of `σ_q`
(`IsCoveringMap.sameCycle_monodromyTriple_σ0_iff_joinedIn` and its analogues).

## Main declarations

* `IsCoveringMap.ncard_connectedComponent_inter_fiber_σ0`,
  `IsCoveringMap.ncard_connectedComponent_inter_fiber_σ1`,
  `IsCoveringMap.ncard_connectedComponent_inter_fiber_σinf`: the component of the cycle of `i`
  has `Function.minimalPeriod σ_q i` points over the local basepoint.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ0`,
  `IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ1`,
  `IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σinf`: the restriction of
  `p` to that component is, in the coordinate of `D_q*`, isomorphic to `w ↦ w ^ e` exactly when
  `e = Function.minimalPeriod σ_q i`.

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

/-! ### Degrees and charts from the cycles of a local monodromy -/

section Local

variable {S : Set ThricePuncturedSphere} {y : ThricePuncturedSphere} {α : Path basePt y}
  {σ : Perm (Fin n)}

include hp in
/-- If two sheets lie in the same cycle of `σ` exactly when the endpoints of their lifts of `α` are
joined inside `p ⁻¹' S`, then the component of `p ⁻¹' S` containing the endpoint of the lift from
the sheet `i` has `Function.minimalPeriod σ i` points over `y`: the endpoints of the lifts of `α`
starting at the sheets of the cycle of `i`. -/
private theorem ncard_connectedComponent_inter_fiber (hS : IsOpen S)
    (hmem : ∀ e : p ⁻¹' {basePt}, (hp.monodromy (.mk α) e : E) ∈ p ⁻¹' S)
    (hjoin : ∀ j k : Fin n, σ.SameCycle j k ↔
      JoinedIn (p ⁻¹' S) (hp.monodromy (.mk α) (ν.symm j) : E) (hp.monodromy (.mk α) (ν.symm k)))
    (i : Fin n) :
    {z ∈ connectedComponent (⟨hp.monodromy (.mk α) (ν.symm i), hmem _⟩ : p ⁻¹' S) |
      p z = y}.ncard = minimalPeriod σ i := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (p ⁻¹' S) :=
    (hS.preimage hp.continuous).locallyPathConnectedSpace
  -- The point over `y` of the sheet `j`.
  let x : Fin n → p ⁻¹' S := fun j ↦ ⟨hp.monodromy (.mk α) (ν.symm j), hmem _⟩
  have hx : Injective x := fun j k hjk ↦ by
    have h : ((hp.monodromy (.mk α) (ν.symm j) : p ⁻¹' {y}) : E) =
        hp.monodromy (.mk α) (ν.symm k) :=
      congrArg (fun z : p ⁻¹' S ↦ (z : E)) hjk
    rw [← coveringFiberEquiv_apply, ← coveringFiberEquiv_apply, ← Subtype.ext_iff,
      EmbeddingLike.apply_eq_iff_eq, EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  -- Two of these points lie in one component exactly when their sheets lie in one cycle.
  have hjoin' (j : Fin n) : x j ∈ connectedComponent (x i) ↔ σ.SameCycle i j := by
    rw [← pathComponent_eq_connectedComponent, mem_pathComponent_iff, hjoin,
      joinedIn_iff_joined (x i).2 (x j).2]
  have hset : {z ∈ connectedComponent (x i) | p z = y} = x '' {j | σ.SameCycle i j} := by
    ext z
    constructor
    · rintro ⟨hzC, hz⟩
      -- Every point over `y` is the endpoint of the lift of `α` from some sheet.
      let j := ν ((coveringFiberEquiv hp (.mk α)).symm ⟨z, hz⟩)
      have hxj : x j = z := Subtype.ext <| by
        simp only [x, j, Equiv.symm_apply_apply, ← coveringFiberEquiv_apply,
          Equiv.apply_symm_apply]
      exact ⟨j, (hjoin' j).1 (hxj ▸ hzC), hxj⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(hjoin' j).2 hj, (hp.monodromy (.mk α) (ν.symm j)).2⟩
  rw [hset, ncard_image_of_injective _ hx, ncard_setOf_sameCycle]

include hp in
/-- Under the hypotheses of `ncard_connectedComponent_inter_fiber`, and in a coordinate `κ`
identifying `S` with the punctured unit disc, the restriction of `p` to the component of `p ⁻¹' S`
containing the endpoint of the lift from the sheet `i` is isomorphic over `𝔻*` to `w ↦ w ^ e`
exactly when `e` is the length of the cycle of `i` under `σ`. -/
private theorem exists_homeomorph_puncturedDiscPow_iff_minimalPeriod (hy : y ∈ S) (hS : IsOpen S)
    (hmem : ∀ e : p ⁻¹' {basePt}, (hp.monodromy (.mk α) e : E) ∈ p ⁻¹' S)
    (hjoin : ∀ j k : Fin n, σ.SameCycle j k ↔
      JoinedIn (p ⁻¹' S) (hp.monodromy (.mk α) (ν.symm j) : E) (hp.monodromy (.mk α) (ν.symm k)))
    (κ : S ≃ₜ ↥(ball (0 : ℂ) 1 \ {0})) (i : Fin n) {e : ℕ} (he : e ≠ 0) :
    (∃ h : connectedComponent (⟨hp.monodromy (.mk α) (ν.symm i), hmem _⟩ : p ⁻¹' S) ≃ₜ
          ↥(ball (0 : ℂ) 1 \ {0}),
        puncturedDiscPow he ∘ h =
          (connectedComponent (⟨hp.monodromy (.mk α) (ν.symm i), hmem _⟩ : p ⁻¹' S)).domRestrict
            (κ ∘ S.restrictPreimage p)) ↔
      minimalPeriod σ i = e := by
  have hq := (hp.restrictPreimage S).homeomorph_comp κ
  -- The fibres of `p` are finite, being in bijection with the numbered fibre over `basePt`.
  have hfin (w : ↥(ball (0 : ℂ) 1 \ {0})) :
      ((κ ∘ S.restrictPreimage p) ⁻¹' {w}).Finite := by
    have := finite_fiber_of_finite_fiber hp (Finite.of_equiv _ ν.symm)
      (κ.symm w : ThricePuncturedSphere)
    refine (Set.toFinite (p ⁻¹' {(κ.symm w : ThricePuncturedSphere)})).preimage
      Subtype.val_injective.injOn |>.subset fun z hz ↦ ?_
    rw [mem_preimage, mem_singleton_iff, comp_apply, ← Homeomorph.eq_symm_apply] at hz
    exact congrArg Subtype.val hz
  rw [hq.exists_homeomorph_connectedComponent_puncturedDiscPow_comp_eq_iff hfin _ he
    (κ ⟨y, hy⟩), ← ncard_connectedComponent_inter_fiber hp ν hS hmem hjoin i]
  simp only [comp_apply, κ.injective.eq_iff, Subtype.ext_iff, restrictPreimage_coe]

end Local

/-! ### The puncture `0` -/

/-- **The degree of a component over `0` is the length of its cycle.** The connected component of
`p ⁻¹' D₀*` that corresponds to the cycle of the sheet `i` under
`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents` contains exactly
`Function.minimalPeriod σ0 i` points over `zeroBasePt = 1/4`. -/
theorem _root_.IsCoveringMap.ncard_connectedComponent_inter_fiber_σ0 (i : Fin n) :
    {y ∈ connectedComponent (⟨hp.monodromy (.mk αZero) (ν.symm i),
        hp.monodromy_αZero_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodZero) |
          p y = zeroBasePt}.ncard =
      minimalPeriod (hp.monodromyTriple ν).σ0 i :=
  ncard_connectedComponent_inter_fiber hp ν isOpen_puncturedNeighborhoodZero
    hp.monodromy_αZero_mem_preimage (hp.sameCycle_monodromyTriple_σ0_iff_joinedIn ν) i

/-- The coordinate `z ↦ 2 * z` of the punctured neighborhood of `0`, valued in the punctured unit
disc. -/
local notation "κZero" =>
  puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf.trans
    puncturedDiscOneHalfHomeomorphPuncturedDisc

/-- **The components over `0` are power maps.** In the coordinate `z ↦ 2 * z`, which identifies
the punctured neighborhood `D₀*` of `0` with the punctured unit disc `𝔻*`, the restriction of `p`
to the component of `p ⁻¹' D₀*` corresponding to the cycle of the sheet `i` is isomorphic over
`𝔻*` to the power map `w ↦ w ^ e`, for `e ≠ 0`, exactly when `e` is the length
`Function.minimalPeriod σ0 i` of that cycle. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ0
    (i : Fin n) {e : ℕ} (he : e ≠ 0) :
    (∃ h : connectedComponent (⟨hp.monodromy (.mk αZero) (ν.symm i),
          hp.monodromy_αZero_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodZero) ≃ₜ
            ↥(ball (0 : ℂ) 1 \ {0}),
        puncturedDiscPow he ∘ h =
          (connectedComponent (⟨hp.monodromy (.mk αZero) (ν.symm i),
            hp.monodromy_αZero_mem_preimage (ν.symm i)⟩ :
              p ⁻¹' puncturedNeighborhoodZero)).domRestrict
                (κZero ∘ puncturedNeighborhoodZero.restrictPreimage p)) ↔
      minimalPeriod (hp.monodromyTriple ν).σ0 i = e :=
  exists_homeomorph_puncturedDiscPow_iff_minimalPeriod hp ν zeroBasePt.2
    isOpen_puncturedNeighborhoodZero hp.monodromy_αZero_mem_preimage
    (hp.sameCycle_monodromyTriple_σ0_iff_joinedIn ν) κZero i he

/-! ### The puncture `1` -/

/-- **The degree of a component over `1` is the length of its cycle.** The connected component of
`p ⁻¹' D₁*` that corresponds to the cycle of the sheet `i` under
`IsCoveringMap.sameCycleQuotientσ1EquivConnectedComponents` contains exactly
`Function.minimalPeriod σ1 i` points over `oneBasePt = 3/4`. -/
theorem _root_.IsCoveringMap.ncard_connectedComponent_inter_fiber_σ1 (i : Fin n) :
    {y ∈ connectedComponent (⟨hp.monodromy (.mk αOne) (ν.symm i),
        hp.monodromy_αOne_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodOne) |
          p y = oneBasePt}.ncard =
      minimalPeriod (hp.monodromyTriple ν).σ1 i :=
  ncard_connectedComponent_inter_fiber hp ν isOpen_puncturedNeighborhoodOne
    hp.monodromy_αOne_mem_preimage (hp.sameCycle_monodromyTriple_σ1_iff_joinedIn ν) i

/-- The coordinate `z ↦ 2 * (1 - z)` of the punctured neighborhood of `1`, valued in the punctured
unit disc. -/
local notation "κOne" =>
  puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.trans
    puncturedDiscOneHalfHomeomorphPuncturedDisc

/-- **The components over `1` are power maps.** In the coordinate `z ↦ 2 * (1 - z)`, which
identifies the punctured neighborhood `D₁*` of `1` with the punctured unit disc `𝔻*`, the
restriction of `p` to the component of `p ⁻¹' D₁*` corresponding to the cycle of the sheet `i` is
isomorphic over `𝔻*` to the power map `w ↦ w ^ e`, for `e ≠ 0`, exactly when `e` is the length
`Function.minimalPeriod σ1 i` of that cycle. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ1
    (i : Fin n) {e : ℕ} (he : e ≠ 0) :
    (∃ h : connectedComponent (⟨hp.monodromy (.mk αOne) (ν.symm i),
          hp.monodromy_αOne_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodOne) ≃ₜ
            ↥(ball (0 : ℂ) 1 \ {0}),
        puncturedDiscPow he ∘ h =
          (connectedComponent (⟨hp.monodromy (.mk αOne) (ν.symm i),
            hp.monodromy_αOne_mem_preimage (ν.symm i)⟩ :
              p ⁻¹' puncturedNeighborhoodOne)).domRestrict
                (κOne ∘ puncturedNeighborhoodOne.restrictPreimage p)) ↔
      minimalPeriod (hp.monodromyTriple ν).σ1 i = e :=
  exists_homeomorph_puncturedDiscPow_iff_minimalPeriod hp ν oneBasePt.2
    isOpen_puncturedNeighborhoodOne hp.monodromy_αOne_mem_preimage
    (hp.sameCycle_monodromyTriple_σ1_iff_joinedIn ν) κOne i he

/-! ### The puncture `∞` -/

/-- **The degree of a component over infinity is the length of its cycle.** The connected
component of `p ⁻¹' D∞*` that corresponds to the cycle of the sheet `i` under
`IsCoveringMap.sameCycleQuotientσinfEquivConnectedComponents` contains exactly
`Function.minimalPeriod σinf i` points over `pPlus`: the endpoints of the lifts of `αPlus`
starting at the sheets of that cycle. -/
theorem _root_.IsCoveringMap.ncard_connectedComponent_inter_fiber_σinf (i : Fin n) :
    {y ∈ connectedComponent (⟨hp.monodromy (.mk αPlus) (ν.symm i),
        hp.monodromy_αPlus_mem_preimage (ν.symm i)⟩ : p ⁻¹' puncturedNeighborhoodInf) |
          p y = pPlus}.ncard =
      minimalPeriod (hp.monodromyTriple ν).σinf i :=
  ncard_connectedComponent_inter_fiber hp ν isOpen_puncturedNeighborhoodInf
    hp.monodromy_αPlus_mem_preimage (hp.sameCycle_monodromyTriple_σinf_iff_joinedIn ν) i

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
      minimalPeriod (hp.monodromyTriple ν).σinf i = e :=
  exists_homeomorph_puncturedDiscPow_iff_minimalPeriod hp ν infBasePt.2
    isOpen_puncturedNeighborhoodInf hp.monodromy_αPlus_mem_preimage
    (hp.sameCycle_monodromyTriple_σinf_iff_joinedIn ν) κInf i he

end TauCeti
