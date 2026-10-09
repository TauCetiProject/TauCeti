/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Cyclic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.GroupTheory.GroupAction.Transitive
import TauCeti.GroupTheory.Perm.PermCongr
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.RingTheory.RootsOfUnity.PowFiber
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The finite connected covers of the punctured disc

Let `𝔻* = ball 0 1 \ {0}` be the punctured unit disc in `ℂ`. For `e ≠ 0` the power map
`z ↦ z ^ e` sends `𝔻*` onto itself, and it is a covering map with `e` sheets: the fibre over `w`
is the set of `e`-th roots of `w`. This is the local model of a branched cover near a point of
ramification index `e`.

Conversely, every connected cover of `𝔻*` with `e ≠ 0` sheets is isomorphic over `𝔻*` to this
model. The fundamental group of `𝔻*` is infinite cyclic, so a connected cover of `𝔻*` is
determined up to isomorphism by its number of sheets
(`IsCoveringMap.exists_homeomorph_comp_eq_of_card_fiber_eq`). The isomorphism can moreover be
chosen to carry any given point over `w` to any given `e`-th root of `w`; it is therefore not
unique, but only unique up to the rotations of `𝔻*` by `e`-th roots of unity.

## Main declarations

* `TauCeti.pow_mem_ball_zero_one_diff_singleton_iff`: for `e ≠ 0`, `z ^ e` lies in the punctured
  unit ball exactly when `z` does.
* `TauCeti.puncturedDiscPow`: the map `z ↦ z ^ e` from `𝔻*` to itself, for `e ≠ 0`.
* `TauCeti.puncturedDiscPow_mul`: the power maps compose, `z ^ (e * f) = (z ^ f) ^ e`.
* `TauCeti.isCoveringMap_puncturedDiscPow`: it is a covering map.
* `TauCeti.isQuotientCoveringMap_puncturedDiscPow`: it is the quotient covering by the rotations
  through the `e`-th roots of unity.
* `TauCeti.card_puncturedDiscPow_preimage_singleton`: each of its fibres has `e` points.
* `TauCeti.puncturedDiscCircle`: the canonical counterclockwise generator based at `1/2`.
* `TauCeti.isCycleOn_monodromyPerm_puncturedDiscCircle`: monodromy of the power map around this
  generator is one cycle on its `e`-element fibre.
* `TauCeti.puncturedDiscPowDeckMulEquiv`: **its deck group is the group of `e`-th roots of
  unity**, acting by rotations.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq`: **a connected cover of `𝔻*`
  with `e ≠ 0` sheets is isomorphic over `𝔻*` to `z ↦ z ^ e`**, by an isomorphism matching any
  given points of the two fibres over a point.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq_iff`: a connected cover of `𝔻*` is
  isomorphic over `𝔻*` to `z ↦ z ^ e` exactly when it has `e` sheets.
* `TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`: any two such isomorphisms differ by
  rotation through a unique `e`-th root of unity.
* `IsCoveringMap.existsUnique_homeomorph_puncturedDiscPow_comp_eq`: prescribing the image of
  one point makes the isomorphism with the power-map model unique.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §5, Theorem 5.10 (a finite cover of the punctured disc with `k` sheets is `z ↦ z ^ k`).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the classification of
  covering spaces).
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

variable {e : ℕ}

private theorem puncturedDiscRadius_pos : (0 : ℝ) < 1 / 2 := by
  norm_num

private theorem puncturedDiscSphere_subset : sphere (0 : ℂ) (1 / 2) ⊆ ball 0 1 :=
  sphere_subset_ball (by norm_num)

private theorem puncturedDiscStarConvex : StarConvex ℝ (0 : ℂ) (ball 0 1) :=
  (convex_ball (0 : ℂ) 1).starConvex (mem_ball_self one_pos)

/-- The basepoint `1/2` in the punctured unit disc. -/
noncomputable def puncturedDiscBasepoint : ↥(ball (0 : ℂ) 1 \ {0}) :=
  puncturedDiscStarConvex.sphereHomotopyEquiv puncturedDiscRadius_pos
    puncturedDiscSphere_subset ((sphereCircleHomeomorph 0 puncturedDiscRadius_pos).symm 1)

/-- The punctured-disc basepoint is the positive real point `1/2`. -/
@[simp]
theorem coe_puncturedDiscBasepoint : (puncturedDiscBasepoint : ℂ) = 1 / 2 := by
  rw [puncturedDiscBasepoint, StarConvex.coe_sphereHomotopyEquiv_apply,
    coe_sphereCircleHomeomorph_symm_apply]
  norm_num

/-- The counterclockwise circle of radius `1/2` about zero, regarded as a loop in the punctured
unit disc based at `puncturedDiscBasepoint`. -/
noncomputable def puncturedDiscCircle : Path puncturedDiscBasepoint puncturedDiscBasepoint :=
  (Complex.sphereLoop 0 puncturedDiscRadius_pos).map
    (puncturedDiscStarConvex.sphereHomotopyEquiv puncturedDiscRadius_pos
      puncturedDiscSphere_subset).toFun.continuous

/-- The punctured-disc circle is the usual positive parametrization
`t ↦ (1/2) * exp (2πit)`. -/
@[simp]
theorem coe_puncturedDiscCircle_apply (t : unitInterval) :
    (puncturedDiscCircle t : ℂ) = circleMap 0 (1 / 2) (2 * Real.pi * t) := by
  -- `puncturedDiscCircle` is by definition this mapped loop; `rw [puncturedDiscCircle]` is not
  -- usable, since the endpoints of the mapped loop only agree with `puncturedDiscBasepoint` up to
  -- unfolding, so we evaluate the mapped loop with `Path.map_coe` and let `refine` unfold it.
  have hmap := congrFun (Path.map_coe (Complex.sphereLoop 0 puncturedDiscRadius_pos)
    (puncturedDiscStarConvex.sphereHomotopyEquiv puncturedDiscRadius_pos
      puncturedDiscSphere_subset).toFun.continuous) t
  refine (congrArg Subtype.val hmap).trans ?_
  rw [Function.comp_apply, StarConvex.coe_sphereHomotopyEquiv_apply,
    Complex.coe_sphereLoop_apply]

/-- The counterclockwise circle generates the fundamental group of the punctured disc. -/
theorem zpowers_puncturedDiscCircle_eq_top :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk puncturedDiscCircle)) = ⊤ := by
  let x : sphere (0 : ℂ) (1 / 2) :=
    (sphereCircleHomeomorph 0 puncturedDiscRadius_pos).symm 1
  let W := puncturedDiscStarConvex.fundamentalGroupMulEquivInt puncturedDiscRadius_pos
    puncturedDiscSphere_subset x
  apply W.zpowers_eq_top_of_apply_eq_ofAdd_one
  simpa only [W, puncturedDiscBasepoint, puncturedDiscCircle, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.mk_map] using
    puncturedDiscStarConvex.fundamentalGroupMulEquivInt_sphereLoop puncturedDiscRadius_pos
      puncturedDiscSphere_subset

/-- The scalar action of the `e`-th roots of unity on the punctured disc is rotation. -/
noncomputable instance puncturedDiscSMul [NeZero e] :
    SMul (rootsOfUnity e ℂ) ↥(ball (0 : ℂ) 1 \ {0}) where
  smul ζ z := ⟨ζ • (z : ℂ), by
    rcases z.2 with ⟨hz, hz0⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz ⊢
      rwa [rootsOfUnity.smul_eq_mul, norm_mul,
        Complex.norm_eq_one_of_mem_rootsOfUnity ζ.2, one_mul]
    · rw [mem_singleton_iff, rootsOfUnity.smul_eq_mul]
      exact mul_ne_zero (ζ : ℂˣ).ne_zero hz0⟩

/-- The action of the `e`-th roots of unity on the punctured disc is rotation. -/
noncomputable instance puncturedDiscMulAction [NeZero e] :
    MulAction (rootsOfUnity e ℂ) ↥(ball (0 : ℂ) 1 \ {0}) where
  one_smul z := Subtype.ext (one_smul _ (z : ℂ))
  mul_smul ζ η z := Subtype.ext (mul_smul ζ η (z : ℂ))

@[simp]
theorem coe_rootsOfUnity_smul_puncturedDisc [NeZero e] (ζ : rootsOfUnity e ℂ)
    (z : ↥(ball (0 : ℂ) 1 \ {0})) :
    ((ζ • z : ↥(ball (0 : ℂ) 1 \ {0})) : ℂ) = ζ • (z : ℂ) :=
  (rfl)

/-- Rotation by a root of unity is continuous on the punctured disc. -/
noncomputable instance puncturedDiscContinuousConstSMul [NeZero e] :
    ContinuousConstSMul (rootsOfUnity e ℂ) ↥(ball (0 : ℂ) 1 \ {0}) where
  continuous_const_smul ζ :=
    Continuous.subtype_mk ((continuous_const_smul ζ).comp continuous_subtype_val) _

/-- Rotation by a root of unity acts cancellatively on the punctured disc. -/
noncomputable instance puncturedDiscIsCancelSMul [NeZero e] :
    IsCancelSMul (rootsOfUnity e ℂ) ↥(ball (0 : ℂ) 1 \ {0}) where
  right_cancel' ζ η z h := by
    apply Subtype.ext
    apply Units.ext
    exact mul_right_cancel₀ z.2.2 <| by
      simpa only [coe_rootsOfUnity_smul_puncturedDisc, rootsOfUnity.smul_eq_mul] using
        congrArg Subtype.val h

/-- For `e ≠ 0`, `z ^ e` lies in the punctured unit ball exactly when `z` does. -/
theorem pow_mem_ball_zero_one_diff_singleton_iff {𝕜 : Type*} [NormedDivisionRing 𝕜] (he : e ≠ 0)
    {z : 𝕜} : z ^ e ∈ ball (0 : 𝕜) 1 \ {0} ↔ z ∈ ball (0 : 𝕜) 1 \ {0} := by
  simp [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg z) he, he]

/-- The **power map** `z ↦ z ^ e` from the punctured unit disc `ball 0 1 \ {0}` to itself, for
`e ≠ 0`. -/
def puncturedDiscPow (he : e ≠ 0) : C(↥(ball (0 : ℂ) 1 \ {0}), ↥(ball (0 : ℂ) 1 \ {0})) where
  toFun z := ⟨(z : ℂ) ^ e, (pow_mem_ball_zero_one_diff_singleton_iff he).2 z.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_puncturedDiscPow_apply (he : e ≠ 0) (z : ↥(ball (0 : ℂ) 1 \ {0})) :
    (puncturedDiscPow he z : ℂ) = (z : ℂ) ^ e :=
  (rfl)

/-- The first power map of the punctured disc is the identity. -/
@[simp]
theorem puncturedDiscPow_one : puncturedDiscPow one_ne_zero = ContinuousMap.id _ := by
  ext
  simp

/-- The power maps of the punctured disc compose: `z ↦ z ^ (e * f)` is `z ↦ z ^ e` after
`z ↦ z ^ f`. -/
theorem puncturedDiscPow_mul {f : ℕ} (he : e ≠ 0) (hf : f ≠ 0) :
    puncturedDiscPow (mul_ne_zero he hf) = (puncturedDiscPow he).comp (puncturedDiscPow hf) := by
  ext
  simp [pow_mul']

/-- **The power map of the punctured disc is a covering map.** It is the restriction of the
covering map `z ↦ z ^ e` of `ℂ \ {0}` to the preimage of the punctured disc, which is the punctured
disc itself. -/
theorem isCoveringMap_puncturedDiscPow (he : e ≠ 0) : IsCoveringMap (puncturedDiscPow he) := by
  have hs : (· ^ e) ⁻¹' (ball (0 : ℂ) 1 \ {0}) = ball (0 : ℂ) 1 \ {0} :=
    Set.ext fun _ => pow_mem_ball_zero_one_diff_singleton_iff he
  -- `Homeomorph.setCongr` does not move the point and `Set.restrictPreimage_mk` applies the power
  -- map, so the composite below is `puncturedDiscPow he` by definition.
  exact (((isCoveringMapOn_npow (𝕜 := ℂ) e (Nat.cast_ne_zero.2 he)).mono
    fun _ hz => hz.2).isCoveringMap_restrictPreimage).comp_homeomorph (.setCongr hs.symm)

/-- **Monodromy of the power map around the puncture is one cycle.** For the positive generator
`puncturedDiscCircle` of the fundamental group, monodromy acts transitively by the powers of a
single permutation on the entire fibre over `puncturedDiscBasepoint`. -/
theorem isCycleOn_monodromyPerm_puncturedDiscCircle (he : e ≠ 0) :
    ((isCoveringMap_puncturedDiscPow he).monodromyPerm puncturedDiscBasepoint
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk puncturedDiscCircle))).IsCycleOn
        Set.univ := by
  let hp := isCoveringMap_puncturedDiscPow he
  let _ := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  have htransitive : MulAction.IsPretransitive
      (hp.monodromyPerm puncturedDiscBasepoint).range
      (puncturedDiscPow he ⁻¹' {puncturedDiscBasepoint}) := by
    rw [← hp.toPermHom_eq_monodromyPerm puncturedDiscBasepoint,
      MulAction.isPretransitive_range_toPermHom_iff]
    exact hp.monodromy_isPretransitive puncturedDiscBasepoint
  exact (hp.monodromyPerm puncturedDiscBasepoint).isCycleOn_apply_of_zpowers_eq_top
    htransitive zpowers_puncturedDiscCircle_eq_top

/-- **The power map is the quotient covering by rotations through the `e`-th roots of unity.**
Its fibres are exactly the rotation orbits. -/
theorem isQuotientCoveringMap_puncturedDiscPow [NeZero e] :
    IsQuotientCoveringMap (puncturedDiscPow (NeZero.ne e)) (rootsOfUnity e ℂ) := by
  let he := NeZero.ne e
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨isCoveringMap_puncturedDiscPow he, ?_, inferInstance, inferInstance, ?_⟩
  · intro w
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) (Nat.pos_of_ne_zero he)
    have hzmem : z ∈ ball (0 : ℂ) 1 \ {0} :=
      (pow_mem_ball_zero_one_diff_singleton_iff he).1 (hz ▸ w.2)
    exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩
  · intro z w
    rw [MulAction.mem_orbit_iff]
    constructor
    · intro h
      obtain ⟨ζ, hζ⟩ := (pow_eq_pow_iff_exists_rootsOfUnity_smul he).mp
        (congrArg Subtype.val h).symm
      exact ⟨ζ, Subtype.ext hζ⟩
    · rintro ⟨ζ, hζ⟩
      apply Subtype.ext
      exact (congrArg (fun u : ℂ ↦ u ^ e) (congrArg Subtype.val hζ)).symm.trans
        (rootsOfUnity.smul_pow ζ (w : ℂ))

/-- **The deck group of the punctured-disc power map is the group of `e`-th roots of unity.**
Under this isomorphism a root of unity acts by rotation
(`puncturedDiscPowDeckMulEquiv_apply`). -/
noncomputable def puncturedDiscPowDeckMulEquiv (he : e ≠ 0) :
    rootsOfUnity e ℂ ≃* deck (puncturedDiscPow he) :=
  letI : NeZero e := ⟨he⟩
  letI := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  have : Nonempty ↥(ball (0 : ℂ) 1 \ {0}) :=
    ⟨⟨(1 / 2 : ℂ), by norm_num [mem_ball_zero_iff]⟩⟩
  Deck.IsQuotientCoveringMap.deckMulEquiv
    (isQuotientCoveringMap_puncturedDiscPow (e := e))

/-- A root of unity acts through `puncturedDiscPowDeckMulEquiv` by multiplying points of the
punctured disc. -/
@[simp]
theorem puncturedDiscPowDeckMulEquiv_apply (he : e ≠ 0) (ζ : rootsOfUnity e ℂ)
    (z : ↥(ball (0 : ℂ) 1 \ {0})) :
    ((puncturedDiscPowDeckMulEquiv he ζ).1 z : ℂ) = ζ • (z : ℂ) := by
  let _ : NeZero e := ⟨he⟩
  rw [puncturedDiscPowDeckMulEquiv,
    Deck.IsQuotientCoveringMap.deckMulEquiv_apply,
    coe_rootsOfUnity_smul_puncturedDisc]

/-- Every deck transformation of the punctured-disc power map is rotation by the corresponding
root of unity under `puncturedDiscPowDeckMulEquiv`. -/
@[simp]
theorem puncturedDiscPowDeckMulEquiv_symm_apply (he : e ≠ 0)
    (φ : deck (puncturedDiscPow he)) (z : ↥(ball (0 : ℂ) 1 \ {0})) :
    (((puncturedDiscPowDeckMulEquiv he).symm φ : ℂˣ) : ℂ) * (z : ℂ) = (φ.1 z : ℂ) := by
  let _ : NeZero e := ⟨he⟩
  simpa only [puncturedDiscPowDeckMulEquiv_apply, rootsOfUnity.smul_eq_mul] using
    congrArg (fun ψ : deck (puncturedDiscPow he) => (ψ.1 z : ℂ))
      ((puncturedDiscPowDeckMulEquiv he).apply_symm_apply φ)

/-- The deck group of `z ↦ z ^ e` has order `e`. -/
theorem card_deck_puncturedDiscPow (he : e ≠ 0) :
    Nat.card (deck (puncturedDiscPow he)) = e := by
  rw [← Nat.card_congr (puncturedDiscPowDeckMulEquiv he).toEquiv]
  let _ : NeZero e := ⟨he⟩
  exact Complex.card_rootsOfUnity e

/-- **The power map of the punctured disc has `e` sheets:** the fibre over any point `w` consists
of the `e` distinct `e`-th roots of `w`. -/
theorem card_puncturedDiscPow_preimage_singleton (he : e ≠ 0) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    Nat.card (puncturedDiscPow he ⁻¹' {w}) = e := by
  classical
  have hζ := Complex.isPrimitiveRoot_exp e he
  have himage : Subtype.val '' (puncturedDiscPow he ⁻¹' {w}) =
      (Polynomial.nthRootsFinset e (w : ℂ) : Set ℂ) := by
    ext z
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero he)]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← coe_puncturedDiscPow_apply he, Set.mem_singleton_iff.1 hz]
    · intro hz
      refine ⟨⟨z, (pow_mem_ball_zero_one_diff_singleton_iff he).1 (hz ▸ w.2)⟩, ?_, rfl⟩
      exact Set.mem_singleton_iff.2 (Subtype.ext hz)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) (Nat.pos_of_ne_zero he)
  rw [← Nat.card_image_of_injective Subtype.val_injective, himage, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, hζ.card_nthRootsFinset_of_pow_eq hα w.2.2]

variable {E : Type*} [TopologicalSpace E] [ConnectedSpace E] {p : E → ↥(ball (0 : ℂ) 1 \ {0})}

/-- **Every finite connected cover of the punctured disc is a power map.** Let `p : E → 𝔻*` be a
covering map from a connected space whose fibre over `w` has `e ≠ 0` points. Then `p` is
isomorphic over `𝔻*` to `z ↦ z ^ e`, by a homeomorphism `E ≃ₜ 𝔻*` carrying any given point `y₀`
over `w` to any given `e`-th root `z₀` of `w`. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq (hp : IsCoveringMap p)
    (he : e ≠ 0) {w : ↥(ball (0 : ℂ) 1 \ {0})} (hcard : Nat.card (p ⁻¹' {w}) = e)
    (y₀ : p ⁻¹' {w}) (z₀ : puncturedDiscPow he ⁻¹' {w}) :
    ∃ h : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}), h y₀ = z₀ ∧ puncturedDiscPow he ∘ h = p := by
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  have : LocallyPathConnectedSpace ↥(ball (0 : ℂ) 1 \ {0}) :=
    (isOpen_ball.sdiff isClosed_singleton).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace E := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have := ((convex_ball (0 : ℂ) 1).starConvex (mem_ball_self one_pos)
    ).isCyclic_fundamentalGroup_diff_singleton (r := 1 / 2) (by norm_num)
    (sphere_subset_ball (by norm_num)) w
  exact hp.exists_homeomorph_comp_eq_of_card_fiber_eq (isCoveringMap_puncturedDiscPow he) y₀ z₀
    (by rw [hcard, card_puncturedDiscPow_preimage_singleton])

/-- **The finite connected covers of the punctured disc are classified by their degree.** A
covering map `p : E → 𝔻*` from a connected space is isomorphic over `𝔻*` to `z ↦ z ^ e`, for
`e ≠ 0`, exactly when its fibre over some (equivalently, every) point `w` has `e` points. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq_iff (hp : IsCoveringMap p)
    (he : e ≠ 0) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    (∃ h : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}), puncturedDiscPow he ∘ h = p) ↔
      Nat.card (p ⁻¹' {w}) = e := by
  refine ⟨fun ⟨h, hcomp⟩ => ?_, fun hcard => ?_⟩
  · rw [← card_puncturedDiscPow_preimage_singleton he w]
    exact Nat.card_congr <| h.toEquiv.subtypeEquiv fun y => by simp [← hcomp]
  · have : Nonempty (p ⁻¹' {w}) := (Nat.card_pos_iff.1 (hcard ▸ Nat.pos_of_ne_zero he)).1
    have : Nonempty (puncturedDiscPow he ⁻¹' {w}) := (Nat.card_pos_iff.1
      ((card_puncturedDiscPow_preimage_singleton he w).symm ▸ Nat.pos_of_ne_zero he)).1
    exact (hp.exists_homeomorph_puncturedDiscPow_comp_eq he hcard (Classical.arbitrary _)
      (Classical.arbitrary _)).imp fun _ h => h.2

omit [ConnectedSpace E] in
/-- **Two identifications of a cover with the punctured-disc power map differ by a unique
rotation.** More precisely, if `h` and `k` are homeomorphisms from the same space to the
punctured disc and both identify a map `p` with `z ↦ z ^ e`, then there is a unique `e`-th root
of unity `ζ` such that, after coercion to `ℂ`, `k y = ζ · h y` for every `y`.

No covering or connectedness hypothesis is needed: the difference `k ∘ h⁻¹` is a deck
transformation of the power map, whose deck group is the group of `e`-th roots of unity. -/
theorem existsUnique_rootsOfUnity_smul_homeomorph (he : e ≠ 0)
    (h k : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}))
    (hh : puncturedDiscPow he ∘ h = p) (hk : puncturedDiscPow he ∘ k = p) :
    ∃! ζ : rootsOfUnity e ℂ, ∀ y, (k y : ℂ) = ((ζ : ℂˣ) : ℂ) * (h y : ℂ) := by
  let _ : NeZero e := ⟨he⟩
  let φ : deck (puncturedDiscPow he) := ⟨h.symm.trans k, by
    ext z
    have hhk := congrArg Subtype.val (congr_fun hk (h.symm z))
    have hhh := congrArg Subtype.val (congr_fun hh (h.symm z))
    simpa only [Function.comp_apply, Homeomorph.trans_apply, h.apply_symm_apply] using
      hhk.trans hhh.symm⟩
  let ζ := (puncturedDiscPowDeckMulEquiv he).symm φ
  refine ⟨ζ, ?_, ?_⟩
  · intro y
    simpa only [ζ, φ, Homeomorph.trans_apply, h.symm_apply_apply] using
      (puncturedDiscPowDeckMulEquiv_symm_apply he φ (h y)).symm
  · intro η hη
    let z : ↥(ball (0 : ℂ) 1 \ {0}) := ⟨(1 / 2 : ℂ), by
      norm_num [mem_ball_zero_iff]⟩
    apply Subtype.ext
    apply Units.ext
    apply mul_right_cancel₀ z.2.2
    have hζ : (k (h.symm z) : ℂ) = ((ζ : ℂˣ) : ℂ) * (h (h.symm z) : ℂ) := by
      simpa only [ζ, φ, Homeomorph.trans_apply, h.apply_symm_apply] using
        (puncturedDiscPowDeckMulEquiv_symm_apply he φ z).symm
    simpa only [h.apply_symm_apply] using (hη (h.symm z)).symm.trans hζ

/-- **A point-rigidified finite connected cover of the punctured disc has a unique power-map
model.** Given points `y₀` and `z₀` in corresponding fibres, there is exactly one
homeomorphism over the punctured disc carrying `y₀` to `z₀`. Without the point condition,
the homeomorphism is unique only up to the rotations described by
`existsUnique_rootsOfUnity_smul_homeomorph`. -/
theorem _root_.IsCoveringMap.existsUnique_homeomorph_puncturedDiscPow_comp_eq
    (hp : IsCoveringMap p) (he : e ≠ 0) {w : ↥(ball (0 : ℂ) 1 \ {0})}
    (hcard : Nat.card (p ⁻¹' {w}) = e) (y₀ : p ⁻¹' {w})
    (z₀ : puncturedDiscPow he ⁻¹' {w}) :
    ∃! h : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}),
      h y₀ = z₀ ∧ puncturedDiscPow he ∘ h = p := by
  obtain ⟨h, hy, hcomp⟩ := hp.exists_homeomorph_puncturedDiscPow_comp_eq he hcard y₀ z₀
  refine ⟨h, ⟨hy, hcomp⟩, ?_⟩
  rintro k ⟨ky, kcomp⟩
  apply Homeomorph.ext
  exact fun x => congr_fun ((isCoveringMap_puncturedDiscPow he).eq_of_comp_eq h.continuous
    k.continuous (hcomp.trans kcomp.symm) y₀ (by rw [hy, ky])) x |>.symm

end TauCeti
