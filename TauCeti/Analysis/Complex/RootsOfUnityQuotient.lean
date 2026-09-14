/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.LocalAtTarget
public import TauCeti.RingTheory.RootsOfUnity.PowFiber
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus

/-!
# The quotient of a disc by a finite rotation group

The group `rootsOfUnity m ℂ` of the `m`-th roots of unity acts on `ℂ` by rotations. This file
proves that `u ↦ u ^ m` is the orbit map of that action, topologically: for every invariant set
`s ⊆ ℂ`, the orbit space of `s` is homeomorphic to the image of `s` under `u ↦ u ^ m`. For the
open disc of radius `r` about `0` the image is the disc of radius `r ^ m`, so the quotient of a
disc by a cyclic rotation group of order `m` is again a disc, with coordinate `u ^ m`.

This is the local model of a quotient Riemann surface at a point whose stabilizer is cyclic of
order `m`: in a coordinate centred at the fixed point in which a generator acts by a primitive
`m`-th root of unity, the orbit space near the point is a disc, and the quotient map is
`u ↦ u ^ m`. For `m ≥ 2`, the only point of the disc with a nontrivial stabilizer is its centre
(`TauCeti.freeLocus_rootsOfUnity`); on the complementary free locus the orbit projection is a
covering map by `TauCeti.isCoveringMap_quotientMk_freeLocus`, and `u ↦ u ^ m` itself is a
covering map of the punctured plane with nonvanishing derivative (Mathlib's
`isCoveringMapOn_npow`). At the centre, `u ↦ u ^ m` vanishes to order exactly `m`
(Mathlib's `analyticOrderAt_centeredMonomial`).

The homeomorphism is built from Mathlib's theorem that `u ↦ u ^ m` is an open quotient map of
`ℂ` (`Complex.isOpenQuotientMap_pow`, a consequence of the open mapping theorem), restricted to
the saturated set `s`, together with the identification of its fibres with the orbits of the
roots of unity (`TauCeti.orbitRel_rootsOfUnity_apply`).

## Main declarations

* `TauCeti.SubMulAction.rootsOfUnityQuotientHomeomorph`: the orbit space of an invariant set `s` is
  homeomorphic to `(· ^ m) '' s`, sending the class of `u` to `u ^ m`.
* `TauCeti.rootsOfUnityBall`: the open disc of radius `r` about `0`, as an invariant set.
* `TauCeti.image_pow_ball`: `u ↦ u ^ m` maps the disc of radius `r` onto the disc of radius
  `r ^ m`.
* `TauCeti.rootsOfUnityBallQuotientHomeomorph`: the orbit space of the disc of radius `r` is
  homeomorphic to the disc of radius `r ^ m`.
* `TauCeti.freeLocus_rootsOfUnity`: for `m ≥ 2`, the action is free exactly off `0`.

## References

* Hershel M. Farkas and Irwin Kra, *Riemann Surfaces*, second edition, Chapter I §4.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter III §3.
-/

public section

namespace TauCeti

open MulAction Set

variable {m : ℕ} [NeZero m]

namespace SubMulAction

/-- The map from the orbit space of an invariant set to its image under `u ↦ u ^ m`. -/
def rootsOfUnityQuotientMap (s : SubMulAction (rootsOfUnity m ℂ) ℂ) :
    orbitRel.Quotient (rootsOfUnity m ℂ) s → (· ^ m) '' (s : Set ℂ) :=
  Quotient.lift (fun u ↦ ⟨(u : ℂ) ^ m, mem_image_of_mem _ u.2⟩) fun _ _ h ↦
    Subtype.ext <| ((_root_.SubMulAction.mem_orbit_subMul_iff).trans
      (orbitRel_rootsOfUnity_apply (NeZero.ne m))).mp h

@[simp]
theorem coe_rootsOfUnityQuotientMap_mk (s : SubMulAction (rootsOfUnity m ℂ) ℂ) (u : s) :
    (rootsOfUnityQuotientMap s (Quotient.mk _ u) : ℂ) = (u : ℂ) ^ m := by
  rw [rootsOfUnityQuotientMap, Quotient.lift_mk]

/-- The orbit space of a set `s ⊆ ℂ` invariant under the `m`-th roots of unity is homeomorphic to
the image of `s` under `u ↦ u ^ m`, by sending the orbit of `u` to `u ^ m`. -/
noncomputable def rootsOfUnityQuotientHomeomorph (s : SubMulAction (rootsOfUnity m ℂ) ℂ) :
    orbitRel.Quotient (rootsOfUnity m ℂ) s ≃ₜ (· ^ m) '' (s : Set ℂ) := by
  let f : s → (· ^ m) '' (s : Set ℂ) := fun u ↦ ⟨(u : ℂ) ^ m, mem_image_of_mem _ u.2⟩
  have hrel (u v : s) : orbitRel (rootsOfUnity m ℂ) s u v ↔ (u : ℂ) ^ m = (v : ℂ) ^ m :=
    _root_.SubMulAction.mem_orbit_subMul_iff.trans
      (orbitRel_rootsOfUnity_apply (NeZero.ne m))
  have hf : IsOpenMap f := by
    have hpre := (Complex.isOpenQuotientMap_pow m).isOpenMap.restrictPreimage
      ((· ^ m) '' (s : Set ℂ))
    exact hpre.comp (Homeomorph.setCongr (preimage_image_pow_eq (NeZero.ne m) s).symm).isOpenMap
  refine Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (rootsOfUnityQuotientMap s) ⟨?_, ?_⟩)
    (continuous_quot_lift _ (by fun_prop))
    (IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective hf)
  · rintro ⟨a⟩ ⟨b⟩ hab
    exact Quot.sound ((hrel a b).mpr (Subtype.ext_iff.mp hab))
  · rintro ⟨_, u, hu, rfl⟩
    exact ⟨Quotient.mk _ ⟨u, hu⟩, rfl⟩

@[simp]
theorem coe_rootsOfUnityQuotientHomeomorph_mk (s : SubMulAction (rootsOfUnity m ℂ) ℂ) (u : s) :
    (rootsOfUnityQuotientHomeomorph s (Quotient.mk _ u) : ℂ) = (u : ℂ) ^ m := by
  change (rootsOfUnityQuotientMap s (Quotient.mk _ u) : ℂ) = (u : ℂ) ^ m
  rw [coe_rootsOfUnityQuotientMap_mk]

end SubMulAction

variable (m) in
/-- The open disc of radius `r` about `0`, as a set invariant under the `m`-th roots of
unity. -/
def rootsOfUnityBall (r : ℝ) : SubMulAction (rootsOfUnity m ℂ) ℂ where
  carrier := Metric.ball 0 r
  smul_mem' ζ u hu := by
    rw [Metric.mem_ball, dist_zero_right] at hu ⊢
    rwa [Subgroup.smul_def, Units.smul_def, smul_eq_mul, norm_mul,
      Complex.norm_eq_one_of_mem_rootsOfUnity ζ.2, one_mul]

@[simp]
theorem coe_rootsOfUnityBall (r : ℝ) :
    (rootsOfUnityBall m r : Set ℂ) = Metric.ball 0 r :=
  (rfl)

@[simp]
theorem mem_rootsOfUnityBall {r : ℝ} {u : ℂ} : u ∈ rootsOfUnityBall m r ↔ ‖u‖ < r := by
  rw [← SetLike.mem_coe, coe_rootsOfUnityBall, mem_ball_zero_iff]

/-- For `0 ≤ r`, the map `u ↦ u ^ m` sends the disc of radius `r` about `0` onto the disc of
radius `r ^ m`. -/
theorem image_pow_ball {r : ℝ} (hr : 0 ≤ r) :
    (· ^ m) '' Metric.ball (0 : ℂ) r = Metric.ball 0 (r ^ m) := by
  ext w
  simp only [mem_image, Metric.mem_ball, dist_zero_right]
  have hlt {u : ℂ} : ‖u‖ ^ m < r ^ m ↔ ‖u‖ < r :=
    pow_lt_pow_iff_left₀ (norm_nonneg u) hr (NeZero.ne m)
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [norm_pow, hlt]
  · intro hw
    obtain ⟨u, rfl⟩ := (Complex.isOpenQuotientMap_pow m).surjective w
    exact ⟨u, hlt.mp (by rwa [← norm_pow]), rfl⟩

/-- For `0 ≤ r`, the orbit space of the disc of radius `r` about `0` under the `m`-th roots of
unity is homeomorphic to the disc of radius `r ^ m`, by sending the orbit of `u` to `u ^ m`. -/
noncomputable def rootsOfUnityBallQuotientHomeomorph {r : ℝ} (hr : 0 ≤ r) :
    orbitRel.Quotient (rootsOfUnity m ℂ) (rootsOfUnityBall m r) ≃ₜ Metric.ball (0 : ℂ) (r ^ m) :=
  (SubMulAction.rootsOfUnityQuotientHomeomorph (rootsOfUnityBall m r)).trans
    (Homeomorph.setCongr (image_pow_ball hr))

@[simp]
theorem coe_rootsOfUnityBallQuotientHomeomorph_mk {r : ℝ} (hr : 0 ≤ r)
    (u : rootsOfUnityBall m r) :
    (rootsOfUnityBallQuotientHomeomorph hr (Quotient.mk _ u) : ℂ) = (u : ℂ) ^ m := by
  change (SubMulAction.rootsOfUnityQuotientHomeomorph (rootsOfUnityBall m r)
    (Quotient.mk _ u) : ℂ) = (u : ℂ) ^ m
  rw [SubMulAction.coe_rootsOfUnityQuotientHomeomorph_mk]

omit [NeZero m] in
/-- For `m ≥ 2`, the `m`-th roots of unity act freely exactly on the nonzero complex numbers:
the centre `0` is the only point with a nontrivial stabilizer. -/
theorem freeLocus_rootsOfUnity (hm : 1 < m) :
    (freeLocus (rootsOfUnity m ℂ) ℂ : Set ℂ) = {0}ᶜ := by
  ext u
  simp only [SetLike.mem_coe, mem_freeLocus, mem_compl_iff, mem_singleton_iff]
  refine ⟨fun hu h ↦ ?_, stabilizer_rootsOfUnity_of_ne_zero⟩
  have : NeZero m := ⟨by omega⟩
  have : Nontrivial (rootsOfUnity m ℂ) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rwa [Complex.card_rootsOfUnity])
  rw [h, stabilizer_rootsOfUnity_zero] at hu
  exact top_ne_bot hu

end TauCeti
