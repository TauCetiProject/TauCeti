/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Homeomorphisms glued from a closed ball and its exterior

Let `X` and `Y` be proper metric spaces, `g` a map continuous on a closed ball `closedBall c r`
of `X` and bijective from it onto a set `s ⊆ Y`, and `h` a map continuous on the closed exterior
`(ball c r)ᶜ`, bijective from the open exterior `(closedBall c r)ᶜ` onto `sᶜ`, and tending to
infinity at infinity. If `g` and `h` agree on the sphere `sphere c r`, the map that is `g` on the
closed ball and `h` outside it is a homeomorphism of `X` onto `Y`
(`TauCeti.exists_homeomorph_of_bijOn_closedBall_compl`): it is a continuous bijection and a proper
map, hence closed.
-/

public section

open Bornology Filter Function Metric Set

namespace TauCeti

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MetricSpace Y] [ProperSpace Y]

/-- **Gluing across a sphere.** A map `g` continuous on `closedBall c r` and bijective from it onto
`s`, and a map `h` continuous on `(ball c r)ᶜ`, bijective from `(closedBall c r)ᶜ` onto `sᶜ` and
tending to infinity at infinity, that agree on `sphere c r`, glue to a homeomorphism `X ≃ₜ Y`. -/
theorem exists_homeomorph_of_bijOn_closedBall_compl {g h : X → Y} {c : X} {r : ℝ} {s : Set Y}
    (hgc : ContinuousOn g (closedBall c r)) (hg : BijOn g (closedBall c r) s)
    (hhc : ContinuousOn h (ball c r)ᶜ) (hh : BijOn h (closedBall c r)ᶜ sᶜ)
    (hgh : EqOn g h (sphere c r)) (hht : Tendsto h (cobounded X) (cobounded Y)) :
    ∃ e : X ≃ₜ Y, EqOn e g (closedBall c r) ∧ EqOn e h (closedBall c r)ᶜ := by
  classical
  let H : X → Y := fun z => if dist z c ≤ r then g z else h z
  have hHc : Continuous H := by
    refine continuous_if_le (continuous_id.dist continuous_const) continuous_const
      (hgc.mono fun z hz => mem_closedBall.2 hz) (hhc.mono fun z hz => ?_) fun z hz => hgh hz
    simpa using hz
  have hHg : EqOn H g (closedBall c r) := fun z hz => by
    simp [H, mem_closedBall.1 hz]
  have hHh : EqOn H h (closedBall c r)ᶜ := fun z hz => by
    have : ¬ dist z c ≤ r := by simpa using hz
    simp [H, this]
  /- `H` is a bijection: `g` fills `s` from the closed ball, and `h` fills `sᶜ` from outside. -/
  have hbij : Bijective H := by
    have h₁ : BijOn H (closedBall c r) s := hg.congr hHg.symm
    have h₂ : BijOn H (closedBall c r)ᶜ sᶜ := hh.congr hHh.symm
    have hinj : InjOn H (closedBall c r ∪ (closedBall c r)ᶜ) := by
      rw [injOn_union disjoint_compl_right]
      exact ⟨h₁.injOn, h₂.injOn, fun x hx y hy hxy => h₂.mapsTo hy (hxy ▸ h₁.mapsTo hx)⟩
    have := h₁.union h₂ hinj
    rw [union_compl_self, union_compl_self] at this
    exact bijOn_univ.1 this
  /- `H` tends to infinity at infinity, so it is proper and hence closed. -/
  have hHt : Tendsto H (cocompact X) (cocompact Y) := by
    rw [← cobounded_eq_cocompact, ← cobounded_eq_cocompact]
    refine hht.congr' ?_
    filter_upwards [isBounded_def.1 isBounded_closedBall] with z hz
    exact (hHh hz).symm
  have hHom : IsHomeomorph H := isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨hHc, (isProperMap_iff_tendsto_cocompact.2 ⟨hHc, hHt⟩).isClosedMap, hbij⟩
  have hcoe : ⇑(hHom.homeomorph H) = H := by
    ext z
    simp
  refine ⟨hHom.homeomorph H, ?_, ?_⟩ <;> rw [hcoe]
  exacts [hHg, hHh]

end TauCeti
