/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Topology.Homotopy.AddCircle
import Mathlib.Analysis.Convex.PathConnected

/-!
# Slice loops in the end charts and positive end charts of the pair of pants

On each end `q` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, the positive end chart
`φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`, defined in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart`) reads the end chart `φ_q` with the sign
`q.endSign = ±1` of the end (`+1` on the input ends `0`, `1` and `-1` on the output end `∞`). At
height `s`, the slice loop `t ↦ u(φ_q(±s, t))` of a map `u` into an arbitrary topological or uniform
space differs from the positive-end slice loop `t ↦ u(φ'_q(s, t))` by the involution `t ↦ ±t`.

This file transports uniform and pointwise convergence of slice loops, `t = 0` isolation within a
class of curves, and `AddCircle 1` null-homotopy between `positiveEndChart` and `endChart` without
any manifold or Floer assumptions on the target space, supplying the topological transport steps
used for manifold Floer end breaking and convergence in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`.

## Main results

* `TauCeti.Floer.tendstoUniformly_endChart_of_positiveEndChart`,
  `TauCeti.Floer.tendsto_endChart_of_positiveEndChart`: uniform and pointwise convergence of
  positive-end slice loops `u(φ'_q(σ i, ·)) → x` transfer to `u(φ_q(±σ i, ·)) → (t ↦ x(±t))`
  (converses to `TauCeti.Floer.tendstoUniformly_comp_positiveEndChart`).
* `TauCeti.Floer.eventually_forall_eq_of_comp_endSign_mul`: isolation at `t = 0` among curves in a
  subset `B` transfers from a family `S` to any family `S'` mapped into `S` by `t ↦ q.endSign * t`.
* `TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul`,
  `TauCeti.Floer.exists_nullhomotopic_positiveEndChart_of_subset`,
  `TauCeti.Floer.exists_nullhomotopic_positiveEndChart`: reading a loop with `t ↦ ±t` preserves
  null-homotopy on `AddCircle 1`, and a null-homotopic end loop at one height `s₀ > a` yields a
  null-homotopic positive-end loop at every height `s > a`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on orientation and time-reversal conventions on input and output cylindrical
  ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4 and
  Section 8.1, on cylindrical end coordinates of punctured Riemann surfaces.
-/

public section

open Set Filter Function TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti.Floer

/-- Transfer uniform convergence of positive-end loops `u(φ'_q(σ i, ·)) → x` into uniform
convergence of the end loops `u(φ_q(±σ i, ·)) → (t ↦ x(±t))`. -/
theorem tendstoUniformly_endChart_of_positiveEndChart {ι α : Type*} [UniformSpace α]
    {u : ℝ × ℝ → α} {q : Puncture} {σ : ι → ℝ} {x : ℝ → α} {l : Filter ι}
    (h : TendstoUniformly (fun i t ↦ u (positiveEndChart q (σ i, t))) x l) :
    TendstoUniformly (fun i t ↦ u (endChart q (q.endSign * σ i, t)))
      (fun t ↦ x (q.endSign * t)) l := by
  rw [funext fun i ↦ comp_endChart_eq_comp_positiveEndChart u q (σ i)]
  exact h.comp _

/-- Transfer pointwise convergence of positive-end loops `u(φ'_q(σ i, t)) → x(t)` into pointwise
convergence of the end loops `u(φ_q(±σ i, t)) → x(±t)`. -/
theorem tendsto_endChart_of_positiveEndChart {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} {σ : ι → ℝ} {u : ℝ × ℝ → X} {q : Puncture} {x : ℝ → X}
    (h : ∀ t, Tendsto (fun i ↦ u (positiveEndChart q (σ i, t))) l (𝓝 (x t))) (t : ℝ) :
    Tendsto (fun i ↦ u (endChart q (q.endSign * σ i, t))) l (𝓝 (x (q.endSign * t))) := by
  simpa only [endChart_eq_positiveEndChart] using h (q.endSign * t)

/-- Isolation at `t = 0` among curves with values in `B` transfers from a family `S` of curves to
any family `S'` mapped into `S` by `t ↦ q.endSign * t`. -/
theorem eventually_forall_eq_of_comp_endSign_mul {X : Type*} [TopologicalSpace X]
    {q : Puncture} {S' S : Set (ℝ → X)} {B : Set X}
    (hS : ∀ ⦃x⦄, x ∈ S' → (fun t ↦ x (q.endSign * t)) ∈ S)
    (hiso : ∀ y ∈ S, (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
      ∀ y' ∈ S, (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∀ x ∈ S', (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ S', (∀ t, x' t ∈ B) → x' 0 = p → x' = x := fun x hx hxB ↦ by
  have h0 := hiso (fun t ↦ x (q.endSign * t)) (hS hx) (fun _ ↦ hxB _)
  rw [mul_zero] at h0
  refine h0.mono fun p hp x' hx' hx'B hx'0 ↦ funext fun t ↦ ?_
  have heq := congrFun (hp (fun r ↦ x' (q.endSign * r)) (hS hx') (fun _ ↦ hx'B _)
    (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using heq

/-- Reading a `1`-periodic loop with the time `±t` of an end preserves null-homotopy on
`AddCircle 1`. -/
theorem exists_nullhomotopic_comp_endSign_mul {X : Type*} [TopologicalSpace X] (q : Puncture)
    {x : ℝ → X} (hx : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x t) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = x (q.endSign * t) := by
  obtain ⟨g, hg, hgx⟩ := hx
  have h := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
  rw [abs_endSign, div_one] at h
  obtain ⟨g', hg', hg'x⟩ := h
  exact ⟨g', hg', fun t ↦ by rw [hg'x t, hgx, mul_comm]⟩

/-- If `u` is continuous on a domain `U ⊆ ℝ × ℝ` containing the positive end `s > a` of `q`, then a
null-homotopic end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > a`) yields a null-homotopic positive-end loop
`t ↦ u(φ'_q(s, t))` at every `s > a`. -/
theorem exists_nullhomotopic_positiveEndChart_of_subset {X : Type*} [TopologicalSpace X]
    {U : Set (ℝ × ℝ)} {u : ℝ × ℝ → X} (hu : ContinuousOn u U) {q : Puncture} {a : ℝ}
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) {s₀ s : ℝ} (hs₀ : a < s₀)
    (hs : a < s)
    (hnull : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s, t)) := by
  have h₀ : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s₀, t) := by
    simpa only [comp_apply, positiveEndChart_mk] using exists_nullhomotopic_comp_endSign_mul q hnull
  exact ((convex_Ioi a).isPathConnected ⟨s₀, hs₀⟩).exists_nullhomotopic_addCircle_of_periodic
    (hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn fun _ hz ↦ haU _ hz.1)
    (fun _ _ _ ↦ by simp only [comp_apply, positiveEndChart_add_one]) hs₀ h₀ hs

/-- A null-homotopic end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) of a map `u` continuous on `S` yields
a null-homotopic positive-end loop `t ↦ u(φ'_q(s, t))` at every `s > 0`. -/
theorem exists_nullhomotopic_positiveEndChart {X : Type*} [TopologicalSpace X] {u : ℝ × ℝ → X}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture} {s₀ s : ℝ} (hs₀ : 0 < s₀)
    (hs : 0 < s)
    (hnull : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s₀, t))) :
    ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (positiveEndChart q (s, t)) :=
  exists_nullhomotopic_positiveEndChart_of_subset hu
    (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal hζ) hs₀ hs hnull

end TauCeti.Floer
