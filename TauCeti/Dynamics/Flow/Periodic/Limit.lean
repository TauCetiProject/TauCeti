/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
import TauCeti.Dynamics.Flow.ClosedOrbit
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Limits of periodic orbits of a flow

Let `ϕ` be a continuous flow by `ℝ` on a space `X`, and let `xᵢ` be points with return times
`Tᵢ`, `ϕ Tᵢ xᵢ = xᵢ`, converging along a filter to `x₀` and `T₀`. This file proves the three facts
which turn such a family of periodic orbits into a periodic orbit through `x₀`:

* `x₀` returns at time `T₀`, `ϕ T₀ x₀ = x₀`, when `X` is Hausdorff
  (`Flow.apply_eq_self_of_tendsto`), since the return condition is closed;
* if the return times are positive and tend to `0`, then `x₀` is a rest point
  (`Flow.apply_eq_self_of_tendsto_zero`): each `xᵢ` returns at every integer multiple of `Tᵢ`, and
  these multiples approximate any given time;
* if `T₀ > 0` and the loops `t ↦ ϕ t xᵢ` on the circles `ℝ/Tᵢℤ` are null-homotopic, then so is the
  limit loop `t ↦ ϕ t x₀` on `ℝ/T₀ℤ`, when `X` is locally path-connected and semilocally simply
  connected (`Flow.exists_nullhomotopic_of_tendsto`), as for instance every manifold is.

For the last statement, the loops on the periodic orbits form a continuous family of based loops
indexed by the periodic points, and in a semilocally simply connected space null-homotopy of such
a family is locally constant
(`TauCeti.eventually_homotopic_refl_iff_of_semilocallySimplyConnectedOn`); the limit loop is
therefore null-homotopic as soon as a nearby loop is.

These are the compactness steps by which closed orbits of bounded period on nearby energy levels,
produced by a variational or capacity argument, give a closed orbit on the limiting level, as in
the Hofer–Zehnder–Struwe almost existence theorem.

## Main results

* `Flow.apply_eq_self_of_tendsto`: limits of periodic points are periodic, with the limit period.
* `Flow.apply_eq_self_of_tendsto_zero`: limits of periodic points with periods tending to `0` are
  rest points.
* `Flow.exists_nullhomotopic_of_tendsto`: limits of contractible periodic orbits of positive limit
  period are contractible.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
-/

public section

noncomputable section

open Filter Set Topology TauCeti
open scoped unitInterval

namespace Flow

variable {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X) {ι : Type*} {l : Filter ι}
  {x : ι → X} {T : ι → ℝ} {x₀ : X} {T₀ : ℝ}

/-- **Limits of periodic points are periodic.** If `xᵢ → x₀` and `Tᵢ → T₀` along a nontrivial
filter, and eventually `xᵢ` returns to itself at time `Tᵢ`, then `x₀` returns to itself at time
`T₀`. -/
theorem apply_eq_self_of_tendsto [T2Space X] [l.NeBot] (hx : Tendsto x l (𝓝 x₀))
    (hT : Tendsto T l (𝓝 T₀)) (hper : ∀ᶠ i in l, ϕ (T i) (x i) = x i) : ϕ T₀ x₀ = x₀ :=
  tendsto_nhds_unique
    (((ϕ.continuous continuous_fst continuous_snd).tendsto (T₀, x₀)).comp (hT.prodMk_nhds hx))
    (hx.congr' (hper.mono fun _ h ↦ h.symm))

/-- **Limits of fast periodic points are rest points.** If `xᵢ → x₀` along a nontrivial filter, and
eventually `xᵢ` returns to itself at a positive time `Tᵢ`, where `Tᵢ → 0`, then `x₀` is fixed by
the flow at every time. -/
theorem apply_eq_self_of_tendsto_zero [T2Space X] [l.NeBot] (hx : Tendsto x l (𝓝 x₀))
    (hT : Tendsto T l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < T i)
    (hper : ∀ᶠ i in l, ϕ (T i) (x i) = x i) (t : ℝ) : ϕ t x₀ = x₀ := by
  -- The multiples `⌊t / Tᵢ⌋ Tᵢ` are return times of `xᵢ` within `Tᵢ` of `t`.
  refine ϕ.apply_eq_self_of_tendsto (T := fun i ↦ ⌊t / T i⌋ * T i) hx ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun i ↦ t - T i) (h := fun _ ↦ t)
      (by simpa using tendsto_const_nhds.sub hT) tendsto_const_nhds ?_ ?_ <;>
      filter_upwards [hpos] with i hi
    · have h := (div_le_iff₀ hi).1 (Int.lt_floor_add_one (t / T i)).le
      linarith
    · exact (le_div_iff₀ hi).1 (Int.floor_le (t / T i))
  · filter_upwards [hper] with i hi
    have hz := (ϕ.periods (x i)).zsmul_mem (ϕ.mem_periods.2 hi) ⌊t / T i⌋
    rwa [ϕ.mem_periods, zsmul_eq_mul] at hz

/-- The orbit segment `θ ↦ ϕ (θ τ) y`, `θ ∈ [0, 1]`, depends continuously on `(τ, y)`. -/
private def orbitSegment (p : ℝ × X) : C(I, X) :=
  ⟨fun θ ↦ ϕ (θ * p.1) p.2, ϕ.continuous (by fun_prop) continuous_const⟩

private theorem continuous_orbitSegment : Continuous ϕ.orbitSegment :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (ϕ.continuous (by fun_prop) (continuous_snd.comp continuous_fst))

/-- The orbit segment of a point returning at time `τ`, as a based loop. -/
private def orbitLoop {τ : ℝ} {y : X} (hy : ϕ τ y = y) : Path y y where
  toContinuousMap := ϕ.orbitSegment (τ, y)
  source' := by simp [orbitSegment, ϕ.map_zero_apply]
  target' := by simpa [orbitSegment] using hy

/-- The loop `t ↦ ϕ t y` on `ℝ/τℤ` is null-homotopic exactly when its orbit segment
`θ ↦ ϕ (θ τ) y` is homotopic to the constant loop. -/
private theorem nullhomotopic_iff_orbitLoop {τ : ℝ} [Fact (0 < τ)] {y : X} (hy : ϕ τ y = y)
    {g : C(AddCircle τ, X)} (hg : ∀ t : ℝ, g t = ϕ t y) :
    g.Nullhomotopic ↔ (ϕ.orbitLoop hy).Homotopic (Path.refl y) :=
  g.nullhomotopic_iff_homotopic_refl _ fun θ ↦ by
    simp [orbitLoop, orbitSegment, hg]

/-- **Limits of contractible periodic orbits are contractible.** Let `X` be locally path-connected
and semilocally simply connected. Suppose that `xᵢ → x₀` and `Tᵢ → T₀ > 0` along a nontrivial
filter, that `x₀` returns to itself at time `T₀`, and that eventually the loop `t ↦ ϕ t xᵢ` lifts
to a null-homotopic map `ℝ/Tᵢℤ → X`. Then the loop `t ↦ ϕ t x₀` lifts to a null-homotopic map
`ℝ/T₀ℤ → X`. -/
theorem exists_nullhomotopic_of_tendsto [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] [l.NeBot] (hx : Tendsto x l (𝓝 x₀))
    (hT : Tendsto T l (𝓝 T₀)) (hT₀ : 0 < T₀) (h₀ : ϕ T₀ x₀ = x₀)
    (h : ∀ᶠ i in l, ∃ g : C(AddCircle (T i), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ϕ t (x i)) :
    ∃ g : C(AddCircle T₀, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ϕ t x₀ := by
  have : Fact (0 < T₀) := ⟨hT₀⟩
  -- The limit loop descends to the circle `ℝ/T₀ℤ`.
  have hper : Function.Periodic (fun t ↦ ϕ t x₀) T₀ := fun t ↦ by
    simp only [ϕ.map_add, h₀]
  let g₀ : C(AddCircle T₀, X) :=
    ⟨hper.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (ϕ.continuous continuous_id continuous_const)⟩
  have hg₀ (t : ℝ) : g₀ t = ϕ t x₀ := hper.lift_coe t
  refine ⟨g₀, (ϕ.nullhomotopic_iff_orbitLoop h₀ hg₀).2 ?_, hg₀⟩
  -- The loops `ϕ.orbitLoop` on the periodic orbits form a continuous family of based loops
  -- indexed by the periodic points `(τ, y)`, and null-homotopy of such a family is locally
  -- constant at the limit loop, where `X` is semilocally simply connected.
  let Y := {p : ℝ × X // ϕ p.1 p.2 = p.2}
  let γ : ∀ y : Y, Path y.1.2 y.1.2 := fun y ↦ ϕ.orbitLoop y.2
  have hp : Continuous fun q : Y × I ↦ (q.1 : ℝ × X) := continuous_subtype_val.comp continuous_fst
  have hγ : Continuous ↿γ :=
    ϕ.continuous (β := Y × I) (t := fun q ↦ (q.2 : ℝ) * (q.1 : ℝ × X).1)
      (f := fun q ↦ (q.1 : ℝ × X).2)
      ((continuous_subtype_val.comp continuous_snd).mul (continuous_fst.comp hp))
      (continuous_snd.comp hp)
  let y₀ : Y := ⟨(T₀, x₀), h₀⟩
  have hloc := eventually_homotopic_refl_iff_of_semilocallySimplyConnectedOn
    (a := fun y : Y ↦ y.1.2) γ hγ (y₀ := y₀) (.of_semilocallySimplyConnectedSpace _)
  -- Eventually `xᵢ` returns to itself at time `Tᵢ`, so `(Tᵢ, xᵢ)` tends to `(T₀, x₀)` in `Y`.
  have hret : ∀ᶠ i in l, 0 < T i ∧ ϕ (T i) (x i) = x i := by
    filter_upwards [hT.eventually (lt_mem_nhds hT₀), h] with i hTi hi
    obtain ⟨g, -, hgx⟩ := hi
    have : Fact (0 < T i) := ⟨hTi⟩
    exact ⟨hTi, by rw [← hgx, AddCircle.coe_period, ← QuotientAddGroup.mk_zero, hgx,
      ϕ.map_zero_apply]⟩
  classical
  let f : ι → Y := fun i ↦ if hi : ϕ (T i) (x i) = x i then ⟨(T i, x i), hi⟩ else y₀
  have hf : Tendsto f l (𝓝 y₀) :=
    tendsto_subtype_rng.2 <| (hT.prodMk_nhds hx).congr' (hret.mono fun i hi ↦ by simp [f, hi.2])
  obtain ⟨i, ⟨hTi, hi⟩, ⟨g, hg, hgx⟩, hiff⟩ := (hret.and (h.and (hf.eventually hloc))).exists
  have : Fact (0 < T i) := ⟨hTi⟩
  have hfi : f i = ⟨(T i, x i), hi⟩ := by simp [f, hi]
  rw [hfi] at hiff
  exact hiff.1 ((ϕ.nullhomotopic_iff_orbitLoop hi hgx).1 hg)

end Flow
