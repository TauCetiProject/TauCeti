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
import TauCeti.Topology.Homotopy.Path
import TauCeti.Topology.Homotopy.TubeNeighborhood

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

For the last statement, the limit loop lies in a tube: a chain of open sets along a partition of
the loop, in which any two paths with common ends are homotopic. Tubes are open in the
compact-open topology, so the nearby loops lie in the same tube, and joining the base points of a
nearby loop and of the limit loop by a short path at both ends of the tube shows that the limit
loop is conjugate to the nearby loop by that path.

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
  set γ₀ := ϕ.orbitLoop h₀
  -- The limit loop lies in a tube, and a path-connected neighbourhood `W` of `x₀` lies in the
  -- vertex sets at both of its ends.
  obtain ⟨n, part, U, hγ₀⟩ := γ₀.exists_isInTube_of_semilocallySimplyConnectedOn
    (.of_semilocallySimplyConnectedSpace _)
  cases n with
  | zero => exact isEmptyElim part
  | succ n =>
  have hV : U.V 0 ∩ U.V (Fin.last (n + 1)) ∈ 𝓝 x₀ := by
    refine inter_mem ((U.isOpen_V _).mem_nhds ?_) ((U.isOpen_V _).mem_nhds ?_)
    · simpa using hγ₀.mem_V 0
    · simpa using hγ₀.mem_V (Fin.last _)
  obtain ⟨W, ⟨hWx, hW⟩, hWV⟩ := (path_connected_basis x₀).mem_iff.1 hV
  -- Choose a nearby periodic orbit in the same tube, with base point in `W`.
  have htube : ∀ᶠ i in l, Path.IsInTube (ϕ.orbitSegment (T i, x i)) part U :=
    (ϕ.continuous_orbitSegment.tendsto (T₀, x₀)).comp (hT.prodMk_nhds hx)
      |>.eventually ((U.isOpen_setOf_isInTube part).mem_nhds hγ₀)
  obtain ⟨i, hi, hxi, hTi, g, hg, hgx⟩ :=
    (htube.and ((hx.eventually_mem hWx).and ((hT.eventually (lt_mem_nhds hT₀)).and h))).exists
  have : Fact (0 < T i) := ⟨hTi⟩
  have hyi : ϕ (T i) (x i) = x i := by
    rw [← hgx, AddCircle.coe_period, ← QuotientAddGroup.mk_zero, hgx, ϕ.map_zero_apply]
  set γ := ϕ.orbitLoop hyi
  have hγ : γ.Homotopic (Path.refl (x i)) := (ϕ.nullhomotopic_iff_orbitLoop hyi hgx).1 hg
  -- Rungs between the two loops at the vertices of the partition: the same path `α` in `W` at
  -- both ends, and any path in the vertex set elsewhere.
  obtain ⟨α, hα⟩ := hW.joinedIn _ (mem_of_mem_nhds hWx) _ hxi
  have hend {j : Fin (n + 2)} (hj : j = 0 ∨ j = Fin.last (n + 1)) :
      γ₀ (part.t j) = x₀ ∧ γ (part.t j) = x i := by
    rcases hj with rfl | rfl <;> simp
  let rung (j : Fin (n + 2)) : Path (γ₀ (part.t j)) (γ (part.t j)) :=
    if hj : j = 0 ∨ j = Fin.last (n + 1) then
      α.cast (hend hj).1 (hend hj).2
    else ((U.isPathConnected_V j).joinedIn _ (hγ₀.mem_V j) _ (hi.mem_V j)).somePath
  have hrung (j : Fin (n + 2)) : range (rung j) ⊆ U.V j := by
    by_cases hj : j = 0 ∨ j = Fin.last (n + 1)
    · simp only [rung, hj, ↓reduceDIte]
      rintro _ ⟨t, rfl⟩
      refine (hWV (hα t)).elim fun h₀ h₁ ↦ ?_
      rcases hj with rfl | rfl
      exacts [h₀, h₁]
    · simp only [rung, hj, ↓reduceDIte]
      exact range_subset_iff.2 (JoinedIn.somePath_mem _)
  have hrung_end {j : Fin (n + 2)} (hj : j = 0 ∨ j = Fin.last (n + 1)) :
      (rung j).cast (hend hj).1.symm (hend hj).2.symm = α := by
    ext t
    simp [rung, hj]
  -- On each segment, both loops and the rungs at its ends lie in one path-homotopy-trivial set.
  have h_rect : ∀ k : Fin (n + 1),
      ((γ₀.subpath (part.t k.castSucc) (part.t k.succ)).trans (rung k.succ)).Homotopic
        ((rung k.castSucc).trans (γ.subpath (part.t k.castSucc) (part.t k.succ))) := fun k ↦
    isPathHomotopyTrivial_def.mp (U.isPathHomotopyTrivial_U k) _ _
      (by
        rw [Path.trans_range]
        exact union_subset (hγ₀.range_subpath_subset k) ((hrung _).trans (U.V_succ_subset k)))
      (by
        rw [Path.trans_range]
        exact union_subset ((hrung _).trans (U.V_castSucc_subset k)) (hi.range_subpath_subset k))
  have key := Path.Homotopic.trans_of_subpath_trans γ₀ γ part rung h_rect
  rw [hrung_end (.inr rfl), hrung_end (.inl rfl)] at key
  -- So `γ₀ · α ≃ α · γ ≃ α ≃ refl · α`, and `γ₀` is null-homotopic.
  exact Path.Homotopic.trans_right_cancel <| key.trans <|
    (Path.Homotopic.trans_right_of_nullhomotopic hγ).trans (Path.Homotopic.refl_trans _).symm

end Flow
