/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.CompactOpen
public import TauCeti.Dynamics.Flow.ClosedOrbit
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Translation flows on spaces of maps, and periods of cylinders with a constant end

For a real topological vector space `G` which is locally compact and a vector `v : G`, translating
the domain along `v` is a flow on the space `C(G, X)` of continuous maps with the compact-open
topology: at time `t` a map `u` is sent to `z ↦ u (z + t • v)` (`TauCeti.translationFlow`). Its
periods at `u` are the times `t` for which `t • v` is a period of `u`
(`TauCeti.mem_periods_translationFlow`).

On the cylinder `ℝ × ℝ`, with coordinates `(s, t)` and maps `1`-periodic in `t`, the flows along
`(1, 0)` and `(0, 1)` are the commuting translation `u ↦ u(· + a, ·)` and time rotation
`u ↦ u(·, · + θ)` acting on Floer cylinders. This file computes their joint stabilizer for a map
`u` with a *constant end*, a point `x` with `u (s, t) → x` as `s → -∞` uniformly in `t`, that is,
along the filter `atBot ×ˢ ⊤`.

* A period `c` of `u` with nonzero `s`-component forces `u` to be constant: iterating `c` towards
  the constant end, the value of `u` at each point is the limit `x`
  (`Function.Periodic.eq_of_tendsto_atBot`). So if `u` is not invariant under all time rotations,
  each of its periods has zero `s`-component (`Function.Periodic.fst_eq_zero_of_tendsto_atBot`).
* If `u` is continuous, `1`-periodic in `t` and not invariant under all time rotations, its time
  periods are the multiples of `1 / n` for some `n ≥ 1`
  (`Function.Periodic.exists_periods_translationFlow_eq_zmultiples_inv`): modulo `1`, the
  stabilizer of `u` for the rotation action of the circle `ℝ / ℤ` is the finite cyclic group of
  order `n`.
* Hence, with a constant end, the periods of such a map are exactly `{0} × (1 / n) ℤ`
  (`Function.Periodic.exists_periodic_iff_of_tendsto_atBot`): translations act freely, and the
  stabilizer of the action of `ℝ × ℝ / ℤ` is finite.

These are the topological facts about stabilizers used in the dimension count for autonomous Floer
cylinders: away from the time-invariant cylinders, the translation and rotation action has finite
stabilizers. Only continuity is used; no equation is involved.

## Main definitions

* `TauCeti.translationFlow v`: the flow on `C(G, X)` translating the domain along `v`.

## Main results

* `TauCeti.translationFlow_comm`: translation flows along two vectors commute.
* `TauCeti.mem_periods_translationFlow`: the periods of the translation flow at `u` are the
  times `t` with `Function.Periodic u (t • v)`.
* `Function.Periodic.eq_of_tendsto_atBot`: a map on `ℝ × Y` with a constant end at `-∞` and a
  period with nonzero first component is constant.
* `Function.Periodic.exists_periods_translationFlow_eq_zmultiples_inv`: the time-rotation periods
  of a cylinder which is not time-invariant are `(1 / n) ℤ`.
* `Function.Periodic.exists_periodic_iff_of_tendsto_atBot`: the periods of a cylinder with a
  constant end which is not time-invariant are `{0} × (1 / n) ℤ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the translation action on connecting trajectories.
-/

public section

open Filter Function Topology

/-! ### Periods and constant ends -/

namespace Function.Periodic

variable {α X : Type*} [AddMonoid α] [TopologicalSpace X] [T2Space X] {u : α → X} {c : α}

/-- If `c` is a period of `u`, `u` tends to `x` along a filter `l`, and the iterated translates
`z + n • c` tend to `l`, then `u z = x`. -/
theorem eq_of_tendsto_of_tendsto_add_nsmul (h : Periodic u c) {l : Filter α} {x : X}
    (hu : Tendsto u l (𝓝 x)) {z : α} (hz : Tendsto (fun n : ℕ ↦ z + n • c) atTop l) :
    u z = x := by
  exact tendsto_nhds_unique (tendsto_const_nhds (x := u z))
    ((hu.comp hz).congr fun n ↦ h.nsmul n z)

variable {Y : Type*} [AddGroup Y] {u : ℝ × Y → X} {c : ℝ × Y} {x : X}

/-- **A period moving towards a constant end.** If `u : ℝ × Y → X` tends to `x` as the first
coordinate tends to `-∞`, uniformly in the second, then every period `c` of `u` with `c.1 ≠ 0`
forces `u` to be constant equal to `x`. -/
theorem eq_of_tendsto_atBot (h : Periodic u c) (hc : c.1 ≠ 0)
    (hu : Tendsto u (atBot ×ˢ ⊤) (𝓝 x)) (z : ℝ × Y) : u z = x := by
  -- Replace `c` by `-c` if necessary, so that its first component is negative.
  obtain ⟨d, hd, hd₀⟩ : ∃ d, Periodic u d ∧ d.1 < 0 := by
    rcases hc.lt_or_gt with hc | hc
    · exact ⟨c, h, hc⟩
    · exact ⟨-c, h.neg, by simpa using hc⟩
  refine hd.eq_of_tendsto_of_tendsto_add_nsmul hu (tendsto_prod_iff'.2 ⟨?_, tendsto_top⟩)
  simp only [Prod.fst_add, Prod.smul_fst, nsmul_eq_mul]
  exact tendsto_atBot_add_const_left _ _
    (Tendsto.atTop_mul_const_of_neg hd₀ tendsto_natCast_atTop_atTop)

/-- For a map with a constant end at `-∞` which is not invariant under every translation `(0, θ)`
of the second coordinate, every period has zero first component. -/
theorem fst_eq_zero_of_tendsto_atBot (h : Periodic u c) (hu : Tendsto u (atBot ×ˢ ⊤) (𝓝 x))
    (hθ : ∃ θ : Y, ¬Periodic u (0, θ)) : c.1 = 0 := by
  -- A period with nonzero first component makes `u` constant, hence invariant.
  by_contra hc
  obtain ⟨θ, hθ⟩ := hθ
  exact hθ fun z ↦ by rw [h.eq_of_tendsto_atBot hc hu, h.eq_of_tendsto_atBot hc hu]

end Function.Periodic

namespace TauCeti

/-! ### The translation flow -/

section TranslationFlow

variable {G X : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module ℝ G] [ContinuousSMul ℝ G] [LocallyCompactSpace G] [TopologicalSpace X]

/-- The flow on the continuous maps `G → X` translating the domain along `v`: at time `t` it sends
`u` to `z ↦ u (z + t • v)`. -/
noncomputable def translationFlow (v : G) : Flow ℝ C(G, X) where
  toFun t u := u.comp (ContinuousMap.addRight (t • v))
  cont' := by
    have h : Continuous fun t : ℝ ↦ ContinuousMap.addRight (t • v) :=
      ContinuousMap.continuous_of_continuous_uncurry _
        (continuous_snd.add (continuous_fst.smul continuous_const))
    exact ContinuousMap.continuous_comp'.comp ((h.comp continuous_fst).prodMk continuous_snd)
  map_add' t₁ t₂ u := by
    ext z
    simp [add_smul, add_assoc, add_comm (t₁ • v)]
  map_zero' u := by
    ext z
    simp

@[simp]
theorem translationFlow_apply (v : G) (t : ℝ) (u : C(G, X)) (z : G) :
    translationFlow v t u z = u (z + t • v) :=
  (rfl)

/-- The translation flows along any two vectors commute. -/
theorem translationFlow_comm (v w : G) (s t : ℝ) (u : C(G, X)) :
    translationFlow v s (translationFlow w t u) = translationFlow w t (translationFlow v s u) := by
  ext z
  simp only [translationFlow_apply, add_right_comm]

/-- The periods of the translation flow along `v` at `u` are the times `t` for which `t • v` is a
period of `u`. -/
theorem mem_periods_translationFlow {v : G} {t : ℝ} {u : C(G, X)} :
    t ∈ (translationFlow v).periods u ↔ Periodic u (t • v) := by
  simp [Periodic, ContinuousMap.ext_iff]

end TranslationFlow

end TauCeti

/-! ### Periods of cylinders -/

namespace Function.Periodic

open TauCeti

variable {X : Type*} [TopologicalSpace X] {u : C(ℝ × ℝ, X)}

/-- **Time-rotation periods of a cylinder.** If a continuous map `u` on the cylinder is
`1`-periodic in `t` but not invariant under every time rotation `(s, t) ↦ (s, t + θ)`, then its
time-rotation periods are the integer multiples of `1 / n` for some `n ≥ 1`. So modulo `1`, the
stabilizer of `u` for the rotation action of the circle is finite cyclic of order `n`. -/
theorem exists_periods_translationFlow_eq_zmultiples_inv [T1Space X] (h₁ : Periodic u (0, 1))
    (hu : ∃ θ : ℝ, ¬Periodic u (0, θ)) :
    ∃ n : ℕ, 0 < n ∧
      (translationFlow ((0, 1) : ℝ × ℝ)).periods u = AddSubgroup.zmultiples ((n : ℝ)⁻¹) := by
  have hθ (θ : ℝ) : θ • ((0, 1) : ℝ × ℝ) = (0, θ) := by simp
  refine (translationFlow ((0, 1) : ℝ × ℝ)).exists_periods_eq_zmultiples_inv ?_ ?_
  · rwa [← Flow.mem_periods, mem_periods_translationFlow, hθ]
  · obtain ⟨θ, hθu⟩ := hu
    refine ⟨θ, fun h ↦ hθu ?_⟩
    rw [← hθ, ← mem_periods_translationFlow]
    exact (translationFlow _).mem_periods.2 h

/-- **The stabilizer of a cylinder with a constant end.** Let `u` be a continuous map on the
cylinder, `1`-periodic in `t`, tending to `x` as `s → -∞` uniformly in `t`, and not invariant under
every time rotation. Then for some `n ≥ 1` the periods of `u` are exactly the pairs `(0, θ)` with
`θ` an integer multiple of `1 / n`: no nontrivial translation in `s`, combined with any rotation,
fixes `u`. -/
theorem exists_periodic_iff_of_tendsto_atBot [T2Space X] (h₁ : Periodic u (0, 1))
    (hu : ∃ θ : ℝ, ¬Periodic u (0, θ)) {x : X} (hx : Tendsto u (atBot ×ˢ ⊤) (𝓝 x)) :
    ∃ n : ℕ, 0 < n ∧
      ∀ c : ℝ × ℝ, Periodic u c ↔ c.1 = 0 ∧ c.2 ∈ AddSubgroup.zmultiples ((n : ℝ)⁻¹) := by
  obtain ⟨n, hn, hP⟩ := h₁.exists_periods_translationFlow_eq_zmultiples_inv hu
  -- A vector with zero `s`-component is a multiple of `(0, 1)`.
  have hc₂ (c : ℝ × ℝ) (hc₁ : c.1 = 0) : c.2 • ((0, 1) : ℝ × ℝ) = c := by
    ext <;> simp [hc₁]
  refine ⟨n, hn, fun c ↦ ⟨fun hc ↦ ?_, fun ⟨hc₁, hc₂'⟩ ↦ ?_⟩⟩
  · have hc₁ := hc.fst_eq_zero_of_tendsto_atBot hx hu
    refine ⟨hc₁, ?_⟩
    rwa [← hP, mem_periods_translationFlow, hc₂ c hc₁]
  · rwa [← hP, mem_periods_translationFlow, hc₂ c hc₁] at hc₂'

end Function.Periodic
