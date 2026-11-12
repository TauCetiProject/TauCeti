/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.IntervalBase
public import TauCeti.Analysis.Calculus.Morse.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The negative gradient flow of the Euclidean quartic

The quartic `(x² - 1)² / 4` on `ℝ` is the base potential `TauCeti.intervalBasePotential 1`. It
has a local maximum at `0` and minima at `±1`, and its negative gradient field is `x (1 - x²)`,
whose linearization is `1` at `0` and `-2` at `±1`, so trajectories leave `0` at rate `1` and
approach `±1` at rate `2`. Its flow `TauCeti.intervalBaseFlow 1`, trajectory
`TauCeti.intervalBaseOrbit 1` from `0` to `1` and time coordinate
`TauCeti.intervalBaseTimeCoordinate` on `(0, 1)` are developed in
`TauCeti.Analysis.Calculus.Morse.IntervalBase`, for the base of a continuation, together with
the facts about the whole interval `[-1, 1]` used here. For
every `C`, the flow keeps `(-1, 1)` invariant and its lines are the only negative gradient
trajectories staying in `[-1, 1]` (`TauCeti.eq_intervalBaseFlow_of_isIntegralCurve`), since the
field is Lipschitz there. For `C ≠ 0` the critical points are `-1`, `0` and `1`
(`TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_iff`). For `C > 0` the flow tends
forward to the sign of the initial point (`TauCeti.tendsto_intervalBaseFlow_atTop_sign`) and
backward to `0` or the fixed endpoint (`TauCeti.tendsto_intervalBaseFlow_atBot_ite`). Outside
`[-1, 1]` the flow is not used. In the time coordinate
`s`, the identities `q² = σ (2s)` and `1 - q² = σ (-2s)` for the sigmoid `σ` display the two
asymptotic rates exactly, and the flow line through any point of `(0, 1)` is a translate of `q`
(`TauCeti.intervalBaseFlow_eq_intervalBaseOrbit`).

The separated sum `quarticWellSum y = ∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ` is the standard model
for compactified spaces of broken trajectories and for the comparison of Morse chains with
cellular chains of the cube. Its critical points are the points of `{-1, 0, 1}^ι`, all
nondegenerate, and the Morse index of such a point is the number of its zero coordinates
(`TauCeti.morseIndex_quarticWellSum`). Its partial derivatives are those of the summands
(`TauCeti.fderiv_quarticWellSum_apply`), so its negative gradient field for the Euclidean inner
product acts coordinatewise, and its flow `quarticWellSumFlow` is the coordinatewise flow
`TauCeti.intervalBaseFlow 1`. It keeps the cube `[-1, 1]^ι` invariant, and every point of the cube
has a forward limit, the coordinatewise sign, and a backward limit, which keeps the coordinates
equal to `±1` and replaces the others by `0`. So the points of the cube flowing backward to a
critical point `p` form the open face of the cube centred at `p`. A point `y` of the cube lies on a
trajectory from `p` to `q` exactly when, coordinatewise, either `p i = 0`, `y i ∈ (-1, 1)` and
`q i` is the sign of `y i`, or `y i = p i = q i = ±1`
(`TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff`). The coordinates that move are those with
`p i = 0 ≠ q i`, and their number is the index difference.

## Main definitions

* `TauCeti.quarticWellSum`, `TauCeti.quarticWellSumFlow`: the separated sum on `ι → ℝ` and its
  coordinatewise flow.

## Main results

* `TauCeti.isNondegenerateCriticalPoint_quarticWellSum_iff`, `TauCeti.morseIndex_quarticWellSum`:
  the critical points of the separated sum and their indices.
* `TauCeti.hasDerivAt_quarticWellSumFlow`, `TauCeti.fderiv_quarticWellSum_apply`: the coordinatewise
  flow integrates the negative Euclidean gradient.
* `TauCeti.tendsto_quarticWellSumFlow_atTop`, `TauCeti.tendsto_quarticWellSumFlow_atBot`,
  `TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff`: limits and connecting trajectories in the
  cube.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3 (the comparison of the Morse complex with cellular
  homology, which this quartic on the cube models).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (negative gradient trajectories and their limits).
-/

public section

noncomputable section

open Real Set Filter Topology
open scoped Gradient

namespace TauCeti

variable {C : ℝ}

/-! ### The quartic on the cube -/

section Sum

variable {ι : Type*}

/-- The **negative gradient flow of the Euclidean quartic** on the cube `[-1, 1]^ι`: the flow
`TauCeti.intervalBaseFlow 1` in each coordinate. -/
def quarticWellSumFlow (s : ℝ) (y : ι → ℝ) : ι → ℝ := fun i ↦ intervalBaseFlow 1 s (y i)

@[simp]
theorem quarticWellSumFlow_apply (s : ℝ) (y : ι → ℝ) (i : ι) :
    quarticWellSumFlow s y i = intervalBaseFlow 1 s (y i) := (rfl)

@[simp]
theorem quarticWellSumFlow_zero_left (y : ι → ℝ) : quarticWellSumFlow 0 y = y :=
  funext fun i ↦ intervalBaseFlow_zero 1 (y i)

/-- The flow property of the coordinatewise flow on the cube. -/
theorem quarticWellSumFlow_add {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s r : ℝ) :
    quarticWellSumFlow (s + r) y = quarticWellSumFlow s (quarticWellSumFlow r y) :=
  funext fun i ↦ intervalBaseFlow_add 1 s r ⟨hy.1 i, hy.2 i⟩

/-- The flow keeps the cube `[-1, 1]^ι` invariant. -/
theorem quarticWellSumFlow_mem_Icc {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s : ℝ) :
    quarticWellSumFlow s y ∈ Icc (-1) 1 :=
  ⟨fun i ↦ (intervalBaseFlow_mem_Icc 1 s ⟨hy.1 i, hy.2 i⟩).1,
    fun i ↦ (intervalBaseFlow_mem_Icc 1 s ⟨hy.1 i, hy.2 i⟩).2⟩

/-- The coordinatewise flow solves the negative gradient equation `yᵢ' = yᵢ (1 - yᵢ²)` of the
Euclidean quartic. -/
theorem hasDerivAt_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) (s : ℝ) :
    HasDerivAt (fun s ↦ quarticWellSumFlow s y)
      (fun i ↦ -∇ (intervalBasePotential 1) (quarticWellSumFlow s y i)) s :=
  hasDerivAt_pi.2 fun i ↦ isIntegralCurve_intervalBaseFlow 1 ⟨hy.1 i, hy.2 i⟩ s

/-- **Forward limits**: every point flows to the critical point given by the signs of its
coordinates. On the cube `[-1, 1]^ι` this is the forward limit of the negative gradient
trajectory through the point. -/
theorem tendsto_quarticWellSumFlow_atTop (y : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 fun i ↦ (SignType.sign (y i) : ℝ)) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_intervalBaseFlow_atTop_sign one_pos (y i)

/-- **Backward limits on the cube**: as `s → -∞` a point of `[-1, 1]^ι` tends to the critical
point keeping its coordinates equal to `±1` and replacing the others by `0`. -/
theorem tendsto_quarticWellSumFlow_atBot {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot
      (𝓝 fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_intervalBaseFlow_atBot_ite one_pos ⟨hy.1 i, hy.2 i⟩

/-- **Connecting trajectories in the cube.** A point `y` of `[-1, 1]^ι` lies on a trajectory from
`p` to `q` exactly when each coordinate either moves, with `p i = 0`, `y i ∈ (-1, 1)` and `q i`
the sign of `y i`, or stays at `y i = p i = q i = ±1`. -/
theorem tendsto_quarticWellSumFlow_atBot_atTop_iff {y p q : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q) ↔
      ∀ i, (y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i) := by
  have hbot := tendsto_quarticWellSumFlow_atBot hy
  have htop := tendsto_quarticWellSumFlow_atTop y
  have key : ∀ i, (p i = (if y i ∈ Ioo (-1) 1 then 0 else y i) ∧
      q i = SignType.sign (y i)) ↔ ((y i ∈ Ioo (-1) 1 ∧ p i = 0 ∧ q i = SignType.sign (y i)) ∨
        ((y i = -1 ∨ y i = 1) ∧ p i = y i ∧ q i = y i)) := fun i ↦ by
    by_cases hi : y i ∈ Ioo (-1) 1
    · have : ¬(y i = -1 ∨ y i = 1) := by rintro (h | h) <;> simp [h] at hi
      simp [hi, this]
    · have h : y i ∈ Icc (-1) 1 \ Ioo (-1) 1 := ⟨⟨hy.1 i, hy.2 i⟩, hi⟩
      rw [Icc_sdiff_Ioo_same (by norm_num), mem_insert_iff, mem_singleton_iff] at h
      have hs : (SignType.sign (y i) : ℝ) = y i := by rcases h with h | h <;> simp [h]
      simp [hi, h, hs]
  refine ⟨fun ⟨hp, hq⟩ i ↦ (key i).1 ⟨congrFun (tendsto_nhds_unique hp hbot) i,
    congrFun (tendsto_nhds_unique hq htop) i⟩, fun h ↦ ?_⟩
  have hp : p = fun i ↦ if y i ∈ Ioo (-1) 1 then 0 else y i := funext fun i ↦ ((key i).2 (h i)).1
  have hq : q = fun i ↦ (SignType.sign (y i) : ℝ) := funext fun i ↦ ((key i).2 (h i)).2
  exact ⟨hp ▸ hbot, hq ▸ htop⟩

variable [Fintype ι]

/-- The **Euclidean quartic** `∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ`, the separated sum of copies of
the base potential `TauCeti.intervalBasePotential 1`. -/
def quarticWellSum (y : ι → ℝ) : ℝ := ∑ i, intervalBasePotential 1 (y i)

theorem quarticWellSum_def (y : ι → ℝ) :
    quarticWellSum y = ∑ i, intervalBasePotential 1 (y i) := (rfl)

private theorem quarticWellSum_eq :
    (quarticWellSum : (ι → ℝ) → ℝ) = fun z ↦ ∑ i, intervalBasePotential 1 (z i) :=
  funext quarticWellSum_def

/-- The partial derivatives of the Euclidean quartic are those of its summands, so its gradient
for the Euclidean inner product is `(yᵢ (yᵢ² - 1))ᵢ`, and `TauCeti.quarticWellSumFlow` integrates
its negative. -/
theorem fderiv_quarticWellSum_apply (y v : ι → ℝ) :
    fderiv ℝ quarticWellSum y v = ∑ i, ∇ (intervalBasePotential 1) (y i) * v i := by
  rw [quarticWellSum_eq,
    fderiv_sum_comp_eval fun _ ↦ (hasDerivAt_intervalBasePotential 1 _).differentiableAt]
  simp

/-- **The Euclidean quartic is a Morse function**: its critical points are the points of
`{-1, 0, 1}^ι`, all nondegenerate. -/
@[simp]
theorem isNondegenerateCriticalPoint_quarticWellSum_iff {y : ι → ℝ} :
    IsNondegenerateCriticalPoint quarticWellSum y ↔ ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1 := by
  rw [quarticWellSum_eq, isNondegenerateCriticalPoint_sum_comp_eval_iff
    fun _ ↦ (contDiff_intervalBasePotential 1).contDiffAt]
  refine forall_congr' fun i ↦ ?_
  rw [← isNondegenerateCriticalPoint_intervalBasePotential_iff one_ne_zero,
    isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential 1).contDiffAt,
    iteratedDeriv_succ, iteratedDeriv_one]

/-- The Morse index of a critical point of the Euclidean quartic is the number of its zero
coordinates. -/
theorem morseIndex_quarticWellSum {y : ι → ℝ} (hy : ∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) :
    morseIndex quarticWellSum y = {i | y i = 0}.ncard := by
  rw [quarticWellSum_eq,
    morseIndex_sum_comp_eval fun _ ↦ (contDiff_intervalBasePotential 1).contDiffAt]
  have h := iteratedDeriv_two_intervalBasePotential 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  congr 1
  ext i
  rw [mem_ofPred_eq, mem_ofPred_eq, h]
  rcases hy i with h | h | h <;> rw [h] <;> norm_num

/-- The coordinatewise flow through a point of the cube `[-1, 1]^ι` is an integral curve of the
negative Euclidean gradient field `(-∇ (TauCeti.intervalBasePotential 1) (zᵢ))ᵢ` of the quartic,
see `TauCeti.fderiv_quarticWellSum_apply`. -/
theorem isIntegralCurve_quarticWellSumFlow {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    IsIntegralCurve (fun s ↦ quarticWellSumFlow s y)
      (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)) :=
  hasDerivAt_quarticWellSumFlow hy

/-- **Uniqueness of captured trajectories** on the cube: a negative gradient trajectory of the
Euclidean quartic which stays in `[-1, 1]^ι` is the flow line through its initial point. -/
theorem eq_quarticWellSumFlow_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)))
    (hmem : ∀ s, γ s ∈ Icc (-1) 1) : γ = fun s ↦ quarticWellSumFlow s (γ 0) := by
  funext s i
  exact congrFun (eq_intervalBaseFlow_of_isIntegralCurve (fun s ↦ hasDerivAt_pi.1 (hγ s) i)
    fun s ↦ ⟨(hmem s).1 i, (hmem s).2 i⟩) s

end Sum

end TauCeti
