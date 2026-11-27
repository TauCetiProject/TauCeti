/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.DG.DegreeZero
public import TauCeti.Geometry.Manifold.Morse.Examples.Circle
public import Mathlib.Topology.Covering.FundamentalGroupCircle
import TauCeti.Algebra.AddCircle

/-!
# The Barraud–Cornea cocycle of the height function of the circle

The cosine `circleCos` is the height function of the circle `S¹ = ℝ ⧸ 2πℤ`, with its maximum at
`0` and its minimum at `π`. This file computes the trajectory space from the maximum to the
minimum for every adapted pseudo-gradient, and the degree-zero entry of the Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) between them: its image in the group ring
of the fundamental group is `∑_ε r_ε [θ ∘ γ_ε]`, the sum of the classes of the loops traced along
the two half-circles `γ_ε`, weighted by the coefficients `r_ε` of the two trajectories. When both
coefficients are `1`, as in the mod-two fundamental chain, it is `(1 + t) g`, with `t` the image of
a generator of `π₁(S¹)`. For `g = 1` and coefficients mod two this is the twisted Morse
differential `1 + t` of the circle, with its `π₁`-monodromy, which the classical mod-two Morse
differential `1 + 1 = 0` forgets.

* **The two half-circles.** The Moore path `circleCosHalfPath ε`, `ε = ±1`, is at the angle
  `ε · arccos (1 - t)` at time `t`, so that the cosine decreases along it at unit speed from `1`
  to `-1`; it runs through the upper half-circle for `ε = 1` and through the lower one for
  `ε = -1`.
* **Every trajectory from the maximum to the minimum is a half-circle.** A broken trajectory from
  `0` to `π`, parametrized by the values of the cosine, is at a point with `cos = 1 - t` at time
  `t`, that is at one of the two angles `± arccos (1 - t)`
  (`TauCeti.eq_or_eq_neg_arccos_of_circleCos_eq`). These two angles differ for `0 < t < 2`, so by
  connectedness of `(0, 2)` the path follows one half-circle throughout
  (`IsAdaptedPseudoGradient.exists_morseLevelPath_eq_circleCosHalfPath`). Only the values of the
  cosine along the path enter, not the Morse–Smale condition.
* **Both half-circles occur.** The midpoints `± π / 2` of the half-circles lie on trajectories from
  `0` to `π`, since along their orbits the cosine stays on one side of its value `0` there
  (`IsAdaptedPseudoGradient.circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet`).
  Recording these trajectories on the levels of `c` gives two points of the trajectory space
  (`IsAdaptedPseudoGradient.circleCosTrajectory`), whose Moore paths are the two half-circles
  (`IsAdaptedPseudoGradient.morseLevelPath_circleCosTrajectory`). A record is determined by its
  Moore path (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath_injective`), so when the levels of
  `c` are dense in `(-1, 1)` these are all the points of the trajectory space, and they are
  distinct (`IsAdaptedPseudoGradient.bijective_circleCosTrajectory`).
* **The degree-zero entry of the cocycle.** For a map `θ` from the circle to `Y` sending `0` and
  `π` to `y₀`, the image in `R[π₁(Y, y₀)]` of the entry of the Barraud–Cornea cocycle of a
  twisting chain system `S` at `(0, π)` is `∑_ε r_ε [θ ∘ γ_ε]`, over the loops traced by `θ`
  along the two half-circles (`TauCeti.circleCosHalfLoop`), weighted by the coefficients of the
  two trajectories in `S`
  (`IsAdaptedPseudoGradient.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos`).
* **The two loops differ by a generator.** The lower half-circle followed by the upper one run
  backwards is a loop once around the circle (`TauCeti.circleCosLoop`), whose class has winding
  number `1` (`TauCeti.windingNumber_fundamentalGroupHom_circleCosLoop`). The class of the lower
  half-loop is its image under `θ` times the class of the upper half-loop
  (`TauCeti.fundamentalGroupHom_circleCosHalfLoop_neg_one`). So when `S` gives both trajectories
  the coefficient `1`, as the mod-two fundamental chain of the two-point trajectory space does,
  the entry is `(1 + t) g`, with `g` the class of the upper half-loop and `t` the image under `θ`
  of the generator
  (`IsAdaptedPseudoGradient.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_mul`).
  For instance (an illustration, not formalized here), when `θ` is constant on the upper
  half-circle, as the collapse of an embedded tree through the critical points along it is,
  `g = 1` and the entry is `1 + t`.

The lemmas in the namespace `TauCeti.IsAdaptedPseudoGradient` are abbreviated above.

## Main definitions

* `TauCeti.circleCosHalfPath`: the two half-circles, parametrized by the values of the cosine.
* `TauCeti.circleCosHalfLoop`: the loops traced along them by a map from the circle.
* `TauCeti.circleCosLoop`: the loop once around the circle.
* `TauCeti.IsAdaptedPseudoGradient.circleCosTrajectory`: the two trajectories from the maximum to
  the minimum, as points of the trajectory space.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_morseLevelPath_eq_circleCosHalfPath`: every broken
  trajectory from the maximum to the minimum runs along a half-circle.
* `TauCeti.IsAdaptedPseudoGradient.bijective_circleCosTrajectory`: the trajectory space from the
  maximum to the minimum consists of the two trajectories through the half-circles.
* `TauCeti.windingNumber_fundamentalGroupHom_circleCosLoop`: the loop around the circle has winding
  number one.
* `TauCeti.fundamentalGroupHom_circleCosHalfLoop_neg_one`: the two half-loops differ by the loop
  around the circle.
* `TauCeti.IsAdaptedPseudoGradient.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos` and
  `..._eq_mul`: the degree-zero entry of the Barraud–Cornea cocycle from the maximum to the
  minimum, in general and for the coefficients `1`.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
-/

public section

universe u

open Filter Function Set
open scoped Manifold ContDiff Real NNReal

namespace TauCeti

local instance morseDGCircleTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ### The two half-circles -/

/-- **The half-circle along which the cosine decreases at unit speed.** The Moore path of
length `2` from `0` to `π` on the circle `ℝ ⧸ 2πℤ` which is at the angle `ε · arccos (1 - t)` at
time `t`, so that the cosine takes the value `1 - t` there. It runs through the upper half-circle
`[0, π]` for `ε = 1` and through the lower half-circle `[-π, 0]` for `ε = -1`. -/
noncomputable def circleCosHalfPath (ε : ℤˣ) : MoorePath (AddCircle (2 * π)) where
  toFun t := (((ε : ℤ) : ℝ) * Real.arccos (1 - t) : ℝ)
  continuous_toFun := (AddCircle.continuous_mk' _).comp <| continuous_const.mul <|
    Real.continuous_arccos.comp (continuous_const.sub NNReal.continuous_coe)
  length := 2
  apply_of_length_le' t ht := by
    have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [NNReal.coe_ofNat]
    rw [Real.arccos_of_le_neg_one (by linarith), Real.arccos_of_le_neg_one (by norm_num)]

/-- The point of `circleCosHalfPath ε` at time `t` is the angle `ε · arccos (1 - t)`. -/
@[simp]
theorem circleCosHalfPath_apply (ε : ℤˣ) (t : ℝ≥0) :
    circleCosHalfPath ε t = (((ε : ℤ) : ℝ) * Real.arccos (1 - t) : ℝ) :=
  (rfl)

/-- The upper half-circle is at the angle `arccos (1 - t)` at time `t`. -/
theorem circleCosHalfPath_one_apply (t : ℝ≥0) :
    circleCosHalfPath 1 t = (Real.arccos (1 - t) : ℝ) := by
  simp

/-- The lower half-circle is at the angle `-arccos (1 - t)` at time `t`. -/
theorem circleCosHalfPath_neg_one_apply (t : ℝ≥0) :
    circleCosHalfPath (-1) t = (-Real.arccos (1 - t) : ℝ) := by
  simp

/-- The half-circles have length `2`, the drop of the cosine from `1` to `-1`. -/
@[simp]
theorem length_circleCosHalfPath (ε : ℤˣ) : (circleCosHalfPath ε).length = 2 :=
  (rfl)

/-- The half-circles start at the maximum `0` of the cosine. -/
@[simp]
theorem source_circleCosHalfPath (ε : ℤˣ) : (circleCosHalfPath ε).source = 0 := by
  simp [MoorePath.source_def]

/-- The half-circles end at the minimum `π` of the cosine. -/
@[simp]
theorem target_circleCosHalfPath (ε : ℤˣ) : (circleCosHalfPath ε).target = (π : ℝ) := by
  have h : Real.arccos (1 - ((2 : ℝ≥0) : ℝ)) = π := by
    rw [NNReal.coe_ofNat, show (1 : ℝ) - 2 = -1 by norm_num, Real.arccos_neg_one]
  rw [MoorePath.target_def, length_circleCosHalfPath]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [circleCosHalfPath_one_apply, h]
  · -- The circle `AddCircle (2π)` is `Real.Angle`, in which `-π = π`.
    rw [circleCosHalfPath_neg_one_apply, h]
    exact (Real.Angle.coe_neg π).trans Real.Angle.neg_coe_pi

/-- Along each half-circle the cosine decreases at unit speed: at time `t ≤ 2` it is `1 - t`. -/
theorem circleCos_circleCosHalfPath (ε : ℤˣ) {t : ℝ≥0} (ht : t ≤ 2) :
    circleCos (circleCosHalfPath ε t) = 1 - t := by
  have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
  have h := Real.cos_arccos (x := 1 - t) (by linarith [t.coe_nonneg]) (by linarith [t.coe_nonneg])
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [circleCosHalfPath_one_apply, circleCos_coe, h]
  · rw [circleCosHalfPath_neg_one_apply, circleCos_coe, Real.cos_neg, h]

/-- At a time `t ∈ (0, 2)` the two half-circles are at different points. -/
theorem circleCosHalfPath_one_ne_neg_one {t : ℝ≥0} (ht₀ : 0 < t) (ht₂ : t < 2) :
    circleCosHalfPath 1 t ≠ circleCosHalfPath (-1) t := by
  have ht₀' : (0 : ℝ) < t := by exact_mod_cast ht₀
  have ht₂' : (t : ℝ) < 2 := by exact_mod_cast ht₂
  have hpos : 0 < Real.arccos (1 - t) := Real.arccos_pos.2 (by linarith)
  have hlt : Real.arccos (1 - t) < π := Real.arccos_lt_pi.2 (by linarith)
  intro h
  rw [circleCosHalfPath_one_apply, circleCosHalfPath_neg_one_apply] at h
  have := AddCircle.eq_of_coe_eq_of_abs_sub_lt h (by
    rw [sub_neg_eq_add, abs_of_pos (by linarith)]
    linarith)
  linarith

/-- The half-circles are distinguished by their points at time `1`, `π / 2` and `-π / 2`. -/
theorem circleCosHalfPath_apply_one_injective :
    Injective fun ε : ℤˣ ↦ circleCosHalfPath ε 1 := by
  intro ε ε' h
  have hne := circleCosHalfPath_one_ne_neg_one (t := 1) one_pos one_lt_two
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
  exacts [rfl, (hne h).elim, (hne h.symm).elim, rfl]

/-- The point of a half-circle at time `1` lies on the level `0` of the cosine. -/
theorem circleCos_circleCosHalfPath_apply_one (ε : ℤˣ) :
    circleCos (circleCosHalfPath ε 1) = 0 := by
  simpa using circleCos_circleCosHalfPath ε (t := 1) one_le_two

/-! ### Loops along the half-circles -/

/-- **The half-loops.** The Moore loop at `y₀` traced by a map `θ` from the circle along the
half-circle `ε`, when `θ` sends both ends `0` and `π` to `y₀`. -/
noncomputable def circleCosHalfLoop {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (θ : C(AddCircle (2 * π), Y)) (h₀ : θ 0 = y₀) (hπ : θ ((π : ℝ) : AddCircle (2 * π)) = y₀)
    (ε : ℤˣ) : MooreLoopSpace Y y₀ :=
  ⟨(circleCosHalfPath ε).map θ, by rw [MoorePath.source_map, source_circleCosHalfPath, h₀],
    by rw [MoorePath.target_map, target_circleCosHalfPath, hπ]⟩

/-- The Moore path of a half-loop is the half-circle mapped by `θ`. -/
@[simp]
theorem toMoorePath_circleCosHalfLoop {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (θ : C(AddCircle (2 * π), Y)) (h₀ : θ 0 = y₀) (hπ : θ ((π : ℝ) : AddCircle (2 * π)) = y₀)
    (ε : ℤˣ) : (circleCosHalfLoop θ h₀ hπ ε).toMoorePath = (circleCosHalfPath ε).map θ :=
  (rfl)

/-- **The loop once around the circle**: the lower half-circle from `0` to `π`, followed by the
upper half-circle run backwards from `π` to `0`. It goes once around the circle in the direction
of decreasing angles. -/
noncomputable def circleCosLoop : MooreLoopSpace (AddCircle (2 * π)) 0 :=
  ⟨(circleCosHalfPath (-1)).trans (circleCosHalfPath 1).symm
      (by rw [target_circleCosHalfPath, MoorePath.source_symm, target_circleCosHalfPath]),
    by rw [MoorePath.source_trans, source_circleCosHalfPath],
    by rw [MoorePath.target_trans, MoorePath.target_symm, source_circleCosHalfPath]⟩

/-- The Moore path of the loop around the circle is the lower half-circle followed by the upper one
run backwards. -/
@[simp]
theorem toMoorePath_circleCosLoop :
    circleCosLoop.toMoorePath = (circleCosHalfPath (-1)).trans (circleCosHalfPath 1).symm
      (by rw [target_circleCosHalfPath, MoorePath.source_symm, target_circleCosHalfPath]) :=
  (rfl)

/-- **The loop around the circle has winding number one**: in the convention of
`MooreLoopSpace.fundamentalGroupHom`, which sends a Moore loop to the inverse of the class of its
fixed-interval loop, its class is the generator of `π₁(S¹, 0) ≅ ℤ` of winding number `1`. -/
theorem windingNumber_fundamentalGroupHom_circleCosLoop :
    AddCircle.windingNumber (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop) = 1 := by
  -- A lift of the fixed-interval loop: it runs from `0` down to `-π` along the lower half-circle,
  -- and on to `-2π` along the upper one.
  let F : C(unitInterval, ℝ) :=
    ⟨fun s ↦ if (s : ℝ) ≤ 1 / 2 then -Real.arccos (1 - 4 * s) else Real.arccos (4 * s - 3) - 2 * π,
      Continuous.if_le (by fun_prop) (by fun_prop) continuous_subtypeVal continuous_const
        fun s hs ↦ by
          rw [hs]
          norm_num [Real.arccos_neg_one]
          linarith⟩
  have hF : ((↑) : ℝ → AddCircle (2 * π)) ∘ F = circleCosLoop.toPath := by
    funext s
    have hs₁ := unitInterval.le_one s
    have hL : circleCosLoop.toMoorePath.length = 4 := by
      simp only [toMoorePath_circleCosLoop, MoorePath.length_trans, MoorePath.length_symm,
        length_circleCosHalfPath]
      norm_num
    simp only [Function.comp_apply, MooreLoopSpace.toPath_apply, ContinuousMap.coe_mk, F, hL]
    set t := (4 : ℝ≥0) * unitInterval.toNNReal s
    have ht : (t : ℝ) = 4 * s := by simp [t]
    simp only [toMoorePath_circleCosLoop, MoorePath.trans_apply, length_circleCosHalfPath,
      MoorePath.symm_apply]
    have h2 : t ≤ 2 ↔ (s : ℝ) ≤ 1 / 2 := by
      rw [← NNReal.coe_le_coe, ht, NNReal.coe_ofNat]
      constructor <;> intro h <;> linarith
    by_cases h₁ : (s : ℝ) ≤ 1 / 2
    · rw [ite_eq_left h₁, ite_eq_left (h2.2 h₁), circleCosHalfPath_apply, ht]
      norm_num
    · rw [ite_eq_right h₁, ite_eq_right (mt h2.1 h₁), circleCosHalfPath_apply]
      have h2' : (2 : ℝ≥0) ≤ t := (not_le.1 (mt h2.1 h₁)).le
      have h4 : t - 2 ≤ 2 := by
        rw [tsub_le_iff_right, ← NNReal.coe_le_coe, NNReal.coe_add, ht, NNReal.coe_ofNat]
        linarith
      rw [NNReal.coe_sub h4, NNReal.coe_sub h2', ht, NNReal.coe_ofNat,
        show (1 : ℝ) - (2 - (4 * s - 2)) = 4 * s - 3 by ring]
      exact AddCircle.coe_eq_coe_iff_exists_zsmul.2 ⟨-1, by rw [neg_one_zsmul]; push_cast; ring⟩
  have h := AddCircle.windingNumber_eq_div circleCosLoop.toPath F hF
  have hF0 : F 0 = 0 := by simp [F]
  have hF1 : F 1 = -(2 * π) := by norm_num [F]
  rw [hF0, hF1, sub_zero, neg_div, div_self Real.two_pi_pos.ne'] at h
  rw [MooreLoopSpace.fundamentalGroupHom_apply, AddCircle.windingNumber, map_inv, toAdd_inv]
  exact_mod_cast congrArg Neg.neg h

/-- **The two half-loops differ by the loop around the circle.** For a map `θ` from the circle
sending `0` and `π` to `y₀`, the class in `π₁(Y, y₀)` of the loop traced along the lower
half-circle is the image under `θ` of the class of the loop around the circle, times the class of
the loop traced along the upper half-circle. -/
theorem fundamentalGroupHom_circleCosHalfLoop_neg_one {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (θ : C(AddCircle (2 * π), Y)) (h₀ : θ 0 = y₀) (hπ : θ ((π : ℝ) : AddCircle (2 * π)) = y₀) :
    MooreLoopSpace.fundamentalGroupHom y₀ (circleCosHalfLoop θ h₀ hπ (-1)) =
      FundamentalGroup.mapOfEq θ h₀ (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop) *
        MooreLoopSpace.fundamentalGroupHom y₀ (circleCosHalfLoop θ h₀ hπ 1) := by
  have h : circleCosHalfLoop θ h₀ hπ (-1) * (circleCosHalfLoop θ h₀ hπ 1).symm =
      MooreLoopSpace.map θ h₀ circleCosLoop :=
    MooreLoopSpace.ext <| by
      rw [MooreLoopSpace.toMoorePath_mul, MooreLoopSpace.toMoorePath_map]
      simp only [toMoorePath_circleCosLoop, MooreLoopSpace.toMoorePath_symm,
        toMoorePath_circleCosHalfLoop,
        MoorePath.map_trans, MoorePath.map_symm]
  rw [← MooreLoopSpace.fundamentalGroupHom_map, ← h, map_mul,
    MooreLoopSpace.fundamentalGroupHom_symm, inv_mul_cancel_right]

/-- The maximum and the minimum of the cosine are distinct points of the circle. -/
private theorem zero_ne_coe_pi : (0 : AddCircle (2 * π)) ≠ (π : ℝ) :=
  fun h ↦ Real.Angle.pi_ne_zero h.symm

/-! ### The trajectories from the maximum to the minimum -/

namespace IsAdaptedPseudoGradient

variable {X : (x : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) x}
  (hX : IsAdaptedPseudoGradient circleCos X) {ι : Type*} {c : ι → ℝ}

/-- **Every broken trajectory from the maximum to the minimum of the cosine is a half-circle.**
For every pseudo-gradient adapted to the cosine on the circle, the Moore path of a recorded broken
trajectory from `0` to `π`, parametrized by the values of the cosine, is one of the two
half-circles `circleCosHalfPath ε`. -/
theorem exists_morseLevelPath_eq_circleCosHalfPath
    (hdense : Ioo (circleCos ((π : ℝ) : AddCircle (2 * π))) (circleCos 0) ⊆ closure (range c))
    (w : hX.morseBrokenTrajectoryRecords 0 ((π : ℝ) : AddCircle (2 * π)) c) :
    ∃ ε : ℤˣ, hX.morseLevelPath isMorse_circleCos hdense w = circleCosHalfPath ε := by
  set γ := hX.morseLevelPath isMorse_circleCos hdense w
  -- Up to time `2`, the cosine takes the value `1 - t` at time `t`, so `γ t` is one of the two
  -- points of the half-circles at time `t`.
  have hor (t : ℝ≥0) (ht : t ≤ 2) :
      γ t = circleCosHalfPath 1 t ∨ γ t = circleCosHalfPath (-1) t := by
    have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
    have hval : circleCos (γ t) = 1 - t := by
      rw [morseLevelPath_apply, hX.apply_morseLevelPoint w.property
        (by rw [circleCos_zero, circleCos_pi]; constructor <;> linarith [t.coe_nonneg]),
        circleCos_zero]
    simpa using eq_or_eq_neg_arccos_of_circleCos_eq hval (by linarith) (by linarith [t.coe_nonneg])
  -- On the connected interval `(0, 2)`, `γ` follows one half-circle throughout.
  have hcont := γ.continuous
  obtain ⟨ε, hε⟩ : ∃ ε : ℤˣ, Ioo 0 2 ⊆ {t | γ t = circleCosHalfPath ε t} := by
    obtain h | h := isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_Ioo
      {t | γ t = circleCosHalfPath 1 t} {t | γ t = circleCosHalfPath (-1) t}
      (isClosed_eq hcont (circleCosHalfPath 1).continuous)
      (isClosed_eq hcont (circleCosHalfPath (-1)).continuous)
      (fun t ht ↦ hor t ht.2.le)
      (eq_empty_of_forall_notMem fun t ⟨ht, h₁, h₂⟩ ↦
        circleCosHalfPath_one_ne_neg_one ht.1 ht.2 (h₁.symm.trans h₂))
    exacts [⟨1, h⟩, ⟨-1, h⟩]
  -- At time `0` both start at `0`, and from time `2` on both are stopped at `π`.
  have hL : γ.length = 2 := by
    rw [length_morseLevelPath, circleCos_zero, circleCos_pi]
    norm_num
  refine ⟨ε, MoorePath.ext (hL.trans (length_circleCosHalfPath ε).symm) fun t ↦ ?_⟩
  rcases eq_or_ne t 0 with rfl | ht₀
  · rw [← MoorePath.source_def, ← MoorePath.source_def, source_morseLevelPath,
      source_circleCosHalfPath]
  rcases lt_or_ge t 2 with ht₂ | ht₂
  · exact hε ⟨pos_iff_ne_zero.2 ht₀, ht₂⟩
  · rw [γ.apply_of_length_le (hL.trans_le ht₂),
      MoorePath.apply_of_length_le _ (by simpa using ht₂), target_morseLevelPath,
      target_circleCosHalfPath]

/-- **The midpoints of the half-circles lie on trajectories from `0` to `π`.** For every
pseudo-gradient adapted to the cosine, the points `± π / 2` flow down to the minimum `π` and come
from the maximum `0`: along their orbits the cosine stays below, respectively above, its value
`0` there, while the only critical points are `0` and `π`. -/
theorem circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet (ε : ℤˣ) :
    circleCosHalfPath ε 1 ∈
      hX.flow.unstableSet 0 ∩ hX.flow.stableSet ((π : ℝ) : AddCircle (2 * π)) := by
  have hcont : Continuous circleCos := (contMDiff_circleCos (n := 0)).continuous
  have hanti (t : ℝ) (ht : t ≤ 0) : circleCos (hX.flow t (circleCosHalfPath ε 1)) ≥ 0 := by
    simpa only [Flow.map_zero_apply, circleCos_circleCosHalfPath_apply_one] using
      hX.antitone_flow (circleCosHalfPath ε 1) ht
  have hanti' (t : ℝ) (ht : 0 ≤ t) : circleCos (hX.flow t (circleCosHalfPath ε 1)) ≤ 0 := by
    simpa only [Flow.map_zero_apply, circleCos_circleCosHalfPath_apply_one] using
      hX.antitone_flow (circleCosHalfPath ε 1) ht
  constructor
  · obtain ⟨q, hq, hzq⟩ := hX.exists_mem_unstableSet (circleCosHalfPath ε 1)
    rcases mem_criticalPoints_circleCos_iff.1 (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq) with
      rfl | rfl
    · exact hzq
    · -- The cosine is at least `0` along the backward orbit, so its limit is not `π`.
      have h := ge_of_tendsto ((hcont.tendsto _).comp (Flow.mem_unstableSet.1 hzq))
        (eventually_atBot.2 ⟨0, hanti⟩)
      rw [circleCos_pi] at h
      norm_num at h
  · obtain ⟨q, hq, hzq⟩ := hX.exists_mem_stableSet (circleCosHalfPath ε 1)
    rcases mem_criticalPoints_circleCos_iff.1 (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq) with
      rfl | rfl
    · -- The cosine is at most `0` along the forward orbit, so its limit is not `0`.
      have h := le_of_tendsto ((hcont.tendsto _).comp (Flow.mem_stableSet.1 hzq))
        (eventually_atTop.2 ⟨0, hanti'⟩)
      rw [circleCos_zero] at h
      norm_num at h
    · exact hzq

variable (c)

/-- The time at which the trajectory through the midpoint of the half-circle `ε` crosses the
level `c i`. -/
private noncomputable def circleCosCrossingTime (ε : ℤˣ)
    (i : c ⁻¹' Ioo (circleCos ((π : ℝ) : AddCircle (2 * π))) (circleCos 0)) : ℝ :=
  (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet zero_ne_coe_pi
    (hX.circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet ε) i.property.1
    i.property.2).exists.choose

private theorem circleCos_flow_circleCosCrossingTime (ε : ℤˣ)
    (i : c ⁻¹' Ioo (circleCos ((π : ℝ) : AddCircle (2 * π))) (circleCos 0)) :
    circleCos (hX.flow (circleCosCrossingTime hX c ε i) (circleCosHalfPath ε 1)) = c i :=
  (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet zero_ne_coe_pi
    (hX.circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet ε) i.property.1
    i.property.2).exists.choose_spec

/-- **The trajectory through the half-circle `ε`**: the point of the trajectory space from `0` to
`π` which records, on the levels of `c` strictly between `-1` and `1`, the trajectory through the
midpoint `ε π / 2` of the half-circle `ε`. -/
noncomputable def circleCosTrajectory (ε : ℤˣ) :
    hX.morseBrokenTrajectorySpace c 0 ((π : ℝ) : AddCircle (2 * π)) :=
  ⟨fun i ↦ hX.flow (circleCosCrossingTime hX c ε i) (circleCosHalfPath ε 1),
    mem_morseBrokenTrajectorySpace.2 ⟨zero_ne_coe_pi,
    hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 circleCosMaxCrit.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 circleCosMinCrit.property) zero_ne_coe_pi _
      (hX.mem_morseTrajectoryRecords.2
        ⟨_, hX.circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet ε, fun i ↦
          ⟨circleCos_flow_circleCosCrossingTime hX c ε i, _, rfl⟩⟩)⟩⟩

variable {c}
  (hdense : Ioo (circleCos ((π : ℝ) : AddCircle (2 * π))) (circleCos 0) ⊆ closure (range c))

/-- **The Moore path of the trajectory through the half-circle `ε` is that half-circle.** -/
theorem morseLevelPath_circleCosTrajectory (ε : ℤˣ) :
    hX.morseLevelPath isMorse_circleCos
        (subset_closure_range_domRestrict_preimage isOpen_Ioo hdense)
        (inclusion (morseBrokenTrajectorySpace_subset _ _) (hX.circleCosTrajectory c ε)) =
      circleCosHalfPath ε := by
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo hdense
  obtain ⟨ε', h⟩ := hX.exists_morseLevelPath_eq_circleCosHalfPath hdense'
    (inclusion (morseBrokenTrajectorySpace_subset _ _) (hX.circleCosTrajectory c ε))
  rw [h, circleCosHalfPath_apply_one_injective (a₁ := ε') (a₂ := ε) ?_]
  -- At time `1` the path is on the level `0`, at the midpoint of the half-circle `ε`.
  have hz := hX.circleCosHalfPath_apply_one_mem_unstableSet_inter_stableSet ε
  have hmid := hX.morseLevelPoint_eq isMorse_circleCos hdense' (k := 1)
    (x := ![0, ((π : ℝ) : AddCircle (2 * π))]) (z := ![circleCosHalfPath ε 1])
    (m := circleCosHalfPath ε 1) rfl rfl
    (fun j ↦ by
      fin_cases j
      exacts [mem_criticalPoints_iff_mfderiv_eq_zero.1 circleCosMaxCrit.property,
        mem_criticalPoints_iff_mfderiv_eq_zero.1 circleCosMinCrit.property])
    (fun j ↦ by fin_cases j; exact zero_ne_coe_pi) (fun j ↦ by fin_cases j; exact hz)
    (w := (hX.circleCosTrajectory c ε : c ⁻¹' Ioo _ _ → AddCircle (2 * π)))
    (fun i ↦ ⟨circleCos_flow_circleCosCrossingTime hX c ε i, 0, _, rfl⟩)
    (.inr ⟨0, 0, Flow.map_zero_apply ..⟩)
  rw [circleCos_circleCosHalfPath_apply_one] at hmid
  have h1 := congrArg (· 1) h
  simp only [morseLevelPath_apply, NNReal.coe_one, circleCos_zero, sub_self] at h1
  exact h1.symm.trans hmid

include hdense in
/-- **The trajectory space from the maximum to the minimum of the cosine has exactly two points**:
for every pseudo-gradient adapted to the cosine and levels dense in `(-1, 1)`, the trajectories
through the two half-circles are distinct and are all of its points. -/
theorem bijective_circleCosTrajectory : Bijective (hX.circleCosTrajectory c) := by
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo hdense
  refine ⟨fun ε ε' h ↦ ?_, fun w ↦ ?_⟩
  · have := congrArg (fun w ↦ hX.morseLevelPath isMorse_circleCos hdense'
      (inclusion (morseBrokenTrajectorySpace_subset _ _) w)) h
    simp only [hX.morseLevelPath_circleCosTrajectory hdense] at this
    exact circleCosHalfPath_apply_one_injective (congrArg (· 1) this)
  · obtain ⟨ε, hε⟩ := hX.exists_morseLevelPath_eq_circleCosHalfPath hdense'
      (inclusion (morseBrokenTrajectorySpace_subset _ _) w)
    refine ⟨ε, inclusion_injective (morseBrokenTrajectorySpace_subset _ _) <|
      hX.morseLevelPath_injective isMorse_circleCos hdense' ?_⟩
    rw [hX.morseLevelPath_circleCosTrajectory hdense, hε]

/-! ### The Barraud–Cornea cocycle -/

variable {Y : Type u} [TopologicalSpace Y] {θ : C(AddCircle (2 * π), Y)} {y₀ : Y}
  {R : Type u} [CommRing R]
  {ind : criticalPoints 𝓘(ℝ) circleCos → ℤ}

/-- **The entry of the Barraud–Cornea cocycle of the cosine from the maximum to the minimum, in
degree zero.** For every pseudo-gradient adapted to the cosine on the circle and every twisting
chain system `S` on its trajectory spaces, the image in the group ring `R[π₁(Y, y₀)]` of the entry
at `(0, π)` is `∑_ε r_ε [θ ∘ γ_ε]`, the sum over the two half-circles `γ_ε` of the classes of
their loops `θ ∘ γ_ε`, weighted by the coefficients `r_ε` of the two trajectories in the
`0`-chain of `S`. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ) circleCos,
      Ioo (circleCos y) (circleCos x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ) circleCos, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ) circleCos), c i ≠ circleCos x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
        circleCosMaxCrit circleCosMinCrit) =
      ∑ ε : ℤˣ, MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
        (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) ε))
        (NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
          (hX.circleCosTrajectory c ε)) := by
  have hbij := hX.bijective_circleCosTrajectory (hdense circleCosMaxCrit circleCosMinCrit)
  rw [loopChainToGroupAlgebra_barraudCorneaCocycle_m]
  refine (Finsupp.sum_of_support_subset _ (s := Finset.univ.map ⟨_, hbij.1⟩)
      (fun w _ ↦ Finset.mem_map.2 ⟨_, Finset.mem_univ _, (hbij.2 w).choose_spec⟩) _
      (fun _ _ ↦ MonoidAlgebra.single_zero _)).trans ?_
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  congr 2
  exact MooreLoopSpace.ext <| (toMoorePath_morseLoopEvaluation ..).trans <|
    (congrArg (MoorePath.map θ) (hX.morseLevelPath_circleCosTrajectory
      (hdense circleCosMaxCrit circleCosMinCrit) ε)).trans (toMoorePath_circleCosHalfLoop ..).symm

/-- **The degree-zero entry of the Barraud–Cornea cocycle of the cosine is
`r₊ [θ ∘ γ₊] + r₋ [θ ∘ γ₋]`**: the sum of the classes in `π₁(Y, y₀)` of the loops traced by `θ`
along the upper and the lower half-circle, weighted by the coefficients `r₊` and `r₋` of the two
trajectories from the maximum to the minimum in the `0`-chain of `S`. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_add_single
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ) circleCos,
      Ioo (circleCos y) (circleCos x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ) circleCos, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ) circleCos), c i ≠ circleCos x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
        circleCosMaxCrit circleCosMinCrit) =
      MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) 1))
          (NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
            (hX.circleCosTrajectory c 1)) +
        MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) (-1)))
          (NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
            (hX.circleCosTrajectory c (-1))) := by
  rw [hX.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos hdense hθ hc S,
    Fintype.sum_eq_add 1 (-1) (by decide) fun ε hε ↦
      ((Int.units_eq_one_or ε).elim hε.1 hε.2).elim]

/-- **The degree-zero entry of the Barraud–Cornea cocycle of the cosine is `[θ ∘ γ₊] + [θ ∘ γ₋]`**
when `S` gives both trajectories from the maximum to the minimum the coefficient `1`, as the
mod-two fundamental chain of the two-point trajectory space does: the sum of the classes in
`π₁(Y, y₀)` of the loops traced by `θ` along the upper and the lower half-circle. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_of_forall_eq_one
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ) circleCos,
      Ioo (circleCos y) (circleCos x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ) circleCos, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ) circleCos), c i ≠ circleCos x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0) w
      = 1) :
    loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
        circleCosMaxCrit circleCosMinCrit) =
      MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) 1)) 1 +
        MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) (-1))) 1 := by
  rw [hX.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_add_single hdense hθ hc
    S]
  exact congrArg₂ (· + ·) (congrArg _ (hS _)) (congrArg _ (hS _))

/-- **The degree-zero entry of the Barraud–Cornea cocycle of the cosine is `(1 + t) g`.** When `S`
gives both trajectories from the maximum to the minimum the coefficient `1`, the image of the
entry at `(0, π)` in `R[π₁(Y, y₀)]` is `(1 + t) g`, where `g` is the class of the loop traced by
`θ` along the upper half-circle and `t` is the image under `θ` of the class of the loop once around
the circle, of winding number `1` (`TauCeti.windingNumber_fundamentalGroupHom_circleCosLoop`). -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_mul
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ) circleCos,
      Ioo (circleCos y) (circleCos x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ) circleCos, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ) circleCos), c i ≠ circleCos x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0) w
      = 1) :
    loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
        circleCosMaxCrit circleCosMinCrit) =
      (1 + MonoidAlgebra.single (FundamentalGroup.mapOfEq θ (hθ circleCosMaxCrit)
          (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop)) 1) *
        MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (circleCosHalfLoop θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit) 1)) 1 := by
  rw [hX.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_of_forall_eq_one hdense hθ hc S
    hS, fundamentalGroupHom_circleCosHalfLoop_neg_one θ (hθ circleCosMaxCrit) (hθ circleCosMinCrit),
    add_mul, one_mul, MonoidAlgebra.single_mul_single, mul_one]
  -- The two sides differ only in the base point `0 = ↑circleCosMaxCrit` of `mapOfEq`.
  rfl

end IsAdaptedPseudoGradient

end TauCeti
