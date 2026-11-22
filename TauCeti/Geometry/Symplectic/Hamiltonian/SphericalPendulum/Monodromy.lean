/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.PeriodLattice
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.DiscreteSubset

/-!
# The Hamiltonian monodromy of the spherical pendulum

The energy `H` and the vertical angular momentum `J` of the spherical pendulum generate an action
of `ℝ²` on its phase space, and above the curve of relative equilibria the stabilizer of every
point of the fibre `F⁻¹(h, j)` of `F = (H, J)` is the **period lattice** spanned by

* `γ₂ = (T(h, j), -Θ(h, j))`, one oscillation of the height under the energy flow followed by the
  rotation back by the rotation angle, and
* `γ_J = (0, 2π)`, one turn of the rotation flow

(`TauCeti.hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure`), where `T` is the
period of the height and `Θ` the rotation angle. This file transports the period lattice once
around the counterclockwise circle `γ(t) = (1 + r cos t, r sin t)`, `t ∈ [0, 2π]`, of radius
`r > 0` about the focus–focus value `(1, 0)` of `F`, assuming that off the axis `j = 0` it runs
strictly above the curve of relative equilibria, as every circle of radius `r ≤ 1` does
(`TauCeti.mem_sphericalPendulumTurningPointDomain_of_le_one`). It computes the **monodromy** of the
pendulum: any continuous continuation of `γ₂` comes back as `γ₂ + γ_J`, while `γ_J` comes back as
itself, so in the basis `(γ_J, γ₂)` the monodromy matrix, whose columns are the transported basis
vectors, is `[[1, 1], [0, 1]]`.

Precisely, let `v` be continuous on `[0, 2π]`, with `v(t)` in the period lattice over `γ(t)` at
every `t` with `γ(t)` off the axis `j = 0`, that is, with `sin t ≠ 0`. Then there is a single
integer `m`, the `γ₂`-coordinate of `v`, with energy component `v(t)₀ = m T(γ(t))` at all these
times, and

`v(2π) = v(0) + m (0, 2π)`

(`TauCeti.exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`, and
`TauCeti.exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum` for the
stabilizers themselves). These statements constrain every continuous section of the period
lattice along the circle; the existence of the continuation of `γ₂` across the axis, where the
explicit description of the period lattice above does not apply, is not proved here.

The proof reads off both coordinates. On each of the two open half-circles the integer
`v(t)₀ / T(γ(t))` is constant, since `T` is continuous and positive there
(`TauCeti.continuousOn_sphericalPendulumPeriod`). The two constants agree because the period is even
in `j` (`TauCeti.sphericalPendulumPeriod_neg_right`), so the values of `T ∘ γ` at `π ± s` coincide,
and stays at least `2π / √(2 (4 + r))` along the circle
(`TauCeti.two_mul_pi_div_sqrt_le_sphericalPendulumPeriod`): a jump of the integer at `t = π` would
make `v(t)₀` jump. The same symmetry at `t = 0` and `t = 2π` gives `v(2π)₀ = v(0)₀`. The second
coordinate `v(t)₁` agrees modulo `2π` with `-m Θ(γ(t))`, and the one-sided limits of `Θ` at the
axis, `±2π` at `(1 + r, 0)` and `±π` at `(1 - r, 0)`, make every such continuous lift rise by
`2πm` once around the circle
(`TauCeti.sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle`).

The monodromy is nontrivial, so the period lattice has no continuous basis along the circle. A
continuous section of the period lattice that returns to its initial value after one turn has
`m = 0`, so its energy component vanishes
(`TauCeti.apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`), and two such
sections never span the period lattice at a point of the circle off the axis
(`TauCeti.closure_pair_ne_hamiltonianFlowStabilizer_sphericalPendulum`), whose vector `γ₂` has
positive energy component. This is the obstruction, found by Duistermaat, to global action-angle
coordinates for the spherical pendulum around its unstable equilibrium.

## Main results

* `TauCeti.exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`: a continuous family of
  vectors of the explicit lattices along the circle comes back shifted by `m γ_J`.
* `TauCeti.exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`: the same for
  the period lattices, the stabilizers of the flow action.
* `TauCeti.apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`: a section of the
  period lattice along the circle returning to its initial value has zero energy component.
* `TauCeti.closure_pair_ne_hamiltonianFlowStabilizer_sphericalPendulum`: two such sections do not
  span the period lattice.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the monodromy of the spherical pendulum).
* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum, its rotation number and monodromy).
* K. Efstathiou, A. Giacobbe, P. Mardešić and D. Sugny, *Rotation forms and local Hamiltonian
  monodromy*, arXiv:1608.01579, Sections II–III.
-/

public section

open Set Filter Real
open scoped Topology

namespace TauCeti

section Monodromy

variable {r : ℝ}

/-- On a preconnected set of times at which the circle `γ(t) = (1 + r cos t, r sin t)` lies in the
domain of the period, a continuous function whose values are integer multiples of the period
`T(γ(t))` is one fixed integer multiple of it, since `T ∘ γ` is continuous and positive there. -/
private theorem exists_eq_intCast_mul_sphericalPendulumPeriod {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {f : ℝ → ℝ} (hf : ContinuousOn f s)
    (hfT : ∀ t ∈ s, ∃ m : ℤ, f t = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) :
    ∃ m : ℤ, ∀ t ∈ s, f t = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := by
  have hT : ∀ t ∈ s, sphericalPendulumPeriod (1 + r * cos t) (r * sin t) ≠ 0 := fun t ht ↦ by
    obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 (hγ t ht)
    exact (sphericalPendulumPeriod_pos hj hz hV).ne'
  have hTc : ContinuousOn (fun t ↦ sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) s :=
    continuousOn_sphericalPendulumPeriod.comp
      (by fun_prop : Continuous fun t : ℝ ↦ (1 + r * cos t, r * sin t)).continuousOn
      fun t ht ↦ hγ t ht
  -- The ratio `f / (T ∘ γ)` is continuous with values in the discrete set `ℤ ⊆ ℝ`.
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := hs.eqOn_const_of_mapsTo
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range (hf.div hTc hT)
    (fun t ht ↦ by
      obtain ⟨m, hm⟩ := hfT t ht
      exact ⟨m, by rw [Pi.div_apply, hm, mul_div_cancel_right₀ _ (hT t ht)]⟩)
    (range_nonempty _)
  exact ⟨m, fun t ht ↦ (div_eq_iff (hT t ht)).1 (hm ht)⟩

/-- The period is symmetric along the circle `γ(t) = (1 + r cos t, r sin t)` under the reflection
`t ↦ 2π - t` across the axis `j = 0`, since it is even in `j`. -/
private theorem sphericalPendulumPeriod_circle_two_mul_pi_sub (t : ℝ) :
    sphericalPendulumPeriod (1 + r * cos (2 * π - t)) (r * sin (2 * π - t)) =
      sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := by
  rw [cos_two_pi_sub, sin_two_pi_sub, mul_neg, sphericalPendulumPeriod_neg_right]

/-- Along the circle `γ(t) = (1 + r cos t, r sin t)`, `r > 0`, the period `T(γ(t))` is at least
`2π / √(2 (4 + r))` wherever `γ(t)` lies above the curve of relative equilibria off the axis, since
the energy `1 + r cos t` is at most `1 + r` there
(`TauCeti.two_mul_pi_div_sqrt_le_sphericalPendulumPeriod`) and exceeds `-1`, the infimum of the
effective potential. -/
private theorem two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_circle (hr : 0 < r) {t : ℝ}
    (hγ : (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain) :
    2 * π / √(2 * (4 + r)) ≤ sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := by
  obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 hγ
  have hh : -1 < 1 + r * cos t := by
    rw [sphericalPendulumEffectivePotential_def] at hV
    have : 0 ≤ (r * sin t) ^ 2 / (2 * (1 - z ^ 2)) :=
      div_nonneg (sq_nonneg _) (by nlinarith [hz.1, hz.2])
    linarith [hz.1]
  exact (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by linarith))
    (Real.sqrt_le_sqrt (by nlinarith [cos_le_one t]))).trans
    (two_mul_pi_div_sqrt_le_sphericalPendulumPeriod hj hz hV)

/-- The times `c + σ s`, for `s ∈ (0, π)`, tend to `c` within `[0, 2π]` as `s → 0⁺`, when they
lie in `[0, 2π]`. -/
private theorem tendsto_add_mul_nhdsGT {c σ : ℝ} (hcs : ∀ s ∈ Ioo 0 π, c + σ * s ∈ Icc 0 (2 * π)) :
    Tendsto (fun s ↦ c + σ * s) (𝓝[>] 0) (𝓝[Icc 0 (2 * π)] c) :=
  tendsto_nhdsWithin_iff.2 ⟨((by fun_prop : Continuous fun s : ℝ ↦ c + σ * s).tendsto' 0 c
    (by simp)).mono_left nhdsWithin_le_nhds, Filter.eventually_of_mem (Ioo_mem_nhdsGT pi_pos) hcs⟩

/-- **No jump across `t = π`.** If a function continuous at `π` within `[0, 2π]` is `m₁ T(γ(t))` on
the upper half-circle `(0, π)` and `m₂ T(γ(t))` on the lower half-circle `(π, 2π)`, then
`m₁ = m₂`. At `π ± s` the period takes the same value, at least `2π / √(2 (4 + r))`, so a jump of
the integer would make the function jump. -/
private theorem eq_of_forall_eq_intCast_mul_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {f : ℝ → ℝ} (hf : ContinuousWithinAt f (Icc 0 (2 * π)) π) {m₁ m₂ : ℤ}
    (h₁ : ∀ t ∈ Ioo 0 π, f t = m₁ * sphericalPendulumPeriod (1 + r * cos t) (r * sin t))
    (h₂ : ∀ t ∈ Ioo π (2 * π), f t = m₂ * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) :
    m₁ = m₂ := by
  have hpi : 0 < π := pi_pos
  have hg := (hf.tendsto.comp (tendsto_add_mul_nhdsGT (σ := 1) fun s hs ↦
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩)).sub
    (hf.tendsto.comp (tendsto_add_mul_nhdsGT (σ := -1) fun s hs ↦
      ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩))
  rw [sub_self] at hg
  have hc : 0 < 2 * π / √(2 * (4 + r)) := by positivity
  have hle : ∀ s ∈ Ioo 0 π,
      |((m₂ : ℝ) - m₁)| * (2 * π / √(2 * (4 + r))) ≤ |f (π + 1 * s) - f (π + -1 * s)| := by
    intro s hs
    have hplus : π + 1 * s ∈ Ioo π (2 * π) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hminus : π + -1 * s ∈ Ioo 0 π := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hsym := sphericalPendulumPeriod_circle_two_mul_pi_sub (r := r) (π + -1 * s)
    rw [show 2 * π - (π + -1 * s) = π + 1 * s by ring] at hsym
    have hT := two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_circle hr
      (hγ _ (sin_pos_of_pos_of_lt_pi hminus.1 hminus.2).ne')
    rw [h₂ _ hplus, h₁ _ hminus, hsym, ← sub_mul, abs_mul, abs_of_pos (hc.trans_le hT)]
    exact mul_le_mul_of_nonneg_left hT (abs_nonneg _)
  have h0 := ge_of_tendsto hg.abs (Filter.eventually_of_mem (Ioo_mem_nhdsGT hpi) hle)
  rw [abs_zero] at h0
  have : ((m₂ : ℝ) - m₁) = 0 :=
    abs_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_left h0 hc) (abs_nonneg _))
  exact_mod_cast (sub_eq_zero.1 this).symm

/-- A function continuous on `[0, 2π]` whose values off the axis are integer multiples of the period
`T(γ(t))` is one fixed integer multiple of it: the integer is constant on each open half-circle
and does not jump at `t = π`. -/
private theorem exists_forall_eq_intCast_mul_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (2 * π)))
    (hfT : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      ∃ m : ℤ, f t = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) :
    ∃ m : ℤ, ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      f t = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := by
  have hpi : 0 < π := pi_pos
  have hIcc₁ : Ioo 0 π ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨ht.1.le, by linarith [ht.2]⟩
  have hIcc₂ : Ioo π (2 * π) ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨by linarith [ht.1], ht.2.le⟩
  have hsin₁ : ∀ t ∈ Ioo 0 π, sin t ≠ 0 := fun t ht ↦ (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hsin₂ : ∀ t ∈ Ioo π (2 * π), sin t ≠ 0 := fun t ht ↦
    (sin_neg_of_pi_lt_of_lt_two_pi ht.1 ht.2).ne
  obtain ⟨m₁, hm₁⟩ := exists_eq_intCast_mul_sphericalPendulumPeriod isPreconnected_Ioo
    (fun t ht ↦ hγ t (hsin₁ t ht)) (hf.mono hIcc₁) fun t ht ↦ hfT t (hIcc₁ ht) (hsin₁ t ht)
  obtain ⟨m₂, hm₂⟩ := exists_eq_intCast_mul_sphericalPendulumPeriod isPreconnected_Ioo
    (fun t ht ↦ hγ t (hsin₂ t ht)) (hf.mono hIcc₂) fun t ht ↦ hfT t (hIcc₂ ht) (hsin₂ t ht)
  obtain rfl := eq_of_forall_eq_intCast_mul_sphericalPendulumPeriod hr hγ
    (hf π ⟨hpi.le, by linarith⟩) hm₁ hm₂
  refine ⟨m₁, fun t ht hs ↦ ?_⟩
  rcases lt_trichotomy t π with htπ | rfl | htπ
  · exact hm₁ t ⟨ht.1.lt_of_ne (by rintro rfl; simp at hs), htπ⟩
  · simp at hs
  · exact hm₂ t ⟨htπ, ht.2.lt_of_ne (by rintro rfl; simp at hs)⟩

/-- A function continuous on `[0, 2π]` that is a fixed integer multiple of the period `T(γ(t))` off
the axis takes the same value at `0` and `2π`, since `T ∘ γ` takes the same value at `s` and
`2π - s`. -/
private theorem apply_two_mul_pi_eq_apply_zero_of_eq_intCast_mul {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * π))) {m : ℤ}
    (hfT : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      f t = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) :
    f (2 * π) = f 0 := by
  have hpi : 0 < π := pi_pos
  refine tendsto_nhds_unique ((hf _ ⟨by linarith, le_rfl⟩).tendsto.comp
    (tendsto_add_mul_nhdsGT (σ := -1) fun s hs ↦ ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩))
    (((hf _ ⟨le_rfl, by linarith⟩).tendsto.comp (tendsto_add_mul_nhdsGT (σ := 1) fun s hs ↦
      ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩)).congr' ?_)
  refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hpi) fun s hs ↦ ?_
  have hs₁ : 0 + 1 * s ∈ Icc 0 (2 * π) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hs₂ : 2 * π + -1 * s ∈ Icc 0 (2 * π) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsin : sin s ≠ 0 := (sin_pos_of_pos_of_lt_pi hs.1 hs.2).ne'
  have hsin₁ : sin (0 + 1 * s) ≠ 0 := by simpa using hsin
  have hsin₂ : sin (2 * π + -1 * s) ≠ 0 := by
    rwa [show 2 * π + -1 * s = 2 * π - s by ring, sin_two_pi_sub, neg_ne_zero]
  simp only [Function.comp_apply]
  rw [hfT _ hs₁ hsin₁, hfT _ hs₂ hsin₂, show 2 * π + -1 * s = 2 * π - (0 + 1 * s) by ring,
    sphericalPendulumPeriod_circle_two_mul_pi_sub]

/-- **The monodromy of the explicit period lattices.** Let `γ(t) = (1 + r cos t, r sin t)`, with
`r > 0`, be the counterclockwise circle about the focus–focus value `(1, 0)`, running above the
curve of relative equilibria off the axis `j = 0`, and let `v` be continuous on `[0, 2π]` with
`v(t)` in the lattice spanned by `(T(γ(t)), -Θ(γ(t)))` and `(0, 2π)` whenever `sin t ≠ 0`. Then
for one integer `m` the energy component of `v(t)` is `m T(γ(t))` at all these times, and after
one turn `v(2π) = v(0) + m (0, 2π)`. So transport around the circle fixes `(0, 2π)`, and any
continuous continuation of `(T, -Θ)` (the case `m = 1`) returns as `(T, -Θ) + (0, 2π)`. -/
theorem exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → v t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]}) :
    ∃ m : ℤ, (∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
        v t 0 = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) ∧
      v (2 * π) = v 0 + m • ![0, 2 * π] := by
  -- The coordinates of `v(t)` in the basis `(T, -Θ)`, `(0, 2π)`.
  have hcoord : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → ∃ m n : ℤ,
      v t 0 = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t) ∧
      v t 1 = -(m * sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)) + n * (2 * π) := by
    intro t ht hs
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.1 (hvΛ t ht hs)
    exact ⟨m, n, by simp [← hmn], by simp [← hmn]⟩
  have hv₀ : ContinuousOn (fun t ↦ v t 0) (Icc 0 (2 * π)) :=
    (continuous_apply 0).comp_continuousOn hv
  -- The `(T, -Θ)`-coordinate `m` is the same at all times, so the energy component returns.
  obtain ⟨m, hm⟩ := exists_forall_eq_intCast_mul_sphericalPendulumPeriod hr hγ hv₀
    fun t ht hs ↦ (hcoord t ht hs).imp fun _ ⟨_, h, _⟩ ↦ h
  refine ⟨m, hm, ?_⟩
  have hend₀ : v (2 * π) 0 = v 0 0 := apply_two_mul_pi_eq_apply_zero_of_eq_intCast_mul hv₀ hm
  -- The rotation component is a lift of `-m Θ ∘ γ` modulo `2π`, so it rises by `2πm`.
  have hend₁ : v (2 * π) 1 - v 0 1 = -(((-m : ℤ) : ℝ) * (2 * π)) :=
    sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle hr
      hγ (-m)
      (L := fun t ↦ v t 1) ((continuous_apply 1).comp_continuousOn hv) fun t ht hs ↦ by
        obtain ⟨m', n, h₀, h₁⟩ := hcoord t ht hs
        obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 (hγ t hs)
        have hmm : (m' : ℝ) = m := mul_right_cancel₀ (sphericalPendulumPeriod_pos hj hz hV).ne'
          (h₀.symm.trans (hm t ht hs))
        rw [h₁, hmm, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
        exact ⟨n, by push_cast; ring⟩
  ext i
  fin_cases i
  · simp [hend₀]
  · push_cast at hend₁
    simp only [Fin.mk_one, Fin.isValue, Matrix.smul_cons, smul_zero, zsmul_eq_mul,
      Matrix.smul_empty, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith

/-- **The monodromy of the spherical pendulum.** Let `γ(t) = (1 + r cos t, r sin t)`, with
`r > 0`, be the counterclockwise circle about the focus–focus value `(1, 0)` of the
energy–momentum map `F = (H, J)`, running above the curve of relative equilibria off the axis
`j = 0` (as it does for `r ≤ 1`), let `x(t)` be a point of the fibre `F⁻¹(γ(t))` for every `t` with
`sin t ≠ 0`, and let `v` be continuous on `[0, 2π]` with `v(t)` in the period lattice, the
stabilizer of `x(t)` under the flow action of `F`, at all these times. Then for one integer `m`,
the `γ₂`-coordinate of `v`, the energy component of `v(t)` is `m T(γ(t))`, and after one turn
`v(2π) = v(0) + m (0, 2π)`. In the basis `γ_J = (0, 2π)`, `γ₂ = (T, -Θ)` of the period lattice,
transport fixes `γ_J`, and any continuous continuation of `γ₂` (the case `m = 1`) returns as
`γ₂ + γ_J`; were such a continuation to exist, the monodromy matrix would be `[[1, 1], [0, 1]]`.
The existence of this continuation across the axis is not proved here. -/
theorem exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {x : ℝ → sphericalPendulumPhaseSpace}
    (hx : ∀ t, sin t ≠ 0 → sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
    {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      v t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t)) :
    ∃ m : ℤ, (∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
        v t 0 = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) ∧
      v (2 * π) = v 0 + m • ![0, 2 * π] :=
  exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ hv fun t ht hs ↦ by
    obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1
      (hγ t hs)
    rw [← hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure hj hz hV (hx t hs)]
    exact hvΛ t ht hs

/-- **Sections of the period lattice returning after one turn.** Along the circle
`γ(t) = (1 + r cos t, r sin t)`, `r > 0`, about the focus–focus value `(1, 0)`, running above the
curve of relative equilibria off the axis, a continuous section `v` of the period lattice with
`v(2π) = v(0)` has zero energy component at every time off the axis: by the monodromy
`TauCeti.exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum` its
`γ₂`-coordinate vanishes. -/
theorem apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {x : ℝ → sphericalPendulumPhaseSpace}
    (hx : ∀ t, sin t ≠ 0 → sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
    {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      v t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t))
    (hper : v (2 * π) = v 0) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) (hs : sin t ≠ 0) : v t 0 = 0 := by
  obtain ⟨m, hm, hv2π⟩ :=
    exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hv hvΛ
  have hm0 : m = 0 := by simpa using congrFun (hper.symm.trans hv2π) 1
  simpa [hm0] using hm t ht hs

/-- **The period lattice has no continuous basis around the focus–focus value.** Along the circle
`γ(t) = (1 + r cos t, r sin t)`, `r > 0`, about the focus–focus value `(1, 0)`, running above the
curve of relative equilibria off the axis, two continuous sections `v`, `w` of the period lattice
that return to their initial values after one turn do not span the period lattice at any time off
the axis: both have zero energy component
(`TauCeti.apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`), while the
period lattice contains `γ₂ = (T, -Θ)` with `T > 0`. -/
theorem closure_pair_ne_hamiltonianFlowStabilizer_sphericalPendulum (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {x : ℝ → sphericalPendulumPhaseSpace}
    (hx : ∀ t, sin t ≠ 0 → sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
    {v w : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hw : ContinuousOn w (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      v t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t))
    (hwΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      w t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t))
    (hvper : v (2 * π) = v 0) (hwper : w (2 * π) = w 0) {t : ℝ} (ht : t ∈ Icc 0 (2 * π))
    (hs : sin t ≠ 0) :
    AddSubgroup.closure {v t, w t} ≠
      isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t) := by
  intro h
  obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1
    (hγ t hs)
  have hγ₂ : ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
      -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] ∈
      AddSubgroup.closure {v t, w t} := by
    rw [h, hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure hj hz hV (hx t hs)]
    exact AddSubgroup.subset_closure (mem_insert _ _)
  obtain ⟨a, b, hab⟩ := AddSubgroup.mem_closure_pair.1 hγ₂
  have hv0 :=
    apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hv hvΛ hvper ht
      hs
  have hw0 :=
    apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hw hwΛ hwper ht
      hs
  exact (sphericalPendulumPeriod_pos hj hz hV).ne (by simpa [hv0, hw0] using congrFun hab 0)

end Monodromy

end TauCeti
