/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.PeriodLattice
import TauCeti.Topology.Circle.Degree
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Hamiltonian monodromy of the spherical pendulum

Above the curve of relative equilibria, the period lattice of the spherical pendulum at a value
`(h, j)` with `j ≠ 0` of the energy–momentum map `F = (H, J)`, the stabilizer of any point of the
fibre `F⁻¹(h, j)` under the flow action of `F`, is the lattice of `ℝ²` spanned by

* `γ₂ = (T(h, j), -Θ(h, j))`: the energy flow for the period `T` of the height, closed by the
  rotation flow backwards through the rotation angle `Θ`;
* `γ_J = (0, 2π)`: the rotation flow, the flow of `J`, for one full turn

(`TauCeti.hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure`). Through the
orbit map, these lattices are the first homology groups of the Liouville tori. This file
transports them around the focus–focus value `(1, 0)` of `F` and derives what the **Hamiltonian
monodromy** of the pendulum forces on continuous sections of these lattices: each gains `m γ_J`,
where `m` is its `γ₂`-coordinate.

Let `γ(t) = (1 + r cos t, r sin t)`, `t ∈ [0, 2π]`, be the counterclockwise circle of radius
`r > 0` about `(1, 0)`, running above the curve of relative equilibria off the axis `j = 0`.
A continuous section `b` of the period lattices along `γ` is a function continuous on
`[0, 2π]` with `b(t)` in the lattice at `γ(t)` whenever `sin t ≠ 0`; nothing is assumed at the
two times where `γ` crosses the axis. On each of the two open half-circles such a section has
constant integer coordinates in the basis `(γ₂, γ_J)`, since the period `T` and the rotation angle
`Θ` are continuous there and `T > 0`. Comparing the one-sided limits at the axis, where `Θ` tends
to `±π` at `(1 - r, 0)` and to `±2π` at `(1 + r, 0)`
(`TauCeti.tendsto_sphericalPendulumRotationAngle_circle`), and using that `T` is even in `j` and
bounded away from `0`, the section returns to

`b(2π) = b(0) + m γ_J`,

where `m` is its `γ₂`-coordinate on the upper half-circle
(`exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`,
`TauCeti.apply_two_mul_pi_eq_apply_zero_add_zsmul_of_mem_closure_sphericalPendulumPeriod`).
So a continuous section through `γ_J` on the upper half-circle, such as the constant one, returns
to its initial value, and a continuous section through `γ₂` there gains `γ_J`
(`TauCeti.apply_two_mul_pi_eq_apply_zero_of_mem_closure_sphericalPendulumPeriod`,
`TauCeti.apply_two_mul_pi_eq_apply_zero_add_of_mem_closure_sphericalPendulumPeriod`). The same
holds for sections of the stabilizers themselves
(`TauCeti.exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer`).
This file does not show that `γ₂` extends to such a section: that needs the period `T` to extend
continuously across the axis, which is not proved here. Granting it, the transport fixes `γ_J`
and sends `γ₂` to `γ₂ + γ_J`, so in the transported basis `(γ_J, γ₂)` the monodromy matrix is
`[[1, 1], [0, 1]]`.

Consequently every closed continuous section, one with `b(2π) = b(0)`, is a multiple of `γ_J` on
the upper half-circle (`TauCeti.exists_forall_eq_zsmul_of_mem_closure_sphericalPendulumPeriod`),
and no two closed continuous sections span the period lattice at any time of the upper
half-circle (`TauCeti.closure_pair_ne_closure_sphericalPendulumPeriod`). On both half-circles the
energy component of a continuous section is `m T` for the one integer `m`
(`TauCeti.exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`), so on the stabilizers a
closed continuous section has zero energy component at every time off the axis, and two closed
continuous sections span the stabilizer at no such time
(`TauCeti.apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`,
`TauCeti.closure_pair_ne_hamiltonianFlowStabilizer_sphericalPendulum`). The period lattices
along the loop thus admit no continuous basis. This is Duistermaat's obstruction to global
action–angle coordinates around `(1, 0)`, which would supply such a basis.

## Main results

* `exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`:
  a continuous section of the period lattices along the loop gains `m γ_J`, where `m` is its
  `γ₂`-coordinate.
* `TauCeti.apply_two_mul_pi_eq_apply_zero_add_zsmul_of_mem_closure_sphericalPendulumPeriod`: a
  continuous section equal to `m γ₂ + n γ_J` at a time of the upper half-circle gains `m γ_J`.
* `TauCeti.apply_two_mul_pi_eq_apply_zero_of_mem_closure_sphericalPendulumPeriod`,
  `TauCeti.apply_two_mul_pi_eq_apply_zero_add_of_mem_closure_sphericalPendulumPeriod`: continuous
  sections through `γ_J` close up, and continuous sections through `γ₂` gain `γ_J`.
* `TauCeti.closure_pair_ne_closure_sphericalPendulumPeriod`: closed continuous sections never span
  the period lattice on the upper half-circle.
* `TauCeti.exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod`,
  `TauCeti.exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum`: the energy
  component of a continuous section is `m T` on both half-circles, and the section gains `m γ_J`.
* `TauCeti.closure_pair_ne_hamiltonianFlowStabilizer_sphericalPendulum`: closed continuous
  sections of the stabilizers never span the stabilizer at any time off the axis.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706.
* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum and its monodromy).
* K. Efstathiou, A. Giacobbe, P. Mardešić and D. Sugny, *Rotation forms and local Hamiltonian
  monodromy*, arXiv:1608.01579, Section III.
-/

public section

open Filter Set Real
open scoped Topology

namespace TauCeti

section Monodromy

variable {r : ℝ}

/-- On a preconnected set of times where the circle `γ(t) = (1 + r cos t, r sin t)` runs above the
curve of relative equilibria off the axis, a continuous section of the period lattices has
constant integer coordinates in the basis `((T, -Θ), (0, 2π))`. -/
private theorem exists_forall_eq_of_isPreconnected {s : Set ℝ} (hs : IsPreconnected s)
    (hsne : s.Nonempty)
    (hγ : ∀ t ∈ s, (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b s)
    (hbΛ : ∀ t ∈ s, b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]}) :
    ∃ m n : ℤ, ∀ t ∈ s, b t =
      m • ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] + n • ![0, 2 * π] := by
  set T : ℝ → ℝ := fun t ↦ sphericalPendulumPeriod (1 + r * cos t) (r * sin t) with hTdef
  set Θ : ℝ → ℝ := fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t) with hΘdef
  have hγc : Continuous fun t : ℝ ↦ (1 + r * cos t, r * sin t) := by fun_prop
  have hT : ContinuousOn T s := continuousOn_sphericalPendulumPeriod.comp hγc.continuousOn hγ
  have hΘ : ContinuousOn Θ s :=
    continuousOn_sphericalPendulumRotationAngle.comp hγc.continuousOn hγ
  have hTpos : ∀ t ∈ s, 0 < T t := fun t ht ↦ sphericalPendulumPeriod_pos_of_mem (hγ t ht)
  have hb₀ : ContinuousOn (fun t ↦ b t 0) s := (continuous_apply 0).comp_continuousOn hb
  have hb₁ : ContinuousOn (fun t ↦ b t 1) s := (continuous_apply 1).comp_continuousOn hb
  choose! M N hMN using fun t ht ↦ AddSubgroup.mem_closure_pair.1 (hbΛ t ht)
  have h₀ : ∀ t ∈ s, b t 0 = M t * T t := fun t ht ↦ by
    simpa using (congrFun (hMN t ht) 0).symm
  have h₁ : ∀ t ∈ s, b t 1 = M t * -Θ t + N t * (2 * π) := fun t ht ↦ by
    simpa using (congrFun (hMN t ht) 1).symm
  obtain ⟨t₀, ht₀⟩ := hsne
  -- The `γ₂`-coordinate `b₀ / T` is continuous with values in `ℤ`, hence constant.
  have hdiv : ∀ t ∈ s, b t 0 / T t = M t := fun t ht ↦ by
    rw [h₀ t ht, mul_div_cancel_right₀ _ (hTpos t ht).ne']
  have hM : ∀ t ∈ s, M t = M t₀ := fun t ht ↦ by
    have := hs.constant_of_mapsTo (isDiscrete_iff_discreteTopology.2
      Int.isClosedEmbedding_coe_real.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology)
      (hb₀.div hT fun t ht ↦ (hTpos t ht).ne') (fun t ht ↦ ⟨M t, (hdiv t ht).symm⟩) ht ht₀
    exact_mod_cast (hdiv t ht).symm.trans (this.trans (hdiv t₀ ht₀))
  -- Given the `γ₂`-coordinate, the `γ_J`-coordinate is constant for the same reason.
  obtain ⟨D, hD⟩ := hs.exists_forall_sub_eq_of_coe_eq (f := fun t ↦ b t 1)
    (g := fun t ↦ M t₀ * -Θ t) hb₁ (continuousOn_const.mul hΘ.neg) fun t ht ↦
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨N t, by rw [h₁ t ht, hM t ht]; ring⟩
  refine ⟨M t₀, N t₀, fun t ht ↦ ?_⟩
  have e₁ := hD t ht
  have e₀ := hD t₀ ht₀
  simp only [h₁ t₀ ht₀] at e₀
  ext i
  fin_cases i
  · simp [h₀ t ht, hM t ht, hTdef]
  · simp only [hΘdef] at e₁ e₀
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, zsmul_eq_mul, Fin.isValue]
    linarith

/-- On the upper half-circle the period is at least `2π / √(2 (r + 4))`, since there
`h = 1 + r cos t ≤ 1 + r`. -/
private theorem two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_of_mem_Ioo (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {t : ℝ} (ht : t ∈ Ioo 0 π) :
    2 * π / √(2 * (r + 4)) ≤ sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := by
  obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1
    (hγ t (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne')
  -- The energy `1 + r cos t` exceeds `-1`, as it lies above the effective potential.
  have hh : 0 < 2 * (1 + r * cos t + 3) := by
    nlinarith [neg_one_lt_sphericalPendulumLowerTurningPoint hj hz hV,
      sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz hV,
      one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint hj hz hV]
  exact (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hh)
    (Real.sqrt_le_sqrt (by nlinarith [cos_le_one t]))).trans
      (two_mul_pi_div_sqrt_le_sphericalPendulumPeriod hj hz hV)

/-- Along the circle `γ(t) = (1 + r cos t, r sin t)` about the focus–focus value, a continuous
section of the period lattices has the same `γ₂`-coordinate on the two half-circles, and the same
first coordinate at both ends of `[0, 2π]`. The reflection `t ↦ 2π - t` swaps the half-circles and
reflects `γ` in the axis `j = 0`, so it preserves the period `T`, which is even in `j`; and `T` is
bounded below near the axis. -/
private theorem eq_and_apply_two_mul_pi_zero_eq (hr : 0 < r) (hγ : ∀ t, sin t ≠ 0 →
      (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π))) {m₁ n₁ m₂ n₂ : ℤ}
    (h₁ : ∀ t ∈ Ioo 0 π, b t =
      m₁ • ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] + n₁ • ![0, 2 * π])
    (h₂ : ∀ t ∈ Ioo π (2 * π), b t =
      m₂ • ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] + n₂ • ![0, 2 * π]) :
    m₁ = m₂ ∧ b (2 * π) 0 = b 0 0 := by
  have hpi : 0 < π := pi_pos
  have hIcc₁ : Ioo 0 π ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨ht.1.le, by linarith [ht.2]⟩
  have hIcc₂ : Ioo π (2 * π) ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨by linarith [ht.1], ht.2.le⟩
  have hmaps : MapsTo (fun t ↦ 2 * π - t) (Ioo 0 π) (Ioo π (2 * π)) := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hv : ∀ t ∈ Ioo 0 π,
      b t 0 = m₁ * sphericalPendulumPeriod (1 + r * cos t) (r * sin t) ∧
        b (2 * π - t) 0 = m₂ * sphericalPendulumPeriod (1 + r * cos t) (r * sin t) := fun t ht ↦ by
    rw [h₁ t ht, h₂ _ (hmaps ht)]
    simp [cos_two_pi_sub, sin_two_pi_sub]
  -- The first coordinates of `b` and of `b` after the reflection, near a time of the upper half.
  have hlim₁ {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 (2 * π)) :
      Tendsto (fun t ↦ b t 0) (𝓝[Ioo 0 π] t₀) (𝓝 (b t₀ 0)) :=
    ((continuous_apply 0).continuousAt.tendsto.comp (hb t₀ ht₀).tendsto).mono_left
      (nhdsWithin_mono _ hIcc₁)
  have hlim₂ {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc 0 (2 * π)) (h : 2 * π - t₁ = t₀) :
      Tendsto (fun t ↦ b (2 * π - t) 0) (𝓝[Ioo 0 π] t₁) (𝓝 (b t₀ 0)) := by
    subst h
    exact ((continuous_apply 0).continuousAt.tendsto.comp ((hb _ ht₀).tendsto.mono_left
      (nhdsWithin_mono _ hIcc₂))).comp
        ((continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin hmaps)
  -- Near `π`, `(m₁ - m₂) T(γ t)` tends to `b(π)₀ - b(π)₀ = 0` while `T ≥ 2π / √(2 (r + 4))`.
  have hm : m₁ = m₂ := by
    by_contra hne
    have : (𝓝[Ioo 0 π] π).NeBot := right_nhdsWithin_Ioo_neBot hpi
    have hbound : ∀ t ∈ Ioo 0 π, 2 * π / √(2 * (r + 4)) ≤ |b t 0 - b (2 * π - t) 0| := by
      intro t ht
      have hTt := two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_of_mem_Ioo hr hγ ht
      have hP := hTt.trans_lt' (by positivity)
      have hm₁₂ : (1 : ℝ) ≤ |(m₁ : ℝ) - m₂| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
      rw [(hv t ht).1, (hv t ht).2, ← sub_mul, abs_mul, abs_of_pos hP]
      exact hTt.trans (le_mul_of_one_le_left hP.le hm₁₂)
    have := ge_of_tendsto ((hlim₁ ⟨hpi.le, by linarith⟩).sub
      (hlim₂ ⟨hpi.le, by linarith⟩ (by ring))).abs (eventually_nhdsWithin_of_forall hbound)
    rw [sub_self, abs_zero] at this
    exact absurd this (not_le.2 (by positivity))
  -- Near `0`, both `b(t)₀` and `b(2π - t)₀` are `m T(γ t)`.
  subst hm
  have : (𝓝[Ioo 0 π] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hpi
  exact ⟨rfl, tendsto_nhds_unique ((hlim₂ ⟨by linarith, le_rfl⟩ (sub_zero _)).congr'
    (eventually_nhdsWithin_of_forall fun t ht ↦ by rw [(hv t ht).1, (hv t ht).2]))
    (hlim₁ ⟨le_rfl, by linarith⟩)⟩

/-- **The Hamiltonian monodromy of the spherical pendulum.** Let `γ(t) = (1 + r cos t, r sin t)`,
`t ∈ [0, 2π]`, be the counterclockwise circle of radius `r > 0` about the focus–focus value
`(1, 0)`, and suppose that off the axis `j = 0` it runs strictly above the curve of relative
equilibria. Let `b` be continuous on `[0, 2π]`, with `b(t)` in the period lattice spanned by
`γ₂ = (T, -Θ)` and `γ_J = (0, 2π)` at `γ(t)` whenever `sin t ≠ 0`. Then `b` has constant integer
coordinates `(m, n)` in this basis on the upper half-circle, and after one turn it has gained
`m γ_J`: `b(2π) = b(0) + m (0, 2π)`. -/
theorem exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod
    (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]}) :
    ∃ m n : ℤ, (∀ t ∈ Ioo 0 π, b t =
      m • ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] + n • ![0, 2 * π]) ∧
      b (2 * π) = b 0 + m • ![0, 2 * π] := by
  have hpi : 0 < π := pi_pos
  have h2pi : π < 2 * π := by linarith
  have hr₂ := lt_two_of_mem_sphericalPendulumTurningPointDomain
    (by simpa using hγ (π / 2) (by simp))
  obtain ⟨l₀, lπ₁, lπ₂, l₂π⟩ := tendsto_sphericalPendulumRotationAngle_circle hr hr₂
  have hIcc₁ : Ioo 0 π ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨ht.1.le, by linarith [ht.2]⟩
  have hIcc₂ : Ioo π (2 * π) ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨by linarith [ht.1], ht.2.le⟩
  have hsin₁ : ∀ t ∈ Ioo 0 π, sin t ≠ 0 := fun t ht ↦ (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hsin₂ : ∀ t ∈ Ioo π (2 * π), sin t ≠ 0 := fun t ht ↦
    (sin_neg_of_pi_lt_of_lt_two_pi ht.1 ht.2).ne
  obtain ⟨m, n₁, h₁⟩ := exists_forall_eq_of_isPreconnected isPreconnected_Ioo (nonempty_Ioo.2 hpi)
    (fun t ht ↦ hγ t (hsin₁ t ht)) (hb.mono hIcc₁) fun t ht ↦ hbΛ t (hIcc₁ ht) (hsin₁ t ht)
  obtain ⟨m₂, n₂, h₂⟩ := exists_forall_eq_of_isPreconnected isPreconnected_Ioo
    (nonempty_Ioo.2 h2pi) (fun t ht ↦ hγ t (hsin₂ t ht)) (hb.mono hIcc₂)
    fun t ht ↦ hbΛ t (hIcc₂ ht) (hsin₂ t ht)
  obtain ⟨rfl, h₀⟩ := eq_and_apply_two_mul_pi_zero_eq hr hγ hb h₁ h₂
  -- The second coordinate of `b` at a crossing of the axis is the one-sided limit of
  -- `-m Θ(γ t) + 2π n` from either half-circle.
  have key {s : Set ℝ} {t₀ L : ℝ} {n : ℤ} (_ : (𝓝[s] t₀).NeBot) (hs : s ⊆ Icc 0 (2 * π))
      (ht₀ : t₀ ∈ Icc 0 (2 * π))
      (hf : ∀ t ∈ s, b t 1 =
        m * -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t) + n * (2 * π))
      (hL : Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))
        (𝓝[s] t₀) (𝓝 L)) :
      b t₀ 1 = m * -L + n * (2 * π) :=
    tendsto_nhds_unique (((continuous_apply 1).continuousAt.tendsto.comp
      (hb t₀ ht₀).tendsto).mono_left (nhdsWithin_mono _ hs))
      (((tendsto_const_nhds.mul hL.neg).add tendsto_const_nhds).congr'
        (eventually_nhdsWithin_of_forall fun t ht ↦ (hf t ht).symm))
  have hv₁ : ∀ t ∈ Ioo 0 π, b t 1 =
      m * -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t) + n₁ * (2 * π) :=
    fun t ht ↦ by simp [h₁ t ht]
  have hw₁ : ∀ t ∈ Ioo π (2 * π), b t 1 =
      m * -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t) + n₂ * (2 * π) :=
    fun t ht ↦ by simp [h₂ t ht]
  have hπ : π ∈ Icc 0 (2 * π) := ⟨hpi.le, h2pi.le⟩
  have eπ₁ := key (right_nhdsWithin_Ioo_neBot hpi) hIcc₁ hπ hv₁ lπ₁
  have eπ₂ := key (left_nhdsWithin_Ioo_neBot h2pi) hIcc₂ hπ hw₁ lπ₂
  have e₀ := key (left_nhdsWithin_Ioo_neBot hpi) hIcc₁ ⟨le_rfl, by linarith⟩ hv₁ l₀
  have e₂π := key (right_nhdsWithin_Ioo_neBot h2pi) hIcc₂ ⟨by linarith, le_rfl⟩ hw₁ l₂π
  refine ⟨m, n₁, h₁, ?_⟩
  ext i
  fin_cases i
  · simpa using h₀
  · simp only [Pi.add_apply, Pi.smul_apply]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, zsmul_eq_mul, Fin.isValue]
    linear_combination e₂π - e₀ + eπ₁ - eπ₂

/-- **The Hamiltonian monodromy of the spherical pendulum, on the stabilizers.** Let
`γ(t) = (1 + r cos t, r sin t)`, `t ∈ [0, 2π]`, be a circle of radius `r > 0` about the focus–focus
value `(1, 0)` running strictly above the curve of relative equilibria off the axis `j = 0`, and
let `x(t)` be a point of the fibre `F⁻¹(γ(t))` for every `t` with `sin t ≠ 0`. If `b` is
continuous on `[0, 2π]` and `b(t)` lies in the stabilizer of `x(t)` under the flow action of `F`
whenever `sin t ≠ 0`, then `b` has constant integer coordinates `(m, n)` in the basis
`((T, -Θ), (0, 2π))` on the upper half-circle, and `b(2π) = b(0) + m (0, 2π)`. -/
theorem exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer
    (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {x : ℝ → sphericalPendulumPhaseSpace}
    (hx : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      b t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t)) :
    ∃ m n : ℤ, (∀ t ∈ Ioo 0 π, b t =
      m • ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] + n • ![0, 2 * π]) ∧
      b (2 * π) = b 0 + m • ![0, 2 * π] :=
  exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ
    hb fun t ht hs ↦ by
      rw [← hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem (hγ t hs)
        (hx t ht hs)]
      exact hbΛ t ht hs

/-- **The monodromy on a section with given coordinates.** A continuous section of the period
lattices along the circle `γ` about the focus–focus value that equals `m γ₂ + n γ_J`, with
`γ₂ = (T, -Θ)` and `γ_J = (0, 2π)`, at some time of the upper half-circle gains `m γ_J` after one
turn. -/
theorem apply_two_mul_pi_eq_apply_zero_add_zsmul_of_mem_closure_sphericalPendulumPeriod
    (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 π) {m n : ℤ}
    (hbt₀ : b t₀ = m • ![sphericalPendulumPeriod (1 + r * cos t₀) (r * sin t₀),
      -sphericalPendulumRotationAngle (1 + r * cos t₀) (r * sin t₀)] + n • ![0, 2 * π]) :
    b (2 * π) = b 0 + m • ![0, 2 * π] := by
  obtain ⟨m', n', h, h2π⟩ :=
    exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ
      hb hbΛ
  have hT := (two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_of_mem_Ioo hr hγ ht₀).trans_lt'
    (by positivity)
  have h₀ := congrFun ((h t₀ ht₀).symm.trans hbt₀) 0
  simp only [Pi.add_apply, Pi.smul_apply] at h₀
  simp only [Matrix.cons_val_zero, smul_zero, add_zero, zsmul_eq_mul] at h₀
  rw [h2π, Int.cast_injective (mul_right_cancel₀ hT.ne' h₀)]

/-- **The monodromy fixes `γ_J`.** A continuous section of the period lattices along the circle
`γ` about the focus–focus value that equals `γ_J = (0, 2π)` at some time of the upper half-circle
returns to its initial value after one turn. The constant section `γ_J` is one. -/
theorem apply_two_mul_pi_eq_apply_zero_of_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 π) (hbt₀ : b t₀ = ![0, 2 * π]) :
    b (2 * π) = b 0 := by
  rw [apply_two_mul_pi_eq_apply_zero_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ hb
    hbΛ ht₀ (m := 0) (n := 1) (by rw [hbt₀, zero_smul, one_smul, zero_add]), zero_smul, add_zero]

/-- **Sections through `γ₂` gain `γ_J`.** A continuous section of the period lattices along the
circle `γ` about the focus–focus value that equals `γ₂ = (T, -Θ)` at some time of the upper
half-circle gains `γ_J = (0, 2π)` after one turn. So the monodromy sends `γ₂` to `γ₂ + γ_J` as soon
as such a section exists; its existence, which needs the period `T` to extend continuously across
the axis `j = 0`, is not proved here. -/
theorem apply_two_mul_pi_eq_apply_zero_add_of_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 π)
    (hbt₀ : b t₀ = ![sphericalPendulumPeriod (1 + r * cos t₀) (r * sin t₀),
      -sphericalPendulumRotationAngle (1 + r * cos t₀) (r * sin t₀)]) :
    b (2 * π) = b 0 + ![0, 2 * π] := by
  rw [apply_two_mul_pi_eq_apply_zero_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ hb
    hbΛ ht₀ (m := 1) (n := 0) (by rw [hbt₀, one_smul, zero_smul, add_zero]), one_smul]

/-- **Closed sections are multiples of `γ_J`.** A continuous section of the period lattices along
the circle `γ` about the focus–focus value that returns to its initial value after one turn is an
integer multiple of `γ_J = (0, 2π)` on the upper half-circle. -/
theorem exists_forall_eq_zsmul_of_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b : ℝ → Fin 2 → ℝ} (hb : ContinuousOn b (Icc 0 (2 * π)))
    (hbΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    (hb₀ : b (2 * π) = b 0) :
    ∃ n : ℤ, ∀ t ∈ Ioo 0 π, b t = n • ![0, 2 * π] := by
  obtain ⟨m, n, h, h2π⟩ :=
    exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ
      hb hbΛ
  have hm : m = 0 := by simpa [pi_ne_zero] using congrFun (h2π.symm.trans hb₀) 1
  exact ⟨n, fun t ht ↦ by rw [h t ht, hm, zero_smul, zero_add]⟩

/-- **The period lattices along the loop have no continuous basis.** No two continuous sections of
the period lattices along the circle `γ` about the focus–focus value that return to their initial
values after one turn span the period lattice at any time of the upper half-circle. Global
action–angle coordinates around `(1, 0)` would provide two such sections. -/
theorem closure_pair_ne_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {b₁ b₂ : ℝ → Fin 2 → ℝ} (hb₁ : ContinuousOn b₁ (Icc 0 (2 * π)))
    (hb₂ : ContinuousOn b₂ (Icc 0 (2 * π)))
    (hbΛ₁ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b₁ t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    (hbΛ₂ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → b₂ t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]})
    (h₁ : b₁ (2 * π) = b₁ 0) (h₂ : b₂ (2 * π) = b₂ 0) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    AddSubgroup.closure {b₁ t, b₂ t} ≠ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]} := by
  obtain ⟨n₁, hn₁⟩ :=
    exists_forall_eq_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ hb₁ hbΛ₁ h₁
  obtain ⟨n₂, hn₂⟩ :=
    exists_forall_eq_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ hb₂ hbΛ₂ h₂
  intro hEq
  -- `γ₂` would be a combination of multiples of `γ_J`, whose first coordinates vanish.
  obtain ⟨k, l, hkl⟩ := AddSubgroup.mem_closure_pair.1
    (hEq ▸ AddSubgroup.subset_closure (by simp) :
      ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] ∈
        AddSubgroup.closure {b₁ t, b₂ t})
  have h₀ := congrFun hkl 0
  simp only [hn₁ t ht, hn₂ t ht, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, smul_zero,
    add_zero] at h₀
  exact ((two_mul_pi_div_sqrt_le_sphericalPendulumPeriod_of_mem_Ioo hr hγ ht).trans_lt'
    (by positivity)).ne' h₀.symm

/-- **The energy component of a continuous section along the whole loop.** Let
`γ(t) = (1 + r cos t, r sin t)`, with `r > 0`, be the counterclockwise circle about the
focus–focus value `(1, 0)`, running above the curve of relative equilibria off the axis `j = 0`,
and let `v` be continuous on `[0, 2π]` with `v(t)` in the lattice spanned by `(T(γ(t)), -Θ(γ(t)))`
and `(0, 2π)` whenever `sin t ≠ 0`. Then for one integer `m` the energy component of `v(t)` is
`m T(γ(t))` at all these times, on both half-circles, and after one turn
`v(2π) = v(0) + m (0, 2π)`. -/
theorem exists_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 → v t ∈ AddSubgroup.closure
      {![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
        -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)], ![0, 2 * π]}) :
    ∃ m : ℤ, (∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
        v t 0 = m * sphericalPendulumPeriod (1 + r * cos t) (r * sin t)) ∧
      v (2 * π) = v 0 + m • ![0, 2 * π] := by
  have hpi : 0 < π := pi_pos
  have hIcc₂ : Ioo π (2 * π) ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨by linarith [ht.1], ht.2.le⟩
  have hsin₂ : ∀ t ∈ Ioo π (2 * π), sin t ≠ 0 := fun t ht ↦
    (sin_neg_of_pi_lt_of_lt_two_pi ht.1 ht.2).ne
  obtain ⟨m, n₁, h₁, h2π⟩ :=
    exists_forall_eq_and_apply_two_mul_pi_eq_add_zsmul_of_mem_closure_sphericalPendulumPeriod hr hγ
      hv hvΛ
  -- On the lower half-circle the `γ₂`-coordinate is the same `m`.
  obtain ⟨m₂, n₂, h₂⟩ := exists_forall_eq_of_isPreconnected isPreconnected_Ioo
    (nonempty_Ioo.2 (by linarith)) (fun t ht ↦ hγ t (hsin₂ t ht)) (hv.mono hIcc₂)
    fun t ht ↦ hvΛ t (hIcc₂ ht) (hsin₂ t ht)
  obtain ⟨rfl, -⟩ := eq_and_apply_two_mul_pi_zero_eq hr hγ hv h₁ h₂
  refine ⟨m, fun t ht hs ↦ ?_, h2π⟩
  rcases lt_trichotomy t π with htπ | rfl | htπ
  · simp [h₁ t ⟨ht.1.lt_of_ne (by rintro rfl; simp at hs), htπ⟩]
  · simp at hs
  · simp [h₂ t ⟨htπ, ht.2.lt_of_ne (by rintro rfl; simp at hs)⟩]

/-- **The energy component along the whole loop, on the stabilizers.** Let
`γ(t) = (1 + r cos t, r sin t)`, with `r > 0`, be the counterclockwise circle about the
focus–focus value `(1, 0)`, running above the curve of relative equilibria off the axis `j = 0`,
let `x(t)` be a point of the fibre `F⁻¹(γ(t))` for every `t` with `sin t ≠ 0`, and let `v` be
continuous on `[0, 2π]` with `v(t)` in the period lattice, the stabilizer of `x(t)` under the flow
action of `F`, at all these times. Then for one integer `m`, the `γ₂`-coordinate of `v`, the
energy component of `v(t)` is `m T(γ(t))`, and after one turn `v(2π) = v(0) + m (0, 2π)`. -/
theorem exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {x : ℝ → sphericalPendulumPhaseSpace}
    (hx : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
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
    rw [← hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem (hγ t hs)
      (hx t ht hs)]
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
    (hx : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
    {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hvΛ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      v t ∈ isSymplectic_sphericalPendulumSymplecticForm.hamiltonianFlowStabilizer
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.contMDiff
        isIntegrableSystem_sphericalPendulumEnergyMomentumVec.poissonBracket_eq_zero
        isCompleteVectorField_hamiltonianVectorField_sphericalPendulumEnergyMomentumVec (x t))
    (hper : v (2 * π) = v 0) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) (hs : sin t ≠ 0) : v t 0 = 0 := by
  obtain ⟨m, hm, hv2π⟩ :=
    exists_eq_add_zsmul_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hv hvΛ
  have hm0 : m = 0 := by simpa [pi_ne_zero] using congrFun (hper.symm.trans hv2π) 1
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
    (hx : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      sphericalPendulumEnergyMomentum (x t) = (1 + r * cos t, r * sin t))
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
  have hγ₂ : ![sphericalPendulumPeriod (1 + r * cos t) (r * sin t),
      -sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)] ∈
      AddSubgroup.closure {v t, w t} := by
    rw [h, hamiltonianFlowStabilizer_sphericalPendulumEnergyMomentum_eq_closure_of_mem (hγ t hs)
      (hx t ht hs)]
    exact AddSubgroup.subset_closure (mem_insert _ _)
  obtain ⟨a, b, hab⟩ := AddSubgroup.mem_closure_pair.1 hγ₂
  have hv0 :=
    apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hv hvΛ hvper ht
      hs
  have hw0 :=
    apply_zero_eq_zero_of_mem_hamiltonianFlowStabilizer_sphericalPendulum hr hγ hx hw hwΛ hwper ht
      hs
  exact (sphericalPendulumPeriod_pos_of_mem (hγ t hs)).ne (by simpa [hv0, hw0] using congrFun hab 0)

end Monodromy

end TauCeti
