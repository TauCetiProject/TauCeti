/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.Trajectory
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Analysis.SpecificLimits.ShiftDoubling
import TauCeti.Geometry.Symplectic.Floer.Translation.Basic

/-!
# Floer trajectories near a nondegenerate orbit are stationary

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C²` Hamiltonian, `1`-periodic in
time, and `x` a `1`-periodic orbit of its Hamiltonian vector field which is *nondegenerate*: the
propagator of the linearized equation `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at
time `1`. The stationary cylinder `(s, t) ↦ x(t)` is a Floer trajectory of energy zero. This file
shows that it is isolated among all finite-energy Floer trajectories, uniformly in the trajectory:
for every `c > 0` and `M` there is `δ > 0` such that every `C²` solution `u` of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops, finite energy and almost complex
structures satisfying `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖`, which stays within `δ` of `x`,
`‖u(s, t) - x(t)‖ ≤ δ` for all `s` and `t`, is the stationary cylinder over `x`
(`TauCeti.SymplecticForm.exists_pos_forall_eq_of_floer`). Equivalently, every other finite-energy
trajectory leaves the `δ`-neighbourhood of `x`.

This is the local input of Floer breaking that does not go through the action spectrum. The energy
gap `TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_floerEnergyDensity` bounds the
energy of nonstationary trajectories below by the least positive difference of finitely many
actions. Here no finiteness of actions is assumed: only the nondegeneracy of the single orbit `x`
enters, and the threshold `δ` depends only on `H`, `x`, `c` and `M`. In a sequence of trajectories
that breaks, it rules out levels hiding in a small neighbourhood of a nondegenerate orbit.

**The argument.** Let `A(s)` be the action of the loop `u(s, ·)` and `g(s) = A(s) - A_H(x)`. The
energy of `u` over `[a, b] × [0, 1]` is `A(b) - A(a)`
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_eq_hamiltonianAction_sub`), so `g` is
nondecreasing, and it is bounded because the actions have limits at both ends
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`). Near a
nondegenerate orbit, `|g(s)|` is at most a constant `K` times the energy of the slice at `s`
(`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity`).
Integrating this over `[s, s + K]` and over `[s - K, s]` and using monotonicity gives
`2 g(s) ≤ g(s + K)` and `g(s - K) ≤ 2 g(s)`, so a nonzero value of `g` would grow geometrically in
one of the two directions, contradicting boundedness. Hence `g = 0`
(`TauCeti.eq_of_monotone_of_abs_sub_le_mul`), the energy is zero and `u` is stationary
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`). Its loop is then an orbit
near `x`, which is `x` itself by
`TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_integral_of_nondegenerate`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on Floer trajectories near nondegenerate orbits and the
  inequality between the action and the energy that also gives their exponential decay.
-/

public section

open Set Filter Topology MeasureTheory Function intervalIntegral Metric

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V} {c : ℝ}

variable {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}

/-- A stationary Floer trajectory `u(s, t) = u(0, t)` whose loop is close enough to `x` to fall
under the estimate `‖γ - x‖ ≤ C ∫₀¹ ‖γ' - X_{H_t}(γ)‖` for loops near a nondegenerate orbit is the
stationary cylinder over `x`: its loop is an orbit, so the right-hand side vanishes. -/
private theorem eq_of_forall_eq_apply_zero {C δ : ℝ} (hu : ContDiff ℝ 2 u)
    (hper : ∀ s, Periodic (fun t ↦ u (s, t)) 1) (hxper : Periodic x 1)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hstat : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s, t) = u (0, t))
    (hiso : ∀ {γ γ' : ℝ → V}, Continuous γ' → (∀ t, HasDerivAt γ (γ' t) t) →
      γ 1 = γ 0 → (∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - x t‖ ≤ δ) → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ t - x t‖ ≤ C * ∫ s in (0 : ℝ)..1, ‖γ' s - ω.hamiltonianVectorField (H s) (γ s)‖)
    (hclose : ∀ t, ‖u (0, t) - x t‖ ≤ δ) (s t : ℝ) : u (s, t) = x t := by
  -- By periodicity it suffices to compare the loops at `Int.fract t ∈ [0, 1)`.
  have hfract (t : ℝ) : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  set γ : ℝ → V := fun t ↦ u (0, t)
  have hustat : u = fun w ↦ γ w.2 := funext fun ⟨s, t⟩ ↦
    calc u (s, t) = u (s, Int.fract t) := ((hper s).apply_fract t).symm
      _ = u (0, Int.fract t) := hstat s _ (hfract t)
      _ = γ t := (hper 0).apply_fract t
  set γ' : ℝ → V := fun t ↦ fderiv ℝ u (0, t) (0, 1)
  have hγ'c : Continuous γ' :=
    ((hu.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const
  have hγ (t : ℝ) : HasDerivAt γ (γ' t) t :=
    hasDerivAt_slice_right ((hu.differentiable (by norm_num)).differentiableAt)
  -- The loop `γ` is an orbit of the Hamiltonian vector field.
  have horbit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ' t - ω.hamiltonianVectorField (H t) (γ t) = 0 := by
    have h := hfloer (0, t) ⟨mem_univ _, ht⟩
    rw [hustat] at h
    rw [← (hγ t).deriv, sub_eq_zero]
    exact (isComplexLinearMap_perturbedFDeriv_comp_snd_iff (hγ t).differentiableAt).1 h
  have hγx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = x t := by
    have h := hiso hγ'c hγ (by simpa using hper 0 0) (fun t _ ↦ hclose t) t ht
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ by
      rw [uIcc_of_le zero_le_one] at hs
      simp only [horbit s hs, norm_zero], intervalIntegral.integral_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  calc u (s, t) = γ t := congrFun hustat (s, t)
    _ = γ (Int.fract t) := ((hper 0).apply_fract t).symm
    _ = x (Int.fract t) := hγx _ (hfract t)
    _ = x t := hxper.apply_fract t

/-- **Floer trajectories near a nondegenerate orbit are stationary.** Let `H` be a `C²`
Hamiltonian, `1`-periodic in time, and let `x` be a `1`-periodic orbit of its Hamiltonian vector
field which is nondegenerate: the propagator of `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed
vector at time `1`. Let `0 < c` and `M` be tameness constants. Then there is `δ > 0` such that every
`C²` solution `u` of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with
`1`-periodic loops, almost complex structures satisfying `c ‖v‖² ≤ ω(v, J z v)` and
`‖J z v‖ ≤ M ‖v‖`, and finite energy, which stays `δ`-close to `x`, is the stationary cylinder over
`x`: `u(s, t) = x(t)` for all `s` and `t`. -/
theorem exists_pos_forall_eq_of_floer (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) (hc : 0 < c) (M : ℝ) :
    ∃ δ > 0, ∀ {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V},
      ContDiff ℝ 2 u → (∀ s, Periodic (fun t ↦ u (s, t)) 1) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤ →
      (∀ s t, ‖u (s, t) - x t‖ ≤ δ) → ∀ s t, u (s, t) = x t := by
  have hx1 : x 1 = x 0 := by simpa using hxper 0
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  obtain ⟨δ₁, hδ₁, K, hK, hslice⟩ :=
    exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity hH hx hx1 hnd c M hc
  obtain ⟨δ₂, hδ₂, C, -, hiso⟩ :=
    exists_forall_norm_sub_le_mul_integral_of_nondegenerate hH hx hx1 hnd
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {u J} hu hper hJc hJM hfloer hE hclose ↦ ?_⟩
  have hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz ↦
    tames_of_mul_norm_sq_le hc (hJc z hz)
  -- The loops stay in a compact neighbourhood of `x`, so the actions have limits at both ends.
  have huK (s t : ℝ) : u (s, t) ∈ cthickening δ₁ (range x) :=
    mem_cthickening_of_dist_le _ (x t) _ _ (mem_range_self t) (by
      rw [dist_eq_norm]; exact (hclose s t).trans (min_le_left _ _))
  obtain ⟨x₀, x₁, -, -, hlim₀, hlim₁, hEeq⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq hH1 hHper hu hper
      (hxper.compact_of_continuous one_ne_zero hxc).cthickening huK hc hJc hJM hfloer hE
  have hmono : Monotone fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t)) := monotoneOn_univ.1
    (ω.monotoneOn_hamiltonianAction_of_floer isOpen_univ hH1 hu.contDiffOn (fun s _ ↦ hper s)
      hJ hfloer)
  -- Near `x` the action defect of a loop is at most `K` times the energy of its slice, so every
  -- loop has the action of `x`.
  have hAx (s : ℝ) : ω.hamiltonianAction H (fun t ↦ u (s, t)) = ω.hamiltonianAction H x := by
    refine eq_of_monotone_of_abs_sub_le_mul hK hmono
      ⟨_, forall_mem_range.2 (hmono.ge_of_tendsto hlim₁)⟩
      ⟨_, forall_mem_range.2 (hmono.le_of_tendsto hlim₀)⟩ (fun s ↦ ?_) (fun a ↦
        ω.integrableOn_and_integral_setIntegral_floerEnergyDensity_eq hH1 isOpen_univ
          hu.contDiffOn (by linarith) (subset_univ _) fun r _ ↦ by simpa using hper r 0) s
    exact hslice isOpen_univ (hu.of_le one_le_two).contDiffOn (fun t ↦ mem_univ (s, t))
      (by simpa using hper s 0) (fun t ht ↦ hJc (s, t) ⟨mem_univ s, ht⟩)
      (fun t ht ↦ hJM (s, t) ⟨mem_univ s, ht⟩) (fun t ht ↦ hfloer (s, t) ⟨mem_univ s, ht⟩)
      fun t _ ↦ (hclose s t).trans (min_le_left _ _)
  -- The two ends have the action of `x`, so the energy vanishes and `u` is stationary.
  have hA : (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) =
      fun _ ↦ ω.hamiltonianAction H x := funext hAx
  rw [hA] at hlim₀ hlim₁
  have hzero := hEeq.trans (by rw [tendsto_nhds_unique hlim₁ tendsto_const_nhds,
    tendsto_nhds_unique hlim₀ tendsto_const_nhds, sub_self, ENNReal.ofReal_zero])
  exact eq_of_forall_eq_apply_zero hu hper hxper hfloer
    ((ω.lintegral_floerEnergyDensity_eq_zero_iff hH1 isOpen_univ (hu.of_le one_le_two).contDiffOn
      (subset_univ _) hJ hfloer).1 hzero) hiso fun t ↦ (hclose 0 t).trans (min_le_right _ _)

end TauCeti.SymplecticForm
