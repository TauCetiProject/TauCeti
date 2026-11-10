/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Dynamics.Flow.Periodic.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Periodic orbits at the ends of finite-energy Floer half-cylinders

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C¹` Hamiltonian, `1`-periodic in
time, and `u` a solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the
half-cylinder `s > a`, for the cylindrical perturbation `K = H_t dt`, with `1`-periodic loops
`t ↦ u(s, t)` in a compact set. The almost complex structures `J z` may depend on the domain point
and are uniformly tame: `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` with `c > 0`. This is the
situation on a cylindrical end of a punctured Floer domain, such as an input end of a pair of
pants, after the target has been localized to a coordinate chart.

On such an end, the defect `∂_t u - X_{H_t}(u)` of the loops from Hamilton's equation is the
`∂_t` component of the perturbed derivative `du - X_K`, so its squared `L²` norm over the
half-cylinder is bounded by `(1 + M²) / c` times the energy
(`TauCeti.SymplecticForm.lintegral_norm_sq_sliceDefect_le`). Consequently, if the energy is finite:

* there are `s_n → ∞`, with `s_n > a`, such that the loops `t ↦ u(s_n, t)` converge uniformly to
  a `1`-periodic orbit `x` of the Hamiltonian vector field, `x' = X_{H_t}(x)`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer`);
* if `u` is `C²`, the actions `A_H(u(s, ·))` of the loops increase with `s` on any open interval
  where `u` solves the equation
  (`TauCeti.SymplecticForm.monotoneOn_hamiltonianAction_of_floer`), and they tend to the action
  `A_H(x)` of such an orbit as `s → ∞`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer`), since
  the actions of loops with vanishing defect converge to the action of their limit
  (`TauCeti.SymplecticForm.tendsto_hamiltonianAction_of_tendsto_integral_norm_sq_sliceDefect`);
* the energy of `u` over `[b, ∞) × [0, 1]` is then `A_H(x) - A_H(u(b, ·))`
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_Ici_eq_of_tendsto_hamiltonianAction`).

These are the asymptotic orbits through which the actions of the generators enter the energy
identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of a pair of pants, and the first step of Floer
breaking at an end. For these statements no nondegeneracy of the orbits, and no bound on the
derivative of `u`, is assumed; accordingly the orbit is obtained along a sequence, while the limit
of the actions holds along the whole end.

Under two further assumptions, the loops converge for all `s → ∞`. If the derivative of `u` is
bounded on the half-cylinder and every `1`-periodic orbit in `K` is nondegenerate, meaning that its
initial point is a nondegenerate fixed point of the time-one map of the Hamiltonian evolution, then
the loops `t ↦ u(s, t)` converge uniformly to a single `1`-periodic orbit as `s → ∞`
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_floer`). This is the
asymptotic condition `u(s, ·) → x` at the ends of the Floer trajectories and pairs of pants which
are counted in the Floer complex and its product. Nondegenerate fixed points of the time-one map
are isolated (`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`), and periodic solutions
through isolated fixed points are isolated among the periodic solutions
(`TauCeti.exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt`). So the statement is an
instance of the convergence theorem `TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`
for loops with square-integrable defect.

**The negative end.** The same holds on a half-cylinder `s < a` as `s → -∞`, the negative end of a
Floer trajectory and the output end of a pair of pants. The defect only involves `∂_t u`, so the
loops of `u` near `-∞` accumulate at, or under the two further assumptions converge to, periodic
orbits by the reflected convergence theorems for loops with square-integrable defect
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer_Iio`,
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_atBot_of_floer`). Along that
end the actions decrease to the action of an orbit
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer`),
and the energy of `u` over `(-∞, b] × [0, 1]` is `A_H(u(b, ·)) - A_H(x)`
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_Iic_eq_of_tendsto_hamiltonianAction`).

**Floer cylinders.** Combining the two ends, a finite-energy Floer cylinder on `ℝ × [0, 1]` with
loops in a compact set connects a periodic orbit `x₁` at `-∞` to a periodic orbit `x₂` at `∞`,
and its energy is the action difference `A_H(x₂) - A_H(x₁)`
(`TauCeti.SymplecticForm.exists_periodic_lintegral_floerEnergyDensity_eq_hamiltonianAction_sub`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {a c M : ℝ} {K : Set V}

/-- The defect of the loops of `u` from Hamilton's equation `x' = X_{H_t}(x)` is the `∂_t`
component `∂_t u - X_{H_t}(u)` of the perturbed derivative for the cylindrical perturbation
`K = H_t dt`. -/
theorem sliceDefect_hamiltonianVectorField (ω : SymplecticForm V) (H : ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z =
      ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag := by
  rw [perturbedFDeriv_apply_stdComplexLineImag, sliceDefect_def, stdComplexLineImag_eq]

/-- **The energy controls the defect.** For a solution of the Floer equation for the cylindrical
perturbation `K = H_t dt` on a measurable set `U`, with almost complex structures satisfying
`c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` there, the integral of `‖∂_t u - X_{H_t}(u)‖²` over
`U` is at most `(1 + M²) / c` times the energy over `U`. -/
theorem lintegral_norm_sq_sliceDefect_le {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) (hJM : ∀ z ∈ U, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫⁻ z in U, ENNReal.ofReal
        (‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ ^ 2) ≤
      ENNReal.ofReal ((1 + M ^ 2) / c) *
        ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  refine le_trans (lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal ?_)
    (ω.setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le hU hc hJc hJM hfloer)
  rw [sliceDefect_hamiltonianVectorField]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- **Finite energy gives a square-integrable defect.** Under the hypotheses of
`TauCeti.SymplecticForm.lintegral_norm_sq_sliceDefect_le`, if the energy over `U` is finite, then
so is the integral of `‖∂_t u - X_{H_t}(u)‖²` over `U`. -/
theorem lintegral_norm_sq_sliceDefect_ne_top {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) (hJM : ∀ z ∈ U, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in U,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in U, ENNReal.ofReal
        (‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ ^ 2) ≠ ⊤ :=
  ((lintegral_norm_sq_sliceDefect_le hU hc hJc hJM hfloer).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top)).ne

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]` for uniformly tame almost complex
structures `J z`. If the energy of `u` over `(a, ∞) × [0, 1]` is finite, then there are
`s_n → ∞`, with `s_n > a`, such that the loops `t ↦ u(s_n, t)` converge uniformly to a
`1`-periodic orbit `x` of the Hamiltonian vector field. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_floer (hH : ContDiff ℝ 1 (uncurry H))
    (hHper : Periodic H 1) (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop := by
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, -⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top hu hper hK huK
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
      (fun v t ↦ by simp only [hHper t])
      (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc hJc
        hJM hfloer hE)
  exact ⟨x, hxper, hx, φ, hφa, hφ, hux⟩

/-- **The energy of a Floer half-cylinder.** Let `u` be a `C²` solution of the Floer equation on
`(a, ∞) × [0, 1]` with `1`-periodic loops and tame almost complex structures. If the actions
`A_H(u(s, ·))` tend to `L` as `s → ∞`, then for `b > a` the energy of `u` over `[b, ∞) × [0, 1]` is
`L - A_H(u(b, ·))`. -/
theorem setLIntegral_floerEnergyDensity_Ici_eq_of_tendsto_hamiltonianAction
    (hH : ContDiff ℝ 1 (uncurry H)) (hu : ContDiffOn ℝ 2 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hJ : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {b L : ℝ} (hb : a < b)
    (hL : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop (𝓝 L)) :
    ∫⁻ z in Ici b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (L - ω.hamiltonianAction H (fun t ↦ u (b, t))) := by
  have hRsub (n : ℕ) : Icc b (b + n) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 :=
    Set.prod_mono (fun s h ↦ hb.trans_le h.1) le_rfl
  have hRU (n : ℕ) : Icc b (b + n) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ :=
    (hRsub n).trans (Set.prod_mono le_rfl (subset_univ _))
  have hEcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
    (isOpen_Ioi.prod isOpen_univ) (hu.of_le one_le_two) contDiffOn_const
    (contDiff_uncurry_cylindrical hH).contDiffOn
  -- Exhaust the half-cylinder by the rectangles `[b, b + n] × [0, 1]`, on which the energy is the
  -- change of action.
  refine setLIntegral_Ici_prod_eq_ofReal_of_tendsto (fun n ↦ ?_) hL
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hEcont.mono (hRU n)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall
        fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hRsub n hz)) (hfloer z (hRsub n hz)))),
    ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH (isOpen_Ioi.prod isOpen_univ) hu
      (le_add_of_nonneg_right n.cast_nonneg) (hRU n)
      fun s h ↦ by simpa using hper s (hb.trans_le h.1) 0]

/-- **The action increases along a Floer half-cylinder.** Let `I` be an open interval, for
instance `(a, ∞)` or `(-∞, a)`, and let `u` be a `C²` solution of the Floer equation on
`I × [0, 1]` with `1`-periodic loops and tame almost complex structures. Then the action
`A_H(u(s, ·))` of the loop at `s` is monotone in `s ∈ I`. -/
theorem monotoneOn_hamiltonianAction_of_floer {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected)
    (hH : ContDiff ℝ 1 (uncurry H)) (hu : ContDiffOn ℝ 2 u (I ×ˢ univ))
    (hper : ∀ s ∈ I, Periodic (fun t ↦ u (s, t)) 1) (hJ : ∀ z ∈ I ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ I ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    MonotoneOn (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) I := by
  intro s₁ hs₁ s₂ hs₂ hs
  have hR : Icc s₁ s₂ ×ˢ Icc (0 : ℝ) 1 ⊆ I ×ˢ Icc 0 1 := Set.prod_mono (hIc.out hs₁ hs₂) le_rfl
  exact ω.hamiltonianAction_le_hamiltonianAction (fun z hz ↦ hJ z (hR hz)) hH
    (hI.prod isOpen_univ) hu hs (hR.trans (Set.prod_mono le_rfl (subset_univ _)))
    (fun s h ↦ by simpa using hper s (hIc.out hs₁ hs₂ h) 0) fun z hz ↦ by
      simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ u z).1 (hfloer z (hR hz))

/-- **The action along loops with vanishing defect.** Let `H` be a `C¹` Hamiltonian and let `u` be
`C¹` on the half-cylinder `s > a`, with loops in a compact set `K`. If the loops at `s_i > a`
converge pointwise to a solution `x` of `x' = X_{H_t}(x)` and the `L²` norms of their defects
`∂_t u - X_{H_t}(u)` tend to `0`, then their actions tend to the action of `x`. -/
theorem tendsto_hamiltonianAction_of_tendsto_integral_norm_sq_sliceDefect
    (hH : ContDiff ℝ 1 (uncurry H)) (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ℝ} (hφa : ∀ i, a < φ i)
    (hdef : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1,
      ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (φ i, t)‖ ^ 2) l (𝓝 0))
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hux : ∀ t, Tendsto (fun i ↦ u (φ i, t)) l (𝓝 (x t))) :
    Tendsto (fun i ↦ ω.hamiltonianAction H (fun t ↦ u (φ i, t))) l
      (𝓝 (ω.hamiltonianAction H x)) := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  have hX : Continuous (uncurry X) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
  have hloop : ∀ i, Continuous fun t ↦ u (φ i, t) := fun i ↦
    continuous_slice_of_continuousOn hu.continuousOn (hφa i)
  have hdefc : ∀ i, Continuous fun t ↦ sliceDefect X u (φ i, t) := fun i ↦
    continuous_sliceDefect_slice hu hX (hφa i)
  -- Integrals of continuous functions of `(t, u(s_i, t))` over a period converge.
  have hdct : ∀ Φ : ℝ × V → ℝ, Continuous Φ →
      Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, Φ (t, u (φ i, t))) l
        (𝓝 (∫ t in (0 : ℝ)..1, Φ (t, x t))) := fun Φ hΦ ↦
    tendsto_intervalIntegral_comp_of_tendsto (y := fun i t ↦ u (φ i, t)) hΦ hK
      (fun i ↦ (hloop i).continuousOn) (fun i t _ ↦ huK _ (hφa i) t) fun t _ ↦ hux t
  -- The pairing of the loops with their defects tends to `0`.
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  have hpair : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ω (u (φ i, t)) (sliceDefect X u (φ i, t)))
      l (𝓝 0) :=
    tendsto_integral_apply_of_tendsto_integral_norm (y := fun i t ↦ u (φ i, t))
      (fun i t ↦ hR _ (huK _ (hφa i) t)) hdefc
      (tendsto_integral_norm_sliceDefect_of_tendsto_integral_norm_sq hu hX hφa hdef le_rfl
        zero_le_one le_rfl)
  -- Hence the actions converge.
  have hω1 := hdct (fun p ↦ ω p.2 (X p.1 p.2)) (ω.continuous_apply_comp continuous_snd hX)
  have hH1 := hdct (uncurry H) hH.continuous
  have hlim := ((hω1.add hpair).const_mul (1 / 2 : ℝ)).add hH1
  have hxd : ∀ t, deriv x t = X t (x t) := fun t ↦ (hx t).deriv
  have hxA : ω.hamiltonianAction H x = 1 / 2 * ((∫ t in (0 : ℝ)..1, ω (x t) (X t (x t))) + 0) +
      ∫ t in (0 : ℝ)..1, H t (x t) := by
    rw [add_zero, hamiltonianAction_def, loopArea_def]
    simp only [hxd]
  rw [hxA]
  refine hlim.congr fun i ↦ ?_
  have hs := hφa i
  have hderiv : ∀ t, deriv (fun t ↦ u (φ i, t)) t = X t (u (φ i, t)) + sliceDefect X u (φ i, t) :=
    fun t ↦ (hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) hs t).deriv
  have hi₁ : IntervalIntegrable (fun t ↦ ω (u (φ i, t)) (X t (u (φ i, t)))) volume 0 1 :=
    (ω.continuous_apply_comp (hloop i) (hX.comp (continuous_id.prodMk (hloop i)))
      ).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t ↦ ω (u (φ i, t)) (sliceDefect X u (φ i, t))) volume 0 1 :=
    (ω.continuous_apply_comp (hloop i) (hdefc i)).intervalIntegrable _ _
  simp only [hamiltonianAction_def, loopArea_def, hderiv, map_add,
    intervalIntegral.integral_add hi₁ hi₂, uncurry_apply_pair]

/-- **The asymptotic action of a finite-energy Floer half-cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer`, if `u` is moreover
`C²`, then there is a `1`-periodic orbit `x` of the Hamiltonian vector field such that the loops
`t ↦ u(s_n, t)` converge uniformly to `x` along some `s_n → ∞` with `s_n > a`, and the actions
`A_H(u(s, ·))` tend to the action `A_H(x)` as `s → ∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hu : ContDiffOn ℝ 2 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, hdef⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top (hu.of_le one_le_two) hper hK
      huK (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
      (fun v t ↦ by simp only [hHper t])
      (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc hJc
        hJM hfloer hE)
  refine ⟨x, hxper, hx, ⟨φ, hφa, hφ, hux⟩, ?_⟩
  have hseq := tendsto_hamiltonianAction_of_tendsto_integral_norm_sq_sliceDefect hH
    (hu.of_le one_le_two) hK huK hφa hdef hx hux.tendsto_at
  -- The actions increase along the end, so their limit along `s_n` is their limit as `s → ∞`.
  have hJ : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  have hmono := monotoneOn_hamiltonianAction_of_floer isOpen_Ioi ordConnected_Ioi hH hu hper hJ
    hfloer
  set A : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))
  have hb : ∀ s, a < max s (a + 1) := fun s ↦ (lt_add_one a).trans_le (le_max_right _ _)
  have hAmono : Monotone fun s ↦ A (max s (a + 1)) := fun s₁ s₂ h ↦
    hmono (hb s₁) (hb s₂) (max_le_max h le_rfl)
  have hAeq : (fun s ↦ A (max s (a + 1))) =ᶠ[atTop] A :=
    (eventually_ge_atTop (a + 1)).mono fun s hs ↦ by simp only [max_eq_left hs]
  refine (tendsto_congr' hAeq).1 ((tendsto_iff_tendsto_subseq_of_monotone hAmono hφ).2 ?_)
  exact hseq.congr' (hφ.eventually hAeq.symm)

/-- A `1`-periodic orbit through a nondegenerate fixed point of the time-one map is isolated
among the `1`-periodic orbits in the uniform distance. -/
private theorem exists_pos_forall_eq_of_isNondegenerateFixedPt {L : ℝ≥0}
    {hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)} {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
      (∀ t, dist (y t) (x t) < ε) → y = x := by
  -- A nondegenerate fixed point of the time-one map is isolated among its fixed points.
  have hiso := hnd.eventually_not_isFixedPt
  rw [timeDependentHamiltonianFlow_eq, ← zero_add (1 : ℝ)] at hiso
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt _ hx hiso
  exact ⟨ε, hε, fun y hyper hy _ hyx ↦ h y hy hyper (hyx 0)⟩

/-- **Convergence of a finite-energy Floer half-cylinder to a nondegenerate orbit.** Under the
hypotheses of `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer`, suppose
moreover that the derivative of `u` is bounded on the half-cylinder, that the suspension of the
Hamiltonian vector field is globally Lipschitz, so that its evolution `φ` is defined, and that every
`1`-periodic orbit `x` of the Hamiltonian vector field in `K` is nondegenerate: `x(0)` is a
nondegenerate fixed point of the time-one map `φ(0, 1)`. Then the loops `t ↦ u(s, t)` converge
uniformly, as `s → ∞`, to a single `1`-periodic orbit. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_floer
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1)
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hK : IsCompact K) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (s, t)) x atTop := by
  refine exists_periodic_hasDerivAt_tendstoUniformly_atTop hu hper hK huK
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
    (fun v t ↦ by simp only [hHper t])
    (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc hJc hJM
      hfloer hE) hC fun x hxper hx hxK ↦
    exists_pos_forall_eq_of_isNondegenerateFixedPt hx (hnd x hxper hx hxK)

/-! ### The negative end

On the half-cylinder `s < a`, the negative end of a Floer trajectory or the output end of a pair
of pants, the loops of a finite-energy solution approach periodic orbits as `s → -∞`. The defect
`∂_t u - X_{H_t}(u)` does not see the direction of `s`, so the accumulation and convergence of the
loops follow from the reflected statements for loops with square-integrable defect; the actions
of the loops decrease to the action of the limiting orbit. -/

/-- **Periodic orbits at the negative end of a finite-energy Floer half-cylinder.** Let `H` be a
`C¹` Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s < a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(-∞, a) × [0, 1]` for uniformly tame almost complex
structures `J z`. If the energy of `u` over `(-∞, a) × [0, 1]` is finite, then there are
`s_n → -∞`, with `s_n < a`, such that the loops `t ↦ u(s_n, t)` converge uniformly to a
`1`-periodic orbit `x` of the Hamiltonian vector field. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_floer_Iio (hH : ContDiff ℝ 1 (uncurry H))
    (hHper : Periodic H 1) (hu : ContDiffOn ℝ 1 u (Iio a ×ˢ univ))
    (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, s < a → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Iio a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Iio a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ φ : ℕ → ℝ, (∀ n, φ n < a) ∧ Tendsto φ atTop atBot ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop := by
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, -⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_Iio_ne_top hu hper hK huK
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
      (fun v t ↦ by simp only [hHper t])
      (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Iio.prod measurableSet_Icc) hc hJc
        hJM hfloer hE)
  exact ⟨x, hxper, hx, φ, hφa, hφ, hux⟩

/-- **The energy of a Floer half-cylinder at the negative end.** Let `u` be a `C²` solution of
the Floer equation on `(-∞, a) × [0, 1]` with `1`-periodic loops and tame almost complex
structures. If the actions `A_H(u(s, ·))` tend to `L` as `s → -∞`, then for `b < a` the energy of
`u` over `(-∞, b] × [0, 1]` is `A_H(u(b, ·)) - L`. -/
theorem setLIntegral_floerEnergyDensity_Iic_eq_of_tendsto_hamiltonianAction
    (hH : ContDiff ℝ 1 (uncurry H)) (hu : ContDiffOn ℝ 2 u (Iio a ×ˢ univ))
    (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1)
    (hJ : ∀ z ∈ Iio a ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ Iio a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {b L : ℝ} (hb : b < a)
    (hL : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot (𝓝 L)) :
    ∫⁻ z in Iic b ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (ω.hamiltonianAction H (fun t ↦ u (b, t)) - L) := by
  have hRsub (n : ℕ) : Icc (b - n) b ×ˢ Icc (0 : ℝ) 1 ⊆ Iio a ×ˢ Icc 0 1 :=
    Set.prod_mono (fun s h ↦ h.2.trans_lt hb) le_rfl
  have hRU (n : ℕ) : Icc (b - n) b ×ˢ Icc (0 : ℝ) 1 ⊆ Iio a ×ˢ univ :=
    (hRsub n).trans (Set.prod_mono le_rfl (subset_univ _))
  have hEcont := ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
    (isOpen_Iio.prod isOpen_univ) (hu.of_le one_le_two) contDiffOn_const
    (contDiff_uncurry_cylindrical hH).contDiffOn
  -- Exhaust the half-cylinder by the rectangles `[b - n, b] × [0, 1]`, on which the energy is the
  -- change of action.
  refine setLIntegral_Iic_prod_eq_ofReal_of_tendsto (fun n ↦ ?_) hL
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hEcont.mono (hRU n)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall
        fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hRsub n hz)) (hfloer z (hRsub n hz)))),
    ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH (isOpen_Iio.prod isOpen_univ) hu
      (sub_le_self b n.cast_nonneg) (hRU n)
      fun s h ↦ by simpa using hper s (h.2.trans_lt hb) 0]

/-- **The asymptotic action at the negative end of a finite-energy Floer half-cylinder.** Under
the hypotheses of `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer_Iio`,
if `u` is moreover `C²`, then there is a `1`-periodic orbit `x` of the Hamiltonian vector field
such that the loops `t ↦ u(s_n, t)` converge uniformly to `x` along some `s_n → -∞` with
`s_n < a`, and the actions `A_H(u(s, ·))` tend to the action `A_H(x)` as `s → -∞`. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hu : ContDiffOn ℝ 2 u (Iio a ×ˢ univ))
    (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, s < a → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Iio a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Iio a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ φ : ℕ → ℝ, (∀ n, φ n < a) ∧ Tendsto φ atTop atBot ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot
        (𝓝 (ω.hamiltonianAction H x)) := by
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, hdef⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_Iio_ne_top (hu.of_le one_le_two) hper
      hK huK (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
      (fun v t ↦ by simp only [hHper t])
      (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Iio.prod measurableSet_Icc) hc hJc
        hJM hfloer hE)
  refine ⟨x, hxper, hx, ⟨φ, hφa, hφ, hux⟩, ?_⟩
  -- Along `s_n` the actions converge, by the positive-end statement for the reflected map
  -- `(s, t) ↦ u(-s, t)`, whose loops and defects are those of `u`.
  have hseq : Tendsto (fun n ↦ ω.hamiltonianAction H (fun t ↦ u (φ n, t))) atTop
      (𝓝 (ω.hamiltonianAction H x)) := by
    have h := tendsto_hamiltonianAction_of_tendsto_integral_norm_sq_sliceDefect
      (u := fun z ↦ u (-z.1, z.2)) (a := -a) (φ := fun n ↦ -φ n) hH
      ((hu.of_le one_le_two).comp (contDiff_neg.prodMap contDiff_id).contDiffOn
        fun _ hz ↦ ⟨neg_lt.1 hz.1, trivial⟩)
      hK (fun s hs t ↦ huK (-s) (neg_lt.1 hs) t) (fun n ↦ neg_lt_neg (hφa n))
      (by simpa only [sliceDefect_comp_neg_fst, neg_neg] using hdef) hx
      (by simpa only [neg_neg] using fun t ↦ hux.tendsto_at t)
    simpa only [neg_neg] using h
  -- The actions increase along the end, so their limit along `s_n` is their limit as `s → -∞`.
  have hJ : ∀ z ∈ Iio a ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  have hmono := monotoneOn_hamiltonianAction_of_floer isOpen_Iio ordConnected_Iio hH hu hper hJ
    hfloer
  set A : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))
  have hb : ∀ s, min (-s) (a - 1) < a := fun s ↦ (min_le_right _ _).trans_lt (sub_one_lt a)
  have hAanti : Antitone fun s ↦ A (min (-s) (a - 1)) := fun s₁ s₂ h ↦
    hmono (hb s₂) (hb s₁) (min_le_min (neg_le_neg h) le_rfl)
  have hAeq : (fun s ↦ A (min (-s) (a - 1))) ∘ Neg.neg =ᶠ[atBot] A :=
    (eventually_le_atBot (a - 1)).mono fun s hs ↦ by simp only [comp_apply, neg_neg, min_eq_left hs]
  have hψ : Tendsto (fun n ↦ -φ n) atTop atTop := tendsto_neg_atBot_atTop.comp hφ
  have hlim := (tendsto_iff_tendsto_subseq_of_antitone hAanti hψ).2
    (hseq.congr' (hφ.eventually (eventually_le_atBot (a - 1)) |>.mono fun n hn ↦ by
      simp only [A, comp_apply, neg_neg, min_eq_left hn]))
  exact (tendsto_congr' hAeq).1 (hlim.comp tendsto_neg_atBot_atTop)

/-- **Convergence at the negative end of a finite-energy Floer half-cylinder.** Under the
hypotheses of `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer_Iio`,
suppose moreover that the derivative of `u` is bounded on the half-cylinder, that the suspension
of the Hamiltonian vector field is globally Lipschitz, so that its evolution `φ` is defined, and
that every `1`-periodic orbit `x` of the Hamiltonian vector field in `K` is nondegenerate: `x(0)`
is a nondegenerate fixed point of the time-one map `φ(0, 1)`. Then the loops `t ↦ u(s, t)`
converge uniformly, as `s → -∞`, to a single `1`-periodic orbit. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atBot_of_floer
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1)
    (hu : ContDiffOn ℝ 1 u (Iio a ×ˢ univ)) (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1)
    (hK : IsCompact K) (huK : ∀ s, s < a → ∀ t, u (s, t) ∈ K) (hc : 0 < c)
    (hJc : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Iio a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Iio a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Iio a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Iio a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (s, t)) x atBot := by
  refine exists_periodic_hasDerivAt_tendstoUniformly_atBot hu hper hK huK
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous
    (fun v t ↦ by simp only [hHper t])
    (lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Iio.prod measurableSet_Icc) hc hJc hJM
      hfloer hE) hC fun x hxper hx hxK ↦
    exists_pos_forall_eq_of_isNondegenerateFixedPt hx (hnd x hxper hx hxK)

/-! ### Floer cylinders -/

/-- **A finite-energy Floer cylinder connects two periodic orbits.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, and let `u` be a `C²` map on `ℝ × ℝ` with `1`-periodic loops
`t ↦ u(s, t)` in a compact set `K`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]` for uniformly tame almost complex structures
`J z`. If the energy of `u` over `ℝ × [0, 1]` is finite, then there are `1`-periodic orbits `x₁` and
`x₂` of the Hamiltonian vector field such that the actions `A_H(u(s, ·))` tend to `A_H(x₁)` as
`s → -∞` and to `A_H(x₂)` as `s → ∞`, each orbit is the uniform limit of the loops along a
sequence going to its end, and the energy of `u` is `A_H(x₂) - A_H(x₁)`. -/
theorem exists_periodic_lintegral_floerEnergyDensity_eq_hamiltonianAction_sub
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hu : ContDiff ℝ 2 u)
    (hper : ∀ s, Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K) (huK : ∀ s t, u (s, t) ∈ K)
    (hc : 0 < c) (hJc : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x₁ x₂ : ℝ → V, Periodic x₁ 1 ∧ Periodic x₂ 1 ∧
      (∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t) ∧
      (∀ t, HasDerivAt x₂ (ω.hamiltonianVectorField (H t) (x₂ t)) t) ∧
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atBot ∧ TendstoUniformly (fun n t ↦ u (φ n, t)) x₁ atTop) ∧
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧ TendstoUniformly (fun n t ↦ u (φ n, t)) x₂ atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot
        (𝓝 (ω.hamiltonianAction H x₁)) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop
        (𝓝 (ω.hamiltonianAction H x₂)) ∧
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₂ - ω.hamiltonianAction H x₁) := by
  have hsub : ∀ I : Set ℝ, I ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 := fun I ↦
    Set.prod_mono (subset_univ I) le_rfl
  have hE' : ∀ I : Set ℝ, ∫⁻ z in I ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤ := fun I ↦
    ne_top_of_le_ne_top hE (lintegral_mono_set (hsub I))
  -- The two ends, each on a half-cylinder.
  obtain ⟨x₁, hx₁per, hx₁, ⟨φ₁, -, hφ₁, hux₁⟩, hbot⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer (a := 0) hH hHper
      hu.contDiffOn (fun s _ ↦ hper s) hK (fun s _ ↦ huK s) hc
      (fun z hz ↦ hJc z (hsub _ hz)) (fun z hz ↦ hJM z (hsub _ hz))
      (fun z hz ↦ hfloer z (hsub _ hz)) (hE' _)
  obtain ⟨x₂, hx₂per, hx₂, ⟨φ₂, -, hφ₂, hux₂⟩, htop⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := 0) hH hHper
      hu.contDiffOn (fun s _ ↦ hper s) hK (fun s _ ↦ huK s) hc
      (fun z hz ↦ hJc z (hsub _ hz)) (fun z hz ↦ hJM z (hsub _ hz))
      (fun z hz ↦ hfloer z (hsub _ hz)) (hE' _)
  refine ⟨x₁, x₂, hx₁per, hx₂per, hx₁, hx₂, ⟨φ₁, hφ₁, hux₁⟩, ⟨φ₂, hφ₂, hux₂⟩, hbot, htop, ?_⟩
  -- The energy over the whole strip is the change of action between the two ends.
  have hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  simpa only [fderiv_cylindrical_apply_stdComplexLineReal, integral_zero, sub_zero] using
    ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction_sub_integral
      (H := fun w ↦ H w.2) hJ (contDiff_uncurry_cylindrical hH) isOpen_univ hu.contDiffOn
      (subset_univ _) (fun s ↦ by simpa using hper s 0)
      (fun z hz ↦ by
        simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ u z).1 (hfloer z hz))
      (by simp only [fderiv_cylindrical_apply_stdComplexLineReal]; exact integrableOn_zero) hbot
      htop

end TauCeti.SymplecticForm
