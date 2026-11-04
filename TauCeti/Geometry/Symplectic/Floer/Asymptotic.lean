/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Symplectic.Floer.Action
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz

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

* there are `s_n → ∞` such that the loops `t ↦ u(s_n, t)` converge uniformly to a `1`-periodic
  orbit `x` of the Hamiltonian vector field, `x' = X_{H_t}(x)`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer`);
* if `u` is `C²`, the actions `A_H(u(s, ·))` of the loops increase to the action `A_H(x)` of such
  an orbit as `s → ∞`
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer`);
* the energy of `u` over `[b, ∞) × [0, 1]` is then `A_H(x) - A_H(u(b, ·))`
  (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_Ici_eq_of_tendsto_hamiltonianAction`).

These are the asymptotic orbits through which the actions of the generators enter the energy
identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of a pair of pants, and the first step of Floer
breaking at an end. No nondegeneracy of the orbits, and no bound on the derivative of `u`, is
assumed; accordingly the orbit is obtained along a sequence, while the limit of the actions holds
along the whole end. Convergence of the loops for all `s → ∞` needs isolated orbits and is not
proved here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal

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

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]` for uniformly tame almost complex
structures `J z`. If the energy of `u` over `(a, ∞) × [0, 1]` is finite, then there are `s_n → ∞`
such that the loops `t ↦ u(s_n, t)` converge uniformly to a `1`-periodic orbit `x` of the
Hamiltonian vector field. -/
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
      ∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧ TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop := by
  have hfin := (lintegral_norm_sq_sliceDefect_le (measurableSet_Ioi.prod measurableSet_Icc) hc
    hJc hJM hfloer).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top)
  obtain ⟨x, hxper, hx, φ, -, hφ, hux, -⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top hu hper hK huK
      (ω.continuous_hamiltonianVectorField_uncurry hH)
      (fun v t ↦ by simp only [hHper t]) hfin.ne
  exact ⟨x, hxper, hx, φ, hφ, hux⟩

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
  set E : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u
  set R : ℕ → Set (ℝ × ℝ) := fun n ↦ Icc b (b + n) ×ˢ Icc 0 1
  have hRsub : ∀ n, R n ⊆ Ioi a ×ˢ Icc 0 1 := fun n ↦
    Set.prod_mono (fun s h ↦ hb.trans_le h.1) le_rfl
  have hEcont : ContinuousOn E (Ioi a ×ˢ univ) :=
    ω.continuousOn_floerEnergyDensity (isOpen_Ioi.prod isOpen_univ) (hu.of_le one_le_two)
      contDiffOn_const (contDiff_uncurry_cylindrical hH).contDiffOn
  -- On each rectangle the energy is the change of action.
  have hrect : ∀ n : ℕ, ∫⁻ z in R n, ENNReal.ofReal (E z) =
      ENNReal.ofReal (ω.hamiltonianAction H (fun t ↦ u (b + n, t)) -
        ω.hamiltonianAction H (fun t ↦ u (b, t))) := by
    intro n
    have hRU : R n ⊆ Ioi a ×ˢ univ := (hRsub n).trans (Set.prod_mono le_rfl (subset_univ _))
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hEcont.mono hRU).integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      ((ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall
        fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hRsub n hz)) (hfloer z (hRsub n hz))))]
    rw [ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH (isOpen_Ioi.prod isOpen_univ)
      hu (le_add_of_nonneg_right n.cast_nonneg) hRU
      fun s h ↦ by simpa using hper s (hb.trans_le h.1) 0]
  -- The rectangles exhaust the half-cylinder.
  have hmono : Monotone R := fun m n hmn ↦
    Set.prod_mono (Icc_subset_Icc le_rfl (by simpa using hmn)) le_rfl
  have hunion : ⋃ n, R n = Ici b ×ˢ Icc 0 1 := by
    refine (iUnion_subset fun n ↦ Set.prod_mono Icc_subset_Ici_self le_rfl).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (z.1 - b)
    exact mem_iUnion.2 ⟨n, ⟨hz.1, by linarith⟩, hz.2⟩
  have hlim : Tendsto (fun n ↦ ∫⁻ z in R n, ENNReal.ofReal (E z)) atTop
      (𝓝 (∫⁻ z in Ici b ×ˢ Icc 0 1, ENNReal.ofReal (E z))) := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono' (Measure.restrict_mono (hmono hmn)
      le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [hrect]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((hL.comp (tendsto_atTop_add_const_left _ b tendsto_natCast_atTop_atTop)).sub_const _)

/-- **The asymptotic action of a finite-energy Floer half-cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_of_floer`, if `u` is moreover
`C²`, then there is a `1`-periodic orbit `x` of the Hamiltonian vector field such that the loops
`t ↦ u(s_n, t)` converge uniformly to `x` along some `s_n → ∞`, and the actions `A_H(u(s, ·))`
tend to the action `A_H(x)` as `s → ∞`. -/
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
      (∃ φ : ℕ → ℝ, Tendsto φ atTop atTop ∧ TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  have hX : Continuous (uncurry X) := ω.continuous_hamiltonianVectorField_uncurry hH
  have hfin := (lintegral_norm_sq_sliceDefect_le (measurableSet_Ioi.prod measurableSet_Icc) hc
    hJc hJM hfloer).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top)
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, hdef⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top (hu.of_le one_le_two) hper hK
      huK hX (fun v t ↦ by simp only [X, hHper t]) hfin.ne
  refine ⟨x, hxper, hx, ⟨φ, hφ, hux⟩, ?_⟩
  have hmem : ∀ s, a < s → ∀ t : ℝ, (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) :=
    fun s hs t ↦ ⟨hs, mem_univ t⟩
  have hu1 : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ) := hu.of_le one_le_two
  have hloop : ∀ s, a < s → Continuous fun t ↦ u (s, t) := fun s hs ↦
    hu1.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (hmem s hs)
  have hdefc : ∀ s, a < s → Continuous fun t ↦ sliceDefect X u (s, t) := fun s hs ↦
    (continuousOn_sliceDefect hu1 hX).comp_continuous (continuous_const.prodMk continuous_id)
      (hmem s hs)
  have hxcont : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hpt : ∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t)) := hux.tendsto_at
  -- Integrals of continuous functions of `(t, u(s_n, t))` over a period converge.
  have hdct : ∀ Φ : ℝ × V → ℝ, Continuous Φ →
      Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, Φ (t, u (φ n, t))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, Φ (t, x t))) := by
    intro Φ hΦ
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hΦ.continuousOn
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
      (Eventually.of_forall fun n ↦ (hΦ.comp (continuous_id.prodMk
        (hloop _ (hφa n)))).aestronglyMeasurable)
      (Eventually.of_forall fun n ↦ Eventually.of_forall fun t ht ↦ ?_) intervalIntegrable_const
      (Eventually.of_forall fun t _ ↦
        (hΦ.tendsto (t, x t)).comp (tendsto_const_nhds.prodMk_nhds (hpt t)))
    rw [uIoc_of_le zero_le_one] at ht
    exact hC _ ⟨⟨ht.1.le, ht.2⟩, huK _ (hφa n) t⟩
  -- The pairing of the loops with their defects tends to `0`.
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  set Bω := ω.toBilinForm.toContinuousBilinearMap
  have hω : ∀ v w, |ω v w| ≤ ‖Bω‖ * ‖v‖ * ‖w‖ := fun v w ↦ by
    simpa only [Bω, LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs] using
      Bω.le_opNorm₂ v w
  have hpair : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ω (u (φ n, t)) (sliceDefect X u (φ n, t)))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖Bω‖ * R *
        √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2)) atTop (𝓝 0) := by
      have h := ((Real.continuous_sqrt.tendsto 0).comp hdef).const_mul (‖Bω‖ * R)
      rw [Real.sqrt_zero, mul_zero] at h
      exact h
    refine squeeze_zero_norm (fun n ↦ ?_) hsq
    have hd : Continuous fun t ↦ ‖sliceDefect X u (φ n, t)‖ := (hdefc _ (hφa n)).norm
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ (huK _ (hφa n) 0))
    calc ‖∫ t in (0 : ℝ)..1, ω (u (φ n, t)) (sliceDefect X u (φ n, t))‖
        ≤ ∫ t in (0 : ℝ)..1, ‖Bω‖ * R * ‖sliceDefect X u (φ n, t)‖ := by
          refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Eventually.of_forall fun t _ ↦ ?_) ((continuous_const.mul hd).intervalIntegrable _ _)
          rw [Real.norm_eq_abs]
          refine (hω _ _).trans ?_
          gcongr
          exact hR _ (huK _ (hφa n) t)
      _ = ‖Bω‖ * R * ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ ‖Bω‖ * R * (√(1 - 0) * √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2)) := by
          gcongr
          exact integral_le_sqrt_mul_sqrt_integral_sq zero_le_one (fun t _ ↦ norm_nonneg _)
            (hd.intervalIntegrable _ _) ((hd.pow 2).intervalIntegrable _ _)
      _ = ‖Bω‖ * R * √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) := by
          rw [sub_zero, Real.sqrt_one, one_mul]
  -- The actions converge along the sequence.
  have hderiv : ∀ s, a < s → ∀ t, deriv (fun t ↦ u (s, t)) t =
      X t (u (s, t)) + sliceDefect X u (s, t) := fun s hs t ↦ by
    rw [sliceDefect_def, add_sub_cancel]
    exact ((hu1.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (hmem s hs t))).hasDerivAt_slice_snd.deriv
  have hseq : Tendsto (fun n ↦ ω.hamiltonianAction H (fun t ↦ u (φ n, t))) atTop
      (𝓝 (ω.hamiltonianAction H x)) := by
    have hω1 := hdct (fun p ↦ ω p.2 (X p.1 p.2)) (ω.continuous_apply_comp continuous_snd hX)
    have hH1 := hdct (uncurry H) hH.continuous
    have hlim := ((hω1.add hpair).const_mul (1 / 2 : ℝ)).add hH1
    have hxd : ∀ t, deriv x t = X t (x t) := fun t ↦ (hx t).deriv
    have hxA : ω.hamiltonianAction H x = 1 / 2 * ((∫ t in (0 : ℝ)..1, ω (x t) (X t (x t))) + 0) +
        ∫ t in (0 : ℝ)..1, H t (x t) := by
      rw [add_zero, hamiltonianAction_def, loopArea_def]
      simp only [hxd]
    rw [hxA]
    refine hlim.congr fun n ↦ ?_
    have hs := hφa n
    have hi₁ : IntervalIntegrable (fun t ↦ ω (u (φ n, t)) (X t (u (φ n, t)))) volume 0 1 :=
      (ω.continuous_apply_comp (hloop _ hs) (hX.comp (continuous_id.prodMk (hloop _ hs)))
        ).intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun t ↦ ω (u (φ n, t)) (sliceDefect X u (φ n, t))) volume 0 1 :=
      (ω.continuous_apply_comp (hloop _ hs) (hdefc _ hs)).intervalIntegrable _ _
    simp only [hamiltonianAction_def, loopArea_def, hderiv _ hs, map_add,
      intervalIntegral.integral_add hi₁ hi₂, uncurry_apply_pair]
  -- The actions increase along the end, so the limit along the sequence is the limit.
  set A : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))
  have hJ : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  have hmono : ∀ s₁ s₂, a < s₁ → s₁ ≤ s₂ → A s₁ ≤ A s₂ := by
    intro s₁ s₂ hs₁ hs
    have hR : Icc s₁ s₂ ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 :=
      Set.prod_mono (fun s h ↦ hs₁.trans_le h.1) le_rfl
    exact ω.hamiltonianAction_le_hamiltonianAction (fun z hz ↦ hJ z (hR hz)) hH
      (isOpen_Ioi.prod isOpen_univ) hu hs (hR.trans (Set.prod_mono le_rfl (subset_univ _)))
      (fun s h ↦ by simpa using hper s (hs₁.trans_le h.1) 0) fun z hz ↦ by
        simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ u z).1 (hfloer z (hR hz))
  have hle : ∀ s, a < s → A s ≤ ω.hamiltonianAction H x := fun s hs ↦
    ge_of_tendsto hseq ((hφ.eventually_ge_atTop s).mono fun n hn ↦ hmono s _ hs hn)
  refine tendsto_order.2 ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hseq.eventually (lt_mem_nhds hl)).exists
    filter_upwards [eventually_ge_atTop (φ n)] with s hs
    exact hn.trans_le (hmono _ _ (hφa n) hs)
  · filter_upwards [eventually_gt_atTop a] with s hs
    exact (hle s hs).trans_lt hl

end TauCeti.SymplecticForm
