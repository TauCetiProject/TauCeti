/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.Plane.Convergence
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Exponential decay and `C¹` exponential convergence at the end of a PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞` and end
chart `φ_p` (`TauCeti.Floer.PSSPlane.endChart`), and let `K : ℂ → V → ℂ →L[ℝ] ℝ` be a Hamiltonian
perturbation on `ℂ` with values in a symplectic vector space `(V, ω)` that equals `H(t) dt` beyond
longitudinal height `T₀` on the end of `p`, for a period-one Hamiltonian `H : ℝ → V → ℝ` (for
instance `K = p.perturbation H` with `T₀ = 2`). Adapting
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.ExponentialDecay` to the PSS planes, when the end
loops `t ↦ u(φ_p(ε R, t))` of a finite-energy Floer solution `u` on `{‖w‖ > r}` converge uniformly
as `R → ∞` to a nondegenerate `1`-periodic orbit `x` of `H`, this file proves that the exterior
Floer energy of `u` decays exponentially, and that `u ∘ φ_p` converges exponentially to the
stationary cylinder `(s, t) ↦ x(t)` in `C⁰` and `C¹`, without requiring any global Lipschitz
hypothesis on `H`.

**Linearized nondegeneracy in the positive end chart.** In the positive end chart
`φ_+ = positive.endChart`, `u ∘ φ_+` solves the half-cylinder Floer equation for
`H'_p(t, y) = ε H(ε t, y)` (`TauCeti.Floer.PSSPlane.positiveEndHamiltonian`) and converges uniformly
to `t ↦ x(ε t)`. By `TauCeti.Geometry.Symplectic.Floer.SignedEnd.Orbit`, fixed vectors of the
linearized return map (`TauCeti.dysonSeriesLeft`) along `t ↦ x(ε t)` for `H'_p` coincide with fixed
vectors along `x` for `H` (`dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff`), and
vanish in particular when `x(0)` is a nondegenerate fixed point of the time-one map of `H`
(`eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self`).

**Exterior energy decay and `C⁰` exponential convergence.** Applying
`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp` to
`u ∘ φ_+` and changing variables back via
`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ici_eq`
shows that for a `C²` solution on `{‖w‖ > r}` with uniformly tame almost complex structures on the
end, the Floer energy over `{‖w‖ ≥ exp (2π R)}` is eventually at most `C exp (-κ R)`
(`exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlane_le_exp`). Under a bound on
`∂_s(u ∘ φ_+)`, `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` gives
`‖u(φ_p(ε R, t)) - x(t)‖ ≤ C exp (-κ R)`
(`exists_pos_eventually_norm_sub_le_exp_pssPlane_endChart`).

**Cylindrical ends and `C¹` exponential convergence.** When `H` and `u` are `C³` and the almost
complex structure beyond `T₀` is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a
`1`-periodic family `J₀` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`, the
sign-cancellation identity `d(u ∘ φ_p)(ε R, t) = ε d(u ∘ φ_+)(R, ε t)`
(`norm_fderiv_comp_pssPlane_endChart_sub_smulRight`) combines with the half-cylinder `C¹` decay
theorem `TauCeti.SymplecticForm.exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp` to show that
`d(u ∘ φ_p)(ε R, t)` converges exponentially to `dt ⊗ X_{H_t}(x(t))`
(`exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp`) and that
`∂_s(u ∘ φ_p)(ε R, t)` decays exponentially
(`exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_apply_one_zero_le_exp`). When every
`1`-periodic orbit of `H` in `B` is linearly nondegenerate,
`TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_integral_of_nondegenerate` supplies orbit
isolation for full-end convergence on the cylindrical end, giving unconditional `C¹` exponential
convergence to a `1`-periodic orbit `x` along the end
(`exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp`), together with its
`s → -∞` (`atBot`) form in `negative.endChart`
(`exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_pssPlane_endChart_negative_le_exp`) matching
the negative-end hypothesis of neck pre-gluing
(`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`).

## Main results

* `dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff`,
  `eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self`: linearized return-map
  nondegeneracy in `positive.endChart`.
* `exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlane_le_exp`: exponential decay of the
  exterior Floer energy over `{‖w‖ ≥ exp (2π R)}`.
* `exists_pos_eventually_norm_sub_le_exp_pssPlane_endChart`: conditional `C⁰` exponential
  convergence of the end loops of a PSS plane to a nondegenerate orbit.
* `exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp`,
  `exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_apply_one_zero_le_exp`: exponential
  `C¹` convergence of `d(u ∘ φ_p)` and exponential decay of `∂_s(u ∘ φ_p)` along a cylindrical end.
* `exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp`,
  `exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_pssPlane_endChart_negative_le_exp`:
  unconditional `C¹` exponential convergence on a cylindrical end (as `R → +∞` for either plane,
  and as `s → -∞` in `negative.endChart`), plus `_of_isNondegenerateFixedPt` specializations.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
* J. Robbin and D. Salamon, *Asymptotic behaviour of holomorphic strips*, Ann. Inst. H. Poincaré
  Anal. Non Linéaire 18 (2001), 573–612.
-/

public section

open Set Real Filter Function MeasureTheory
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}

/-! ### Linearized nondegeneracy, exterior energy decay, and `C⁰` exponential convergence -/

/-- **Linearized return-map fixed vectors in `positive.endChart`.** For a `1`-periodic `C²`
Hamiltonian `H` and a continuous `1`-periodic loop `x`, a vector `v` is fixed by the linearized
return map of `p.positiveEndHamiltonian H` along `t ↦ x(ε t)` if and only if it is fixed by the
linearized return map of `H` along `x`. -/
theorem dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff (p : PSSPlane)
    (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V} (hxc : Continuous x)
    (hxper : Periodic x 1) {v : V} :
    dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t)) (x (p.endSign * t))) 1 v = v ↔
      dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v := by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian]
  exact ω.dysonSeriesLeft_signedHamiltonian_apply_eq_self_iff p.endSign_mul_endSign hHs hH hxc hxper

/-- **Nondegeneracy in the positive end chart of a PSS plane.** If `x` is a `1`-periodic orbit of a
`1`-periodic `C²` Hamiltonian `H` and `x(0)` is a nondegenerate fixed point of the time-one map of
`H`, then the linearized return map of `p.positiveEndHamiltonian H` along `t ↦ x(ε t)` has no
nonzero fixed vector. -/
theorem eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self
    (p : PSSPlane) {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {v : V} (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t)) (x (p.endSign * t))) 1 v = v) :
    v = 0 := by
  rw [p.positiveEndHamiltonian_eq_signedHamiltonian] at hv
  exact ω.eq_zero_of_dysonSeriesLeft_signedHamiltonian_apply_eq_self p.endSign_mul_endSign hL hHs hH
    hx hxper hnd hv

/-- A `1`-periodic orbit of a `C²` Hamiltonian whose linearized return map has no nonzero fixed
vector is isolated among `1`-periodic orbits. -/
private theorem exists_pos_forall_periodic_eq_of_dysonSeriesLeft
    (hHs : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0) :
    ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) →
      (∀ t, dist (y t) (x t) < δ) → y = x := by
  obtain ⟨δ, hδ, C, _, hclose⟩ := exists_forall_norm_sub_le_mul_integral_of_nondegenerate hHs hx
    (by simpa using hxper 0) hnd
  refine ⟨δ, hδ, fun y hyper hy hyx ↦ funext fun t ↦ ?_⟩
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun s ↦ (hy s).continuousAt
  have hγ' : Continuous fun s ↦ ω.hamiltonianVectorField (H s) (y s) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (hHs.of_le one_le_two)).continuous.comp
      (continuous_id.prodMk hyc)
  have hle := hclose hγ' hy (by simpa using hyper 0)
    (fun s _ ↦ by rw [← dist_eq_norm]; exact (hyx s).le)
  simp only [sub_self, norm_zero, intervalIntegral.integral_zero, mul_zero] at hle
  obtain ⟨t', ht', heq⟩ := (hyper.sub hxper).exists_mem_Ico₀ one_pos t
  have h0 : y t' - x t' = 0 := norm_le_zero_iff.1 (hle t' (Ico_subset_Icc_self ht'))
  have heq' : y t - x t = y t' - x t' := by simpa only [Pi.sub_apply] using heq
  exact sub_eq_zero.1 (heq'.trans h0)

/-- In `p.endChart` at `(ε R, t)`, the distance from `d(u ∘ p.endChart)` to `dt ⊗ X_{H_t}(x(t))`
equals the distance in `positive.endChart` at `(R, ε t)` from `d(u ∘ positive.endChart)` to
`dt ⊗ X_{H'_p(ε t)}(x(ε (ε t)))`. -/
theorem norm_fderiv_comp_pssPlane_endChart_sub_smulRight (p : PSSPlane) (u : ℝ × ℝ → V)
    (H : ℝ → V → ℝ) (x : ℝ → V) (R t : ℝ) :
    ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ =
      ‖fderiv ℝ (u ∘ positive.endChart) (R, p.endSign * t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorField (p.positiveEndHamiltonian H (p.endSign * t))
            (x (p.endSign * (p.endSign * t))))‖ := by
  rw [p.fderiv_comp_endChart, p.endSign_smul_endSign_mul_mk, endSign_mul_endSign_mul,
    p.positiveEndHamiltonian_eq_signedHamiltonian]
  exact ω.norm_smul_sub_smulRight_hamiltonianVectorField p.endSign_mul_endSign _ H (x t) t

/-- **Exponential decay of the exterior energy of a PSS plane.** Let `K = H(t) dt` beyond `T₀` on
the end of `p` for a `1`-periodic `C²` Hamiltonian `H`, and let `u` be `C²` on `{‖w‖ > r}`, solving
`(du - X_K)^{0,1} = 0` there with finite energy. Suppose that on some half-cylinder `s > b` of
`positive.endChart` the almost complex structures are uniformly tame, and that the end loops
`t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a `1`-periodic orbit `x` of `H` whose
linearized return map has no nonzero fixed vector. Then the Floer energy of `u` over
`{‖w‖ ≥ exp (2π R)}` is eventually at most `C exp (-κ R)`, for some `κ > 0`. -/
theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlane_le_exp
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop)
    {b : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop,
      ∫⁻ z in {z | Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * R))) := by
  -- Reduce to the positive half-cylinder `(a, ∞) × ℝ` via `floer_comp_pssPlane_endChart_positive`.
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r (max T₀ b)
  have haT : T₀ ≤ a := (le_max_left _ _).trans ha
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := ((le_max_right _ _).trans ha).trans_lt hz
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable two_ne_zero).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hu', hper', -, hfloer', hE'⟩ := floer_comp_pssPlane_endChart_positive hKH hH hHd
    two_ne_zero haT hr hu (fun _ _ ↦ mem_univ _) hfloer hE
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp
    (a := a) (J := J ∘ positive.endChart) (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (p.periodic_positiveEndHamiltonian hH) hu' hper' hc
    (fun z hz v ↦ hJc z (hab hz.1) v) (fun z hz v ↦ hJM z (hab hz.1) v) hfloer' hE'
    (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian p hx)
    (fun v hv ↦ hnd v
      ((dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff p hHs hH hxc hxper).1 hv))
    (tendstoUniformly_comp_endChart_positive hconv)
  -- Change variables from `[R, ∞) × [0, 1]` back to `{‖w‖ ≥ exp (2π R)}`.
  refine ⟨κ, hκ, C, (hdecay.and (eventually_gt_atTop a)).mono fun R ⟨hR, hRa⟩ ↦ ?_⟩
  have hrR : r < Real.exp (2 * π * R) :=
    hr.trans_lt (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hRa Real.two_pi_pos))
  rw [← setLIntegral_floerEnergyDensity_comp_pssPlane_endChart_positive_Ici_eq hKH hH hHd
    (haT.trans hRa.le) fun z hz ↦ (hu.differentiableOn two_ne_zero z (hrR.trans_le hz)
      ).differentiableAt ((isOpen_lt_norm_equivRealProdCLM_symm r).mem_nhds (hrR.trans_le hz))]
  exact hR

/-- **Conditional `C⁰` exponential convergence of the end of a PSS plane.** Under the hypotheses of
`exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlane_le_exp`, if moreover
`∂_s(u ∘ positive.endChart)` is bounded on `s > b`, then the end loops `t ↦ u(φ_p(ε R, t))`
converge to `x` exponentially fast: eventually `‖u(φ_p(ε R, t)) - x(t)‖ ≤ C exp (-κ R)` for every
`t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_pssPlane_endChart
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop)
    {b L : ℝ} (hL : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z (1, 0)‖ ≤ L)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖u (p.endChart (p.endSign * R, t)) - x t‖ ≤ C * Real.exp (-(κ * R)) := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r (max T₀ b)
  have haT : T₀ ≤ a := (le_max_left _ _).trans ha
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := ((le_max_right _ _).trans ha).trans_lt hz
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable two_ne_zero).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hu', hper', -, hfloer', hE'⟩ := floer_comp_pssPlane_endChart_positive hKH hH hHd
    two_ne_zero haT hr hu (fun _ _ ↦ mem_univ _) hfloer hE
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_sub_le_exp (a := a) (L := L)
    (J := J ∘ positive.endChart) (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (p.periodic_positiveEndHamiltonian hH) hu' hper' hc
    (fun z hz v ↦ hJc z (hab hz.1) v) (fun z hz v ↦ hJM z (hab hz.1) v) hfloer' hE'
    (fun z hz ↦ hL z (hab hz.1)) (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian p hx)
    (fun v hv ↦ hnd v
      ((dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff p hHs hH hxc hxper).1 hv))
    (tendstoUniformly_comp_endChart_positive hconv)
  refine ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ ?_⟩
  have h := hR (p.endSign * t)
  rwa [comp_apply, ← p.endChart_endSign_mul, endSign_mul_endSign_mul] at h

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {W : Set (ℝ × V)}
  {J₀ : ℝ → V → AlmostComplexStructure V}

/-! ### Exponential decay of derivatives and `C¹` convergence on cylindrical ends -/

/-- **Exponential `C¹` convergence of `d(u ∘ φ_p)` along a cylindrical end of a PSS plane.** Let
`K = H(t) dt` beyond `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian `H`, and let `u` be
`C³` on `{‖w‖ > r}`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` there with
finite energy. Suppose that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`, and that the end loops `t ↦ u(φ_p(ε R, t))` converge
uniformly as `R → ∞` to a `1`-periodic orbit `x` of `H` whose linearized return map has no nonzero
fixed vector. Then `d(u ∘ φ_p)(ε R, t)` converges exponentially to `dt ⊗ X_{H_t}(x(t))`:
eventually `‖d(u ∘ φ_p)(ε R, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C exp (-κ R)` for every `t`. -/
theorem exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * R)) := by
  -- Pull the cylindrical end back to `positive.endChart` on `(a, ∞) × ℝ`.
  obtain ⟨a, haT, hr⟩ := exists_le_and_le_exp r T₀
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable (by norm_num)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hW', hJ₀', hJ₀per', hBW', hJ₀t', hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive_of_cylindrical hKH hH hHd (by norm_num) haT hr hu huB
      hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  -- Apply half-cylinder `C¹` exponential convergence to `u ∘ positive.endChart`, then reflect
  -- `(R, ε t)` back to `(ε R, t)` via `norm_fderiv_comp_pssPlane_endChart_sub_smulRight`.
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp
    (p.contDiff_uncurry_positiveEndHamiltonian hHs) (p.periodic_positiveEndHamiltonian hH)
    hW' hJ₀' hJ₀per' hB hBW' hJ₀t' hu' hper' huB' hfloer' hE'
    (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian p hx)
    (fun v hv ↦ hnd v ((dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self_iff p
      (hHs.of_le (by norm_num)) hH hxc hxper).1 hv))
    (tendstoUniformly_comp_endChart_positive hconv)
  refine ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ ?_⟩
  rw [norm_fderiv_comp_pssPlane_endChart_sub_smulRight]
  exact hR (p.endSign * t)

/-- **Exponential decay of `∂_s(u ∘ φ_p)` along a cylindrical end of a PSS plane.** Under the
hypotheses of `exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp`,
`∂_s(u ∘ φ_p)` decays exponentially: eventually `‖d(u ∘ φ_p)(ε R, t)(1, 0)‖ ≤ C exp (-κ R)` for
every `t`. -/
theorem exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_apply_one_zero_le_exp
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) (1, 0)‖ ≤ C * Real.exp (-(κ * R)) := by
  obtain ⟨κ, hκ, C, h⟩ :=
    exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp p hKH hH hHs hu
      hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ hxper hx hnd hconv
  refine ⟨κ, hκ, C, h.mono fun R hR t ↦ ?_⟩
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hle := (fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))).le_opNorm
    (1, 0)
  rw [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', zero_smul, sub_zero, h10, mul_one] at hle
  exact hle.trans (hR t)

/-- **Unconditional `C¹` exponential convergence on a cylindrical end of a PSS plane.** Let
`K = H(t) dt` beyond `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian `H`, and let `u` be
`C³` on `{‖w‖ > r}`, with image in a compact set `B` in which every `1`-periodic orbit of `H` has
no nonzero fixed vector under the linearized return map, solving `(du - X_K)^{0,1} = 0` there with
finite energy. Suppose that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`. Then there exist a `1`-periodic orbit `x` of `H`, a
rate `κ > 0`, and a constant `C` such that eventually as `R → ∞`, for every `t`, `u ∘ φ_p` is
differentiable at `(ε R, t)` and both `‖(u ∘ φ_p)(ε R, t) - x(t)‖` and
`‖d(u ∘ φ_p)(ε R, t) - dt ⊗ X_{H_t}(x(t))‖` are at most `C exp (-κ R)`. -/
theorem exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∀ v, dysonSeriesLeft
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
        DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign * R, t) ∧
        ‖(u ∘ p.endChart) (p.endSign * R, t) - x t‖ ≤ C * Real.exp (-(κ * R)) ∧
        ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (-(κ * R)) := by
  have hHs2 : ContDiff ℝ 2 (uncurry H) := hHs.of_le (by norm_num)
  obtain ⟨b, L, c, hc, M, hL, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le_and_tame p hKH hH hHs hu hB huB
      hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ
  -- Linearized nondegeneracy isolates every `1`-periodic orbit in `B`, giving full-end convergence.
  obtain ⟨x, hxper, hx, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical_of_isolated p
      hKH hH hHs hu hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ fun y hyper hy hyB ↦ by
        obtain ⟨δ, hδ, hiso⟩ := exists_pos_forall_periodic_eq_of_dysonSeriesLeft hHs2 hyper hy
          (hnd y hyper hy hyB)
        exact ⟨δ, hδ, fun z hzper hz _ hzy ↦ hiso z hzper hz hzy⟩
  obtain ⟨a, -, hr⟩ := exists_le_and_le_exp r 0
  have hxB (t : ℝ) : x t ∈ B := by
    refine hB.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop a).mono fun R hR ↦ huB _ ?_)
    rw [endChart_endSign_mul]
    exact lt_norm_equivRealProdCLM_symm_endChart_positive hr hR
  have hndx := hnd x hxper hx hxB
  -- Combine the `C⁰` and `C¹` eventual exponential bounds into one rate and constant.
  obtain ⟨κ₀, hκ₀, C₀, h₀⟩ := exists_pos_eventually_norm_sub_le_exp_pssPlane_endChart p hKH hH hHs2
    (hu.of_le (by norm_num)) hfloer hE hxper hx hndx hconv
    (fun z hz ↦ ((fderiv ℝ (u ∘ positive.endChart) z).le_opNorm _).trans (by simpa using hL z hz))
    hc hJc hJM
  obtain ⟨κ₁, hκ₁, C₁, h₁⟩ :=
    exists_pos_eventually_norm_fderiv_comp_pssPlane_endChart_sub_smulRight_le_exp p hKH hH hHs hu hB
      huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ hxper hx hndx hconv
  obtain ⟨κ, hκ, C, h⟩ := exists_pos_eventually_forall_le_mul_exp (ι := Bool)
    (f := fun i R t ↦ bif i then
      ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖
      else ‖(u ∘ p.endChart) (p.endSign * R, t) - x t‖)
    (Bool.forall_bool.2 ⟨⟨κ₀, hκ₀, C₀, h₀⟩, ⟨κ₁, hκ₁, C₁, h₁⟩⟩)
  refine ⟨x, hxper, hx, κ, hκ, C, ?_⟩
  filter_upwards [h, eventually_gt_atTop a] with R hR hRa t
  have hd : DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign * R, t) := by
    rw [p.differentiableAt_comp_endChart_iff, p.endSign_smul_endSign_mul_mk]
    exact (differentiableAt_endChart_positive (hu.differentiableOn (by norm_num)) hr hRa).comp _
      (positive.contDiff_endChart.differentiable one_ne_zero _)
  exact ⟨hd, hR false t, hR true t⟩

/-- **Unconditional `C¹` exponential convergence on a cylindrical end (fixed-point nondegeneracy).**
Specialization of `exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp` when the
suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `B` starts at a
nondegenerate fixed point of the time-one map. -/
theorem
    exists_pos_eventually_norm_sub_and_fderiv_pssPlane_endChart_le_exp_of_isNondegenerateFixedPt
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
        DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign * R, t) ∧
        ‖(u ∘ p.endChart) (p.endSign * R, t) - x t‖ ≤ C * Real.exp (-(κ * R)) ∧
        ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (-(κ * R)) :=
  exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp p hKH hH hHs hu hB huB
    hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ fun x hxper hx hxB _ hv ↦
      ω.eq_zero_of_dysonSeriesLeft_apply_eq_self_of_isNondegenerateFixedPt hL
        (hHs.of_le (by norm_num)) hx (hnd x hxper hx hxB) hv

/-- **Unconditional `C¹` exponential convergence as `s → -∞` on the negative PSS plane.** Let
`K = H(t) dt` for `re (negative.endCoord w) ≤ T₀` on `PSSPlane.negative` (for instance
`K = negative.perturbation H` with `T₀ = -2`), and suppose that `J(negative.endChart (s, t)) =
J₀(t, u(negative.endChart (s, t)))` for `s ≤ T₀` and every `1`-periodic orbit of `H` in `B` has no
nonzero fixed vector under the linearized return map. Then there exist a `1`-periodic orbit `x` of
`H`, a rate `κ > 0`, and a constant `C` such that eventually as `s → -∞` (`atBot`), for every `t`,
`u ∘ negative.endChart` is differentiable at `(s, t)` and both
`‖(u ∘ negative.endChart)(s, t) - x(t)‖` and
`‖d(u ∘ negative.endChart)(s, t) - dt ⊗ X_{H_t}(x(t))‖` are at most `C exp (κ s)`. -/
theorem exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_pssPlane_endChart_negative_le_exp
    (hKH : ∀ w x, w ≠ 0 → (negative.endCoord w).re ≤ T₀ →
      K w x = H (negative.endCoord w).im x • negative.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, s ≤ T₀ →
      J (negative.endChart (s, t)) = J₀ t (u (negative.endChart (s, t))))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∀ v, dysonSeriesLeft
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atBot, ∀ t,
        DifferentiableAt ℝ (u ∘ negative.endChart) (s, t) ∧
        ‖(u ∘ negative.endChart) (s, t) - x t‖ ≤ C * Real.exp (κ * s) ∧
        ‖fderiv ℝ (u ∘ negative.endChart) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (κ * s) := by
  obtain ⟨x, hxper, hx, κ, hκ, C, h⟩ :=
    exists_pos_eventually_norm_sub_and_fderiv_comp_pssPlane_endChart_le_exp negative (T₀ := -T₀)
      (fun w y hw hre ↦ hKH w y hw (by simp only [endSign_negative, neg_one_mul] at hre; linarith))
      hH hHs hu hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t
      (fun s t hs ↦ by simpa only [endSign_negative, neg_one_mul] using hJ (-s) t (by linarith))
      hnd
  refine ⟨x, hxper, hx, κ, hκ, C, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually h] with s hs t
  simpa only [endSign_negative, neg_one_mul, mul_neg, neg_neg] using hs t

/-- **Unconditional `C¹` exponential convergence as `s → -∞` on the negative PSS plane
(fixed-point nondegeneracy).** Specialization of
`exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_pssPlane_endChart_negative_le_exp` when the
suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `B` starts at a
nondegenerate fixed point of the time-one map. -/
theorem
    exists_pos_eventually_atBot_pssPlane_endChart_negative_le_exp_of_isNondegenerateFixedPt
    (hKH : ∀ w x, w ≠ 0 → (negative.endCoord w).re ≤ T₀ →
      K w x = H (negative.endCoord w).im x • negative.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJ : ∀ s t, s ≤ T₀ →
      J (negative.endChart (s, t)) = J₀ t (u (negative.endChart (s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atBot, ∀ t,
        DifferentiableAt ℝ (u ∘ negative.endChart) (s, t) ∧
        ‖(u ∘ negative.endChart) (s, t) - x t‖ ≤ C * Real.exp (κ * s) ∧
        ‖fderiv ℝ (u ∘ negative.endChart) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (κ * s) :=
  exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_pssPlane_endChart_negative_le_exp hKH hH hHs
    hu hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ fun x hxper hx hxB _ hv ↦
      ω.eq_zero_of_dysonSeriesLeft_apply_eq_self_of_isNondegenerateFixedPt hL
        (hHs.of_le (by norm_num)) hx (hnd x hxper hx hxB) hv

end InnerProductSpace

end TauCeti.SymplecticForm
