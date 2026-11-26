/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Convergence
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Exponential convergence at the end of a PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞` and end
lift `φ` (`p.cylindricalEndLift`), and let `𝔎 : ℂ → V → ℂ →L[ℝ] ℝ` be a Hamiltonian perturbation on
`ℂ` with values in a symplectic vector space `(V, ω)` that equals `H(t) dt` beyond signed
longitudinal height `T₀` on the end of `p`, for a period-one Hamiltonian `H : ℝ → V → ℝ` (for
instance `𝔎 = p.perturbation H` with `T₀ = 2`, or `TauCeti.Floer.negativePlanePerturbation H` on the
negative plane). Adapting `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.ExponentialDecay` to
the PSS planes, when the end loops `ℓ_R(t) = u(φ(ε R + i t))` of a finite-energy Floer solution `u`
on `{‖w‖ > r}` converge uniformly as `R → ∞` to a nondegenerate `1`-periodic orbit `x` of `H`, this
file proves that the exterior Floer energy of `u` decays exponentially, and that `u ∘ realChart φ`
converges exponentially to the stationary cylinder `(s, t) ↦ x(t)` in `C⁰` and `C¹`, without
requiring a global Lipschitz hypothesis on `H`.

**Exterior energy decay and conditional `C⁰` exponential convergence.** On the positive plane,
pulling `u` back along `realChart φ_+` reduces to a finite-energy Floer half-cylinder for `H(t) dt`
(`TauCeti.SymplecticForm.floer_comp_realChart_positive_of_eq_smul_endAngularForm`). Applying
`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp` and
changing variables back via
`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ici_eq` shows that
for a `C²` solution on `{‖w‖ > r}` with uniformly tame almost complex structures on the end, the
Floer energy over `{‖w‖ ≥ exp (2πR)}` is eventually at most `C exp (-κ R)`
(`exists_pos_eventually_setLIntegral_floerEnergyDensity_le_exp_of_eq_smul_endAngularForm`). On the
negative plane, fixed vectors of the linearized return map of `-H(-t)` along `t ↦ x(-t)` transfer to
`H` along `x` (`dysonSeriesLeft_fderiv_hamiltonianVectorField_apply_eq_self_of_reverse`). Under a
bound on `∂_s(u ∘ realChart φ)`, `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp`
gives `‖ℓ_R(t) - x(t)‖ ≤ C exp (-κ R)`
(`exists_pos_eventually_norm_sub_le_exp_of_eq_smul_endAngularForm`).

**Cylindrical ends and `C¹` exponential convergence.** When `H` and `u` are `C³` and the almost
complex structure beyond `T₀` is cylindrical,
`J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a `1`-periodic family `Jq` which is
`C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, the half-cylinder `C¹` decay theorem
`TauCeti.SymplecticForm.exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp` shows that
`d(u ∘ realChart φ)(ε R, t)` converges exponentially to `dt ⊗ X_{H_t}(x(t))`
(`exists_pos_eventually_norm_fderiv_comp_realChart_sub_smulRight_le_exp_of_cylindrical`). When
every `1`-periodic orbit of `H` in `K` is linearly nondegenerate,
`TauCeti.SymplecticForm.exists_pos_forall_periodic_eq_of_nondegenerate` supplies the orbit
isolation hypothesis of `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Convergence` on the
cylindrical end, giving unconditional `C¹` exponential convergence to a `1`-periodic orbit `x`
along the end (`exists_pos_eventually_norm_sub_and_fderiv_comp_realChart_le_exp_of_cylindrical`),
its `s → -∞` (`atBot`) form on the negative plane
(`exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_realChart_negative_le_exp`) matching the
negative-end hypothesis of neck pre-gluing
(`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`), and the specializations
to `p.perturbation H` with fixed-point nondegeneracy
(`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`,
`exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation`,
`exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
* J. Robbin and D. Salamon, *Asymptotic behaviour of holomorphic strips*, Ann. Inst. H. Poincaré
  Anal. Non Linéaire 18 (2001), 573–612.
-/

public section

open Set Real Function Filter MeasureTheory
open TauCeti.Complex (realChart realChart_apply realChart_mk contDiff_realChart
  isOpen_setOf_lt_norm_equivRealProdCLM_symm)
open scoped ENNReal NNReal Topology Manifold

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}

/-- Shared `C²` half-cylinder setup on `(a, ∞)` for the positive PSS plane. -/
private theorem floer_positive_of_tendstoUniformly
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r b : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V}
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) x atTop)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart positive.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, ‖J (realChart positive.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ a : ℝ, T₀ ≤ a ∧ r ≤ Real.exp (2 * π * a) ∧ (∀ z : ℝ × ℝ, a < z.1 → b < z.1) ∧
      ContDiffOn ℝ 2 (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ ω v ((J ∘ realChart positive.cylindricalEndLift) z v)) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
        ‖(J ∘ realChart positive.cylindricalEndLift) z v‖ ≤ M * ‖v‖) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart positive.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ ∧
      TendstoUniformly (fun R t ↦ (u ∘ realChart positive.cylindricalEndLift) (R, t)) x atTop := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp_mul Real.two_pi_pos r (max T₀ b)
  have haT : T₀ ≤ a := (le_max_left _ _).trans ha
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := ((le_max_right _ _).trans ha).trans_lt hz
  obtain ⟨hu', hper', -, hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH
      (fun t ↦ (hHs.of_uncurry_left t).differentiable two_ne_zero) two_ne_zero haT hr hu
      (fun _ _ ↦ mem_univ _) hfloer hE
  refine ⟨a, haT, hr, hab, hu', hper', fun z hz v ↦ hJc z (hab z hz.1) v,
    fun z hz v ↦ hJM z (hab z hz.1) v, hfloer', hE', ?_⟩
  simpa only [comp_apply, realChart_mk, endSign_positive, one_mul] using hconv

/-- Exterior energy exponential decay on the positive PSS plane. -/
private theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_positive_le_exp
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) x atTop)
    {b : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart positive.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, ‖J (realChart positive.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop,
      ∫⁻ z in {z | Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * R))) := by
  obtain ⟨a, haT, hr, -, hu', hper', hJc', hJM', hfloer', hE', hconv'⟩ :=
    floer_positive_of_tendstoUniformly h𝔎 hH hHs hu hfloer hE hconv hJc hJM
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp
    (a := a) hHs hH hu' hper' hc hJc' hJM' hfloer' hE' hxper hx hnd hconv'
  refine ⟨κ, hκ, C, (hdecay.and (eventually_gt_atTop a)).mono fun R ⟨hR, hRa⟩ ↦ ?_⟩
  have hrR : r < Real.exp (2 * π * R) :=
    hr.trans_lt (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hRa Real.two_pi_pos))
  rw [← ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_Ici_eq h𝔎 hH
    (fun t ↦ (hHs.of_uncurry_left t).differentiable two_ne_zero)
    (haT.trans hRa.le) fun z hz ↦
      (hu.contDiffAt ((isOpen_setOf_lt_norm_equivRealProdCLM_symm r).mem_nhds
        (hrR.trans_le hz))).differentiableAt two_ne_zero]
  exact hR

omit [FiniteDimensional ℝ V] in
/-- Transfers uniform tameness bounds on `J ∘ realChart negative.cylindricalEndLift` over
`{z | b < negative.endSign * z.1}` to `J ∘ realChart positive.cylindricalEndLift` over
`{z | b < z.1}`. -/
private theorem tame_comp_realChart_positive_of_negative {b : ℝ}
    (hJc : ∀ z : ℝ × ℝ, b < negative.endSign * z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart negative.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < negative.endSign * z.1 →
      ∀ v, ‖J (realChart negative.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    (∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart positive.cylindricalEndLift z) v)) ∧
    ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, ‖J (realChart positive.cylindricalEndLift z) v‖ ≤ M * ‖v‖ := by
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;>
    rw [← neg_neg z, ← realChart_cylindricalEndLift_negative]
  · exact hJc (-z) (by simpa [endSign_negative] using hz)
  · exact hJM (-z) (by simpa [endSign_negative] using hz)

/-- Time reversal transfers a nondegenerate `1`-periodic orbit `x` of `H` along which the negative
end of `u` converges to the `1`-periodic orbit `t ↦ x(-t)` of `-H(-t)` along which the positive end
of `u` converges. -/
private theorem reverse_orbit_negative (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (negative.cylindricalEndLift (↑(negative.endSign * R) + ↑t * Complex.I)))) x atTop) :
    (∀ t, HasDerivAt (fun s ↦ x (-s))
      (ω.hamiltonianVectorField (fun y ↦ -H (-t) y) (x (-t))) t) ∧
    (∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (fun y ↦ -H (-t) y)) (x (-t))) 1 v = v →
      v = 0) ∧
    TendstoUniformly (fun R (t : ℝ) ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))))
      (fun t ↦ x (-t)) atTop := by
  have hx' (t : ℝ) : HasDerivAt (fun s ↦ x (-s))
      (ω.hamiltonianVectorField (fun y ↦ -H (-t) y) (x (-t))) t :=
    ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg (G := fun y ↦ -H (-t) y)
      (by simpa only [neg_neg, Pi.neg_def] using hx (-t))
  have hxc : Continuous fun t ↦ x (-t) :=
    (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt).comp continuous_neg
  refine ⟨hx', fun v hv ↦ hnd v ?_, ?_⟩
  · simpa only [neg_neg] using
      ω.dysonSeriesLeft_fderiv_hamiltonianVectorField_apply_eq_self_of_reverse hHs hH hxc
        hxper.comp_neg hv
  · simpa only [Function.comp_def, cylindricalEndLift_negative_endSign_mul, neg_neg] using
      hconv.comp fun t : ℝ ↦ -t

/-! ### Exterior energy decay and conditional `C⁰` exponential convergence -/

/-- **Exponential decay of the exterior energy of a PSS plane.** Let `𝔎` agree with `H(t) dt` beyond
signed height `T₀` on the end of `p` for a `1`-periodic `C²` Hamiltonian `H`, and let `u` be `C²` on
`{‖w‖ > r}`, solving `(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that on some
half-cylinder `ε s > b` the almost complex structures are uniformly tame, and that the end loops
`t ↦ u(φ(ε R + i t))` converge uniformly as `R → ∞` to a `1`-periodic orbit `x` of `H` whose
linearized return map fixes no nonzero vector. Then the Floer energy of `u` over
`{‖w‖ ≥ exp (2πR)}` is eventually at most `C exp (-κ R)`, for some `κ > 0`. -/
theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_le_exp_of_eq_smul_endAngularForm
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop)
    {b : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart p.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, ‖J (realChart p.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop,
      ∫⁻ z in {z | Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * R))) := by
  cases p
  · exact exists_pos_eventually_setLIntegral_floerEnergyDensity_positive_le_exp
      (fun w y hw hz ↦ h𝔎 w y hw (by simpa [endSign_positive] using hz)) hH hHs hu hfloer hE
      hxper hx hnd hconv hc
      (fun z hz ↦ hJc z (by simpa [endSign_positive] using hz))
      (fun z hz ↦ hJM z (by simpa [endSign_positive] using hz))
  obtain ⟨hx', hnd', hconv'⟩ := reverse_orbit_negative hH hHs hxper hx hnd hconv
  obtain ⟨hJc', hJM'⟩ := tame_comp_realChart_positive_of_negative hJc hJM
  exact exists_pos_eventually_setLIntegral_floerEnergyDensity_positive_le_exp
    (fun w y hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 y hw hz)
    (hH.comp_neg.comp Neg.neg) hHs.uncurry_comp_neg.neg hu hfloer hE hxper.comp_neg hx' hnd' hconv'
    hc hJc' hJM'

/-- Conditional `C⁰` exponential convergence on the positive PSS plane. -/
private theorem exists_pos_eventually_norm_sub_le_exp_positive_of_eq_smul
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) x atTop)
    {b L : ℝ}
    (hL : ∀ z : ℝ × ℝ, b < z.1 →
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) z (1, 0)‖ ≤ L)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart positive.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, ‖J (realChart positive.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I))) - x t‖ ≤
        C * Real.exp (-(κ * R)) := by
  obtain ⟨a, -, -, hab, hu', hper', hJc', hJM', hfloer', hE', hconv'⟩ :=
    floer_positive_of_tendstoUniformly h𝔎 hH hHs hu hfloer hE hconv hJc hJM
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_sub_le_exp (a := a) (L := L)
    hHs hH hu' hper' hc hJc' hJM' hfloer' hE' (fun z hz ↦ hL z (hab z hz.1)) hxper hx hnd hconv'
  refine ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ ?_⟩
  simpa only [comp_apply, realChart_mk, endSign_positive, one_mul] using hR t

/-- **Conditional `C⁰` exponential convergence of the end of a PSS plane.** Under the hypotheses of
`exists_pos_eventually_setLIntegral_floerEnergyDensity_le_exp_of_eq_smul_endAngularForm`, if
moreover `∂_s(u ∘ realChart φ)` is bounded on `ε s > b`, then the end loops
`t ↦ u(φ(ε R + i t))` converge to `x` exponentially fast: eventually
`‖u(φ(ε R + i t)) - x(t)‖ ≤ C exp (-κ R)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_of_eq_smul_endAngularForm
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop)
    {b L : ℝ}
    (hL : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z (1, 0)‖ ≤ L)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart p.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, ‖J (realChart p.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))) - x t‖ ≤
        C * Real.exp (-(κ * R)) := by
  cases p
  · exact exists_pos_eventually_norm_sub_le_exp_positive_of_eq_smul
      (fun w y hw hz ↦ h𝔎 w y hw (by simpa [endSign_positive] using hz)) hH hHs hu hfloer hE
      hxper hx hnd hconv (fun z hz ↦ hL z (by simpa [endSign_positive] using hz)) hc
      (fun z hz ↦ hJc z (by simpa [endSign_positive] using hz))
      (fun z hz ↦ hJM z (by simpa [endSign_positive] using hz))
  obtain ⟨hx', hnd', hconv'⟩ := reverse_orbit_negative hH hHs hxper hx hnd hconv
  obtain ⟨hJc', hJM'⟩ := tame_comp_realChart_positive_of_negative hJc hJM
  have hL' (z : ℝ × ℝ) (hz : b < z.1) :
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) z (1, 0)‖ ≤ L := by
    rw [fderiv_comp_realChart_cylindricalEndLift_positive, neg_apply, norm_neg]
    exact hL (-z) (by simpa [endSign_negative] using hz)
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_sub_le_exp_positive_of_eq_smul
    (fun w y hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 y hw hz)
    (hH.comp_neg.comp Neg.neg) hHs.uncurry_comp_neg.neg hu hfloer hE hxper.comp_neg hx' hnd' hconv'
    hL' hc hJc' hJM'
  refine ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ ?_⟩
  simpa only [cylindricalEndLift_negative_endSign_mul, neg_neg] using hR (-t)

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {Jq : ℝ → V → AlmostComplexStructure V} {K : Set V} {W : Set (ℝ × V)} {r : ℝ}

/-- The end lift of the negative plane is that of the positive plane after the reflection
`z ↦ -z`, and `X_{-H(t)} = -X_{H_t}`. So, read through the end lift of the negative plane at
`(-s, t)`, the distance of the derivative of `u` from that of the stationary cylinder of the orbit
`x` of `H` is the distance, read through the end lift of the positive plane at `(s, -t)`, of the
derivative of `u` from that of the stationary cylinder of the orbit `t ↦ x(-t)` of `-H(-t)`. -/
private theorem norm_fderiv_comp_realChart_negative_sub_smulRight (u : ℝ × ℝ → V) (x : ℝ → V)
    (s t : ℝ) :
    ‖fderiv ℝ (u ∘ realChart negative.cylindricalEndLift) (negative.endSign * s, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ =
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) (s, -t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (x (-(-t))))‖ := by
  have hX : ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (x (-(-t))) =
      -ω.hamiltonianVectorField (H t) (x t) := by
    simpa only [neg_neg, Pi.neg_def] using ω.hamiltonianVectorField_neg (H t) (x t)
  rw [fderiv_comp_realChart_cylindricalEndLift_negative, hX, ← norm_neg]
  congr 1
  ext <;> simp [add_comm]

/-! ### Exponential decay of derivatives and `C¹` convergence on cylindrical ends -/

/-- **Exponential `C¹` convergence of `d(u ∘ realChart φ)` along a cylindrical end of a PSS plane.**
Let `𝔎` agree with `H(t) dt` beyond signed height `T₀` on the end of `p` for a `1`-periodic `C³`
Hamiltonian `H`, and let `u` be `C³` on `{‖w‖ > r}`, with image in a compact set `K`, solving
`(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that for `s ≥ T₀` the almost complex
structure is cylindrical, `J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a
`1`-periodic family `Jq` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, and
that the end loops `t ↦ u(φ(ε R + i t))` converge uniformly as `R → ∞` to a `1`-periodic orbit `x`
of `H` whose linearized return map fixes no nonzero vector. Then `d(u ∘ realChart φ)(ε R, t)`
converges exponentially to `dt ⊗ X_{H_t}(x(t))`. -/
theorem exists_pos_eventually_norm_fderiv_comp_realChart_sub_smulRight_le_exp_of_cylindrical
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0)
    (hconv : TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * R)) := by
  obtain ⟨a, haT, hr⟩ := exists_le_and_le_exp_mul Real.two_pi_pos r T₀
  cases p
  · obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
      ω.floer_comp_realChart_positive_of_cylindrical
        (fun w y hw hz ↦ h𝔎 w y hw (by simpa [endSign_positive] using hz)) hH
        (fun t ↦ (hHs.of_uncurry_left t).differentiable (by norm_num)) (by norm_num) haT hr hu huK
        hfloer hE fun s t hs ↦ by simpa [endSign_positive] using hJ s t hs
    have hconv' : TendstoUniformly (fun R t ↦ (u ∘ realChart positive.cylindricalEndLift) (R, t))
        x atTop := by simpa only [comp_apply, realChart_mk, endSign_positive, one_mul] using hconv
    obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp hHs hH hW
      hJq hJqper hK hKW hJqt hu' hper' huK' hfloer' hE' hxper hx hnd hconv'
    exact ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ by simpa only [endSign_positive, one_mul] using hR t⟩
  -- Reduce the negative plane to `(Jq (-t), -H(-t))` along `t ↦ x(-t)`.
  obtain ⟨hx', hnd', hconv₀⟩ :=
    reverse_orbit_negative hH (hHs.of_le (by norm_num)) hxper hx hnd hconv
  obtain ⟨hH', hHs', hW', hJq', hJqper', hKW', hJqt', hu', hper', huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_negative_of_cylindrical h𝔎 hH hHs (by norm_num) haT hr hu huK hfloer hE
      hW hJq hJqper hKW hJqt hJ
  have hconv' : TendstoUniformly (fun R t ↦ (u ∘ realChart positive.cylindricalEndLift) (R, t))
      (fun t ↦ x (-t)) atTop := by
    simpa only [comp_apply, realChart_mk, endSign_positive, one_mul] using hconv₀
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp hHs' hH' hW'
    hJq' hJqper' hK hKW' hJqt' hu' hper' huK' hfloer' hE' hxper.comp_neg hx' hnd' hconv'
  exact ⟨κ, hκ, C, hdecay.mono fun R hR t ↦
    (norm_fderiv_comp_realChart_negative_sub_smulRight u x R t).trans_le (hR (-t))⟩

/-- **Unconditional `C¹` exponential convergence on a cylindrical end of a PSS plane.** Let `𝔎`
agree with `H(t) dt` beyond signed height `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian
`H`, and let `u` be `C³` on `{‖w‖ > r}`, with image in a compact set `K` in which every `1`-periodic
orbit of `H` has no nonzero fixed vector under the linearized return map, solving
`(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that for `s ≥ T₀` the almost complex
structure is cylindrical, `J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a
`1`-periodic family `Jq` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then
there exist a `1`-periodic orbit `x` of `H`, a rate `κ > 0`, and a constant `C` such that eventually
as `R → ∞`, for every `t`, `u ∘ realChart φ` is differentiable at `(ε R, t)` and both
`‖(u ∘ realChart φ)(ε R, t) - x(t)‖` and `‖d(u ∘ realChart φ)(ε R, t) - dt ⊗ X_{H_t}(x(t))‖` are at
most `C exp (-κ R)`. -/
theorem exists_pos_eventually_norm_sub_and_fderiv_comp_realChart_le_exp_of_cylindrical
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∀ v, dysonSeriesLeft
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
        DifferentiableAt ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) ∧
        ‖(u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) - x t‖ ≤
          C * Real.exp (-(κ * R)) ∧
        ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (-(κ * R)) := by
  have hHs2 : ContDiff ℝ 2 (uncurry H) := hHs.of_le (by norm_num)
  obtain ⟨b, L, c, hc, M, hL, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le_and_tame p h𝔎 hH hHs hu hK huK
      hfloer hE hW hJq hJqper hKW hJqt hJ
  -- Linearized nondegeneracy isolates every `1`-periodic orbit in `K`, giving full-end convergence.
  obtain ⟨x, hxper, hx, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_cylindrical_of_isolated p h𝔎 hH hHs hu hK
      huK hfloer hE hW hJq hJqper hKW hJqt hJ fun y hyper hy hyK ↦ by
        obtain ⟨δ, hδ, hiso⟩ :=
          exists_pos_forall_periodic_eq_of_nondegenerate hHs2 hyper hy (hnd y hyper hy hyK)
        exact ⟨δ, hδ, fun z hzper hz _ hzy ↦ hiso z hzper hz hzy⟩
  obtain ⟨a, -, hr⟩ := exists_le_and_le_exp_mul Real.two_pi_pos r 0
  have hmem {R : ℝ} (hR : a < R) (t : ℝ) :
      r < ‖Complex.equivRealProdCLM.symm
        (realChart p.cylindricalEndLift (p.endSign * R, t))‖ :=
    p.lt_norm_symm_realChart_cylindricalEndLift_of_le_exp hr (by simpa [← mul_assoc] using hR)
  have hxK (t : ℝ) : x t ∈ K :=
    hK.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop a).mono fun R hR ↦ by rw [← realChart_mk]; exact huK _ (hmem hR t))
  have hndx := hnd x hxper hx hxK
  obtain ⟨κ₀, hκ₀, C₀, h₀⟩ := exists_pos_eventually_norm_sub_le_exp_of_eq_smul_endAngularForm p h𝔎
    hH hHs2 (hu.of_le (by norm_num)) hfloer hE hxper hx hndx hconv
    (fun z hz ↦ ((fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z).le_opNorm _).trans
      (by simpa using hL z hz))
    hc hJc hJM
  obtain ⟨κ₁, hκ₁, C₁, h₁⟩ :=
    exists_pos_eventually_norm_fderiv_comp_realChart_sub_smulRight_le_exp_of_cylindrical p h𝔎 hH hHs
      hu hK huK hfloer hE hW hJq hJqper hKW hJqt hJ hxper hx hndx hconv
  simp_rw [← realChart_mk, ← comp_apply (f := u)] at h₀
  obtain ⟨κ, hκ, C, h⟩ := exists_pos_eventually_forall_le_mul_exp (ι := Bool)
    (f := fun i R t ↦ bif i then
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖
      else ‖(u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) - x t‖)
    (Bool.forall_bool.2 ⟨⟨κ₀, hκ₀, C₀, h₀⟩, ⟨κ₁, hκ₁, C₁, h₁⟩⟩)
  refine ⟨x, hxper, hx, κ, hκ, C, ?_⟩
  filter_upwards [h, eventually_gt_atTop a] with R hR hRa t
  have hd : DifferentiableAt ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) :=
    ((hu.contDiffAt ((isOpen_setOf_lt_norm_equivRealProdCLM_symm r).mem_nhds
      (hmem hRa t))).differentiableAt (by norm_num)).comp _
      ((contDiff_realChart p.contDiff_cylindricalEndLift).differentiable one_ne_zero _)
  exact ⟨hd, hR false t, hR true t⟩

/-- **Unconditional `C¹` exponential convergence as `s → -∞` on the negative PSS plane.** Let `𝔎`
agree with `H(t) dt` for `(negative.endCoord w).re ≤ T₀` on `PSSPlane.negative`, and suppose that
`J(realChart φ_- (s, t)) = Jq(t, u(realChart φ_- (s, t)))` for `s ≤ T₀` and every `1`-periodic orbit
of `H` in `K` has no nonzero fixed vector under the linearized return map. Then there exist a
`1`-periodic orbit `x` of `H`, a rate `κ > 0`, and a constant `C` such that eventually as `s → -∞`
(`atBot`), for every `t`, `u ∘ realChart φ_-` is differentiable at `(s, t)` and both
`‖(u ∘ realChart φ_-)(s, t) - x(t)‖` and `‖d(u ∘ realChart φ_-)(s, t) - dt ⊗ X_{H_t}(x(t))‖` are at
most `C exp (κ s)`. -/
theorem exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_realChart_negative_le_exp
    (h𝔎 : ∀ w x, w ≠ 0 → (negative.endCoord w).re ≤ T₀ →
      𝔎 w x = H (negative.endCoord w).im x • negative.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, s ≤ T₀ →
      J (realChart negative.cylindricalEndLift (s, t)) =
        Jq t (u (realChart negative.cylindricalEndLift (s, t))))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∀ v, dysonSeriesLeft
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v → v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atBot, ∀ t,
        DifferentiableAt ℝ (u ∘ realChart negative.cylindricalEndLift) (s, t) ∧
        ‖(u ∘ realChart negative.cylindricalEndLift) (s, t) - x t‖ ≤ C * Real.exp (κ * s) ∧
        ‖fderiv ℝ (u ∘ realChart negative.cylindricalEndLift) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (κ * s) := by
  obtain ⟨x, hxper, hx, κ, hκ, C, h⟩ :=
    exists_pos_eventually_norm_sub_and_fderiv_comp_realChart_le_exp_of_cylindrical negative
      (T₀ := -T₀)
      (fun w y hw hre ↦ h𝔎 w y hw (by simp only [endSign_negative, neg_one_mul] at hre; linarith))
      hH hHs hu hK huK hfloer hE hW hJq hJqper hKW hJqt
      (fun s t hs ↦ by simpa only [endSign_negative, neg_one_mul] using hJ (-s) t (by linarith))
      hnd
  refine ⟨x, hxper, hx, κ, hκ, C, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually h] with s hs t
  simpa only [endSign_negative, neg_one_mul, mul_neg, neg_neg] using hs t

/-- **Exponential `C¹` convergence at the end of a PSS plane.** Let `𝔎` be the perturbation of a
PSS plane `p` given by a period-one `C³` Hamiltonian `H` whose suspended Hamiltonian vector field
is globally Lipschitz, and let `ε = p.endSign`. Let `u` be `C³` on a part `‖w‖ > r` of the end, with
image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there with finite
energy there. Suppose that the almost complex structure is cylindrical there,
`J(w) = J_t(u(w))` with `t = (p.endCoord w).im` the angular coordinate of `w`, for a one-periodic
family `J_t(x)` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, and that every
one-periodic orbit `x` of `H` in `K` is nondegenerate: `x(0)` is a nondegenerate fixed point of the
time-one map. Then the end of `u` converges exponentially fast in `C¹` to the stationary cylinder of
a one-periodic orbit `x` of `H`: with `φ` the end lift `p.cylindricalEndLift`, for some `κ > 0` and
`C`, eventually

`‖u(φ(ε s + i t)) - x(t)‖ + ‖d(u ∘ φ)(ε s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C exp (-κ s)`

for every `t`. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I))) - x t‖ +
            ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨a, ha2, hr⟩ := exists_le_and_le_exp_mul Real.two_pi_pos r 2
  have hJcyl (s t : ℝ) (hs : a + 1 ≤ s) :
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))) := by
    have hlt : r < ‖Complex.equivRealProdCLM.symm
        (realChart p.cylindricalEndLift (p.endSign * s, t))‖ :=
      p.lt_norm_symm_realChart_cylindricalEndLift_of_le_exp hr
        (by simpa [← mul_assoc] using (lt_add_one a).trans_le hs)
    rw [hJ _ hlt, TauCeti.Complex.equivRealProdCLM_symm_realChart,
      p.apply_im_endCoord_cylindricalEndLift hJqper]
    simp
  obtain ⟨x, hxper, hx, κ, hκ, C, h⟩ :=
    exists_pos_eventually_norm_sub_and_fderiv_comp_realChart_le_exp_of_cylindrical p
      (𝔎 := p.perturbation H) (T₀ := a + 1)
      (fun _ y _ hw ↦ p.perturbation_eq_smul_endAngularForm (by linarith) y) hH hHs hu hK huK
      hfloer hE hW hJq hJqper hKW hJqt hJcyl fun y hyper hy hyK _ hv ↦
        ω.eq_zero_of_dysonSeriesLeft_apply_eq_self hL (hHs.of_le (by norm_num)) hy
          (hnd y hyper hy hyK) hv
  refine ⟨x, hxper, hx, κ, hκ, C + C, h.mono fun s hs t ↦ ?_⟩
  rw [← realChart_mk, add_mul]
  exact add_le_add (hs t).2.1 (hs t).2.2

/-- **Exponential convergence at the end of a PSS plane.** Under the hypotheses of
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`, the loops
`ℓ_s(t) = u(φ(ε s + i t))` along the end converge exponentially fast to a one-periodic orbit `x`
of `H`: for some `κ > 0` and `C`, eventually `‖ℓ_s(t) - x(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I))) - x t‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation p hH hHs hu hK
      huK hfloer hE hW hJq hJqper hKW hJqt hJ hL hnd
  exact ⟨x, hxper, hx, κ, hκ, A,
    h.mono fun s hs t ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hs t)⟩

/-- **The end of a PSS plane converges to a nondegenerate orbit.** Under the hypotheses of
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`, the loops
`ℓ_s(t) = u(φ(ε s + i t))` along the end converge uniformly, as `s → ∞`, to a one-periodic orbit
of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation p hH hHs hu hK huK hfloer hE hW
      hJq hJqper hKW hJqt hJ hL hnd
  refine ⟨x, hxper, hx, Metric.tendstoUniformly_iff.2 fun δ hδ ↦ ?_⟩
  -- The bound `A exp (-κ s)` tends to `0`.
  have h0 : Tendsto (fun s ↦ A * Real.exp (-(κ * s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ)).const_mul A
  filter_upwards [h, h0.eventually (gt_mem_nhds hδ)] with s hs hsδ t
  rw [dist_comm, dist_eq_norm]
  exact (hs t).trans_lt hsδ

end InnerProductSpace

end TauCeti.SymplecticForm
