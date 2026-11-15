/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.Plane.Convergence

/-!
# Exponential decay and `C¹` exponential convergence at the end of a PSS plane

Let `𝔎` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from
a period-one Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the sign
of the end of `p` at `∞`. Let `u` be a finite-energy solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on an exterior neighborhood `‖w‖ > r` of `∞`. When the end loops
`t ↦ u(φ_p(ε R, t))` in the end chart `φ_p` (`TauCeti.Floer.PSSPlane.endChart`) converge uniformly
as `R → ∞` to a nondegenerate one-periodic orbit `x` of `H`, this file proves that the exterior
Floer energy of `u` decays exponentially, and that `u ∘ φ_p` converges exponentially to the
stationary cylinder `(s, t) ↦ x(t)` in `C⁰` and `C¹`.

**Nondegeneracy in the positive end chart.** In the positive end chart `φ_+ = positive.endChart`,
`u ∘ φ_+` solves the half-cylinder Floer equation for the positive end Hamiltonian
`H'_p(t, y) = ε H(ε t, y)` (`TauCeti.Floer.PSSPlane.positiveEndHamiltonian`) and converges
uniformly to the orbit `t ↦ x(ε t)` of `H'_p`. Because `dX_{H'_p(ε t)}(x(t)) = ε dX_{H_t}(x(t))`,
reversing time by `ε` conjugates periodic solutions of the linearized equation along `t ↦ x(ε t)`
to periodic solutions along `x`. Nondegeneracy of `x(0)` as a fixed point of the time-one map of
`H` therefore implies that the linearized return map of `H'_p` along `t ↦ x(ε t)` has no nonzero
fixed vector (`eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self`).

**Exterior energy decay and `C⁰` exponential convergence.** Applying
`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp` to
`u ∘ φ_+` and changing variables back via
`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ici_eq` shows that
for a `C²` solution on `{‖w‖ > r}` with uniformly tame almost complex structures on the end, the
Floer energy over `{‖w‖ ≥ exp (2π R)}` is eventually at most `C exp (-κ R)`
(`exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlanePerturbation_le_exp`). Under a
bound on `∂_s(u ∘ φ_+)`, `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` gives
`‖u(φ_p(ε R, t)) - x(t)‖ ≤ C exp (-κ R)`
(`exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation`).

**Cylindrical ends and `C¹` exponential convergence.** When `H` and `u` are `C³` and the almost
complex structure on the end beyond `T₀` is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`,
for a `1`-periodic family `J₀` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on
`ℝ × K`, the chain rule `d(u ∘ φ_p)(ε R, t) = ε d(u ∘ φ_+)(R, ε t)` cancels the sign in
`X_{H'_p(ε t)}(x(t)) = ε X_{H_t}(x(t))`. Consequently the full derivative `d(u ∘ φ_p)(ε R, t)`
converges exponentially to `dt ⊗ X_{H_t}(x(t))`
(`exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp`), and in particular
`∂_s(u ∘ φ_p)(ε R, t)` decays exponentially
(`exists_pos_eventually_norm_fderiv_comp_endChart_apply_one_zero_le_exp`). When every `1`-periodic
orbit of `H` in `K` is nondegenerate, combining this with
`exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation_of_cylindrical` yields
unconditional `C¹` exponential convergence to a `1`-periodic orbit `x` along the end
(`exists_pos_eventually_norm_sub_and_fderiv_comp_endChart_le_exp`), together
with its `s → -∞` (`atBot`) form for `negative.endChart`
(`exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_endChart_negative_le_exp`)
matching the negative-end hypothesis of neck pre-gluing
(`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`).

## Main results

* `TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self`:
  nondegeneracy of `x(0)` for the time-one map of `H` implies nondegeneracy of the linearized
  return map of `p.positiveEndHamiltonian H` along `t ↦ x(ε t)`.
* `exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlanePerturbation_le_exp`: exponential
  decay of the Floer energy of a PSS plane over `{‖w‖ ≥ exp (2π R)}`.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation`: conditional
  `C⁰` exponential convergence of the end loops of a PSS plane to a nondegenerate orbit.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp`,
  `TauCeti.SymplecticForm.exists_pos_eventually_norm_fderiv_comp_endChart_apply_one_zero_le_exp`:
  exponential `C¹` convergence of `d(u ∘ φ_p)` and exponential decay of `∂_s(u ∘ φ_p)` along a
  cylindrical end.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_and_fderiv_comp_endChart_le_exp`,
  `exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_endChart_negative_le_exp`:
  unconditional `C¹` exponential convergence on a cylindrical end (as `R → +∞` for either plane,
  and as `s → -∞` in `negative.endChart`).

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
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}

/-! ### Nondegeneracy, exterior energy decay, and `C⁰` exponential convergence -/

/-- **Nondegeneracy in the positive end chart of a PSS plane.** Let `x` be a `1`-periodic orbit of
a `1`-periodic `C²` Hamiltonian `H` whose suspended Hamiltonian vector field is globally Lipschitz,
and suppose that `x(0)` is a nondegenerate fixed point of the time-one map of `H`. Then for either
PSS plane `p`, the return map of the linearized equation of `p.positiveEndHamiltonian H` along the
orbit `t ↦ x(ε t)` has no nonzero fixed vector. -/
theorem eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self
    (p : PSSPlane) {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {v : V} (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t)) (x (p.endSign * t))) 1 v = v) :
    v = 0 := by
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  set S' : ℝ → V →L[ℝ] V := fun t ↦
    fderiv ℝ (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t)) (x (p.endSign * t))
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hSc : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hHs hxc
  have hS'c : Continuous S' := ω.continuous_fderiv_hamiltonianVectorField_comp
    (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (hxc.comp (continuous_const.mul continuous_id))
  have hS'p : Periodic S' 1 := fun t ↦ by
    simp only [S', p.periodic_positiveEndHamiltonian hH t]
    exact congrArg _ (p.periodic_comp_endSign_mul hxper t)
  have hS' (t : ℝ) : S' (p.endSign * t) = p.endSign • S t := by
    simp only [S', S, hamiltonianVectorField_pssPlane_positiveEndHamiltonian_endSign_mul,
      fderiv_const_smul_field, Pi.smul_apply, endSign_mul_endSign_mul]
  set ζ : ℝ → V := fun t ↦ dysonSeriesLeft S' (p.endSign * t) v
  have hζ (t : ℝ) : HasDerivAt ζ (S t (ζ t)) t := by
    have h := (hasDerivAt_dysonSeriesLeft_apply hS'c v (p.endSign * t)).scomp t
      ((hasDerivAt_id' t).const_mul p.endSign)
    rw [hS', mul_one, smul_apply, smul_smul, endSign_mul_endSign, one_smul] at h
    exact h
  have hζp : Periodic ζ 1 :=
    p.periodic_comp_endSign_mul ((periodic_dysonSeriesLeft_apply_iff hS'c hS'p v).2 hv)
  have hζ0 : ζ 0 = v := by simp [ζ, dysonSeriesLeft_zero]
  have hΨ : dysonSeriesLeft S 1 v = v := by
    rw [← hζ0, ← eq_dysonSeriesLeft_apply hSc hζ, ← zero_add (1 : ℝ), hζp 0]
  have hD := (ω.differentiable_timeDependentHamiltonianFlow hL hHs 0 1 (x 0)).hasFDerivAt
  refine (isNondegenerateFixedPt_iff.1 hnd).2.2 v ?_
  rw [hD.hasMFDerivAt.mfderiv,
    fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft ω hL hHs hx]
  simp only [zero_add, sub_zero]
  exact hΨ

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Uniform convergence of `t ↦ u(φ_p(ε R, t))` to `x` gives uniform convergence of
`t ↦ (u ∘ φ_+)(R, t)` to `t ↦ x(ε t)`. -/
private theorem tendstoUniformly_comp_endChart_positive {p : PSSPlane} {x : ℝ → V}
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop) :
    TendstoUniformly (fun R t ↦ (u ∘ positive.endChart) (R, t))
      (fun t ↦ x (p.endSign * t)) atTop := by
  have h : (fun R t ↦ (u ∘ positive.endChart) (R, t)) =
      fun R ↦ (fun t ↦ u (p.endChart (p.endSign * R, t))) ∘ fun t ↦ p.endSign * t := by
    funext R t
    simp only [comp_apply, endChart_endSign_mul, endSign_mul_endSign_mul]
  rw [h]
  exact hconv.comp _

/-- **Exponential decay of the exterior energy of a PSS plane.** Let `𝔎` be the perturbation of a
PSS plane `p` given by a `1`-periodic `C²` Hamiltonian `H` whose suspended Hamiltonian vector field
is globally Lipschitz, and let `u` be `C²` on `{‖w‖ > r}`, solving `(du - X_𝔎)^{0,1} = 0` there
with finite energy. Suppose that on some half-cylinder `s > b` of `positive.endChart` the almost
complex structures are uniformly tame, `c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖` with `c > 0`, and
that the end loops `t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a nondegenerate
`1`-periodic orbit `x` of `H`. Then the Floer energy of `u` over `{‖w‖ ≥ exp (2π R)}` is eventually
at most `C exp (-κ R)`, for some `κ > 0`. -/
theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlanePerturbation_le_exp
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop)
    {b : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop,
      ∫⁻ z in {z | Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * R))) := by
  set a := max (max 2 b) (Real.log r / (2 * π))
  have ha₂ : 2 ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hz
  have hmem (z : ℝ × ℝ) (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le one_le_two
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp
    (a := a) (J := J ∘ positive.endChart) (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (p.periodic_positiveEndHamiltonian hH)
    (hu.comp (positive.contDiff_endChart (n := 2)).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, endChart_add_one]) hc
    (fun z hz v ↦ hJc z (hab z hz.1) v) (fun z hz v ↦ hJM z (hab z hz.1) v)
    (fun z hz ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_endChart_positive p hH hHs1
      (ha₂.trans hz.1.le)
      ((hu.differentiableOn two_ne_zero).differentiableAt
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (hmem z hz.1)))
      (hfloer _ (hmem z hz.1)))
    (ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top p hH hHs1 ha₂
      (le_max_right _ _) (hu.differentiableOn two_ne_zero) hE)
    (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian (p := p) hx)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self p hL hHs
      hH hx hxper hnd hv)
    (tendstoUniformly_comp_endChart_positive hconv)
  refine ⟨κ, hκ, C, (hdecay.and (eventually_gt_atTop a)).mono fun R ⟨hR, hRa⟩ ↦ ?_⟩
  have hrR : r < Real.exp (2 * π * R) := by
    have h := hmem (R, 0) hRa
    rwa [norm_symm_endChart, endSign_positive, one_mul] at h
  rw [← ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ici_eq p hH hHs1
    (ha₂.trans hRa.le) hrR (hu.differentiableOn two_ne_zero)]
  exact hR

/-- **Exponential convergence of the end of a PSS plane to a nondegenerate orbit.** Under the
hypotheses of `exists_pos_eventually_setLIntegral_floerEnergyDensity_pssPlanePerturbation_le_exp`,
suppose moreover that `∂_s(u ∘ positive.endChart)` is bounded on `s > b`. Then the end loops
`t ↦ u(φ_p(ε R, t))` converge to `x` exponentially fast: for some `κ > 0` and `C`, eventually
`‖u(φ_p(ε R, t)) - x(t)‖ ≤ C exp (-κ R)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop)
    {b B : ℝ} (hB : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z (1, 0)‖ ≤ B)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖u (p.endChart (p.endSign * R, t)) - x t‖ ≤ C * Real.exp (-(κ * R)) := by
  set a := max (max 2 b) (Real.log r / (2 * π))
  have ha₂ : 2 ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hz
  have hmem (z : ℝ × ℝ) (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le one_le_two
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_sub_le_exp (a := a) (L := B)
    (J := J ∘ positive.endChart) (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (p.periodic_positiveEndHamiltonian hH)
    (hu.comp (positive.contDiff_endChart (n := 2)).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, endChart_add_one]) hc
    (fun z hz v ↦ hJc z (hab z hz.1) v) (fun z hz v ↦ hJM z (hab z hz.1) v)
    (fun z hz ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_endChart_positive p hH hHs1
      (ha₂.trans hz.1.le)
      ((hu.differentiableOn two_ne_zero).differentiableAt
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (hmem z hz.1)))
      (hfloer _ (hmem z hz.1)))
    (ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top p hH hHs1 ha₂
      (le_max_right _ _) (hu.differentiableOn two_ne_zero) hE)
    (fun z hz ↦ hB z (hab z hz.1))
    (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian (p := p) hx)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self p hL hHs
      hH hx hxper hnd hv)
    (tendstoUniformly_comp_endChart_positive hconv)
  refine ⟨κ, hκ, C, hdecay.mono fun R hR t ↦ ?_⟩
  have h := hR (p.endSign * t)
  rwa [comp_apply, ← p.endChart_endSign_mul, endSign_mul_endSign_mul] at h

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {T₀ : ℝ} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {K : Set V} {W : Set (ℝ × V)}
  {J₀ : ℝ → V → AlmostComplexStructure V}

/-! ### Exponential decay of derivatives and `C¹` convergence on cylindrical ends -/

/-- **Exponential `C¹` convergence of `d(u ∘ φ_p)` along a cylindrical end of a PSS plane.** Let `𝔎`
be the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H` whose suspended
Hamiltonian vector field is globally Lipschitz, and let `u` be `C³` on `{‖w‖ > r}`, with image in a
compact set `K`, solving `(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that for `s ≥ T₀`
the almost complex structure is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a
`1`-periodic family `J₀` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, and
that the end loops `t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a nondegenerate
`1`-periodic orbit `x` of `H`. Then the full derivative of `u ∘ φ_p` converges exponentially to the
derivative `(σ, τ) ↦ τ X_{H_t}(x(t))` of the stationary cylinder: for some `κ > 0` and `C`,
eventually `‖d(u ∘ φ_p)(ε R, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C exp (-κ R)` for every `t`. -/
theorem exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
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
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * R)) := by
  set a := max (max T₀ 2) (Real.log r / (2 * π))
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have ha₂ : 2 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have hmem (z : ℝ × ℝ) (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  set g : ℝ × V → ℝ × V := fun q ↦ (p.endSign * q.1, q.2)
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le (by norm_num)
  obtain ⟨κ, hκ, C, hdecay⟩ := exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp
    (a := a) (J := fun t y ↦ J₀ (p.endSign * t) y) (W := g ⁻¹' W)
    (p.contDiff_uncurry_positiveEndHamiltonian hHs) (p.periodic_positiveEndHamiltonian hH)
    (hW.preimage hg.continuous) (hJ₀.comp hg.contDiffOn (mapsTo_preimage g W))
    (p.periodic_comp_endSign_mul hJ₀per) hK (fun q hq ↦ hKW ⟨mem_univ _, hq.2⟩)
    (fun t y hy ↦ hJ₀t _ y hy)
    (hu.comp (positive.contDiff_endChart (n := 3)).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, endChart_add_one])
    (fun s hs t ↦ huK _ (hmem (s, t) hs))
    (fun z hz ↦ by
      have hJeq := hJ z.1 (p.endSign * z.2) (haT.trans hz.1.le)
      rw [endChart_endSign_mul, endSign_mul_endSign_mul, Prod.mk.eta] at hJeq
      rw [comp_apply, ← hJeq]
      exact ω.isComplexLinearMap_perturbedFDeriv_comp_endChart_positive p hH hHs1
        (ha₂.trans hz.1.le)
        ((hu.differentiableOn (by norm_num)).differentiableAt
          ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (hmem z hz.1)))
        (hfloer _ (hmem z hz.1)))
    (ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top p hH hHs1 ha₂
      (le_max_right _ _) (hu.differentiableOn (by norm_num)) hE)
    (p.periodic_comp_endSign_mul hxper)
    (hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian (p := p) hx)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_pssPlane_positiveEndHamiltonian_apply_eq_self p hL
      (hHs.of_le (by norm_num)) hH hx hxper hnd hv)
    (tendstoUniformly_comp_endChart_positive hconv)
  refine ⟨κ, hκ, C, (hdecay.and (eventually_gt_atTop a)).mono fun R ⟨hR, hRa⟩ t ↦ ?_⟩
  have hsmul : p.endSign • (p.endSign * R, t) = (R, p.endSign * t) := by
    simp [Prod.smul_mk, smul_eq_mul]
  have hmem' :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart (p.endSign • (p.endSign * R, t)))‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) (by rw [hsmul]; exact hRa)
  have hd : DifferentiableAt ℝ (u ∘ positive.endChart) (p.endSign • (p.endSign * R, t)) :=
    ((hu.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hmem')).comp _
      ((positive.contDiff_endChart (n := 1)).differentiable one_ne_zero _)
  have hsub : fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t)) =
      p.endSign • (fderiv ℝ (u ∘ positive.endChart) (R, p.endSign * t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorField (p.positiveEndHamiltonian H (p.endSign * t))
            (x (p.endSign * (p.endSign * t))))) := by
    rw [p.fderiv_comp_endChart hd, hsmul]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_snd', endSign_mul_endSign_mul,
      hamiltonianVectorField_pssPlane_positiveEndHamiltonian_endSign_mul, Pi.smul_apply, smul_sub,
      smul_smul]
    congr 2
    calc v.2 = p.endSign * p.endSign * v.2 := by rw [endSign_mul_endSign, one_mul]
      _ = p.endSign * (v.2 * p.endSign) := by ring
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_endSign, one_mul]
  exact hR (p.endSign * t)

/-- **Exponential decay of `∂_s(u ∘ φ_p)` along a cylindrical end of a PSS plane.** Under the
hypotheses of `exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp`, `∂_s(u ∘ φ_p)`
decays exponentially: for some `κ > 0` and `C`, eventually
`‖d(u ∘ φ_p)(ε R, t)(1, 0)‖ ≤ C exp (-κ R)` for every `t`. -/
theorem exists_pos_eventually_norm_fderiv_comp_endChart_apply_one_zero_le_exp
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
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
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hconv : TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) (1, 0)‖ ≤ C * Real.exp (-(κ * R)) := by
  obtain ⟨κ, hκ, C, h⟩ := exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp
    p hH hHs hu hK huK hfloer hE hW hJ₀ hJ₀per hKW hJ₀t hJ hL hxper hx hnd hconv
  refine ⟨κ, hκ, C, h.mono fun R hR t ↦ ?_⟩
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hle := (fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))).le_opNorm
    (1, 0)
  rw [sub_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', zero_smul,
    sub_zero, h10, mul_one] at hle
  exact hle.trans (hR t)

/-- **Unconditional `C¹` exponential convergence on a cylindrical end of a PSS plane.** Let `𝔎` be
the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H` whose suspended
Hamiltonian vector field is globally Lipschitz, and let `u` be `C³` on `{‖w‖ > r}`, with image in a
compact set `K` in which every `1`-periodic orbit of `H` is nondegenerate, solving
`(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that for `s ≥ T₀` the almost complex
structure is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀`
which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then there exist a
`1`-periodic orbit `x` of `H`, a rate `κ > 0`, and a constant `C` such that eventually as `R → ∞`,
for every `t`, `u ∘ φ_p` is differentiable at `(ε R, t)` and both `‖(u ∘ φ_p)(ε R, t) - x(t)‖` and
`‖d(u ∘ φ_p)(ε R, t) - dt ⊗ X_{H_t}(x(t))‖` are at most `C exp (-κ R)`. -/
theorem exists_pos_eventually_norm_sub_and_fderiv_comp_endChart_le_exp
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
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
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ R in atTop, ∀ t,
        DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign * R, t) ∧
        ‖(u ∘ p.endChart) (p.endSign * R, t) - x t‖ ≤ C * Real.exp (-(κ * R)) ∧
        ‖fderiv ℝ (u ∘ p.endChart) (p.endSign * R, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (-(κ * R)) := by
  obtain ⟨b, B, c, hc, M, hB, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_endChart_positive_le_and_tame p hH hHs hu hK huK hfloer hE hW
      hJ₀ hJ₀per hKW hJ₀t hJ
  obtain ⟨x, hxper, hx, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation_of_cylindrical p hH hHs
      hu hK huK hfloer hE hW hJ₀ hJ₀per hKW hJ₀t hJ hL hnd
  have hxK (t : ℝ) : x t ∈ K := by
    refine hK.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop (Real.log r / (2 * π))).mono fun R hR ↦ huK _ ?_)
    rw [endChart_endSign_mul]
    exact lt_norm_symm_endChart_positive le_rfl hR
  have hnd₀ := hnd x hxper hx hxK
  obtain ⟨κ₁, hκ₁, C₁, h₁⟩ := exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation p hH
    (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hfloer hE hL hxper hx hnd₀ hconv
    (fun z hz ↦ ((fderiv ℝ (u ∘ positive.endChart) z).le_opNorm _).trans (by simpa using hB z hz))
    hc hJc hJM
  obtain ⟨κ₂, hκ₂, C₂, h₂⟩ := exists_pos_eventually_norm_fderiv_comp_endChart_sub_smulRight_le_exp
    p hH hHs hu hK huK hfloer hE hW hJ₀ hJ₀per hKW hJ₀t hJ hL hxper hx hnd₀ hconv
  set κ := min κ₁ κ₂
  set C := max (max C₁ C₂) 0
  refine ⟨x, hxper, hx, κ, lt_min hκ₁ hκ₂, C, ?_⟩
  filter_upwards [h₁, h₂, eventually_gt_atTop (max 0 (Real.log r / (2 * π)))] with R hR₁ hR₂ hR t
  have hR₀ : 0 ≤ R := ((le_max_left _ _).trans_lt hR).le
  have hRr : Real.log r / (2 * π) < R := (le_max_right _ _).trans_lt hR
  have hsmul : p.endSign • (p.endSign * R, t) = (R, p.endSign * t) := by
    simp [Prod.smul_mk, smul_eq_mul]
  have hmem :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart (p.endSign • (p.endSign * R, t)))‖ :=
    lt_norm_symm_endChart_positive le_rfl (by simpa [hsmul] using hRr)
  have hd : DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign * R, t) :=
    p.differentiableAt_comp_endChart
      (((hu.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hmem)).comp _
        ((positive.contDiff_endChart (n := 1)).differentiable one_ne_zero _))
  refine ⟨hd, (hR₁ t).trans ?_, (hR₂ t).trans ?_⟩
  · exact mul_le_mul ((le_max_left _ _).trans (le_max_left _ _))
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hR₀)))
      (Real.exp_pos _).le (le_max_right _ _)
  · exact mul_le_mul ((le_max_right _ _).trans (le_max_left _ _))
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hR₀)))
      (Real.exp_pos _).le (le_max_right _ _)

/-- **Unconditional `C¹` exponential convergence as `s → -∞` on the negative PSS plane.** Under the
hypotheses of `exists_pos_eventually_norm_sub_and_fderiv_comp_endChart_le_exp` for
`PSSPlane.negative`, there exist a `1`-periodic orbit `x` of `H`, a rate `κ > 0`, and a constant `C`
such that eventually as `s → -∞` (`atBot`), for every `t`, `u ∘ negative.endChart` is differentiable
at `(s, t)` and both `‖(u ∘ negative.endChart)(s, t) - x(t)‖` and
`‖d(u ∘ negative.endChart)(s, t) - dt ⊗ X_{H_t}(x(t))‖` are at most `C exp (κ s)`. -/
theorem exists_pos_eventually_atBot_norm_sub_and_fderiv_comp_endChart_negative_le_exp
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ negative.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negative.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ negative.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negative.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (negative.endChart (negative.endSign * s, t)) =
        J₀ t (u (negative.endChart (negative.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atBot, ∀ t,
        DifferentiableAt ℝ (u ∘ negative.endChart) (s, t) ∧
        ‖(u ∘ negative.endChart) (s, t) - x t‖ ≤ C * Real.exp (κ * s) ∧
        ‖fderiv ℝ (u ∘ negative.endChart) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (κ * s) := by
  obtain ⟨x, hxper, hx, κ, hκ, C, h⟩ :=
    exists_pos_eventually_norm_sub_and_fderiv_comp_endChart_le_exp negative
      hH hHs hu hK huK hfloer hE hW hJ₀ hJ₀per hKW hJ₀t hJ hL hnd
  refine ⟨x, hxper, hx, κ, hκ, C, ?_⟩
  filter_upwards [tendsto_neg_atBot_atTop.eventually h] with s hs t
  simpa only [endSign_negative, neg_one_mul, mul_neg, neg_neg] using hs t

end InnerProductSpace

end TauCeti.SymplecticForm
