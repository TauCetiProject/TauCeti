/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit

/-!
# Convergence and bounded derivatives at the end of a PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞` and end
chart `φ_p` (`TauCeti.Floer.PSSPlane.endChart`), and let `K : ℂ → V → ℂ →L[ℝ] ℝ` be a Hamiltonian
perturbation on `ℂ` with values in a symplectic vector space `(V, ω)` that equals `H(t) dt` beyond
longitudinal height `T₀` on the end of `p`, for a period-one Hamiltonian `H : ℝ → V → ℝ` (for
instance `K = p.perturbation H` with `T₀ = 2`). Together with
`TauCeti.Geometry.Symplectic.Floer.Plane.Chart` and `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit`,
this file adapts `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart`,
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit`, and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` to the PSS planes, upgrading
subsequential orbit breaking at `∞` to uniform convergence along the entire end and deriving
derivative bounds on cylindrical ends.

**Full-end convergence under orbit isolation.** When `u` is a finite-energy Floer solution on an
exterior `{‖w‖ > r}` with image in a compact set `B` in which the `1`-periodic orbits of `H` are
uniformly isolated, and `u ∘ φ_+` has bounded derivative with uniformly tame almost complex
structures on some half-cylinder `s > b` of `φ_+ = positive.endChart`, the end loops
`t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit `x` of `H`
(`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated`), without any
global Lipschitz hypothesis on `H`. In particular this holds when `H` has globally Lipschitz
suspension and every `1`-periodic orbit in `B` starts at a nondegenerate fixed point of the
time-one map (`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop`). For a whole
PSS plane with `K = p.perturbation H`, combining this with
`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` yields the
whole-plane energy identity `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)` with full-end uniform convergence
(`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated`,
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt`).

**Bounded derivatives on cylindrical ends.** When `H` and `u` are `C³` and the almost complex
structure is cylindrical beyond `T₀` on the end of `p`,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`, `TauCeti.Geometry.Symplectic.Floer.CylindricalEnd`
bounds `d(u ∘ φ_+)` on `s ≥ b` and `d(u ∘ φ_p)` on `ε s ≥ b` whenever `T₀ < b` and `r < exp (2π b)`
(`exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le`,
`exists_forall_norm_fderiv_comp_pssPlane_endChart_le`), discharging both the derivative bound and
uniform tameness hypotheses automatically
(`exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le_and_tame`,
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical_of_isolated`,
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical`,
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated`,
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.3
  and Section 4.6, on mean-value derivative bounds on cylindrical ends.
-/

public section

open Set Real Filter Function MeasureTheory
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {B : Set V}

/-- Nondegeneracy of the time-one map at `x 0` for every `1`-periodic orbit `x` of `H` in `B`
implies uniform isolation of `1`-periodic orbits of `H` in `B`. -/
private theorem isolated_of_isNondegenerateFixedPt {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (x : ℝ → V) (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxB : ∀ t, x t ∈ B) :
    ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
      (∀ t, dist (y t) (x t) < δ) → y = x := by
  obtain ⟨δ, hδ, h⟩ := ω.exists_pos_forall_periodic_eq_signedHamiltonian_of_isNondegenerateFixedPt
    (one_mul (1 : ℝ)) hL (by simpa only [signedHamiltonian_one] using hx) (hnd x hxper hx hxB)
  exact ⟨δ, hδ, fun y hyper hy _ hyx ↦
    h y hyper (by simpa only [signedHamiltonian_one] using hy) (hyx 0)⟩

/-! ### Uniform convergence along the end under orbit isolation -/

/-- **Full-end convergence on a PSS plane under orbit isolation.** Let `K = H(t) dt` beyond `T₀` on
the end of `p` for a `1`-periodic `C¹` Hamiltonian `H`, and let `u` be `C¹` on `{‖w‖ > r}`, with
image in a compact set `B` in which the `1`-periodic orbits of `H` are uniformly isolated, solving
`(du - X_K)^{0,1} = 0` there with finite energy. If on some half-cylinder `s > b` of
`positive.endChart` the derivative of `u ∘ positive.endChart` is bounded and `J` is uniformly tame,
then the end loops `t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit
of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated
    (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
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
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
        (∀ t, dist (y t) (x t) < δ) → y = x)
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r (max T₀ b)
  have haT : T₀ ≤ a := (le_max_left _ _).trans ha
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := ((le_max_right _ _).trans ha).trans_lt hz
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive hKH hH hHd one_ne_zero haT hr hu huB hfloer hE
  have hH' : ContDiff ℝ 1 (uncurry (p.positiveEndHamiltonian H)) :=
    p.contDiff_uncurry_positiveEndHamiltonian hHs
  have hH'per : Periodic (p.positiveEndHamiltonian H) 1 := p.periodic_positiveEndHamiltonian hH
  have hfin := lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc
    (fun z hz v ↦ hJc z (hab hz.1) v) (fun z hz v ↦ hJM z (hab hz.1) v) hfloer' hE'
  obtain ⟨y, hyper, hy, huy⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop hu' hper' hB
    huB' (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH')).continuous
    (fun v t ↦ by simp only [hH'per t]) hfin (fun z hz ↦ hC z (hab hz.1)) fun y hyper hy hyB ↦ by
      rw [p.positiveEndHamiltonian_eq_signedHamiltonian] at hy ⊢
      exact ω.exists_pos_forall_periodic_eq_signedHamiltonian_of_isolated p.endSign_mul_endSign hiso
        hyper hy hyB
  refine ⟨fun t ↦ y (p.endSign * t), p.periodic_comp_endSign_mul hyper,
    hasDerivAt_comp_pssPlane_endSign_mul p hy, ?_⟩
  rw [funext fun R ↦ p.comp_endChart_eq_comp_endChart_positive u R]
  exact huy.comp _

/-- **Full-end convergence on a PSS plane at nondegenerate fixed points.** Specialization of
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated` when the
suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `B` starts at a
nondegenerate fixed point of the time-one map. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop (p : PSSPlane)
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hB : IsCompact B)
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
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated p hKH hH hHs hu
    hB huB hfloer hE (isolated_of_isNondegenerateFixedPt hL hnd) hC hc hJc hJM

/-- **Whole-plane energy of a finite-energy PSS plane with isolated orbits.** Let `𝔎` be the
perturbation of a PSS plane `p` given by a `1`-periodic `C¹` Hamiltonian `H`, and let `u` be a `C²`
solution of `(du - X_𝔎)^{0,1} = 0` on the whole plane for tamed almost complex structures `J(z)`,
with finite energy. Suppose that on `{‖w‖ > r}` the image of `u` lies in a compact set `B` in which
the `1`-periodic orbits of `H` are uniformly isolated, `c ‖v‖² ≤ ω(v, J(z) v)` and
`‖J(z) v‖ ≤ M ‖v‖` with `c > 0`, and `u ∘ positive.endChart` has bounded derivative on some
half-cylinder `s > b`. Then the end loops `ℓ_R(t) = u(φ_p(ε R, t))` converge uniformly as `R → ∞`
to a `1`-periodic orbit `x` of `H`, their actions `A_H(ℓ_R)` converge to `A_H(x)`, and
`E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hB : IsCompact B) {r : ℝ}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
        (∀ t, dist (y t) (x t) < δ) → y = x)
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, ⟨σ, hσ, hσx⟩, hA, hEx⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq p hH hHs hu hB
      huB hc hJc hJM hJ hfloer hE
  obtain ⟨b', hbb', hrb'⟩ := exists_le_and_le_exp r b
  have hmem {z : ℝ × ℝ} (hz : b' < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_equivRealProdCLM_symm_endChart_positive hrb' hz
  obtain ⟨x', -, -, hx'⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated p
      (K := p.perturbation H) (T₀ := 2) (fun _ y _ hw ↦ perturbation_eq_smul_endAngularForm hw y)
      hH hHs (hu.of_le one_le_two).contDiffOn hB huB (fun z _ ↦ hfloer z)
      ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne hiso
      (fun z hz ↦ hC z (hbb'.trans_lt hz)) hc (fun z hz v ↦ hJc _ (hmem hz) v)
      (fun z hz v ↦ hJM _ (hmem hz) v)
  simp_rw [← endChart_mk] at hσx hA
  have hxx' : x = x' := funext fun t ↦
    tendsto_nhds_unique (hσx.tendsto_at t) ((hx'.tendsto_at t).comp hσ)
  exact ⟨x, hxper, hx, hxx' ▸ hx', hA, hEx⟩

/-- **Whole-plane energy of a finite-energy PSS plane with a nondegenerate end.** Specialization of
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated` when the suspension of `H`
is globally Lipschitz and every `1`-periodic orbit in `B` starts at a nondegenerate fixed point of
the time-one map. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hB : IsCompact B) {r : ℝ}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :=
  exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated p hH hHs hu hB huB hc hJc
    hJM hJ hfloer hE (isolated_of_isNondegenerateFixedPt hL hnd) hC

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {W : Set (ℝ × V)}
  {J₀ : ℝ → V → AlmostComplexStructure V}

/-! ### Bounded derivatives and convergence on cylindrical ends -/

/-- **Bounded derivative in `positive.endChart` on a cylindrical end of a PSS plane.** Let
`K = H(t) dt` beyond `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian `H`, and let `u` be
`C³` on `{‖w‖ > r}`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` there with
finite energy. Suppose that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`. Then for every `b > T₀` with `r < exp (2π b)` the
derivative of `u ∘ positive.endChart` is bounded on `s ≥ b`. -/
theorem exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le (p : PSSPlane)
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
    {b : ℝ} (hb : T₀ < b) (hbr : r < Real.exp (2 * π * b)) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C := by
  obtain ⟨a, haT, hr, hab⟩ := exists_le_and_le_exp_and_lt hb hbr
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable (by norm_num)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨hW', hJ₀', hJ₀per', hBW', hJ₀t', hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_pssPlane_endChart_positive_of_cylindrical hKH hH hHd (by norm_num) haT hr hu huB
      hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ
  exact exists_forall_norm_fderiv_le_of_floer (p.contDiff_uncurry_positiveEndHamiltonian hHs)
    (p.periodic_positiveEndHamiltonian hH) hW' hJ₀' hJ₀per' hB hBW' hJ₀t' hu' hper' huB' hfloer'
    hE' hab

/-- **Bounded derivative in `p.endChart` on a cylindrical end of a PSS plane.** Under the
hypotheses of `exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le`, the derivative of
`u ∘ p.endChart` is bounded on the half-cylinder `ε s ≥ b`. -/
theorem exists_forall_norm_fderiv_comp_pssPlane_endChart_le (p : PSSPlane)
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
    {b : ℝ} (hb : T₀ < b) (hbr : r < Real.exp (2 * π * b)) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ p.endSign * z.1 → ‖fderiv ℝ (u ∘ p.endChart) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le p hKH hH hHs hu
    hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ hb hbr
  refine ⟨C, fun z hz ↦ ?_⟩
  rw [p.fderiv_comp_endChart, norm_smul, Real.norm_eq_abs, abs_endSign, one_mul]
  exact hC (p.endSign • z) hz

/-- **Derivative and tameness bounds on a cylindrical end of a PSS plane.** Under the hypotheses
of `exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le`, on some half-cylinder `s > b` of
`positive.endChart` the derivative of `u ∘ positive.endChart` is bounded and the almost complex
structures are uniformly tame. -/
theorem exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le_and_tame (p : PSSPlane)
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
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t)))) :
    ∃ b C c, 0 < c ∧ ∃ M,
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C) ∧
      (∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v)) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖ := by
  obtain ⟨a, haT, hr⟩ := exists_le_and_le_exp r T₀
  set b := a + 1
  have hb : T₀ < b := haT.trans_lt (lt_add_one a)
  have hbr : r < Real.exp (2 * π * b) :=
    hr.trans_lt (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (lt_add_one a) Real.two_pi_pos))
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le p hKH hH hHs hu
    hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ hb hbr
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hB
    (hJ₀.continuousOn.mono hBW) hJ₀per hJ₀t
  have hbT {z : ℝ × ℝ} (hz : b < z.1) : T₀ ≤ z.1 := (hb.trans hz).le
  have huB' {z : ℝ × ℝ} (hz : b < z.1) : (u ∘ positive.endChart) z ∈ B :=
    huB _ (lt_norm_equivRealProdCLM_symm_endChart_positive hr ((lt_add_one a).trans hz))
  refine ⟨b, C, c, hc, M, fun z hz ↦ hC z hz.le, fun z hz v ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [eq_comp_endChart_positive hJ (hbT hz)]
    exact (hcM _ _ (huB' hz) v).1
  · rw [eq_comp_endChart_positive hJ (hbT hz)]
    exact (hcM _ _ (huB' hz) v).2

/-- **Full-end convergence on a cylindrical end of a PSS plane under orbit isolation.** Let
`K = H(t) dt` beyond `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian `H`, and let `u` be
`C³` on `{‖w‖ > r}`, with image in a compact set `B` in which the `1`-periodic orbits of `H` are
uniformly isolated, solving `(du - X_K)^{0,1} = 0` there with finite energy. If for `s ≥ T₀` the
almost complex structure is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a
`1`-periodic family `J₀` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`, then
the end loops `t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit of
`H`. -/
theorem
    exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical_of_isolated
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
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
        (∀ t, dist (y t) (x t) < δ) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop := by
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le_and_tame p hKH hH hHs hu hB huB
      hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ
  exact exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_isolated p hKH hH
    (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hB huB hfloer hE hiso hC hc hJc hJM

/-- **Full-end convergence on a cylindrical end of a PSS plane at nondegenerate fixed points.**
Specialization of
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical_of_isolated`
when the suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `B` starts at a
nondegenerate fixed point of the time-one map. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical
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
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_pssPlane_endChart_atTop_of_cylindrical_of_isolated p
    hKH hH hHs hu hB huB hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJ
    (isolated_of_isNondegenerateFixedPt hL hnd)

/-- **Whole-plane energy of a finite-energy PSS plane with a cylindrical end and isolated orbits.**
Let `𝔎` be the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H`, and let
`u` be a `C³` solution of `(du - X_𝔎)^{0,1} = 0` on the whole plane for tamed almost complex
structures `J(z)`, with finite energy. Suppose that on `{‖w‖ > r}` the image of `u` lies in a
compact set `B` in which the `1`-periodic orbits of `H` are uniformly isolated, and that for
`s ≥ T₀` the almost complex structure is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for
a `1`-periodic family `J₀` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on `ℝ × B`.
Then the end loops `ℓ_R(t) = u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a `1`-periodic orbit
`x` of `H`, their actions `A_H(ℓ_R)` converge to `A_H(x)`, and `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) (hu : ContDiff ℝ 3 u)
    (hB : IsCompact B) {r : ℝ}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJcyl : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
        (∀ t, dist (y t) (x t) < δ) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  have hE' : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ :=
    ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_pssPlane_endChart_positive_le_and_tame p
      (K := p.perturbation H) (T₀ := max T₀ 2)
      (fun _ x _ hw ↦ perturbation_eq_smul_endAngularForm ((le_max_right _ _).trans hw) x)
      hH hHs hu.contDiffOn hB huB (fun z _ ↦ hfloer z) hE' hW hJ₀ hJ₀per hBW hJ₀t
      fun s t hs ↦ hJcyl s t ((le_max_left _ _).trans hs)
  set r' := max r (Real.exp (2 * π * b))
  have hr'r {z : ℝ × ℝ} (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      r < ‖Complex.equivRealProdCLM.symm z‖ :=
    (le_max_left _ _).trans_lt hz
  have hzb {z : ℝ × ℝ} (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      ∃ ζ ∈ Ioi b ×ˢ Ico (0 : ℝ) 1, positive.endChart ζ = z := by
    have hb' : z ∈ {w | Real.exp (2 * π * b) < ‖Complex.equivRealProdCLM.symm w‖} :=
      (le_max_right _ _).trans_lt hz
    rwa [← image_endChart_positive_Ioi_prod_Ico b] at hb'
  exact exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated p hH
    (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hB (r := r')
    (fun z hz ↦ huB z (hr'r hz)) hc
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJc ζ hζ.1 v)
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJM ζ hζ.1 v)
    hJ hfloer hE hiso hC

/-- **Whole-plane energy of a finite-energy PSS plane with a cylindrical end.** Specialization of
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated` when the
suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `B` starts at a
nondegenerate fixed point of the time-one map. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) (hu : ContDiff ℝ 3 u)
    (hB : IsCompact B) {r : ℝ}
    (huB : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ B)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hBW : univ ×ˢ B ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ B, ω.Tames (J₀ t x))
    (hJcyl : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :=
  exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated p hH hHs hu
    hB huB hJ hfloer hE hW hJ₀ hJ₀per hBW hJ₀t hJcyl (isolated_of_isNondegenerateFixedPt hL hnd)

end InnerProductSpace

end TauCeti.SymplecticForm
