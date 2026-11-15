/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
import TauCeti.Algebra.Ring.Periodic
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# The asymptotic orbit at the end of a finite-energy PSS plane

Let `p` be a PSS plane, let `ε = ±1` be the sign of its end at `∞`, and let `H` be a period-one
`C¹` Hamiltonian on a symplectic vector space `(V, ω)`. Let `𝔎` be a perturbation that is
`H(t) dt` in end coordinates on the part `ε s ≥ T₀` of the end, as the perturbation
`TauCeti.Floer.PSSPlane.perturbation` given by `H` is for `T₀ = 2`. Let `u` be a solution of the
Floer equation `(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end, for uniformly tame almost
complex structures `J(z)`, with image in a compact set and with finite energy there.
For `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift. This file shows that `u` breaks
off a one-periodic orbit at its end:

* if `u` is `C²`, there are a one-periodic orbit `x` of the Hamiltonian vector field,
  `x' = X_{H_t}(x)`, and radii `R_n → ∞` such that the loops `ℓ_{R_n}` converge uniformly to `x`,
  and the actions `A_H(ℓ_R)` tend to `A_H(x)` as `R → ∞`
  (`exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer` in
  `TauCeti.SymplecticForm`, and
  `SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation` for
  the perturbation of a PSS plane);
* for the perturbation of a PSS plane, the uniform convergence along some `R_n → ∞` already holds
  if `u` is `C¹`
  (`SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`);
* hence, for a `C²` solution on the whole plane with finite energy, the energy is
  `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`
  (`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SymplecticForm`).

So `x` is the generator at which a PSS plane meets the Floer complex: an input for the positive
plane, an output for the negative plane. The energy identity of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action` assumed convergence of the end actions; here it
follows from finite energy and compactness.

**The end as a Floer half-cylinder.** In the real coordinates `ℝ × ℝ ≃ ℂ` the end lift is the map
`ψ = TauCeti.Complex.realChart p.cylindricalEndLift`, which sends `(s, t)` to `φ(s + i t)`. It is
holomorphic, preserves orientation, is `1`-periodic in `t` and is injective on every band of
angular width one. On `ε s ≥ T₀` the perturbation `𝔎` pulls back along `ψ` to `H(t) dt`
(`TauCeti.Floer.PSSPlane.perturbationPullback_realChart_cylindricalEndLift_of_le`), so `u ∘ ψ`
solves the Floer equation `∂_s v + J (∂_t v - X_{H_t}(v)) = 0` of a cylinder
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift`),
and its energy over a part of `{ε s ≥ T₀}` within a band of angular width one is the energy of `u`
over the image
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_eq`).
Hence its energy over a band `P × [0, 1]` with `ε s ≥ T₀` on `P` is at most the energy of `u`
over any set containing the image
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le`).
The end is the positive half-cylinder `s > a` on the positive plane and the negative half-cylinder
`s < -a` on the negative plane, for `a ≥ T₀` large, and the results of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` apply to either.

The `C¹` statement uses the half-cylinder theorem on the positive end only. The negative plane is
the positive plane for the reversed Hamiltonian `-H(-t)`
(`TauCeti.Floer.PSSPlane.perturbation_negative`), and its loops are the loops of the positive plane
traversed backwards (`TauCeti.Floer.PSSPlane.cylindricalEndLift_negative_endSign_mul`). Reversing
time turns an orbit `y` of `-H(-t)` into the orbit `t ↦ y(-t)` of `H`, since both the time and the
derivative change sign
(`TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart realChart_mk contDiff_realChart)
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {K : Set V} {p : PSSPlane} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}

/-! ### The end in real coordinates -/

/-- The end lift in real coordinates sends `(s, t)` to a point of norm `exp (2π ε s)`. -/
private theorem norm_symm_realChart_cylindricalEndLift (p : PSSPlane) (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ =
      Real.exp (2 * π * (p.endSign * z.1)) := by
  rw [TauCeti.Complex.equivRealProdCLM_symm_realChart, norm_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- The half-cylinder `ε s > a` lies in the part `‖w‖ > exp (2πa)` of the plane. -/
private theorem exp_lt_norm_realChart_cylindricalEndLift {a : ℝ} {z : ℝ × ℝ}
    (hz : a < p.endSign * z.1) :
    Real.exp (2 * π * a) <
      ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ := by
  rw [norm_symm_realChart_cylindricalEndLift, Real.exp_lt_exp]
  nlinarith [Real.pi_pos]

/-- Every part `‖w‖ > r` of the plane contains a part `‖w‖ > exp (2πa)` with `a ≥ T₀`. -/
private theorem exists_le_exp_lt_norm_subset (T₀ r : ℝ) :
    ∃ a : ℝ, T₀ ≤ a ∧ {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := by
  refine ⟨max T₀ (max 0 r), le_max_left _ _, fun z (hz : Real.exp _ < _) ↦ lt_of_le_of_lt ?_ hz⟩
  have h₀ : 0 ≤ max T₀ (max 0 r) := (le_max_left 0 r).trans (le_max_right _ _)
  have hr : r ≤ max T₀ (max 0 r) := (le_max_right 0 r).trans (le_max_right _ _)
  have h₁ := Real.add_one_le_exp (2 * π * max T₀ (max 0 r))
  have h₂ : 0 ≤ (2 * π - 1) * max T₀ (max 0 r) :=
    mul_nonneg (by linarith [Real.two_le_pi]) h₀
  linarith

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The loops of `u` along the end, read in real coordinates. -/
private theorem comp_cylindricalEndLift_endSign_mul (p : PSSPlane) (u : ℝ × ℝ → V) (R t : ℝ) :
    u (Complex.equivRealProdCLM (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))) =
      (u ∘ realChart p.cylindricalEndLift) (p.endSign * R, t) := by
  rw [comp_apply, realChart_mk]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The loops of `u ∘ ψ` are periodic. -/
private theorem periodic_comp_realChart_cylindricalEndLift (p : PSSPlane) (u : ℝ × ℝ → V)
    (s : ℝ) : Periodic (fun t ↦ (u ∘ realChart p.cylindricalEndLift) (s, t)) 1 := fun t ↦ by
  simp only [comp_apply, realChart_cylindricalEndLift_add_one]

/-! ### The Floer equation and the energy on the end -/

omit [FiniteDimensional ℝ V] in
/-- On the part `ε s ≥ T₀` of the end, where `𝔎` is `H(t) dt`, the perturbation is
differentiable in the target point. -/
private theorem differentiableAt_perturbation_realChart
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hHd : ∀ t, Differentiable ℝ (H t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ p.endSign * ζ.1) (v : ℂ)
    (y : V) :
    DifferentiableAt ℝ
      (fun x ↦ 𝔎 (Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)) x v) y := by
  have hre : T₀ ≤ p.endSign *
      (p.endCoord (Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ))).re := by
    rw [TauCeti.Complex.equivRealProdCLM_symm_realChart, re_endCoord_cylindricalEndLift]
    simpa using hζ
  simp_rw [hKH _ _ hre, smul_apply, smul_eq_mul]
  exact ((hHd _) y).mul_const _

/-- On the part `ε s ≥ T₀` of the end, the perturbed derivative of a map `v` for the cylindrical
datum `H(t) dt` is its perturbed derivative for the pullback of `𝔎` along the end lift. -/
private theorem perturbedFDeriv_comp_realChart_eq
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (v : ℝ × ℝ → V) {ζ : ℝ × ℝ} (hζ : T₀ ≤ p.endSign * ζ.1) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v ζ =
      ω.perturbedFDeriv
        (perturbationPullback (realChart p.cylindricalEndLift)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (realChart p.cylindricalEndLift)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) v ζ :=
  ω.perturbedFDeriv_congr _
    (funext fun x ↦ by
      rw [perturbationPullback_realChart_cylindricalEndLift_of_le p hKH hH hζ]
      simp [stdComplexLineReal_eq])
    (funext fun x ↦ by
      rw [perturbationPullback_realChart_cylindricalEndLift_of_le p hKH hH hζ]
      simp [stdComplexLineImag_eq])

/-- **The end of a PSS plane solves the Floer equation of a cylinder.** Let `𝔎` be a perturbation
that is `H(t) dt` on the part `ε s ≥ T₀` of the end of a PSS plane, and let `u` solve the Floer
equation `(du - X_𝔎)^{0,1} = 0` for the almost complex structure `J` at the image `ψ(ζ)` of a point
`ζ` with `ε s ≥ T₀` under the end lift `ψ` in real coordinates. Then `u ∘ ψ` solves the Floer
equation `∂_s v + J (∂_t v - X_{H_t}(v)) = 0` of a cylinder at `ζ`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {J : AlmostComplexStructure V}
    {ζ : ℝ × ℝ} (hζ : T₀ ≤ p.endSign * ζ.1)
    (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ζ :
        ℝ × ℝ →ₗ[ℝ] V) := by
  rw [perturbedFDeriv_comp_realChart_eq hKH hH _ hζ]
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    (Ks := fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I)
    ((contDiff_realChart (p.contDiff_cylindricalEndLift (n := 1))).differentiable one_ne_zero ζ)
    hu (differentiableAt_perturbation_realChart hKH hHd hζ 1 _)
    (differentiableAt_perturbation_realChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)) hfloer

/-- **The energy of a part of the end of a PSS plane.** Let `𝔎` be a perturbation that is
`H(t) dt` on the part `ε s ≥ T₀` of the end of a PSS plane, and let `s` be a measurable set of
points with `ε s ≥ T₀` and angular coordinate in `[t₀, t₀ + 1)`. If `u` is differentiable on the
image of `s` under the end lift `ψ` in real coordinates, then the energy of `u ∘ ψ` for the
cylindrical datum `H(t) dt` over `s` is the energy of `u` over `ψ(s)`. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_eq
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsT : ∀ ζ ∈ s, T₀ ≤ p.endSign * ζ.1) {t₀ : ℝ}
    (hst : ∀ ζ ∈ s, ζ.2 ∈ Ico t₀ (t₀ + 1))
    (hu : ∀ ζ ∈ s, DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ)) :
    ∫⁻ z in s, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart p.cylindricalEndLift) z) =
      ∫⁻ z in realChart p.cylindricalEndLift '' s, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have hψ : Differentiable ℝ (realChart p.cylindricalEndLift) :=
    (contDiff_realChart (p.contDiff_cylindricalEndLift (n := 1))).differentiable one_ne_zero
  have hinj : InjOn (realChart p.cylindricalEndLift) s :=
    TauCeti.Complex.injOn_realChart <| (p.injOn_cylindricalEndLift t₀).mono <| by
      rintro _ ⟨ζ, hζ, rfl⟩
      simpa using hst ζ hζ
  -- On `s` the energy density is the Jacobian times the energy density of `u`.
  have hdens : ∀ ζ ∈ s, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (u ∘ realChart p.cylindricalEndLift) ζ =
        |(fderiv ℝ (realChart p.cylindricalEndLift) ζ).det| *
          ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u
            (realChart p.cylindricalEndLift ζ) := by
    intro ζ hζ
    rw [floerEnergyDensity_def, perturbedFDeriv_comp_realChart_eq hKH hH _ (hsT ζ hζ),
      ← floerEnergyDensity_def, abs_of_pos (p.det_fderiv_realChart_cylindricalEndLift_pos ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I)
      (hψ ζ) (hu ζ hζ) (differentiableAt_perturbation_realChart hKH hHd (hsT ζ hζ) 1 _)
      (differentiableAt_perturbation_realChart hKH hHd (hsT ζ hζ) Complex.I _)
  exact (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs hinj
    (fun ζ _ ↦ hψ ζ) hdens).symm

/-- **The energy of the end of a PSS plane.** Let `𝔎` be a perturbation that is `H(t) dt` on the
part `ε s ≥ T₀` of the end of a PSS plane, and let `P` be a measurable set of longitudinal
coordinates with `ε s ≥ T₀` on `P`. If `u` is differentiable on the image of the band
`P × [0, 1]` under the end lift `ψ` in real coordinates, and `U` contains that image, then the
energy of `u ∘ ψ` for the cylindrical datum `H(t) dt` over `P × [0, 1]` is at most the energy of
`u` over `U`. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {P : Set ℝ}
    (hP : MeasurableSet P) (hPT : ∀ s ∈ P, T₀ ≤ p.endSign * s) {U : Set (ℝ × ℝ)}
    (hU : ∀ ζ ∈ P ×ˢ Icc 0 1, realChart p.cylindricalEndLift ζ ∈ U)
    (hu : ∀ ζ ∈ P ×ˢ Icc 0 1, DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ)) :
    ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart p.cylindricalEndLift) z) ≤
      ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  -- The closed band differs from the half-open one by a null set.
  have hae : (P ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] P ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  rw [setLIntegral_congr hae, setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_eq
    hKH hH hHd (hP.prod measurableSet_Ico) (fun ζ hζ ↦ hPT ζ.1 hζ.1) (t₀ := 0)
    (fun ζ hζ ↦ by simpa using hζ.2) fun ζ hζ ↦ hu ζ ⟨hζ.1, Ico_subset_Icc_self hζ.2⟩]
  refine lintegral_mono_set ?_
  rintro _ ⟨ζ, hζ, rfl⟩
  exact hU ζ ⟨hζ.1, Ico_subset_Icc_self hζ.2⟩

/-- **The half-cylinder at the end of a PSS plane.** Let `𝔎` be a perturbation that is `H(t) dt`
on the part `ε s ≥ T₀` of the end. If `u` is `Cⁿ`, `n ≠ 0`, on a part `‖w‖ > r` of the plane,
with image in `K`, solving the Floer equation for `𝔎` there for structures `J(z)` bounded by `c`
and `M`, and with finite energy there, then on some half-cylinder `ε s > a` the map `u ∘ ψ` and the
structures `J ∘ ψ` satisfy the hypotheses of the finite-energy half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` for the cylindrical datum `H(t) dt`. -/
private theorem exists_halfCylinder_comp_realChart_cylindricalEndLift
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r : ℝ} (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ a : ℝ, ContDiffOn ℝ n (u ∘ realChart p.cylindricalEndLift) {z | a < p.endSign * z.1} ∧
      (∀ z, a < p.endSign * z.1 → (u ∘ realChart p.cylindricalEndLift) z ∈ K) ∧
      (∀ z, a < p.endSign * z.1 → ∀ v,
        c * ‖v‖ ^ 2 ≤ ω v ((J ∘ realChart p.cylindricalEndLift) z v)) ∧
      (∀ z, a < p.endSign * z.1 → ∀ v,
        ‖(J ∘ realChart p.cylindricalEndLift) z v‖ ≤ M * ‖v‖) ∧
      (∀ z, a < p.endSign * z.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((J ∘ realChart p.cylindricalEndLift) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart p.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∀ P : Set ℝ, MeasurableSet P → (∀ s ∈ P, a < p.endSign * s) →
        ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) z) ≠ ⊤ := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ T₀`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_le_exp_lt_norm_subset T₀ r
  have hmem {z : ℝ × ℝ} (hz : a < p.endSign * z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ :=
    hsub (exp_lt_norm_realChart_cylindricalEndLift hz)
  have hud := (hu.mono hsub).differentiableOn hn
  have hdiff {z : ℝ × ℝ} (hz : a < p.endSign * z.1) :
      DifferentiableAt ℝ u (realChart p.cylindricalEndLift z) :=
    hud.differentiableAt <| (isOpen_lt continuous_const (by fun_prop)).mem_nhds
      (exp_lt_norm_realChart_cylindricalEndLift hz)
  refine ⟨a, (hu.mono hsub).comp (contDiff_realChart p.contDiff_cylindricalEndLift).contDiffOn
      fun z hz ↦ exp_lt_norm_realChart_cylindricalEndLift hz,
    fun z hz ↦ huK _ (hmem hz), fun z hz ↦ hJc _ (hmem hz), fun z hz ↦ hJM _ (hmem hz),
    fun z hz ↦ isComplexLinearMap_perturbedFDeriv_comp_realChart_cylindricalEndLift hKH hH hHd
      (ha.trans hz.le) (hdiff hz) (hfloer _ (hmem hz)),
    fun P hP hPa ↦ ?_⟩
  exact ((setLIntegral_floerEnergyDensity_comp_realChart_cylindricalEndLift_le hKH hH hHd hP
    (fun s hs ↦ ha.trans (hPa s hs).le)
    (U := {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖})
    (fun ζ hζ ↦ exp_lt_norm_realChart_cylindricalEndLift (hPa _ hζ.1))
    fun ζ hζ ↦ hdiff (hPa _ hζ.1)).trans_lt ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne

/-! ### The orbit at the end -/

/-- **The asymptotic action at the end of a finite-energy PSS plane.** Let `𝔎` be a perturbation
of a PSS plane that is `H(t) dt` on the part `ε s ≥ T₀` of the end, for a period-one `C¹`
Hamiltonian `H`. Let `u` be `C²` on a part `‖w‖ > r` of the end, with image in a compact set `K`,
solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there for almost complex structures `J(z)` with
`c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`, and with finite energy there. Then there
is a one-periodic orbit `x` of the Hamiltonian vector field such that the loops
`ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`,
converge uniformly to `x` along some `R_n → ∞`, and their actions `A_H(ℓ_R)` tend to the action
`A_H(x)` as `R → ∞`. The positive plane's end is the half-cylinder `s > a` and the negative plane's
end is `s < -a`, so no time reversal of the Hamiltonian is needed. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer
    (hKH : ∀ w x, T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  obtain ⟨a, hv, hvK, hJc', hJM', hfloer', hE'⟩ :=
    exists_halfCylinder_comp_realChart_cylindricalEndLift hKH hH hHd two_ne_zero hu huK hJc hJM
      hfloer hE
  simp_rw [comp_cylindricalEndLift_endSign_mul p u]
  cases p with
  | positive =>
    -- On the positive plane the end is the positive half-cylinder `s > a`.
    have hpos (s : ℝ) (hs : a < s) : a < positive.endSign * s := by rwa [endSign_positive, one_mul]
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer hHs hH
        (hv.mono fun z hz ↦ hpos _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hpos s hs)) hc (fun z hz ↦ hJc' z (hpos _ hz.1))
        (fun z hz ↦ hJM' z (hpos _ hz.1)) (fun z hz ↦ hfloer' z (hpos _ hz.1))
        (hE' _ measurableSet_Ioi hpos)
    refine ⟨x, hxper, hx, ⟨φ, hφ, by simpa only [endSign_positive, one_mul] using hux⟩, ?_⟩
    simpa only [endSign_positive, one_mul] using hA
  | negative =>
    -- On the negative plane the end is the negative half-cylinder `s < -a`.
    have hneg (s : ℝ) (hs : s < -a) : a < negative.endSign * s := by
      rw [endSign_negative]
      linarith
    obtain ⟨x, hxper, hx, ⟨φ, -, hφ, hux⟩, hA⟩ :=
      exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer hHs hH
        (hv.mono fun z hz ↦ hneg _ hz.1)
        (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
        (fun s hs t ↦ hvK (s, t) (hneg s hs)) hc (fun z hz ↦ hJc' z (hneg _ hz.1))
        (fun z hz ↦ hJM' z (hneg _ hz.1)) (fun z hz ↦ hfloer' z (hneg _ hz.1))
        (hE' _ measurableSet_Iio hneg)
    refine ⟨x, hxper, hx, ⟨fun n ↦ -φ n, tendsto_neg_atBot_atTop.comp hφ, ?_⟩, ?_⟩
    · simpa only [endSign_negative, neg_mul, one_mul, neg_neg] using hux
    · refine (hA.comp tendsto_neg_atTop_atBot).congr fun R ↦ ?_
      simp only [comp_apply, endSign_negative, neg_mul, one_mul]

/-- **The asymptotic orbit at the end of the positive plane.** This is the case `p = positive` of
`exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation`, for an arbitrary Hamiltonian;
the negative plane is reduced to it. -/
private theorem exists_periodic_hasDerivAt_tendstoUniformly_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  have hHd : ∀ t, Differentiable ℝ (H t) := fun t ↦
    (hHs.differentiable one_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  obtain ⟨a, hv, hvK, hJc', hJM', hfloer', hE'⟩ :=
    exists_halfCylinder_comp_realChart_cylindricalEndLift
      (fun _ x hw ↦ perturbation_eq_smul_endAngularForm hw x) hH hHd one_ne_zero hu huK hJc hJM
      hfloer hE
  have hpos (s : ℝ) (hs : a < s) : a < positive.endSign * s := by rwa [endSign_positive, one_mul]
  obtain ⟨x, hxper, hx, φ, -, hφ, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_of_floer
    hHs hH (hv.mono fun z hz ↦ hpos _ hz.1)
    (fun s _ ↦ periodic_comp_realChart_cylindricalEndLift _ u s) hK
    (fun s hs t ↦ hvK (s, t) (hpos s hs)) hc (fun z hz ↦ hJc' z (hpos _ hz.1))
    (fun z hz ↦ hJM' z (hpos _ hz.1)) (fun z hz ↦ hfloer' z (hpos _ hz.1))
    (hE' _ measurableSet_Ioi hpos)
  simp_rw [comp_cylindricalEndLift_endSign_mul positive u]
  exact ⟨x, hxper, hx, φ, hφ, by simpa only [endSign_positive, one_mul] using hux⟩

omit [FiniteDimensional ℝ V] in
/-- The negative plane given by `H` is the positive plane given by the reversed Hamiltonian
`-H(-t)` (`TauCeti.Floer.PSSPlane.perturbation_negative`), which is again period-one and `C¹`. -/
private theorem periodic_contDiff_reverse (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) :
    Periodic (fun t y ↦ -H (-t) y) 1 ∧ ContDiff ℝ 1 (uncurry fun t y ↦ -H (-t) y) :=
  ⟨hH.comp_neg.comp Neg.neg, (hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg⟩

/-- **The orbit at the end of the negative plane.** Reversing time turns a one-periodic orbit `y` of
the reversed Hamiltonian `-H(-t)` into the one-periodic orbit `t ↦ y(-t)` of `H`; if the loops of
`u` along the end of the positive plane converge uniformly to `y` along `R_n`, then the loops of `u`
along the end of the negative plane converge uniformly to `t ↦ y(-t)` along `R_n`. -/
private theorem periodic_hasDerivAt_tendstoUniformly_negative (ω : SymplecticForm V)
    {y : ℝ → V} (hyper : Periodic y 1)
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (fun x ↦ -H (-t) x) (y t)) t)
    {R : ℕ → ℝ} (huy : TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
      (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) y atTop) :
    Periodic (fun t ↦ y (-t)) 1 ∧
      (∀ t, HasDerivAt (fun t ↦ y (-t)) (ω.hamiltonianVectorField (H t) (y (-t))) t) ∧
      TendstoUniformly (fun n (t : ℝ) ↦ u (Complex.equivRealProdCLM
        (negative.cylindricalEndLift (↑(negative.endSign * R n) + ↑t * Complex.I))))
        (fun t ↦ y (-t)) atTop := by
  refine ⟨hyper.comp_neg, fun t ↦ ?_, ?_⟩
  · exact ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg
      (by simpa only [neg_neg, Pi.neg_def] using hy (-t))
  simp only [cylindricalEndLift_negative_endSign_mul]
  exact huy.comp fun t ↦ -t

/-- **The asymptotic orbit at the end of a finite-energy PSS plane.** Let `𝔎` be the perturbation of
a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`. Let `u` be `C¹` on a part `‖w‖ > r` of
the end, with image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there
for almost complex structures `J(z)` with `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖`, `c > 0`,
and with finite energy there. Then there is a one-periodic orbit `x` of the Hamiltonian vector
field such that the loops `ℓ_R(t) = u(φ(ε R + i t))`, where `φ` is the end lift
`p.cylindricalEndLift` and `ε = p.endSign`, converge uniformly to `x` along some `R_n → ∞`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
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
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop := by
  cases p
  · exact exists_periodic_hasDerivAt_tendstoUniformly_positive hH hHs hu hK huK hc hJc hJM hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  obtain ⟨y, hyper, hy, R, hR, huy⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_positive hH' hHs' hu hK huK hc hJc hJM hfloer hE
  obtain ⟨hxper, hx, hux⟩ := ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy
  exact ⟨_, hxper, hx, R, hR, hux⟩

/-- **The asymptotic action at the end of a finite-energy PSS plane.** The case of
`SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer`
for the perturbation `𝔎` of a PSS plane `p` given by a period-one `C¹` Hamiltonian `H`, which is
`H(t) dt` on the part `ε s ≥ 2` of the end. -/
theorem exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
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
        u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) :=
  exists_periodic_hasDerivAt_tendsto_hamiltonianAction_cylindricalEndLift_of_floer
    (fun _ x hw ↦ perturbation_eq_smul_endAngularForm hw x) hH hHs hu hK huK hc hJc hJM hfloer hE

/-- **The energy of a finite-energy PSS plane.** Let `𝔎` be the perturbation of a PSS plane `p`
given by a period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on the whole plane, for almost complex structures `J(z)` tamed by `ω`, with
finite energy. Suppose that on a part `‖w‖ > r` of the end the image of `u` lies in a compact set
`K` and `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with `c > 0`. Then there is a one-periodic
orbit `x` of the Hamiltonian vector field, the uniform limit of the loops `ℓ_R(t) = u(φ(ε R + i t))`
along some `R_n → ∞`, where `φ` is the end lift `p.cylindricalEndLift` and `ε = p.endSign`, such
that the actions `A_H(ℓ_R)` tend to `A_H(x)` as `R → ∞` and

`E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
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
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) x atTop) ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, hux, hA⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_pssPlanePerturbation p hH hHs
      hu.contDiffOn hK huK hc hJc hJM (fun z _ ↦ hfloer z)
      ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  exact ⟨x, hxper, hx, hux, hA, lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu hJ
    hfloer hA⟩

end TauCeti.SymplecticForm
