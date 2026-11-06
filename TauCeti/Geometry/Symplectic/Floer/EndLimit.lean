/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.Translation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Limits of Floer cylinders along their ends

A Floer solution `u` on a cylindrical end, where the perturbation is `K = H_t dt` and the almost
complex structure `J_t` does not depend on `s`, is studied through its translates
`u_k(s, t) = u(s + s_k, t)` along a sequence `s_k → ±∞`. This file shows that, for a solution with
finite energy on the end, every `C¹` limit of such translates is a stationary cylinder over a
Hamiltonian orbit, and that the actions of the loops `t ↦ u(s_k, t)` converge to the action of that
orbit. So whenever the translates converge along a subsequence, the limit of the end actions, if it
exists, is the action of a Hamiltonian orbit.

The argument is general. The Floer equation `(du - X_K)^{0,1} = 0` at a point is closed under
pointwise convergence of maps and of their derivatives
(`SymplecticForm.isComplexLinearMap_perturbedFDeriv_of_tendsto`), and the Floer energy density
converges with them. By Fatou's lemma, a `C¹` limit of solutions whose energies over an open set
`Ω` tend to zero has zero energy over `Ω`, so its perturbed derivative vanishes on `Ω`
(`SymplecticForm.perturbedFDeriv_eq_zero_of_tendsto_lintegral`). On an end, the energy of the
translates over a fixed window `(a, b) × (0, 1)` is the energy of `u` over the moving window
`(a + s_k, b + s_k) × (0, 1)`. It tends to zero when `u` has finite energy on the end
(`TauCeti.tendsto_setLIntegral_Ioo_add_prod_atTop`,
`TauCeti.tendsto_setLIntegral_Ioo_add_prod_atBot`).
For `K = H_t dt` the vanishing of `du - X_K` says `∂_s v = 0` and `∂_t v = X_{H_t}(v)`, so the
limit is `v(s, t) = x(t)` for a solution `x` of Hamilton's equation
(`SymplecticForm.apply_eq_and_hasDerivAt_of_tendsto_translate`). If the translates and their
derivatives converge locally uniformly, the end actions converge to `A_H(x)`
(`SymplecticForm.tendsto_hamiltonianAction_of_tendstoLocallyUniformly_translate`).

The target is a symplectic vector space and the almost complex structures may depend on the time
and the target point. The convergence of a subsequence of translates is assumed rather than proved:
it follows from uniform derivative bounds along the end, which come from excluding bubbling, by
elliptic regularity and the Arzelà–Ascoli theorem. Exponential convergence to a nondegenerate orbit
is not treated here.

## Main results

* `SymplecticForm.isComplexLinearMap_perturbedFDeriv_of_tendsto`: pointwise `C¹` limits of Floer
  solutions are Floer solutions.
* `SymplecticForm.perturbedFDeriv_eq_zero_of_tendsto_lintegral`: `C¹` limits of Floer solutions
  with energies tending to zero have vanishing perturbed derivative.
* `SymplecticForm.apply_eq_and_hasDerivAt_of_tendsto_translate`: limits of translates of a Floer
  solution along an end with finite energy are stationary cylinders over Hamiltonian orbits.
* `SymplecticForm.tendsto_hamiltonianAction_of_tendstoLocallyUniformly_translate`: the actions of
  the end loops converge to the action of the limit loop.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, and *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120**
  (1989), 575–611, on the convergence of finite-energy solutions to critical points at the ends.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
-/

public section

open Filter Function MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ}

section Limit

variable {ι : Type*} {l : Filter ι} {u : ι → ℝ × ℝ → V} {v : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- The perturbed derivatives at `z` of maps converging at `z` together with their derivatives
converge to the perturbed derivative of the limit, when the Hamiltonian vector fields of the
perturbation at `z` are continuous at the limit point. -/
private theorem tendsto_perturbedFDeriv_apply (ω : SymplecticForm V)
    (hXs : ContinuousAt (ω.hamiltonianVectorField (Ks z)) (v z))
    (hXt : ContinuousAt (ω.hamiltonianVectorField (Kt z)) (v z))
    (hx : Tendsto (fun i ↦ u i z) l (𝓝 (v z)))
    (hdx : Tendsto (fun i ↦ fderiv ℝ (u i) z) l (𝓝 (fderiv ℝ v z))) (w : ℝ × ℝ) :
    Tendsto (fun i ↦ ω.perturbedFDeriv Ks Kt (u i) z w) l
      (𝓝 (ω.perturbedFDeriv Ks Kt v z w)) := by
  simp only [perturbedFDeriv_apply]
  exact ((hdx.eval_const w).sub ((hXs.tendsto.comp hx).const_smul w.1)).sub
    ((hXt.tendsto.comp hx).const_smul w.2)

/-- **Limits of Floer solutions are Floer solutions.** Let `u i` solve the Floer equation
`(du - X_K)^{0,1} = 0` at `z` for the almost complex structures `J(u i z)`, which may depend on the
target point. If the values and the derivatives of the `u i` at `z` converge to those of `v`, and
if `J` and the Hamiltonian vector fields of `K` at `z` are continuous at `v z`, then `v` solves the
Floer equation at `z` for `J(v z)`. -/
theorem isComplexLinearMap_perturbedFDeriv_of_tendsto (ω : SymplecticForm V) [l.NeBot]
    {J : V → AlmostComplexStructure V}
    (hJ : ContinuousAt (fun x ↦ (J x).toLinearMap.toContinuousLinearMap) (v z))
    (hXs : ContinuousAt (ω.hamiltonianVectorField (Ks z)) (v z))
    (hXt : ContinuousAt (ω.hamiltonianVectorField (Kt z)) (v z))
    (hx : Tendsto (fun i ↦ u i z) l (𝓝 (v z)))
    (hdx : Tendsto (fun i ↦ fderiv ℝ (u i) z) l (𝓝 (fderiv ℝ v z)))
    (hsol : ∀ᶠ i in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u i z))
      (ω.perturbedFDeriv Ks Kt (u i) z : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (v z))
      (ω.perturbedFDeriv Ks Kt v z : ℝ × ℝ →ₗ[ℝ] V) := by
  have hP := ω.tendsto_perturbedFDeriv_apply hXs hXt hx hdx
  -- Pass to the limit in `P_i (0, 1) = J(u i z) (P_i (1, 0))`.
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe]
  refine tendsto_nhds_unique (hP stdComplexLineImag) ?_
  have h := (isBoundedBilinearMap_apply.continuous.tendsto _).comp
    ((hJ.tendsto.comp hx).prodMk_nhds (hP stdComplexLineReal))
  simp only [comp_def, LinearMap.coe_toContinuousLinearMap'] at h
  refine h.congr' (hsol.mono fun i hi ↦ ?_)
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe] at hi
  exact hi.symm

/-- The Floer energy densities at `z` of maps converging at `z` together with their derivatives
converge to the energy density of the limit. -/
private theorem tendsto_floerEnergyDensity (ω : SymplecticForm V)
    (hXs : ContinuousAt (ω.hamiltonianVectorField (Ks z)) (v z))
    (hXt : ContinuousAt (ω.hamiltonianVectorField (Kt z)) (v z))
    (hx : Tendsto (fun i ↦ u i z) l (𝓝 (v z)))
    (hdx : Tendsto (fun i ↦ fderiv ℝ (u i) z) l (𝓝 (fderiv ℝ v z))) :
    Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) z) l
      (𝓝 (ω.floerEnergyDensity Ks Kt v z)) := by
  have hP := ω.tendsto_perturbedFDeriv_apply hXs hXt hx hdx
  simp only [floerEnergyDensity_def]
  exact ((ω.continuous_apply_comp continuous_fst continuous_snd).tendsto _).comp
    ((hP stdComplexLineReal).prodMk_nhds (hP stdComplexLineImag))

/-- For a family of Hamiltonians that is jointly `C¹` over `Ω × V` with `Ω` open, the Hamiltonian
vector field at a point of `Ω` is continuous. -/
private theorem continuous_hamiltonianVectorField_of_contDiffOn (ω : SymplecticForm V)
    {K : ℝ × ℝ → V → ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hK : ContDiffOn ℝ 1 (uncurry K) (Ω ×ˢ univ)) (hz : z ∈ Ω) :
    Continuous (ω.hamiltonianVectorField (K z)) :=
  continuous_iff_continuousAt.2 fun x ↦
    ((ω.continuousOn_uncurry_hamiltonianVectorField hΩ hK).continuousAt
      ((hΩ.prod isOpen_univ).mem_nhds ⟨hz, mem_univ x⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt

/-- **Limits of Floer solutions with vanishing energy have vanishing perturbed derivative.** Let
`Ω` be an open set of the domain, `K` a `C¹` perturbation over `Ω` and `J(z, x)` almost complex
structures depending continuously on the target point `x`. Let `u k` eventually be `C¹` solutions
of the Floer equation `(du - X_K)^{0,1} = 0` on `Ω` whose energies over `Ω` tend to zero, and
suppose that the values and the derivatives of the `u k` converge pointwise on `Ω` to those of a
map `v` that is `C¹` on `Ω`. If `J(z, v z)` is tamed by `ω` on `Ω`, then the perturbed derivative
`dv - X_K` of `v` vanishes on `Ω`. -/
theorem perturbedFDeriv_eq_zero_of_tendsto_lintegral (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℕ → ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (Ω ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (Ω ×ˢ univ))
    (hJ : ∀ z ∈ Ω, ContinuousAt (fun x ↦ (J z x).toLinearMap.toContinuousLinearMap) (v z))
    (hJv : ∀ z ∈ Ω, ω.Tames (J z (v z))) (hu : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (u k) Ω)
    (hsol : ∀ᶠ k in atTop, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u k z)) (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hv : ContDiffOn ℝ 1 v Ω) (hx : ∀ z ∈ Ω, Tendsto (fun k ↦ u k z) atTop (𝓝 (v z)))
    (hdx : ∀ z ∈ Ω, Tendsto (fun k ↦ fderiv ℝ (u k) z) atTop (𝓝 (fderiv ℝ v z)))
    (hE : Tendsto (fun k ↦ ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z))
      atTop (𝓝 0)) :
    ∀ z ∈ Ω, ω.perturbedFDeriv Ks Kt v z = 0 := by
  have hXs z (hz : z ∈ Ω) :=
    (ω.continuous_hamiltonianVectorField_of_contDiffOn hΩ hKs hz).continuousAt (x := v z)
  have hXt z (hz : z ∈ Ω) :=
    (ω.continuous_hamiltonianVectorField_of_contDiffOn hΩ hKt hz).continuousAt (x := v z)
  -- The limit solves the Floer equation on `Ω`.
  have hsolv z (hz : z ∈ Ω) := ω.isComplexLinearMap_perturbedFDeriv_of_tendsto (hJ z hz)
    (hXs z hz) (hXt z hz) (hx z hz) (hdx z hz) (hsol.mono fun k hk ↦ hk z hz)
  -- By Fatou's lemma, applied to a tail of the sequence on which every `u k` is `C¹` on `Ω`, the
  -- energy of the limit over `Ω` vanishes.
  obtain ⟨N, hN⟩ := eventually_atTop.1 hu
  have hmeas (k : ℕ) : AEMeasurable
      (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u (k + N)) z)) (volume.restrict Ω) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (ω.continuousOn_floerEnergyDensity hΩ
      (hN _ (Nat.le_add_left N k)) hKs hKt)).aemeasurable hΩ.measurableSet
  have hE0 : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt v z) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt v z)
        = ∫⁻ z in Ω, liminf (fun k ↦ ENNReal.ofReal
            (ω.floerEnergyDensity Ks Kt (u (k + N)) z)) atTop :=
          setLIntegral_congr_fun hΩ.measurableSet fun z hz ↦
            (((ENNReal.continuous_ofReal.tendsto _).comp (ω.tendsto_floerEnergyDensity
              (hXs z hz) (hXt z hz) (hx z hz) (hdx z hz))).comp
                (tendsto_add_atTop_nat N)).liminf_eq.symm
      _ ≤ liminf (fun k ↦ ∫⁻ z in Ω, ENNReal.ofReal
            (ω.floerEnergyDensity Ks Kt (u (k + N)) z)) atTop := lintegral_liminf_le' hmeas
      _ = 0 := (hE.comp (tendsto_add_atTop_nat N)).liminf_eq
  intro z hz
  exact (ω.floerEnergyDensity_eq_zero_iff (hJv z hz) (hsolv z hz)).1
    (ω.floerEnergyDensity_eq_zero_of_setLIntegral_eq_zero hΩ hv hKs hKt hJv hsolv hE0 z hz)

end Limit

section Translate

variable {H : ℝ → V → ℝ} {u v : ℝ × ℝ → V} {s : ℕ → ℝ}

/-- For the cylindrical perturbation `K = H_t dt`, the perturbed derivative of the translate
`(s, t) ↦ u(s + c, t)` at `z` is that of `u` at `z + (c, 0)`. -/
private theorem perturbedFDeriv_cylindrical_comp_add_right (ω : SymplecticForm V) (c : ℝ)
    (z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) z =
      ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u (z + (c, 0)) := by
  simpa using ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u (c, 0) z

/-- **Limits of translates along an end are stationary orbit cylinders.** Let `H` be a `C¹`
time-dependent Hamiltonian and `J_t(x)` almost complex structures tamed by `ω`, continuous in
the target point. Let `u` be `C¹` on a set `W` and solve the Floer equation
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` there. Along a sequence `s_k`, suppose that every window
`(a, b) × (0, 1)` translated by `(s_k, 0)` eventually lies in `W`, and that the energy of `u` over
the translated windows `(a + s_k, b + s_k) × (0, 1)` tends to zero. If the translates
`u(· + (s_k, 0))` and their derivatives converge pointwise to a `C¹` map `v` and its derivative,
then `v` is stationary on the strip `ℝ × [0, 1]`, `v(s, t) = x(t)` with `x(t) = v(0, t)`, and
`x' = X_{H_t}(x)` on `[0, 1]`.

The energy hypothesis holds at either end of a solution with finite energy on a half-strip, by
`TauCeti.tendsto_setLIntegral_Ioo_add_prod_atTop` and
`TauCeti.tendsto_setLIntegral_Ioo_add_prod_atBot`. -/
theorem apply_eq_and_hasDerivAt_of_tendsto_translate (ω : SymplecticForm V)
    {J : ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × ℝ)} (hH : ContDiff ℝ 1 (uncurry H))
    (hJ : ∀ t, Continuous fun x ↦ (J t x).toLinearMap.toContinuousLinearMap)
    (hJt : ∀ t x, ω.Tames (J t x)) (hu : ContDiffOn ℝ 1 u W)
    (hsol : ∀ z ∈ W, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hsW : ∀ a b, ∀ᶠ k in atTop, ∀ z ∈ Ioo a b ×ˢ Ioo (0 : ℝ) 1, z + (s k, 0) ∈ W)
    (hE : ∀ a b, Tendsto (fun k ↦ ∫⁻ z in Ioo (a + s k) (b + s k) ×ˢ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)) atTop (𝓝 0))
    (hv : ContDiff ℝ 1 v) (hx : ∀ z, Tendsto (fun k ↦ u (z + (s k, 0))) atTop (𝓝 (v z)))
    (hdx : ∀ z, Tendsto (fun k ↦ fderiv ℝ u (z + (s k, 0))) atTop (𝓝 (fderiv ℝ v z))) :
    (∀ σ, ∀ t ∈ Icc (0 : ℝ) 1, v (σ, t) = v (0, t)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun t ↦ v (0, t)) (ω.hamiltonianVectorField (H t) (v (0, t))) t := by
  have hKt : ContDiff ℝ 1 (uncurry fun w : ℝ × ℝ ↦ H w.2) := contDiff_uncurry_cylindrical hH
  -- On each window `(a, b) × (0, 1)` the translates have vanishing energy in the limit, so the
  -- perturbed derivative of `v` vanishes there.
  have hopen : ∀ z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1,
      ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0 := by
    intro z hz
    set Ω := Ioo (z.1 - 1) (z.1 + 1) ×ˢ Ioo (0 : ℝ) 1
    have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
    have hΩW : ∀ᶠ k in atTop, ∀ w ∈ Ω, w + (s k, 0) ∈ W :=
      hsW (z.1 - 1) (z.1 + 1)
    refine ω.perturbedFDeriv_eq_zero_of_tendsto_lintegral (J := fun w ↦ J w.2)
      (u := fun k w ↦ u (w + (s k, 0))) hΩ contDiffOn_const hKt.contDiffOn
      (fun w _ ↦ (hJ w.2).continuousAt) (fun w _ ↦ hJt _ _)
      (hΩW.mono fun k hk ↦ hu.comp (contDiff_id.add contDiff_const).contDiffOn hk)
      (hΩW.mono fun k hk w hw ↦ ?_) hv.contDiffOn (fun w _ ↦ hx w)
      (fun w _ ↦ by simpa only [fderiv_comp_add_right] using hdx w) ?_ z
      ⟨⟨by linarith, by linarith⟩, hz.2⟩
    · simpa [perturbedFDeriv_cylindrical_comp_add_right] using hsol _ (hk w hw)
    · refine (hE (z.1 - 1) (z.1 + 1)).congr fun k ↦ ?_
      have hpre : (· + (s k, 0)) ⁻¹'
          (Ioo (z.1 - 1 + s k) (z.1 + 1 + s k) ×ˢ Ioo (0 : ℝ) 1) = Ω := by
        ext w
        simp [Ω]
      rw [← lintegral_floerEnergyDensity_comp_add_right, hpre]
      simp
  -- By continuity it vanishes on the closed strip.
  have hXt : Continuous fun z : ℝ × ℝ ↦ ω.hamiltonianVectorField (H z.2) (v z) :=
    continuousOn_univ.1 (ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn isOpen_univ
      hv.continuous.continuousOn (by simpa using hKt.contDiffOn))
  have hclosed : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1,
      ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0 := by
    intro z hz
    refine ContinuousLinearMap.ext fun e ↦ ?_
    have hc : Continuous fun z ↦ ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z e := by
      simp only [perturbedFDeriv_apply, hamiltonianVectorField_const, Pi.zero_apply, smul_zero,
        sub_zero]
      exact ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
        (continuous_const.smul hXt)
    simpa using (EqOn.of_subset_closure (fun z hz ↦ congrArg (· e) (hopen z hz))
      hc.continuousOn continuous_const.continuousOn (prod_mono subset_rfl Ioo_subset_Icc_self)
      (by rw [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one])) hz
  -- So `v` is a solution with zero energy on the strip, hence stationary there.
  have hfl : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (v z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z : ℝ × ℝ →ₗ[ℝ] V) := fun z hz ↦ by
    rw [hclosed z hz, isComplexLinearMap_stdComplexLine_iff]
    simp
  have hE0 : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) v z) = 0 := by
    rw [setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ by
      rw [floerEnergyDensity_def, hclosed z hz]]
    simp
  refine ⟨(ω.lintegral_floerEnergyDensity_eq_zero_iff (J := fun z ↦ J z.2 (v z)) hH isOpen_univ
    hv.contDiffOn (subset_univ _) (fun _ _ ↦ hJt _ _) hfl).1 hE0, fun t ht ↦ ?_⟩
  -- Along `s = 0`, the equation `∂_t v - X_{H_t}(v) = 0` is Hamilton's equation.
  have h := ((hv.differentiable one_ne_zero) (0, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t))
  have h0 : fderiv ℝ v (0, t) stdComplexLineImag = ω.hamiltonianVectorField (H t) (v (0, t)) := by
    have h0 := congrArg (· stdComplexLineImag) (hclosed (0, t) ⟨mem_univ _, ht⟩)
    rwa [perturbedFDeriv_apply_stdComplexLineImag, zero_apply, sub_eq_zero] at h0
  rw [stdComplexLineImag_eq] at h0
  simpa [comp_def, h0] using h

/-- **The end actions converge to the action of the limit loop.** Let `H` be a continuous
time-dependent Hamiltonian and let `u` be `C¹` on an open set `W` which eventually contains the
segments `{s_k} × [0, 1]`. If the translates `u(· + (s_k, 0))` and their derivatives converge
locally uniformly to a differentiable map `v` and its derivative, then the actions of the loops
`t ↦ u(s_k, t)` converge to the action of the loop `t ↦ v(0, t)`.

Under the hypotheses of `SymplecticForm.apply_eq_and_hasDerivAt_of_tendsto_translate`, that loop
is a solution of Hamilton's equation, so the end actions converge to the action of an orbit. -/
theorem tendsto_hamiltonianAction_of_tendstoLocallyUniformly_translate (ω : SymplecticForm V)
    {W : Set (ℝ × ℝ)} (hH : Continuous (uncurry H)) (hW : IsOpen W) (hu : ContDiffOn ℝ 1 u W)
    (hsW : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1, (s k, t) ∈ W) (hv : Differentiable ℝ v)
    (hx : TendstoLocallyUniformly (fun k z ↦ u (z + (s k, 0))) v atTop)
    (hdx : TendstoLocallyUniformly (fun k z ↦ fderiv ℝ u (z + (s k, 0))) (fderiv ℝ v) atTop) :
    Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u (s k, t))) atTop
      (𝓝 (ω.hamiltonianAction H (fun t ↦ v (0, t)))) := by
  set γ : ℝ → ℝ × ℝ := fun t ↦ (0, t)
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image (by fun_prop)
  have hγ : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' (γ '' Icc 0 1) := subset_preimage_image γ _
  -- The derivatives of the loops are the `∂_t` derivatives of the maps.
  have hderiv {f : ℝ × ℝ → V} {c t : ℝ} (hf : DifferentiableAt ℝ f (c, t)) :
      deriv (fun t ↦ f (c, t)) t = fderiv ℝ f (c, t) (0, 1) := by
    have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t c).prodMk (hasDerivAt_id t))
    simpa [comp_def] using h.deriv
  have hdiff : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (s k, t) :=
    hsW.mono fun k hk t ht ↦
      (hu.differentiableOn one_ne_zero _ (hk t ht)).differentiableAt (hW.mem_nhds (hk t ht))
  have hline (k : ℕ) : Continuous fun t : ℝ ↦ (s k, t) := by fun_prop
  refine ω.tendsto_hamiltonianAction hH
    (hsW.mono fun k hk ↦ hu.continuousOn.comp (hline k).continuousOn fun t ht ↦ hk t ht)
    ((hsW.and hdiff).mono fun k hk ↦
      (((hu.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const).comp
        (hline k).continuousOn fun t ht ↦ hk.1 t ht).congr fun t ht ↦ hderiv (hk.2 t ht))
    ?_ ?_
  · simpa [comp_def, γ] using
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hx _ hK).comp γ).mono hγ
  · have h := (((ContinuousLinearMap.apply ℝ V ((0 : ℝ), (1 : ℝ))).uniformContinuous
      |>.comp_tendstoUniformlyOn (tendstoLocallyUniformly_iff_forall_isCompact.1 hdx _ hK)).comp
        γ).mono hγ
    refine (h.congr (hdiff.mono fun k hk t ht ↦ ?_)).congr_right fun t _ ↦ ?_
    · simp [γ, hderiv (hk t ht)]
    · simp [γ, hderiv (hv _)]

end Translate

end TauCeti.SymplecticForm
