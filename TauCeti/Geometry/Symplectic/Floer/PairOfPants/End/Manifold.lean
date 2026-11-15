/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# Asymptotic orbits and end convergence for Floer pairs of pants in manifolds

Let `K` be a Hamiltonian perturbation datum on `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond `T₀` on
an end `q` (or each end `q`) for `1`-periodic Hamiltonians `H_q` on a finite-dimensional manifold
`M` with nondegenerate two-form `ω`, and let `u : S → M` solve `(du - X_K)^{0,1} = 0` on `S` for
uniformly tame `J z` on `T_{u z} M` with `u(S) ⊆ B` for compact `B ⊆ M`. This file proves
subsequential orbit breaking at `q` under finite energy, whole-end (`s → ∞`) convergence under
nondegeneracy and bounded end derivative, and the manifold pair-of-pants energy identity.

**Positive end charts.** In `φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart`), `K` pulls
back beyond `T₀` to `H'_q(t) dt` for `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), so `u ∘ φ'_q` solves the half-cylinder Floer equation
beyond `T₀` (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`) with
end energy bounded by the energy over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`), and orbits of
`X_{H'_q}` read at `±t` give orbits of `X_{H_q}`
(`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul`,
`TauCeti.SmoothTwoForm.mem_contractiblePeriodicSolutions_comp_endSign_mul`).

**Breaking and convergence at an end.** Measuring convergence and tameness near `B` through `C¹`
`e : M → F` injective on `B` with injective differential on `B`
(`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`):
* Finite energy yields a `1`-periodic orbit `y_q` in `B` and `s_n → ∞` with `u(φ_q(±s_n, ·)) → y_q`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`,
  `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`).
* For `C²` `H_q` on Hausdorff boundaryless `M` with `d(e ∘ u ∘ φ'_q)` bounded on `s > b` and
  cluster-point `1`-periodic orbits in `B` nondegenerate, `u(φ_q(±s, ·)) → y_q` as `s → ∞`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`), or in the contractible
  sector (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer` and
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`).

**The manifold energy identity with asymptotic orbits.** When `u(S) ⊆ B` and `u^*ω` and `R_K(u)` are
integrable, the energy is finite
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_ne_top_of_isCompact`), and dominated
convergence (`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`) yields
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` at genuine asymptotic `1`-periodic
(or contractible `1`-periodic) orbits `y_q` (in `TauCeti.SmoothTwoForm.IsNondegenerate`:
`exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`,
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`,
`exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`, and
`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation`), lifting
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` to manifolds.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

open Floer

private theorem tendstoUniformly_endChart_of_positiveEndChart {ι α β : Type*}
    [TopologicalSpace α] [UniformSpace β] {l : Filter ι} {q : Puncture} {e : α → β}
    {u : ℝ × ℝ → α} {x : ℝ → α} {σ : ι → ℝ}
    (hu : TendstoUniformly (fun i t ↦ e (u (positiveEndChart q (σ i, t)))) (e ∘ x) l)
    (hpt : ∀ t, Tendsto (fun i ↦ u (positiveEndChart q (σ i, t))) l (𝓝 (x t))) :
    TendstoUniformly (fun i t ↦ e (u (endChart q (q.endSign * σ i, t))))
        (e ∘ fun t ↦ x (q.endSign * t)) l ∧
      ∀ t, Tendsto (fun i ↦ u (endChart q (q.endSign * σ i, t))) l (𝓝 (x (q.endSign * t))) :=
  ⟨by simpa only [Function.comp_def, endChart_eq_positiveEndChart] using
      hu.comp (fun t ↦ q.endSign * t),
    fun t ↦ by simpa only [endChart_eq_positiveEndChart, comp_apply] using hpt (q.endSign * t)⟩

section

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Orbits and positive end charts on a manifold -/

/-- Reading an orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the end gives an
orbit of `H_q`. -/
theorem hasMFDerivAt_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I x t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t ↦ x (q.endSign * t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t)))) := by
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ ↦ q.endSign * τ) t
      (q.endSign • ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id t).const_smul q.endSign)
  have hH : positiveEndHamiltonian H q (q.endSign * t) = q.endSign • H q t :=
    funext fun y ↦ by simp [positiveEndHamiltonian_apply, ← mul_assoc]
  have hder : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField
        (positiveEndHamiltonian H q (q.endSign * t)) (x (q.endSign * t)))).comp
        (q.endSign • ContinuousLinearMap.id ℝ ℝ :
          TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (q.endSign * t))) := by
    apply ContinuousLinearMap.ext_ring
    -- `TangentSpace 𝓘(ℝ, ℝ)` is definitionally `ℝ`, so `q.endSign • id` sends `1` to `q.endSign`.
    have hg1 : (q.endSign • ContinuousLinearMap.id ℝ ℝ :
        TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (q.endSign * t)) 1 = (q.endSign : ℝ) := by
      simp
    rw [ContinuousLinearMap.comp_apply, hg1, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, one_apply_eq_self, hH,
      hamiltonianVectorField_const_smul, smul_smul, endSign_mul_self, one_smul]
  exact ((hx (q.endSign * t)).comp t hg).congr_mfderiv hder.symm

/-- A `1`-periodic orbit of the positive end Hamiltonian `H'_q`, read with the time `±t` of the
end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxd, hxper⟩ := mem_periodicSolutions.1 hx
  exact mem_periodicSolutions.2 ⟨hasMFDerivAt_comp_endSign_mul hxd, periodic_comp_endSign_mul hxper⟩

/-- A contractible `1`-periodic orbit of the positive end Hamiltonian `H'_q`, read with the time
`±t` of the end, is a contractible `1`-periodic orbit of `H_q`. -/
theorem mem_contractiblePeriodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ contractiblePeriodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1) :
    (fun t ↦ x (q.endSign * t)) ∈
      contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  obtain ⟨hxp, g, hg, hgx⟩ := mem_contractiblePeriodicSolutions.1 hx
  have h := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
  rw [abs_endSign, div_one] at h
  obtain ⟨g', hg', hg'g⟩ := h
  exact mem_contractiblePeriodicSolutions.2
    ⟨mem_periodicSolutions_comp_endSign_mul hxp, g', hg', fun t ↦ by rw [hg'g, hgx, mul_comm]⟩

omit [IsManifold I (⊤ : ℕ∞) M] in
private theorem mdifferentiableAt_perturbation_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (v : ℂ) (y : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)
      y := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    simpa [positiveEndChart_apply, re_endCoord_endChart, ← mul_assoc] using hζ
  have h : (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) = fun x ↦
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v •
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x :=
    funext fun x ↦ by rw [hKH _ x hre, smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  exact h ▸ (hHd _ y).const_smul _

private theorem perturbedMFDeriv_comp_positiveEndChart_eq {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) {u : ℝ × ℝ → M} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ =
      ω.perturbedMFDeriv
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag)
        (u ∘ positiveEndChart q) ζ := by
  refine ContinuousLinearMap.ext fun (a : ℝ × ℝ) ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply,
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x,
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x]

/-- **An end of a Floer pair of pants in a manifold solves the Floer equation of a half-cylinder.**
Let `K` be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a Hamiltonian `H_q` that is
`1`-periodic in time and differentiable in the target variable, and let `u` be differentiable at
`φ'_q(ζ)` with `ζ.1 ≥ T₀` and solve `(du - X_K)^{0,1} = 0` there for `J` on `T_{u(φ'_q(ζ))} M`. Then
`u ∘ φ'_q` solves `∂_s v + J (∂_t v - X_{H'_q}(v)) = 0` at `ζ` for the positive end Hamiltonian
`H'_q`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M} {ζ : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (positiveEndChart q ζ)))}
    (hζ : T₀ ≤ ζ.1) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (positiveEndChart q ζ))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positiveEndChart q ζ)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (u ∘ positiveEndChart q) ζ).toLinearMap := by
  rw [perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζ]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hu
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ 1 _)
    (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζ Complex.I _)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hfloer

/-- **The energy of an end of a Floer pair of pants in a manifold.** Let `K` be equal to `H_q(t) dt`
beyond `T₀` on the end `q`, for `H_q` that is `1`-periodic in time and differentiable in the target
variable, and let `u` be differentiable on `S`. Then the energy of `u ∘ φ'_q` for `H'_q` over
`(a, ∞) × [0, 1]` (`a ≥ max T₀ 0`) is at most the energy of `u` over `S`. -/
theorem setLIntegral_floerEnergyDensity_comp_positiveEndChart_le {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t)) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal) {a : ℝ}
    (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) z) ≤
      ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Ioi a ×ˢ Ioo 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ioo_ae_eq_Icc.symm
  have hdens : ∀ ζ ∈ Ioi a ×ˢ Ioo (0 : ℝ) 1, ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ =
        |(fderiv ℝ (positiveEndChart q) ζ).det| * ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u (positiveEndChart q ζ) := by
    intro ζ hζ
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (ha₀.trans_lt hζ.1)
    have hζT : T₀ ≤ ζ.1 := haT.trans hζ.1.le
    rw [floerEnergyDensity_def, perturbedMFDeriv_comp_positiveEndChart_eq hKH hH hζT,
      ← floerEnergyDensity_def, abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
    exact ω.floerEnergyDensity_perturbationPullback
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
      ((hu _ hS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS))
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT 1 _)
      (mdifferentiableAt_perturbation_positiveEndChart hKH hHd hζT Complex.I _)
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul
    (measurableSet_Ioi.prod measurableSet_Ioo)
    ((injOn_positiveEndChart q).mono (prod_mono (subset_univ _) le_rfl))
    (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ) hdens]
  exact lintegral_mono_set fun _ ⟨_, hζ, h⟩ ↦
    h ▸ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ.1)

/-! ### Asymptotic orbits at the ends -/

section EndOrbits

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ F] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart
    {ι : Type*} {l : Filter ι} [l.NeBot] {q : Puncture} (he : Continuous e) {B : Set M}
    (hB : IsCompact B) (he_inj : InjOn e B) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {X : ℝ → (x : M) → TangentSpace I x} {σ : ι → ℝ} (hσ : ∀ᶠ i in l, 0 < σ i) {y : ℝ → M}
    (hy : y ∈ periodicSolutions X 1) (hyB : ∀ t, y t ∈ B)
    (hconv : TendstoUniformly (fun i t ↦ e (u (endChart q (q.endSign * σ i, t)))) (e ∘ y) l) :
    y ∈ contractiblePeriodicSolutions X 1 :=
  mem_contractiblePeriodicSolutions_of_tendstoUniformly_Ioi
    (u := fun p ↦ u (endChart q (q.endSign * p.1, p.2))) one_pos he hB he_inj
    (hu.comp ((contDiff_endChart q 0).continuous.comp (by fun_prop)).continuousOn
      fun p hp ↦ endChart_endSign_mul_mem_thricePuncturedSphereReal hp.1 p.2)
    (fun _ _ t ↦ by simp only [endChart_add_one])
    (fun _ hs t ↦ huB _ (endChart_endSign_mul_mem_thricePuncturedSphereReal hs t))
    hnull hσ hy hyB hconv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem floer_comp_positiveEndChart_of_le {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (ha₀ : 0 ≤ a) (haT : T₀ ≤ a) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    (hHs.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)).mdifferentiable one_ne_zero
  have hud : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u thricePuncturedSphereReal :=
    hu.mdifferentiableOn one_ne_zero
  have hmem {z : ℝ × ℝ} (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn (fun _ hz ↦ hmem hz.1),
    fun z hz ↦ ?_, ne_top_of_le_ne_top hE
      (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd hud ha₀ haT)⟩
  have heq := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 <|
      isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd (haT.trans hz.1.le)
        ((hud _ (hmem hz.1)).mdifferentiableAt
          (isOpen_thricePuncturedSphereReal.mem_nhds (hmem hz.1)))
        (hfloer _ (hmem hz.1))
  rwa [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] at heq

namespace IsNondegenerate

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at an end.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q` on `M`,
and let `u` be `C¹` on `S`, with image in a compact set `B`, solving `(du - X_K)^{0,1} = 0` on `S`
with finite energy. For `e : M → F` of class `C¹`, injective on `B` with injective differential on
`B`, and almost complex structures uniformly tame wrt `e` on `s > b` of `φ'_q`, there are a
`1`-periodic orbit `y` of `X_{H_q}` in `B` and `s_n → ∞` along which `t ↦ u(φ_q(±s_n, t))` converges
to `y` pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := le_max_of_le_left (le_max_right _ _)
  obtain ⟨hu', hfloer', hE'⟩ := floer_comp_positiveEndChart_of_le hKH hH hHs hu hfloer hE ha₀
    (le_max_of_le_left (le_max_left _ _))
  obtain ⟨x, hx, hxB, φ, -, hφ, hux, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHs) (periodic_positiveEndHamiltonian hH)
      he hB he_inj hde hu' (fun _ _ _ ↦ by simp only [positiveEndChart_add_one])
      (fun _ hs _ ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v) hfloer' hE'
  exact ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx, fun _ ↦ hxB _,
    φ, hφ, tendstoUniformly_endChart_of_positiveEndChart hux hpt⟩

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at an end.** The
compact-manifold case of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {b c : ℝ} (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact hKH hH hHs he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hc hJc hfloer hE).imp
    fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-! ### Convergence along the whole end to nondegenerate orbits -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q))) {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hnd : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (x 0)) :
    ∃ U ∈ 𝓝 (x 0), ∀ z ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
      z 0 ∈ U → z = x := by
  obtain ⟨U, hU, hU'⟩ := hω.exists_mem_nhds_forall_mem_periodicSolutions_hamiltonianVectorField_eq
    hHs (mem_periodicSolutions.1 (mem_periodicSolutions_comp_endSign_mul hx)).1
    (by simpa only [mul_zero] using hnd)
  refine ⟨U, by simpa only [mul_zero] using hU, fun z hz hzU ↦ funext fun t ↦ ?_⟩
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using
    congrFun (hU' _ (mem_periodicSolutions_comp_endSign_mul hz) (by simpa [mul_zero] using hzU))
      (q.endSign * t)

/-- **An end of a Floer pair of pants in a manifold converges to a nondegenerate orbit.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a `1`-periodic `C²` Hamiltonian `H_q` on a
Hausdorff boundaryless manifold `M` with nondegenerate `ω`, and let `u` be `C¹` on `S` with image in
compact `B`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. If every `1`-periodic orbit
of `H_q` in `B` along which a sequence of end loops converges uniformly starts at a nondegenerate
fixed point of the time-one map, and on `s > b` of `φ'_q` the derivative `d(e ∘ u ∘ φ'_q)` is
bounded and `J` is uniformly tame wrt `e`, then `t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single
`1`-periodic orbit `y` of `X_{H_q}` in `B`, pointwise in `M` and uniformly after `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c) (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := le_max_of_le_left (le_max_right _ _)
  obtain ⟨hu', hfloer', hE'⟩ := floer_comp_positiveEndChart_of_le hKH hH (hHsq.of_le one_le_two) hu
    hfloer hE ha₀ (le_max_of_le_left (le_max_left _ _))
  obtain ⟨x, hx, hxB, hux, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHsq.of_le one_le_two))
      (periodic_positiveEndHamiltonian hH) he hB he_inj hde hu'
      (fun _ _ _ ↦ by simp only [positiveEndChart_add_one])
      (fun _ hs _ ↦ huB _ (positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hs)))
      (fun z hz ↦ hC z ((le_max_right _ _).trans_lt hz.1)) (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc z ((le_max_right _ _).trans_lt hz.1) v) hfloer' hE'
      fun x hx hxB ⟨σ, hσa, hσtop, hσu, hσpt⟩ ↦ by
        have hnd₀ := hnd (fun t ↦ x (q.endSign * t)) (mem_periodicSolutions_comp_endSign_mul hx)
          (fun _ ↦ hxB _) ⟨σ, fun n ↦ ha₀.trans_lt (hσa n), hσtop,
            tendstoUniformly_endChart_of_positiveEndChart hσu hσpt⟩
        exact (hω.exists_mem_nhds_forall_eq_of_isNondegenerateFixedPt hHsq hx
          (by simpa only [mul_zero] using hnd₀)).imp fun _ ⟨hU, hU'⟩ ↦ ⟨hU, fun z hz _ _ ↦ hU' z hz⟩
  exact ⟨fun t ↦ x (q.endSign * t), mem_periodicSolutions_comp_endSign_mul hx, fun _ ↦ hxB _,
    tendstoUniformly_endChart_of_positiveEndChart (σ := fun s ↦ s) hux hpt⟩

/-- **An end of a Floer pair of pants in a closed manifold converges to a nondegenerate orbit.** The
compact-manifold case of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c) (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hfloer hE hHsq
    (fun y hy _ ↦ hnd y hy) hC hc hJc).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

/-- **A contractible end of a Floer pair of pants in a manifold converges to a nondegenerate
contractible orbit.** Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, if some circle
`t ↦ u(φ_q(±s, t))` (`s > 0`) on `q` is contractible in `M` and every contractible `1`-periodic
orbit of `H_q` in `B` is nondegenerate (noncontractible periodic orbits may be degenerate), then
`t ↦ u(φ_q(±s, t))` converges as `s → ∞` to a single contractible `1`-periodic orbit `y` in `B`,
pointwise in `M` and uniformly after `e`. -/
theorem
  exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c) (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, hyB, huy, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      he hB he_inj hde hu huB hfloer hE hHsq (fun z hz hzB ⟨σ, hσpos, _, hσu, _⟩ ↦
        hnd z (mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart (l := atTop)
          he.continuous hB he_inj hu.continuousOn huB hnull (Eventually.of_forall hσpos) hz hzB
          hσu) hzB) hC hc hJc
  exact ⟨y, mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart he.continuous hB he_inj
    hu.continuousOn huB hnull (eventually_gt_atTop 0) hy hyB huy, hyB, huy, hpt⟩

/-- **A contractible end of a Floer pair of pants in a closed manifold converges to a nondegenerate
contractible orbit.** The compact-manifold case of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate) {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hHsq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (hnd : ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    {b C c : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hc : 0 < c) (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v)) :
    ∃ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  (exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    hω hKH hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull
    hfloer hE hHsq (fun y hy _ ↦ hnd y hy) hC hc hJc).imp fun _ ⟨hy, _, h⟩ ↦ ⟨hy, h⟩

end IsNondegenerate
end EndOrbits
end

/-! ### The energy identity with asymptotic orbits on a manifold -/

section EnergyIdentity

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

namespace IsNondegenerate

/-- **The manifold pair-of-pants energy identity with nondegenerate asymptotic orbits.** Let `K` be
`C¹` on `S × M` and equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C²`
Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` with nondegenerate `ω`. Let `u` be `C¹`
on `S` with image in compact `B`, solving `(du - X_K)^{0,1} = 0` on `S` for uniformly tame `J` wrt
`e : M → F`, with integrable `u^*ω` and `R_K(u)` over `S` and `d(e ∘ u ∘ φ'_q)` bounded on a
half-cylinder of each end `q`. If every sequential cluster-point `1`-periodic orbit of `H_q` in `B`
is nondegenerate, then `u` has finite energy, its end loops converge as `s → ∞` to `1`-periodic
orbits `y_q` in `B`, its Floer energy density is integrable over `S`, and
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    floerEnergyDensity_nonneg hω (fun v hv ↦ (mul_pos hc (pow_pos (norm_pos_iff.2 fun hdv ↦
      hv ((hde _ (huB z hz)).eq_iff.1 (by rwa [map_zero]))) 2)).trans_le (hJc z hz v)) (hfloer z hz)
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hA hR
  have hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
    rw [hS]
    exact hω.lintegral_floerEnergyDensity_ne_top_of_isCompact hK hKH hH
      (fun q ↦ (hHs q).continuous) hB hu huB he_nonneg hA hR
  choose b C hbC using hC
  choose y hy using fun q ↦
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
      (hKH q) (hH q) he hB he_inj hde hu huB hfloer hE (hHs q) (hnd q)
      (b := max (b q) 0) (fun z hz ↦ hbC q z ((le_max_left _ _).trans_lt hz)) hc
      fun z hz v ↦ hJc _ (positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hz)) v
  have hh (q : Puncture) := tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous
    hu.continuousOn hB huB tendsto_id fun t _ ↦ (hy q).2.2.2 t
  have hint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA hR hh
  refine ⟨y, hy, by rwa [IntegrableOn, hS], ?_⟩
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hint hA hR hh

/-- **The energy identity of the pair-of-pants perturbation with nondegenerate asymptotic orbits.**
The specialization of `exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact` to
`TauCeti.Floer.pairOfPantsPerturbation`, whose curvature term is automatically integrable. -/
theorem
  exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 (q) := (hHs q).of_le one_le_two
  exact hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- **The energy identity of the pair-of-pants perturbation in a closed manifold**
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` on
a compact Hausdorff boundaryless manifold `M`). -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t))) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  (exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    hω hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hc hJc
    hfloer hA (fun q y hy _ ↦ hnd q y hy) hC).imp fun _ ⟨hy, hint, hid⟩ ↦
      ⟨fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hint, hid⟩

/-- **The manifold pair-of-pants energy identity with contractible asymptotic orbits.** Under the
hypotheses of `exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact`, if on each
end `q` some circle `t ↦ u(φ_q(±s, t))` (`s > 0`) is contractible in `M` and every contractible
`1`-periodic orbit of `H_q` in `B` is nondegenerate (noncontractible periodic orbits may be
degenerate), then `u` has finite energy, its end loops converge as `s → ∞` to contractible
`1`-periodic orbits `y_q` in `B`, its Floer energy density is integrable over `S`, and
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  obtain ⟨y, hy, hint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_eq_of_isCompact hK hKH hH hHs he hB
      he_inj hde hu huB hc hJc hfloer hA hR (fun q z hz hzB ⟨σ, hσpos, _, hσu, _⟩ ↦
        hnd q z (mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart (l := atTop)
          he.continuous hB he_inj hu.continuousOn huB (hnull q) (Eventually.of_forall hσpos) hz hzB
          hσu) hzB) hC
  exact ⟨y, fun q ↦ ⟨mem_contractiblePeriodicSolutions_of_tendstoUniformly_endChart he.continuous
    hB he_inj hu.continuousOn huB (hnull q) (eventually_gt_atTop 0) (hy q).1 (hy q).2.1
    (hy q).2.2.1, (hy q).2⟩, hint, hid⟩

/-- **The energy identity of the pair-of-pants perturbation with contractible asymptotic orbits**
(`exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact` for
`TauCeti.Floer.pairOfPantsPerturbation`). -/
theorem exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs1 (q) := (hHs q).of_le one_le_two
  exact hω.exists_mem_contractiblePeriodicSolutions_integral_floerEnergyDensity_eq_of_isCompact
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs1 w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs1 hu.continuousOn) hnd hC

/-- **The energy identity of the pair-of-pants perturbation with contractible asymptotic orbits in
a closed manifold:** the compact-manifold case of
`exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact`. -/
theorem exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧
      ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hnd : ∀ q, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  (exists_mem_contractiblePeriodicSolutions_integral_pairOfPantsPerturbation_of_isCompact
    hω hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull
    hc hJc hfloer hA (fun q y hy _ ↦ hnd q y hy) hC).imp fun _ ⟨hy, hint, hid⟩ ↦
      ⟨fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hint, hid⟩

end IsNondegenerate
end EnergyIdentity
end SmoothTwoForm
end TauCeti
