/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere.Basic
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Fredholm.SemiFredholm
import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Plane
import TauCeti.Geometry.Symplectic.Floer.Linearization.Infinity
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Cokernel
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.Constructions.SumProd

/-!
# The linearized Floer operator on the Riemann sphere is Fredholm

Let `D_u : W^{1,2}(S², V) → L²(S², V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the weight
`TauCeti.Floer.sphereWeight`) of the linearized Floer operator of data on the Riemann sphere, read
in the coordinate `w ∈ ℂ ≅ ℝ × ℝ`, which near the point at infinity are a fixed compatible
structure `J₀` and the zero perturbation. Its kernel is finite-dimensional and its range is closed
(`finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base`,
`isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`, in the namespace
`TauCeti.SymplecticForm`).
This file proves that its cokernel is finite-dimensional too, so that `D_u` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base`). These
are the domains of the comparison family between the pair-of-pants product and the quantum
product, whose members are three-pole spheres unperturbed near their poles.

By Peetre's argument
(`TauCeti.SymplecticForm.finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_le`)
it suffices that every cokernel element, a square-integrable `C²` covector field `η` with
`D_u^* η = 0`, satisfies `∫ ‖η‖² ≤ A ∫_K ‖η‖²` for a compact square `K`. This comes from the
semi-Fredholm estimate of `D_u^*` on the sphere
`exists_forall_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add_of_eq_base`
in the namespace `TauCeti.SymplecticForm`, which bounds the `W^{1,2}` norm of compactly supported
fields, in the chart `w` on a disc `|w| ≤ R` and in the chart `ζ = w⁻¹` on the rest of the sphere,
by `∫ (1 + |w|²)² ‖D_u^* η‖²` and the `L²` norm on `K`. It is applied to cut-off fields `χ η`.

* **Decay at infinity.** Near infinity the data are constant, and `η` read as a `(0, 1)`-form in
  the chart `ζ`, `η' = η (ζ⁻¹) ∘ (a + b J₀)` with `a + i b = -ζ⁻²`, extends smoothly across
  `ζ = 0` (`exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero`, in the
  namespace `TauCeti.SymplecticForm`).
  So `η'` is bounded near `ζ = 0`, and inverting `a + b J₀`, whose squared norm is the Jacobian
  `|w|⁴` of the inversion
  (`TauCeti.Floer.det_mul_norm_sq_le_mul_norm_covectorPullback_realChart_sq`), gives
  `|w|⁴ ‖η(w)‖² ≤ S` for large `|w|`.
* **Logarithmic cutoffs.** Since `D_u^* η = 0`, the adjoint of `χ η` only involves `dχ`, and
  `(1 + |w|²)² ‖D_u^* (χ η)‖² ≤ 4 (1 + B)² S ‖dχ‖²` where `dχ` lives. A cutoff with linear profile
  at scale `n` has Dirichlet energy bounded below independently of `n`, but the logarithmic cutoffs
  `χ_n`, equal to `1` on `|w| ≤ n` and to `0` on `|w| ≥ n²`, have energy at most
  `8π c₀² / log n` (`TauCeti.Complex.exists_contDiff_logCutoff`), since a point of the plane, here
  the point at infinity, has capacity zero. So the weighted adjoint term of `χ_n η` tends to zero.
* **The `L²` norm near infinity.** Changing variables along the inversion, whose Jacobian is
  `|w|⁴`, the `L²` norm of `χ_n η` on `|w| > R` is at most `(1 + B)²` times the `W^{1,2}` energy of
  its pullback on `|ζ| ≤ R⁻¹`, which the estimate controls. Letting `n → ∞` gives the claim, the
  tail `∫_{|w| ≥ n} ‖η‖²` tending to zero.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendices B and C, on the Fredholm property
  of real Cauchy–Riemann operators on closed surfaces.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Floer problems on the sphere comparing the pair-of-pants and quantum products.
-/

public section

open Set Function Filter MeasureTheory Metric Real
open scoped ENNReal Topology
open TauCeti.Complex (realChart contDiffAt_realChart_inv)

namespace TauCeti

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V} {J₀ : AlmostComplexStructure V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- `J` is bounded along `u` when it is continuous along a continuous `u` and equal to `J₀` on
`‖z‖ ≥ T`. -/
private theorem exists_forall_norm_le_of_eq_base (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hJ : ∀ z, ContinuousAt
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : Continuous u) :
    ∃ B, ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℝ × ℝ) T).exists_bound_of_continuousOn
    (continuous_comp_prodMk_of_continuousAt hJ hu).continuousOn
  refine ⟨max B₀ ‖J₀.toLinearMap.toContinuousLinearMap‖, fun z ↦ ?_⟩
  rcases le_or_gt ‖z‖ T with hz | hz
  · exact (hB₀ z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · rw [hJ₀ z hz.le]
    exact le_max_right _ _

/-- Where `|w| > 2 max T 0 + 1`, the data are `J₀` and `0` near `w`, so a covector field annihilated
by the formal adjoint of the data is annihilated by that of the constant data. -/
private theorem floerLinearizationAdjoint_const_eq_zero_of_eq_base (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) {z : ℝ × ℝ}
    (hz : 2 * max T 0 + 1 < ‖Complex.equivRealProdCLM.symm z‖) :
    ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u η z = 0 := by
  have hzT : max T 0 < ‖z‖ := by linarith [norm_equivRealProdCLM_symm_le_two_mul z]
  have hT : T ≤ ‖z‖ := (le_max_left _ _).trans hzT.le
  rw [← ω.floerLinearizationAdjoint_congr_data u η
    (eventuallyEq_const_of_eq_base hJ₀ (by linarith [le_max_left T 0]))
    (funext (hKs₀ z hT)) (funext (hKt₀ z hT))]
  exact hD z

/-- **Decay at infinity of solutions of the adjoint.** Let the data be `J₀` and the zero
perturbation on `‖z‖ ≥ T`, with `ω` invariant under `J₀`. A square-integrable `C¹` covector field
`η` with `D_u^* η = 0` satisfies `|w|⁴ ‖η(w)‖² ≤ S` on `|w| ≥ r`, for some `r` and `S`: read in
the chart `ζ = w⁻¹`, it extends smoothly across `ζ = 0`, hence is bounded near `ζ = 0`, and the
factor `a + b J₀` of the pullback has squared norm the Jacobian `|w|⁴` of the inversion. -/
private theorem exists_mul_norm_sq_le_of_floerLinearizationAdjoint_eq_zero (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) (h₀ : ω.Invariant J₀)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2) :
    ∃ r S, 0 ≤ S ∧ ∀ z, r ≤ ‖Complex.equivRealProdCLM.symm z‖ →
      ‖Complex.equivRealProdCLM.symm z‖ ^ 4 * ‖η z‖ ^ 2 ≤ S := by
  set T₁ := 2 * max T 0 + 1
  have hT₁ : 0 < T₁ := by positivity
  obtain ⟨η₀, hη₀, hη₀eq⟩ :=
    exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero h₀ u
      (T := T₁) (fun z _ ↦ (hη.differentiable one_ne_zero) z)
      (fun z hz ↦ floerLinearizationAdjoint_const_eq_zero_of_eq_base ω hJ₀ hKs₀ hKt₀ hD hz)
      hηi.integrableOn
  -- `η₀` is bounded on the closed disc `|ζ| ≤ (2 T₁)⁻¹`.
  have hsub : {ζ : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ (2 * T₁)⁻¹} ⊆
      {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < T₁⁻¹} := fun ζ hζ ↦
    lt_of_le_of_lt hζ (inv_strictAnti₀ hT₁ (by linarith))
  obtain ⟨S₀, hS₀⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * T₁)⁻¹).exists_bound_of_continuousOn
      (hη₀.continuousOn.mono hsub)
  refine ⟨2 * T₁, (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 * S₀ ^ 2, by positivity,
    fun z hz ↦ ?_⟩
  have hz0 : 0 < ‖Complex.equivRealProdCLM.symm z‖ := by linarith
  -- The point `ζ = w⁻¹` of the disc, where `η₀` is the pullback of `η`.
  have hζz : realChart (·⁻¹) (realChart (·⁻¹) z) = z := TauCeti.Complex.realChart_inv_involutive z
  have hNζ := TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv z
  have hζ0 : Complex.equivRealProdCLM.symm (realChart (·⁻¹) z) ≠ 0 := by
    rw [← norm_pos_iff, hNζ]
    positivity
  have hζD : ‖Complex.equivRealProdCLM.symm (realChart (·⁻¹) z)‖ ≤ (2 * T₁)⁻¹ := by
    rw [hNζ]
    exact inv_anti₀ (by positivity) hz
  have hdet : (fderiv ℝ (realChart (·⁻¹)) (realChart (·⁻¹) z)).det =
      ‖Complex.equivRealProdCLM.symm z‖ ^ 4 := by
    rw [TauCeti.Complex.det_fderiv_realChart_inv hζ0, hζz]
  have h := det_mul_norm_sq_le_mul_norm_covectorPullback_realChart_sq (u := u) (g := η)
    (J := fun _ _ ↦ J₀) (hasDerivAt_inv hζ0) (by rw [hdet]; positivity) le_rfl
  rw [hdet, hζz, ← hη₀eq _ (hsub hζD) hζ0] at h
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    (sq_nonneg _))
  simpa using hS₀ _ hζD

/-- Away from `ζ = 0`, the pullback `g' = g (ζ⁻¹) ∘ (a + b J)` of a `C¹` covector field `g` through
the inversion is `C¹`, when `J` is `C¹` along a `C¹` map `u`. -/
private theorem contDiffAt_covectorPullback_realChart_inv
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) {ζ : ℝ × ℝ}
    (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    ContDiffAt ℝ 1 (covectorPullback (realChart (·⁻¹))
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g) ζ := by
  set ι : ℝ × ℝ → ℝ × ℝ := realChart (·⁻¹)
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  have hι : ContDiffAt ℝ 2 ι ζ := contDiffAt_realChart_inv hζ
  have hι1 : ContDiffAt ℝ 1 ι ζ := hι.of_le one_le_two
  have hd : ContDiffAt ℝ 1 (fun ζ ↦ fderiv ℝ ι ζ stdComplexLineReal) ζ :=
    (hι.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hJu : ContDiffAt ℝ 1 (fun ζ ↦ J' (ι ζ) (u (ι ζ))) ζ :=
    (hJ (ι ζ)).comp (f := fun ζ ↦ (ι ζ, u (ι ζ))) ζ (hι1.prodMk (hu.contDiffAt.comp ζ hι1))
  have hM : ContDiffAt ℝ 1 (fun ζ ↦ (fderiv ℝ ι ζ stdComplexLineReal).1 • (1 : V →L[ℝ] V) +
      (fderiv ℝ ι ζ stdComplexLineReal).2 • J' (ι ζ) (u (ι ζ))) ζ :=
    ((contDiff_fst.contDiffAt.comp ζ hd).smul contDiffAt_const).add
      ((contDiff_snd.contDiffAt.comp ζ hd).smul hJu)
  rw [show covectorPullback ι J' u g = _ from funext (covectorPullback_apply ι J' u g)]
  exact (hg.contDiffAt.comp ζ hι1).clm_comp hM

/-- **A cut-off field read through the inversion.** For a compactly supported `C¹` covector field
`g`, the `W^{1,2}` density of its pullback `g' = g (ζ⁻¹) ∘ (a + b J)` through the inversion is
integrable on every disc `|ζ| ≤ ρ`. Away from `ζ = 0` the pullback is `C¹`, and near `ζ = 0` it
vanishes since `g` has compact support. -/
private theorem integrableOn_sobolevDensity_covectorPullback_inv
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (ρ : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (realChart (·⁻¹))
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g))
      {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ ρ} := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set ι : ℝ × ℝ → ℝ × ℝ := realChart (·⁻¹)
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set N : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hNc : Continuous N := Complex.equivRealProdCLM.symm.continuous.norm
  -- Near `ζ = 0`, away from `ζ = 0`, the pullback vanishes.
  obtain ⟨M, hM⟩ := hgc.isCompact.exists_bound_of_continuousOn hNc.continuousOn
  set M' := max M 1
  have hM'0 : 0 < M' := lt_max_of_lt_right one_pos
  have hvan (ζ : ℝ × ℝ) (hζ0 : Complex.equivRealProdCLM.symm ζ ≠ 0) (hζ : N ζ < M'⁻¹) :
      sobolevDensity (covectorPullback ι J' u g) ζ = 0 := by
    have hev : covectorPullback ι J' u g =ᶠ[𝓝 ζ] 0 := by
      filter_upwards [(isOpen_lt hNc continuous_const).mem_nhds hζ,
        (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds hζ0]
        with ζ' hζ' hζ'0
      refine covectorPullback_eq_zero_of_apply_eq_zero ι J' u
        (image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_)
      have h1 := hM _ hmem
      have h2 : N (ι ζ') = (N ζ')⁻¹ := TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv ζ'
      have h3 : M' < (N ζ')⁻¹ := lt_inv_of_lt_inv₀ (norm_pos_iff.2 hζ'0) hζ'
      have h4 : ‖‖Complex.equivRealProdCLM.symm (ι ζ')‖‖ = N (ι ζ') := norm_norm _
      linarith [le_max_left M 1]
    simp [sobolevDensity_apply, hev.fderiv_eq, hev.eq_of_nhds]
  -- Integrable on the compact annulus `(2 M')⁻¹ ≤ |ζ| ≤ ρ`, and zero almost everywhere off it.
  set K' := {ζ : ℝ × ℝ | (2 * M')⁻¹ ≤ N ζ} ∩ {ζ | N ζ ≤ ρ}
  have hK' : IsCompact K' := (isCompact_setOf_norm_equivRealProdCLM_symm_le ρ).of_isClosed_subset
    ((isClosed_le continuous_const hNc).inter (isClosed_le hNc continuous_const))
    inter_subset_right
  have hint : IntegrableOn (sobolevDensity (covectorPullback ι J' u g)) K' :=
    ContinuousOn.integrableOn_compact hK' fun ζ hζ ↦
      (continuousAt_sobolevDensity (contDiffAt_covectorPullback_realChart_inv hJ hu hg
        (norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hζ.1)))).continuousWithinAt
  refine hint.of_ae_sdiff_eq_zero
    (measurableSet_le hNc.measurable measurable_const).nullMeasurableSet
    ((Measure.ae_ne volume 0).mono fun ζ hζ0 hζ ↦ ?_)
  have hζ0' : Complex.equivRealProdCLM.symm ζ ≠ 0 := fun h ↦
    hζ0 (Complex.equivRealProdCLM.symm.map_eq_zero_iff.1 h)
  have hlt : N ζ < (2 * M')⁻¹ := by
    by_contra h
    exact hζ.2 ⟨not_lt.1 h, hζ.1⟩
  exact hvan ζ hζ0' (hlt.trans (inv_strictAnti₀ hM'0 (by linarith)))

/-- **The `L²` norm near infinity through the inversion.** If `‖J(z, u z)‖ ≤ B`, the `L²` norm of a
compactly supported `C¹` covector field `g` on `|w| > r` is at most `(1 + B)²` times the `W^{1,2}`
energy of its pullback `g' = g (ζ⁻¹) ∘ (a + b J)` through the inversion on the disc `|ζ| ≤ r⁻¹`. -/
private theorem setIntegral_norm_sq_le_mul_setIntegral_sobolevDensity_covectorPullback_inv
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {r : ℝ}
    (hr : 0 < r) :
    ∫ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖}, ‖g z‖ ^ 2 ≤
      (1 + B) ^ 2 * ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r⁻¹},
        sobolevDensity (covectorPullback (realChart (·⁻¹))
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g) ζ := by
  set ι : ℝ × ℝ → ℝ × ℝ := realChart (·⁻¹)
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set N : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hNc : Continuous N := Complex.equivRealProdCLM.symm.continuous.norm
  set S := {ζ : ℝ × ℝ | Complex.equivRealProdCLM.symm ζ ≠ 0} ∩ {ζ | N ζ < r⁻¹}
  have hS : MeasurableSet S :=
    ((isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
      (isOpen_lt hNc continuous_const)).measurableSet
  -- The inversion maps `S` onto `|w| > r`.
  have hSimg : ι '' S = {z | r < N z} := by
    rw [TauCeti.Complex.realChart_inv_involutive.image_eq_preimage_symm]
    ext z
    simp only [S, mem_preimage, mem_inter_iff, mem_ofPred_eq, N,
      TauCeti.Complex.equivRealProdCLM_symm_realChart, ne_eq, inv_eq_zero, norm_inv]
    constructor
    · rintro ⟨hz0, hz⟩
      exact (inv_lt_inv₀ (norm_pos_iff.2 hz0) hr).1 hz
    · intro hz
      have hz0 : 0 < ‖Complex.equivRealProdCLM.symm z‖ := hr.trans hz
      exact ⟨norm_pos_iff.1 hz0, (inv_lt_inv₀ hz0 hr).2 hz⟩
  have hint := integrableOn_sobolevDensity_covectorPullback_inv hJ hu hg hgc r⁻¹
  rw [← hSimg, integral_image_eq_integral_of_eq_abs_det_smul hS
    TauCeti.Complex.realChart_inv_involutive.injective.injOn
    (fun ζ hζ ↦ (contDiffAt_realChart_inv hζ.1 (n := 1)).differentiableAt one_ne_zero)
    (f := fun ζ ↦ |(fderiv ℝ ι ζ).det| • ‖g (ι ζ)‖ ^ 2) fun _ _ ↦ rfl, ← integral_const_mul]
  have hSD : S ⊆ {ζ | N ζ ≤ r⁻¹} := fun ζ hζ ↦ show N ζ ≤ r⁻¹ from le_of_lt hζ.2
  calc ∫ ζ in S, |(fderiv ℝ ι ζ).det| • ‖g (ι ζ)‖ ^ 2
      ≤ ∫ ζ in S, (1 + B) ^ 2 * sobolevDensity (covectorPullback ι J' u g) ζ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ζ ↦ by positivity)
          ((hint.mono_set hSD).const_mul _) ((ae_restrict_iff' hS).2 (ae_of_all _ fun ζ hζ ↦ ?_))
        have hdet : 0 ≤ (fderiv ℝ ι ζ).det := by
          rw [TauCeti.Complex.det_fderiv_realChart_inv hζ.1]
          positivity
        simp only [smul_eq_mul, abs_of_nonneg hdet]
        have hdet' : 0 < (fderiv ℝ ι ζ).det := by
          rw [TauCeti.Complex.det_fderiv_realChart_inv hζ.1,
            TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
          have := norm_pos_iff.2 hζ.1
          positivity
        refine (det_mul_norm_sq_le_mul_norm_covectorPullback_realChart_sq (hasDerivAt_inv hζ.1)
          hdet' (hB _)).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
        rw [sobolevDensity_apply]
        nlinarith [sq_nonneg ‖fderiv ℝ (covectorPullback ι J' u g) ζ stdComplexLineReal‖,
          sq_nonneg ‖fderiv ℝ (covectorPullback ι J' u g) ζ stdComplexLineImag‖]
    _ ≤ ∫ ζ in {ζ | N ζ ≤ r⁻¹}, (1 + B) ^ 2 * sobolevDensity (covectorPullback ι J' u g) ζ :=
        setIntegral_mono_set (hint.const_mul _)
          (ae_of_all _ fun ζ ↦ mul_nonneg (sq_nonneg _) (sobolevDensity_nonneg _ ζ))
          (Eventually.of_forall hSD)

/-- **The weighted adjoint of a cut-off cokernel element.** Let `D_u^* η = 0`, `‖J(z, u z)‖ ≤ B`,
and `|w|⁴ ‖η(w)‖² ≤ S` on `|w| ≥ n`, with `1 ≤ n`. For a cutoff `χ` whose derivative vanishes on
`|w| < n`, `∫ (1 + |w|²)² ‖D_u^* (χ η)‖² ≤ 4 (1 + B)² S ∫ ‖dχ‖²`: the adjoint of `χ η` only involves
`dχ`, and `(1 + |w|²)² ≤ 4 |w|⁴` where `dχ` lives. -/
private theorem integral_mul_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) {n S : ℝ} (hn : 1 ≤ n) (hS0 : 0 ≤ S)
    (hS : ∀ z, n ≤ ‖Complex.equivRealProdCLM.symm z‖ →
      ‖Complex.equivRealProdCLM.symm z‖ ^ 4 * ‖η z‖ ^ 2 ≤ S)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχd : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < n → fderiv ℝ χ z = 0)
    (hχi : Integrable fun z ↦ ‖fderiv ℝ χ z‖ ^ 2) :
    ∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u (fun z ↦ χ z • η z) z‖ ^ 2 ≤
      4 * (1 + B) ^ 2 * S * ∫ z, ‖fderiv ℝ χ z‖ ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity) (hχi.const_mul _)
    (ae_of_all _ fun z ↦ ?_)
  dsimp only
  have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero (Ks := Ks) (Kt := Kt)
    (u := u) (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    ((hχ.differentiable one_ne_zero) z) ((hη.differentiable one_ne_zero) z)
    (((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero) (hD z)
  rcases lt_or_ge ‖Complex.equivRealProdCLM.symm z‖ n with hz | hz
  · -- Inside `|w| < n` the cutoff is locally constant.
    rw [hχd z hz, norm_zero, zero_mul, zero_mul] at hle
    rw [norm_le_zero_iff.1 hle, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · have hw : 1 + z.1 ^ 2 + z.2 ^ 2 = 1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2 := by
      rw [sq_norm_equivRealProdCLM_symm]
      ring
    have hN2 : 1 ≤ ‖Complex.equivRealProdCLM.symm z‖ ^ 2 := one_le_pow₀ (hn.trans hz)
    have h1 : (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2) ^ 2 ≤
        4 * ‖Complex.equivRealProdCLM.symm z‖ ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hN2)
        (by positivity : (0 : ℝ) ≤ 3 * ‖Complex.equivRealProdCLM.symm z‖ ^ 2 + 1)]
    have h2 := pow_le_pow_left₀ (norm_nonneg _)
      (hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add_right (hB z) 1) (norm_nonneg _)) (norm_nonneg _))) 2
    rw [hw]
    calc _ ≤ 4 * ‖Complex.equivRealProdCLM.symm z‖ ^ 4 *
          (‖fderiv ℝ χ z‖ * (1 + B) * ‖η z‖) ^ 2 :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = 4 * (1 + B) ^ 2 * ‖fderiv ℝ χ z‖ ^ 2 *
          (‖Complex.equivRealProdCLM.symm z‖ ^ 4 * ‖η z‖ ^ 2) := by ring
      _ ≤ 4 * (1 + B) ^ 2 * ‖fderiv ℝ χ z‖ ^ 2 * S :=
          mul_le_mul_of_nonneg_left (hS z hz) (by positivity)
      _ = 4 * (1 + B) ^ 2 * S * ‖fderiv ℝ χ z‖ ^ 2 := by ring

/-- **The `L²` norm of a cokernel element from a cut-off one.** Let `‖J(z, u z)‖ ≤ B`, and let
`D_u^*` satisfy the semi-Fredholm estimate on the sphere with constants `R > 0` and `C`. For a
square-integrable `C²` covector field `η` and a compactly supported `C²` cutoff `χ` equal to `1` on
`|w| ≤ n`, with `2 (R + 1) ≤ n`, the `L²` norm of `η` is at most
`max 1 (1 + B)² C (E + ∫_{‖z‖ ≤ R + 1} ‖η‖²) + ∫_{|w| ≥ n} ‖η‖²`, for the weighted adjoint term
`E = ∫ (1 + |w|²)² ‖D_u^* (χ η)‖²` of the estimate applied to `χ η`. Inside `|w| ≤ R` the field is
`χ η`; outside, change variables to the chart `ζ = w⁻¹`. -/
private theorem integral_norm_sq_le_of_cutoff (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B) {R C : ℝ} (hR : 0 < R)
    (hadj : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ R}, sobolevDensity η z) +
          ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ R⁻¹},
            sobolevDensity (covectorPullback (realChart (·⁻¹))
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in closedBall 0 (R + 1), ‖η z‖ ^ 2))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) {n : ℝ}
    (hn : 2 * (R + 1) ≤ n) (hχ1 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ n → χ z = 1) :
    ∫ z, ‖η z‖ ^ 2 ≤ max 1 ((1 + B) ^ 2) * C *
        ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
            (fun z ↦ χ z • η z) z‖ ^ 2) +
          ∫ z in closedBall 0 (R + 1), ‖η z‖ ^ 2) +
      ∫ z in {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖}, ‖η z‖ ^ 2 := by
  have hNc : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ :=
    Complex.equivRealProdCLM.symm.continuous.norm
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g := hχ.smul hη
  have hgc : HasCompactSupport g := hχc.smul_right
  have hgη (z : ℝ × ℝ) (hz : ‖Complex.equivRealProdCLM.symm z‖ ≤ n) : g z = η z := by
    simp [g, hχ1 z hz]
  have hest := hadj hg hgc
  -- The `L²` term of the estimate sees `η` itself.
  have hP : ∫ z in closedBall (0 : ℝ × ℝ) (R + 1), ‖g z‖ ^ 2 =
      ∫ z in closedBall (0 : ℝ × ℝ) (R + 1), ‖η z‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_closedBall fun z hz ↦ by
      have h1 := mem_closedBall_zero_iff.1 hz
      have h2 := norm_equivRealProdCLM_symm_le_two_mul z
      simp only [hgη z (by linarith)]
  rw [hP] at hest
  have hD₀ : MeasurableSet {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ R} :=
    measurableSet_le hNc.measurable measurable_const
  have hsplit := integral_add_compl hD₀ hηi
  rw [show {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ R}ᶜ =
    {z | R < ‖Complex.equivRealProdCLM.symm z‖} by ext z; simp] at hsplit
  have hDisc := Floer.setIntegral_norm_sq_le_setIntegral_sobolevDensity
    (isCompact_setOf_norm_equivRealProdCLM_symm_le R) hηi.integrableOn (hg.of_le one_le_two)
    fun z hz ↦ hgη z (le_trans hz (by linarith))
  have hEnd := setIntegral_norm_sq_le_setIntegral_add
    (S := {z : ℝ × ℝ | R < ‖Complex.equivRealProdCLM.symm z‖})
    (measurableSet_le measurable_const hNc.measurable) hηi
    (hg.continuous.integrable_norm_sq_of_hasCompactSupport hgc) fun z hz ↦ hgη z (not_le.1 hz).le
  have hCV := setIntegral_norm_sq_le_mul_setIntegral_sobolevDensity_covectorPullback_inv hJ hu hB
    (hg.of_le one_le_two) hgc hR
  have hX₁ := setIntegral_nonneg (μ := volume) hD₀ fun z _ ↦ sobolevDensity_nonneg g z
  have hX₂ := setIntegral_nonneg (μ := volume) (measurableSet_le hNc.measurable
    (measurable_const (a := R⁻¹))) fun ζ _ ↦ sobolevDensity_nonneg (covectorPullback
      (realChart (·⁻¹)) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g) ζ
  have hm1 : 1 ≤ max 1 ((1 + B) ^ 2) := le_max_left _ _
  have hmB : (1 + B) ^ 2 ≤ max 1 ((1 + B) ^ 2) := le_max_right _ _
  have hfin := mul_le_mul_of_nonneg_left hest (by linarith : (0 : ℝ) ≤ max 1 ((1 + B) ^ 2))
  nlinarith [mul_le_mul_of_nonneg_right hmB hX₂, mul_le_mul_of_nonneg_right hm1 hX₁]

/-- **The `L²` norm of a cokernel element lives on a square.** Let the data be `J₀` and the zero
perturbation on `‖z‖ ≥ T`, let `J` be `C¹` and `K_s`, `K_t` be `C²` along a `C¹` map `u`, with
`J(w, u w)` compatible. Then there are `R` and `A` such that every square-integrable `C²` covector
field `η` with `D_u^* η = 0` satisfies `∫ ‖η‖² ≤ A ∫_{‖z‖ ≤ R + 1} ‖η‖²`. The semi-Fredholm estimate
of `D_u^*` on the sphere is applied to the logarithmic cutoffs `χ_n η`, whose weighted adjoint is
at most a constant times `1 / log n` by the decay of `η` at infinity. -/
private theorem exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero
    (ω : SymplecticForm V) (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    ∃ R A, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in closedBall 0 (R + 1), ‖η z‖ ^ 2 := by
  obtain ⟨R, C, hR, hC, hadj⟩ :=
  exists_forall_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add_of_eq_base
      hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  obtain ⟨B, hB⟩ :=
    exists_forall_norm_le_of_eq_base hJ₀ (fun z ↦ (hJ z).continuousAt) hu.continuous
  have h₀ : ω.Compatible J₀ := compatible_of_eq_base hJ₀ hc
  set m := max 1 ((1 + B) ^ 2)
  refine ⟨R, m * C, fun η hη hD hηi ↦ ?_⟩
  obtain ⟨r₁, S, hS0, hS⟩ := exists_mul_norm_sq_le_of_floerLinearizationAdjoint_eq_zero ω hJ₀
    hKs₀ hKt₀ h₀.invariant (hη.of_le one_le_two) hD hηi
  set P := ∫ z in closedBall (0 : ℝ × ℝ) (R + 1), ‖η z‖ ^ 2
  set K := 4 * (1 + B) ^ 2 * S * (8 * π * logCutoffConst ^ 2)
  -- The error terms of the cutoffs at scale `n` tend to zero: the tail of `‖η‖²`, and `K / log n`.
  have hlim : Tendsto (fun n : ℕ ↦ m * C * (K / Real.log n + P) +
      ∫ z in {z : ℝ × ℝ | (n : ℝ) ≤ ‖Complex.equivRealProdCLM.symm z‖}, ‖η z‖ ^ 2) atTop
      (𝓝 (m * C * P)) := by
    have hlog : Tendsto (fun n : ℕ ↦ K / Real.log n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop.const_mul K
    have := ((hlog.add_const P).const_mul (m * C)).add
      ((tendsto_setIntegral_setOf_le hηi
        Complex.equivRealProdCLM.symm.continuous.norm.measurable).comp tendsto_natCast_atTop_atTop)
    rwa [zero_add, add_zero] at this
  refine ge_of_tendsto hlim ?_
  -- The scale `n` of the cutoff: beyond the decay radius, the square `‖z‖ ≤ R + 1` and `4`.
  filter_upwards [eventually_ge_atTop ⌈max (max r₁ 4) (2 * (R + 1))⌉₊] with n hn
  have hn' : max (max r₁ 4) (2 * (R + 1)) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn4 : (4 : ℝ) ≤ n := (le_max_right r₁ 4).trans ((le_max_left _ _).trans hn')
  have hnr : r₁ ≤ n := (le_max_left r₁ 4).trans ((le_max_left _ _).trans hn')
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨χ, hχs, -, hχ1, hχ0, hχd0, hχi, hχE⟩ :=
    TauCeti.Complex.exists_contDiff_logCutoff hn0 (show 4 * (n : ℝ) ≤ n ^ 2 by nlinarith)
  rw [show (n : ℝ) ^ 2 / n = n by field_simp] at hχE
  have hE := integral_mul_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu hB
    (hη.of_le one_le_two) hD (by linarith : (1 : ℝ) ≤ n) hS0
    (fun z hz ↦ hS z (hnr.trans hz)) (hχs.of_le (by simp)) hχd0 hχi
  have hcut := integral_norm_sq_le_of_cutoff ω hJ hu hB hR hadj hη hηi (hχs.of_le (by simp))
    (HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le ((n : ℝ) ^ 2))
      fun z hz ↦ hχ0 z (not_le.1 hz).le) ((le_max_right _ _).trans hn') hχ1
  have hKE : 4 * (1 + B) ^ 2 * S * ∫ z, ‖fderiv ℝ χ z‖ ^ 2 ≤ K / Real.log n :=
    (mul_le_mul_of_nonneg_left hχE (by positivity)).trans_eq (by simp only [K]; ring)
  refine hcut.trans (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left
    (hE.trans hKE) P) (mul_nonneg (by positivity) hC)) _)

/-- **The cokernel of the linearized operator on the sphere is finite-dimensional.** Let the Floer
data `J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C³`
and `K_s`, `K_t` be `C⁴` along a `C³` map `u`, with `J(w, u w)` compatible. Then the orthogonal
complement of the range of the realization of `D_u` from `W^{1,2}` of the sphere to `L²` is
finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hKs2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Ks) (z, u z) := (hKs z).of_le (by norm_num)
  have hKt2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Kt) (z, u z) := (hKt z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  obtain ⟨R, A, hglob⟩ := exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero ω hJ₀
    hKs₀ hKt₀ hJ1 hKs2 hKt2 hu1 hc
  exact finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_le ω
    isWeight_sphereWeight hJ hKs hKt hu hc
    (ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z hz y ↦ by rw [hJ₀ z hz y]) hKs₀ hKt₀ hJ1 hKs2 hKt2 hu1)
    (isCompact_closedBall 0 (R + 1)) hglob

/-- **The linearized operator on the sphere is Fredholm.** Let the Floer data `J`, `K_s`, `K_t` on
the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero perturbation on `‖w‖ ≥ T`, a
neighbourhood of the point at infinity of the sphere. Let `J` be `C³` and `K_s`, `K_t` be `C⁴` along
a `C³` map `u`, with `J(w, u w)` compatible. Then the realization of `D_u` from `W^{1,2}` of the
sphere to `L²` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hKs2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Ks) (z, u z) := (hKs z).of_le (by norm_num)
  have hKt2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Kt) (z, u z) := (hKt z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hcl := isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base ω hJ₀ hKs₀
    hKt₀ hJ1 hKs2 hKt2 hu1 hc
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range] at hcl
  exact ContinuousLinearMap.isFredholm_of_isClosed_range_of_finiteDimensional_orthogonal
    (finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base ω hJ₀ hKs₀
      hKt₀ hJ1 hKs2 hKt2 hu1 hc) hcl
    (finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
      ω hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc)

end SymplecticForm

end TauCeti
