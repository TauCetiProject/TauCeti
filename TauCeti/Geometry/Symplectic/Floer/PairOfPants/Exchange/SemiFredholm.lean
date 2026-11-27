/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart.Output
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.Topology.Algebra.Support

/-!
# The semi-Fredholm estimate along the input-exchange family

Graded commutativity of the pair-of-pants product counts the members of the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, on the pair of pants
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic vector space `(V, ω)`. Each member is the
pair-of-pants datum far out on the two input ends, but on the output end it is the pair-of-pants
datum translated by `c`: it is `H_∞(t) dt` in the end chart `c + φ'_∞` recentred at `c`, not in the
standard end chart `φ'_∞`. So the semi-Fredholm estimate of the linearized Floer operator for data
which are the pair-of-pants datum far out on every end does not apply to it as it stands. This file
proves the same estimate for data with a recentred output end, and in particular along the whole
input-exchange family: the `W^{1,2}` energy of a section, measured in the standard end charts and
on a truncation `S_T`, is controlled by the `L²` norms of `D_u ξ` on `S` and of `ξ` on `S_{T + 1}`.

* **Translating the output end.** The linearized operator commutes with translations of the domain
  (`TauCeti.SymplecticForm.floerLinearization_comp_add_right`). Far out on the output end, the
  translates by `c` of the data `(J, K_s, K_t)` and of `u` are the pair-of-pants datum and a
  solution of its Floer equation, so the end estimate of the pair of pants,
  `exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization` in the
  namespace `TauCeti.SymplecticForm`, applies to them. That estimate asks for data regular on all
  of `S`, which the translates are not near the translated input punctures, so `J` and `u` are
  composed instead with the diffeomorphism `TauCeti.Floer.exchangeMap` of `S`, which preserves `S`
  and is the translation by `c` far out on the output end.
* **Comparing the end charts.** The estimate for the translate controls the `W^{1,2}` energy of
  `ξ` in the recentred chart `c + φ'_∞`. Changing variables along the two holomorphic charts, both
  energies agree up to constants with the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` for the
  cylindrical weight `ρ` (`TauCeti.Floer.lintegral_comp_positiveEndChart_le`,
  `TauCeti.Floer.lintegral_image_positiveEndChart_le`), and the weight changes by at most a factor
  `8` under the translation far out (`TauCeti.Floer.cylindricalWeight_add_le`). So the energy in
  the standard chart is at most `320π²` times that of the translate
  (`TauCeti.Floer.setIntegral_sobolevDensity_comp_positiveEndChart_inf_le`).
* **Patching.** With the end estimates of the pair of pants on the input ends, the patching
  argument of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`,
  `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends`,
  gives the semi-Fredholm estimate.

## Main results

* `TauCeti.Floer.setIntegral_sobolevDensity_comp_positiveEndChart_inf_le`: the `W^{1,2}` energy of
  a section far out on the output end, in the standard end chart, is at most `320π²` times that of
  its translate by `c ∈ [0, 1]`.

In the namespace `TauCeti.SymplecticForm`:

* the end estimate on an output end recentred at `c`:
  `exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_recentered`
* `exists_forall_le_mul_integral_floerLinearization_add_of_recentered`: the semi-Fredholm estimate
  for data which far out are the pair-of-pants datum on the input ends and its translate by `c` on
  the output end;
* `exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add`: the semi-Fredholm
  estimate along every member of the input-exchange family.

The Sobolev realization of the operator, the finiteness of its cokernel and its index are not
treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and its graded
  commutativity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology ENNReal NNReal Manifold

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {c : ℝ}

/-- If the support of `ξ` lies at distance at least `r` from `0`, then the support of its translate
`w ↦ ξ (w + c)` by `c ∈ [0, 1]` lies at distance at least `r - 1`. -/
private theorem sub_one_le_norm_of_mem_tsupport_comp_add (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {α : Type*} [Zero α] {ξ : ℝ × ℝ → α} {r : ℝ}
    (hξR : ∀ z ∈ tsupport ξ, r ≤ ‖Complex.equivRealProdCLM.symm z‖)
    {v : ℝ × ℝ} (hv : v ∈ tsupport fun z ↦ ξ (z + (c, 0))) :
    r - 1 ≤ ‖Complex.equivRealProdCLM.symm v‖ := by
  have h := hξR _ ((tsupport_comp_add_right ξ _).subset hv)
  rw [TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero] at h
  have := norm_add_le (Complex.equivRealProdCLM.symm v) (c : ℂ)
  rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at this
  linarith

/-- Beyond the height `1`, a map composed with `Φ_c` and read in the positive end chart `φ'_∞` is
the map read in the end chart `c + φ'_∞` recentred at `c`, near every point. -/
private theorem comp_exchangeMap_comp_positiveEndChart_eventuallyEq {α : Type*}
    (u : ℝ × ℝ → α) {ζ : ℝ × ℝ} (hζ : 1 < ζ.1) :
    (u ∘ exchangeMap c) ∘ positiveEndChart inf =ᶠ[𝓝 ζ]
      fun ζ' ↦ u (positiveEndChart inf ζ' + (c, 0)) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ] with ζ' hζ'
  rw [comp_apply, comp_apply, (exchangeMap_eventuallyEq_add_of_one_lt (by
    rwa [fst_positiveEndCoord_positiveEndChart])).eq_of_nhds]

/-- The `W^{1,2}` energy of a `C¹` section with compact support in `S` over the band
`(0, ∞) × [0, 1]` of a positive end chart, as a lower integral over `(0, ∞) × [0, 1)`. -/
private theorem ofReal_setIntegral_sobolevDensity_comp_positiveEndChart (q : Puncture)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ENNReal.ofReal (∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) =
      ∫⁻ ζ in Ioi 0 ×ˢ Ico (0 : ℝ) 1,
        ENNReal.ofReal (‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (0, 1)‖ ^ 2 + ‖ξ (positiveEndChart q ζ)‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_sobolevDensity_comp_positiveEndChart hξ hξc hξS q 0)
    (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)]
  have hae : Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1 =ᵐ[volume] Ioi (0 : ℝ) ×ˢ Icc (0 : ℝ) 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEqSet.rfl Ico_ae_eq_Icc
  rw [setLIntegral_congr hae]
  simp_rw [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq, comp_apply]

/-- **The weighted energy under a horizontal translation.** For a `C¹` section `ξ` with support at
distance at least `5` from `0` and `0 ≤ c ≤ 1`, the weighted energy
`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` is at most `8` times that of its translate
`w ↦ ξ (w + c)` over the image of the band `(0, ∞) × [0, 1)` under `φ'_∞`, which contains the
support of the translate. -/
private theorem lintegral_le_mul_setLIntegral_image_positiveEndChart_inf_add (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {ξ : ℝ × ℝ → V}
    (hξR : ∀ z ∈ tsupport ξ, 5 ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    ∫⁻ w, ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      8 * ∫⁻ w in positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight w * ‖ξ (w + (c, 0))‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ ξ (z + (c, 0))) w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ ξ (z + (c, 0))) w (0, 1)‖ ^ 2) := by
  set a : ℝ × ℝ := (c, 0)
  -- The weighted density `ρ ‖η‖² + ‖∂s η‖² + ‖∂t η‖²`, which vanishes off the support of `η`.
  set W : (ℝ × ℝ → V) → ℝ × ℝ → ℝ≥0∞ := fun η w ↦ ENNReal.ofReal (cylindricalWeight w *
    ‖η w‖ ^ 2 + ‖fderiv ℝ η w (1, 0)‖ ^ 2 + ‖fderiv ℝ η w (0, 1)‖ ^ 2)
  have hW0 {η : ℝ × ℝ → V} {w : ℝ × ℝ} (hw : w ∉ tsupport η) : W η w = 0 := by
    have hd : fderiv ℝ η w = 0 :=
      Function.notMem_support.1 fun h ↦ hw (support_fderiv_subset ℝ h)
    simp [W, image_eq_zero_of_notMem_tsupport hw, hd]
  have hR (v : ℝ × ℝ) (hv : v ∈ tsupport fun z ↦ ξ (z + a)) :
      4 ≤ ‖Complex.equivRealProdCLM.symm v‖ := by
    linarith [sub_one_le_norm_of_mem_tsupport_comp_add hc₀ hc₁ hξR hv]
  -- Translating by `a` costs a factor `8` in the weight, and nothing in the derivatives.
  have htr (v : ℝ × ℝ) : W ξ (v + a) ≤ 8 * W (fun z ↦ ξ (z + a)) v := by
    by_cases hv : v ∈ tsupport fun z ↦ ξ (z + a)
    · have hρ := cylindricalWeight_add_le hc₀ hc₁ (hR v hv)
      simp only [W, fderiv_comp_add_right]
      rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := cylindricalWeight_nonneg v
      nlinarith [mul_le_mul_of_nonneg_right hρ (sq_nonneg ‖ξ (v + a)‖),
        sq_nonneg ‖fderiv ℝ ξ (v + a) (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ (v + a) (0, 1)‖]
    · rw [hW0 (by rwa [tsupport_comp_add_right] at hv)]
      exact bot_le
  have hsupp : Function.support (W fun z ↦ ξ (z + a)) ⊆
      positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1) :=
    fun v hv ↦ mem_image_positiveEndChart_inf_of_two_lt_norm
      (by linarith [hR v (by_contra fun h ↦ hv (hW0 h))])
  calc ∫⁻ w, W ξ w = ∫⁻ v, W ξ (v + a) := (lintegral_add_right_eq_self (W ξ) a).symm
    _ ≤ ∫⁻ v, 8 * W (fun z ↦ ξ (z + a)) v := lintegral_mono htr
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, setLIntegral_eq_of_support_subset hsupp]

/-- **The `W^{1,2}` energy on the output end under a horizontal translation.** Let `ξ` be a `C¹`
section with compact support at distance at least `5` from `0`, and `0 ≤ c ≤ 1`. Then the
`W^{1,2}` energy of `ξ` read in the positive end chart `φ'_∞` of the output end, over the band
`(0, ∞) × [0, 1]`, is at most `320π²` times that of its translate `w ↦ ξ (w + c)`. Equivalently,
measured in the end chart `c + φ'_∞` recentred at `c`, the energy of `ξ` controls its energy in the
standard end chart. -/
theorem setIntegral_sobolevDensity_comp_positiveEndChart_inf_le (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξR : ∀ z ∈ tsupport ξ, 5 ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ ≤
      320 * π ^ 2 * ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ ξ (z + (c, 0))) ∘ positiveEndChart inf) ζ := by
  set ξ' : ℝ × ℝ → V := fun z ↦ ξ (z + (c, 0))
  have hξ' : ContDiff ℝ 1 ξ' := hξ.comp (contDiff_id.add contDiff_const)
  have hξ'S : tsupport ξ' ⊆ thricePuncturedSphereReal := fun v hv ↦
    mem_thricePuncturedSphereReal_of_two_le_norm
      (by linarith [sub_one_le_norm_of_mem_tsupport_comp_add hc₀ hc₁ hξR hv])
  have h320 : (2 : ℝ≥0∞) * (8 * ENNReal.ofReal (20 * π ^ 2)) = ENNReal.ofReal (320 * π ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (setIntegral_nonneg
      (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦ sobolevDensity_nonneg _ ζ)),
    ofReal_setIntegral_sobolevDensity_comp_positiveEndChart inf hξ hξc fun z hz ↦
      mem_thricePuncturedSphereReal_of_two_le_norm (by linarith [hξR z hz]),
    ENNReal.ofReal_mul (by positivity),
    ofReal_setIntegral_sobolevDensity_comp_positiveEndChart inf hξ'
      (hξc.comp_homeomorph (Homeomorph.addRight (c, 0))) hξ'S]
  calc _ ≤ 2 * ∫⁻ w in positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1),
          ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
            ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) :=
        lintegral_comp_positiveEndChart_le inf measurableSet_Ioi (fun s hs ↦ le_of_lt hs)
          fun ζ _ ↦ (hξ.differentiable one_ne_zero) _
    _ ≤ 2 * (8 * ∫⁻ w in positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1),
          ENNReal.ofReal (cylindricalWeight w * ‖ξ' w‖ ^ 2 + ‖fderiv ℝ ξ' w (1, 0)‖ ^ 2 +
            ‖fderiv ℝ ξ' w (0, 1)‖ ^ 2)) := by
        gcongr
        exact (setLIntegral_le_lintegral _ _).trans
          (lintegral_le_mul_setLIntegral_image_positiveEndChart_inf_add hc₀ hc₁ hξR)
    _ ≤ 2 * (8 * (ENNReal.ofReal (20 * π ^ 2) * ∫⁻ ζ in Ioi 0 ×ˢ Ico (0 : ℝ) 1,
          ENNReal.ofReal (‖fderiv ℝ (ξ' ∘ positiveEndChart inf) ζ (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (ξ' ∘ positiveEndChart inf) ζ (0, 1)‖ ^ 2 +
              ‖ξ' (positiveEndChart inf ζ)‖ ^ 2))) := by
        gcongr
        exact lintegral_image_positiveEndChart_le inf measurableSet_Ioi (fun s hs ↦ le_of_lt hs)
          fun ζ _ ↦ (hξ'.differentiable one_ne_zero) _
    _ = _ := by
        rw [← h320]
        ring

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {c : ℝ}

/-- The end estimate of the pair of pants for the data `(J ∘ Φ_c, K, u ∘ Φ_c)`, with `K` the
pair-of-pants perturbation and `Φ_c = TauCeti.Floer.exchangeMap c`, where `(J, K_s, K_t)` and `u`
are as in the end estimate on an output end recentred at `c` below. These data are regular on all
of `S`, and far out on the output end they are the translates by `c` of `(J, K_s, K_t)` and of
`u`. -/
private theorem exists_forall_setIntegral_comp_positiveEndChart_le_comp_exchangeMap
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H inf)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H inf) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord inf z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ ≤
        C * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J (exchangeMap c w) y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u ∘ exchangeMap c) ξ z‖ ^ 2 := by
  have hΦS {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) :
      exchangeMap c z ∈ thricePuncturedSphereReal :=
    (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ z).2 hz
  have hΦc : ContDiff ℝ 1 (exchangeMap c) := (contDiff_exchangeMap c).of_le one_le_two
  -- Beyond `R₂` on the output end, `Φ_c` is the translation by `c` and the hypotheses apply.
  set R₂ := max R₁ 2
  have hR₂ {z : ℝ × ℝ} (hz : R₂ ≤ (positiveEndCoord inf z).1) :
      R₁ ≤ (positiveEndCoord inf z).1 ∧ 1 < (positiveEndCoord inf z).1 :=
    ⟨(le_max_left _ _).trans hz, by linarith [le_max_right R₁ 2]⟩
  have hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J (exchangeMap c p.1) p.2).toLinearMap.toContinuousLinearMap)
        (z, (u ∘ exchangeMap c) z) := fun z hz ↦
    (hJ (exchangeMap c z) (hΦS hz)).comp (f := fun p : (ℝ × ℝ) × V ↦ (exchangeMap c p.1, p.2))
      (z, (u ∘ exchangeMap c) z) ((hΦc.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  have hJeq' (ζ : ℝ × ℝ) (hζ : R₂ ≤ ζ.1) : J (exchangeMap c (positiveEndChart inf ζ)) = Je ζ.2 := by
    rw [(exchangeMap_eventuallyEq_add_of_one_lt (hR₂ (by
      rwa [fst_positiveEndCoord_positiveEndChart])).2).eq_of_nhds]
    exact hJeq ζ ((le_max_left _ _).trans hζ)
  have hF' : ∀ z ∈ thricePuncturedSphereReal, R₂ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (exchangeMap c z) ((u ∘ exchangeMap c) z))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u ∘ exchangeMap c) z : ℝ × ℝ →ₗ[ℝ] V) := fun z _ hz ↦ by
    obtain ⟨hz₁, hz₂⟩ := hR₂ hz
    have hΦz := exchangeMap_eventuallyEq_add_of_one_lt (c := c) hz₂
    obtain ⟨hKs, hKt⟩ := hK z hz₁
    have hu₁ : u ∘ exchangeMap c =ᶠ[𝓝 z] fun w ↦ u (w + (c, 0)) := hΦz.fun_comp u
    rw [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ hu₁,
      ω.perturbedFDeriv_congr (Ks' := fun w ↦ Ks (w + (c, 0))) (Kt' := fun w ↦ Kt (w + (c, 0))) _
        hKs.symm hKt.symm, ω.perturbedFDeriv_comp_add_right, comp_apply, hΦz.eq_of_nhds]
    exact hF z hz₁
  -- The end loops and slice defects of `u ∘ Φ_c` are eventually those of `u` in the recentred
  -- chart.
  have hux' : TendstoUniformlyOn (fun s t ↦ (u ∘ exchangeMap c) (positiveEndChart inf (s, t))) x
      atTop (Icc 0 1) :=
    hux.congr (eventually_gt_atTop 1 |>.mono fun s hs t _ ↦
      ((comp_exchangeMap_comp_positiveEndChart_eventuallyEq (c := c) u (ζ := (s, t))
        hs).eq_of_nhds).symm)
  have hδ' : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        ((u ∘ exchangeMap c) ∘ positiveEndChart inf) (s, t)) 0 atTop (Icc 0 1) :=
    hδ.congr (eventually_gt_atTop 1 |>.mono fun s hs t _ ↦ by
      have h := comp_exchangeMap_comp_positiveEndChart_eventuallyEq (c := c) u (ζ := (s, t)) hs
      simp only [sliceDefect_def, h.fderiv_eq, h.eq_of_nhds])
  exact ω.exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization hH hHs
    inf hX hx hnd hJe hJex hJeq' (fun _ _ _ ↦ ⟨rfl, rfl⟩) hJ'
    (fun z hz ↦ (hu (exchangeMap c z) (hΦS hz)).comp z hΦc.contDiffAt) hF' hux' hδ'

/-- Far out on the output end, the linearized operator of the data `(J ∘ Φ_c, K, u ∘ Φ_c)` of
`exists_forall_setIntegral_comp_positiveEndChart_le_comp_exchangeMap` on the translate
`w ↦ ξ (w + c)` is the translate of the linearized operator of `(J, K_s, K_t, u)` on `ξ`, so the
two have the same `L²` norm. -/
private theorem integral_norm_floerLinearization_comp_exchangeMap_sq (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (u : ℝ × ℝ → V) {ξ : ℝ × ℝ → V}
    (hξR : ∀ v ∈ tsupport fun z ↦ ξ (z + (c, 0)),
      R₁ ≤ (positiveEndCoord inf v).1 ∧ 1 < (positiveEndCoord inf v).1) :
    ∫ z, ‖ω.floerLinearization
        (fun w y ↦ (J (exchangeMap c w) y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ exchangeMap c) (fun z ↦ ξ (z + (c, 0))) z‖ ^ 2 =
      ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        Ks Kt u ξ z‖ ^ 2 := by
  have hD (z : ℝ × ℝ) : ω.floerLinearization
      (fun w y ↦ (J (exchangeMap c w) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u ∘ exchangeMap c)
      (fun z ↦ ξ (z + (c, 0))) z = ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ (z + (c, 0)) := by
    by_cases hz : z ∈ tsupport fun z ↦ ξ (z + (c, 0))
    · obtain ⟨hz₁, hz₂⟩ := hξR z hz
      have hΦz := exchangeMap_eventuallyEq_add_of_one_lt (c := c) hz₂
      have hu₁ : u ∘ exchangeMap c =ᶠ[𝓝 z] fun w ↦ u (w + (c, 0)) := hΦz.fun_comp u
      obtain ⟨hKs, hKt⟩ := hK z hz₁
      rw [← ω.floerLinearization_comp_add_right]
      simp only [floerLinearization_def, hu₁.fderiv_eq, hu₁.eq_of_nhds, hΦz.eq_of_nhds, hKs, hKt]
    · rw [ω.floerLinearization_of_notMem_tsupport _ _ _ _ hz,
        ω.floerLinearization_of_notMem_tsupport _ _ _ _ (by rwa [tsupport_comp_add_right] at hz)]
  simp_rw [hD]
  exact integral_add_right_eq_self (fun z ↦ ‖ω.floerLinearization
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) (c, 0)

/-- **The end estimate on an output end recentred at `c`.** Let `H` be jointly `C²` period-one
Hamiltonians, and let `(J, K_s, K_t)` be Floer data on `S = ℂ ∖ {0, 1}` whose perturbation, far out
on the output end, is the pair-of-pants perturbation of `H` translated by `c ∈ [0, 1]`, and whose
almost complex structure is there a `C¹` family `J_∞(t)`, compatible along `x`, in the recentred
end chart `c + φ'_∞`. Let `u` be a `C¹` map on `S`, along which `J` is `C¹`, that solves the Floer
equation for these data far out on the output end, and whose output end, read in the recentred end
chart, converges uniformly to an orbit `x` of the positive end Hamiltonian `H'_∞` starting at a
nondegenerate fixed point of the time-one map, while the slice defect tends uniformly to zero. Then
there are `C` and `R` such that every `C²` section `ξ` with compact support in the part `-s > R` of
the output end satisfies

`∫_{(0, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`, with the energy measured in the
standard positive end chart `φ'_∞`. The members of the input-exchange family
`TauCeti.Floer.exchangePerturbation` are such data. -/
theorem
    exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H inf)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H inf) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord inf z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2 := by
  obtain ⟨C₀, R₀, hest⟩ := exists_forall_setIntegral_comp_positiveEndChart_le_comp_exchangeMap ω
    hH hHs hc₀ hc₁ hX hx hnd hJe hJex hJeq hK hJ hu hF hux hδ
  -- Sections supported beyond `R₃ + 1` have translates supported beyond `R₃`.
  set R₃ := max R₀ (max R₁ 2)
  have hR₃ : 2 ≤ R₃ := (le_max_right R₁ 2).trans (le_max_right _ _)
  refine ⟨320 * π ^ 2 * C₀, R₃ + 1, fun ξ hξ hξc hξR ↦ ?_⟩
  have hexp : 14 * Real.exp (2 * π * R₃) ≤ 2 * Real.exp (2 * π * (R₃ + 1)) := by
    rw [mul_add, mul_one, Real.exp_add]
    nlinarith [fourteen_le_two_mul_exp_two_pi, Real.exp_pos (2 * π * R₃)]
  have hexp₁ : 1 ≤ Real.exp (2 * π * R₃) := Real.one_le_exp (by positivity)
  have hnorm (z : ℝ × ℝ) (hz : z ∈ tsupport ξ) :
      2 * Real.exp (2 * π * (R₃ + 1)) < ‖Complex.equivRealProdCLM.symm z‖ := by
    obtain ⟨hzS, hzR⟩ := hξR hz
    exact (lt_fst_positiveEndCoord_inf_iff (mem_thricePuncturedSphereReal_iff.1 hzS).1).1 hzR
  have hfar (v : ℝ × ℝ) (hv : v ∈ tsupport fun z ↦ ξ (z + (c, 0))) :
      v ∈ thricePuncturedSphereReal ∧ R₃ < (positiveEndCoord inf v).1 := by
    have hv' : 2 * Real.exp (2 * π * R₃) < ‖Complex.equivRealProdCLM.symm v‖ := by
      linarith [sub_one_le_norm_of_mem_tsupport_comp_add hc₀ hc₁ (fun z hz ↦ (hnorm z hz).le) hv]
    exact ⟨mem_thricePuncturedSphereReal_of_two_le_norm (by linarith),
      (lt_fst_positiveEndCoord_inf_iff (norm_pos_iff.1 (by linarith))).2 hv'⟩
  have hest' := hest (ξ := fun z ↦ ξ (z + (c, 0))) (hξ.comp (contDiff_id.add contDiff_const))
    (hξc.comp_homeomorph (Homeomorph.addRight (c, 0))) fun v hv ↦
      ⟨(hfar v hv).1, (le_max_left _ _).trans_lt (hfar v hv).2⟩
  rw [integral_norm_floerLinearization_comp_exchangeMap_sq ω hK u fun v hv ↦
    ⟨((le_max_left R₁ 2).trans (le_max_right R₀ _)).trans (hfar v hv).2.le,
      by linarith [(hfar v hv).2]⟩] at hest'
  -- The energy in the standard end chart is controlled by that of the translate.
  refine (Floer.setIntegral_sobolevDensity_comp_positiveEndChart_inf_le hc₀ hc₁
    (hξ.of_le one_le_two) hξc fun z hz ↦ by linarith [hnorm z hz]).trans ?_
  have h := mul_le_mul_of_nonneg_left hest' (show (0 : ℝ) ≤ 320 * π ^ 2 by positivity)
  rwa [← mul_assoc] at h

/-- **The semi-Fredholm estimate for data with a recentred output end.** Let `H_q` be jointly `C²`
period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, whose positive end Hamiltonians
`H'_q` have globally Lipschitz suspended vector fields, and let `x_q` be orbits of `H'_q` starting
at nondegenerate fixed points of the time-one maps. Let `(J, K_s, K_t)` be Floer data on `S`, with
`J` `C¹` and `K_s`, `K_t` `C²` along `u`, which far out on each end, beyond a height `R₁`, are
cylindrical: on the input ends `q = 0, 1` they are `J_q(t)` and the pair-of-pants perturbation of
`H` in the positive end charts `φ'_q`, and on the output end they are `J_∞(t)` and the pair-of-pants
perturbation translated by `c ∈ [0, 1]`, in the recentred end chart `c + φ'_∞`. Let `u` be a `C¹`
map on `S`, along which `J` is compatible, that solves the Floer equation beyond `R₁` on each end,
and whose ends, read in these end charts, converge uniformly to the orbits `x_q` while the slice
defects tend uniformly to zero. Then there are `C ≥ 0` and `T ≥ 0` such that every `C²` section `ξ`
with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`, with the energy measured in
the standard positive end charts `φ'_q`. For `c = 0` these are the data of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`; the
members of the input-exchange family are such data for every `c ∈ [0, 1]`
(`exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add`). -/
theorem exists_forall_le_mul_integral_floerLinearization_add_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  -- The end estimates: on the input ends that of the pair of pants, on the output end that of
  -- the recentred end.
  have hinf :=
    exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_recentered
      ω hH hHs hc₀ hc₁ (hX inf) (hx inf) (hnd inf) (hJe inf) (hJex inf) hJeq_inf hK_inf hJ hu
      hF_inf hux_inf hδ_inf
  have hend (q : Puncture) : ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2 := by
    by_cases hq : q = inf
    · subst hq
      exact hinf
    · exact ω.exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization
        hH hHs q (hX q) (hx q) (hnd q) (hJe q) (hJex q) (hJeq q hq) (hK q hq) hJ hu (hF q hq)
        (hux q hq) (hδ q hq)
  choose C R hest using hend
  exact exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_ends
    ω hJ hKs hKt hu hc hest

/-- **The semi-Fredholm estimate along the input-exchange family.** Let `H_q` be jointly `C²`
period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, whose positive end Hamiltonians
`H'_q` have globally Lipschitz suspended vector fields, and let `x_q` be orbits of `H'_q` starting
at nondegenerate fixed points of the time-one maps. Let `K_c` be the member `c ∈ [0, 1]` of the
input-exchange family `TauCeti.Floer.exchangePerturbation H c`, with components `K_s`, `K_t`, and
let `J` be almost complex structures on `S` that far out on each end, beyond a height `R₁`, are
`C¹` families `J_q(t)` compatible along `x_q`: in the positive end charts `φ'_q` on the input ends
and in the recentred end chart `c + φ'_∞` on the output end, where `K_c` is `H_∞(t) dt`. Let `u`
be a `C¹` map on `S`, along which `J` is `C¹` and compatible, that solves the Floer equation for
`(J, K_c)` beyond `R₁` on each end, and whose ends, read in these end charts, converge uniformly to
the orbits `x_q` while the slice defects tend uniformly to zero. Then there are `C ≥ 0` and
`T ≥ 0` such that every `C²` section `ξ` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the data `(J, K_c)`. -/
theorem exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  -- Beyond the height `max R₁ 2`, `K_c` is the pair-of-pants datum on the input ends and its
  -- translate by `c` on the output end.
  set R₂ := max R₁ 2
  have hR₁ : R₁ ≤ R₂ := le_max_left _ _
  have h1 {r : ℝ} (hr : R₂ ≤ r) : 1 < r := by linarith [le_max_right R₁ 2]
  exact ω.exists_forall_le_mul_integral_floerLinearization_add_of_recentered hH hHs hc₀ hc₁ hX hx
    hnd hJe hJex (fun q hq ζ hζ ↦ hJeq q hq ζ (hR₁.trans hζ))
    (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ))
    (fun _ hq _ _ hz ↦
      exchangePerturbation_components_eq_of_pos_fst_positiveEndCoord hc₀ hc₁ hq
        (zero_lt_one.trans (h1 hz)))
    (fun _ hz ↦ exchangePerturbation_add_components_eq_of_one_lt_fst_positiveEndCoord hc₀ hc₁
      (h1 hz)) hJ
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) Complex.I) hu hc
    (fun q hq z hz hzR ↦ hF q hq z hz (hR₁.trans hzR)) (fun z hz ↦ hF_inf z (hR₁.trans hz)) hux
    hux_inf hδ hδ_inf

end SymplecticForm

end TauCeti
