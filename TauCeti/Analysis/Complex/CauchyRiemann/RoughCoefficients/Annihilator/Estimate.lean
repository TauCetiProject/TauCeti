/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator.Basic
public import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Analysis.Sobolev.Wkp.ClosedGraph
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# The interior estimate for annihilators of real Cauchy–Riemann operators

Let `Ω ⊆ ℂ` be open, `V` a finite-dimensional real normed space, `k ∈ ℕ`, `J` a `C^{k+1}` field
of complex structures on `V` and `S` a `C^k` field of endomorphisms over `Ω`, and `1 < q < ∞`. An
`L^q` covector field `η` on `Ω` annihilating `∂_s φ + J ∂_t φ + S φ` for every test function `φ` is
`W^{k+1,q}` on every open `W` with compact closure in `Ω`
(`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`). This file proves the
corresponding estimate: there is a constant `C`, depending on `W` but not on `η`, such that for
every `v ∈ V` the function `η(·) v` is represented in `W^{k+1,q}(W)` with norm at most
`C ‖v‖ ‖η‖_{L^q(Ω)}` (`TauCeti.exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero`).

In a basis `b` of `V`, the tuples `(η(b c))_c` of components of weak solutions form a closed
subspace of `ι → L^q(Ω)`, cut out by the continuous functionals `θ ↦ ∑_c ∫_Ω θ_c (D φ)_c`, and the
regularity theorem represents each component in `W^{k+1,q}(W)`. The closed graph estimate
`TauCeti.Wkp.exists_norm_le_of_forall_exists_value_ae_eq`, applied to each component restricted to
`W`, turns this into the bound, so no constant is tracked through the regularity proof. The bound
for `η(·) v` follows by expanding `v` in the basis.

Together with Rellich's theorem, the estimate shows that the unit ball of weak solutions is
relatively compact in `L^q(W)`, the step towards the finite dimension of the cokernel of a real
Cauchy–Riemann operator on a closed surface.

## Main results

* `TauCeti.exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero`: the interior
  `W^{k+1,q}` estimate for `L^q` annihilators of a real Cauchy–Riemann operator.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.2.3 and Appendix B.4.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Complex Set Module Filter
open scoped ENNReal NNReal Distributions Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V}

/-- The real Cauchy–Riemann operator `φ ↦ ∂_s φ + J ∂_t φ + S φ` applied to a test function. -/
private def crApply (J S : ℂ → V →L[ℝ] V) (φ : ℂ → V) (z : ℂ) : V :=
  fderiv ℝ φ z 1 + J z (fderiv ℝ φ z I) + S z (φ z)

omit [FiniteDimensional ℝ V] in
/-- The real Cauchy–Riemann operator applied to a test function vanishes off its support. -/
private theorem crApply_eq_zero_of_notMem_tsupport (φ : 𝓓(Ω, V)) {z : ℂ}
    (hz : z ∉ tsupport (φ : ℂ → V)) : crApply J S φ z = 0 := by
  simp [crApply, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]

omit [FiniteDimensional ℝ V] in
/-- The real Cauchy–Riemann operator applied to a test function on `Ω` is continuous with compact
support, for coefficients continuous on `Ω`. -/
private theorem continuous_crApply (hJ : ContinuousOn J Ω) (hS : ContinuousOn S Ω)
    (φ : 𝓓(Ω, V)) : Continuous (crApply J S φ) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : z ∈ tsupport (φ : ℂ → V)
  · have hzΩ : z ∈ Ω := φ.tsupport_subset hz
    have hn : (Ω : Set ℂ) ∈ 𝓝 z := Ω.isOpen.mem_nhds hzΩ
    have hd := (φ.contDiff.continuous_fderiv (by simp)).continuousAt (x := z)
    exact (((hd.clm_apply continuousAt_const).add
      ((hJ.continuousAt hn).clm_apply (hd.clm_apply continuousAt_const))).add
      ((hS.continuousAt hn).clm_apply φ.contDiff.continuous.continuousAt))
  · refine (continuousAt_const (y := (0 : V))).congr ?_
    filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hz] with y hy
    exact (crApply_eq_zero_of_notMem_tsupport φ hy).symm

omit [FiniteDimensional ℝ V] in
private theorem hasCompactSupport_crApply (φ : 𝓓(Ω, V)) :
    HasCompactSupport (crApply J S φ) :=
  HasCompactSupport.intro' φ.hasCompactSupport (isClosed_tsupport _) fun _ hz ↦
    crApply_eq_zero_of_notMem_tsupport φ hz

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {ι : Type*} (b : Basis ι ℝ V)

/-- The coordinates of the real Cauchy–Riemann operator applied to a test function are in every
`Lᵖ` space over `Ω`. -/
private theorem memLp_coord_crApply (hJ : ContinuousOn J Ω) (hS : ContinuousOn S Ω) (c : ι)
    (φ : 𝓓(Ω, V)) (r : ℝ≥0∞) :
    MemLp (fun z ↦ b.coord c (crApply J S φ z)) r (volume.restrict (Ω : Set ℂ)) :=
  (((LinearMap.toContinuousLinearMap (b.coord c)).continuous.comp
    (continuous_crApply hJ hS φ)).memLp_of_hasCompactSupport
      ((hasCompactSupport_crApply φ).comp_left (map_zero _))).restrict _

/-- Expanding a covector field in a basis: the pairing of `η` with the real Cauchy–Riemann
operator applied to a test function is the sum over the basis of the pairings of the components
`η(b c)` with the coordinates of `D φ`, all over `Ω`. -/
private theorem integral_apply_crApply_eq_sum [Fintype ι] (hJ : ContinuousOn J Ω)
    (hS : ContinuousOn S Ω)
    {η : ℂ → V →L[ℝ] ℝ} (hη : MemLp η q (volume.restrict (Ω : Set ℂ))) (φ : 𝓓(Ω, V)) :
    ∫ z, η z (crApply J S φ z) =
      ∑ c, ∫ z in Ω, η z (b c) * b.coord c (crApply J S φ z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set ℂ)) fun z hz ↦ by
    rw [crApply_eq_zero_of_notMem_tsupport φ fun h ↦ hz (φ.tsupport_subset h), map_zero]]
  refine Eq.trans ?_ (integral_finsetSum _ fun c _ ↦
    (hη.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b c))).integrable_mul
      (memLp_coord_crApply b hJ hS c φ q.conjExponent))
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  -- The expansion of a covector in the coordinate functionals of `b`.
  -- `η z` expanded in the coordinate functionals of `b`.
  simpa [LinearMap.sum_apply, smul_eq_mul] using (LinearMap.congr_fun
    (b.sum_dual_apply_smul_coord ((η z : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ)) (crApply J S φ z)).symm

/-- **Regularity of a tuple of components.** A tuple `θ` of `L^q` functions on `Ω` that satisfies
the weak equation in components, `∑_c ∫ θ_c (D φ)_c = 0`, is the tuple of components of a weak
solution `∑_c θ_c b.coord c`. So each `θ_c` is `W^{k+1,q}` on every open `W` with compact closure
in `Ω`. -/
private theorem exists_wkp_of_forall_sum_integral_eq_zero [Fintype ι] {k : ℕ}
    (hJ : ContDiffOn ℝ (k + 1) J Ω) (hS : ContDiffOn ℝ k S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    (hq : 1 < q) (hq_top : q ≠ ⊤)
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω)
    (θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ)))
    (hθ : ∀ φ : 𝓓(Ω, V), ∑ c, ∫ z in Ω, θ c z * b.coord c (crApply J S φ z) = 0) (c : ι) :
    ∃ v : Wkp volume W q (k + 1),
      (Wkp.value (k + 1) v : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] θ c := by
  let T : (ι → ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    ∑ c', (ContinuousLinearMap.proj c').smulRight (LinearMap.toContinuousLinearMap (b.coord c'))
  let η : ℂ → V →L[ℝ] ℝ := fun z ↦ T fun c' ↦ θ c' z
  have hηb (z : ℂ) (c' : ι) : η z (b c') = θ c' z := by
    classical
    simp [η, T, Finsupp.single_apply]
  have hη : MemLp η q (volume.restrict (Ω : Set ℂ)) :=
    (MemLp.of_eval fun c' ↦ Lp.memLp (θ c')).continuousLinearMap_comp T
  have hηeq (φ : 𝓓(Ω, V)) : ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 +
      J z (fderiv ℝ (φ : ℂ → V) z I) + S z ((φ : ℂ → V) z)) = 0 := by
    refine (integral_apply_crApply_eq_sum b hJ.continuousOn hS.continuousOn hη φ).trans ?_
    rw [← hθ φ]
    simp only [hηb]
  obtain ⟨v, hv⟩ := ((memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero hJ
    hS hJ2 hq hη.memLpLoc hηeq (r := q) hq_top).clm_comp
      (ContinuousLinearMap.apply ℝ ℝ (b c))).exists_wkp hWc hWΩ
  refine ⟨v, hv.trans (.of_forall fun z ↦ ?_)⟩
  simp only [ContinuousLinearMap.apply_apply, hηb]

/-- The weak solutions, as tuples of `L^q` components in the basis `b`: the common kernel of the
continuous functionals `θ ↦ ∑_c ∫_Ω θ_c (D φ)_c`, one for each test function `φ`. -/
private def weakSolutions (hJ : ContinuousOn J Ω) (hS : ContinuousOn S Ω) [Fintype ι] :
    Submodule ℝ (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) :=
  have : Fact (1 ≤ q.conjExponent) := ⟨le_self_add⟩
  ⨅ φ : 𝓓(Ω, V), LinearMap.ker ((∑ c, (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volume.restrict (Ω : Set ℂ)) q q.conjExponent).flip
      ((memLp_coord_crApply b hJ hS c φ _).toLp _)).comp (ContinuousLinearMap.proj c) :
        (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) →L[ℝ] ℝ) :
          (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) →ₗ[ℝ] ℝ)

private theorem isClosed_weakSolutions (hJ : ContinuousOn J Ω) (hS : ContinuousOn S Ω)
    [Fintype ι] :
    IsClosed (weakSolutions (q := q) b hJ hS : Set (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ)))) := by
  simp only [weakSolutions, Submodule.coe_iInf]
  exact isClosed_iInter fun φ ↦ ContinuousLinearMap.isClosed_ker _

private theorem mem_weakSolutions (hJ : ContinuousOn J Ω) (hS : ContinuousOn S Ω) [Fintype ι]
    {θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))} :
    θ ∈ weakSolutions b hJ hS ↔
      ∀ φ : 𝓓(Ω, V), ∑ c, ∫ z in Ω, θ c z * b.coord c (crApply J S φ z) = 0 := by
  have : Fact (1 ≤ q.conjExponent) := ⟨le_self_add⟩
  simp only [weakSolutions, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  refine forall_congr' fun φ ↦ Eq.congr_left (Finset.sum_congr rfl fun c _ ↦ integral_congr_ae ?_)
  filter_upwards [MemLp.coeFn_toLp (memLp_coord_crApply b hJ hS c φ q.conjExponent)] with z hz
  rw [hz]

/-- **The interior estimate in components.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space with a basis `b`, `J` a `C^{k+1}` field of
complex structures and `S` a `C^k` field of endomorphisms over `Ω`, `1 < q < ∞`, and `W` open with
compact closure in `Ω`. There is a constant `C` such that every `L^q` covector field `η` on `Ω`
with `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω` has components
`η(b c)` in `W^{k+1,q}(W)` with norm at most `C ‖η‖_{L^q(Ω)}`. -/
private theorem exists_norm_wkp_le_components [Finite ι] {k : ℕ}
    (hJ : ContDiffOn ℝ (k + 1) J Ω) (hS : ContDiffOn ℝ k S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    (hq : 1 < q) (hq_top : q ≠ ⊤) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ C : ℝ, ∀ η : ℂ → V →L[ℝ] ℝ, MemLp η q (volume.restrict (Ω : Set ℂ)) →
      (∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
        S z ((φ : ℂ → V) z)) = 0) →
      ∀ c, ∃ u : Wkp volume W q (k + 1),
        (Wkp.value (k + 1) u : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] (fun z ↦ η z (b c)) ∧
          ‖u‖ ≤ C * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal := by
  have := Fintype.ofFinite ι
  have hWΩ' : W ≤ Ω := fun z hz ↦ hWΩ (subset_closure hz)
  let N := weakSolutions (q := q) b hJ.continuousOn hS.continuousOn
  have : CompleteSpace N :=
    (isClosed_weakSolutions b hJ.continuousOn hS.continuousOn).completeSpace_coe
  have hmemN {θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))} :=
    mem_weakSolutions (θ := θ) b hJ.continuousOn hS.continuousOn
  -- The `c`-th component of an element of `N`, restricted to `W`. `Lp ℝ q (volume.restrict Ω)`
  -- is `Wkp volume Ω q 0` by definition (`Wkp.value_zero`), so `Wkp.restrictL` restricts it.
  let R (c : ι) : N →L[ℝ] Lp ℝ q (volume.restrict (W : Set ℂ)) :=
    (Wkp.restrictL hWΩ' 0).comp ((ContinuousLinearMap.proj c).comp N.subtypeL)
  have hR (θ : N) (c : ι) : (R c θ : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] θ.val c := by
    have h := Wkp.value_restrictL_ae (mu := volume) (p := q) hWΩ' 0 (θ.val c)
    rwa [Wkp.value_zero, Wkp.value_zero] at h
  -- The closed graph estimate for each component.
  choose C hC using fun c ↦ Wkp.exists_norm_le_of_forall_exists_value_ae_eq (k := k + 1) (R c)
    fun θ ↦ (exists_wkp_of_forall_sum_integral_eq_zero b hJ hS hJ2 hq hq_top hWc hWΩ θ.val
      (hmemN.1 θ.prop) c).imp fun _ hv ↦ hv.trans (hR θ c).symm
  refine ⟨(∑ c, max (C c) 0) * ∑ c, ‖b c‖, fun η hη h c ↦ ?_⟩
  -- The tuple of components of `η`.
  have hηc (c : ι) : MemLp (fun z ↦ η z (b c)) q (volume.restrict (Ω : Set ℂ)) :=
    hη.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b c))
  let θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ)) := fun c ↦ (hηc c).toLp _
  have hθN : θ ∈ N := hmemN.2 fun φ ↦ by
    rw [← h φ]
    refine (Finset.sum_congr rfl fun c _ ↦ integral_congr_ae ?_).trans
      (integral_apply_crApply_eq_sum b hJ.continuousOn hS.continuousOn hη φ).symm
    filter_upwards [(hηc c).coeFn_toLp] with z hz
    rw [hz]
  obtain ⟨v, hv, hvC⟩ := hC c ⟨θ, hθN⟩
  refine ⟨v, hv.trans ((hR _ c).trans (ae_restrict_of_ae_restrict_of_subset hWΩ'
    (hηc c).coeFn_toLp)), hvC.trans ?_⟩
  -- The tuple of components has norm at most `∑_c ‖b c‖ ‖η‖`.
  set E := (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal
  have hθ : ‖(⟨θ, hθN⟩ : N)‖ ≤ (∑ c, ‖b c‖) * E := by
    rw [← Submodule.norm_coe, Submodule.coe_mk]
    have hE : 0 ≤ E := ENNReal.toReal_nonneg
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun c _ ↦ norm_nonneg _) hE)).2
      fun c' ↦ le_trans ?_ (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun c _ ↦ norm_nonneg (b c)) (Finset.mem_univ c')) hE)
    -- `θ c'` is `η` composed with evaluation at `b c'`, of norm at most `‖b c'‖`.
    have hL : θ c' = (ContinuousLinearMap.apply ℝ ℝ (b c')).compLp (hη.toLp η) :=
      Lp.ext ((MemLp.coeFn_toLp _).trans ((hη.coeFn_toLp.fun_comp _).symm.trans
        ((ContinuousLinearMap.apply ℝ ℝ (b c')).coeFn_compLp' _).symm))
    rw [hL]
    refine ((ContinuousLinearMap.apply ℝ ℝ (b c')).norm_compLp_le _).trans ?_
    rw [Lp.norm_toLp]
    exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      fun f ↦ by simpa [mul_comm] using f.le_opNorm (b c')) hE
  have hCc : C c ≤ ∑ c, max (C c) 0 := (le_max_left _ _).trans
    (Finset.single_le_sum (fun c _ ↦ le_max_right (C c) 0) (Finset.mem_univ c))
  exact (mul_le_mul hCc hθ (norm_nonneg _) (Finset.sum_nonneg fun c _ ↦ le_max_right _ _)).trans_eq
    (mul_assoc _ _ _).symm

/-- **The interior estimate for annihilators of a real Cauchy–Riemann operator.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space, `k ∈ ℕ`, `J` a `C^{k+1}` field of complex
structures and `S` a `C^k` field of endomorphisms over `Ω`, `1 < q < ∞`, and `W` open with
compact closure in `Ω`. There is a constant `C` such that for every `L^q` covector field `η` on
`Ω` with `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω` and every `v : V`,
the function `η(·) v` is in `W^{k+1,q}(W)` with norm at most `C ‖v‖ ‖η‖_{L^q(Ω)}`. -/
theorem exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero {k : ℕ}
    (hJ : ContDiffOn ℝ (k + 1) J Ω) (hS : ContDiffOn ℝ k S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    (hq : 1 < q) (hq_top : q ≠ ⊤) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ C : ℝ, ∀ η : ℂ → V →L[ℝ] ℝ, MemLp η q (volume.restrict (Ω : Set ℂ)) →
      (∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
        S z ((φ : ℂ → V) z)) = 0) →
      ∀ v : V, ∃ u : Wkp volume W q (k + 1),
        (Wkp.value (k + 1) u : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] (fun z ↦ η z v) ∧
          ‖u‖ ≤ C * ‖v‖ * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal := by
  -- Components in a basis, recombined with the coordinates of `v`.
  let b := Module.finBasis ℝ V
  let K : ℝ := ∑ c, ‖LinearMap.toContinuousLinearMap (b.coord c)‖
  obtain ⟨C₀, hC₀⟩ := exists_norm_wkp_le_components b hJ hS hJ2 hq hq_top hWc hWΩ
  refine ⟨max C₀ 0 * K, fun η hη h v ↦ ?_⟩
  set E := (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal
  choose u hu huC using hC₀ η hη h
  refine ⟨∑ c, b.coord c v • u c, ?_, ?_⟩
  · -- The value of the combination is the combination of the values.
    have hsum := Lp.coeFn_finsetSum (μ := volume.restrict (W : Set ℂ)) (p := q) Finset.univ
      fun c ↦ b.coord c v • Wkp.value (k + 1) (u c)
    have hval : Wkp.value (k + 1) (∑ c, b.coord c v • u c) =
        ∑ c, b.coord c v • Wkp.value (k + 1) (u c) := by
      simp only [← Wkp.valueL_apply, map_sum, map_smul]
    rw [hval]
    filter_upwards [hsum,
      ae_all_iff.2 fun c ↦ Lp.coeFn_smul (b.coord c v) (Wkp.value (k + 1) (u c)),
      ae_all_iff.2 hu] with z h₁ h₂ h₃
    -- `η z` expanded in the coordinate functionals of `b`.
    have he : η z v = ∑ c, b.coord c v * η z (b c) := by
      simpa [LinearMap.sum_apply, smul_eq_mul, mul_comm] using (LinearMap.congr_fun
        (b.sum_dual_apply_smul_coord ((η z : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ)) v).symm
    rw [h₁, Finset.sum_apply, he]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [h₂ c, Pi.smul_apply, h₃ c, smul_eq_mul]
  · -- `|vᶜ| ≤ ‖b.coord c‖ ‖v‖` and `‖u c‖ ≤ max C₀ 0 ‖η‖`.
    have hE : 0 ≤ E := ENNReal.toReal_nonneg
    calc ‖∑ c, b.coord c v • u c‖ ≤ ∑ c, ‖b.coord c v‖ * ‖u c‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ (norm_smul _ _).le)
      _ ≤ ∑ c, (‖LinearMap.toContinuousLinearMap (b.coord c)‖ * ‖v‖) * (max C₀ 0 * E) :=
          Finset.sum_le_sum fun c _ ↦ mul_le_mul
            ((LinearMap.toContinuousLinearMap (b.coord c)).le_opNorm v)
            ((huC c).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE)) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max C₀ 0 * K * ‖v‖ * E := by
          simp only [K, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ ↦ by ring

end TauCeti
