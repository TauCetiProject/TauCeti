/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator
public import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Analysis.Sobolev.Wkp.ClosedGraph

/-!
# The interior estimate for annihilators of real Cauchy–Riemann operators

Let `Ω ⊆ ℂ` be open, `V` a finite-dimensional real normed space, `J` a `C¹` field of complex
structures on `V` and `S` a continuous field of endomorphisms over `Ω`, and `1 < q < ∞`. An `L^q`
covector field `η` on `Ω` annihilating `∂_s φ + J ∂_t φ + S φ` for every test function `φ` is
`W^{1,q}` on every open `W` with compact closure in `Ω`
(`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`). This file proves the
corresponding estimate: there is a constant `C`, depending on `W` but not on `η`, with
`‖η(b c)‖_{W^{1,q}(W)} ≤ C ‖η‖_{L^q(Ω)}` for the components of `η` in a basis `b` of `V`
(`TauCeti.exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero`).

The weak solutions form a closed subspace of `L^q(Ω)`, cut out by the continuous functionals
`η ↦ ∫ η (∂_s φ + J ∂_t φ + S φ)`, and the regularity theorem represents their components in
`W^{1,q}(W)`. The closed graph estimate `TauCeti.Wkp.exists_norm_le_of_isClosed` turns this into
the bound, so no constant is tracked through the regularity proof.

Together with Rellich's theorem, the estimate shows that the unit ball of weak solutions is
relatively compact in `L^q(W)`, the step towards the finite dimension of the cokernel of a real
Cauchy–Riemann operator on a closed surface.

## Main results

* `TauCeti.exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero`: the interior
  `W^{1,q}` estimate for `L^q` annihilators of a real Cauchy–Riemann operator.

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
    simp [crApply, fderiv_of_notMem_tsupport ℝ hy, image_eq_zero_of_notMem_tsupport hy]

omit [FiniteDimensional ℝ V] in
private theorem hasCompactSupport_crApply (φ : 𝓓(Ω, V)) :
    HasCompactSupport (crApply J S φ) :=
  HasCompactSupport.intro' φ.hasCompactSupport (isClosed_tsupport _) fun z hz ↦ by
    simp [crApply, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {ι : Type*} (b : Basis ι ℝ V)

/-- Expanding a covector field in a basis: the pairing of `η` with the real Cauchy–Riemann
operator applied to a test function is the sum over the basis of the pairings of the components
`η(b c)` with the coordinates of `D φ`, all over `Ω`. -/
private theorem integral_apply_crApply_eq_sum [Fintype ι] (hJ : ContinuousOn J Ω)
    (hS : ContinuousOn S Ω)
    {η : ℂ → V →L[ℝ] ℝ} (hη : MemLp η q (volume.restrict (Ω : Set ℂ))) (φ : 𝓓(Ω, V)) :
    ∫ z, η z (crApply J S φ z) =
      ∑ c, ∫ z in Ω, η z (b c) * b.coord c (crApply J S φ z) := by
  have hcont := continuous_crApply hJ hS φ
  have hc (c : ι) : MemLp (fun z ↦ b.coord c (crApply J S φ z)) q.conjExponent
      (volume.restrict (Ω : Set ℂ)) :=
    ((LinearMap.toContinuousLinearMap (b.coord c)).continuous.comp hcont).memLp_of_hasCompactSupport
      ((hasCompactSupport_crApply φ).comp_left (map_zero _)) |>.restrict _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set ℂ)) fun z hz ↦ by
    have hzφ : z ∉ tsupport (φ : ℂ → V) := fun h ↦ hz (φ.tsupport_subset h)
    simp [crApply, fderiv_of_notMem_tsupport ℝ hzφ, image_eq_zero_of_notMem_tsupport hzφ]]
  refine Eq.trans ?_ (integral_finsetSum _ fun c _ ↦
    (hη.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b c))).integrable_mul (hc c))
  have key (L : V →L[ℝ] ℝ) (v : V) : L v = ∑ c, L (b c) * b.coord c v := by
    calc L v = L (∑ c, b.repr v c • b c) := by rw [b.sum_repr]
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun c _ ↦ by rw [map_smul, smul_eq_mul, mul_comm,
          Basis.coord_apply]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simpa using key (η z) (crApply J S φ z)

/-- **The interior estimate for annihilators of a real Cauchy–Riemann operator.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space with a basis `b`, `J` a `C¹` field of complex
structures and `S` a continuous field of endomorphisms over `Ω`, `1 < q < ∞`, and `W` open with
compact closure in `Ω`. There is a constant `C` such that every `L^q` covector field `η` on `Ω`
with `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω` has components
`η(b c)` in `W^{1,q}(W)` with norm at most `C ‖η‖_{L^q(Ω)}`. -/
theorem exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero [Finite ι]
    (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    (hq : 1 < q) (hq_top : q ≠ ⊤) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ C : ℝ, ∀ η : ℂ → V →L[ℝ] ℝ, MemLp η q (volume.restrict (Ω : Set ℂ)) →
      (∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
        S z ((φ : ℂ → V) z)) = 0) →
      ∀ c, ∃ u : Wkp volume W q 1,
        (Wkp.value 1 u : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] (fun z ↦ η z (b c)) ∧
          ‖u‖ ≤ C * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal := by
  have : Fact (1 ≤ q.conjExponent) := ⟨le_self_add⟩
  have := Fintype.ofFinite ι
  have hWΩ' : W ≤ Ω := fun z hz ↦ hWΩ (subset_closure hz)
  -- The coordinates of `D φ`, as elements of the dual exponent space.
  let g (φ : 𝓓(Ω, V)) (c : ι) : Lp ℝ q.conjExponent (volume.restrict (Ω : Set ℂ)) :=
    (((LinearMap.toContinuousLinearMap (b.coord c)).continuous.comp
      (continuous_crApply hJ.continuousOn hS φ)).memLp_of_hasCompactSupport
        ((hasCompactSupport_crApply φ).comp_left (map_zero _)) |>.restrict _).toLp _
  -- The weak equation, as the vanishing of continuous functionals of the components.
  let Ψ (φ : 𝓓(Ω, V)) : (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) →L[ℝ] ℝ :=
    ∑ c, (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume.restrict (Ω : Set ℂ)) q
      q.conjExponent).flip (g φ c)).comp (ContinuousLinearMap.proj c)
  let N : Submodule ℝ (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) :=
    ⨅ φ, LinearMap.ker (Ψ φ : (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) →ₗ[ℝ] ℝ)
  have hN : IsClosed (N : Set (ι → Lp ℝ q (volume.restrict (Ω : Set ℂ)))) := by
    simp only [N, Submodule.coe_iInf]
    exact isClosed_iInter fun φ ↦ (Ψ φ).isClosed_ker
  have hΨ (φ : 𝓓(Ω, V)) (θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ))) :
      Ψ φ θ = ∑ c, ∫ z in Ω, θ c z * b.coord c (crApply J S φ z) := by
    simp only [Ψ, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
    refine Finset.sum_congr rfl fun c _ ↦ integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (((LinearMap.toContinuousLinearMap (b.coord c)).continuous.comp
      (continuous_crApply hJ.continuousOn hS φ)).memLp_of_hasCompactSupport
        ((hasCompactSupport_crApply φ).comp_left (map_zero _)) |>.restrict (Ω : Set ℂ))]
      with z hz
    rw [hz, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
  -- Every element of `N` is the tuple of components of a weak solution, which is `W^{1,q}` on `W`.
  have hreg (θ) (hθ : θ ∈ N) (c : ι) : ∃ v : Wkp volume W q 1,
      (Wkp.value 1 v : ℂ → ℝ) =ᵐ[volume.restrict (W : Set ℂ)] θ c := by
    let T : (ι → ℝ) →L[ℝ] V →L[ℝ] ℝ :=
      ∑ c', (ContinuousLinearMap.proj c').smulRight (LinearMap.toContinuousLinearMap (b.coord c'))
    let η : ℂ → V →L[ℝ] ℝ := fun z ↦ T fun c' ↦ θ c' z
    have hηb (z : ℂ) (c' : ι) : η z (b c') = θ c' z := by
      simp only [η, T, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.proj_apply, smul_apply, LinearMap.coe_toContinuousLinearMap',
        Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      rw [Finset.sum_eq_single c' (fun x _ hx ↦ by rw [Finsupp.single_eq_of_ne hx, mul_zero])
        (by simp), Finsupp.single_eq_same, mul_one]
    have hη : MemLp η q (volume.restrict (Ω : Set ℂ)) :=
      (MemLp.of_eval fun c' ↦ Lp.memLp (θ c')).continuousLinearMap_comp T
    have hηeq (φ : 𝓓(Ω, V)) : ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 +
        J z (fderiv ℝ (φ : ℂ → V) z I) + S z ((φ : ℂ → V) z)) = 0 := by
      have h0 : Ψ φ θ = 0 := by
        simp only [N, Submodule.mem_iInf, LinearMap.mem_ker] at hθ
        exact hθ φ
      rw [hΨ] at h0
      refine (integral_apply_crApply_eq_sum b hJ.continuousOn hS hη φ).trans (h0 ▸ ?_)
      simp only [hηb]
    have hk : ContDiffOn ℝ ((0 : ℕ) + 1) J Ω := by simpa using hJ
    have hreg := (memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero (k := 0) hk
      (contDiffOn_zero.2 hS) hJ2 hq hη.memLpLoc hηeq (r := q) hq_top).clm_comp
        (ContinuousLinearMap.apply ℝ ℝ (b c))
    obtain ⟨v, hv⟩ := hreg.exists_wkp hWc hWΩ
    refine ⟨v, hv.trans (.of_forall fun z ↦ ?_)⟩
    simp only [ContinuousLinearMap.apply_apply, hηb]
  obtain ⟨C, hC⟩ := Wkp.exists_norm_le_of_isClosed hWΩ' N hN hreg
  refine ⟨max C 0 * ∑ c, ‖b c‖, fun η hη h c ↦ ?_⟩
  -- The tuple of components of `η`.
  have hηc (c : ι) : MemLp (fun z ↦ η z (b c)) q (volume.restrict (Ω : Set ℂ)) :=
    hη.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b c))
  let θ : ι → Lp ℝ q (volume.restrict (Ω : Set ℂ)) := fun c ↦ (hηc c).toLp _
  have hθN : θ ∈ N := by
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
    intro φ
    rw [ContinuousLinearMap.coe_coe, hΨ, ← h φ]
    refine (Finset.sum_congr rfl fun c _ ↦ integral_congr_ae ?_).trans
      (integral_apply_crApply_eq_sum b hJ.continuousOn hS hη φ).symm
    filter_upwards [(hηc c).coeFn_toLp] with z hz
    rw [hz]
  obtain ⟨v, hv, hvC⟩ := hC θ hθN c
  refine ⟨v, hv.trans (ae_restrict_of_ae_restrict_of_subset (fun z hz ↦ hWΩ' hz)
    (hηc c).coeFn_toLp), hvC.trans ?_⟩
  -- Each component has norm at most `‖b c‖ ‖η‖`.
  have hθc (c : ι) : ‖θ c‖ ≤ ‖b c‖ * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal := by
    rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal (norm_nonneg (b c)), ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hη.eLpNorm_ne_top)
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hηc c).aestronglyMeasurable
        (.of_forall fun z ↦ ?_) q)
    rw [mul_comm]
    exact (η z).le_opNorm (b c)
  have hsum (c : ι) : ‖b c‖ ≤ ∑ c, ‖b c‖ :=
    Finset.single_le_sum (fun c _ ↦ norm_nonneg (b c)) (Finset.mem_univ c)
  have hE := ENNReal.toReal_nonneg (a := eLpNorm η q (volume.restrict (Ω : Set ℂ)))
  have hθ : ‖θ‖ ≤ (∑ c, ‖b c‖) * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun c _ ↦ norm_nonneg _) hE)).2
      fun c ↦ (hθc c).trans (mul_le_mul_of_nonneg_right (hsum c) hE)
  calc C * ‖θ‖ ≤ max C 0 * ‖θ‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C 0 * ((∑ c, ‖b c‖) * (eLpNorm η q (volume.restrict (Ω : Set ℂ))).toReal) :=
      mul_le_mul_of_nonneg_left hθ (le_max_right _ _)
    _ = _ := by ring

end TauCeti
