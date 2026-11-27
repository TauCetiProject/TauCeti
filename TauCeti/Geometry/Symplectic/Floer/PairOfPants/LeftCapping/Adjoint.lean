/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Patching
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The semi-Fredholm estimate of the formal adjoint along the input-exchange family capped at `0`

The left unit of the pair-of-pants product is compared with continuation maps along the
input-exchange family capped at `0`, `K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for
`0 ≤ c ≤ 1`. Its domain is the capped surface `ℂ ∖ {1}`: the input end at `1` carries `H_1`, the
output end, recentred at `c`, carries `H_∞`, and the capped puncture `0` is an interior point. The
linearized Floer operator `D_u` of this family has finite-dimensional kernel and closed range on
`W^{1,2}` (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Sobolev`). Its cokernel is
the kernel of the formal adjoint `D_u^*`, and this file proves the semi-Fredholm estimate of
`D_u^*` on which the finiteness of that cokernel rests, as for the PSS plane and the pair of pants
with continuation necks:

`∑_{e} ∫_{(T, ∞) × [0, 1]} (‖∂s η'_e‖² + ‖∂t η'_e‖² + ‖η'_e‖²)`
`  + ∫_{Σ_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{Σ_{T + 1}} ‖η‖²)`,

in the namespace `TauCeti.SymplecticForm`:
`exists_forall_le_mul_integral_floerLinearizationAdjoint_cappedExchangePerturbation_add`. Here
`ρ` is the cylindrical weight of the capped surface (`TauCeti.Floer.cappedCylindricalWeight`),
`η'_e` is the covector field `η` read on the end `e` as a `(0, 1)`-form, in the positive end chart
`φ'_1` of the pair of pants on the input end and in the chart `c + φ'_∞` on the output end, and
`Σ_T` is the annulus `exp (-2πT) / 2 ≤ |w - 1|`, `|w - c| ≤ 2 exp (2πT)`.

The estimate is patched together from estimates of `D_u^*` on the two ends by
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Patching`. On the input end the end
estimate of the pair of pants applies, since far out the capped datum is the pair-of-pants datum
(`TauCeti.Floer.cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one`); on the output end
the end estimate of the adjoint in a holomorphic end chart applies to the chart `c + φ'_∞`, in
which the capped datum is `H_∞(t) dt`
(`TauCeti.Floer.cappedExchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord`). The weights
`|w - 1|²` and `4π² |w - c|²` of these two estimates are at most `5 ρ⁻¹` and `32π² ρ⁻¹` on the
ends.

The Peetre argument giving a finite cokernel from this estimate, and the index, are not treated
here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendices B and C.1, on the formal adjoint and the semi-Fredholm estimate on punctured
  Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold Real

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {c : ℝ}

/-- The chart `c + φ'_∞` of the output end maps the part `s > 0` into the capped surface: there
`|w - c| = 2 exp (2πs) > 2`. -/
private theorem equivRealProdCLM_symm_positiveEndChart_inf_add_ne_one (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) :
    Complex.equivRealProdCLM.symm (positiveEndChart inf ζ + (c, 0)) ≠ 1 := by
  intro h1
  rw [TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero] at h1
  have hn := norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2
  rw [Prod.mk.eta, eq_sub_of_add_eq h1, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hn
  linarith [Real.one_lt_exp_iff.2 (by positivity : 0 < 2 * π * ζ.1)]

/-- Beyond the height `0` of the input end, a point of the capped surface lies in the pair of
pants `S = ℂ ∖ {0, 1}`. -/
private theorem mem_thricePuncturedSphereReal_of_pos_fst_positiveEndCoord_one {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 1) (h : 0 < (positiveEndCoord one z).1) :
    z ∈ thricePuncturedSphereReal := by
  refine mem_thricePuncturedSphereReal_iff.2 ⟨fun h0 ↦ ?_, hz⟩
  have h₁ := norm_sub_one_lt_of_pos_fst_positiveEndCoord_one h
  rw [h0, zero_sub, norm_neg, norm_one] at h₁
  norm_num at h₁

/-- The weighted square norm of the formal adjoint of the capped datum on a `C¹` covector field
with compact support in the capped surface is integrable, for a weight continuous there. -/
private theorem integrable_mul_norm_floerLinearizationAdjoint_sq_cappedExchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w {z | Complex.equivRealProdCLM.symm z ≠ 1}) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1}) :
    Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
        Complex.I) u η z‖ ^ 2 :=
  ω.integrable_mul_norm_floerLinearizationAdjoint_sq isWeight_cappedCylindricalWeight.isOpen
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) (fun z hz ↦ hJ z hz)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) Complex.I)
    (fun z hz ↦ hu z hz) hw (hη.of_le one_le_two) subset_rfl hηc hηU

/-- The inverse `ρ⁻¹` of the cylindrical weight of the capped surface is continuous there. -/
private theorem continuousOn_inv_cappedCylindricalWeight :
    ContinuousOn (fun z ↦ (cappedCylindricalWeight z)⁻¹)
      {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
  isWeight_cappedCylindricalWeight.continuousOn.inv₀
    fun z hz ↦ (isWeight_cappedCylindricalWeight.pos z hz).ne'

/-- Beyond the height `0` of the input end, `|w - 1|² ≤ 5 ρ⁻¹` for the cylindrical weight `ρ` of the
capped surface. -/
private theorem norm_sub_one_sq_le_inv_cappedCylindricalWeight {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 1) (h : 0 < (positiveEndCoord one z).1) :
    ‖Complex.equivRealProdCLM.symm z - 1‖ ^ 2 ≤ 5 * (cappedCylindricalWeight z)⁻¹ := by
  have h₁ := norm_sub_one_lt_of_pos_fst_positiveEndCoord_one h
  have hw : 1 / 2 ≤ ‖Complex.equivRealProdCLM.symm z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (Complex.equivRealProdCLM.symm z)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hzS := mem_thricePuncturedSphereReal_of_pos_fst_positiveEndCoord_one hz h
  rw [cappedCylindricalWeight_eq_cylindricalWeight hw, ← div_eq_mul_inv,
    le_div_iff₀ (isWeight_cylindricalWeight.pos z hzS)]
  have h₂ := norm_sub_endCenter_sq_mul_cylindricalWeight_le one hzS h.le
  rwa [endCenter_one] at h₂

/-- Beyond the height `0` of the output end recentred at `c ∈ [0, 1]`, `|w - c|² ≤ 8 ρ⁻¹` for the
cylindrical weight `ρ` of the capped surface. -/
private theorem norm_sub_sq_le_inv_cappedCylindricalWeight (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {z : ℝ × ℝ} (h : 0 < (positiveEndCoord inf (z - (c, 0))).1) :
    ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 ≤ 8 * (cappedCylindricalWeight z)⁻¹ := by
  set v := Complex.equivRealProdCLM.symm z
  have hd : 2 < ‖v - c‖ := two_lt_norm_sub_of_pos_fst_positiveEndCoord_inf_sub h
  have hc : ‖(c : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hc₀]; exact hc₁
  have h1c : ‖(1 : ℂ) - c‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  -- Both `|w|` and `|w - 1|` are at least `|w - c| / 2`.
  have hv : ‖v - c‖ / 2 ≤ ‖v‖ := by linarith [norm_sub_le v (c : ℂ)]
  have hv1 : ‖v - c‖ / 2 ≤ ‖v - 1‖ := by
    have := norm_add_le (v - 1) ((1 : ℂ) - c)
    rw [sub_add_sub_cancel] at this
    linarith
  have hA : ‖v - c‖ ^ 2 / 4 ≤ max (‖v‖ ^ 2) (1 / 4) := le_max_of_le_left (by nlinarith)
  have hA₀ : 0 < max (‖v‖ ^ 2) (1 / 4) := lt_max_of_lt_right (by norm_num)
  have hB : ‖v - c‖ ^ 2 / 4 ≤ ‖v - 1‖ ^ 2 := by nlinarith
  have hB₀ : 0 < ‖v - 1‖ ^ 2 := by nlinarith
  have hρ : 0 < cappedCylindricalWeight z :=
    isWeight_cappedCylindricalWeight.pos z fun h1 ↦ by
      have h0 : ‖v - 1‖ = 0 := by rw [show v = 1 from h1, sub_self, norm_zero]
      linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hρ, cappedCylindricalWeight_apply,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, mul_add]
  have h₁ : ‖v - c‖ ^ 2 * (max (‖v‖ ^ 2) (1 / 4))⁻¹ ≤ 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hA₀]
    linarith
  have h₂ : ‖v - c‖ ^ 2 * (‖v - 1‖ ^ 2)⁻¹ ≤ 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hB₀]
    linarith
  linarith

/-- **Changing the weight of an end estimate.** If `w₁ ≤ k w₂` on the support of `η`, with
`w₁ ≥ 0` and `w₂ ‖D^* η‖²` integrable, then `C ∫ w₁ ‖D^* η‖² ≤ max C 0 k ∫ w₂ ‖D^* η‖²`. -/
private theorem mul_integral_mul_norm_floerLinearizationAdjoint_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {w₁ w₂ : ℝ × ℝ → ℝ} {k : ℝ} (hw₁ : ∀ z, 0 ≤ w₁ z)
    (hw : ∀ z ∈ tsupport η, w₁ z ≤ k * w₂ z)
    (hint : Integrable fun z ↦ w₂ z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) (C : ℝ) :
    C * ∫ z, w₁ z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 ≤
      max C 0 * k * ∫ z, w₂ z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  rw [mul_assoc]
  refine (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (integral_nonneg fun z ↦ by have := hw₁ z; positivity)).trans
    (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun z ↦ by have := hw₁ z; positivity)
    (hint.const_mul k) (.of_forall fun z ↦ ?_)
  beta_reduce
  by_cases hz : z ∈ tsupport η
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hw z hz) (sq_nonneg _)
  · simp [floerLinearizationAdjoint_of_notMem_tsupport hz]

/-- **The input end of the capped family.** Far out on the input end at `1`, read in the positive
end chart `φ'_1`, the formal adjoint of the linearized operator of the capped datum controls the
energy of covector fields against the weight `ρ⁻¹`: on the part `s > 0` the capped datum is the
pair-of-pants datum, so the end estimate of the pair of pants applies, and its weight `|w - 1|²` is
at most `5 ρ⁻¹` there. -/
private theorem exists_forall_setIntegral_covectorPullback_le_capped_one (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : ℝ≥0}
    (hX : LipschitzWith Λ (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H one)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H one t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H one) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart one ζ))
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆
        {z | Complex.equivRealProdCLM.symm z ≠ 1 ∧ R < (positiveEndCoord one z).1} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart one)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, (cappedCylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2 := by
  have hSU : thricePuncturedSphereReal ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2
  -- Beyond the height `max R₁ 1 > 0`, the capped datum is the pair-of-pants datum.
  have hR₁ : R₁ ≤ max R₁ 1 := le_max_left _ _
  have hK (z : ℝ × ℝ) (_ : z ∈ thricePuncturedSphereReal)
      (hz : max R₁ 1 ≤ (positiveEndCoord one z).1) :
      (fun x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1) =
          (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        (fun x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I := by
    simp only [cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one (H := H) (L := L)
      (by linarith) hc₀ hc₁ (by linarith [le_max_right R₁ 1] : 0 < (positiveEndCoord one z).1),
      and_self]
  obtain ⟨C, R, hest⟩ :=
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint hH hHs
      one hX hx hnd hJe hJex (R₁ := max R₁ 1) (fun ζ hζ ↦ hJeq ζ (hR₁.trans hζ)) hK
      (fun z hz ↦ hJ z (hSU hz)) (fun z hz ↦ hu z (hSU hz)) (fun ζ hζ ↦ hu₂ ζ (hR₁.trans hζ))
      (fun z hz ↦ hc z (hSU hz)) (fun z hz hzR ↦ hF z hz (hR₁.trans hzR)) hux hδ
  refine ⟨max C 0 * 5, max R 0, fun η hη hηc hηR ↦ ?_⟩
  have hηU : tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} := fun z hz ↦ (hηR hz).1
  have hpos (z : ℝ × ℝ) (hz : z ∈ tsupport η) : 0 < (positiveEndCoord one z).1 :=
    (le_max_right R 0).trans_lt (hηR hz).2
  have hηS : tsupport η ⊆
      {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord one z).1} := fun z hz ↦
    ⟨mem_thricePuncturedSphereReal_of_pos_fst_positiveEndCoord_one (hηU hz) (hpos z hz),
      (le_max_left R 0).trans_lt (hηR hz).2⟩
  have hint :=
    integrable_mul_norm_floerLinearizationAdjoint_sq_cappedExchangePerturbation (c := c) ω hH hHs
      hL hJ hu continuousOn_inv_cappedCylindricalWeight hη hηc hηU
  -- On the support of `η` the weight `|w - 1|²` of the end estimate is at most `5 ρ⁻¹`.
  have hw (z : ℝ × ℝ) (hz : z ∈ tsupport η) :
      ‖Complex.equivRealProdCLM.symm z - one.endCenter‖ ^ 2 ≤
        5 * (cappedCylindricalWeight z)⁻¹ := by
    rw [endCenter_one]
    exact norm_sub_one_sq_le_inv_cappedCylindricalWeight (hηU hz) (hpos z hz)
  calc _ ≤ ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart one)
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ :=
        setIntegral_mono_set (integrableOn_sobolevDensity_covectorPullback_positiveEndChart
          (fun z hz ↦ hJ z (hSU hz)) (fun z hz ↦ hu z (hSU hz)) (hη.of_le one_le_two) hηc
          (fun z hz ↦ (hηS hz).1) one 0)
          (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
          (.of_forall fun _ hζ ↦ prod_mono (Ioi_subset_Ioi (by norm_num)) subset_rfl hζ)
    _ ≤ C * ∫ z, ‖Complex.equivRealProdCLM.symm z - one.endCenter‖ ^ 2 *
        ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2 := hest hη hηc hηS
    _ ≤ _ := mul_integral_mul_norm_floerLinearizationAdjoint_sq_le ω
        (w₂ := fun z ↦ (cappedCylindricalWeight z)⁻¹) (fun z ↦ sq_nonneg _) hw hint C

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Far out on the output end, the pullback of the capped datum along `c + φ'_∞` is the pullback of
the pair-of-pants datum along `φ'_∞`. -/
private theorem perturbationPullback_positiveEndChart_inf_add_cappedExchangePerturbation
    {H : Puncture → ℝ → V → ℝ} {L : ℝ} (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {ζ : ℝ × ℝ}
    (hζ : 1 < ζ.1) (v : ℝ × ℝ) :
    perturbationPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) v ζ =
      perturbationPullback (positiveEndChart inf)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v
        ζ := by
  funext x
  have h1 : 1 < (positiveEndCoord inf (positiveEndChart inf ζ)).1 := by
    rwa [fst_positiveEndCoord_positiveEndChart]
  simp only [perturbationPullback_apply, fderiv_add_const,
    cappedExchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord hL hc₀ hc₁ h1]

/-- **The end estimate on the output end of the capped family, in its chart.** The end estimate
in a holomorphic end chart applies to the chart `c + φ'_∞`, in which the capped datum is
`H_∞(t) dt` beyond the height `2`, with the weight `4π² |w - c|²`, the Jacobian of the chart. -/
private theorem exists_forall_setIntegral_covectorPullback_le_capped_inf_chart
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : ℝ≥0}
    (hX : LipschitzWith Λ (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H inf)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H inf) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu₂ : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart inf ζ + (c, 0)))
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, max R₁ 2 < R ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ∀ ⦃b : ℝ⦄,
      (∀ s t, s ∉ Ioo R b → η (positiveEndChart inf (s, t) + (c, 0)) = 0) →
      Integrable (fun z ↦ 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 *
        ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2) →
      ∫ ζ in Ioi (max R₁ 2) ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2 := by
  -- The perturbation is `H_∞(t) dt` beyond the height `2` of the output end of the pair of pants.
  have hKH (w : ℂ) (y : V) (hw : 2 ≤ inf.endSign * (inf.endCoord w).re) :
      pairOfPantsPerturbation H w y = H inf (inf.endCoord w).im y • inf.endAngularForm w :=
    pairOfPantsPerturbation_eq_smul_endAngularForm hw y
  have hR₁ : R₁ ≤ max R₁ 2 := le_max_left _ _
  have h2 : (2 : ℝ) ≤ max R₁ 2 := le_max_right _ _
  have hdom (ζ : ℝ × ℝ) (hζ : max R₁ 2 < ζ.1) :
      Complex.equivRealProdCLM.symm (positiveEndChart inf ζ + (c, 0)) ≠ 1 :=
    equivRealProdCLM_symm_positiveEndChart_inf_add_ne_one hc₀ hc₁ (by linarith)
  -- The weight `4π² |w - c|²` is the Jacobian of the chart `c + φ'_∞`.
  exact
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart
      (R₁ := max R₁ 2) (ψ := fun ζ ↦ positiveEndChart inf ζ + (c, 0))
      (w := fun z ↦ 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2) hX
      (contDiff_uncurry_positiveEndHamiltonian (hHs inf)) hx hnd hJe hJex
      (fun ζ _ ↦ ((contDiff_positiveEndChart inf 3).add contDiff_const).contDiffAt)
      (fun ζ _ ↦ by rw [fderiv_add_const]; exact isComplexLinearMap_fderiv_positiveEndChart inf ζ)
      (fun ζ _ ↦ by rw [fderiv_add_const]; exact fderiv_positiveEndChart_ne_zero inf ζ)
      (fun s t ↦ by simp only [positiveEndChart_add_one])
      (fun a ha b hb hab ↦ (injOn_positiveEndChart inf 0).mono
        (Set.prod_mono (subset_univ _) (by rw [zero_add]; exact Ioo_subset_Ico_self)) ha hb
        (add_right_cancel hab))
      (fun ζ hζ ↦ hJeq ζ (hR₁.trans hζ.le))
      (fun ζ hζ ↦ by
        rw [perturbationPullback_positiveEndChart_inf_add_cappedExchangePerturbation (by linarith)
          hc₀ hc₁ (by linarith)]
        exact funext (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH
          (h2.trans hζ.le)))
      (fun ζ hζ ↦ by
        rw [perturbationPullback_positiveEndChart_inf_add_cappedExchangePerturbation (by linarith)
          hc₀ hc₁ (by linarith)]
        exact funext (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH (hH inf)
          (h2.trans hζ.le)))
      (fun ζ hζ ↦ hJ _ (hdom ζ hζ)) (fun ζ hζ ↦ hu₂ ζ (hR₁.trans hζ.le))
      (fun ζ hζ ↦ hc _ (hdom ζ hζ))
      (fun ζ hζ ↦ hF _ (by rw [fst_positiveEndCoord_positiveEndChart]; exact hR₁.trans hζ.le))
      hux hδ (fun z ↦ by positivity)
      (fun ζ _ ↦ by
        rw [fderiv_add_const, det_fderiv_positiveEndChart, endCenter_inf, sub_zero,
          TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero, add_sub_cancel_right])

/-- **The output end of the capped family.** Far out on the output end, read in the chart
`c + φ'_∞` in which the capped datum is `H_∞(t) dt`, the formal adjoint of the linearized operator
of the capped datum controls the energy of covector fields against the weight `ρ⁻¹`: this is the
end estimate in a holomorphic end chart, whose weight `4π² |w - c|²`, the Jacobian of the chart,
is at most `32π² ρ⁻¹` there. -/
private theorem exists_forall_setIntegral_covectorPullback_le_capped_inf (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : ℝ≥0}
    (hX : LipschitzWith Λ (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H inf)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H inf t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H inf) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart inf ζ + (c, 0)))
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) x
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1 ∧
        R < (positiveEndCoord inf (z - (c, 0))).1} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, (cappedCylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2 := by
  have h2 : (2 : ℝ) ≤ max R₁ 2 := le_max_right _ _
  obtain ⟨C, R, hR, hest⟩ := exists_forall_setIntegral_covectorPullback_le_capped_inf_chart ω hH
    hHs hL hc₀ hc₁ hX hx hnd hJe hJex hJeq hJ hu₂ hc hF hux hδ
  refine ⟨max C 0 * (32 * π ^ 2), R, fun η hη hηc hηR ↦ ?_⟩
  have hηU : tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} := fun z hz ↦ (hηR hz).1
  have hpos (z : ℝ × ℝ) (hz : z ∈ tsupport η) : 0 < (positiveEndCoord inf (z - (c, 0))).1 :=
    (by linarith : (0 : ℝ) < R).trans (hηR hz).2
  -- `η` vanishes in the chart outside a finite band `(R, b) × ℝ`.
  obtain ⟨N, hN⟩ := exists_forall_fst_positiveEndCoord_inf_sub_le (c := c) hηc.isCompact
  have hs (s t : ℝ) :
      (positiveEndCoord inf (positiveEndChart inf (s, t) + (c, 0) - (c, 0))).1 = s := by
    rw [add_sub_cancel_right, fst_positiveEndCoord_positiveEndChart]
  have hvan (s t : ℝ) (hs' : s ∉ Ioo R (max N R + 1)) :
      η (positiveEndChart inf (s, t) + (c, 0)) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ hs' ⟨?_, ?_⟩
    · have h₁ := (hηR h).2
      rwa [hs] at h₁
    · have h₁ := hN _ h
      rw [hs] at h₁
      linarith [le_max_left N R]
  have hint {w : ℝ × ℝ → ℝ}
      (hw : ContinuousOn w {z | Complex.equivRealProdCLM.symm z ≠ 1}) :=
    integrable_mul_norm_floerLinearizationAdjoint_sq_cappedExchangePerturbation (c := c) ω hH hHs
      hL hJ hu hw hη hηc hηU
  -- On the support of `η` the weight `4π² |w - c|²` of the end estimate is at most `32π² ρ⁻¹`.
  have hw (z : ℝ × ℝ) (hz : z ∈ tsupport η) :
      4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 ≤
        32 * π ^ 2 * (cappedCylindricalWeight z)⁻¹ := by
    have h := norm_sub_sq_le_inv_cappedCylindricalWeight hc₀ hc₁ (hpos z hz)
    nlinarith [Real.pi_pos]
  calc _ = ∫ ζ in Ioi (max R₁ 2) ×ˢ Icc (0 : ℝ) 1, sobolevDensity
        (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioi.prod measurableSet_Icc) (prod_mono (Ioi_subset_Ioi h2) subset_rfl)
          fun ζ hζ ↦ ?_
        have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc
          (fun s t hs ↦ covectorPullback_eq_zero_of_apply_eq_zero
            (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u (hvan s t hs))
          fun h ↦ hζ.2 ⟨hR.trans_le h.1, hζ.1.2⟩
        rw [sobolevDensity_congr_of_eventuallyEq h, sobolevDensity_zero]
    _ ≤ C * ∫ z, 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c‖ ^ 2 *
        ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2 :=
        hest hη hvan (hint (Continuous.continuousOn (by fun_prop)))
    _ ≤ _ := mul_integral_mul_norm_floerLinearizationAdjoint_sq_le ω
        (w₂ := fun z ↦ (cappedCylindricalWeight z)⁻¹) (fun z ↦ by positivity) hw
        (hint continuousOn_inv_cappedCylindricalWeight) C

/-- **The semi-Fredholm estimate of the formal adjoint along the input-exchange family capped at
`0`.** Let `H_q` be jointly `C²` period-one Hamiltonians, let `L > 4` and `c ∈ [0, 1]`, and let
`K_c` be the member `c` of the input-exchange family capped at `0`,
`TauCeti.Floer.cappedExchangePerturbation H L c`, with components `K_s`, `K_t`, on the capped
surface `ℂ ∖ {1}`. Suppose that on the input end at `1` and on the output end the positive end
Hamiltonians `H'_q` have globally Lipschitz suspended vector fields, and let `x_q` be orbits of
`H'_q` starting at nondegenerate fixed points of the time-one maps. Let `J` be almost complex
structures on `ℂ ∖ {1}` that far out on these two ends, beyond a height `R₁`, are `C²` families
`J_q(t)` compatible along `x_q`: in the positive end chart `φ'_1` on the input end and in the
recentred end chart `c + φ'_∞` on the output end, where `K_c` is `H_q(t) dt`. Let `u` be a `C¹`
map on `ℂ ∖ {1}`, along which `J` is `C¹` and compatible, that is `C²` and solves the Floer
equation for `(J, K_c)` beyond `R₁` on the two ends, and whose ends, read in these end charts,
converge uniformly to the orbits `x_q` while the slice defects tend uniformly to zero. Then there
are `C ≥ 0` and `T ≥ 1` such that every `C²` covector field `η` with compact support in
`ℂ ∖ {1}` satisfies

`∑_{e} ∫_{(T, ∞) × [0, 1]} (‖∂s η'_e‖² + ‖∂t η'_e‖² + ‖η'_e‖²)`
`  + ∫_{Σ_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{Σ_{T + 1}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the data `(J, K_c)`, where
`η'_e` is `η` read in the chart of the end `e` as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`), `Σ_T` is the annulus `exp (-2πT) / 2 ≤ |w - 1|`,
`|w - c| ≤ 2 exp (2πT)`, and `ρ` is the cylindrical weight of the capped surface
(`TauCeti.Floer.cappedCylindricalWeight`). This is the counterpart for `D_u^*`, whose kernel is the
cokernel of `D_u`, of
`exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add`. -/
theorem exists_forall_le_mul_integral_floerLinearizationAdjoint_cappedExchangePerturbation_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : Puncture → ℝ≥0}
    (hX : ∀ q (_ : q ≠ zero), LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q, q ≠ zero → ∀ t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q (hq : q ≠ zero), IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q hq) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 2 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q, q ≠ zero → ∀ t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart one ζ))
    (hu₂_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart inf ζ + (c, 0)))
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 1 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} →
      (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart one)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | Real.exp (-(2 * π * T)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ∧
          ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * T)},
          sobolevDensity η z ≤
        C * ((∫ z, (cappedCylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z‖ ^ 2) +
          ∫ z in {z | Real.exp (-(2 * π * (T + 1))) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ∧
            ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * (T + 1))},
            ‖η z‖ ^ 2) := by
  obtain ⟨Cin, Rin, hin⟩ := exists_forall_setIntegral_covectorPullback_le_capped_one ω hH hHs hL
    hc₀ hc₁ (hX one (by decide)) (hx one (by decide)) (hnd one (by decide)) (hJe one (by decide))
    (hJex one (by decide)) hJeq hJ hu hu₂ hc hF hux hδ
  obtain ⟨Cout, Rout, hout⟩ := exists_forall_setIntegral_covectorPullback_le_capped_inf ω hH hHs
    hL hc₀ hc₁ (hX inf (by decide)) (hx inf (by decide)) (hnd inf (by decide))
    (hJe inf (by decide)) (hJex inf (by decide)) hJeq_inf hJ hu hu₂_inf hc hF_inf hux_inf hδ_inf
  exact
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_capped
    ω hc₀ hc₁ hJ (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) Complex.I) hu
    hc (fun z ↦ inv_nonneg.2 (cappedCylindricalWeight_nonneg z))
    continuousOn_inv_cappedCylindricalWeight
    (fun z hz ↦ inv_pos.2 (isWeight_cappedCylindricalWeight.pos z hz)) hin hout

end TauCeti.SymplecticForm
