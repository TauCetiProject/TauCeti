/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Sobolev
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Chart
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Cokernel
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The linearized Floer operator on spheres with moving input ends is Fredholm

The associativity of the pair-of-pants product is proved through a family of spheres with finitely
many moving input ends, with centers `c i` and nonzero scales `a i`, and an output end at `∞`,
carrying the Hamiltonian perturbations `K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`.
The sphere minus its input punctures is the plane minus the centers, `U = ℂ ∖ {c i}`. Along a map
`u` that solves the Floer equation far out on the ends and converges there to nondegenerate
orbits, the realization `D_u : W^{1,2}_0(U, V) → L²(U, V)` of the linearized Floer operator, for
the weight `TauCeti.Floer.movingEndsWeight c`, has finite-dimensional kernel and closed range
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds`,
`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_of_movingEnds`). This file
proves that its cokernel is finite-dimensional too, so that `D_u` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_movingEnds`).

* **The `L²` norm on the ends.** The chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of the input
  end `i` and the positive end chart `φ'_∞` of the output end are holomorphic, so a covector field
  `η` and its pullback `η' = η (ψ ·) ∘ (a + b J)` to an end satisfy
  `det (dψ) ‖η ∘ ψ‖² ≤ (1 + ‖J‖)² ‖η'‖²`
  (`TauCeti.Floer.det_mul_norm_sq_le_and_norm_covectorPullback_realChart_sq_le`). Since `J` is
  bounded along `u` on `U`, changing variables on the bands of the ends bounds the `L²` norm of `η`
  on `U` by the energies on the left of the semi-Fredholm estimate of the formal adjoint `D_u^*`,
  `exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearizationAdjoint_add_of_movingEnds`
  in the namespace `TauCeti.SymplecticForm`.
* **Cutoffs.** For large `n`, the cutoff `χ_n = λ_n - ∑_i b_{n,i}` is `1` on the part of `U` where
  `|w| ≤ n` and `|w - c i| ≥ 2 / n`, and vanishes near the centers and where `|w| ≥ 2n`. Here
  `λ_n` is a radial cutoff at scale `n` and `b_{n,i}` a radial cutoff about `c i` at scale `1 / n`,
  so `|dχ_n|` is `O(1 / n)` on the annulus `n ≤ |w| ≤ 2n` and `O(n)` on the annuli
  `1 / n ≤ |w - c i| ≤ 2 / n`. The weight `ρ` of the moving ends dominates `|w - c i|⁻²` and
  `(1 + |w|²)⁻¹`, so `ρ⁻¹ |dχ_n|²` is bounded uniformly in `n`, and supported where the height
  `|w| + ∑_i 2 / |w - c i|` is at least `n`.
* **Cokernel elements are controlled on a truncation.** For a cokernel element `η` (`C²` on `U`,
  `D_u^* η = 0`, square-integrable on `U`), the adjoint estimate for `χ_n η`, with the weight
  `K ρ⁻¹`, bounds `∫_U ‖η‖²` by a constant times `∫_{Σ_{T+1}} ‖η‖²` plus terms controlled by the
  `L²` norm of `η` where the height is at least `n`, which tends to zero. Peetre's argument,
  `finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_setIntegral_norm_sq_le` in
  the namespace `TauCeti.SymplecticForm`, then shows that the orthogonal complement of the range
  is finite-dimensional.

The target is a symplectic vector space. The index of `D_u` is not computed here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendices B and C, on the formal adjoint and
  the Fredholm property of real Cauchy–Riemann operators on punctured Riemann surfaces.
-/

public section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold Topology
open TauCeti.Complex (realChart realChart_apply equivRealProdCLM_symm_realChart)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ}

/-! ### The `L²` norm from the energies on the ends -/

/-- The positive end chart of `q` is the real chart of `w ↦ φ_q(ε_q w)`, where `ε_q` is the sign
of the end. -/
private theorem positiveEndChart_eq_realChart (q : Puncture) :
    positiveEndChart q = realChart fun w ↦ q.cylindricalEndLift ((q.endSign : ℂ) * w) := by
  funext z
  rw [positiveEndChart_apply, endChart_eq_realChart, realChart_apply, realChart_apply, map_smul,
    Complex.real_smul]

/-- Changing variables along a chart `φ` that is injective on `S`: if
`|det dφ| F ∘ φ ≤ G` on `S`, then the lower integral of `F` over `φ(S)` is at most that of `G`
over `S`. -/
private theorem setLIntegral_image_le {φ : ℝ × ℝ → ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hφ : ∀ g : ℝ × ℝ → ℝ≥0∞, ∫⁻ w in φ '' S, g w =
      ∫⁻ ζ in S, ENNReal.ofReal |(fderiv ℝ φ ζ).det| * g (φ ζ))
    {F G : ℝ × ℝ → ℝ} (hpt : ∀ ζ ∈ S, |(fderiv ℝ φ ζ).det| * F (φ ζ) ≤ G ζ) :
    ∫⁻ w in φ '' S, ENNReal.ofReal (F w) ≤ ∫⁻ ζ in S, ENNReal.ofReal (G ζ) := by
  rw [hφ]
  refine setLIntegral_mono' hS fun ζ hζ ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hpt ζ hζ)

omit [FiniteDimensional ℝ V] in
/-- If `det dφ ‖η ∘ φ‖² ≤ (1 + ‖J‖)² ‖η'‖²` with `det dφ > 0` and `‖J‖ ≤ B`, then
`|det dφ| ‖η ∘ φ‖²` is at most `(1 + B)²` times the energy density of the pulled-back form. -/
private theorem abs_det_mul_norm_sq_le_mul_sobolevDensity {φ : ℝ × ℝ → ℝ × ℝ} {ζ : ℝ × ℝ}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {η' : ℝ × ℝ → V →L[ℝ] ℝ} {NJ B : ℝ} (hdet : 0 < (fderiv ℝ φ ζ).det)
    (h : (fderiv ℝ φ ζ).det * ‖η (φ ζ)‖ ^ 2 ≤ (1 + NJ) ^ 2 * ‖η' ζ‖ ^ 2) (hNJ : 0 ≤ NJ)
    (hB : NJ ≤ B) :
    |(fderiv ℝ φ ζ).det| * ‖η (φ ζ)‖ ^ 2 ≤ (1 + B) ^ 2 * sobolevDensity η' ζ := by
  rw [abs_of_pos hdet]
  refine h.trans (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 2) ?_ (sq_nonneg _)
    (sq_nonneg _))
  rw [sobolevDensity_apply]
  nlinarith [sq_nonneg ‖fderiv ℝ η' ζ stdComplexLineReal‖,
    sq_nonneg ‖fderiv ℝ η' ζ stdComplexLineImag‖]

/-- **The `L²` norm on the sphere from the energies.** Let the discs `‖w - c i‖ < ‖a i‖ / 2` of the
input ends be pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, with nonzero scales, let
`J` and `u` be `C¹` along `u` on the plane minus the centers, with `‖J(z, u z)‖ ≤ B` there, and let
`T ≥ 1`. Then for every `C¹` covector field `g` with compact support in the plane minus the
centers, `∫ ‖g‖²` over the plane minus the centers is at most `(1 + B)²` times the energies of the
pulled-back forms on the half-cylinders `s > T` of the ends, plus the `W^{1,2}` energy of `g` on
the truncation `Σ_T`. -/
private theorem setIntegral_norm_sq_le_of_movingEnds (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    {B : ℝ} (hB : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) {T : ℝ} (hT : 1 ≤ T) :
    ∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ‖g z‖ ^ 2 ≤
      (1 + B) ^ 2 * ((∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u g) ζ) +
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart inf)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u g) ζ) +
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
        sobolevDensity g z := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set S : Set (ℝ × ℝ) := Ioi T ×ˢ Ico 0 1
  have hS : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ico
  have hTr := isCompact_preimage_puncturedSphereTruncation c a T
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- The energies on the bands are finite and nonnegative.
  set E : ι → ℝ := fun i ↦ ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
    (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) J' u g) ζ
  set Eo : ℝ := ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
    sobolevDensity (covectorPullback (positiveEndChart inf) J' u g) ζ
  set Ec : ℝ := ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
    sobolevDensity g z
  have hP : MeasurableSet (Ioi T ×ˢ Icc (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Icc
  have hE0 (i : ι) : 0 ≤ E i := setIntegral_nonneg hP fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  have hEo0 : 0 ≤ Eo := setIntegral_nonneg hP fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  have hEc0 : 0 ≤ Ec := setIntegral_nonneg hTr.measurableSet fun z _ ↦ sobolevDensity_nonneg _ z
  have hband {G : ℝ × ℝ → ℝ} (hG : IntegrableOn G (Ioi T ×ˢ Icc 0 1)) (hG0 : ∀ ζ, 0 ≤ G ζ) :
      ∫⁻ ζ in S, ENNReal.ofReal ((1 + B) ^ 2 * G ζ) ≤
        ENNReal.ofReal ((1 + B) ^ 2 * ∫ ζ in Ioi T ×ˢ Icc 0 1, G ζ) := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hG.const_mul _)
      (ae_of_all _ fun ζ ↦ by have := hG0 ζ; positivity)]
    exact lintegral_mono_set (prod_mono subset_rfl Ico_subset_Icc_self)
  -- The pointwise comparison on the band of an input end.
  have hin (i : ι) (ζ : ℝ × ℝ) (hζ : ζ ∈ S) :
      |(fderiv ℝ (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ).det| *
          ‖g (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)‖ ^ 2 ≤
        (1 + B) ^ 2 * sobolevDensity (covectorPullback
          (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) J' u g) ζ := by
    have hf := hasDerivAt_add_mul_cylindricalEndLift (c i) (a i) (Complex.equivRealProdCLM.symm ζ)
    have hne (j : ι) : Complex.equivRealProdCLM.symm
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) ≠ c j := by
      rw [equivRealProdCLM_symm_realChart]
      exact add_mul_cylindricalEndLift_ne hsep (ha i)
        (by simpa using (zero_lt_one.trans_le hT).trans hζ.1) j
    have hdet : 0 < (fderiv ℝ (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ).det := by
      rw [det_fderiv_realChart_add_mul_cylindricalEndLift]
      have := sub_ne_zero.2 (hne i)
      positivity
    have hf' : a i * deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ) ≠ 0 :=
      Complex.normSq_pos.1 (by rw [← TauCeti.Complex.det_fderiv_realChart hf]; exact hdet)
    exact abs_det_mul_norm_sq_le_mul_sobolevDensity hdet
      (det_mul_norm_sq_le_and_norm_covectorPullback_realChart_sq_le hf hf' J u g).1 (norm_nonneg _)
      (hB _ hne)
  -- The pointwise comparison on the band of the output end.
  have hφ := positiveEndChart_eq_realChart inf
  have hon (ζ : ℝ × ℝ) (hζ : ζ ∈ S) :
      |(fderiv ℝ (positiveEndChart inf) ζ).det| * ‖g (positiveEndChart inf ζ)‖ ^ 2 ≤
        (1 + B) ^ 2 * sobolevDensity (covectorPullback (positiveEndChart inf) J' u g) ζ := by
    have hne : ∀ j, Complex.equivRealProdCLM.symm (positiveEndChart inf ζ) ≠ c j :=
      equivRealProdCLM_symm_positiveEndChart_inf_ne
        (fun i ↦ (le_add_of_nonneg_right (by positivity)).trans (hout i))
        (hT.trans_lt hζ.1)
    have hdet := det_fderiv_positiveEndChart_pos inf ζ
    have hf : HasDerivAt (fun w ↦ inf.cylindricalEndLift ((inf.endSign : ℂ) * w)) _
        (Complex.equivRealProdCLM.symm ζ) :=
      (inf.hasDerivAt_cylindricalEndLift _).comp _
        ((hasDerivAt_id (Complex.equivRealProdCLM.symm ζ)).const_mul (inf.endSign : ℂ))
    have hf' := Complex.normSq_pos.1
      (by rw [← TauCeti.Complex.det_fderiv_realChart hf, ← hφ]; exact hdet)
    have h := (det_mul_norm_sq_le_and_norm_covectorPullback_realChart_sq_le hf hf' J u g).1
    rw [← hφ] at h
    exact abs_det_mul_norm_sq_le_mul_sobolevDensity hdet h (norm_nonneg _) (hB _ hne)
  -- Cover the sphere by the truncation and the bands, and compare the lower integrals.
  have hFi : Integrable fun z ↦ ‖g z‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖g z‖ ^ 2)
      (hg.continuous.norm.pow 2) (hgc.comp_left (g := fun v : V →L[ℝ] ℝ ↦ ‖v‖ ^ 2) (by simp))
  have hlin : ENNReal.ofReal (∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
      ‖g z‖ ^ 2) ≤
      ENNReal.ofReal Ec + ((∑ i, ENNReal.ofReal ((1 + B) ^ 2 * E i)) +
        ENNReal.ofReal ((1 + B) ^ 2 * Eo)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFi.integrableOn (ae_of_all _ fun z ↦ by positivity)]
    refine (lintegral_mono_set (subset_preimage_puncturedSphereTruncation_union ha T)).trans <|
      (lintegral_union_le _ _ _).trans (add_le_add ?_ ((lintegral_union_le _ _ _).trans
        (add_le_add ((lintegral_iUnion_le _ _).trans ?_) ?_)))
    · rw [ofReal_integral_eq_lintegral_ofReal
        ((continuous_sobolevDensity hg).continuousOn.integrableOn_compact hTr)
        (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z)]
      refine lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal ?_
      rw [sobolevDensity_apply]
      nlinarith [sq_nonneg ‖fderiv ℝ g z stdComplexLineReal‖,
        sq_nonneg ‖fderiv ℝ g z stdComplexLineImag‖]
    · rw [tsum_fintype]
      refine Finset.sum_le_sum fun i _ ↦ (setLIntegral_image_le hS (fun G ↦
        lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
          (fun ζ _ ↦ (TauCeti.Complex.hasFDerivAt_realChart (hasDerivAt_add_mul_cylindricalEndLift
            (c i) (a i) _)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
          ((injOn_realChart_add_mul_cylindricalEndLift (ha i)).mono
            (prod_mono subset_rfl (by rw [zero_add]))) G) (hin i)).trans ?_
      exact hband (integrableOn_sobolevDensity_covectorPullback_realChart_of_movingEnds ha hJ hu
        hg hgc hgU i T) (sobolevDensity_nonneg _)
    · exact (setLIntegral_image_le hS (fun G ↦ lintegral_image_positiveEndChart inf
        measurableSet_Ioi G) hon).trans (hband
          (integrableOn_sobolevDensity_covectorPullback_positiveEndChart_of_movingEnds ha hJ hu hg
            hgc hgU T) (sobolevDensity_nonneg _))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by have := hE0 i; positivity),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ ↦ by have := hE0 i; positivity)
      (by positivity), ← ENNReal.ofReal_add hEc0 (by
        have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ by
          have := hE0 i
          exact (by positivity : 0 ≤ (1 + B) ^ 2 * E i)
        positivity)] at hlin
  have hle := (ENNReal.ofReal_le_ofReal_iff (by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ by
      have := hE0 i
      exact (by positivity : 0 ≤ (1 + B) ^ 2 * E i)
    positivity)).1 hlin
  rw [← Finset.mul_sum] at hle
  linarith

/-! ### `J` is bounded along `u` -/

/-- **`J` is bounded along `u` on a sphere with moving input ends.** Let `J` be continuous along
`u` on the plane minus the centers, equal beyond `s = 2` to continuous families `J_e i (t)` in the
chart of the input end `i` and `J_out (t)` in the positive end chart of the output end, and let
the loops of `u` on the ends converge uniformly to loops continuous on `[0, 1]`. Then
`‖J(z, u z)‖` is bounded on the plane minus the centers. -/
private theorem exists_forall_norm_le_of_movingEnds {ι : Type*} [Finite ι] {c a : ι → ℂ}
    (ha : ∀ i, a i ≠ 0) {x : ι → ℝ → V}
    (hx : ∀ i, ContinuousOn (x i) (Icc 0 1)) {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, Continuous fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xout : ℝ → V} (hxout : ContinuousOn xout (Icc 0 1))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : Continuous fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ContinuousAt (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) z)
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1)) :
    ∃ B, ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B := by
  have := Fintype.ofFinite ι
  -- Far out on an end the loops of `u` stay within `1` of the orbit, which is bounded.
  have hend {y : ℝ → V} (hy : ContinuousOn y (Icc 0 1)) {Jq : ℝ → V → AlmostComplexStructure V}
      (hJq : Continuous fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
      {φ : ℝ × ℝ → ℝ × ℝ}
      (hφ : TendstoUniformlyOn (fun s t ↦ u (φ (s, t))) y atTop (Icc 0 1)) :
      ∃ S Bq, ∀ ζ : ℝ × ℝ, S ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
        ‖(Jq ζ.2 (u (φ ζ))).toLinearMap.toContinuousLinearMap‖ ≤ Bq := by
    obtain ⟨S, hS⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hφ) 1 one_pos)
    obtain ⟨X, hX⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
    obtain ⟨Bq, hBq⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_Icc.prod (isCompact_closedBall (0 : V) (X + 1))) hJq.continuousOn
    refine ⟨S, Bq, fun ζ hζ ht ↦ hBq (ζ.2, u (φ ζ)) ⟨ht, ?_⟩⟩
    have h := hS ζ.1 hζ ζ.2 ht
    rw [Prod.mk.eta, dist_eq_norm] at h
    rw [mem_closedBall_zero_iff]
    linarith [hX ζ.2 ht, norm_sub_norm_le (u (φ ζ)) (y ζ.2), norm_sub_rev (y ζ.2) (u (φ ζ))]
  choose S Bi hSB using fun i ↦ hend (hx i) (hJe i) (hux i)
  obtain ⟨So, Bo, hSBo⟩ := hend hxout hJout huxout
  set T : ℝ := 2 + ∑ i, |S i| + |So|
  have hsum : 0 ≤ ∑ i, |S i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hST (i : ι) : S i ≤ T := by
    have := Finset.single_le_sum (f := fun i ↦ |S i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
    linarith [le_abs_self (S i), abs_nonneg So]
  have hSoT : So ≤ T := by linarith [le_abs_self So]
  have h2T : 2 ≤ T := by linarith [abs_nonneg So]
  obtain ⟨B₀, hB₀⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_preimage_puncturedSphereTruncation c a T) fun z hz ↦
      (hJ z (preimage_puncturedSphereTruncation_subset ha T hz)).continuousWithinAt
  have hBsum : 0 ≤ ∑ i, |Bi i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  refine ⟨|B₀| + ∑ i, |Bi i| + |Bo|, fun z hz ↦ ?_⟩
  rcases subset_preimage_puncturedSphereTruncation_union ha T hz with hzT | hzi | hzo
  · linarith [hB₀ z hzT, le_abs_self B₀, abs_nonneg Bo]
  · obtain ⟨i, ζ, hζ, rfl⟩ := mem_iUnion.1 hzi
    have h1 : T < ζ.1 := hζ.1
    rw [hJeq i ζ (by linarith)]
    have := Finset.single_le_sum (f := fun i ↦ |Bi i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
    linarith [hSB i ζ (by linarith [hST i]) (Ico_subset_Icc_self hζ.2), le_abs_self (Bi i),
      abs_nonneg B₀, abs_nonneg Bo]
  · obtain ⟨ζ, hζ, rfl⟩ := hzo
    have h1 : T < ζ.1 := hζ.1
    rw [hJoutq ζ (by linarith)]
    linarith [hSBo ζ (by linarith) (Ico_subset_Icc_self hζ.2), le_abs_self Bo, abs_nonneg B₀]

/-! ### The weight of the adjoint estimate -/

/-- The weight of the moving ends is positive everywhere. -/
private theorem movingEndsWeight_pos (c : ι → ℂ) (z : ℝ × ℝ) : 0 < movingEndsWeight c z := by
  rw [movingEndsWeight_apply]
  positivity

/-- At a point `w ≠ 0` with `2 |c i| ≤ |w|` for every center, `ρ(w) |w|² ≤ 4 |ι| + 1` for the
weight `ρ` of the moving ends. -/
private theorem movingEndsWeight_mul_norm_sq_le {z : ℝ × ℝ}
    (hz0 : Complex.equivRealProdCLM.symm z ≠ 0)
    (hz : ∀ i, 2 * ‖c i‖ ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    movingEndsWeight c z * ‖Complex.equivRealProdCLM.symm z‖ ^ 2 ≤ 4 * Fintype.card ι + 1 := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : 0 < ‖w‖ := norm_pos_iff.2 hz0
  have hi (i : ι) : (‖w - c i‖ ^ 2)⁻¹ * ‖w‖ ^ 2 ≤ 4 := by
    have h : ‖w‖ / 2 ≤ ‖w - c i‖ := by linarith [hz i, norm_sub_norm_le w (c i)]
    have hwc : 0 < ‖w - c i‖ := by linarith
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : (1 + ‖w‖ ^ 2)⁻¹ * ‖w‖ ^ 2 ≤ 1 := by
    rw [inv_mul_eq_div, div_le_one (by positivity)]
    linarith
  rw [movingEndsWeight_apply, add_mul, Finset.sum_mul]
  calc _ ≤ (∑ _i : ι, (4 : ℝ)) + 1 := add_le_add (Finset.sum_le_sum fun i _ ↦ hi i) h1
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **The weight of the adjoint estimate.** There is `K > 0` such that `K ρ⁻¹`, for the weight `ρ`
of the moving ends, is at least the Jacobian weights `|p - c i|²` and `|p|²` of the end charts
beyond `s = 2`. -/
private theorem exists_weight_of_movingEnds (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
        ‖Complex.equivRealProdCLM.symm
            (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) - c i‖ ^ 2 ≤
          K * (movingEndsWeight c
            (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))⁻¹) ∧
      ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ‖Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)‖ ^ 2 ≤
        K * (movingEndsWeight c (positiveEndChart inf ζ))⁻¹ := by
  set K₁ : ι → ℝ := fun i ↦ (∑ j, (‖a i‖ / ‖a j‖) ^ 2) + ‖a i‖ ^ 2 / 4
  have hK₁ (i : ι) : 0 ≤ K₁ i := by positivity
  have hsum : 0 ≤ ∑ i, K₁ i := Finset.sum_nonneg fun i _ ↦ hK₁ i
  refine ⟨(∑ i, K₁ i) + (4 * Fintype.card ι + 1), by positivity, fun i ζ hζ ↦ ?_, fun ζ hζ ↦ ?_⟩
  · set p := realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ
    have hd := norm_equivRealProdCLM_symm_realChart_add_mul_cylindricalEndLift_sub (c i) (a i) ζ
    have hapos := norm_pos_iff.2 (ha i)
    have hne : Complex.equivRealProdCLM.symm p ≠ c i := by
      rw [← sub_ne_zero, ← norm_pos_iff, hd]
      positivity
    have hexp : Real.exp (-(2 * π * ζ.1)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
    have h : movingEndsWeight c p * ‖Complex.equivRealProdCLM.symm p - c i‖ ^ 2 ≤ K₁ i :=
      movingEndsWeight_mul_norm_sub_sq_le ha hsep hne (by rw [hd]; nlinarith)
    have hi := Finset.single_le_sum (f := K₁) (fun i _ ↦ hK₁ i) (Finset.mem_univ i)
    rw [← div_eq_mul_inv, le_div_iff₀ (movingEndsWeight_pos c p), mul_comm]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  · set p := positiveEndChart inf ζ
    have hnorm := norm_equivRealProdCLM_symm_positiveEndChart_inf ζ.1 ζ.2
    rw [Prod.mk.eta] at hnorm
    have hx : 2 ≤ Real.exp (2 * π) := by linarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
    have h₂ : Real.exp (2 * π) * Real.exp (2 * π) ≤ Real.exp (2 * π * ζ.1) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [pi_pos])
    have h := movingEndsWeight_mul_norm_sq_le (c := c) (z := p)
      (by rw [← norm_pos_iff, hnorm]; positivity)
      fun i ↦ by rw [hnorm]; nlinarith [hout i, norm_nonneg (a i), Real.exp_pos (2 * π)]
    rw [← div_eq_mul_inv, le_div_iff₀ (movingEndsWeight_pos c p)]
    nlinarith

/-! ### Cutoffs -/

/-- The height `|w| + ∑ i 2 / |w - c i|` of a point of the plane: it is large exactly near the
punctures `c i` and `∞` of the sphere with moving input ends. -/
private noncomputable def movingEndsHeight (c : ι → ℂ) (z : ℝ × ℝ) : ℝ :=
  ‖Complex.equivRealProdCLM.symm z‖ + ∑ i, 2 / ‖Complex.equivRealProdCLM.symm z - c i‖

private theorem measurable_movingEndsHeight (c : ι → ℂ) : Measurable (movingEndsHeight c) :=
  Complex.equivRealProdCLM.symm.continuous.norm.measurable.add
    (Finset.measurable_sum _ fun _ _ ↦ measurable_const.div
      (Complex.equivRealProdCLM.symm.continuous.sub continuous_const).norm.measurable)

/-- **Cutoffs on a sphere with moving input ends.** There is `M` such that for every large `n`
there is a smooth `χ` with compact support in the plane minus the centers, equal to `1` where
`|w| ≤ n` and `|w - c i| ≥ 2 / n` for every `i`, with `ρ^{-1/2} |dχ| ≤ M` on the plane minus the
centers, for the weight `ρ` of the moving ends, and `dχ = 0` where the height is less than `n`. -/
private theorem exists_cutoff_of_movingEnds (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) :
    ∃ M, ∀ᶠ n : ℕ in atTop, ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ∧
      (∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ n →
        (∀ i, 2 / (n : ℝ) ≤ ‖Complex.equivRealProdCLM.symm z - c i‖) → χ z = 1) ∧
      ∀ z, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
        (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ χ z‖ ≤
          {z | (n : ℝ) ≤ movingEndsHeight c z}.indicator (fun _ ↦ M) z := by
  set E := ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖
  refine ⟨6 * E + Fintype.card ι * (4 * E), ?_⟩
  set N : ℝ := 1 + ∑ i, (‖c i‖ + 2 + 6 / ‖a i‖)
  filter_upwards [eventually_ge_atTop ⌈N⌉₊] with n hn
  have hnN : N ≤ n := (Nat.le_ceil N).trans (by exact_mod_cast hn)
  have hci (i : ι) : ‖c i‖ + 2 + 6 / ‖a i‖ ≤ n := by
    have := Finset.single_le_sum (f := fun i ↦ ‖c i‖ + 2 + 6 / ‖a i‖)
      (fun i _ ↦ by positivity) (Finset.mem_univ i)
    linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
      (by positivity : (0 : ℝ) ≤ ‖c i‖ + 2 + 6 / ‖a i‖)
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hδ : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have hδ1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hδ0 : 0 < (n : ℝ)⁻¹ := inv_pos.2 hn0
  obtain ⟨θ, hθs, -, hθ1, hθ0, hθd0, hθd2, hθM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hn0
  obtain ⟨β, hβs, -, hβ1, hβ0, hβd0, hβd2, hβM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hδ0
  simp only [ContinuousLinearEquiv.coe_coe] at hθ1 hθ0 hθd0 hθd2 hβ1 hβ0 hβd0 hβd2
  set c' : ι → ℝ × ℝ := fun i ↦ Complex.equivRealProdCLM (c i)
  have hc' (z : ℝ × ℝ) (i : ι) :
      ‖Complex.equivRealProdCLM.symm (z - c' i)‖ = ‖Complex.equivRealProdCLM.symm z - c i‖ := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  have hβ0' (i : ι) (z : ℝ × ℝ) (h : 2 / (n : ℝ) ≤ ‖Complex.equivRealProdCLM.symm z - c i‖) :
      β (z - c' i) = 0 :=
    hβ0 _ (by rw [hc', ← div_eq_mul_inv]; exact h)
  -- The cutoff `χ = θ - ∑ i β (· - c' i)`.
  set χ : ℝ × ℝ → ℝ := fun z ↦ θ z - ∑ i, β (z - c' i)
  have hχs : ContDiff ℝ 2 χ := (hθs.of_le (by simp)).sub
    (ContDiff.sum fun i _ ↦ (hβs.of_le (by simp)).comp (contDiff_id.sub contDiff_const))
  have hone (z : ℝ × ℝ) (hz : ‖Complex.equivRealProdCLM.symm z‖ ≤ n)
      (hzc : ∀ i, 2 / (n : ℝ) ≤ ‖Complex.equivRealProdCLM.symm z - c i‖) : χ z = 1 := by
    simp only [χ, hθ1 z hz, Finset.sum_eq_zero fun i _ ↦ hβ0' i z (hzc i), sub_zero]
  -- `χ` vanishes off the compact set `K`, near the centers and where `|w| ≥ 2n`.
  set K : Set (ℝ × ℝ) := {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * n} ∩
    ⋂ i, {z | (n : ℝ)⁻¹ ≤ ‖Complex.equivRealProdCLM.symm z - c i‖}
  have hKc : IsClosed K := (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop))
  have hK : IsCompact K :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * n)).of_isClosed_subset hKc
      fun z hz ↦ hz.1
  have hzero (z : ℝ × ℝ) (hz : z ∉ K) : χ z = 0 := by
    simp only [K, mem_inter_iff, Set.mem_ofPred_eq, mem_iInter, not_and_or, not_forall,
      not_le] at hz
    rcases hz with hz | ⟨i, hi⟩
    · have hβz (j : ι) : β (z - c' j) = 0 := hβ0' j z (by
        have := hci j
        have := norm_sub_norm_le (Complex.equivRealProdCLM.symm z) (c j)
        have h2n : 2 / (n : ℝ) ≤ 2 := div_le_self (by norm_num) hn1
        linarith [norm_nonneg (a j), (by positivity : (0 : ℝ) ≤ 6 / ‖a j‖)])
      simp only [χ, hθ0 z hz.le, Finset.sum_eq_zero fun j _ ↦ hβz j, sub_zero]
    · have hθz : θ z = 1 := hθ1 z (by
        have := hci i
        have := norm_sub_norm_le (Complex.equivRealProdCLM.symm z) (c i)
        linarith [(by positivity : (0 : ℝ) ≤ 6 / ‖a i‖)])
      have hβi : β (z - c' i) = 1 := hβ1 _ ((hc' z i).le.trans hi.le)
      have hβj (j : ι) (hji : j ≠ i) : β (z - c' j) = 0 := hβ0' j z (by
        have hapos := norm_pos_iff.2 (ha i)
        have h6 : 6 ≤ n * ‖a i‖ :=
          (div_le_iff₀ hapos).1 (by linarith [hci i, norm_nonneg (c i)])
        have h6' : 6 * (n : ℝ)⁻¹ ≤ ‖a i‖ := by
          have := mul_le_mul_of_nonneg_right h6 hδ0.le
          rw [mul_comm (n : ℝ), mul_assoc, hδ, mul_one] at this
          exact this
        have hsj : ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖ := hsep hji.symm
        have htri :=
          norm_sub_le_norm_sub_add_norm_sub (c i) (Complex.equivRealProdCLM.symm z) (c j)
        rw [norm_sub_rev (c i) (Complex.equivRealProdCLM.symm z)] at htri
        rw [div_eq_mul_inv]
        linarith [norm_nonneg (a j)])
      simp only [χ, hθz, Finset.sum_eq_single i (fun j _ hji ↦ hβj j hji)
        (fun h ↦ absurd (Finset.mem_univ i) h), hβi, sub_self]
  have hsupp : tsupport χ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
    refine (closure_minimal (fun z hz ↦ by_contra fun h ↦ (mem_support.1 hz) (hzero z h))
      hKc).trans
      fun z hz i h ↦ ?_
    have := (mem_iInter.1 hz.2) i
    simp only [Set.mem_ofPred_eq, h, sub_self, norm_zero] at this
    linarith
  -- The derivative of `χ`, and the bounds of its two parts against the weight.
  have hχd (z : ℝ × ℝ) : fderiv ℝ χ z = fderiv ℝ θ z - ∑ i, fderiv ℝ β (z - c' i) := by
    have hθd : HasFDerivAt θ (fderiv ℝ θ z) z := ((hθs.differentiable (by simp)) z).hasFDerivAt
    have hβd (i : ι) : HasFDerivAt (fun z ↦ β (z - c' i)) (fderiv ℝ β (z - c' i)) z := by
      simpa [Function.comp_def] using ((hβs.differentiable (by simp)) (z - c' i)).hasFDerivAt.comp
        z ((hasFDerivAt_id z).sub_const (c' i))
    exact (hθd.fun_sub (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hβd i)).fderiv
  have hsθ (z : ℝ × ℝ) : (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ θ z‖ ≤ 6 * E := by
    rcases lt_or_ge ‖Complex.equivRealProdCLM.symm z‖ n with h | -
    · rw [hθd0 z h, norm_zero, mul_zero]
      positivity
    rcases lt_or_ge (2 * (n : ℝ)) ‖Complex.equivRealProdCLM.symm z‖ with h' | h'
    · rw [hθd2 z h', norm_zero, mul_zero]
      positivity
    calc _ ≤ (1 + 2 * n) * (2 * E / n) :=
          mul_le_mul ((inv_sqrt_movingEndsWeight_le c z).trans (by linarith)) (hθM z)
            (norm_nonneg _) (by positivity)
      _ = 2 * E / n + 4 * E := by field_simp; ring
      _ ≤ 6 * E := by linarith [div_le_self (by positivity : 0 ≤ 2 * E) hn1]
  have hsβ (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (i : ι) :
      (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ β (z - c' i)‖ ≤ 4 * E := by
    rcases lt_or_ge ‖Complex.equivRealProdCLM.symm z - c i‖ (n : ℝ)⁻¹ with h | -
    · rw [hβd0 _ ((hc' z i).trans_lt h), norm_zero, mul_zero]
      positivity
    rcases lt_or_ge (2 * (n : ℝ)⁻¹) ‖Complex.equivRealProdCLM.symm z - c i‖ with h' | h'
    · rw [hβd2 _ (h'.trans_le (hc' z i).ge), norm_zero, mul_zero]
      positivity
    calc _ ≤ (2 * (n : ℝ)⁻¹) * (2 * E / (n : ℝ)⁻¹) :=
          mul_le_mul ((inv_sqrt_movingEndsWeight_le_norm_sub i (hz i)).trans h') (hβM _)
            (norm_nonneg _) (by positivity)
      _ = 4 * E := by field_simp; ring
  refine ⟨χ, hχs, HasCompactSupport.intro hK hzero, hsupp, hone, fun z hz ↦ ?_⟩
  rw [hχd z]
  by_cases hν : (n : ℝ) ≤ movingEndsHeight c z
  · rw [indicator_of_mem (show z ∈ {z | (n : ℝ) ≤ movingEndsHeight c z} from hν)]
    calc _ ≤ (√(movingEndsWeight c z))⁻¹ *
          (‖fderiv ℝ θ z‖ + ∑ i, ‖fderiv ℝ β (z - c' i)‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
            (add_le_add le_rfl (norm_sum_le _ _))) (by positivity)
      _ = (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ θ z‖ +
          ∑ i, (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ β (z - c' i)‖ := by
          rw [mul_add, Finset.mul_sum]
      _ ≤ 6 * E + ∑ _i : ι, 4 * E :=
          add_le_add (hsθ z) (Finset.sum_le_sum fun i _ ↦ hsβ z hz i)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · rw [indicator_of_notMem (show z ∉ {z | (n : ℝ) ≤ movingEndsHeight c z} from hν)]
    simp only [movingEndsHeight, not_le] at hν
    have hs0 : 0 ≤ ∑ i, 2 / ‖Complex.equivRealProdCLM.symm z - c i‖ :=
      Finset.sum_nonneg fun i _ ↦ by positivity
    have h1 : ‖Complex.equivRealProdCLM.symm z‖ < n := by linarith
    have h2 (i : ι) : 2 * (n : ℝ)⁻¹ < ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      have hpos : 0 < ‖Complex.equivRealProdCLM.symm z - c i‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 (hz i))
      have hle := Finset.single_le_sum (f := fun i ↦ 2 / ‖Complex.equivRealProdCLM.symm z - c i‖)
        (fun i _ ↦ by positivity) (Finset.mem_univ i)
      have hlt : 2 / ‖Complex.equivRealProdCLM.symm z - c i‖ < n := by
        linarith [norm_nonneg (Complex.equivRealProdCLM.symm z)]
      rw [div_lt_iff₀ hpos] at hlt
      nlinarith
    rw [hθd0 z h1, Finset.sum_eq_zero fun i _ ↦ hβd2 _ ((h2 i).trans_le (hc' z i).ge), sub_zero,
      norm_zero, mul_zero]

/-- The formal adjoint `D_u^*` vanishes at a point near which the covector field vanishes. -/
private theorem floerLinearizationAdjoint_eq_zero_of_eventuallyEq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (h : η =ᶠ[𝓝 z] 0) :
    ω.floerLinearizationAdjoint J Ks Kt u η z = 0 := by
  have h' : (fun w ↦ (η w).comp (J w (u w))) =ᶠ[𝓝 z] fun _ ↦ 0 :=
    h.mono fun w hw ↦ by simp [hw]
  rw [floerLinearizationAdjoint_def, h.fderiv_eq, h'.fderiv_eq, h.eq_of_nhds]
  simp

/-- A point of the plane minus the centers of height less than `n` satisfies `|w| ≤ n` and
`|w - c i| ≥ 2 / n` for every `i`. -/
private theorem norm_le_and_forall_le_of_movingEndsHeight_lt {z : ℝ × ℝ}
    (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) {n : ℝ} (hn : 0 < n)
    (hν : movingEndsHeight c z < n) :
    ‖Complex.equivRealProdCLM.symm z‖ ≤ n ∧
      ∀ i, 2 / n ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ := by
  rw [movingEndsHeight] at hν
  have hs0 : 0 ≤ ∑ i, 2 / ‖Complex.equivRealProdCLM.symm z - c i‖ :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  refine ⟨by linarith, fun i ↦ ?_⟩
  have hpos : 0 < ‖Complex.equivRealProdCLM.symm z - c i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hz i))
  have hle := Finset.single_le_sum (f := fun i ↦ 2 / ‖Complex.equivRealProdCLM.symm z - c i‖)
    (fun i _ ↦ by positivity) (Finset.mem_univ i)
  have hlt : 2 / ‖Complex.equivRealProdCLM.symm z - c i‖ < n := by
    linarith [norm_nonneg (Complex.equivRealProdCLM.symm z)]
  rw [div_lt_iff₀ hpos] at hlt
  rw [div_le_iff₀ hn]
  linarith

/-- **The weighted adjoint of a cut-off cokernel element.** Let `J` be `C¹` along a map `u`, `C¹`
on the plane minus the centers, with `‖J(z, u z)‖ ≤ B` there, let `η` be `C¹` there with
`D_u^* η = 0`, and let `χ` be a `C¹` cutoff supported in the plane minus the centers with
`ρ^{-1/2} |dχ| ≤ M` on the points of height at least `n` and `dχ = 0` elsewhere. Then
`K ρ⁻¹ ‖D_u^* (χ η)‖² ≤ K M² (1 + B)² ‖η‖²` at the points of height at least `n`, and the left
side vanishes elsewhere. -/
private theorem mul_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    {B : ℝ} (hB : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiffOn ℝ 1 η {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (hD : ∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
      ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
        η z = 0)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχU : tsupport χ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) {K M n : ℝ}
    (hK : 0 ≤ K)
    (hχd : ∀ z, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      (√(movingEndsWeight c z))⁻¹ * ‖fderiv ℝ χ z‖ ≤
        {z | n ≤ movingEndsHeight c z}.indicator (fun _ ↦ M) z) (z : ℝ × ℝ) :
    K * (movingEndsWeight c z)⁻¹ * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
        (fun z ↦ χ z • η z) z‖ ^ 2 ≤
      K * M ^ 2 * (1 + B) ^ 2 * {z | n ≤ movingEndsHeight c z}.indicator
        ({z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}.indicator fun z ↦ ‖η z‖ ^ 2) z := by
  set U := {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  set Hn := {z | n ≤ movingEndsHeight c z}
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set D := ‖ω.floerLinearizationAdjoint J' Ks Kt u (fun z ↦ χ z • η z) z‖ with hDdef
  have hR0 : 0 ≤ K * M ^ 2 * (1 + B) ^ 2 * Hn.indicator (U.indicator fun z ↦ ‖η z‖ ^ 2) z :=
    mul_nonneg (by positivity)
      (indicator_nonneg (fun _ _ ↦ indicator_nonneg (fun _ _ ↦ by positivity) _) _)
  by_cases hz : z ∈ U
  · have hJd : DifferentiableAt ℝ (fun w ↦ J' w (u w)) z :=
      ((hJ z hz).comp₂ contDiffAt_id (hu z hz)).differentiableAt one_ne_zero
    have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le (Ks := Ks) (Kt := Kt)
      ((hχ.differentiable one_ne_zero) z)
      ((hη.differentiableOn one_ne_zero).differentiableAt
        ((isWeight_movingEndsWeight c).isOpen.mem_nhds hz)) hJd
    rw [hD z hz, norm_zero, mul_zero, zero_add] at hle
    set s := (√(movingEndsWeight c z))⁻¹
    have hs0 : 0 ≤ s := by positivity
    have hs : (movingEndsWeight c z)⁻¹ = s ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (movingEndsWeight_pos c z).le]
    have hB1 : 0 ≤ 1 + B :=
      by linarith [hB z hz, norm_nonneg (J z (u z)).toLinearMap.toContinuousLinearMap]
    -- `s ‖D_u^* (χ η)‖ ≤ s ‖dχ‖ (1 + B) ‖η‖`.
    have h1 : s * D ≤ s * ‖fderiv ℝ χ z‖ * ((1 + B) * ‖η z‖) := by
      calc s * D ≤ s * (‖fderiv ℝ χ z‖ *
            (1 + ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖) * ‖η z‖) :=
            mul_le_mul_of_nonneg_left hle hs0
        _ ≤ s * (‖fderiv ℝ χ z‖ * (1 + B) * ‖η z‖) := by
            gcongr
            exact hB z hz
        _ = _ := by ring
    have h2 := hχd z hz
    have hsD : 0 ≤ s * D := by positivity
    rw [hs, show K * s ^ 2 * D ^ 2 = K * (s * D) ^ 2 by ring]
    by_cases hn : z ∈ Hn
    · rw [indicator_of_mem hn, indicator_of_mem hz]
      rw [indicator_of_mem hn] at h2
      have h3 : s * D ≤ M * ((1 + B) * ‖η z‖) :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
      calc K * (s * D) ^ 2 ≤ K * (M * ((1 + B) * ‖η z‖)) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsD h3 2) hK
        _ = _ := by ring
    · rw [indicator_of_notMem hn] at h2
      have h0 : s * ‖fderiv ℝ χ z‖ = 0 := le_antisymm h2 (by positivity)
      rw [h0, zero_mul] at h1
      rw [le_antisymm h1 hsD]
      simpa using hR0
  · have hz' : z ∉ tsupport fun z ↦ χ z • η z :=
      fun h ↦ hz (hχU (tsupport_smul_subset_left χ η h))
    rw [hDdef, floerLinearizationAdjoint_eq_zero_of_eventuallyEq_zero ω
      (notMem_tsupport_iff_eventuallyEq.1 hz'), norm_zero]
    simpa using hR0

/-- **The `L²` norm of a cokernel element is controlled on a truncation.** Under the hypotheses of
the semi-Fredholm estimate of the formal adjoint on a sphere with moving input ends
(`exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearizationAdjoint_add_of_movingEnds`),
there are `A` and `T` such that every covector field `η`, `C²` on the plane minus the centers, with
`D_u^* η = 0` there and `‖η‖²` integrable there, satisfies `∫ ‖η‖² ≤ A ∫_{Σ_T} ‖η‖²`, the integral
on the left over the plane minus the centers. The adjoint estimate is applied to the cut-off
fields `χ_n η`, with the weight `K ρ⁻¹`, and the terms coming from the cutoff are controlled by the
`L²` norm of `η` where the height is at least `n`, which tends to zero. -/
private theorem
    exists_setIntegral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero_of_movingEnds
    (ω : SymplecticForm V) {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 2 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 2 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      ContDiffAt ℝ 2 u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))
    (hu₂out : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart inf ζ))
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    ∃ A T, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄,
      ContDiffOn ℝ 2 η {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      (∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
        ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u η z = 0) →
      IntegrableOn (fun z ↦ ‖η z‖ ^ 2) {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} →
      ∫ z in {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ‖η z‖ ^ 2 ≤
        A * ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
          ‖η z‖ ^ 2 := by
  set U := {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  have hρ := isWeight_movingEndsWeight c
  have hUm : MeasurableSet U := hρ.isOpen.measurableSet
  -- The constants: the adjoint estimate for the weight `K ρ⁻¹`, the bound of `J` and the cutoffs.
  obtain ⟨Kw, hKw, hwin, hwout⟩ := exists_weight_of_movingEnds ha hsep hout
  obtain ⟨C, -, T, hT, hest⟩ :=
    ω.exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearizationAdjoint_add_of_movingEnds
      hH hHs hHout hHouts ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq
      hJoutq hJ hu hu₂ hu₂out hc hF hFout hux hδ huxout hδout
      (w := fun z ↦ Kw * (movingEndsWeight c z)⁻¹)
      (fun z ↦ by have := movingEndsWeight_pos c z; positivity)
      (continuousOn_const.mul (hρ.continuousOn.inv₀ fun z _ ↦ (movingEndsWeight_pos c z).ne'))
      (fun z _ ↦ by have := movingEndsWeight_pos c z; positivity) hwin hwout
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_movingEnds ha
    (fun i ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx i t).continuousAt).continuousOn)
    (fun i ↦ (hJe i).continuous)
    (continuous_iff_continuousAt.2 fun t ↦ (hxout t).continuousAt).continuousOn
    hJout.continuous hJeq hJoutq
    (fun z hz ↦ ((hJ z hz).comp₂ contDiffAt_id (hu z hz)).continuousAt) hux huxout
  obtain ⟨M, hM⟩ := exists_cutoff_of_movingEnds ha hsep
  set m := max 1 ((1 + B) ^ 2)
  set c₀ := Kw * M ^ 2 * (1 + B) ^ 2
  refine ⟨m * max C 0, T + 1, fun η hη hD hηi ↦ ?_⟩
  set F := U.indicator fun z ↦ ‖η z‖ ^ 2
  have hFi : Integrable F := hηi.integrable_indicator hUm
  set tail : ℕ → ℝ := fun n ↦ ∫ z in {z | (n : ℝ) ≤ movingEndsHeight c z}, F z
  have htail : Tendsto tail atTop (𝓝 0) :=
    (tendsto_setIntegral_setOf_le hFi (measurable_movingEndsHeight c)).comp
      tendsto_natCast_atTop_atTop
  set Tr := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a (T + 1)
  set P := ∫ z in Tr, ‖η z‖ ^ 2
  -- For every large `n`, the estimate of `χ_n η` bounds `∫ ‖η‖²` by `m C (c₀ tail_n + P) + tail_n`;
  -- letting `n → ∞` gives the claim.
  refine ge_of_tendsto (by simpa using
    (((htail.const_mul c₀).add_const P).const_mul (m * max C 0)).add htail) ?_
  filter_upwards [hM, eventually_ge_atTop ⌈2 * Real.exp (2 * π * (T + 1)) +
    ∑ i, 2 / (‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2)⌉₊] with n ⟨χ, hχs, hχc, hχU, hχ1, hχd⟩ hn
  have hnT : 2 * Real.exp (2 * π * (T + 1)) +
      ∑ i, 2 / (‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hNT0 : 0 ≤ ∑ i, 2 / (‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2) :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hX0 := Real.exp_pos (2 * π * (T + 1))
  have hn0 : (0 : ℝ) < n := by linarith
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g :=
    ContDiffOn.contDiff_smul_of_tsupport_subset hη hρ.isOpen hχs.contDiffOn hχU
  have hgc : HasCompactSupport g := hχc.smul_right
  have hgU : tsupport g ⊆ U := (tsupport_smul_subset_left χ η).trans hχU
  -- On `Σ_{T+1}` the cutoff is `1`.
  have hgTr (z : ℝ × ℝ) (hz : z ∈ Tr) : g z = η z := by
    simp only [Tr, mem_preimage, mem_puncturedSphereTruncation] at hz
    refine (congrArg (· • η z) (hχ1 z (by linarith [hz.2, hnT, hNT0]) fun i ↦ ?_)).trans
      (one_smul _ _)
    have hY : 0 < ‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2 := by
      have := norm_pos_iff.2 (ha i)
      positivity
    have hi := Finset.single_le_sum (f := fun i ↦ 2 / (‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2))
      (fun i _ ↦ by positivity) (Finset.mem_univ i)
    have h2 := (div_le_iff₀ hY).1 (show 2 / (‖a i‖ * Real.exp (-(2 * π * (T + 1))) / 2) ≤ n by
      linarith)
    exact ((div_le_iff₀ hn0).2 (by linarith)).trans (hz.1 i)
  have hP : ∫ z in Tr, ‖g z‖ ^ 2 = P :=
    setIntegral_congr_fun (isCompact_preimage_puncturedSphereTruncation c a (T + 1)).measurableSet
      fun z hz ↦ by simp only [hgTr z hz]
  have hest' := hest hg hgc hgU
  rw [hP] at hest'
  -- The cutoff costs at most `c₀ tail_n` in the weighted norm of the adjoint.
  have hHn : MeasurableSet {z | (n : ℝ) ≤ movingEndsHeight c z} :=
    measurableSet_le measurable_const (measurable_movingEndsHeight c)
  have hW : ∫ z, Kw * (movingEndsWeight c z)⁻¹ * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u g z‖ ^ 2 ≤ c₀ * tail n := by
    refine (integral_mono_of_nonneg
      (ae_of_all _ fun z ↦ by have := movingEndsWeight_pos c z; positivity)
      ((hFi.indicator hHn).const_mul c₀)
      (ae_of_all _ fun z ↦ mul_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu hB
        (hη.of_le one_le_two) hD (hχs.of_le one_le_two) hχU hKw.le hχd z)).trans_eq ?_
    rw [integral_const_mul, integral_indicator hHn]
  have hW0 : 0 ≤ ∫ z, Kw * (movingEndsWeight c z)⁻¹ * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u g z‖ ^ 2 :=
    integral_nonneg fun z ↦ by have := movingEndsWeight_pos c z; positivity
  -- The `L²` norm of `g` on the sphere from the energies, and of `η` from that of `g`.
  have hL := setIntegral_norm_sq_le_of_movingEnds ha hsep hout hJ hu hB (hg.of_le one_le_two) hgc
    hgU (T := T) (by linarith)
  have hgi : Integrable fun z ↦ ‖g z‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖g z‖ ^ 2)
      (hg.continuous.norm.pow 2) (hgc.comp_left (g := fun v : V →L[ℝ] ℝ ↦ ‖v‖ ^ 2) (by simp))
  have hind : Integrable ({z | (n : ℝ) ≤ movingEndsHeight c z}.indicator F) := hFi.indicator hHn
  have hηg : ∫ z in U, ‖η z‖ ^ 2 ≤ (∫ z in U, ‖g z‖ ^ 2) + tail n := by
    calc ∫ z in U, ‖η z‖ ^ 2 ≤ ∫ z in U, (‖g z‖ ^ 2 +
          {z | (n : ℝ) ≤ movingEndsHeight c z}.indicator F z) := by
          refine setIntegral_mono_on hηi (hgi.integrableOn.add hind.integrableOn) hUm
            fun z hz ↦ ?_
          by_cases hν : (n : ℝ) ≤ movingEndsHeight c z
          · have hFz : F z = ‖η z‖ ^ 2 := indicator_of_mem hz _
            rw [indicator_of_mem (show z ∈ {z | (n : ℝ) ≤ movingEndsHeight c z} from hν), hFz]
            linarith [sq_nonneg ‖g z‖]
          · obtain ⟨h1, h2⟩ := norm_le_and_forall_le_of_movingEndsHeight_lt hz hn0 (not_le.1 hν)
            simp only [g, hχ1 z h1 h2, one_smul]
            linarith [indicator_nonneg (fun z (_ : z ∈ {z | (n : ℝ) ≤ movingEndsHeight c z}) ↦
              indicator_nonneg (fun z (_ : z ∈ U) ↦ sq_nonneg ‖η z‖) z) z]
      _ = (∫ z in U, ‖g z‖ ^ 2) + ∫ z in U, {z | (n : ℝ) ≤ movingEndsHeight c z}.indicator F z :=
          integral_add hgi.integrableOn hind.integrableOn
      _ ≤ _ := by
          gcongr
          exact (setIntegral_le_integral hind (ae_of_all _ (indicator_nonneg fun z _ ↦
            indicator_nonneg (fun z _ ↦ sq_nonneg ‖η z‖) z))).trans_eq (integral_indicator hHn)
  -- The arithmetic: `∫ ‖η‖² ≤ m (E + D) + tail_n ≤ m C (c₀ tail_n + P) + tail_n`.
  have hP0 : 0 ≤ P := setIntegral_nonneg (isCompact_preimage_puncturedSphereTruncation c a
    (T + 1)).measurableSet fun z _ ↦ sq_nonneg _
  have ht0 : 0 ≤ tail n := setIntegral_nonneg hHn fun z _ ↦
    indicator_nonneg (fun z _ ↦ sq_nonneg ‖η z‖) z
  have hIoi : MeasurableSet (Ioi T ×ˢ Icc (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Icc
  have hE0 : 0 ≤ (∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
      (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z)
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u g) ζ) +
      ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart inf)
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u g) ζ :=
    add_nonneg (Finset.sum_nonneg fun i _ ↦ setIntegral_nonneg hIoi fun ζ _ ↦
      sobolevDensity_nonneg _ ζ) (setIntegral_nonneg hIoi fun ζ _ ↦ sobolevDensity_nonneg _ ζ)
  have hD0 : 0 ≤ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a T,
      sobolevDensity g z :=
    setIntegral_nonneg (isCompact_preimage_puncturedSphereTruncation c a T).measurableSet
      fun z _ ↦ sobolevDensity_nonneg _ z
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmB : (1 + B) ^ 2 ≤ m := le_max_right _ _
  have hC : C * ((∫ z, Kw * (movingEndsWeight c z)⁻¹ * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u g z‖ ^ 2) + P) ≤ max C 0 * (c₀ * tail n + P) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _))
  nlinarith [hP0, ht0, mul_le_mul_of_nonneg_right hmB hE0, mul_le_mul_of_nonneg_right hm1 hD0,
    mul_le_mul_of_nonneg_left (hest'.trans hC) (by positivity : (0 : ℝ) ≤ m)]

/-! ### The Fredholm property -/

/-- **The linearized operator on a sphere with moving input ends is Fredholm.** Let the discs
`‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, with nonzero scales, and let the Hamiltonians `H i` and `Hout` be jointly `C⁴`
of period one. For each input end `i`, let `x i` be an orbit of `H i` starting at a nondegenerate
fixed point of its time-one map and let `J_e i` be a `C²` family of almost complex structures
compatible along `x i`; for the output end, let `x_out` and `J_out` be the same data for the
Hamiltonian `H'(t, y) = -Hout(-t, y)` of the output end read in its positive end chart. Let `J`
be `J_e i (t)` beyond `s = 2` in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input
end and `J_out (t)` beyond `s = 2` in the positive end chart `φ'_∞` of the output end, let `u` and
`J` along `u` be `C³` on the sphere minus its input punctures, the plane minus the centers `c i`,
with `J` compatible along `u` there, and let `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2` on each end, with loops
converging uniformly to the orbits and slice defects tending uniformly to zero. Then the
realization `D_u : W^{1,2}_0 → L²` of the linearized Floer operator for the weight
`TauCeti.Floer.movingEndsWeight c` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_of_movingEnds (ω : SymplecticForm V)
    {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 4 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 4 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ι → ℝ≥0}
    (hX : ∀ i, LipschitzWith (L i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : ι → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 2 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Lout : ℝ≥0}
    (hXout : LipschitzWith Lout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 2 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 3 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) →
      ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} (movingEndsWeight c)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).IsFredholm := by
  have hHs₂ (i : ι) : ContDiff ℝ 2 (uncurry (H i)) := (hHs i).of_le (by norm_num)
  have hHouts₂ : ContDiff ℝ 2 (uncurry Hout) := hHouts.of_le (by norm_num)
  have hJe₁ (i : ι) := (hJe i).of_le one_le_two
  have hJ₁ (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) :=
    (hJ z hz).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hu₁ (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) :=
    (hu z hz).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  -- Beyond `s = 2` the ends avoid the centers, so `u` is `C²` there.
  have hu₂ (i : ι) (ζ : ℝ × ℝ) (hζ : 2 < ζ.1) :
      ContDiffAt ℝ 2 u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) :=
    (hu _ fun j ↦ by
      rw [equivRealProdCLM_symm_realChart]
      exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simpa using (by linarith : 0 < ζ.1)) j
      ).of_le (by norm_num)
  have hu₂out (ζ : ℝ × ℝ) (hζ : 2 < ζ.1) : ContDiffAt ℝ 2 u (positiveEndChart inf ζ) :=
    (hu _ (equivRealProdCLM_symm_positiveEndChart_inf_ne
      (fun i ↦ (le_add_of_nonneg_right (by positivity)).trans (hout i))
      (by linarith))).of_le (by norm_num)
  obtain ⟨A, T, hglob⟩ :=
    exists_setIntegral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero_of_movingEnds ω hH hHs₂
      hHout hHouts₂ ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq hJoutq
      hJ₁ hu₁ hu₂ hu₂out hc hF hFout hux hδ huxout hδout
  exact .of_finite_ker_of_isClosed_range_of_finite_orthogonal _
    (finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds ω hH hHs₂ hHout hHouts₂ ha
      hsep hout hX hx hnd hJe₁ hJex hXout hxout hndout (hJout.of_le one_le_two) hJoutx hJeq hJoutq
      hJ₁ hu₁ hc hF hFout hux hδ huxout hδout)
    (isClosed_range_floerConformalSobolevOperator_of_movingEnds ω hH hHs₂ hHout hHouts₂ ha hsep
      hout hX hx hnd hJe₁ hJex hXout hxout hndout (hJout.of_le one_le_two) hJoutx hJeq hJoutq hJ₁
      hu₁ hc hF hFout hux hδ huxout hδout)
    (finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_setIntegral_norm_sq_le ω
      (isWeight_movingEndsWeight c) hJ
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz (u z) 1)
      (fun z hz ↦
        contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz (u z) Complex.I)
      hu hc
      (ω.memLp_floerConformalJetCoeff_of_movingEnds hH hHs₂ hHout hHouts₂ ha hsep hout
        (fun i ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx i t).continuousAt).continuousOn) hJe₁
        (continuous_iff_continuousAt.2 fun t ↦ (hxout t).continuousAt).continuousOn
        (hJout.of_le one_le_two) hJeq hJoutq hJ₁ hu₁ hF hFout hux hδ huxout hδout)
      (isCompact_preimage_puncturedSphereTruncation c a T)
      (preimage_puncturedSphereTruncation_subset ha T) hglob)

end TauCeti.SymplecticForm
