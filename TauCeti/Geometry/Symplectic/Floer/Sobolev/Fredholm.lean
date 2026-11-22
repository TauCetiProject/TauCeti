/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The index of the linearized Floer operator depends only on the asymptotic orbits

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator
`D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + A(z) ξ` along a map `u : ℝ × ℝ → V` of the cylinder into a
finite-dimensional symplectic inner product space `V`, for Floer data that are cylindrical near
the ends (`TauCeti.Floer.IsCylindricalNearEnds`) and `C¹` on the whole cylinder (with `C²`
Hamiltonians), with almost complex structures compatible with `ω`. This file shows that the
Fredholm property and the index of `D_u` do not depend on `u` beyond its asymptotic orbits.

* **Invariance.** Let `u` and `u'` be `C¹` maps whose loops converge uniformly to the same
  nondegenerate one-periodic orbits `x₋` at `-∞` and `x₊` at `+∞`, with slice defects
  `∂t u - X_{H±_t}(u)` tending uniformly to zero at the ends. Then `D_u` is Fredholm exactly when
  `D_{u'}` is (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_cylindrical`), and
  then the two have the same index
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical`).
* **Equal ends.** In a unitary trivialization, where `V = F` is a finite-dimensional complex inner
  product space with `ω = Im ⟪·, ·⟫`, take the `s`-independent Floer data `(i, 0, H_t)` of a
  Hamiltonian `H`: complex structure `J = i`, `K_s = 0` and `K_t = H_t`. The linearized operator for
  these data along any map `u` from a nondegenerate one-periodic orbit `x` of `H` to itself is
  Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_isNondegenerateFixedPt`) of index
  zero (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt`). This
  holds for any `C¹` map `u` whose loops converge uniformly to `x` at both ends, with slice defects
  tending uniformly to zero there; `u` need not solve the Floer equation (it may be, for instance,
  a pre-glued map).

The proof deforms `u` into `u'` along the segment `u_λ = u + λ (u' - u)`. Every `u_λ` has the
same asymptotic orbits, so the semi-Fredholm estimate
(`TauCeti.SymplecticForm.exists_hasSemiFredholmEstimate_floerJetCoeff_of_cylindrical`) holds along
the whole segment. The coefficient field of `D_{u_λ}` at `z` is a continuous function of
`(z, u_λ z, ∂t u_λ z)`, which only depends on `z` through a compact set because the data are
cylindrical near the ends, and `u_λ` and `∂t u_λ` are bounded on the strip. So the coefficient
fields depend continuously on `λ` in `L^∞`, and the Fredholm property and the index are constant
along the segment (`TauCeti.CylinderSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`).
At a stationary cylinder over a nondegenerate orbit, `D_u` is invertible in a unitary
trivialization
(`TauCeti.SymplecticForm.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt`), which
gives the case of equal ends.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm index of `∂s + J ∂t + S(s, t)`, which depends
  only on the asymptotic operators.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33, on the homotopy invariance of the index of operators with fixed limits.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap Metric
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

section Coefficient

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field of the linearized Floer operator at `z`, as a function of `z`, the value
`y = u z` and the slice velocity `d = ∂t u z` of the map. -/
private def jetCoeffAt (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (p : (ℝ × ℝ) × V × V) : V × V × V →L[ℝ] V :=
  (fst ℝ V V).comp (snd ℝ V (V × V)) +
    (J p.1 p.2.1).comp ((snd ℝ V V).comp (snd ℝ V (V × V))) +
    ((fderiv ℝ (J p.1) p.2.1).flip (p.2.2 - ω.hamiltonianVectorField (Kt p.1) p.2.1) -
      fderiv ℝ (ω.hamiltonianVectorField (Ks p.1)) p.2.1 -
      (J p.1 p.2.1).comp (fderiv ℝ (ω.hamiltonianVectorField (Kt p.1)) p.2.1)).comp
      (fst ℝ V (V × V))

/-- The coefficient field of the linearized Floer operator along `u` at `z` is `jetCoeffAt` at
`(z, u z, ∂t u z)`: both unfold to the same expression, `stdComplexLineImag` being `(0, 1)`. -/
private theorem floerJetCoeff_eq_jetCoeffAt (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerJetCoeff J Ks Kt u z = jetCoeffAt ω J Ks Kt (z, u z, fderiv ℝ u z (0, 1)) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [floerJetCoeff_apply, floerLinearizationCoeff_apply, jetCoeffAt, stdComplexLineImag_eq]

/-- `jetCoeffAt` is continuous when the data are `C¹` (with `C²` Hamiltonians) on the whole
cylinder. -/
private theorem continuous_jetCoeffAt (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ J p.1 p.2)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt)) :
    Continuous (jetCoeffAt ω J Ks Kt) := by
  have hπ : Continuous fun p : (ℝ × ℝ) × V × V ↦ (p.1, p.2.1) :=
    continuous_fst.prodMk continuous_snd.fst
  have hXs := (continuous_fderiv_slice_right (f := fun z ↦ ω.hamiltonianVectorField (Ks z))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKs)).comp hπ
  have hXt := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKt
  have hdXt := (continuous_fderiv_slice_right
    (f := fun z ↦ ω.hamiltonianVectorField (Kt z)) hXt).comp hπ
  have hJp : Continuous fun p : (ℝ × ℝ) × V × V ↦ J p.1 p.2.1 := hJ.continuous.comp hπ
  have hXtp : Continuous fun p : (ℝ × ℝ) × V × V ↦ ω.hamiltonianVectorField (Kt p.1) p.2.1 :=
    hXt.continuous.comp hπ
  have hflip : Continuous fun p : (ℝ × ℝ) × V × V ↦
      (fderiv ℝ (J p.1) p.2.1).flip (p.2.2 - ω.hamiltonianVectorField (Kt p.1) p.2.1) :=
    ((flipₗᵢ ℝ V V V).continuous.comp ((continuous_fderiv_slice_right hJ).comp hπ)).clm_apply
      (continuous_snd.snd.sub hXtp)
  exact (continuous_const.fun_add (hJp.clm_comp continuous_const)).fun_add
    (((hflip.fun_sub hXs).fun_sub (hJp.clm_comp hdXt)).clm_comp continuous_const)

/-- Floer data cylindrical near the ends with radius `R` give the same coefficient field at `z`
and at the point `(projIcc (-|R|) |R| _ z.1, z.2)` of `[-|R|, |R|] × ℝ` nearest to `z`. -/
private theorem jetCoeffAt_projIcc (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) (z : ℝ × ℝ) (y d : V) :
    jetCoeffAt ω (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt (z, y, d) =
      jetCoeffAt ω (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        (((projIcc (-|R|) |R| (neg_le_self (abs_nonneg R)) z.1 : ℝ), z.2), y, d) := by
  obtain ⟨s, t⟩ := z
  obtain ⟨hJ, hKs, hKt⟩ := hcyl.eq_projIcc s t
  simp only [jetCoeffAt, hJ, hKs, hKt]

/-- Data of an end of the cylinder that are the values of `C¹` cylinder data at a fixed `s = a`
(with `C²` Hamiltonians) are `C¹` (with `C²` Hamiltonians), and compatible where the cylinder data
are. -/
private theorem endData_of_eq (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Kt : ℝ × ℝ → V → ℝ} {Je : ℝ → V → AlmostComplexStructure V} {He : ℝ → V → ℝ} (a : ℝ)
    (hJe : ∀ t, J (a, t) = Je t) (hHe : ∀ t, Kt (a, t) = He t)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKt : ContDiff ℝ 2 (uncurry Kt)) (hJc : ∀ z y, ω.Compatible (J z y)) :
    (ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) ∧
      ContDiff ℝ 2 (uncurry He) ∧ ∀ t y, ω.Compatible (Je t y) := by
  obtain rfl : Je = fun t ↦ J (a, t) := funext fun t ↦ (hJe t).symm
  obtain rfl : He = fun t ↦ Kt (a, t) := funext fun t ↦ (hHe t).symm
  exact ⟨hJ.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd),
    hKt.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd), fun t ↦ hJc (a, t)⟩

/-- **Uniform closeness of the coefficient fields along a segment of maps.** For data cylindrical
near the ends and `C¹` on the whole cylinder (with `C²` Hamiltonians), and differentiable maps
`u`, `u'` which are bounded on the strip `ℝ × [0, 1]` together with their derivatives in `t`, the
coefficient fields of the linearized Floer operator along `u + μ (u' - u)` and `u + lam (u' - u)`
are uniformly close on the strip for `μ` close to `lam`. -/
private theorem exists_pos_forall_dist_floerJetCoeff_add_smul_sub_lt (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hu : Differentiable ℝ u) (hu' : Differentiable ℝ u') {B : ℝ}
    (hB : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t)‖ ≤ B ∧ ‖u' (s, t)‖ ≤ B ∧
      ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ B ∧ ‖fderiv ℝ u' (s, t) (0, 1)‖ ≤ B) (lam : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∃ η > 0, ∀ μ, |μ - lam| < η → ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 →
      dist (ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          (u + μ • (u' - u)) z)
        (ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          (u + lam • (u' - u)) z) < r := by
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 ⟨le_rfl, zero_le_one⟩).1
  -- For `|μ - lam| ≤ 1`, the arguments `((projIcc (-|R|) |R| _ z.1, z.2), u_μ z, ∂t u_μ z)` of
  -- `jetCoeffAt` on the strip lie in the compact set `K`, on which `jetCoeffAt` is uniformly
  -- continuous.
  set B' := B + 2 * (|lam| + 1) * B
  set K : Set ((ℝ × ℝ) × V × V) :=
    (Icc (-|R|) |R| ×ˢ Icc (0 : ℝ) 1) ×ˢ (closedBall 0 B' ×ˢ closedBall 0 B')
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod
    ((isCompact_closedBall 0 B').prod (isCompact_closedBall 0 B'))
  have hnorm {μ : ℝ} (hμ : |μ - lam| ≤ 1) {a b : V} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
      ‖a + μ • (b - a)‖ ≤ B' := by
    have hμ' : |μ| ≤ |lam| + 1 := by linarith [abs_sub_abs_le_abs_sub μ lam]
    calc ‖a + μ • (b - a)‖ ≤ ‖a‖ + |μ| * (‖b‖ + ‖a‖) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
      _ ≤ B + (|lam| + 1) * (B + B) := by gcongr
      _ = B' := by ring
  have hmem {μ : ℝ} (hμ : |μ - lam| ≤ 1) {z : ℝ × ℝ} (hz : z.2 ∈ Icc (0 : ℝ) 1) :
      (((projIcc (-|R|) |R| (neg_le_self (abs_nonneg R)) z.1 : ℝ), z.2), (u + μ • (u' - u)) z,
        fderiv ℝ (u + μ • (u' - u)) z (0, 1)) ∈ K := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hB z.1 z.2 hz
    refine ⟨⟨Subtype.prop _, hz⟩, mem_closedBall_zero_iff.2 ?_, mem_closedBall_zero_iff.2 ?_⟩
    · simpa using hnorm hμ h₁ h₂
    · simpa [fderiv_add_smul_sub_apply (hu _) (hu' _)] using hnorm hμ h₃ h₄
  obtain ⟨δ, hδ, hΦ⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous
    (continuous_jetCoeffAt ω (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs
      hKt).continuousOn) r hr
  refine ⟨min 1 (δ / (2 * B + 1)), lt_min one_pos (by positivity), fun μ hμ z hz ↦ ?_⟩
  rw [lt_min_iff] at hμ
  rw [floerJetCoeff_eq_jetCoeffAt, floerJetCoeff_eq_jetCoeffAt,
    jetCoeffAt_projIcc ω hcyl z ((u + μ • (u' - u)) z),
    jetCoeffAt_projIcc ω hcyl z ((u + lam • (u' - u)) z)]
  refine hΦ _ (hmem hμ.1.le hz) _ (hmem (by simp) hz) ?_
  -- The two points differ by `(μ - lam) (u' - u)` in the value and the slice velocity.
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hB z.1 z.2 hz
  have hsmall {a b : V} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
      dist (a + μ • (b - a)) (a + lam • (b - a)) < δ := by
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
    calc |μ - lam| * ‖b - a‖ ≤ |μ - lam| * (2 * B + 1) := by
          gcongr; linarith [norm_sub_le b a]
      _ < δ / (2 * B + 1) * (2 * B + 1) := by gcongr; exact hμ.2
      _ = δ := div_mul_cancel₀ _ (by positivity)
  simp only [Prod.dist_eq, dist_self, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    fderiv_add_smul_sub_apply (hu _) (hu' _)]
  exact max_lt hδ (max_lt (hsmall h₁ h₂) (hsmall h₃ h₄))

/-- **Continuity of the coefficient fields along a segment of maps in `L^∞`.** Under the
hypotheses of `exists_pos_forall_dist_floerJetCoeff_add_smul_sub_lt`, with `u` and `u'` of class
`C¹`, the coefficient field of the linearized Floer operator along `u + μ (u' - u)` depends
continuously on `μ` in `L^∞` of the strip. -/
private theorem tendsto_eLpNorm_floerJetCoeff_add_smul_sub (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u') {B : ℝ}
    (hB : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t)‖ ≤ B ∧ ‖u' (s, t)‖ ≤ B ∧
      ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ B ∧ ‖fderiv ℝ u' (s, t) (0, 1)‖ ≤ B) (lam : ℝ) :
    Tendsto (fun μ : ℝ ↦ eLpNorm
      (ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          (u + μ • (u' - u)) -
        ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          (u + lam • (u' - u))) ∞ stripMeasure) (𝓝 lam) (𝓝 0) := by
  -- The coefficient fields along the segment are continuous, hence measurable.
  have hcont (μ : ℝ) := ω.continuous_floerJetCoeff
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) (u := u + μ • (u' - u))
    (fun _ ↦ hJ.contDiffAt) (fun _ ↦ hKs.contDiffAt) (fun _ ↦ hKt.contDiffAt)
    (hu.add ((hu'.sub hu).const_smul μ))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  obtain ⟨η, hη, h⟩ := exists_pos_forall_dist_floerJetCoeff_add_smul_sub_lt ω hcyl hJ hKs hKt
    (hu.differentiable one_ne_zero) (hu'.differentiable one_ne_zero) hB lam
    (ENNReal.ofReal_pos.1 hr)
  filter_upwards [Metric.ball_mem_nhds lam hη] with μ hμ
  rw [mem_ball, Real.dist_eq] at hμ
  refine le_trans ?_ hrε.le
  rw [eLpNorm_exponent_top ((hcont μ).sub (hcont lam)).aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
  rw [Pi.sub_apply, ← dist_eq_norm]
  exact (h μ hμ z hz.2).le

end Coefficient

section Invariance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Fredholm property and the index pass from `D_u` to `D_{u'}` along the segment
`u + λ (u' - u)`. -/
private theorem isFredholm_and_index_eq_of_cylindrical (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u' (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u').IsFredholm ∧
      (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          u').index =
        (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          u).index := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hR := le_abs_self R
  have hR' : -|R| ≤ -R := by linarith
  -- The data of the ends are the data of the cylinder at `s = ∓|R|`.
  obtain ⟨hJm, hHm, hJxm⟩ := endData_of_eq ω (-|R|)
    (fun t ↦ hcyl.almostComplex_eq_of_le_neg (_, t) hR')
    (fun t ↦ hcyl.hamiltonianT_eq_of_le_neg (_, t) hR') hJ hKt hJc
  obtain ⟨hJp, hHp, hJxp⟩ := endData_of_eq ω |R| (fun t ↦ hcyl.almostComplex_eq_of_le (_, t) hR)
    (fun t ↦ hcyl.hamiltonianT_eq_of_le (_, t) hR) hJ hKt hJc
  have hXmc : Continuous (uncurry fun t ↦ ω.hamiltonianVectorField (Hm t)) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHm).continuous
  have hXpc : Continuous (uncurry fun t ↦ ω.hamiltonianVectorField (Hp t)) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHp).continuous
  have hxmc : Continuous xm := continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt
  have hxpc : Continuous xp := continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt
  have hd := hu.differentiable one_ne_zero
  have hd' := hu'.differentiable one_ne_zero
  -- Every point of the segment has the asymptotics of `u` and `u'`.
  have hseg (μ : ℝ) := And.intro
    (tendstoUniformlyOn_add_smul_sub_and_sliceDefect hXmc hd hd' hxmc huxm hδm hu'xm hδ'm μ)
    (tendstoUniformlyOn_add_smul_sub_and_sliceDefect hXpc hd hd' hxpc huxp hδp hu'xp hδ'p μ)
  set M : ℝ → ℝ × ℝ → V × V × V →L[ℝ] V := fun μ ↦
    ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt (u + μ • (u' - u))
  have hcylμ (μ : ℝ) :=
    Floer.isCylindricalNearEnds_of_contDiff hcyl hJ hKs hKt (u + μ • (u' - u))
  have huμ (μ : ℝ) : ContDiff ℝ 1 (u + μ • (u' - u)) := hu.add ((hu'.sub hu).const_smul μ)
  have hM (μ : ℝ) : MemLp (M μ) ∞ stripMeasure :=
    ω.memLp_floerJetCoeff_of_cylindrical (hcylμ μ) (huμ μ) hHm hJm (hseg μ).1.1 (hseg μ).1.2 hHp
      hJp (hseg μ).2.1 (hseg μ).2.2
  have hest (μ : ℝ) : ∃ C T, HasSemiFredholmEstimate (M μ) C T :=
    ω.exists_hasSemiFredholmEstimate_floerJetCoeff_of_cylindrical (hcylμ μ) (huμ μ)
      (fun z ↦ hJc z _) hXm hHm hxm hndm hJm (fun t ↦ hJxm t _) (hseg μ).1.1 (hseg μ).1.2 hXp hHp
      hxp hndp hJp (fun t ↦ hJxp t _) (hseg μ).2.1 (hseg μ).2.2
  -- `u`, `u'` and their derivatives in `t` are bounded on the strip.
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_le_and_norm_fderiv_apply_le_of_sliceDefect hXmc hXpc hu hxmc hxpc huxm hδm
      huxp hδp
  obtain ⟨C', hC'⟩ :=
    exists_forall_norm_le_and_norm_fderiv_apply_le_of_sliceDefect hXmc hXpc hu' hxmc hxpc hu'xm hδ'm
      hu'xp hδ'p
  have hcont (μ : ℝ) (_ : μ ∈ univ) :
      Tendsto (fun ν ↦ eLpNorm (M ν - M μ) ∞ stripMeasure) (𝓝[univ] μ) (𝓝 0) := by
    rw [nhdsWithin_univ]
    exact tendsto_eLpNorm_floerJetCoeff_add_smul_sub ω hcyl hJ hKs hKt hu hu' (B := max C C')
      (fun s t ht ↦ ⟨(hC s t ht).1.trans (le_max_left _ _), (hC' s t ht).1.trans (le_max_right _ _),
        (hC s t ht).2.trans (le_max_left _ _), (hC' s t ht).2.trans (le_max_right _ _)⟩) μ
  have h₀ : u + (0 : ℝ) • (u' - u) = u := by simp
  have h₁ : u + (1 : ℝ) • (u' - u) = u' := by simp
  have key := isFredholm_and_index_eq_of_hasSemiFredholmEstimate isPreconnected_univ
    (fun μ _ ↦ hM μ) hcont (fun μ _ ↦ hest μ) (mem_univ 0) (mem_univ 1)
    (by simpa only [M, h₀, ← floerSobolevOperator_def] using h)
  simpa only [M, h₀, h₁, ← floerSobolevOperator_def] using key

/-- **The Fredholm property of the linearized Floer operator depends only on the asymptotic
orbits.** Let the Floer data `(J, K_s, K_t)` be `C¹` (with `C²` Hamiltonians) on the whole
cylinder, compatible with `ω` and cylindrical near the ends: equal to `(J₋_t, 0, H₋_t)` for
`s ≤ -R` and to `(J₊_t, 0, H₊_t)` for `s ≥ R`. Let `u` and `u'` be `C¹` maps whose loops converge
uniformly to the same nondegenerate one-periodic orbits `x₋` of `H₋` at `-∞` and `x₊` of `H₊` at
`+∞`, with slice defects `∂t u - X_{H±_t}(u)` tending uniformly to zero at the corresponding end.
Then `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` is Fredholm if and only if `D_{u'}` is. -/
theorem isFredholm_floerSobolevOperator_iff_of_cylindrical (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u' (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).IsFredholm ↔
      (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u').IsFredholm :=
  ⟨fun h ↦ (isFredholm_and_index_eq_of_cylindrical ω hcyl hJ hKs hKt hJc hu hu' hXm hxm hndm huxm
      hδm hu'xm hδ'm hXp hxp hndp huxp hδp hu'xp hδ'p h).1,
    fun h ↦ (isFredholm_and_index_eq_of_cylindrical ω
      (Floer.isCylindricalNearEnds_of_contDiff hcyl hJ hKs hKt u') hJ hKs hKt hJc hu' hu hXm hxm
      hndm hu'xm hδ'm huxm hδm hXp hxp hndp hu'xp hδ'p huxp hδp h).1⟩

/-- **The index of the linearized Floer operator depends only on the asymptotic orbits.** Under
the hypotheses of `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_cylindrical`, if
`D_u` is Fredholm, then `D_{u'}` has the same index as `D_u`. -/
theorem index_floerSobolevOperator_eq_of_cylindrical (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u' (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u').index =
      (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).index :=
  (isFredholm_and_index_eq_of_cylindrical ω hcyl hJ hKs hKt hJc hu hu' hXm hxm hndm huxm hδm
    hu'xm hδ'm hXp hxp hndp huxp hδp hu'xp hδ'p h).2

end Invariance

section Unitary

/-! ### Maps from a nondegenerate orbit to itself in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (ω : SymplecticForm F) {H : ℝ → F → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
  {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
  (hum : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atBot (Icc 0 1))
  (hδm : TendstoUniformlyOn
    (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
  (hup : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
  (hδp : TendstoUniformlyOn
    (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop (Icc 0 1))

include hH hHp hx hxp hu hum hδm hup hδp in
/-- The Fredholm property and index zero of the linearized Floer operator along a map from a
nondegenerate orbit to itself, compared with the stationary cylinder. -/
private theorem isFredholm_floerSobolevOperator_and_index_eq_zero
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u).IsFredholm ∧
      (ω.floerSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u).index = 0 := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hH₂ : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  have hKt : ContDiff ℝ 2 (uncurry fun (w : ℝ × ℝ) (y : F) ↦ H w.2 y) :=
    hH₂.comp (contDiff_fst.snd.prodMk contDiff_snd)
  -- The stationary cylinder over `x`, at which the operator is invertible.
  have hs : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ x w.2 :=
    (contDiff_one_of_hasDerivAt (X := fun t ↦ ω.hamiltonianVectorField (H t))
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 0)
        (by simpa using hH.of_le (by norm_num))).continuous hx).comp contDiff_snd
  have hsx (l : Filter ℝ) : TendstoUniformlyOn (fun s t ↦ (fun w : ℝ × ℝ ↦ x w.2) (s, t)) x l
      (Icc 0 1) :=
    tendstoUniformlyOn_const x l _
  have hsδ (l : Filter ℝ) : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H t)) (fun w : ℝ × ℝ ↦ x w.2) (s, t)) 0 l (Icc 0 1) := by
    rw [sliceDefect_comp_snd_eq_zero hx]
    exact tendstoUniformlyOn_const (0 : ℝ → F) l (Icc 0 1)
  have hinv := isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt ω hX hH hHp hx hxp hω hnd
  have hcyl := Floer.isCylindricalNearEnds_comp_snd
    (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) contDiff_const hH₂
    (fun w : ℝ × ℝ ↦ x w.2)
  have hJc (z : ℝ × ℝ) (y : F) : ω.Compatible
      ((fun _ _ ↦ AlmostComplexStructure.ofComplexModule F : ℝ × ℝ → F → _) z y) :=
    ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  refine ⟨(isFredholm_floerSobolevOperator_iff_of_cylindrical ω hcyl contDiff_const contDiff_const
    hKt hJc hs hu hX hx hnd (hsx _) (hsδ _) hum hδm hX hx hnd (hsx _) (hsδ _) hup hδp).1
      hinv.isFredholm, ?_⟩
  rw [index_floerSobolevOperator_eq_of_cylindrical ω hcyl contDiff_const contDiff_const hKt hJc hs
    hu hX hx hnd (hsx _) (hsδ _) hum hδm hX hx hnd (hsx _) (hsδ _) hup hδp hinv.isFredholm]
  obtain ⟨e, he⟩ := hinv
  rw [← he]
  exact e.index_eq_zero

include hH hHp hx hxp hu hum hδm hup hδp in
/-- **The linearized Floer operator from a nondegenerate orbit to itself is Fredholm.** Let `F` be
a finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
`x` be a one-periodic orbit of a one-periodic, jointly `C³` time-dependent Hamiltonian `H` whose
suspended vector field is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the
time-one map. Let `u` be a `C¹` map whose loops converge uniformly to `x` at both ends, with slice
defect `∂t u - X_{H_t}(u)` tending uniformly to zero at both ends. Then, for the `s`-independent
Floer data `(i, 0, H_t)`, the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the
linearized Floer operator is Fredholm. -/
theorem isFredholm_floerSobolevOperator_of_isNondegenerateFixedPt
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).IsFredholm :=
  (isFredholm_floerSobolevOperator_and_index_eq_zero ω hX hH hHp hx hxp hu hum hδm hup hδp hω
    hnd).1

include hH hHp hx hxp hu hum hδm hup hδp in
/-- **The linearized Floer operator from a nondegenerate orbit to itself has index zero.** Under
the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_isNondegenerateFixedPt`, the
realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator has
index zero. -/
theorem index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u).index = 0 :=
  (isFredholm_floerSobolevOperator_and_index_eq_zero ω hX hH hHp hx hxp hu hum hδm hup hδp hω
    hnd).2

end Unitary

end TauCeti.SymplecticForm
