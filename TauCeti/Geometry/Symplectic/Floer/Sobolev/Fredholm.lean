/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Fredholm
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.Continuation
import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Parametrix
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Geometry.Symplectic.Floer.Sobolev.UnitaryFrame
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The index of the linearized Floer operator depends only on the asymptotic data

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator
`D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + A(z) ξ` along a map `u : ℝ × ℝ → V` of the cylinder into a
finite-dimensional symplectic inner product space `V`, for Floer data that are cylindrical near
the ends (`TauCeti.Floer.IsCylindricalNearEnds`) and `C¹` on the whole cylinder (with `C²`
Hamiltonians), with almost complex structures compatible with `ω`. This file shows that the
Fredholm property and the index of `D_u` do not depend on `u` beyond its asymptotic orbits, nor on
the Floer data beyond their end Hamiltonians: in particular they do not depend on the almost
complex structures, also on the ends. In a unitary trivialization (`ω = Im ⟪·, ·⟫`) with
one-periodic `C³` end Hamiltonians, `D_u` is Fredholm for every compatible almost complex structure
when the asymptotic orbits are one-periodic and nondegenerate.

* **Invariance under the map.** Let `u` and `u'` be `C¹` maps whose loops converge uniformly to the
  same nondegenerate one-periodic orbits `x₋` at `-∞` and `x₊` at `+∞`, with slice defects
  `∂t u - X_{H±_t}(u)` tending uniformly to zero at the ends. Then `D_u` is Fredholm exactly when
  `D_{u'}` is (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_cylindrical`), and
  then the two have the same index
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical`).
* **Invariance under the data.** Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be Floer data with the
  same end Hamiltonians `H₋_t` and `H₊_t`, possibly cylindrical from different radii on, and with
  possibly different almost complex structures, also on the ends. Then along the same map `u` the
  operator of the first data is Fredholm exactly when that of the second data is
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_cylindrical_data`), and then the
  two have the same index
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`). For instance, the
  index along a continuation cylinder does not depend on the choice of the homotopy between its
  end Hamiltonians, nor on any of the almost complex structures.
* **Equal ends.** In a unitary trivialization, where `V = F` is a finite-dimensional complex inner
  product space with `ω = Im ⟪·, ·⟫`, take the `s`-independent Floer data `(i, 0, H_t)` of a
  Hamiltonian `H`: complex structure `J = i`, `K_s = 0` and `K_t = H_t`. The linearized operator for
  these data along any map `u` from a nondegenerate one-periodic orbit `x` of `H` to itself is
  Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_isNondegenerateFixedPt`) of index
  zero (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt`). This
  holds for any `C¹` map `u` whose loops converge uniformly to `x` at both ends, with slice defects
  tending uniformly to zero there; `u` need not solve the Floer equation (it may be, for instance,
  a pre-glued map). By the invariance under the data, the same holds for all Floer data with the
  Hamiltonian `H` at both ends and any compatible almost complex structures, such as those of a
  continuation cylinder from `H` to itself. For such data, the Fredholm property is the equal-ends
  case of `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`
  below, and index zero is
`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt_of_cylindrical`
  for them.
* **Every compatible almost complex structure.** In a unitary trivialization, for Floer data
  `(J, K_s, K_t)` with any compatible almost complex structures, along a map `u` asymptotic to
  nondegenerate orbits `x₋` and `x₊`, which may differ, `D_u` is Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`; along a
  Floer trajectory with data `(J_t, 0, H_t)`,
  `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_compatible`), with the index of the
  data `(i, K_s, K_t)`. For these data the parametrix of
  `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical` applies, since `D_u` and
  the stationary operators at its ends share the principal part `∂s + i ∂t`; the invariance under
  the data then passes from `i` to `J`.

The proof of the invariance under the map deforms `u` into `u'` along the segment
`u_λ = u + λ (u' - u)`. Every `u_λ` has the same asymptotic orbits, so the semi-Fredholm estimate
(`TauCeti.SymplecticForm.exists_hasSemiFredholmEstimate_floerJetCoeff_of_cylindrical`) holds along
the whole segment. The coefficient field of `D_{u_λ}` at `z` is a continuous function of
`(z, u_λ z, ∂t u_λ z)`, which only depends on `z` through a compact set because the data are
cylindrical near the ends, and `u_λ` and `∂t u_λ` are bounded on the strip. So the coefficient
fields depend continuously on `λ` in `L^∞`, and the Fredholm property and the index are constant
along the segment (`TauCeti.CylinderSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`).
The proof of the invariance under the data deforms the data instead, keeping `u`: the Hamiltonians
along the segment `K_λ = K + λ (K' - K)`, and the almost complex structures along the continuation
homotopy `TauCeti.Floer.continuationAlmostComplex` from `J` to `J'`, whose Cayley coordinates
relative to a fixed compatible structure run along the segment between those of `J` and `J'`, so
that the structures stay compatible. Every `(J_λ, K_λ)` is cylindrical near the ends with the
same end Hamiltonians, its almost complex structures on the ends are compatible, being points of
the continuation homotopy, and the coefficient field of the data at `λ` is a continuous function
of `(λ, z, u z, ∂t u z)`, so the same argument applies.
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
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the space of compatible structures.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap Metric
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure tendsto_eLpNorm_sub_of_forall_dist_lt)

section Coefficient

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field of the linearized Floer operator at `z`, as a function of `z`, the value
`y = u z` and the slice velocity `d = ∂t u z` of the map. The data are indexed by a parameter
`p.1 ∈ P`: the point `z` itself, or `z` together with the parameter of a family of data. -/
private def jetCoeffAt {P : Type*} (ω : SymplecticForm V) (J : P → V → V →L[ℝ] V)
    (Ks Kt : P → V → ℝ) (p : P × V × V) : V × V × V →L[ℝ] V :=
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

/-- `jetCoeffAt` is continuous when the data are `C¹` (with `C²` Hamiltonians) jointly in the
parameter and the target point. -/
private theorem continuous_jetCoeffAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (ω : SymplecticForm V) {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ}
    (hJ : ContDiff ℝ 1 fun p : P × V ↦ J p.1 p.2)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt)) :
    Continuous (jetCoeffAt ω J Ks Kt) := by
  have hπ : Continuous fun p : P × V × V ↦ (p.1, p.2.1) :=
    continuous_fst.prodMk continuous_snd.fst
  have hXs := (continuous_fderiv_slice_right (f := fun z ↦ ω.hamiltonianVectorField (Ks z))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKs)).comp hπ
  have hXt := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKt
  have hdXt := (continuous_fderiv_slice_right
    (f := fun z ↦ ω.hamiltonianVectorField (Kt z)) hXt).comp hπ
  have hJp : Continuous fun p : P × V × V ↦ J p.1 p.2.1 := hJ.continuous.comp hπ
  have hXtp : Continuous fun p : P × V × V ↦ ω.hamiltonianVectorField (Kt p.1) p.2.1 :=
    hXt.continuous.comp hπ
  have hflip : Continuous fun p : P × V × V ↦
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
          (u + lam • (u' - u))) ∞ stripMeasure) (𝓝 lam) (𝓝 0) :=
  have hM (μ : ℝ) := ω.continuous_floerJetCoeff
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) (u := u + μ • (u' - u))
    (fun _ ↦ hJ.contDiffAt) (fun _ ↦ hKs.contDiffAt) (fun _ ↦ hKt.contDiffAt)
    (hu.add ((hu'.sub hu).const_smul μ))
  tendsto_eLpNorm_sub_of_forall_dist_lt
    (.of_forall fun μ ↦ ((hM μ).sub (hM lam)).aestronglyMeasurable) fun _ hr ↦ by
      obtain ⟨η, hη, h⟩ := exists_pos_forall_dist_floerJetCoeff_add_smul_sub_lt ω hcyl hJ hKs hKt
        (hu.differentiable one_ne_zero) (hu'.differentiable one_ne_zero) hB lam hr
      exact Metric.eventually_nhds_iff.2 ⟨η, hη, fun μ hμ ↦ h μ hμ⟩

/-- The coefficient field at `z` of the data at parameter `μ` of a family of data is `jetCoeffAt`
of the family at `((μ, z), y, d)`. -/
private theorem jetCoeffAt_family (ω : SymplecticForm V) (J : ℝ × (ℝ × ℝ) → V → V →L[ℝ] V)
    (Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ) (μ : ℝ) (p : (ℝ × ℝ) × V × V) :
    jetCoeffAt ω (fun w ↦ J (μ, w)) (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) p =
      jetCoeffAt ω J Ks Kt ((μ, p.1), p.2) :=
  rfl

/-- **Uniform closeness of the coefficient fields along a family of data.** Let
`(J_μ, K_{s,μ}, K_{t,μ})` be a family of Floer data, `C¹` jointly in the parameter `μ`, the point
of the cylinder and the target point (with `C²` Hamiltonians), all cylindrical near the ends with
a common radius and common end Hamiltonians (the almost complex structures of the ends may depend
on `μ`), and let `u` be bounded on the strip `ℝ × [0, 1]` together with its derivative in `t`.
Then the coefficient fields of the linearized Floer operators of the data at `μ` and at `lam`
along `u` are uniformly close on the strip for `μ` close to `lam`. -/
private theorem exists_pos_forall_dist_floerJetCoeff_family_lt (ω : SymplecticForm V)
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : ∀ μ, Floer.IsCylindricalNearEnds (fun w ↦ J (μ, w)) (fun w ↦ Ks (μ, w))
      (fun w ↦ Kt (μ, w)) (Jm μ) (Jp μ) Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt)) {B : ℝ}
    (hB : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t)‖ ≤ B ∧ ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ B) (lam : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∃ η > 0, ∀ μ, |μ - lam| < η → ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 →
      dist (ω.floerJetCoeff (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u z)
        (ω.floerJetCoeff (fun w y ↦ (J (lam, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (lam, w)) (fun w ↦ Kt (lam, w)) u z) < r := by
  -- For `|μ - lam| ≤ 1`, the arguments `((μ, (projIcc (-|R|) |R| _ z.1, z.2)), u z, ∂t u z)` of
  -- `jetCoeffAt` on the strip lie in the compact set `K`, on which `jetCoeffAt` is uniformly
  -- continuous.
  set K : Set ((ℝ × (ℝ × ℝ)) × V × V) :=
    (Icc (lam - 1) (lam + 1) ×ˢ (Icc (-|R|) |R| ×ˢ Icc (0 : ℝ) 1)) ×ˢ
      (closedBall 0 B ×ˢ closedBall 0 B)
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod
    ((isCompact_closedBall 0 B).prod (isCompact_closedBall 0 B))
  have hval (μ : ℝ) (z : ℝ × ℝ) :
      ω.floerJetCoeff (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u z =
        jetCoeffAt ω (fun q y ↦ (J q y).toLinearMap.toContinuousLinearMap) Ks Kt
          ((μ, ((projIcc (-|R|) |R| (neg_le_self (abs_nonneg R)) z.1 : ℝ), z.2)), u z,
            fderiv ℝ u z (0, 1)) := by
    rw [floerJetCoeff_eq_jetCoeffAt, jetCoeffAt_projIcc ω (hcyl μ)]
    exact jetCoeffAt_family ω (fun q y ↦ (J q y).toLinearMap.toContinuousLinearMap) Ks Kt μ _
  have hmem {μ : ℝ} (hμ : |μ - lam| ≤ 1) {z : ℝ × ℝ} (hz : z.2 ∈ Icc (0 : ℝ) 1) :
      ((μ, ((projIcc (-|R|) |R| (neg_le_self (abs_nonneg R)) z.1 : ℝ), z.2)), u z,
        fderiv ℝ u z (0, 1)) ∈ K := by
    obtain ⟨h₁, h₂⟩ := hB z.1 z.2 hz
    obtain ⟨hμ₁, hμ₂⟩ := abs_le.1 hμ
    exact ⟨⟨⟨by linarith, by linarith⟩, Subtype.prop _, hz⟩, mem_closedBall_zero_iff.2 h₁,
      mem_closedBall_zero_iff.2 h₂⟩
  obtain ⟨δ, hδ, hΦ⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous
    (continuous_jetCoeffAt ω (J := fun q y ↦ (J q y).toLinearMap.toContinuousLinearMap) hJ hKs
      hKt).continuousOn) r hr
  refine ⟨min 1 δ, lt_min one_pos hδ, fun μ hμ z hz ↦ ?_⟩
  rw [lt_min_iff] at hμ
  rw [hval, hval]
  refine hΦ _ (hmem hμ.1.le hz) _ (hmem (by simp) hz) ?_
  -- The two points differ only in the parameter.
  simpa [Prod.dist_eq, Real.dist_eq] using hμ.2

/-- **Continuity of the coefficient fields along a family of data in `L^∞`.** Under the
hypotheses of `exists_pos_forall_dist_floerJetCoeff_family_lt`, with `u` of class `C¹`, the
coefficient field of the linearized Floer operator of the data at `μ` along `u` depends
continuously on `μ` in `L^∞` of the strip. -/
private theorem tendsto_eLpNorm_floerJetCoeff_family (ω : SymplecticForm V)
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : ∀ μ, Floer.IsCylindricalNearEnds (fun w ↦ J (μ, w)) (fun w ↦ Ks (μ, w))
      (fun w ↦ Kt (μ, w)) (Jm μ) (Jp μ) Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt)) (hu : ContDiff ℝ 1 u)
    {B : ℝ} (hB : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t)‖ ≤ B ∧ ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ B)
    (lam : ℝ) :
    Tendsto (fun μ : ℝ ↦ eLpNorm
      (ω.floerJetCoeff (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u -
        ω.floerJetCoeff (fun w y ↦ (J (lam, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (lam, w)) (fun w ↦ Kt (lam, w)) u) ∞ stripMeasure) (𝓝 lam) (𝓝 0) :=
  have hM (μ : ℝ) := ω.continuous_floerJetCoeff
    (J := fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap) (u := u)
    (hcyl μ).contDiffAt_almostComplex (hcyl μ).contDiffAt_hamiltonianS
    (hcyl μ).contDiffAt_hamiltonianT hu
  tendsto_eLpNorm_sub_of_forall_dist_lt
    (.of_forall fun μ ↦ ((hM μ).sub (hM lam)).aestronglyMeasurable) fun _ hr ↦ by
      obtain ⟨η, hη, h⟩ :=
        exists_pos_forall_dist_floerJetCoeff_family_lt ω hcyl hJ hKs hKt hB lam hr
      exact Metric.eventually_nhds_iff.2 ⟨η, hη, fun μ hμ ↦ h μ hμ⟩

/-- The path of almost complex structures from `J` to `J'`: at `(μ, z)` and `y` it is the
continuation homotopy, relative to `J₀`, from `J z y` to `J' z y` at time `μ`. It is `J` for
`μ ≤ 0` and `J'` for `μ ≥ 1`. -/
private def pathAlmostComplex {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ∀ z y, ω.Tames (J z y)) (hJ' : ∀ z y, ω.Tames (J' z y)) (p : ℝ × (ℝ × ℝ)) (y : V) :
    AlmostComplexStructure V :=
  Floer.continuationAlmostComplex h₀ (fun _ q ↦ J q.1 q.2) (fun _ q ↦ J' q.1 q.2)
    (fun _ q ↦ hJ q.1 q.2) (fun _ q ↦ hJ' q.1 q.2) (p.1, 0) (p.2, y)

/-- The segment of Hamiltonians from `K` to `K'`, with parameter `μ`: the linear homotopy with
profile `id` from `K` to `K'`, viewed as time-independent Hamiltonians on `(ℝ × ℝ) × V`. -/
private def pathHamiltonian (K K' : ℝ × ℝ → V → ℝ) (p : ℝ × (ℝ × ℝ)) (y : V) : ℝ :=
  Floer.linearHomotopy id (fun _ q ↦ K q.1 q.2) (fun _ q ↦ K' q.1 q.2) (p.1, 0) (p.2, y)

/-- The path of almost complex structures is `J` at `μ = 0`. -/
private theorem pathAlmostComplex_zero {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y)) (z : ℝ × ℝ) (y : V) :
    pathAlmostComplex h₀ hJt hJ't (0, z) y = J z y := by
  rw [pathAlmostComplex]
  exact Floer.continuationAlmostComplex_of_nonpos h₀ (z := ((0 : ℝ), (0 : ℝ))) le_rfl (z, y)

/-- The path of almost complex structures is `J'` at `μ = 1`. -/
private theorem pathAlmostComplex_one {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y)) (z : ℝ × ℝ) (y : V) :
    pathAlmostComplex h₀ hJt hJ't (1, z) y = J' z y := by
  rw [pathAlmostComplex]
  exact Floer.continuationAlmostComplex_of_one_le h₀ (z := ((1 : ℝ), (0 : ℝ))) le_rfl (z, y)

/-- The path of almost complex structures between `ω`-compatible structures is `ω`-compatible. -/
private theorem compatible_pathAlmostComplex {ω : SymplecticForm V}
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} (hJc : ∀ z y, ω.Compatible (J z y))
    (hJ'c : ∀ z y, ω.Compatible (J' z y)) (p : ℝ × (ℝ × ℝ)) (y : V) :
    ω.Compatible (pathAlmostComplex h₀ (fun z y ↦ (hJc z y).tames) (fun z y ↦ (hJ'c z y).tames)
      p y) := by
  rw [pathAlmostComplex]
  exact Floer.compatible_continuationAlmostComplex h₀
    (fun (_ : ℝ) (q : (ℝ × ℝ) × V) ↦ hJc q.1 q.2) (fun (_ : ℝ) (q : (ℝ × ℝ) × V) ↦ hJ'c q.1 q.2)
    _ _

/-- The path of almost complex structures is `C¹` when its endpoints are. -/
private theorem contDiff_pathAlmostComplex {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) :
    ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × V ↦
      (pathAlmostComplex h₀ hJt hJ't p.1 p.2).toLinearMap.toContinuousLinearMap :=
  (Floer.contDiff_continuationAlmostComplex (F := (ℝ × ℝ) × V) h₀ (hJ.comp contDiff_snd)
    (hJ'.comp contDiff_snd)).comp
      ((contDiff_fst.fst.prodMk contDiff_const).prodMk (contDiff_fst.snd.prodMk contDiff_snd))

omit [FiniteDimensional ℝ V] in
/-- The segment of Hamiltonians is `C²` when its endpoints are. -/
private theorem contDiff_pathHamiltonian {K K' : ℝ × ℝ → V → ℝ} (hK : ContDiff ℝ 2 (uncurry K))
    (hK' : ContDiff ℝ 2 (uncurry K')) : ContDiff ℝ 2 (uncurry (pathHamiltonian K K')) :=
  (Floer.contDiff_uncurry_linearHomotopy (n := 2)
    (H₀ := fun (_ : ℝ) (q : (ℝ × ℝ) × V) ↦ K q.1 q.2)
    (H₁ := fun (_ : ℝ) (q : (ℝ × ℝ) × V) ↦ K' q.1 q.2) contDiff_id (hK.comp contDiff_snd)
    (hK'.comp contDiff_snd)).comp
      ((contDiff_fst.fst.prodMk contDiff_const).prodMk (contDiff_fst.snd.prodMk contDiff_snd))

/-- At each parameter, the path of almost complex structures at `z` depends only on `J z` and
`J' z`. -/
private theorem pathAlmostComplex_congr {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y)) (μ : ℝ) {z z' : ℝ × ℝ}
    (h : J z = J z') (h' : J' z = J' z') :
    pathAlmostComplex h₀ hJt hJ't (μ, z) = pathAlmostComplex h₀ hJt hJ't (μ, z') := by
  funext y
  rw [pathAlmostComplex, pathAlmostComplex]
  exact h₀.eq_of_cayley_eq (Floer.tames_continuationAlmostComplex h₀ _ _)
    (Floer.tames_continuationAlmostComplex h₀ _ _)
    (by simp only [Floer.cayley_continuationAlmostComplex, h, h'])

/-- Two sets of Floer data cylindrical near the ends with the same end Hamiltonians, with radii
`R` and `R'`, are joined by a path of data all cylindrical near the ends with the radius
`max R R'` and the same end Hamiltonians. At the parameter `μ` the almost complex structures of
the ends are those of the path at `s = ∓ max R R'`. -/
private theorem isCylindricalNearEnds_path {ω : SymplecticForm V}
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' Hm Hp R' u)
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKs' : ContDiff ℝ 2 (uncurry Ks'))
    (hKt : ContDiff ℝ 2 (uncurry Kt)) (hKt' : ContDiff ℝ 2 (uncurry Kt')) (μ : ℝ) :
    Floer.IsCylindricalNearEnds (fun w ↦ pathAlmostComplex h₀ hJt hJ't (μ, w))
      (fun w ↦ pathHamiltonian Ks Ks' (μ, w)) (fun w ↦ pathHamiltonian Kt Kt' (μ, w))
      (fun t ↦ pathAlmostComplex h₀ hJt hJ't (μ, (-max R R', t)))
      (fun t ↦ pathAlmostComplex h₀ hJt hJ't (μ, (max R R', t))) Hm Hp (max R R') u := by
  have h₁ := hcyl.mono (le_max_left R R')
  have h₂ := hcyl'.mono (le_max_right R R')
  -- Where both Hamiltonians equal the same end Hamiltonian, so does every point of the path.
  have hKeq {K K' : ℝ × ℝ → V → ℝ} {z : ℝ × ℝ} (e : V → ℝ) (he : K z = e) (he' : K' z = e) :
      pathHamiltonian K K' (μ, z) = e := by
    funext y
    simp [pathHamiltonian, Floer.linearHomotopy_def, he, he']
  exact
    { almostComplex_eq_of_le_neg := fun z hz ↦ pathAlmostComplex_congr h₀ hJt hJ't μ
        ((h₁.almostComplex_eq_of_le_neg z hz).trans
          (h₁.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le_neg z hz).trans
          (h₂.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
      almostComplex_eq_of_le := fun z hz ↦ pathAlmostComplex_congr h₀ hJt hJ't μ
        ((h₁.almostComplex_eq_of_le z hz).trans (h₁.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le z hz).trans (h₂.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
      hamiltonianS_eq_zero := fun z hz ↦ hKeq _ (h₁.hamiltonianS_eq_zero z hz)
        (h₂.hamiltonianS_eq_zero z hz)
      hamiltonianT_eq_of_le_neg := fun z hz ↦ hKeq _ (h₁.hamiltonianT_eq_of_le_neg z hz)
        (h₂.hamiltonianT_eq_of_le_neg z hz)
      hamiltonianT_eq_of_le := fun z hz ↦ hKeq _ (h₁.hamiltonianT_eq_of_le z hz)
        (h₂.hamiltonianT_eq_of_le z hz)
      contDiffAt_almostComplex := fun z ↦
        ((contDiff_pathAlmostComplex h₀ hJt hJ't hJ hJ').comp
          ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)).contDiffAt
      contDiffAt_hamiltonianS := fun z ↦
        ((contDiff_pathHamiltonian hKs hKs').comp
          ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)).contDiffAt
      contDiffAt_hamiltonianT := fun z ↦
        ((contDiff_pathHamiltonian hKt hKt').comp
          ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)).contDiffAt }

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

/-- **The Fredholm property and the index along a family of data.** Let `(J_μ, K_{s,μ}, K_{t,μ})`
be a family of Floer data, `C¹` jointly in the parameter `μ`, the point of the cylinder and the
target point (with `C²` Hamiltonians), compatible with `ω`, and all cylindrical near the ends with
a common radius and the same end Hamiltonians `H±`; the almost complex structures of the ends may
depend on `μ`. Along a `C¹` map `u` asymptotic to nondegenerate orbits of `H±`, if the operator of
the data at `μ = 0` is Fredholm, then so is the operator of the data at `μ = 1`, with the same
index. -/
private theorem isFredholm_and_index_eq_of_family (ω : SymplecticForm V)
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : ∀ μ, Floer.IsCylindricalNearEnds (fun w ↦ J (μ, w)) (fun w ↦ Ks (μ, w))
      (fun w ↦ Kt (μ, w)) (Jm μ) (Jp μ) Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ p y, ω.Compatible (J p y)) (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J (0, w) y).toLinearMap.toContinuousLinearMap)
      (fun w ↦ Ks (0, w)) (fun w ↦ Kt (0, w)) u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J (1, w) y).toLinearMap.toContinuousLinearMap)
        (fun w ↦ Ks (1, w)) (fun w ↦ Kt (1, w)) u).IsFredholm ∧
      (ω.floerSobolevOperator (fun w y ↦ (J (1, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (1, w)) (fun w ↦ Kt (1, w)) u).index =
        (ω.floerSobolevOperator (fun w y ↦ (J (0, w) y).toLinearMap.toContinuousLinearMap)
          (fun w ↦ Ks (0, w)) (fun w ↦ Kt (0, w)) u).index := by
  have hR := le_abs_self R
  have hR' : -|R| ≤ -R := by linarith
  -- At each parameter, the data of the ends are those of the cylinder at `s = ∓|R|`; so they are
  -- `C¹` (with `C²` Hamiltonians) and compatible.
  have hend (μ : ℝ) := And.intro
    (endData_of_eq ω (J := fun w ↦ J (μ, w)) (Kt := fun w ↦ Kt (μ, w)) (-|R|)
      (fun t ↦ (hcyl μ).almostComplex_eq_of_le_neg (_, t) hR')
      (fun t ↦ (hcyl μ).hamiltonianT_eq_of_le_neg (_, t) hR')
      (hJ.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd))
      (hKt.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)) fun z ↦ hJc (μ, z))
    (endData_of_eq ω (J := fun w ↦ J (μ, w)) (Kt := fun w ↦ Kt (μ, w)) |R|
      (fun t ↦ (hcyl μ).almostComplex_eq_of_le (_, t) hR)
      (fun t ↦ (hcyl μ).hamiltonianT_eq_of_le (_, t) hR)
      (hJ.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd))
      (hKt.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)) fun z ↦ hJc (μ, z))
  have hHm := (hend 0).1.2.1
  have hHp := (hend 0).2.2.1
  set M : ℝ → ℝ × ℝ → V × V × V →L[ℝ] V := fun μ ↦ ω.floerJetCoeff
    (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks (μ, w))
    (fun w ↦ Kt (μ, w)) u
  have hM (μ : ℝ) : MemLp (M μ) ∞ stripMeasure :=
    ω.memLp_floerJetCoeff_of_cylindrical (hcyl μ) hu hHm (hend μ).1.1 huxm hδm hHp (hend μ).2.1
      huxp hδp
  have hest (μ : ℝ) : ∃ C T, HasSemiFredholmEstimate (M μ) C T :=
    ω.exists_hasSemiFredholmEstimate_floerJetCoeff_of_cylindrical (hcyl μ) hu
      (fun z ↦ hJc (μ, z) _) hXm hHm hxm hndm (hend μ).1.1 (fun t ↦ (hend μ).1.2.2 t _) huxm hδm
      hXp hHp hxp hndp (hend μ).2.1 (fun t ↦ (hend μ).2.2.2 t _) huxp hδp
  -- `u` and its derivative in `t` are bounded on the strip.
  obtain ⟨B, hB⟩ := exists_forall_norm_le_and_norm_fderiv_apply_le_of_sliceDefect
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHm).continuous
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHp).continuous hu
    (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt)
    (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt) huxm hδm huxp hδp
  have hcont (μ : ℝ) (_ : μ ∈ univ) :
      Tendsto (fun ν ↦ eLpNorm (M ν - M μ) ∞ stripMeasure) (𝓝[univ] μ) (𝓝 0) := by
    rw [nhdsWithin_univ]
    exact tendsto_eLpNorm_floerJetCoeff_family ω hcyl hJ hKs hKt hu hB μ
  have key := isFredholm_and_index_eq_of_hasSemiFredholmEstimate isPreconnected_univ
    (fun μ _ ↦ hM μ) hcont (fun μ _ ↦ hest μ) (mem_univ 0) (mem_univ 1)
    (by simpa only [M, ← floerSobolevOperator_def] using h)
  simpa only [M, ← floerSobolevOperator_def] using key

/-- The Fredholm property and the index pass from the data `(J, K_s, K_t)` to the data
`(J', K'_s, K'_t)` with the same end Hamiltonians, along the path of data joining them. -/
private theorem isFredholm_and_index_eq_of_cylindrical_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' Hm Hp R' u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u).IsFredholm ∧
      (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
          u).index =
        (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          u).index := by
  -- The path of data from `(J, K_s, K_t)` at `μ = 0` to `(J', K'_s, K'_t)` at `μ = 1`.
  have h₀ := hJc 0 0
  have hJt (z : ℝ × ℝ) (y : V) := (hJc z y).tames
  have hJ't (z : ℝ × ℝ) (y : V) := (hJ'c z y).tames
  have key := isFredholm_and_index_eq_of_family ω
    (J := pathAlmostComplex h₀ hJt hJ't) (Ks := pathHamiltonian Ks Ks')
    (Kt := pathHamiltonian Kt Kt')
    (Jm := fun μ t ↦ pathAlmostComplex h₀ hJt hJ't (μ, (-max R R', t)))
    (Jp := fun μ t ↦ pathAlmostComplex h₀ hJt hJ't (μ, (max R R', t)))
    (isCylindricalNearEnds_path h₀ hcyl hcyl' hJt hJ't hJ hJ' hKs hKs' hKt hKt')
    (contDiff_pathAlmostComplex h₀ hJt hJ't hJ hJ') (contDiff_pathHamiltonian hKs hKs')
    (contDiff_pathHamiltonian hKt hKt') (fun p y ↦ compatible_pathAlmostComplex h₀ hJc hJ'c p y)
    hu hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp
    (by simpa [pathAlmostComplex_zero, pathHamiltonian.eq_unfold] using h)
  simpa [pathAlmostComplex_zero, pathAlmostComplex_one, pathHamiltonian.eq_unfold] using key

/-- **The Fredholm property of the linearized Floer operator depends only on the end
Hamiltonians.** Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be Floer data that are `C¹` (with `C²`
Hamiltonians) on the whole cylinder, compatible with `ω`, and cylindrical near the ends with the
same end Hamiltonians: equal to `(J₋_t, 0, H₋_t)` and `(J'₋_t, 0, H₋_t)` for `s` near `-∞` and to
`(J₊_t, 0, H₊_t)` and `(J'₊_t, 0, H₊_t)` for `s` near `+∞`, possibly with different radii. The
almost complex structures may differ everywhere, also on the ends. Let `u` be a `C¹` map whose
loops converge uniformly to nondegenerate one-periodic orbits `x₋` of `H₋` at `-∞` and `x₊` of
`H₊` at `+∞`, with slice defects `∂t u - X_{H±_t}(u)` tending uniformly to zero at the
corresponding end. Then the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the
linearized Floer operator of the first data is Fredholm if and only if that of the second data
is. -/
theorem isFredholm_floerSobolevOperator_iff_of_cylindrical_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' Hm Hp R' u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).IsFredholm ↔
      (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u).IsFredholm :=
  ⟨fun h ↦ (isFredholm_and_index_eq_of_cylindrical_data ω hcyl hcyl' hJ hKs hKt hJ' hKs' hKt' hJc
      hJ'c hu hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp h).1,
    fun h ↦ (isFredholm_and_index_eq_of_cylindrical_data ω hcyl' hcyl hJ' hKs' hKt' hJ hKs hKt
      hJ'c hJc hu hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp h).1⟩

/-- **The index of the linearized Floer operator depends only on the end Hamiltonians.** Under
the hypotheses of `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_cylindrical_data`,
if the realization `D_u` of the linearized Floer operator of the first data is Fredholm, then that
of the second data has the same index. -/
theorem index_floerSobolevOperator_eq_of_cylindrical_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' Hm Hp R' u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u).index =
      (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).index :=
  (isFredholm_and_index_eq_of_cylindrical_data ω hcyl hcyl' hJ hKs hKt hJ' hKs' hKt' hJc hJ'c hu
    hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp h).2

end Invariance

section Compatible

/-! ### Every compatible almost complex structure -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized Floer operator on the cylinder is Fredholm for every compatible almost complex
structure.** Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω`
is `Im ⟪·, ·⟫`, and let the Floer data `(J, K_s, K_t)` be `C¹` (with `C²` Hamiltonians) on the
whole cylinder, compatible with `ω`, and cylindrical near the ends: equal to `(J₋_t, 0, H₋_t)` for
`s ≤ -R` and to `(J₊_t, 0, H₊_t)` for `s ≥ R`. Let `H±` be one-periodic, jointly `C³`
time-dependent Hamiltonians whose suspended vector fields are globally Lipschitz, and let `x±` be
one-periodic orbits of `H±` with `x±(0)` a nondegenerate fixed point of the time-one map. If `u` is
a `C¹` map whose loops converge uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, with slice defects
`∂t u - X_{H±_t}(u)` tending uniformly to zero at the corresponding end, then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator is Fredholm. By
`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`, its index is that of
the data `(i, K_s, K_t)` with the complex structure `i` of `F`. -/
theorem isFredholm_floerSobolevOperator_of_cylindrical_of_compatible (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {Jm Jp : ℝ → F → AlmostComplexStructure F}
    {R : ℝ} {u : ℝ × ℝ → F} (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  -- The data `(i, K_s, K_t)` have the same end Hamiltonians, and their operator is Fredholm by
  -- the parametrix built from the invertible stationary end operators.
  have hcyl₀ : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      Ks Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u :=
    { almostComplex_eq_of_le_neg := fun _ _ ↦ rfl
      almostComplex_eq_of_le := fun _ _ ↦ rfl
      hamiltonianS_eq_zero := hcyl.hamiltonianS_eq_zero
      hamiltonianT_eq_of_le_neg := hcyl.hamiltonianT_eq_of_le_neg
      hamiltonianT_eq_of_le := hcyl.hamiltonianT_eq_of_le
      contDiffAt_almostComplex := fun _ ↦ contDiffAt_const
      contDiffAt_hamiltonianS := hcyl.contDiffAt_hamiltonianS
      contDiffAt_hamiltonianT := hcyl.contDiffAt_hamiltonianT }
  have h₀ := ω.isFredholm_floerSobolevOperator_of_cylindrical hω hcyl₀ hu.continuous hXm hHm
    hHmper hxm hxmper hndm huxm hXp hHp hHpper hxp hxpper hndp huxp
  -- Deforming the almost complex structures from `i` to `J` keeps the operator Fredholm.
  exact (isFredholm_floerSobolevOperator_iff_of_cylindrical_data ω hcyl₀ hcyl contDiff_const hKs
    hKt hJ hKs hKt (fun _ _ ↦ ω.compatible_ofComplexModule_of_forall_eq_im_inner hω) hJc hu hXm
    hxm hndm huxm hδm hXp hxp hndp huxp hδp).1 h₀

/-- **The linearized Floer operator along a Floer trajectory is Fredholm for every compatible
almost complex structure.** Let `F` be a finite-dimensional complex inner product space whose
symplectic form `ω` is `Im ⟪·, ·⟫`, let `J_t(y)` be a `C¹` family of `ω`-compatible almost complex
structures, and let `H` be a one-periodic, jointly `C³` time-dependent Hamiltonian whose suspended
vector field is globally Lipschitz, with one-periodic orbits `x₋` and `x₊` whose initial points are
nondegenerate fixed points of the time-one map. For the `s`-independent Floer data `(J_t, 0, H_t)`
and a `C¹` map `u` whose loops converge uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, with slice
defect `∂t u - X_{H_t}(u)` tending uniformly to zero at both ends, the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator is Fredholm. -/
theorem isFredholm_floerSobolevOperator_of_compatible (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {J : ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 1 fun p : ℝ × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ t y, ω.Compatible (J t y)) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u).IsFredholm := by
  have hH₂ : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  exact ω.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible hω
    (Floer.isCylindricalNearEnds_comp_snd hJ hH₂ (R := 0) u)
    (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)) contDiff_const
    (hH₂.comp (contDiff_fst.snd.prodMk contDiff_snd)) (fun z ↦ hJc z.2) hu hX hH hHper hxm hxmper
    hndm huxm hδm hX hH hHper hxp hxpper hndp huxp hδp

end Compatible

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
    (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) (R := 0) contDiff_const hH₂
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

section EqualEnds

variable {J : ℝ × ℝ → F → AlmostComplexStructure F} {Ks Kt : ℝ × ℝ → F → ℝ}
  {Jm Jp : ℝ → F → AlmostComplexStructure F} {R : ℝ}
  (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp H H R u)
  (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
  (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
  (hJc : ∀ z y, ω.Compatible (J z y))

include hH hHp hx hxp hu hum hδm hup hδp hcyl hJ hKs hKt hJc in
/-- **The linearized Floer operator for data with equal ends has index zero.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and let
`x` be a one-periodic orbit of a one-periodic, jointly `C³` time-dependent Hamiltonian `H` whose
suspended vector field is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the
time-one map. Let `(J, K_s, K_t)` be Floer data, `C¹` (with `C²` Hamiltonians) on the whole
cylinder and compatible with `ω`, which are cylindrical near the ends with the Hamiltonian `H` at
both ends: equal to `(J₋_t, 0, H_t)` for `s` near `-∞` and to `(J₊_t, 0, H_t)` for `s` near `+∞`,
such as the data of a continuation cylinder from `H` to itself. Let `u` be a `C¹` map whose loops
converge uniformly to `x` at both ends, with slice defect `∂t u - X_{H_t}(u)` tending uniformly to
zero at both ends. Then the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the
linearized Floer operator of these data has index zero; it is Fredholm by
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`. -/
theorem index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt_of_cylindrical
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).index = 0 := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hH₂ : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  -- Compare with the `s`-independent data `(i, 0, H_t)`, whose operator has index zero.
  obtain ⟨h₀, hi₀⟩ :=
    isFredholm_floerSobolevOperator_and_index_eq_zero ω hX hH hHp hx hxp hu hum hδm hup hδp hω hnd
  obtain ⟨-, hi⟩ := isFredholm_and_index_eq_of_cylindrical_data ω
    (Floer.isCylindricalNearEnds_comp_snd (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (R := 0) contDiff_const hH₂ u) hcyl contDiff_const contDiff_const
    (hH₂.comp (contDiff_fst.snd.prodMk contDiff_snd)) hJ hKs hKt
    (fun _ _ ↦ ω.compatible_ofComplexModule_of_forall_eq_im_inner hω) hJc hu hX hx hnd hum hδm hX
    hx hnd hup hδp h₀
  exact hi.trans hi₀

end EqualEnds

end Unitary

end TauCeti.SymplecticForm
