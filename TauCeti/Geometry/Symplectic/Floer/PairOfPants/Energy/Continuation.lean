/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity

/-!
# The energy of a pair of pants with continuation necks

Let `K = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L` be the pair-of-pants
perturbation with continuation necks at the positions `L_q` from inner Hamiltonians `G_q` to outer
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`. Far out on each end it is `H_q(t) dt`, so
the energy identity of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity` applies to
it. For a solution `u` of the Floer equation `(du - X_K)^{0,1} = 0` with tame almost complex
structures, into a symplectic vector space, whose end loops `t ↦ u(φ_q(s, t))` have actions
converging to `a_q` as `±s → ∞`, the energy is

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)`,

where the actions are those of the outer Hamiltonians `H_q`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq`).

If `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, the curvature along every map continuous on `S` is
integrable (`SymplecticForm.integrable_hamiltonianCurvature_pairOfPantsContinuationPerturbation`)
with integral at most `∑ q, (B_q + D_q)` in absolute value, whatever the neck positions. This gives
the energy bound `E(u) ≤ a_0 + a_1 - a_∞ + ∑ q, (B_q + D_q)`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`) and the
action bound `a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + D_q)`
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation`),
uniformly in the neck positions although the necks become arbitrarily long. These are the bounds
that confine the one-parameter families of pairs of pants with moving necks, whose broken ends are
the compositions of continuation maps with pair-of-pants products, to finitely many classes below
each energy level.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ}
  {L : Puncture → ℝ} {u : ℝ × ℝ → V}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Beyond the height `2 + ∑ q, |L_q|` on each end, past every neck and collar, the perturbation
is `H_q(t) dt`. -/
private theorem pairOfPantsContinuationPerturbation_eq_smul_endAngularForm_of_le {r : Puncture}
    {w : ℂ} (hw : 2 + ∑ q, |L q| ≤ r.endSign * (r.endCoord w).re) (x : V) :
    pairOfPantsContinuationPerturbation G H L w x = H r (r.endCoord w).im x • r.endAngularForm w :=
  have hL : L r ≤ ∑ q, |L q| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun q _ ↦ abs_nonneg (L q)) (Finset.mem_univ r))
  pairOfPantsContinuationPerturbation_eq_smul_endAngularForm
    (by linarith [Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) ↦ abs_nonneg (L q)])
    (by linarith) x

variable [FiniteDimensional ℝ V]

/-- **The curvature of the pair of pants with continuation necks is integrable.** If
`|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then along any map continuous on
`S = ℂ ∖ {0, 1}` the curvature term `R_K(u)` is integrable over the plane, for all neck
positions. -/
theorem integrable_hamiltonianCurvature_pairOfPantsContinuationPerturbation (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ)
    (hu : ContinuousOn u thricePuncturedSphereReal) :
    Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) := by
  have hK (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z)
        x v) (thricePuncturedSphereReal ×ˢ univ) := fun p hp ↦
    (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hp.1 p.2
      v).contDiffWithinAt
  refine ⟨?_, (lintegral_enorm_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG
    hH hGs hHs hGB hHB hD L u).trans_lt (ENNReal.sum_lt_top.2 fun q _ ↦
      ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)⟩
  -- The curvature is continuous on `S`, whose complement is null.
  rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal]
  exact (ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal hu (hK 1)
    (hK Complex.I)).aestronglyMeasurable isOpen_thricePuncturedSphereReal.measurableSet

/-- **The energy identity for the pair of pants with continuation necks.** Let `K` be the
pair-of-pants perturbation with continuation necks at the positions `L_q` from period-one `C¹`
inner Hamiltonians `G_q` to outer Hamiltonians `H_q`, and let `u` be a `C²` map from
`S = ℂ ∖ {0, 1}` to a symplectic vector space which solves the Floer equation
`(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J(z)` tamed by `ω`, and whose
curvature term `R_K(u)` is integrable. If on each end `q` the actions `A_{H_q}` of the loops
`t ↦ u(φ_q(s, t))` tend to `a_q` as `±s → ∞`, then the energy of `u` is

`E(u) = a_0 + a_1 - a_∞ - ∫ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (L : Puncture → ℝ) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ENNReal.ofReal (∑ q, q.endSign * a q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) :=
  lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm ω
    (fun _ hz x v ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz x v)
    (fun _ _ x hw ↦ pairOfPantsContinuationPerturbation_eq_smul_endAngularForm_of_le hw x) hH
    (fun q ↦ (hHs q).continuous) hu
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)) hR ha

/-- **The energy bound for the pair of pants with continuation necks.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq`, without the
integrability of the curvature, if `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then the energy
of `u` is at most `a_0 + a_1 - a_∞ + ∑ q, (B_q + D_q)`, whatever the neck positions. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ)
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≤
      ENNReal.ofReal (∑ q, q.endSign * a q + ∑ q, (B q + D q)) := by
  rw [lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq ω hG hH hGs hHs L hu hJ
    hfloer (integrable_hamiltonianCurvature_pairOfPantsContinuationPerturbation ω hG hH hGs hHs hGB
      hHB hD L hu.continuousOn) ha]
  refine ENNReal.ofReal_le_ofReal (sub_le_iff_le_add.2 ?_)
  have h := neg_abs_le (∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z))
  rw [← setIntegral_univ] at h ⊢
  linarith [abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs
    hHs hGB hHB hD L u univ]

/-- **The action bound for the pair of pants with continuation necks.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`, the limiting
action of the output end is at most the sum of the limiting actions of the input ends plus
`∑ q, (B_q + D_q)`:

`a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + D_q)`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ)
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    a inf ≤ a zero + a one + ∑ q, (B q + D q) := by
  set R := ∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)
  -- The energy is integrable and nonnegative, and it is the signed sum of the actions minus `R`.
  have hK (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) (x : V) (v : ℂ) :=
    contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz x v
  have hKH (q : Puncture) (w : ℂ) (x : V) (hw : 2 + ∑ q, |L q| ≤ q.endSign * (q.endCoord w).re) :=
    pairOfPantsContinuationPerturbation_eq_smul_endAngularForm_of_le (G := G) (H := H) hw x
  have he (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have hRi := integrable_hamiltonianCurvature_pairOfPantsContinuationPerturbation ω hG hH hGs hHs
    hGB hHB hD L hu.continuousOn
  have hEq := integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm ω hK
    hKH hH (fun q ↦ (hHs q).continuous) hu
    (integrable_floerEnergyDensity_of_eq_smul_endAngularForm ω hK hKH hH
      (fun q ↦ (hHs q).continuous) hu he hRi ha) hRi ha
  have hpos := integral_nonneg_of_ae (μ := volume) (by
    filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz using he z hz)
  have hR : |R| ≤ ∑ q, (B q + D q) := by
    simpa only [setIntegral_univ] using
      abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs
        hGB hHB hD L u univ
  rw [hEq] at hpos
  simp only [sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul] at hpos
  linarith [neg_abs_le R]

end SymplecticForm

end TauCeti
