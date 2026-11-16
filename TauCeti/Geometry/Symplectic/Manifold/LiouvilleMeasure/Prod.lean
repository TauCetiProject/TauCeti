/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.MeasureTheory.Integral.Bochner.Alternating

/-!
# The Liouville measure of a product

Let `σ` and `τ` be two-forms on second-countable manifolds `M` and `N` modelled on spaces of
dimensions `2 n` and `2 m`. The product `M × N` carries the product form
`σ ⊕ τ = pr₁^* σ + pr₂^* τ` (`TauCeti.SmoothTwoForm.prod`), and its Liouville measure is the
product of the Liouville measures of the factors
(`TauCeti.SmoothTwoForm.liouvilleMeasure_prod`):

`|(σ ⊕ τ)^(n + m) / (n + m)!| = |σⁿ / n!| ⊗ |τᵐ / m!|`.

In a product chart, the coefficient of `(σ ⊕ τ)^(n + m) / (n + m)!` in the concatenation of bases
of the two model spaces is the product of the coefficients of the volume forms of the factors
(`TauCeti.SmoothTwoForm.volumeForm_prod_apply_append`), and the Haar measure of the concatenated
basis is the product of the Haar measures. Since the density `|ω(b)|` of a top form against the
Haar measure of a basis `b` does not depend on `b`, Fubini's theorem gives the formula on
rectangles inside a product chart, and on each product chart domain the two measures then agree.
No nondegeneracy is needed: a degenerate factor makes both sides vanish where it degenerates.

Pushing forward along a product map `μ × ν`, such as the moment map `(μ, ν)` of the product of
two Hamiltonian torus actions, gives the product of the Duistermaat–Heckman measures
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_prod`).

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_prod`: the Liouville measure of a product is the product
  of the Liouville measures.
* `TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_prod`: the Duistermaat–Heckman measure of a
  product map is the product of the Duistermaat–Heckman measures.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30.1 (the Liouville and Duistermaat–Heckman measures).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n m : ℕ}

/-- In a product chart, the coefficient of the volume form of `σ ⊕ τ` in the concatenation of
bases of the two model spaces is the product of the coefficients of the volume forms of `σ` and
`τ` in these bases. -/
private theorem inChartAt_volumeForm_prod_apply (hn : finrank ℝ E = 2 * n)
    (hm : finrank ℝ F = 2 * m) (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) {p : M × N}
    {z : E × F} (hz : z ∈ (extChartAt (I.prod J) p).target) (b₁ : Basis (Fin (2 * n)) ℝ E)
    (b₂ : Basis (Fin (2 * m)) ℝ F) :
    RoughForm.inChartAt ((prod σ τ).volumeForm (n + m)).1 p z
        ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.mul_add 2 n m).symm))) =
      RoughForm.inChartAt (σ.volumeForm n).1 p.1 z.1 b₁ *
        RoughForm.inChartAt (τ.volumeForm m).1 p.2 z.2 b₂ := by
  have hq : (extChartAt (I.prod J) p).symm z =
      ((extChartAt I p.1).symm z.1, (extChartAt J p.2).symm z.2) := by
    rw [extChartAt_prod, PartialEquiv.prod_coe_symm]
  have hb : ⇑((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.mul_add 2 n m).symm))) =
      fun r ↦ Fin.append (α := E × F) (fun i ↦ (b₁ i, 0)) (fun j ↦ (0, b₂ j))
        (Fin.cast (Nat.mul_add 2 n m) r) := by
    funext r
    simpa [Basis.reindex_apply] using
      congrFun (Basis.coe_prod_reindex_finSumFinEquiv b₁ b₂) (Fin.cast (Nat.mul_add 2 n m) r)
  -- The inverse product chart differentiates componentwise.
  have hfam : (fun r ↦ mfderivWithin 𝓘(ℝ, E × F) (I.prod J) (extChartAt (I.prod J) p).symm
      (range (I.prod J)) z (Fin.append (α := E × F) (fun i ↦ (b₁ i, 0)) (fun j ↦ (0, b₂ j))
        (Fin.cast (Nat.mul_add 2 n m) r))) =
      fun r ↦ (Manifold.tangentSpaceProdEquiv _).symm (Fin.append
        (fun i ↦ (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p.1).symm (range I) z.1 (b₁ i), 0))
        (fun j ↦ (0, mfderivWithin 𝓘(ℝ, F) J (extChartAt J p.2).symm (range J) z.2 (b₂ j)))
        (Fin.cast (Nat.mul_add 2 n m) r)) := by
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) (Fin.cast (Nat.mul_add 2 n m) r)
    · simp only [Fin.append_left]
      rw [mfderivWithin_extChartAt_symm_prod_apply hz, Manifold.tangentSpaceProdEquiv_symm_apply]
      exact Prod.ext rfl (map_zero _)
    · simp only [Fin.append_right]
      rw [mfderivWithin_extChartAt_symm_prod_apply hz, Manifold.tangentSpaceProdEquiv_symm_apply]
      exact Prod.ext (map_zero _) rfl
  rw [RoughForm.inChartAt_apply, RoughForm.inChartAt_apply, RoughForm.inChartAt_apply, hb]
  beta_reduce
  rw [hfam]
  refine (volumeForm_prod_apply_append hn hm σ τ _
    (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I p.1).symm (range I) z.1 (b₁ i))
    (fun j ↦ mfderivWithin 𝓘(ℝ, F) J (extChartAt J p.2).symm (range J) z.2 (b₂ j))).trans ?_
  rw [hq]

section Measure

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [hn : Fact (finrank ℝ E = 2 * n)] [hm : Fact (finrank ℝ F = 2 * m)]

omit [TopologicalSpace H] [TopologicalSpace H'] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
/-- The product of model spaces of dimensions `2 n` and `2 m` has dimension `2 (n + m)`. This
is the dimension instance for the Liouville measure of a product form. -/
instance fact_finrank_prod_eq_two_mul_add : Fact (finrank ℝ (E × F) = 2 * (n + m)) :=
  ⟨by rw [finrank_prod, hn.out, hm.out, Nat.mul_add]⟩

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MeasurableSpace N]
  [BorelSpace N] [SecondCountableTopology N] in
/-- **Fubini in a product chart.** Over a rectangle `S₁ × S₂` of chart coordinates, the integral
of the coefficient of the volume form of `σ ⊕ τ` is the product of the integrals of the
coefficients of the volume forms of `σ` and `τ`. The coefficient is computed in the concatenation
of the bases of the factors, whose Haar measure is the product measure; the Borel structure of
`E × F` is taken arbitrary so that it can be identified with the product structure. -/
private theorem setLIntegral_inChartAt_volumeForm_prod [mEF : MeasurableSpace (E × F)]
    [BorelSpace (E × F)] (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) {x : M} {y : N}
    {S₁ : Set E} {S₂ : Set F} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hS₁x : S₁ ⊆ (extChartAt I x).target) (hS₂y : S₂ ⊆ (extChartAt J y).target) :
    ∫⁻ z in S₁ ×ˢ S₂,
        ENNReal.ofReal |RoughForm.inChartAt ((prod σ τ).volumeForm (n + m)).1 (x, y) z
          (finBasisOfFinrankEq ℝ (E × F) (Fact.out : finrank ℝ (E × F) = 2 * (n + m)))|
        ∂(finBasisOfFinrankEq ℝ (E × F) (Fact.out : finrank ℝ (E × F) = 2 * (n + m))).addHaar =
      (∫⁻ z in S₁, ENNReal.ofReal
          |RoughForm.inChartAt (σ.volumeForm n).1 x z (finBasisOfFinrankEq ℝ E hn.out)|
          ∂(finBasisOfFinrankEq ℝ E hn.out).addHaar) *
        ∫⁻ z in S₂, ENNReal.ofReal
          |RoughForm.inChartAt (τ.volumeForm m).1 y z (finBasisOfFinrankEq ℝ F hm.out)|
          ∂(finBasisOfFinrankEq ℝ F hm.out).addHaar := by
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    (BorelSpace.measurable_eq (α := E × F)).trans (Prod.borelSpace.measurable_eq (α := E × F)).symm
  set b₁ := finBasisOfFinrankEq ℝ E hn.out
  set b₂ := finBasisOfFinrankEq ℝ F hm.out
  -- The coefficients of the factors are continuous on the chart targets.
  have hσ := ((σ.volumeForm n).isSmoothForm.of_le bot_le).continuousOn_inChartAt x
  have hτ := ((τ.volumeForm m).isSmoothForm.of_le bot_le).continuousOn_inChartAt y
  have hf : AEMeasurable (fun z ↦ ENNReal.ofReal |RoughForm.inChartAt (σ.volumeForm n).1 x z b₁|)
      (b₁.addHaar.restrict S₁) :=
    ((ENNReal.continuous_ofReal.comp continuous_abs).comp_continuousOn
      ((continuous_eval_const _).comp_continuousOn (hσ.mono hS₁x))).aemeasurable hS₁
  have hg : AEMeasurable (fun z ↦ ENNReal.ofReal |RoughForm.inChartAt (τ.volumeForm m).1 y z b₂|)
      (b₂.addHaar.restrict S₂) :=
    ((ENNReal.continuous_ofReal.comp continuous_abs).comp_continuousOn
      ((continuous_eval_const _).comp_continuousOn (hτ.mono hS₂y))).aemeasurable hS₂
  -- On the rectangle, the coefficient in the concatenated basis is a product.
  have hcoeff : ∀ z ∈ S₁ ×ˢ S₂,
      ENNReal.ofReal |RoughForm.inChartAt ((prod σ τ).volumeForm (n + m)).1 (x, y) z
        ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.mul_add 2 n m).symm)))| =
        ENNReal.ofReal |RoughForm.inChartAt (σ.volumeForm n).1 x z.1 b₁| *
          ENNReal.ofReal |RoughForm.inChartAt (τ.volumeForm m).1 y z.2 b₂| := by
    intro z hz
    have hz' : z ∈ (extChartAt (I.prod J) (x, y)).target := by
      rw [extChartAt_prod, PartialEquiv.prod_target]
      exact prod_mono hS₁x hS₂y hz
    rw [inChartAt_volumeForm_prod_apply hn.out hm.out σ τ hz', abs_mul,
      ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← withDensity_apply _ (hS₁.prod hS₂), ← Basis.addHaar_withDensity_ofReal_abs_apply_eq _
      ((b₁.prod b₂).reindex (finSumFinEquiv.trans (finCongr (Nat.mul_add 2 n m).symm))),
    withDensity_apply _ (hS₁.prod hS₂), Basis.addHaar_reindex, Basis.prod_addHaar,
    setLIntegral_congr_fun (hS₁.prod hS₂) hcoeff, ← Measure.prod_restrict,
    lintegral_prod_mul hf hg]

/-- The Liouville measure of `σ ⊕ τ` of a rectangle `A × B` inside a product chart domain is the
product of the Liouville measures of `A` and of `B`. -/
private theorem liouvilleMeasure_prod_apply_prod_of_subset (σ : SmoothTwoForm I M)
    (τ : SmoothTwoForm J N) {x : M} {y : N} {A : Set M} {B : Set N} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAx : A ⊆ (extChartAt I x).source)
    (hBy : B ⊆ (extChartAt J y).source) :
    (prod σ τ).liouvilleMeasure (n + m) (A ×ˢ B) =
      σ.liouvilleMeasure n A * τ.liouvilleMeasure m B := by
  have hsub : A ×ˢ B ⊆ (extChartAt (I.prod J) (x, y)).source := by
    rw [extChartAt_prod]
    exact prod_mono hAx hBy
  have himage : extChartAt (I.prod J) (x, y) '' (A ×ˢ B) =
      (extChartAt I x '' A) ×ˢ (extChartAt J y '' B) := by
    rw [extChartAt_prod, prod_image_image_eq, PartialEquiv.prod_coe]
  rw [liouvilleMeasure_apply_of_subset (hA.prod hB) hsub, liouvilleMeasure_apply_of_subset hA hAx,
    liouvilleMeasure_apply_of_subset hB hBy, himage]
  exact setLIntegral_inChartAt_volumeForm_prod (mEF := TauCeti.extChartAtMeasurableSpaceE) σ τ
    (hA.image_extChartAt x hAx) (hB.image_extChartAt y hBy)
    ((image_mono hAx).trans (extChartAt I x).image_source_eq_target.subset)
    ((image_mono hBy).trans (extChartAt J y).image_source_eq_target.subset)

/-- **The Liouville measure of a product is the product of the Liouville measures.** For two-forms
`σ` and `τ` on second-countable manifolds modelled on spaces of dimensions `2 n` and `2 m`, the
Liouville measure `|(σ ⊕ τ)^(n + m) / (n + m)!|` of the product form on `M × N` is the product
measure of `|σⁿ / n!|` and `|τᵐ / m!|`. Neither form needs to be nondegenerate. -/
@[simp]
theorem liouvilleMeasure_prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    (prod σ τ).liouvilleMeasure (n + m) = (σ.liouvilleMeasure n).prod (τ.liouvilleMeasure m) := by
  rw [liouvilleMeasure_def]
  refine (RoughForm.eq_measure_iff.2 fun p s hs hsub ↦ ?_).symm
  have hUV : (extChartAt (I.prod J) p).source =
      (extChartAt I p.1).source ×ˢ (extChartAt J p.2).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source]
  -- On the product chart domain `U × V`, both measures agree on measurable rectangles.
  have hrestrict : ((σ.liouvilleMeasure n).prod (τ.liouvilleMeasure m)).restrict
      ((extChartAt I p.1).source ×ˢ (extChartAt J p.2).source) =
      ((prod σ τ).liouvilleMeasure (n + m)).restrict
        ((extChartAt I p.1).source ×ˢ (extChartAt J p.2).source) := by
    rw [← Measure.prod_restrict]
    refine Measure.prod_eq fun A B hA hB ↦ ?_
    rw [Measure.restrict_apply (hA.prod hB), prod_inter_prod, Measure.restrict_apply hA,
      Measure.restrict_apply hB]
    exact liouvilleMeasure_prod_apply_prod_of_subset σ τ
      (hA.inter (isOpen_extChartAt_source p.1).measurableSet)
      (hB.inter (isOpen_extChartAt_source p.2).measurableSet) inter_subset_right
      inter_subset_right
  rw [← Measure.restrict_eq_self _ (hsub.trans hUV.subset), hrestrict,
    Measure.restrict_eq_self _ (hsub.trans hUV.subset)]
  exact liouvilleMeasure_apply_of_subset hs hsub

/-- **The Duistermaat–Heckman measure of a product.** For measurable maps `μ` on `M` and `ν` on
`N`, such as the moment maps of two Hamiltonian torus actions, the Duistermaat–Heckman measure of
`σ ⊕ τ` and the product map `μ × ν` is the product of the Duistermaat–Heckman measures of `μ` and
of `ν`. -/
theorem duistermaatHeckmanMeasure_prod {G G' : Type*} [MeasurableSpace G] [MeasurableSpace G']
    (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) {μ : M → G} {ν : N → G'}
    (hμ : Measurable μ) (hν : Measurable ν) :
    (prod σ τ).duistermaatHeckmanMeasure (n + m) (Prod.map μ ν) =
      (σ.duistermaatHeckmanMeasure n μ).prod (τ.duistermaatHeckmanMeasure m ν) := by
  rw [duistermaatHeckmanMeasure_def, duistermaatHeckmanMeasure_def,
    duistermaatHeckmanMeasure_def, liouvilleMeasure_prod, Measure.map_prod_map _ _ hμ hν]

end Measure

end TauCeti.SmoothTwoForm
