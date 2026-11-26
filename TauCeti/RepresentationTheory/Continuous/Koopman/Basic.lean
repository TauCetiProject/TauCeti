/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import TauCeti.MeasureTheory.Function.Lp.Subsingleton
public import TauCeti.MeasureTheory.Group.Action
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The Koopman representation on vector-valued `Lᵖ`

Let a group `G` act on a measurable space `X` by measurable maps preserving a measure `μ`, and let
`E` be a normed module over `𝕜`. Then `G` acts on `Lᵖ(X, E; μ)` by left-translation of arguments,
`(κ g f) x = f (g⁻¹ • x)`; the inverse makes this a representation of `G` rather than of the
domain-action wrapper `DomMulAct G` used by Mathlib's `DistribMulAction Mᵈᵐᵃ (Lp E p μ)`. Each
operator is a linear isometry, hence unitary on `L²(X, E; μ)` when `E` is an inner product space,
and for `G` acting on itself by left multiplication it recovers `MeasureTheory.Measure.leftRegular`.

No σ-finiteness, countability, or probability assumption on `μ` is imposed. On `L²(X, E; μ)`,
Cauchy–Schwarz relates the `L¹` variation of the pointwise density `x ↦ ‖f x‖²` under `g` to the
`L²` displacement `‖κ g f - f‖`, supplying the measure-theoretic direction of the $P_2$ criterion
between `L²` almost invariant vectors and `L¹` Reiter densities. For counting measure, we record
pointwise evaluation, the `tsum` form of the $P_2$ squared-density variation bound, support
restrictions on invariants and their orthogonal complement, and equivariance of
`MeasureTheory.L2.countHilbertBasis`.

## Main definitions

* `MeasureTheory.Measure.koopman`: the Koopman representation of `G` on `Lp E p μ`.

## Main statements

* `MeasureTheory.Measure.koopman_apply`, `MeasureTheory.Measure.coeFn_koopman`,
  `MeasureTheory.Measure.coeFn_count_koopman`, and `MeasureTheory.Measure.koopman_eq_leftRegular`:
  unfolding, pointwise evaluation on counting measure, and comparison with `leftRegular`.
* `MeasureTheory.Measure.isUnitary_koopman` and `MeasureTheory.Measure.continuous_koopman_apply`:
  unitarity on `L²` and strong continuity for continuous actions on R₁ Borel spaces.
* `MeasureTheory.Measure.integral_abs_norm_sq_koopman_sub_le` and
  `MeasureTheory.Measure.tsum_abs_norm_sq_count_koopman_sub_le`: `∫ |‖f (g⁻¹ • x)‖² - ‖f x‖²| ∂μ ≤
  2 * ‖f‖ * ‖μ.koopman G 𝕜 E 2 g f - f‖` and its counting-measure `tsum` form.
* `MeasureTheory.Measure.apply_eq_zero_of_infinite_orbit_of_mem_invariants_count_koopman` and
  `MeasureTheory.Measure.apply_eq_zero_of_mem_orthogonal_invariants_count_koopman`: support
  restrictions on invariants and their orthogonal complement in counting-measure `L²`.
* `MeasureTheory.Measure.koopman_countHilbertBasis`: equivariant permutation of
  `MeasureTheory.L2.countHilbertBasis`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.6 and Appendix G.5.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §15.1.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Measure

section General

variable {G X 𝕜 E : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] (μ : Measure X) [SMulInvariantMeasure G X μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

variable (G 𝕜 E) in
/-- **The Koopman representation** of a group `G` on `Lᵖ(X, E; μ)` for a `G`-invariant measure `μ`:
the group element `g` acts by `f ↦ (x ↦ f (g⁻¹ • x))`. -/
noncomputable def koopman : ContRepresentation 𝕜 G (Lp E p μ) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ • ·)
        (measurePreserving_smul g⁻¹ μ)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f ↦ by
        simp only [one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, inv_one, one_smul, ← Function.id_def]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' g h := ContinuousLinearMap.ext fun f ↦ by
        have hfun : (fun x : X ↦ (g * h)⁻¹ • x) =
            (fun x : X ↦ h⁻¹ • x) ∘ (fun x : X ↦ g⁻¹ • x) := by
          funext x
          simp only [Function.comp_apply, mul_inv_rev, mul_smul]
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_smul h⁻¹ μ) (measurePreserving_smul g⁻¹ μ) }

/-- The Koopman operator at `g`, unfolded to `Lp.compMeasurePreserving (g⁻¹ • ·)`. -/
theorem koopman_apply (g : G) (f : Lp E p μ) :
    μ.koopman G 𝕜 E p g f =
      Lp.compMeasurePreserving (g⁻¹ • ·) (measurePreserving_smul g⁻¹ μ) f :=
  (rfl)

/-- The Koopman action on `Lᵖ(X, E; μ)` is represented almost everywhere by `x ↦ f (g⁻¹ • x)`. -/
theorem coeFn_koopman (g : G) (f : Lp E p μ) :
    μ.koopman G 𝕜 E p g f =ᵐ[μ] fun x ↦ f (g⁻¹ • x) := by
  rw [koopman_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- Every Koopman operator preserves the `Lᵖ` norm. -/
@[simp]
theorem norm_koopman_apply (g : G) (f : Lp E p μ) : ‖μ.koopman G 𝕜 E p g f‖ = ‖f‖ := by
  rw [koopman_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The Koopman representation on `L²(X, E; μ)` is unitary.** -/
theorem isUnitary_koopman {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : (μ.koopman G 𝕜 E 2).IsUnitary := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  exact norm_koopman_apply μ 2

/-- For the left regular action of `G` on itself, the Koopman representation coincides with
`MeasureTheory.Measure.leftRegular`. -/
@[simp]
theorem koopman_eq_leftRegular [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] :
    ν.koopman G 𝕜 E p = ν.leftRegular 𝕜 E p :=
  DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun f ↦
    Lp.ext ((coeFn_koopman (G := G) (𝕜 := 𝕜) ν p g f).trans
      (coeFn_leftRegular (𝕜 := 𝕜) ν p g f).symm)

/-- **Strong continuity of the Koopman representation** for `p < ∞`, a continuous action on an R₁
Borel space, and a locally finite measure inner regular with respect to compact sets on finite
measure sets. -/
theorem continuous_koopman_apply [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
    [ContinuousSMul G X] [BorelSpace X] [R1Space X] [μ.InnerRegularCompactLTTop]
    [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g : G ↦ μ.koopman G 𝕜 E p g f := by
  have hg : Continuous fun g : G ↦
      (⟨fun x : X ↦ g⁻¹ • x, continuous_const_smul g⁻¹⟩ : C(X, X)) :=
    (ContinuousMap.curry
      ⟨fun q : G × X ↦ q.1⁻¹ • q.2, continuous_fst.inv.smul continuous_snd⟩).continuous
  simp only [koopman_apply]
  exact continuous_const.compMeasurePreservingLp hg _ hp

/-- **$P_2$ squared-density variation bound.** For any `f ∈ L²(X, E; μ)` and `g : G`, the `L¹(μ)`
variation of the density `x ↦ ‖f x‖²` under `g` is bounded by `2 ‖f‖ ‖κ g f - f‖`. -/
theorem integral_abs_norm_sq_koopman_sub_le (g : G) (f : Lp E 2 μ) :
    ∫ x, |‖f (g⁻¹ • x)‖ ^ 2 - ‖f x‖ ^ 2| ∂μ ≤ 2 * ‖f‖ * ‖μ.koopman G 𝕜 E 2 g f - f‖ := by
  have hcongr : ∫ x, |‖f (g⁻¹ • x)‖ ^ 2 - ‖f x‖ ^ 2| ∂μ =
      ∫ x, |‖(μ.koopman G 𝕜 E 2 g f) x‖ ^ 2 - ‖f x‖ ^ 2| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_koopman (G := G) (𝕜 := 𝕜) μ 2 g f] with x hx
    rw [hx]
  rw [hcongr]
  calc ∫ x, |‖(μ.koopman G 𝕜 E 2 g f) x‖ ^ 2 - ‖f x‖ ^ 2| ∂μ
      ≤ ‖μ.koopman G 𝕜 E 2 g f - f‖ * (‖μ.koopman G 𝕜 E 2 g f‖ + ‖f‖) :=
        Lp.integral_abs_norm_sq_sub_le _ _
    _ = 2 * ‖f‖ * ‖μ.koopman G 𝕜 E 2 g f - f‖ := by
        rw [norm_koopman_apply]
        ring

end General

section Count

variable {G X 𝕜 E : Type*} [Group G] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MulAction G X] [MeasurableConstSMul G X]

omit [MeasurableSingletonClass X] in
/-- On counting measure, the representative of `κ g f` equals `x ↦ f (g⁻¹ • x)` everywhere. -/
@[simp]
theorem coeFn_count_koopman [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : G) (f : Lp E p (count : Measure X)) :
    ⇑((count : Measure X).koopman G 𝕜 E p g f) = fun x ↦ f (g⁻¹ • x) :=
  funext (ae_count_iff.mp (coeFn_koopman (G := G) (𝕜 := 𝕜) count p g f))

omit [MeasurableSingletonClass X] in
/-- **Counting-measure $P_2$ squared-density variation bound.** For any `v ∈ ℓ²(X, E)` and `g : G`,
the `ℓ¹` variation of `x ↦ ‖v x‖²` under `g` is at most
`2 * ‖v‖ * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖`. -/
theorem tsum_abs_norm_sq_count_koopman_sub_le [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : G) (v : Lp E 2 (count : Measure X)) :
    ∑' x, |‖v (g⁻¹ • x)‖ ^ 2 - ‖v x‖ ^ 2| ≤
      2 * ‖v‖ * ‖(count : Measure X).koopman G 𝕜 E 2 g v - v‖ := by
  have hd_int : Integrable (fun x ↦ |‖v (g⁻¹ • x)‖ ^ 2 - ‖v x‖ ^ 2|) (count : Measure X) := by
    simpa only [coeFn_count_koopman] using
      (Lp.integrable_norm_sq_sub ((count : Measure X).koopman G 𝕜 E 2 g v) v).abs
  rw [← integral_count_eq_tsum hd_int]
  exact integral_abs_norm_sq_koopman_sub_le (𝕜 := 𝕜) count g v

/-- Any `G`-invariant vector in counting-measure `Lᵖ` (`1 ≤ p < ∞`) vanishes at every point whose
`G`-orbit is infinite. -/
theorem apply_eq_zero_of_infinite_orbit_of_mem_invariants_count_koopman [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp' : p ≠ ∞) {f : Lp E p (count : Measure X)}
    (hf : f ∈ ((count : Measure X).koopman G 𝕜 E p).invariants) {x : X}
    (horb : (MulAction.orbit G x).Infinite) :
    f x = 0 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hconst : ∀ y ∈ MulAction.orbit G x, f y = f x := by
    rintro _ ⟨g, rfl⟩
    have hg : ((count : Measure X).koopman G 𝕜 E p g f : X → E) (g • x) = f (g • x) := by
      rw [hf g]
    simpa using hg.symm
  let ι := horb.natEmbedding
  let T : Set X := Set.range (Subtype.val ∘ ι)
  have hT_cnt : T.Countable := Set.countable_range _
  have hT_meas : MeasurableSet T := hT_cnt.measurableSet
  have hT_inf : T.Infinite :=
    Set.infinite_range_of_injective (Subtype.val_injective.comp ι.injective)
  have hT_sub : T ⊆ MulAction.orbit G x := by
    rintro _ ⟨n, rfl⟩
    exact (ι n).property
  have hae : f =ᵐ[count.restrict T] fun _ ↦ f x :=
    (ae_restrict_iff' hT_meas).mpr (ae_of_all _ fun y hy ↦ hconst y (hT_sub hy))
  have hc : MemLp (fun _ : X ↦ f x) p (count.restrict T) :=
    (memLp_congr_ae hae).mp ((Lp.memLp f).restrict T)
  have huniv : (count : Measure X).restrict T Set.univ = ∞ := by
    rw [Measure.restrict_apply_univ, count_apply_infinite hT_inf]
  simpa [memLp_const_iff hp0 hp', huniv] using hc

/-- If every `G`-orbit in `X` is infinite, then counting-measure `Lᵖ` (`1 ≤ p < ∞`) has no nonzero
`G`-invariant vectors. -/
theorem invariants_count_koopman_of_infinite_orbit [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ∞)
    (horb : ∀ x : X, (MulAction.orbit G x).Infinite) :
    ((count : Measure X).koopman G 𝕜 E p).invariants = ⊥ := by
  refine le_antisymm (fun f hf ↦ ?_) bot_le
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_of_all _ fun x ↦
    apply_eq_zero_of_infinite_orbit_of_mem_invariants_count_koopman hp' hf (horb x))

/-- The constant indicator of a fixed point `x ∈ MulAction.fixedPoints G X` is `G`-invariant in
counting-measure `Lᵖ`. -/
theorem indicatorConstLp_singleton_mem_invariants_count_koopman [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {x : X} (hx : x ∈ MulAction.fixedPoints G X) (c : E) :
    indicatorConstLp p (measurableSet_singleton x) (by simp) c ∈
      ((count : Measure X).koopman G 𝕜 E p).invariants := by
  intro g
  have hpre : (fun y : X ↦ g⁻¹ • y) ⁻¹' ({x} : Set X) = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by simpa [hx g] using congrArg (g • ·) h,
      fun h ↦ by subst h; exact hx g⁻¹⟩
  rw [koopman_apply, Lp.indicatorConstLp_compMeasurePreserving]
  simp only [hpre]

/-- Every vector in the orthogonal complement of the `G`-invariant subspace of counting-measure
`L²(X, E)` vanishes at all `G`-fixed points. -/
theorem apply_eq_zero_of_mem_orthogonal_invariants_count_koopman [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {f : Lp E 2 (count : Measure X)}
    (hf : f ∈ ((count : Measure X).koopman G 𝕜 E 2).invariantsᗮ)
    {x : X} (hx : x ∈ MulAction.fixedPoints G X) :
    f x = 0 := by
  have hmem := indicatorConstLp_singleton_mem_invariants_count_koopman
    (G := G) (𝕜 := 𝕜) (p := 2) hx (f x)
  have horth : ⟪indicatorConstLp 2 (measurableSet_singleton x) (by simp) (f x), f⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf _ hmem
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner, integral_singleton] at horth
  simpa [measureReal_def] using horth

/-- The Koopman representation on `Lp 𝕜 2 (count : Measure X)` permutes
`MeasureTheory.L2.countHilbertBasis` equivariantly: `κ g (e_x) = e_{g • x}`. -/
@[simp]
theorem koopman_countHilbertBasis [RCLike 𝕜] (g : G) (x : X) :
    (count : Measure X).koopman G 𝕜 𝕜 2 g (L2.countHilbertBasis 𝕜 X x) =
      L2.countHilbertBasis 𝕜 X (g • x) := by
  have hpre : (fun y : X ↦ g⁻¹ • y) ⁻¹' ({x} : Set X) = {g • x} := by
    ext y
    simp [inv_smul_eq_iff]
  rw [L2.countHilbertBasis_apply, L2.countHilbertBasis_apply, koopman_apply,
    Lp.indicatorConstLp_compMeasurePreserving]
  simp only [hpre]

end Count

end MeasureTheory.Measure
