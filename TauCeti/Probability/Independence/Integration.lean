/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability and expectations of products and quadratic forms under independence

A finite product of independent integrable variables is integrable
(`ProbabilityTheory.iIndepFun.integrable_fun_prod`).
The product of two independent square-integrable `RCLike`-valued random variables is square
integrable (`ProbabilityTheory.IndepFun.memLp_two_mul`). For a finite family `W : ι → Ω → 𝕜` with
`RCLike 𝕜`, integrable squared norms, and integrable, vanishing mixed second moments
(or pairwise independent mean-zero square-integrable coordinates), and `A : Matrix ι ι 𝕜`,
`star W ⬝ᵥ A *ᵥ W` is integrable with expectation `∑ i, A i i * E[‖W i‖ ^ 2]`
(`TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_integral_eq_zero` and
`TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun`).
Independent sections also transfer probability bounds to an independent random parameter
(`ProbabilityTheory.IndepFun.measureReal_preimage_le`).

For an independent family `Y`, the expectation of a finite product of functions of members of
`Y`, several factors possibly reading the same member, is the product over the members of the
expectations of the products of the factors reading them
(`ProbabilityTheory.iIndepFun.integral_fun_prod_comp_fiberwise`). This is the factorization
used to evaluate expected products of entries of random matrices along trace words.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.iIndepFun

/-- A product over a finite subset of an independent family of integrable variables is
integrable. The index type need not be finite. -/
theorem integrable_finsetProd {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedCommRing E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {X : ι → Ω → E}
    (h : iIndepFun X P) (s : Finset ι) (hX : ∀ i ∈ s, Integrable (X i) P) :
    Integrable (fun ω ↦ ∏ i ∈ s, X i ω) P := by
  classical
  have := h.isProbabilityMeasure
  let Y (i : ι) (ω : Ω) := ‖X i ω‖
  have hY : iIndepFun Y P := h.comp (fun _ ↦ norm) (fun _ ↦ continuous_norm.measurable)
  have hm (i : s) : AEMeasurable (Y i) P := (hX i i.property).norm.aemeasurable
  have hint : Integrable (fun x : s → ℝ ↦ ∏ i, x i)
      (Measure.pi fun i : s ↦ P.map (Y i)) :=
    Integrable.fintype_prod fun (i : s) ↦
      (integrable_map_measure
        (hX i i.property).norm.aestronglyMeasurable.aestronglyMeasurable_id_map
        (hm i)).2 (hX i i.property).norm
  rw [← (hY.restrict s).map_fun_eq_pi_map hm] at hint
  have hp := hint.comp_aemeasurable (aemeasurable_pi_iff.2 hm)
  have hprod : Integrable (fun ω ↦ ∏ i ∈ s, Y i ω) P :=
    hp.congr (.of_forall fun ω ↦ Finset.prod_coe_sort s (fun i ↦ Y i ω))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa only [Finset.prod_empty] using integrable_const (1 : E)
  · exact hprod.mono' (s.aestronglyMeasurable_fun_prod fun i hi ↦ (hX i hi).aestronglyMeasurable)
      (.of_forall fun ω ↦ s.norm_prod_le' hs (fun i ↦ X i ω))

/-- A finite product of independent integrable random variables is integrable. -/
theorem integrable_fun_prod {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedCommRing E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {X : ι → Ω → E}
    (h : iIndepFun X P) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω ↦ ∏ i, X i ω) P :=
  h.integrable_finsetProd Finset.univ (fun i _ ↦ hX i)

end ProbabilityTheory.iIndepFun

namespace ProbabilityTheory.IndepFun

private theorem indepFun_norm_sq {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    {P : Measure Ω} {X Y : Ω → 𝕜} (h : IndepFun X Y P) :
    IndepFun (fun ω ↦ ‖X ω‖ ^ 2) (fun ω ↦ ‖Y ω‖ ^ 2) P :=
  h.comp (φ := fun z ↦ ‖z‖ ^ 2) (ψ := fun z ↦ ‖z‖ ^ 2) (by fun_prop) (by fun_prop)

/-- The product of independent square-integrable variables is square integrable. -/
theorem memLp_two_mul {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    {P : Measure Ω} {X Y : Ω → 𝕜} (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp (X * Y) 2 P := by
  refine (memLp_two_iff_integrable_sq_norm
    (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2 ?_
  have hx := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hy := (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).1 hY
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using
    ((indepFun_norm_sq h).integrable_mul hx hy).congr (.of_forall fun x ↦ Pi.mul_apply _ _ x)

/-- The second absolute moment of a product of independent variables is the product
of their second absolute moments. -/
theorem integral_norm_sq_mul {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    {P : Measure Ω} {X Y : Ω → 𝕜} (h : IndepFun X Y P)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    (∫ ω, ‖X ω * Y ω‖ ^ 2 ∂P) =
      (∫ ω, ‖X ω‖ ^ 2 ∂P) * (∫ ω, ‖Y ω‖ ^ 2 ∂P) := by
  simp_rw [norm_mul, mul_pow]
  exact (indepFun_norm_sq h).integral_fun_mul_eq_mul_integral
    (hX.norm.pow_const 2).aestronglyMeasurable (hY.norm.pow_const 2).aestronglyMeasurable

/-- An integrable bound for the mean norms of sections also bounds the mean norm of the
joint evaluation at independent variables. -/
theorem integral_norm_comp_prodMk_le_of_sections {Ω α β E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β}
    (hind : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {f : α × β → E} (hf : Measurable f) {g : α → ℝ} (hg : Integrable g (P.map X))
    (hsection : ∀ᵐ x ∂P.map X, Integrable (fun ω ↦ f (x, Y ω)) P ∧
      (∫ ω, ‖f (x, Y ω)‖ ∂P) ≤ g x) :
    Integrable (fun ω ↦ f (X ω, Y ω)) P ∧
      (∫ ω, ‖f (X ω, Y ω)‖ ∂P) ≤ ∫ x, g x ∂P.map X := by
  have hmap := hind.map_prod_eq_prod_map_map hX hY
  have hnorm (x : α) : (∫ y, ‖f (x, y)‖ ∂P.map Y) = ∫ ω, ‖f (x, Y ω)‖ ∂P :=
    integral_map hY (hf.norm.comp measurable_prodMk_left).aestronglyMeasurable
  have hsection' : ∀ᵐ x ∂P.map X, Integrable (fun y ↦ f (x, y)) (P.map Y) ∧
      (∫ y, ‖f (x, y)‖ ∂P.map Y) ≤ g x := hsection.mono fun x hx ↦
    ⟨(integrable_map_measure (hf.comp measurable_prodMk_left).aestronglyMeasurable hY).2 hx.1,
      (hnorm x).trans_le hx.2⟩
  have hm : AEStronglyMeasurable f ((P.map X).prod (P.map Y)) := hf.aestronglyMeasurable
  have hg' := hg.mono' hm.norm.integral_prod_right' (hsection'.mono fun x hx ↦ by
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] using hx.2)
  have hi := (integrable_prod_iff hm).2 ⟨hsection'.mono fun _ hx ↦ hx.1, hg'⟩
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable (hX.prodMk hY)).1
    (hmap ▸ hi), ?_⟩
  rw [← integral_map (hX.prodMk hY) hf.norm.aestronglyMeasurable, hmap, integral_prod _ hi.norm]
  exact integral_mono_ae hg' hg (hsection'.mono fun _ hx ↦ hx.2)

/-- Bound an event of two independent random variables by an almost-everywhere bound on its
sections. The section is measured under the law of the second variable. -/
theorem measureReal_preimage_le {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β}
    (hXY : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {s : Set (α × β)} (hs : MeasurableSet s) {b : ℝ}
    (h : ∀ᵐ x ∂P.map X, (P.map Y).real (Prod.mk x ⁻¹' s) ≤ b) :
    P.real ((fun ω ↦ (X ω, Y ω)) ⁻¹' s) ≤ b := by
  have hb : 0 ≤ b := by
    obtain ⟨x, hx⟩ := h.exists
    exact (measureReal_nonneg).trans hx
  rw [← map_measureReal_apply_of_aemeasurable (hX.prodMk hY) hs,
    hXY.map_prod_eq_prod_map_map hX hY]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb).1
  rw [Measure.prod_apply hs]
  calc
    ∫⁻ x, P.map Y (Prod.mk x ⁻¹' s) ∂P.map X ≤ ∫⁻ _, ENNReal.ofReal b ∂P.map X := by
      apply lintegral_mono_ae
      filter_upwards [h] with x hx
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb).2 hx
    _ = ENNReal.ofReal b := by simp

/-- For independent random variables, a uniform bound on the probabilities of the sections
of a measurable set in the product space bounds the measure of that set by the bound times
the mass of the underlying measure. -/
theorem measure_preimage_prodMk_le_of_forall
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β}
    (hind : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {s : Set (α × β)} (hs : MeasurableSet s) {b : ℝ≥0∞}
    (h : ∀ a, P (Y ⁻¹' (Prod.mk a ⁻¹' s)) ≤ b) :
    P ((fun ω ↦ (X ω, Y ω)) ⁻¹' s) ≤ b * P Set.univ := by
  rw [← Measure.map_apply_of_aemeasurable (hX.prodMk hY) hs,
    hind.map_prod_eq_prod_map_map hX hY, Measure.prod_apply hs]
  have hsection (a : α) : P.map Y (Prod.mk a ⁻¹' s) ≤ b := by
    rw [Measure.map_apply_of_aemeasurable hY (hs.preimage measurable_prodMk_left)]
    exact h a
  exact (lintegral_mono hsection).trans_eq (by
    simp [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ])

end ProbabilityTheory.IndepFun

namespace ProbabilityTheory.iIndepFun

/-- **Expected products of functions of independent variables, grouped by fibers.**
Only finitely many factors and members of the independent family are involved; `e` maps the
factor indices in `s` to the member indices in `t`. Several factors may read the same member. -/
theorem integral_fun_prod_comp_fiberwise_of_maps_to {Ω κ ι β 𝕜 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [RCLike 𝕜] [DecidableEq κ]
    {P : Measure Ω} {Y : κ → Ω → β} (hY : iIndepFun Y P)
    {s : Finset ι} {t : Finset κ} {e : ι → κ} (he : ∀ i ∈ s, e i ∈ t)
    (mY : ∀ j ∈ t, AEMeasurable (Y j) P) {φ : ι → β → 𝕜}
    (hφ : ∀ i ∈ s, AEStronglyMeasurable (φ i) (P.map (Y (e i)))) :
    ∫ ω, ∏ i ∈ s, φ i (Y (e i) ω) ∂P =
      ∏ j ∈ t, ∫ ω, ∏ i ∈ s with e i = j, φ i (Y j ω) ∂P := by
  let ψ (j : κ) (b : β) := ∏ i ∈ s with e i = j, φ i b
  have hψ (j : t) : AEStronglyMeasurable (ψ j) (P.map (Y j)) := by
    exact Finset.aestronglyMeasurable_fun_prod _ fun i hi ↦ by
      obtain ⟨his, hij⟩ := Finset.mem_filter.1 hi
      simpa only [hij] using hφ i his
  have hfactor := (hY.precomp Subtype.val_injective).integral_fun_prod_comp
    (f := fun j : t ↦ ψ j) (fun j ↦ mY j j.property) hψ
  have hfactor' : (∫ ω, ∏ j ∈ t, ψ j (Y j ω) ∂P) =
      ∏ j ∈ t, ∫ ω, ψ j (Y j ω) ∂P := by
    calc
      _ = ∫ ω, ∏ j : t, ψ j (Y j ω) ∂P :=
        integral_congr_ae (.of_forall fun ω ↦ (Finset.prod_coe_sort t
          (fun j ↦ ψ j (Y j ω))).symm)
      _ = _ := hfactor
      _ = _ := Finset.prod_coe_sort t (fun j ↦ ∫ ω, ψ j (Y j ω) ∂P)
  rw [← hfactor']
  congr with ω
  symm
  dsimp only [ψ]
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with e i = j, φ i (Y (e i) ω) := by
      refine Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun i hi ↦ ?_
      rw [(Finset.mem_filter.1 hi).2]
    _ = _ := Finset.prod_fiberwise_of_maps_to he _

/-- **Expected products of functions of independent variables.** Let `Y` be an independent
family indexed by a finite type, and let the factors `φ i (Y (e i))` of a finite product read
members of `Y`, several factors possibly reading the same member. The expectation of the product
is the product, over the members `j`, of the expectations of the products of the factors reading
`j`. -/
theorem integral_fun_prod_comp_fiberwise {Ω κ ι β 𝕜 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [RCLike 𝕜] [Fintype κ] [DecidableEq κ] [Fintype ι]
    {P : Measure Ω} {Y : κ → Ω → β} (hY : iIndepFun Y P) (mY : ∀ j, AEMeasurable (Y j) P)
    (e : ι → κ) {φ : ι → β → 𝕜}
    (hφ : ∀ i, AEStronglyMeasurable (φ i) (P.map (Y (e i)))) :
    ∫ ω, ∏ i, φ i (Y (e i) ω) ∂P = ∏ j, ∫ ω, ∏ i with e i = j, φ i (Y j ω) ∂P :=
  hY.integral_fun_prod_comp_fiberwise_of_maps_to (fun _ _ ↦ Finset.mem_univ _)
    (fun j _ ↦ mY j) (fun i _ ↦ hφ i)

/-- A finite product of functions of independent variables has integral zero when one variable
is read exactly once and its sole factor has integral zero. For an integrable product this
gives expectation zero. The argument comes from the sample-covariance trace-word cancellation
in `TauCeti.Probability.integral_prod_apply_mul_star_apply_eq_zero`. -/
theorem integral_fun_prod_comp_eq_zero_of_singleton_fiber
    {Ω κ ι β 𝕜 : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [RCLike 𝕜] [DecidableEq κ]
    {P : Measure Ω} {Y : κ → Ω → β} (hY : iIndepFun Y P)
    (s : Finset ι) (e : ι → κ) (mY : ∀ j ∈ s.image e, AEMeasurable (Y j) P)
    {φ : ι → β → 𝕜} (hφ : ∀ i ∈ s, AEStronglyMeasurable (φ i) (P.map (Y (e i))))
    {a : ι} (has : a ∈ s) (ha : ∀ b ∈ s, e b = e a → b = a)
    (hzero : ∫ ω, φ a (Y (e a) ω) ∂P = 0) :
    (∫ ω, ∏ i ∈ s, φ i (Y (e i) ω) ∂P) = 0 := by
  classical
  rw [hY.integral_fun_prod_comp_fiberwise_of_maps_to
    (t := s.image e) (fun i hi ↦ Finset.mem_image_of_mem e hi) mY hφ]
  refine Finset.prod_eq_zero (Finset.mem_image_of_mem e has) ?_
  have hfiber : (s.filter fun b ↦ e b = e a) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h ↦ ha b h.1 h.2, fun h ↦ by subst b; exact ⟨has, rfl⟩⟩
  simp only [hfiber, Finset.prod_singleton, hzero]

end ProbabilityTheory.iIndepFun

open ProbabilityTheory Matrix

namespace TauCeti

/-- For coordinates with integrable squared norms and integrable, vanishing mixed second
moments, a quadratic form is integrable and its expectation is the diagonal second-moment sum.
Neither independence nor finiteness of the measure is needed. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_integral_eq_zero
    {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜]
    {P : Measure Ω} {W : ι → Ω → 𝕜}
    (hW_sq : ∀ i, Integrable (fun ω ↦ ‖W i ω‖ ^ 2) P)
    (hW_mul : Pairwise fun i j ↦ Integrable (fun ω ↦ star (W i ω) * W j ω) P)
    (horth : Pairwise fun i j ↦ ∫ ω, star (W i ω) * W j ω ∂P = 0)
    (A : Matrix ι ι 𝕜) :
    Integrable (fun ω ↦ star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω)) P ∧
      ∫ ω, star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖W i ω‖ ^ 2] : ℝ) : 𝕜) := by
  have hexpand (ω : Ω) : star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) =
      ∑ i, ∑ j, A i j * (star (W i ω) * W j ω) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hcast (i : ι) (ω : Ω) :
      A i i * (star (W i ω) * W i ω) = A i i * ((‖W i ω‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul]; norm_cast
  have hterm_int (i j : ι) : Integrable (fun ω ↦ A i j * (star (W i ω) * W j ω)) P := by
    by_cases hij : i = j
    · subst hij; exact (((RCLike.ofRealCLM (K := 𝕜)).integrable_comp (hW_sq i)).const_mul
        (A i i)).congr (.of_forall fun ω ↦ (hcast i ω).symm)
    · exact (hW_mul hij).const_mul (A i j)
  refine ⟨(integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm_int i j).congr
    (.of_forall fun ω ↦ (hexpand ω).symm), ?_⟩
  rw [integral_congr_ae (.of_forall hexpand),
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm_int i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hterm_int i j, Finset.sum_eq_single i]
  · rw [integral_congr_ae (.of_forall (hcast i)), integral_const_mul]
    exact congrArg (A i i * ·) ((RCLike.ofRealCLM (K := 𝕜)).integral_comp_comm (hW_sq i))
  · intro j _ hji
    rw [integral_const_mul, horth hji.symm, mul_zero]
  · exact fun hi ↦ absurd (Finset.mem_univ i) hi

/-- For pairwise independent mean-zero square-integrable `RCLike`-valued coordinates `W` and
`A : Matrix ι ι 𝕜`, `star W ⬝ᵥ A *ᵥ W` is integrable with expectation
`∑ i, A i i * E[‖W i‖ ^ 2]`. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun {Ω ι 𝕜 : Type*}
    [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜] {P : Measure Ω} {W : ι → Ω → 𝕜}
    (hindep : Pairwise fun i j ↦ W i ⟂ᵢ[P] W j) (hW_int : ∀ i, Integrable (W i) P)
    (hW_sq : ∀ i, Integrable (fun ω ↦ ‖W i ω‖ ^ 2) P) (hW_mean : ∀ i, ∫ ω, W i ω ∂P = 0)
    (A : Matrix ι ι 𝕜) :
    Integrable (fun ω ↦ star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω)) P ∧
      ∫ ω, star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖W i ω‖ ^ 2] : ℝ) : 𝕜) := by
  have hW_star (i : ι) : Integrable (fun ω ↦ star (W i ω)) P :=
    (hW_int i).mono (continuous_star.comp_aestronglyMeasurable (hW_int i).1)
      (.of_forall fun _ ↦ by simp)
  refine integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_integral_eq_zero hW_sq
    (fun i j hij ↦ ((hindep hij).comp continuous_star.measurable measurable_id).integrable_smul
      (hW_star i) (hW_int j)) (fun i j hij ↦ ?_) A
  have hmul := ((hindep hij).comp continuous_star.measurable
    measurable_id).integral_fun_mul_eq_mul_integral (hW_star i).1 (hW_int j).1
  simpa only [Function.comp_def, id_eq, hW_mean j, mul_zero] using hmul

end TauCeti
