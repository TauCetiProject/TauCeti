/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Multiplier

/-!
# Multiplication operators on `Lᵖ`

An essentially bounded scalar function `a : Lp 𝕜 ∞ μ` acts on `Lp E p μ` (`1 ≤ p ≤ ∞`) by
pointwise scalar multiplication. This file bundles that action as
`MeasureTheory.Lp.multiplicationOperator a` and records its algebraic, adjoint, norm, pullback,
unitary-conjugation, eigenspace, and commutant properties. Because the operator is built directly
from heterogeneous `Lp` scalar multiplication via `LinearMap.mkContinuous`, the definition and
algebraic identities require only `[NormedField 𝕜]` (without `[NontriviallyNormedField 𝕜]`).

Over a nontrivially normed field `𝕜` on a sigma-finite measure space with nontrivial fiber `E`, the
operator norm on `Lp E p μ` equals the `L∞` norm `‖a‖` (`norm_multiplicationOperator`). On
`Lp E 2 μ` for a complete inner-product space `E` over `𝕜` (`[RCLike 𝕜]`), the Hilbert adjoint of
multiplication by `a` is multiplication by `star a` (`adjoint_multiplicationOperator`), and over
`ℂ` this gives a unital ⋆-algebra homomorphism `MeasureTheory.Lp.multiplicationStarAlgHom`. On
complex scalar `L²`, every bounded operator commuting with indicator multiplications on sets of
finite measure is locally multiplication by an `L∞` symbol (and globally so when the measure is
sigma-finite). As a concrete eigenspace example, multiplication by the real-valued coordinate symbol
`TauCeti.unitInterval.coordLp` on `Lp E 2 (volume : Measure unitInterval)` has no eigenvalues
(`TauCeti.unitInterval.not_hasEigenvalue_multiplicationOperator_coordLp`).

## References

* M. Takesaki, *Theory of Operator Algebras I*, Springer, 2002, Chapter III, §1.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Academic Press, 1983, Example 5.1.6.
-/

public section

noncomputable section

open Filter
open scoped ENNReal ComplexInnerProductSpace InnerProductSpace Topology

namespace MeasureTheory.Lp

open ContinuousLinearMap

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise scalar multiplication by an essentially bounded symbol `a : Lp 𝕜 ∞ μ`, as a
continuous linear operator on `Lp E p μ` (`1 ≤ p ≤ ∞`). -/
def multiplicationOperator (a : Lp 𝕜 ∞ μ) : Lp E p μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun f := a • f
      map_add' := Lp.add_smul a
      map_smul' c f := (Lp.smul_comm c a f).symm }
    ‖a‖ (Lp.norm_smul_le a)

/-- Applying the multiplication operator is heterogeneous `Lp` scalar multiplication. -/
theorem multiplicationOperator_apply (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    multiplicationOperator a f = a • f :=
  (rfl)

/-- The multiplication operator acts by pointwise scalar multiplication almost everywhere. -/
theorem multiplicationOperator_ae (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    multiplicationOperator a f =ᵐ[μ] fun x ↦ a x • f x :=
  coeFn_lpSMul a f

/-- On scalar `L²`, `multiplicationOperator` agrees with the Hölder operator built from complex
multiplication `ContinuousLinearMap.mul ℂ ℂ`. -/
theorem holderL_mul_eq_multiplicationOperator :
    ⇑((ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2) =
      multiplicationOperator (E := ℂ) (p := 2) (μ := μ) := by
  funext a
  ext f
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) a f,
    multiplicationOperator_ae a f] with x h₁ h₂
  rw [ContinuousLinearMap.holderL_apply_apply, h₁, h₂, ContinuousLinearMap.mul_apply', smul_eq_mul]

/-- Multiplication by `a` changes the `Lᵖ` norm by at most `‖a‖ * ‖f‖`. -/
theorem norm_multiplicationOperator_apply_le (a : Lp 𝕜 ∞ μ) (f : Lp E p μ) :
    ‖multiplicationOperator a f‖ ≤ ‖a‖ * ‖f‖ :=
  Lp.norm_smul_le a f

@[simp]
theorem multiplicationOperator_zero :
    multiplicationOperator (E := E) (p := p) (0 : Lp 𝕜 ∞ μ) = 0 :=
  ContinuousLinearMap.ext fun f ↦ Lp.zero_smul 𝕜 ∞ f

/-- Multiplication operators depend additively on their symbols. -/
@[simp]
theorem multiplicationOperator_add (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (a + b) =
      multiplicationOperator a + multiplicationOperator b :=
  ContinuousLinearMap.ext fun f ↦ Lp.smul_add a b f

@[simp]
theorem multiplicationOperator_neg (a : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (-a) = -multiplicationOperator a := by
  ext f
  filter_upwards [multiplicationOperator_ae (-a) f, multiplicationOperator_ae a f,
    Lp.coeFn_neg a, Lp.coeFn_neg (multiplicationOperator a f)] with x h₁ h₂ ha hf
  rw [h₁, ha, Pi.neg_apply, neg_smul, neg_apply, hf, Pi.neg_apply, h₂]

@[simp]
theorem multiplicationOperator_sub (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (a - b) =
      multiplicationOperator a - multiplicationOperator b := by
  rw [sub_eq_add_neg, multiplicationOperator_add, multiplicationOperator_neg, sub_eq_add_neg]

/-- Multiplication operators depend linearly on their symbols. -/
@[simp]
theorem multiplicationOperator_smul (c : 𝕜) (a : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (c • a) = c • multiplicationOperator a :=
  ContinuousLinearMap.ext fun f ↦ Lp.smul_assoc c a f

/-- Composing multiplication operators multiplies their symbols in the same order. -/
theorem multiplicationOperator_comp_multiplicationOperator (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) a ∘L multiplicationOperator b =
      multiplicationOperator (a * b) := by
  ext f
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f,
    multiplicationOperator_ae (a * b) f,
    coeFn_mul a b] with x ha hb hab hsmul
  simp only [comp_apply, ha, hb, hab, hsmul, Pi.mul_apply, smul_smul]

/-- Multiplying symbols multiplies the corresponding operators. -/
@[simp]
theorem multiplicationOperator_mul (a b : Lp 𝕜 ∞ μ) :
    multiplicationOperator (E := E) (p := p) (a * b) =
      multiplicationOperator a * multiplicationOperator b := by
  rw [ContinuousLinearMap.mul_def, multiplicationOperator_comp_multiplicationOperator]

/-- Multiplication operators commute with each other. -/
theorem commute_multiplicationOperator (a b : Lp 𝕜 ∞ μ) :
    Commute (multiplicationOperator (E := E) (p := p) a) (multiplicationOperator b) := by
  refine (commute_iff_eq _ _).2 (ContinuousLinearMap.ext fun f ↦ Lp.ext ?_)
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f, multiplicationOperator_ae b (multiplicationOperator a f),
    multiplicationOperator_ae a f] with x hab hb hba ha
  simp only [mul_apply_eq_comp, hab, hb, hba, ha, smul_smul, mul_comm]

/-- Multiplication by a symbol of norm one almost everywhere preserves the `Lᵖ` norm. -/
theorem norm_multiplicationOperator_apply_of_ae_norm_eq_one {u : Lp 𝕜 ∞ μ}
    (hu : ∀ᵐ x ∂μ, ‖u x‖ = 1) (f : Lp E p μ) :
    ‖multiplicationOperator u f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂μ, ‖multiplicationOperator u f x‖ = ‖f x‖ := by
    filter_upwards [multiplicationOperator_ae u f, hu] with x hx hux
    rw [hx, norm_smul, hux, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.ge))

/-- A symbol equal almost everywhere to a constant acts by scalar multiplication. -/
theorem multiplicationOperator_of_ae_eq_const {a : Lp 𝕜 ∞ μ} {c : 𝕜}
    (ha : a =ᵐ[μ] fun _ ↦ c) :
    multiplicationOperator (E := E) (p := p) a = c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext f
  filter_upwards [multiplicationOperator_ae a f, Lp.coeFn_smul c f, ha] with x h hf ha'
  simp [h, hf, ha']

/-- Multiplication by the unit `1 : Lp 𝕜 ∞ μ` is the identity operator on `Lᵖ`. -/
@[simp]
theorem multiplicationOperator_one :
    multiplicationOperator (E := E) (p := p) (1 : Lp 𝕜 ∞ μ) = 1 := by
  have h := multiplicationOperator_of_ae_eq_const (E := E) (p := p) (c := (1 : 𝕜))
    (coeFn_one (E := 𝕜) (μ := μ))
  rwa [one_smul, ← ContinuousLinearMap.one_def] at h

/-- The scalar embedding into `L∞` acts on `Lᵖ` by scalar multiplication. -/
@[simp]
theorem multiplicationOperator_algebraMap (c : 𝕜) :
    multiplicationOperator (E := E) (p := p) (algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  apply multiplicationOperator_of_ae_eq_const
  simpa only [Algebra.algebraMap_self_apply] using coeFn_algebraMap (R := 𝕜) (μ := μ) c

@[simp]
theorem multiplicationOperator_const [IsFiniteMeasure μ] (c : 𝕜) :
    multiplicationOperator (E := E) (p := p) (Lp.const ∞ μ c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) :=
  multiplicationOperator_of_ae_eq_const (Lp.coeFn_const (μ := μ) ∞ c)

/-- Precomposition along a measure-preserving map intertwines `multiplicationOperator`. -/
theorem compMeasurePreserving_multiplicationOperator_apply {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν) (a : Lp 𝕜 ∞ ν) (f : Lp E p ν) :
    compMeasurePreserving g hg (multiplicationOperator a f) =
      multiplicationOperator (compMeasurePreserving g hg a) (compMeasurePreserving g hg f) := by
  refine Lp.ext (((coeFn_compMeasurePreserving _ hg).trans
    (hg.quasiMeasurePreserving.ae_eq_comp (multiplicationOperator_ae a f))).trans ?_)
  filter_upwards [multiplicationOperator_ae (compMeasurePreserving g hg a)
      (compMeasurePreserving g hg f),
    coeFn_compMeasurePreserving a hg, coeFn_compMeasurePreserving f hg] with x h₃ ha hf
  rw [Function.comp_apply, h₃, ha, hf, Function.comp_apply, Function.comp_apply]

end NormedSpace

section InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- On `L²`, the adjoint of multiplication by `a` is multiplication by `star a`. -/
@[simp]
theorem adjoint_multiplicationOperator (a : Lp 𝕜 ∞ μ) :
    ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := Lp E 2 μ) (F := Lp E 2 μ)
      (multiplicationOperator (E := E) (p := 2) a) =
      multiplicationOperator (E := E) (p := 2) (star a) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multiplicationOperator_ae (star a) f,
    multiplicationOperator_ae a g, Lp.coeFn_star a] with x hf hg ha
  simp [hf, hg, ha, inner_smul_left, inner_smul_right]

/-- The operator-algebra involution of multiplication by `a` is multiplication by `star a`. -/
@[simp]
theorem star_multiplicationOperator (a : Lp 𝕜 ∞ μ) :
    star (multiplicationOperator (E := E) (p := 2) a) =
      multiplicationOperator (E := E) (p := 2) (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_multiplicationOperator]

end InnerProductSpace

section ComplexInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Pointwise multiplication by essentially bounded complex functions, bundled as a unital
⋆-algebra homomorphism into the bounded operators on `L²`. -/
def multiplicationStarAlgHom (μ : Measure α) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : Lp ℂ ∞ μ →⋆ₐ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := multiplicationOperator (E := E)
  map_one' := multiplicationOperator_one
  map_mul' := multiplicationOperator_mul
  map_zero' := multiplicationOperator_zero
  map_add' := multiplicationOperator_add
  commutes' c := by
    rw [multiplicationOperator_algebraMap, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.one_def]
  map_star' a := (star_multiplicationOperator a).symm

@[simp]
theorem multiplicationStarAlgHom_apply (a : Lp ℂ ∞ μ) :
    multiplicationStarAlgHom μ E a = multiplicationOperator (E := E) a :=
  (rfl)

/-- Conjugating `multiplicationOperator a` by the `L²` unitary equivalence induced by an
almost-everywhere inverse pair of measure-preserving maps yields multiplication by the `L∞`
pullback `compMeasurePreserving f hf a`. -/
theorem conjStarAlgEquiv_compMeasurePreservingₗᵢEquiv_multiplicationOperator
    {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α → β} {g : β → α}
    (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g ν μ) (hfg : f ∘ g =ᵐ[ν] id)
    (a : Lp ℂ ∞ ν) :
    (compMeasurePreservingₗᵢEquiv ℂ (E := E) (p := 2) hf hg hfg).conjStarAlgEquiv
        (multiplicationOperator (E := E) a) =
      multiplicationOperator (E := E) (compMeasurePreserving f hf a) := by
  ext h : 1
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, compMeasurePreservingₗᵢEquiv_apply,
    compMeasurePreserving_multiplicationOperator_apply,
    ← compMeasurePreservingₗᵢEquiv_apply ℂ (E := E) (p := 2) hf hg hfg,
    LinearIsometryEquiv.apply_symm_apply]

end ComplexInnerProductSpace

section ExactNorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Over a nontrivially normed field, the operator norm of multiplication by `a` on `Lᵖ` is at
most its `L∞` norm. -/
theorem norm_multiplicationOperator_le (a : Lp 𝕜 ∞ μ) :
    ‖multiplicationOperator (E := E) (p := p) a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- If `0 < c` and `c ≤ ‖a‖` almost everywhere on `s`, then multiplication by `a` scales the `Lᵖ`
norm of a constant indicator of `s` by at least `c`. -/
private theorem mul_norm_indicatorConstLp_le {a : Lp 𝕜 ∞ μ} {c : ℝ} (hc_pos : 0 < c)
    {s : Set α} (hs : MeasurableSet s) (hs_top : μ s ≠ ∞) (ha : ∀ᵐ x ∂μ, x ∈ s → c ≤ ‖a x‖)
    (v : E) :
    c * ‖indicatorConstLp p hs hs_top v‖ ≤
      ‖multiplicationOperator a (indicatorConstLp p hs hs_top v)‖ := by
  set f := indicatorConstLp p hs hs_top v
  refine (le_inv_mul_iff₀ hc_pos).1 (Lp.norm_le_mul_norm_of_ae_le_mul ?_)
  filter_upwards [multiplicationOperator_ae a f,
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hs_top) (c := v), ha] with x hmul hf hax
  rw [hmul, hf]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, norm_smul]
    exact (le_inv_mul_iff₀ hc_pos).2 (mul_le_mul_of_nonneg_right (hax hx) (norm_nonneg v))
  · simp [Set.indicator_of_notMem hx]

/-- On a sigma-finite measure space over a nontrivially normed field, the operator norm of
multiplication by `a` on `Lp E p μ` (`1 ≤ p ≤ ∞`) with values in a nontrivial space `E` is
exactly the `L∞` norm of `a`. -/
@[simp]
theorem norm_multiplicationOperator [SigmaFinite μ] [Nontrivial E] (a : Lp 𝕜 ∞ μ) :
    ‖multiplicationOperator (E := E) (p := p) a‖ = ‖a‖ := by
  apply le_antisymm (norm_multiplicationOperator_le a)
  by_contra hle
  set c := (‖multiplicationOperator (E := E) (p := p) a‖ + ‖a‖) / 2 with hc_def
  have hop_lt_c : ‖multiplicationOperator (E := E) (p := p) a‖ < c := by linarith [hc_def]
  have hc_pos : 0 < c := (norm_nonneg _).trans_lt hop_lt_c
  have hc_lt : c < ‖a‖ := by linarith [hc_def]
  have ha_meas := Lp.aestronglyMeasurable a
  set s := {x | c < ‖ha_meas.mk a x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const ha_meas.stronglyMeasurable_mk.norm.measurable
  have hs_ae : s =ᵐ[μ] {x | c < ‖a x‖} :=
    Filter.eventuallyEqSet_iff.2 (ha_meas.ae_eq_mk.symm.mono fun x hx ↦ by dsimp [s]; rw [hx])
  have hμs : μ s ≠ 0 := by
    rw [measure_congr hs_ae]
    exact measure_lt_norm_ne_zero hc_pos.le hc_lt
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set f := indicatorConstLp p ht hμt_top.ne v
  have hf_pos : 0 < ‖f‖ :=
    norm_pos_iff.2 fun hf0 ↦ (TauCeti.indicatorConstLp_eq_zero_iff.1 hf0).elim hμt_pos.ne' hv
  have hcancel : c * ‖f‖ ≤ ‖multiplicationOperator (E := E) (p := p) a‖ * ‖f‖ :=
    (mul_norm_indicatorConstLp_le hc_pos ht hμt_top.ne
      (ha_meas.ae_eq_mk.mono fun _ hmk hx ↦ by rw [hmk]; exact le_of_lt (hts hx)) v).trans
      (le_opNorm _ _)
  exact (not_le_of_gt hop_lt_c) (le_of_mul_le_mul_right hcancel hf_pos)

/-- On a sigma-finite measure space, `multiplicationOperator` is an isometry into the bounded
operators on `Lᵖ` (`1 ≤ p ≤ ∞`) with values in a nontrivial space. -/
theorem isometry_multiplicationOperator [SigmaFinite μ] [Nontrivial E] :
    Isometry (multiplicationOperator (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)) := by
  refine Isometry.of_dist_eq fun a b ↦ ?_
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm, ← multiplicationOperator_sub,
    norm_multiplicationOperator]

/-- On a sigma-finite measure space, `multiplicationOperator` is injective on `L∞` whenever the
target fibre `E` is nontrivial. -/
theorem multiplicationOperator_injective [SigmaFinite μ] [Nontrivial E] :
    Function.Injective (multiplicationOperator (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)) :=
  (isometry_multiplicationOperator (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)).injective

@[simp]
theorem multiplicationOperator_inj [SigmaFinite μ] [Nontrivial E] {a b : Lp 𝕜 ∞ μ} :
    multiplicationOperator (E := E) (p := p) a = multiplicationOperator (E := E) (p := p) b ↔
      a = b :=
  (multiplicationOperator_injective (𝕜 := 𝕜) (E := E) (p := p) (μ := μ)).eq_iff

end ExactNorm

section Commutant

/-- Multiplication by an `L∞` measurable-set unit indicator cuts off an `L²` constant indicator to
the intersection of the two sets. -/
theorem multiplicationOperator_linftyIndicator_indicatorConstLp
    [NormedAddCommGroup E] [NormedSpace ℂ E] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (v : E) :
    multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) (indicatorConstLp 2 ht hμt v) =
      indicatorConstLp 2 (hs.inter ht)
        ((measure_mono Set.inter_subset_right).trans_lt hμt.lt_top).ne v := by
  apply Lp.ext
  filter_upwards [multiplicationOperator_ae (TauCeti.linftyIndicator μ ℂ s hs)
      (indicatorConstLp 2 ht hμt v),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs,
    indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := v),
    indicatorConstLp_coeFn (p := 2) (hs := hs.inter ht)
      (hμs := ((measure_mono Set.inter_subset_right).trans_lt hμt.lt_top).ne) (c := v)]
    with x hmul hsx htx hst
  rw [hmul, hsx, htx, hst]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

/-- If `s ⊆ t`, multiplying an `L²` constant indicator of `t` by the `L∞` unit indicator of `s`
restricts it to `s`. -/
theorem multiplicationOperator_linftyIndicator_indicatorConstLp_of_subset
    [NormedAddCommGroup E] [NormedSpace ℂ E] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (hst : s ⊆ t) (v : E) :
    multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) (indicatorConstLp 2 ht hμt v) =
      indicatorConstLp 2 hs ((measure_mono hst).trans_lt hμt.lt_top).ne v := by
  simpa [Set.inter_eq_left.mpr hst] using
    multiplicationOperator_linftyIndicator_indicatorConstLp hs ht hμt v

/-- Multiplying an `L²` constant indicator of `s` by the `L∞` unit indicator of `s` fixes it. -/
theorem multiplicationOperator_linftyIndicator_indicatorConstLp_self
    [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (v : E) :
    multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) (indicatorConstLp 2 hs hμs v) =
      indicatorConstLp 2 hs hμs v :=
  multiplicationOperator_linftyIndicator_indicatorConstLp_of_subset hs hs hμs Set.Subset.rfl v

/-- On a sigma-finite measure space, the indicator multiplications along `spanningSets μ` converge
strongly to the identity on `Lp E 2 μ`. -/
theorem tendsto_multiplicationOperator_linftyIndicator_spanningSets [SigmaFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Lp E 2 μ) :
    Tendsto (fun n ↦ multiplicationOperator
      (TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n)) f)
      atTop (𝓝 f) := by
  set P : ℕ → Lp E 2 μ →L[ℂ] Lp E 2 μ := fun n ↦
    multiplicationOperator
      (TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n))
  have hP (n : ℕ) : ‖P n‖ ≤ 1 := (norm_multiplicationOperator_le _).trans
    (TauCeti.isStarProjection_linftyIndicator (μ := μ) (R := ℂ)
      (measurableSet_spanningSets μ n)).norm_le
  have hEqui : Equicontinuous ((↑) ∘ P) :=
    ((NormedSpace.equicontinuous_tfae P).out 2 6).2 (⟨1, hP⟩ : ∃ C, ∀ n, ‖P n‖ ≤ C)
  have hClosed : IsClosed {g : Lp E 2 μ | Tendsto (fun n ↦ P n g) atTop (𝓝 g)} :=
    hEqui.isClosed_setOfPred_tendsto continuous_id
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun g ↦ Tendsto (fun n ↦ P n g) atTop (𝓝 g))
    ?_ (fun _ _ _ _ _ hg₁ hg₂ ↦ by simpa only [map_add] using hg₁.add hg₂) hClosed f
  intro c s hs hμs
  rw [Lp.simpleFunc.coe_indicatorConst]
  simp_rw [P, multiplicationOperator_linftyIndicator_indicatorConstLp
    (measurableSet_spanningSets μ _) hs hμs.ne c]
  refine tendsto_indicatorConstLp_set (l := atTop) ENNReal.ofNat_ne_top ?_
  have hsymm (n : ℕ) : symmDiff (spanningSets μ n ∩ s) s = s \ spanningSets μ n := by
    rw [symmDiff_of_le Set.inter_subset_right, Set.sdiff_inter_self_eq_sdiff]
  simp_rw [hsymm]
  have hinter : (⋂ n, s \ spanningSets μ n) = ∅ := by
    rw [← Set.sdiff_iUnion, iUnion_spanningSets, Set.sdiff_univ]
  simpa [hinter, Function.comp_def] using tendsto_measure_iInter_atTop
    (fun n ↦ (hs.diff (measurableSet_spanningSets μ n)).nullMeasurableSet)
    (fun _ _ hmn ↦ Set.sdiff_subset_sdiff_right (monotone_spanningSets μ hmn))
    ⟨0, ((measure_mono Set.sdiff_subset).trans_lt hμs).ne⟩

/-- Evaluating `T ∘L M_{1_s}` on an `L²` constant indicator `c • 1_r` yields multiplication by
`s.indicator ⇑(T 1_s)`. -/
private theorem comp_multiplicationOperator_linftyIndicator_indicatorConstLp {s r : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hr : MeasurableSet r) (hμr : μ r ≠ ∞) (c : ℂ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ t ht)))
    {a : Lp ℂ ∞ μ} (ha : ⇑a =ᵐ[μ] s.indicator ⇑(T (indicatorConstLp 2 hs hμs (1 : ℂ)))) :
    T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) (indicatorConstLp 2 hr hμr c)) =
      multiplicationOperator a
        (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs)
          (indicatorConstLp 2 hr hμr c)) := by
  set u := indicatorConstLp 2 hs hμs (1 : ℂ)
  have hrs : s ∩ r ⊆ s := Set.inter_subset_left
  have hμsr : μ (s ∩ r) ≠ ∞ := ((measure_mono Set.inter_subset_right).trans_lt hμr.lt_top).ne
  have hcr : indicatorConstLp 2 hr hμr c = c • indicatorConstLp 2 hr hμr (1 : ℂ) := by
    simpa using TauCeti.indicatorConstLp_smul (p := 2) (μ := μ) hr hμr c (1 : ℂ)
  have hPr : multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs)
      (indicatorConstLp 2 hr hμr c) =
      c • multiplicationOperator (TauCeti.linftyIndicator μ ℂ (s ∩ r) (hs.inter hr)) u := by
    rw [hcr, map_smul, multiplicationOperator_linftyIndicator_indicatorConstLp hs hr hμr,
      multiplicationOperator_linftyIndicator_indicatorConstLp_of_subset (hs.inter hr) hs hμs hrs]
  have hTPr : T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs)
      (indicatorConstLp 2 hr hμr c)) =
      c • multiplicationOperator (TauCeti.linftyIndicator μ ℂ (s ∩ r) (hs.inter hr)) (T u) := by
    rw [hPr, map_smul]
    congr 1
    have h := congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ S u)
      ((commute_iff_eq _ _).mp (hcomm (hs.inter hr) hrs))
    rwa [mul_apply_eq_comp, mul_apply_eq_comp] at h
  rw [hTPr, multiplicationOperator_linftyIndicator_indicatorConstLp hs hr hμr]
  apply Lp.ext
  let Psr : Lp ℂ ∞ μ := TauCeti.linftyIndicator μ ℂ (s ∩ r) (hs.inter hr)
  filter_upwards [Lp.coeFn_smul c (multiplicationOperator Psr (T u)),
    multiplicationOperator_ae Psr (T u),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) (hs.inter hr),
    multiplicationOperator_ae a (indicatorConstLp 2 (hs.inter hr) hμsr c), ha,
    indicatorConstLp_coeFn (p := 2) (hs := hs.inter hr) (hμs := hμsr) (c := c)]
    with x hsmul hmul₁ hind hmul₂ ha' hcr'
  rw [hsmul, Pi.smul_apply, hmul₁, hind, hmul₂, ha', hcr']
  by_cases hx : x ∈ s ∩ r
  · simp [hx, hx.left, mul_comm c]
  · simp [hx]

/-- **Local multiplier representation on a finite-measure set.** On an arbitrary measure space, a
bounded operator on `Lp ℂ 2 μ` that commutes with indicator multiplications on measurable subsets
of a finite-measure measurable set `s` agrees after cutoff to `s` with multiplication by an `L∞`
symbol of norm at most `‖T‖`. -/
theorem exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ t ht))) :
    ∃ a : Lp ℂ ∞ μ, ‖a‖ ≤ ‖T‖ ∧
      T ∘L multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) =
        multiplicationOperator a ∘L
          multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) := by
  set u := indicatorConstLp 2 hs hμs (1 : ℂ)
  set φ : α → ℂ := s.indicator ⇑(T u)
  have hφ_eLp : eLpNorm φ ∞ μ ≤ ‖T‖ₑ := by
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    refine eLpNorm_top_le_of_forall_eLpNorm_indicator_le (μ := μ.restrict s) (p := 2)
      (Lp.aestronglyMeasurable (T u)).restrict two_ne_zero ENNReal.ofNat_ne_top fun t ht _ ↦ ?_
    set r : Set α := t ∩ s
    have hr : MeasurableSet r := ht.inter hs
    have hrs : r ⊆ s := Set.inter_subset_right
    have hμr : μ r ≠ ∞ := ((measure_mono hrs).trans_lt hμs.lt_top).ne
    set f := indicatorConstLp 2 hr hμr (1 : ℂ)
    have hfu : multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) u = f :=
      multiplicationOperator_linftyIndicator_indicatorConstLp_of_subset hr hs hμs hrs (1 : ℂ)
    have hTf : T f = multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) (T u) := by
      simpa [mul_apply_eq_comp, hfu] using
        congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ S u) ((commute_iff_eq _ _).mp (hcomm hr hrs))
    have hae : r.indicator ⇑(T u) =ᵐ[μ] ⇑(T f) := by
      filter_upwards [(Lp.ext_iff.mp hTf).trans (multiplicationOperator_ae _ (T u)),
        TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hr] with x hmul hind
      rw [hmul, hind]
      by_cases hx : x ∈ r <;> simp [hx]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict ht.nullMeasurableSet, Measure.restrict_restrict ht,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hr.nullMeasurableSet, eLpNorm_congr_ae hae,
      ← Lp.eNorm_def, Measure.restrict_apply ht]
    refine (T.le_opENorm f).trans_eq ?_
    rw [Lp.eNorm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
      eLpNorm_indicator_const hr.nullMeasurableSet two_ne_zero ENNReal.ofNat_ne_top,
      eNorm_one, one_mul]
  have hφ_mem : MemLp φ ∞ μ := hφ_eLp.trans_lt eNorm_lt_top
  set a : Lp ℂ ∞ μ := hφ_mem.toLp φ
  have ha_norm : ‖a‖ ≤ ‖T‖ := by
    rw [Lp.norm_def, ← toReal_eNorm T]
    exact ENNReal.toReal_mono eNorm_ne_top ((eLpNorm_congr_ae hφ_mem.coeFn_toLp).le.trans hφ_eLp)
  refine ⟨a, ha_norm, ContinuousLinearMap.ext_indicatorConstLp ENNReal.ofNat_ne_top
    fun r hr hμr c ↦ comp_multiplicationOperator_linftyIndicator_indicatorConstLp hs hμs hr hμr c T
      hcomm hφ_mem.coeFn_toLp⟩

/-- **Unconditional commutativity of the multiplier commutant.** On an arbitrary measure space —
with no sigma-finiteness assumption — any two bounded operators on `Lp ℂ 2 μ` that commute with
all finite-measure indicator multiplications commute with each other. -/
theorem commute_of_forall_commute_multiplicationOperator_linftyIndicator
    {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute S (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs)))
    (hT : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs))) :
    Commute S T := by
  refine (commute_iff_eq _ _).mpr
    (ContinuousLinearMap.ext_indicatorConstLp ENNReal.ofNat_ne_top fun s hs hμs c ↦ ?_)
  set u := indicatorConstLp 2 hs hμs c
  set P := multiplicationOperator (E := ℂ) (p := 2) (TauCeti.linftyIndicator μ ℂ s hs)
  have hPu : P u = u :=
    multiplicationOperator_linftyIndicator_indicatorConstLp_self hs hμs c
  obtain ⟨a, -, ha⟩ := exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq hs
    hμs S fun t ht hts ↦ hS ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq hs
    hμs T fun t ht hts ↦ hT ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  have happly {A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {x y : Lp ℂ ∞ μ}
      (hA : A ∘L P = multiplicationOperator x ∘L P)
      (hB : B ∘L P = multiplicationOperator y ∘L P) :
      (A * B) u = multiplicationOperator (x * y) u := by
    have hBu : B u = multiplicationOperator y u := by
      simpa only [comp_apply, hPu] using congrArg (fun R ↦ R u) hB
    have hPBu : P (B u) = B u := by
      rw [hBu, ← mul_apply_eq_comp,
        (commute_iff_eq _ _).mp (commute_multiplicationOperator _ y), mul_apply_eq_comp, hPu]
    calc (A * B) u = (A ∘L P) (B u) := by rw [mul_apply_eq_comp, comp_apply, hPBu]
      _ = multiplicationOperator x (B u) := by rw [hA, comp_apply, hPBu]
      _ = multiplicationOperator (x * y) u := by
        rw [hBu, ← comp_apply, multiplicationOperator_comp_multiplicationOperator]
  rw [happly ha hb, happly hb ha, mul_comm a b]

/-- On an arbitrary measure space, any two operators in the centralizer of the range of
`multiplicationOperator` commute with each other. -/
theorem commute_of_mem_centralizer_range_multiplicationOperator {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : S ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer)
    (hT : T ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer) :
    Commute S T :=
  commute_of_forall_commute_multiplicationOperator_linftyIndicator
    (fun s hs _ ↦ (commute_iff_eq _ _).mpr
      (hS _ ⟨TauCeti.linftyIndicator μ ℂ s hs, rfl⟩).symm)
    (fun s hs _ ↦ (commute_iff_eq _ _).mpr
      (hT _ ⟨TauCeti.linftyIndicator μ ℂ s hs, rfl⟩).symm)

/-- Uniformly bounded `L∞` symbols `b n` compatible along `spanningSets μ` glue into a single
global symbol `a : Lp ℂ ∞ μ` agreeing with `b n` on each `spanningSets μ n`. -/
private theorem exists_mul_linftyIndicator_spanningSets_eq [SigmaFinite μ] {C : ℝ}
    (b : ℕ → Lp ℂ ∞ μ) (hb_norm : ∀ n, ‖b n‖ ≤ C)
    (hcompat : ∀ᵐ x ∂μ, ∀ m n : ℕ, m ≤ n → x ∈ spanningSets μ m → b m x = b n x) :
    ∃ a : Lp ℂ ∞ μ, ∀ n : ℕ,
      a * TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n) =
        b n * TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n) := by
  set φ : α → ℂ := fun x ↦ b (spanningSetsIndex μ x) x
  have hφ_meas : StronglyMeasurable φ :=
    (stronglyMeasurable_uncurry_of_countable fun n ↦ Lp.stronglyMeasurable (b n)).comp_measurable
      ((measurableSet_spanningSetsIndex μ).prodMk measurable_id)
  have hφ_bdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := by
    filter_upwards [ae_all_iff.mpr fun n : ℕ ↦ Lp.ae_norm_le_norm_top (b n)] with x hx
    exact (hx (spanningSetsIndex μ x)).trans (hb_norm _)
  have hφ_mem : MemLp φ ∞ μ := memLp_top_of_bound hφ_meas.aestronglyMeasurable C hφ_bdd
  refine ⟨hφ_mem.toLp φ, fun n ↦ Lp.ext ?_⟩
  set en := TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n)
  filter_upwards [coeFn_mul (hφ_mem.toLp φ) en, coeFn_mul (b n) en, hφ_mem.coeFn_toLp,
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) (measurableSet_spanningSets μ n), hcompat]
    with x hmul₁ hmul₂ ha hind hcomp
  rw [hmul₁, hmul₂, Pi.mul_apply, Pi.mul_apply, ha, hind]
  by_cases hx : x ∈ spanningSets μ n
  · have hφx : φ x = b n x := by
      rcases le_total (spanningSetsIndex μ x) n with hle | hle
      · exact hcomp _ n hle (mem_spanningSetsIndex μ x)
      · exact (hcomp n _ hle hx).symm
    simp [hx, hφx]
  · simp [hx]

/-- **Multiplier commutant theorem on sigma-finite `L²`.** Every bounded operator on `Lp ℂ 2 μ`
that commutes with all finite-measure indicator multiplications is multiplication by an essentially
bounded symbol. -/
theorem exists_multiplicationOperator_eq_of_forall_commute_linftyIndicator [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs))) :
    ∃ a : Lp ℂ ∞ μ, multiplicationOperator (E := ℂ) a = T := by
  set E : ℕ → Set α := spanningSets μ
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_spanningSets μ n
  have hμE (n : ℕ) : μ (E n) ≠ ∞ := (measure_spanningSets_lt_top μ n).ne
  set e : ℕ → Lp ℂ ∞ μ := fun n ↦ TauCeti.linftyIndicator μ ℂ (E n) (hE n)
  choose b hb_norm hb_eq using fun n : ℕ ↦
    exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq (hE n) (hμE n) T
      fun t ht hts ↦ hcomm ht ((measure_mono hts).trans_lt (hμE n).lt_top).ne
  have hcompat : ∀ᵐ x ∂μ, ∀ m n : ℕ, m ≤ n → x ∈ E m → b m x = b n x := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n
    by_cases hmn : m ≤ n
    · have hem : e n * e m = e m :=
        TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_right (hE n) (hE m)
          (monotone_spanningSets μ hmn)
      have hbm : multiplicationOperator (E := ℂ) (p := 2) (b m * e m) =
          multiplicationOperator (E := ℂ) (p := 2) (b n * e m) := by
        calc multiplicationOperator (E := ℂ) (p := 2) (b m * e m)
            = T ∘L multiplicationOperator (e m) := by
                rw [← multiplicationOperator_comp_multiplicationOperator, ← hb_eq m]
          _ = (T ∘L multiplicationOperator (e n)) ∘L multiplicationOperator (e m) := by
                rw [comp_assoc, multiplicationOperator_comp_multiplicationOperator, hem]
          _ = multiplicationOperator (E := ℂ) (p := 2) (b n * e m) := by
                rw [hb_eq n, comp_assoc, multiplicationOperator_comp_multiplicationOperator, hem,
                  multiplicationOperator_comp_multiplicationOperator]
      have hbe := multiplicationOperator_injective (E := ℂ) (p := 2) hbm
      filter_upwards [coeFn_mul (b m) (e m), (Lp.ext_iff.mp hbe).trans (coeFn_mul (b n) (e m)),
        TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) (hE m)] with x h₁ h₂ hind _ hxEm
      rw [Pi.mul_apply, hind, Set.indicator_of_mem hxEm, Pi.one_apply, mul_one] at h₁ h₂
      exact h₁.symm.trans h₂
    · exact ae_of_all _ fun _ hle ↦ (hmn hle).elim
  obtain ⟨a, hae⟩ := exists_mul_linftyIndicator_spanningSets_eq b hb_norm hcompat
  refine ⟨a, ContinuousLinearMap.ext fun f ↦ ?_⟩
  have hstep (n : ℕ) :
      multiplicationOperator a (multiplicationOperator (e n) f) =
        T (multiplicationOperator (e n) f) := by
    rw [← comp_apply, ← comp_apply, hb_eq n, multiplicationOperator_comp_multiplicationOperator,
      multiplicationOperator_comp_multiplicationOperator, hae n]
  have htend := tendsto_multiplicationOperator_linftyIndicator_spanningSets f
  exact tendsto_nhds_unique (((multiplicationOperator a).continuous.tendsto f).comp htend)
    (((T.continuous.tendsto f).comp htend).congr fun n ↦ (hstep n).symm)

/-- On a sigma-finite measure space, the centralizer in `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` of the range of
`multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] :
    (Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_linftyIndicator T fun s hs _ ↦
      (commute_iff_eq _ _).mpr
        (hT _ ⟨TauCeti.linftyIndicator μ ℂ s hs, rfl⟩).symm
  · rintro ⟨a, rfl⟩ S ⟨b, rfl⟩
    exact (commute_iff_eq _ _).mp (commute_multiplicationOperator b a)

/-- An `L∞` symbol supported on a finite-measure measurable set `s` whose multiplication operator
on `Lp E 2 μ` (for a nontrivial space `E`) vanishes is zero in `Lp ℂ ∞ μ` (with no `SigmaFinite`
hypothesis on `μ`). -/
theorem eq_zero_of_mul_linftyIndicator_eq_self_of_multiplicationOperator_eq_zero
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {a : Lp ℂ ∞ μ}
    (hsupp : a * TauCeti.linftyIndicator μ ℂ s hs = a)
    (hzero : multiplicationOperator (E := E) (p := 2) a = 0) : a = 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have happly : multiplicationOperator (E := E) a (indicatorConstLp 2 hs hμs v) = 0 := by
    rw [hzero, zero_apply]
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [(Lp.ext_iff.mp hsupp.symm).trans (Lp.coeFn_mul a _),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs,
    (multiplicationOperator_ae a (indicatorConstLp 2 hs hμs v)).symm.trans
      ((Lp.ext_iff.mp happly).trans (Lp.coeFn_zero E 2 μ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v)]
    with x hmul hsx h0 hind
  by_cases hxs : x ∈ s
  · simp only [hind, Set.indicator_of_mem hxs, Pi.zero_apply, smul_eq_zero] at h0
    exact h0.resolve_right hv
  · rw [hmul, Pi.mul_apply, hsx, Set.indicator_of_notMem hxs, mul_zero, Pi.zero_apply]

/-- If a symbol `a ∈ Lp ℂ ∞ μ` avoids `c` almost everywhere, then `multiplicationOperator a` on
`Lp E 2 μ` has trivial `c`-eigenspace. -/
theorem eq_zero_of_multiplicationOperator_eq_smul [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : Lp ℂ ∞ μ} {c : ℂ} (ha : ∀ᵐ x ∂μ, a x ≠ c) {f : Lp E 2 μ}
    (hf : multiplicationOperator a f = c • f) : f = 0 := by
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [(Lp.ext_iff.mp hf.symm).trans (multiplicationOperator_ae a f),
    Lp.coeFn_smul c f, ha] with x hmul hsmul hne
  have heq : (a x - c) • f x = 0 := by
    rw [sub_smul, ← hmul, hsmul, Pi.smul_apply, sub_self]
  exact (smul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hne)

/-- If a symbol `a ∈ Lp ℂ ∞ μ` avoids `c` almost everywhere, then `c` is not an eigenvalue of
`multiplicationOperator a` on `Lp E 2 μ`. -/
theorem not_hasEigenvalue_multiplicationOperator [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : Lp ℂ ∞ μ) {c : ℂ} (ha : ∀ᵐ x ∂μ, a x ≠ c) :
    ¬ Module.End.HasEigenvalue (multiplicationOperator (E := E) (p := 2) a).toLinearMap c := by
  intro hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  exact hv0 <| eq_zero_of_multiplicationOperator_eq_smul ha (Module.End.mem_eigenspace_iff.mp hv)

end Commutant

end MeasureTheory.Lp

section

open scoped unitInterval

namespace TauCeti.unitInterval

open MeasureTheory

/-- The bounded coordinate symbol `t ↦ (t : ℂ)` in `Lp ℂ ∞ (volume : Measure unitInterval)`. -/
def coordLp : Lp ℂ ∞ (volume : Measure I) :=
  ContinuousMap.toLp ∞ (volume : Measure I) ℂ
    ⟨fun t : I ↦ ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtypeVal⟩

/-- Almost everywhere on `unitInterval`, `coordLp` evaluates to `t ↦ (t : ℂ)`. -/
theorem coeFn_coordLp :
    ⇑coordLp =ᵐ[volume] fun t : I ↦ ((t : ℝ) : ℂ) := by
  rw [coordLp]
  filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (volume : Measure I)
    ⟨fun t : I ↦ ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtypeVal⟩] with t ht
  rw [ht, ContinuousMap.coe_mk]

/-- The real-valued coordinate symbol `coordLp` is self-adjoint. -/
@[simp]
theorem star_coordLp : star coordLp = coordLp :=
  Lp.star_eq_self_of_ae_eq_ofReal coeFn_coordLp

/-- Multiplication by the coordinate function `t ↦ (t : ℂ)` on `Lp E 2 (volume : Measure I)` has
no eigenvalues. -/
theorem not_hasEigenvalue_multiplicationOperator_coordLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) :
    ¬ Module.End.HasEigenvalue
      (Lp.multiplicationOperator (E := E) (p := 2) coordLp).toLinearMap c := by
  have hnull : ∀ᵐ t : I ∂volume, ((t : ℝ) : ℂ) ≠ c := by
    rw [ae_iff]
    exact Set.Subsingleton.measure_zero
      (fun _ hx _ hy ↦ Subtype.ext (Complex.ofReal_injective
        ((not_not.mp hx).trans (not_not.mp hy).symm))) volume
  refine Lp.not_hasEigenvalue_multiplicationOperator coordLp ?_
  filter_upwards [coeFn_coordLp, hnull] with t ht hne
  rwa [ht]

end TauCeti.unitInterval

end
