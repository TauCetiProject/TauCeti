/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Multiplication operators on complex L²

An essentially bounded complex function `a` acts on `L²` by pointwise multiplication.  This file
bundles that action as `MeasureTheory.Lp.multiplicationOperator a` and records its algebraic,
adjoint, norm, pullback, and commutant properties.  In particular, `multiplicationOperator` is a
unital ⋆-algebra homomorphism `MeasureTheory.Lp.multiplicationStarAlgHom`, on a sigma-finite
measure space its operator norm on `L²` with values in any nontrivial space is the `L∞` norm of
the symbol, and on complex scalar `L²` every bounded operator commuting with indicator
multiplications on sets of finite measure is locally multiplication by an `L∞` symbol (and globally
so when the measure is sigma-finite).

The construction is Mathlib's Hölder map for scalar multiplication with one exponent equal to
infinity.  The resulting operator is the ambient multiplication operator compressed in the
definition of a Toeplitz operator and generating the multiplication von Neumann algebra on `L²`.
-/

public section

noncomputable section

open Filter
open scoped ENNReal ComplexInnerProductSpace InnerProduct Topology

namespace MeasureTheory.Lp

open ContinuousLinearMap

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pointwise multiplication by an essentially bounded complex symbol, as a bounded operator on
`L²`. -/
def multiplicationOperator (a : Lp ℂ ∞ μ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2 a

/-- On scalar `L²`, `multiplicationOperator` agrees with the Hölder operator built from complex
multiplication `ContinuousLinearMap.mul ℂ ℂ`. -/
theorem holderL_mul_eq_multiplicationOperator :
    ⇑((ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2) =
      multiplicationOperator (E := ℂ) (μ := μ) := by
  funext a
  have hmul : ContinuousLinearMap.mul ℂ ℂ = (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) :=
    ContinuousLinearMap.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl
  rw [multiplicationOperator, hmul]

/-- The multiplication operator acts by pointwise multiplication almost everywhere. -/
theorem multiplicationOperator_ae (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplicationOperator a f =ᵐ[μ] fun x ↦ a x • f x := by
  simpa only [multiplicationOperator, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.lsmul_apply] using
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).coeFn_holder (r := 2) a f

/-- Applying the multiplication operator is heterogeneous `Lp` scalar multiplication. -/
theorem multiplicationOperator_apply (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplicationOperator a f = a • f := by
  apply Lp.ext
  exact (multiplicationOperator_ae a f).trans (coeFn_lpSMul (r := 2) a f).symm

/-- Multiplication by `a` changes the `L²` norm by at most `‖a‖∞`. -/
theorem norm_multiplicationOperator_apply_le (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    ‖multiplicationOperator a f‖ ≤ ‖a‖ * ‖f‖ := by
  rw [multiplicationOperator_apply]
  exact Lp.norm_smul_le a f

/-- The operator norm of multiplication by `a` is at most its `L∞` norm. -/
theorem norm_multiplicationOperator_le (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := E) a‖ ≤ ‖a‖ :=
  opNorm_le_bound _ (norm_nonneg a) (norm_multiplicationOperator_apply_le a)

@[simp]
theorem multiplicationOperator_zero :
    multiplicationOperator (E := E) (0 : Lp ℂ ∞ μ) = 0 := by
  simp [multiplicationOperator]

/-- Multiplication operators depend additively on their symbols. -/
@[simp]
theorem multiplicationOperator_add (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (a + b) =
      multiplicationOperator a + multiplicationOperator b := by
  simp [multiplicationOperator]

@[simp]
theorem multiplicationOperator_neg (a : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (-a) = -multiplicationOperator a := by
  simp [multiplicationOperator]

@[simp]
theorem multiplicationOperator_sub (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (a - b) =
      multiplicationOperator a - multiplicationOperator b := by
  simp [multiplicationOperator]

/-- Multiplication operators depend complex-linearly on their symbols. -/
@[simp]
theorem multiplicationOperator_smul (c : ℂ) (a : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (c • a) = c • multiplicationOperator a := by
  simp [multiplicationOperator]

/-- Composing multiplication operators multiplies their symbols in the same order. -/
theorem multiplicationOperator_comp_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) a ∘L multiplicationOperator b =
      multiplicationOperator (a * b) := by
  ext f
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f,
    multiplicationOperator_ae (a * b) f,
    coeFn_mul a b] with x ha hb hab hsmul
  simp only [comp_apply, ha, hb, hab, hsmul, Pi.mul_apply]
  rw [smul_smul]

/-- Multiplying symbols multiplies the corresponding operators. -/
@[simp]
theorem multiplicationOperator_mul (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (a * b) =
      multiplicationOperator a * multiplicationOperator b :=
  (multiplicationOperator_comp_multiplicationOperator a b).symm

/-- Multiplication operators commute with each other. -/
theorem commute_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    Commute (multiplicationOperator (E := E) a) (multiplicationOperator b) := by
  refine (commute_iff_eq _ _).2 (ContinuousLinearMap.ext fun f ↦ Lp.ext ?_)
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f, multiplicationOperator_ae b (multiplicationOperator a f),
    multiplicationOperator_ae a f] with x hab hb hba ha
  simp only [mul_apply_eq_comp, hab, hb, hba, ha, smul_smul, mul_comm]

/-- Multiplication by a symbol of modulus one almost everywhere preserves the `L²` norm. -/
theorem norm_multiplicationOperator_apply_of_ae_norm_eq_one {u : Lp ℂ ∞ μ}
    (hu : ∀ᵐ x ∂μ, ‖u x‖ = 1) (f : Lp E 2 μ) :
    ‖multiplicationOperator u f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂μ, ‖multiplicationOperator u f x‖ = ‖f x‖ := by
    filter_upwards [multiplicationOperator_ae u f, hu] with x hx hux
    rw [hx, norm_smul, hux, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.ge))

/-- A symbol equal almost everywhere to a constant acts by scalar multiplication. -/
theorem multiplicationOperator_of_ae_eq_const {a : Lp ℂ ∞ μ} {c : ℂ}
    (ha : a =ᵐ[μ] fun _ ↦ c) :
    multiplicationOperator (E := E) a = c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
  ext f
  filter_upwards [multiplicationOperator_ae a f, Lp.coeFn_smul c f, ha] with x h hf ha'
  simp [h, hf, ha']

/-- Multiplication by the unit `1 : Lp ℂ ∞ μ` is the identity operator on `L²`. -/
@[simp]
theorem multiplicationOperator_one :
    multiplicationOperator (E := E) (1 : Lp ℂ ∞ μ) = 1 := by
  have h := multiplicationOperator_of_ae_eq_const (E := E) (c := (1 : ℂ))
    (coeFn_one (E := ℂ) (μ := μ))
  rwa [one_smul, ← ContinuousLinearMap.one_def] at h

/-- The scalar embedding into `L∞` acts on `L²` by scalar multiplication. -/
@[simp]
theorem multiplicationOperator_algebraMap (c : ℂ) :
    multiplicationOperator (E := E) (algebraMap ℂ (Lp ℂ ∞ μ) c) =
      c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
  apply multiplicationOperator_of_ae_eq_const
  simpa only [Algebra.algebraMap_self_apply] using coeFn_algebraMap (R := ℂ) (μ := μ) c

/-- Precomposition along a measure-preserving map intertwines `multiplicationOperator`. -/
theorem compMeasurePreserving_multiplicationOperator_apply {β : Type*} [MeasurableSpace β]
    {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν) (a : Lp ℂ ∞ ν) (f : Lp E 2 ν) :
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

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The adjoint of multiplication by `a` is multiplication by its complex conjugate. -/
@[simp]
theorem adjoint_multiplicationOperator (a : Lp ℂ ∞ μ) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Lp E 2 μ) (F := Lp E 2 μ)
      (multiplicationOperator (E := E) a) =
      multiplicationOperator (E := E) (star a) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multiplicationOperator_ae (star a) f,
    multiplicationOperator_ae a g, Lp.coeFn_star a] with x hf hg ha
  simp [hf, hg, ha, inner_smul_left, inner_smul_right]

/-- The operator-algebra involution of multiplication by `a` is multiplication by `star a`. -/
@[simp]
theorem star_multiplicationOperator (a : Lp ℂ ∞ μ) :
    star (multiplicationOperator (E := E) a) = multiplicationOperator (E := E) (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_multiplicationOperator]

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

end InnerProductSpace

section FiniteMeasure

variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsFiniteMeasure μ]

@[simp]
theorem multiplicationOperator_const (c : ℂ) :
    multiplicationOperator (E := E) (Lp.const ∞ μ c) =
      c • ContinuousLinearMap.id ℂ (Lp E 2 μ) :=
  multiplicationOperator_of_ae_eq_const (Lp.coeFn_const (μ := μ) ∞ c)

end FiniteMeasure

section ExactNorm

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `c ≤ ‖a‖` pointwise on `s`, then multiplication by `a` scales the `L²` norm of a constant
indicator of `s` by at least `c`. -/
private theorem mul_norm_indicatorConstLp_le {a : Lp ℂ ∞ μ} {c : ℝ} (hc_nonneg : 0 ≤ c)
    {s : Set α} (hs : MeasurableSet s) (hs_top : μ s ≠ ∞) (ha : ∀ x ∈ s, c ≤ ‖a x‖)
    (v : E) :
    c * ‖indicatorConstLp 2 hs hs_top v‖ ≤
      ‖multiplicationOperator a (indicatorConstLp 2 hs hs_top v)‖ := by
  set f := indicatorConstLp 2 hs hs_top v
  set g := indicatorConstLp 2 hs hs_top ((c : ℂ) • v)
  have hfg : c * ‖f‖ = ‖g‖ := by
    simp only [f, g, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_nonneg, mul_assoc]
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖multiplicationOperator a f x‖ := by
    filter_upwards [multiplicationOperator_ae a f, indicatorConstLp_coeFn (p := 2) (c := v),
      indicatorConstLp_coeFn (p := 2) (c := (c : ℂ) • v)] with x hmul hf hg
    rw [hmul, hf, hg]
    by_cases hx : x ∈ s
    · have hcx : c ≤ ‖a x‖ := ha x hx
      simp only [Set.indicator_of_mem hx, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc_nonneg]
      gcongr
    · simp [Set.indicator_of_notMem hx]
  rw [hfg]
  exact Lp.norm_le_norm_of_ae_le hpoint

/-- On a sigma-finite measure space, the operator norm of multiplication by `a` on `L²` with
values in a nontrivial space is exactly the `L∞` norm of `a`. -/
@[simp]
theorem norm_multiplicationOperator [SigmaFinite μ] [Nontrivial E] (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := E) a‖ = ‖a‖ := by
  apply le_antisymm (norm_multiplicationOperator_le a)
  by_contra hle
  have _ : ‖multiplicationOperator (E := E) a‖ < ‖a‖ := lt_of_not_ge hle
  -- Test the operator on the indicator of the set where `‖a‖` exceeds a level `c` strictly
  -- between the operator norm and `‖a‖`.
  set c := (‖multiplicationOperator (E := E) a‖ + ‖a‖) / 2 with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have hop_lt_c : ‖multiplicationOperator (E := E) a‖ < c := by linarith [hc_def]
  have hc_lt : c < ‖a‖ := by linarith [hc_def]
  set s := {x | c < ‖a x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable a).norm.measurable
  have hμs : μ s ≠ 0 := measure_lt_norm_ne_zero hc_nonneg hc_lt
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set f := indicatorConstLp 2 ht hμt_top.ne v
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    have hμt_real_pos : 0 < μ.real t := ENNReal.toReal_pos hμt_pos.ne' hμt_top.ne
    exact mul_pos (norm_pos_iff.mpr hv) (Real.rpow_pos_of_pos hμt_real_pos _)
  -- Comparing the lower bound on `f` with the operator norm forces `c ≤ ‖M_a‖`.
  have hcancel : c * ‖f‖ ≤ ‖multiplicationOperator (E := E) a‖ * ‖f‖ :=
    (mul_norm_indicatorConstLp_le hc_nonneg ht hμt_top.ne
      (fun _ hx ↦ le_of_lt (hts hx)) v).trans
      (le_opNorm _ _)
  exact (not_le_of_gt hop_lt_c) (le_of_mul_le_mul_right hcancel hf_pos)

/-- On a sigma-finite measure space, `multiplicationOperator` is an isometry into the bounded
operators on `L²` with values in a nontrivial space. -/
theorem isometry_multiplicationOperator [SigmaFinite μ] [Nontrivial E] :
    Isometry (multiplicationOperator (E := E) (μ := μ)) :=
  AddMonoidHomClass.isometry_of_norm
    ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2)
    (norm_multiplicationOperator (E := E))

/-- On a sigma-finite measure space, `multiplicationOperator` is injective on `L∞` whenever the
target fibre `E` is nontrivial. -/
theorem multiplicationOperator_injective [SigmaFinite μ] [Nontrivial E] :
    Function.Injective (multiplicationOperator (E := E) (μ := μ)) :=
  (isometry_multiplicationOperator (E := E) (μ := μ)).injective

@[simp]
theorem multiplicationOperator_inj [SigmaFinite μ] [Nontrivial E] {a b : Lp ℂ ∞ μ} :
    multiplicationOperator (E := E) a = multiplicationOperator (E := E) b ↔ a = b :=
  (multiplicationOperator_injective (E := E) (μ := μ)).eq_iff

end ExactNorm

section Commutant

/-- Multiplication by an `L∞` measurable-set unit indicator cuts off an `L²` constant indicator to
the intersection of the two sets. -/
theorem multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp
    [NormedAddCommGroup E] [NormedSpace ℂ E] {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (v : E) :
    multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
        (indicatorConstLp 2 ht hμt v) =
      indicatorConstLp 2 (hs.inter ht)
        ((measure_mono Set.inter_subset_right).trans_lt hμt.lt_top).ne v := by
  apply Lp.ext
  filter_upwards [multiplicationOperator_ae
      (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
      (indicatorConstLp 2 ht hμt v),
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) hs,
    indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := v),
    indicatorConstLp_coeFn (p := 2) (hs := hs.inter ht)
      (hμs := ((measure_mono Set.inter_subset_right).trans_lt hμt.lt_top).ne) (c := v)]
    with x hmul hsx htx hst
  rw [hmul, hsx, htx, hst]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

/-- For an equicontinuous sequence of contractions `P n`, the set of vectors on which `P n g → g`
is norm-closed. -/
private theorem isClosed_tendsto_atTop_of_opNorm_le_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (P : ℕ → F →L[ℂ] F) (hP : ∀ n, ‖P n‖ ≤ 1) :
    IsClosed {g : F | Tendsto (fun n ↦ P n g) atTop (𝓝 g)} := by
  rw [← closure_subset_iff_isClosed]
  intro g hg
  change Tendsto (fun n ↦ P n g) atTop (𝓝 g)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.mp hg (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh (ε / 3) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hstep : dist (P n g) (P n h) ≤ dist g h :=
    ((P n).lipschitzWith.dist_le_mul g h).trans (mul_le_of_le_one_left dist_nonneg (hP n))
  have hnh : dist (P n h) h < ε / 3 := hN n hn
  calc dist (P n g) g
      ≤ dist (P n g) (P n h) + dist (P n h) h + dist h g := dist_triangle4 _ _ _ _
    _ ≤ dist g h + dist (P n h) h + dist g h := by rw [dist_comm h g]; gcongr
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- On a sigma-finite measure space, the indicator multiplications along `spanningSets μ` converge
strongly to the identity on `Lp E 2 μ`. -/
theorem tendsto_multiplicationOperator_toLpTop_piecewise_spanningSets [SigmaFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Lp E 2 μ) :
    Tendsto (fun n ↦ multiplicationOperator
      (SimpleFunc.toLpTop μ ℂ
        (SimpleFunc.piecewise (spanningSets μ n) (measurableSet_spanningSets μ n)
          (1 : SimpleFunc α ℂ) 0)) f)
      atTop (𝓝 f) := by
  set P : ℕ → Lp E 2 μ →L[ℂ] Lp E 2 μ := fun n ↦ multiplicationOperator
    (SimpleFunc.toLpTop μ ℂ
      (SimpleFunc.piecewise (spanningSets μ n) (measurableSet_spanningSets μ n)
        (1 : SimpleFunc α ℂ) 0))
  have hClosed : IsClosed {g : Lp E 2 μ | Tendsto (fun n ↦ P n g) atTop (𝓝 g)} :=
    isClosed_tendsto_atTop_of_opNorm_le_one P fun n ↦ (norm_multiplicationOperator_le _).trans <|
      Lp.norm_top_le_of_ae_bound zero_le_one <| by
        filter_upwards [coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ)
          (measurableSet_spanningSets μ n)] with x hx
        by_cases hxs : x ∈ spanningSets μ n <;> simp [hx, hxs]
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun g ↦ Tendsto (fun n ↦ P n g) atTop (𝓝 g))
    ?_ (fun _ _ _ _ _ hg₁ hg₂ ↦ by simpa only [map_add] using hg₁.add hg₂) hClosed f
  intro c s hs hμs
  rw [Lp.simpleFunc.coe_indicatorConst]
  simp_rw [P, multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp
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

/-- Each superlevel set `{x ∈ s | c ≤ ‖T (1_s) x‖}` with `‖T‖ < c` has measure zero when `T`
commutes with indicator multiplications on measurable subsets of `s`. -/
private theorem measure_inter_le_norm_apply_indicatorConstLp_eq_zero {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0))))
    {c : ℝ} (hc_gt : ‖T‖ < c) :
    μ {x | x ∈ s ∧ c ≤ ‖T (indicatorConstLp 2 hs hμs (1 : ℂ)) x‖} = 0 := by
  set u := indicatorConstLp 2 hs hμs (1 : ℂ)
  have hc_nonneg : 0 ≤ c := (norm_nonneg T).trans hc_gt.le
  set t : Set α := s ∩ {x | c ≤ ‖T u x‖}
  have ht : MeasurableSet t :=
    hs.inter (measurableSet_le measurable_const (Lp.stronglyMeasurable (T u)).norm.measurable)
  have hts : t ⊆ s := Set.inter_subset_left
  have hμt : μ t ≠ ∞ := ((measure_mono hts).trans_lt hμs.lt_top).ne
  set f := indicatorConstLp 2 ht hμt (1 : ℂ)
  have hfu : multiplicationOperator
      (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0)) u = f := by
    simpa [u, f, Set.inter_eq_left.mpr hts] using
      multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp ht hs hμs (1 : ℂ)
  have hTf : T f = multiplicationOperator
      (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0)) (T u) := by
    simpa [mul_apply_eq_comp, hfu] using
      congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ S u) ((commute_iff_eq _ _).mp (hcomm ht hts))
  have hpoint : ∀ᵐ x ∂μ, ‖((c : ℂ) • f) x‖ ≤ ‖T f x‖ := by
    filter_upwards [Lp.coeFn_smul (c : ℂ) f,
      (Lp.ext_iff.mp hTf).trans (multiplicationOperator_ae _ (T u)),
      coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) ht,
      indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := (1 : ℂ))]
      with x hsmul hmul hpt hf'
    rw [hsmul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc_nonneg,
      hmul, hpt, hf']
    by_cases hxt : x ∈ t
    · rw [Set.indicator_of_mem hxt, Set.indicator_of_mem hxt, Pi.one_apply, norm_one, mul_one,
        one_smul]
      exact hxt.2
    · simp [hxt]
  have hcf : c * ‖f‖ ≤ ‖T‖ * ‖f‖ := calc
    c * ‖f‖ = ‖(c : ℂ) • f‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc_nonneg]
    _ ≤ ‖T f‖ := Lp.norm_le_norm_of_ae_le hpoint
    _ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
  by_contra hμt_ne
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hμt_ne hμt) _
  exact hc_gt.not_ge (le_of_mul_le_mul_right hcf hf_pos)

/-- If `T` commutes with indicator multiplications on measurable subsets of a finite-measure set
`s`, then `T (1_s)` is bounded in norm by `‖T‖` almost everywhere on `s`. -/
private theorem ae_norm_apply_indicatorConstLp_le_opNorm {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0)))) :
    ∀ᵐ x ∂μ, x ∈ s → ‖T (indicatorConstLp 2 hs hμs (1 : ℂ)) x‖ ≤ ‖T‖ := by
  have hnull (n : ℕ) := measure_inter_le_norm_apply_indicatorConstLp_eq_zero hs hμs T hcomm
    (lt_add_of_pos_right ‖T‖ (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)))
  filter_upwards [ae_all_iff.mpr fun n : ℕ ↦ measure_eq_zero_iff_ae_notMem.mp (hnull n)]
    with x hx hxs
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hlt : ‖T (indicatorConstLp 2 hs hμs (1 : ℂ)) x‖ < ‖T‖ + 1 / (n + 1 : ℝ) :=
    lt_of_not_ge fun hge ↦ hx n ⟨hxs, hge⟩
  linarith

/-- Evaluating `T ∘L M_{1_s}` on an `L²` constant indicator `c • 1_r` yields multiplication by
`s.indicator ⇑(T 1_s)`. -/
private theorem comp_multiplicationOperator_toLpTop_piecewise_indicatorConstLp {s r : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hr : MeasurableSet r) (hμr : μ r ≠ ∞) (c : ℂ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0))))
    {a : Lp ℂ ∞ μ} (ha : ⇑a =ᵐ[μ] s.indicator ⇑(T (indicatorConstLp 2 hs hμs (1 : ℂ)))) :
    T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
        (indicatorConstLp 2 hr hμr c)) =
      multiplicationOperator a
        (multiplicationOperator
          (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
          (indicatorConstLp 2 hr hμr c)) := by
  set u := indicatorConstLp 2 hs hμs (1 : ℂ)
  have hrs : s ∩ r ⊆ s := Set.inter_subset_left
  have hμsr : μ (s ∩ r) ≠ ∞ := ((measure_mono Set.inter_subset_right).trans_lt hμr.lt_top).ne
  have hPr : multiplicationOperator
      (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
      (indicatorConstLp 2 hr hμr c) =
      c • multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ
          (SimpleFunc.piecewise (s ∩ r) (hs.inter hr) (1 : SimpleFunc α ℂ) 0)) u := by
    rw [show indicatorConstLp 2 hr hμr c = c • indicatorConstLp 2 hr hμr (1 : ℂ) by
      simpa using TauCeti.indicatorConstLp_smul (p := 2) (μ := μ) hr hμr c (1 : ℂ)]
    rw [map_smul, multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp hs hr hμr,
      multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp (hs.inter hr) hs hμs]
    congr 2
    exact (Set.inter_eq_left.mpr hrs).symm
  have hTPr : T (multiplicationOperator
      (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
      (indicatorConstLp 2 hr hμr c)) =
      c • multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ
          (SimpleFunc.piecewise (s ∩ r) (hs.inter hr) (1 : SimpleFunc α ℂ) 0)) (T u) := by
    rw [hPr, map_smul]
    congr 1
    exact congrArg (fun S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ S u)
      ((commute_iff_eq _ _).mp (hcomm (hs.inter hr) hrs))
  rw [hTPr, multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp hs hr hμr]
  apply Lp.ext
  let Psr : Lp ℂ ∞ μ :=
    SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise (s ∩ r) (hs.inter hr) (1 : SimpleFunc α ℂ) 0)
  filter_upwards [Lp.coeFn_smul c (multiplicationOperator Psr (T u)),
    multiplicationOperator_ae Psr (T u),
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) (hs.inter hr),
    multiplicationOperator_ae a (indicatorConstLp 2 (hs.inter hr) hμsr c), ha,
    indicatorConstLp_coeFn (p := 2) (hs := hs.inter hr) (hμs := hμsr) (c := c)]
    with x hsmul hmul₁ hind hmul₂ ha' hcr
  rw [hsmul, Pi.smul_apply, hmul₁, hind, hmul₂, ha', hcr]
  by_cases hx : x ∈ s ∩ r
  · simp [hx, hx.1, mul_comm c]
  · simp [hx]

/-- **Local multiplier representation on a finite-measure set.** On an arbitrary measure space, a
bounded operator on `Lp ℂ 2 μ` that commutes with indicator multiplications on measurable subsets
of a finite-measure measurable set `s` agrees after cutoff to `s` with multiplication by an `L∞`
symbol of norm at most `‖T‖`. -/
theorem exists_norm_le_and_comp_multiplicationOperator_toLpTop_piecewise_eq {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise t ht (1 : SimpleFunc α ℂ) 0)))) :
    ∃ a : Lp ℂ ∞ μ, ‖a‖ ≤ ‖T‖ ∧
      T ∘L multiplicationOperator
          (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0)) =
        multiplicationOperator a ∘L multiplicationOperator
          (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0)) := by
  set φ : α → ℂ := s.indicator ⇑(T (indicatorConstLp 2 hs hμs (1 : ℂ)))
  have hφ_meas : StronglyMeasurable φ :=
    (Lp.stronglyMeasurable (T (indicatorConstLp 2 hs hμs (1 : ℂ)))).indicator hs
  have hφ_bdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ‖T‖ := by
    filter_upwards [ae_norm_apply_indicatorConstLp_le_opNorm hs hμs T hcomm] with x hx
    by_cases hxs : x ∈ s
    · simpa [φ, hxs] using hx hxs
    · simp [φ, hxs]
  have hφ_mem : MemLp φ ∞ μ := memLp_top_of_bound hφ_meas.aestronglyMeasurable ‖T‖ hφ_bdd
  set a : Lp ℂ ∞ μ := hφ_mem.toLp φ
  have ha_norm : ‖a‖ ≤ ‖T‖ := Lp.norm_top_le_of_ae_bound (norm_nonneg T) <| by
    filter_upwards [hφ_mem.coeFn_toLp, hφ_bdd] with x ha hx
    rwa [ha]
  refine ⟨a, ha_norm, ContinuousLinearMap.ext fun f ↦ ?_⟩
  set P := multiplicationOperator (E := ℂ)
    (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top
    (fun f ↦ (T ∘L P) f = (multiplicationOperator a ∘L P) f) ?_
    (fun _ _ _ _ _ hg₁ hg₂ ↦ by simp only [map_add, hg₁, hg₂])
    (isClosed_eq (T ∘L P).continuous (multiplicationOperator a ∘L P).continuous) f
  intro c r hr hμr
  rw [Lp.simpleFunc.coe_indicatorConst]
  exact comp_multiplicationOperator_toLpTop_piecewise_indicatorConstLp hs hμs hr hμr.ne c T
    hcomm hφ_mem.coeFn_toLp

/-- **Unconditional commutativity of the multiplier commutant.** On an arbitrary measure space —
with no sigma-finiteness assumption — any two bounded operators on `Lp ℂ 2 μ` that commute with
all finite-measure indicator multiplications commute with each other. -/
theorem commute_of_forall_commute_multiplicationOperator_toLpTop_piecewise
    {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute S (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))))
    (hT : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0)))) :
    Commute S T := by
  refine (commute_iff_eq _ _).mpr (ContinuousLinearMap.ext fun f ↦ ?_)
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun f ↦ (S * T) f = (T * S) f) ?_
    (fun _ _ _ _ _ hg₁ hg₂ ↦ by simp only [map_add, hg₁, hg₂])
    (isClosed_eq (S * T).continuous (T * S).continuous) f
  intro c s hs hμs
  rw [Lp.simpleFunc.coe_indicatorConst]
  set u := indicatorConstLp 2 hs hμs.ne c
  set P := multiplicationOperator (E := ℂ)
    (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0))
  have hPu : P u = u := by
    simpa [P, u, Set.inter_self] using
      multiplicationOperator_toLpTop_piecewise_one_zero_indicatorConstLp hs hs hμs.ne c
  obtain ⟨a, -, ha⟩ := exists_norm_le_and_comp_multiplicationOperator_toLpTop_piecewise_eq hs
    hμs.ne S fun t ht hts ↦ hS ht ((measure_mono hts).trans_lt hμs).ne
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_multiplicationOperator_toLpTop_piecewise_eq hs
    hμs.ne T fun t ht hts ↦ hT ht ((measure_mono hts).trans_lt hμs).ne
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
  commute_of_forall_commute_multiplicationOperator_toLpTop_piecewise
    (fun s hs _ ↦ (commute_iff_eq _ _).mpr
      (hS _ ⟨SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0), rfl⟩).symm)
    (fun s hs _ ↦ (commute_iff_eq _ _).mpr
      (hT _ ⟨SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0), rfl⟩).symm)

/-- Uniformly bounded `L∞` symbols `b n` compatible along `spanningSets μ` glue into a single
global symbol `a : Lp ℂ ∞ μ` agreeing with `b n` on each `spanningSets μ n`. -/
private theorem exists_mul_toLpTop_spanningSets_eq [SigmaFinite μ] {C : ℝ}
    (b : ℕ → Lp ℂ ∞ μ) (hb_norm : ∀ n, ‖b n‖ ≤ C)
    (hcompat : ∀ᵐ x ∂μ, ∀ m n : ℕ, m ≤ n → x ∈ spanningSets μ m → b m x = b n x) :
    ∃ a : Lp ℂ ∞ μ, ∀ n : ℕ,
      a * SimpleFunc.toLpTop μ ℂ
          (SimpleFunc.piecewise (spanningSets μ n) (measurableSet_spanningSets μ n)
            (1 : SimpleFunc α ℂ) 0) =
        b n * SimpleFunc.toLpTop μ ℂ
          (SimpleFunc.piecewise (spanningSets μ n) (measurableSet_spanningSets μ n)
            (1 : SimpleFunc α ℂ) 0) := by
  set φ : α → ℂ := fun x ↦ b (spanningSetsIndex μ x) x
  have hφ_meas : StronglyMeasurable φ :=
    (stronglyMeasurable_uncurry_of_countable fun n ↦ Lp.stronglyMeasurable (b n)).comp_measurable
      ((measurableSet_spanningSetsIndex μ).prodMk measurable_id)
  have hφ_bdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := by
    filter_upwards [ae_all_iff.mpr fun n : ℕ ↦ Lp.ae_norm_le_norm_top (b n)] with x hx
    exact (hx (spanningSetsIndex μ x)).trans (hb_norm _)
  have hφ_mem : MemLp φ ∞ μ := memLp_top_of_bound hφ_meas.aestronglyMeasurable C hφ_bdd
  refine ⟨hφ_mem.toLp φ, fun n ↦ Lp.ext ?_⟩
  set en := SimpleFunc.toLpTop μ ℂ
    (SimpleFunc.piecewise (spanningSets μ n) (measurableSet_spanningSets μ n)
      (1 : SimpleFunc α ℂ) 0)
  filter_upwards [coeFn_mul (hφ_mem.toLp φ) en, coeFn_mul (b n) en, hφ_mem.coeFn_toLp,
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) (measurableSet_spanningSets μ n), hcompat]
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
theorem exists_multiplicationOperator_eq_of_forall_commute_toLpTop_piecewise [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator
        (SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0)))) :
    ∃ a : Lp ℂ ∞ μ, multiplicationOperator (E := ℂ) a = T := by
  set E : ℕ → Set α := spanningSets μ
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_spanningSets μ n
  have hμE (n : ℕ) : μ (E n) ≠ ∞ := (measure_spanningSets_lt_top μ n).ne
  set e : ℕ → Lp ℂ ∞ μ := fun n ↦
    SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise (E n) (hE n) (1 : SimpleFunc α ℂ) 0)
  choose b hb_norm hb_eq using fun n : ℕ ↦
    exists_norm_le_and_comp_multiplicationOperator_toLpTop_piecewise_eq (hE n) (hμE n) T
      fun t ht hts ↦ hcomm ht ((measure_mono hts).trans_lt (hμE n).lt_top).ne
  have hcompat : ∀ᵐ x ∂μ, ∀ m n : ℕ, m ≤ n → x ∈ E m → b m x = b n x := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n
    by_cases hmn : m ≤ n
    · have hem : e n * e m = e m := by
        have hEmn : E n ∩ E m = E m := Set.inter_eq_right.mpr (monotone_spanningSets μ hmn)
        simp only [e, toLpTop_piecewise_one_zero_mul, hEmn]
      have hbm : multiplicationOperator (E := ℂ) (b m * e m) =
          multiplicationOperator (E := ℂ) (b n * e m) := by
        calc multiplicationOperator (E := ℂ) (b m * e m)
            = T ∘L multiplicationOperator (e m) := by
                rw [← multiplicationOperator_comp_multiplicationOperator, ← hb_eq m]
          _ = (T ∘L multiplicationOperator (e n)) ∘L multiplicationOperator (e m) := by
                rw [comp_assoc, multiplicationOperator_comp_multiplicationOperator, hem]
          _ = multiplicationOperator (E := ℂ) (b n * e m) := by
                rw [hb_eq n, comp_assoc, multiplicationOperator_comp_multiplicationOperator, hem,
                  multiplicationOperator_comp_multiplicationOperator]
      have hbe := multiplicationOperator_injective (E := ℂ) hbm
      filter_upwards [coeFn_mul (b m) (e m), (Lp.ext_iff.mp hbe).trans (coeFn_mul (b n) (e m)),
        coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) (hE m)] with x h₁ h₂ hind _ hxEm
      rw [Pi.mul_apply, hind, Set.indicator_of_mem hxEm, Pi.one_apply, mul_one] at h₁ h₂
      exact h₁.symm.trans h₂
    · exact ae_of_all _ fun _ hle ↦ (hmn hle).elim
  obtain ⟨a, hae⟩ := exists_mul_toLpTop_spanningSets_eq b hb_norm hcompat
  refine ⟨a, ContinuousLinearMap.ext fun f ↦ ?_⟩
  have hstep (n : ℕ) :
      multiplicationOperator a (multiplicationOperator (e n) f) =
        T (multiplicationOperator (e n) f) := by
    change (multiplicationOperator a ∘L multiplicationOperator (e n)) f =
      (T ∘L multiplicationOperator (e n)) f
    rw [hb_eq n, multiplicationOperator_comp_multiplicationOperator,
      multiplicationOperator_comp_multiplicationOperator, hae n]
  have htend := tendsto_multiplicationOperator_toLpTop_piecewise_spanningSets f
  exact tendsto_nhds_unique (((multiplicationOperator a).continuous.tendsto f).comp htend)
    (((T.continuous.tendsto f).comp htend).congr fun n ↦ (hstep n).symm)

/-- On a sigma-finite measure space, the centralizer in `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` of the range of
`multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] :
    (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (E := ℂ) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_toLpTop_piecewise T fun s hs _ ↦
      (commute_iff_eq _ _).mpr
        (hT _ ⟨SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0), rfl⟩).symm
  · rintro ⟨a, rfl⟩ S ⟨b, rfl⟩
    exact (commute_iff_eq _ _).mp (commute_multiplicationOperator b a)

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

/-- An `L∞` symbol supported on a finite-measure measurable set `s` whose multiplication operator
on `Lp ℂ 2 μ` vanishes is zero in `Lp ℂ ∞ μ` (with no `SigmaFinite` hypothesis on `μ`). -/
theorem eq_zero_of_mul_toLpTop_piecewise_eq_self_of_multiplicationOperator_eq_zero
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {a : Lp ℂ ∞ μ}
    (hsupp : a * SimpleFunc.toLpTop μ ℂ (SimpleFunc.piecewise s hs (1 : SimpleFunc α ℂ) 0) = a)
    (hzero : multiplicationOperator (E := ℂ) a = 0) : a = 0 := by
  have happly : multiplicationOperator (E := ℂ) a (indicatorConstLp 2 hs hμs (1 : ℂ)) = 0 := by
    rw [hzero, zero_apply]
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [(Lp.ext_iff.mp hsupp.symm).trans (Lp.coeFn_mul a _),
    coeFn_toLpTop_piecewise_one_zero (μ := μ) (R := ℂ) hs,
    (multiplicationOperator_ae a (indicatorConstLp 2 hs hμs (1 : ℂ))).symm.trans
      ((Lp.ext_iff.mp happly).trans (Lp.coeFn_zero ℂ 2 μ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))]
    with x hmul hsx h0 hind
  by_cases hxs : x ∈ s <;> simp_all

end Commutant

end MeasureTheory.Lp

