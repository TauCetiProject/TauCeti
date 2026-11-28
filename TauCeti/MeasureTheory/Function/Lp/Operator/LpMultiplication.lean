/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
public import TauCeti.MeasureTheory.Function.Lp.Linfty.Algebra
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Operator-valued `L∞` multiplication operators on `Lᵖ`

An essentially bounded operator-valued function `A : Lp (E →L[𝕜] F) ∞ μ` acts on `Lp E p μ`
(`1 ≤ p ≤ ∞`) by `x ↦ A x (f x)`. This file bundles that action as
`MeasureTheory.Lp.operatorMultiplication p : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ`
via `(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p`, proving:
* `1`, `algebraMap`, and `A * B` laws (`operatorMultiplication_one`,
  `operatorMultiplication_algebraMap`, `operatorMultiplication_comp_operatorMultiplication`);
* multiplication by a field of maps with essentially bounded pointwise inverses is invertible
  (`isInvertible_operatorMultiplication_of_comp_eq_id`);
* the `L²` adjoint `adjoint_operatorMultiplication` and `operatorMultiplicationStarAlgHom`;
* more generally, for a continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G` into real Hilbert
  spaces, the `L²` adjoint of Hölder multiplication `f ↦ B(b, f)` by `b ∈ L^∞(μ; E)` is Hölder
  multiplication by the pointwise adjoints `B(b x, ·)†`, that is by `adjointRealCLM ∘L B`
  (`ContinuousLinearMap.adjoint_holderL_apply`);
* the symmetry `⟪A f, ι ∘ g⟫ = ⟪ι ∘ f, A g⟫` on `L²` for an `ι`-symmetric symbol `A`
  (`inner_operatorMultiplication_compLpL`, and `inner_compLpL_compLpL` for a constant one), and
  the skew-adjointness `⟪J ∘ f, g⟫ = -⟪f, J ∘ g⟫` for a skew-adjoint `J`
  (`inner_compLpL_eq_neg_inner_compLpL`);
* the `L²` adjoint of postcomposition by a bounded operator `L` between Hilbert spaces is
  postcomposition by `L†` (`ContinuousLinearMap.adjoint_compLpL`);
* `‖operatorMultiplication p A‖ = ‖A‖` and `isometry_operatorMultiplication` for `[SigmaFinite μ]`.

Multiplication by the indicator of a measurable set `s` is the operator
`MeasureTheory.Lp.indicatorMultiplication 𝕜 p hs` on `Lp E p μ`, built from
`TauCeti.linftyIndicator μ 𝕜 s hs` in scalar `L∞` (`indicatorMultiplication_apply`). It acts as
`f ↦ 1_s f` almost everywhere (`indicatorMultiplication_ae`, `indicatorMultiplication_eq_iff`,
`indicatorMultiplication_eq_self_of_ae_notMem`), agrees with restricting to `s` and extending
by zero (`TauCeti.castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM`), is the identity for `univ`,
zero for `∅` and composes by intersection (`indicatorMultiplication_comp_indicatorMultiplication`),
cut-offs to a set and its complement add up to the identity (`indicatorMultiplication_add_compl`),
it restricts constant indicator classes (`indicatorMultiplication_indicatorConstLp`), it is a
contraction (`norm_indicatorMultiplication_le`), the `Lʳ` seminorm of `1_s f` is that of `f` on `s`
(`eLpNorm_indicatorMultiplication`), cutoffs along shrinking sets with empty intersection tend to
zero (`tendsto_norm_indicatorMultiplication`), cutoffs along `spanningSets μ` on a `σ`-finite space
converge strongly to the identity (`tendsto_indicatorMultiplication_spanningSets`),
almost-everywhere equal sets induce equal operators (`indicatorMultiplication_congr`) and
conversely on finite-measure sets (`ae_eq_of_indicatorMultiplication_eq`,
`indicatorMultiplication_inj`), and it is self-adjoint on `L²`
(`inner_indicatorMultiplication_left`, `adjoint_indicatorMultiplication`).

Compare `MeasureTheory.Lp.multiplicationOperator` and `BoundedContinuousFunction.mulLp`.
-/

public noncomputable section

open ENNReal ContinuousLinearMap
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α 𝕜 E F G : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- Continuous bilinear map sending `(A, f)` to pointwise application `x ↦ A x (f x)`. -/
def operatorMultiplication : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ :=
  (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p

/-- `operatorMultiplication` acts by pointwise operator application almost everywhere. -/
theorem operatorMultiplication_ae (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p A f =ᵐ[μ] fun x ↦ A x (f x) := by
  simpa only [operatorMultiplication, holderL_apply_apply, id_apply] using
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).coeFn_holder (r := p) A f

/-- `operatorMultiplication` is characterized by its almost-everywhere pointwise action. -/
theorem operatorMultiplication_eq_iff {A : Lp (E →L[𝕜] F) ∞ μ} {f : Lp E p μ} {g : Lp F p μ} :
    operatorMultiplication p A f = g ↔ (fun x ↦ A x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (operatorMultiplication_ae A f).symm,
    fun h ↦ Lp.ext ((operatorMultiplication_ae A f).trans h)⟩

/-- The operator norm of `operatorMultiplication p A` is at most the `L∞` norm of `A`. -/
theorem norm_operatorMultiplication_le (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ ≤ ‖A‖ := by
  simpa only [operatorMultiplication, one_mul] using le_of_opNorm_le _
    ((norm_holderL_le (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F))).trans norm_id_le) A

/-- Applying `operatorMultiplication p A` changes the `Lᵖ` norm by at most `‖A‖`. -/
theorem norm_operatorMultiplication_apply_le (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    ‖operatorMultiplication p A f‖ ≤ ‖A‖ * ‖f‖ :=
  (operatorMultiplication p A).le_of_opNorm_le (norm_operatorMultiplication_le A) f

/-- `operatorMultiplication` commutes with heterogeneous `Lp` scalar multiplication on the right. -/
theorem operatorMultiplication_lpSMul_right {q r : ℝ≥0∞} [Fact (1 ≤ r)] [HolderTriple q p r]
    (a : Lp 𝕜 q μ) (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication r A (a • f : Lp E r μ) =
      (a • operatorMultiplication p A f : Lp F r μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae (p := r) A (a • f : Lp E r μ),
    Lp.coeFn_lpSMul (r := r) a f, Lp.coeFn_lpSMul (r := r) a (operatorMultiplication p A f),
    operatorMultiplication_ae (p := p) A f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', map_smul, h₄]

/-- Multiplying the operator symbol on the left by an `L∞` scalar function scales the output. -/
theorem operatorMultiplication_lpSMul_left (a : Lp 𝕜 ∞ μ) (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p (a • A : Lp (E →L[𝕜] F) ∞ μ) f =
      (a • operatorMultiplication p A f : Lp F p μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae (a • A : Lp (E →L[𝕜] F) ∞ μ) f,
    Lp.coeFn_lpSMul (r := ∞) a A, Lp.coeFn_lpSMul (r := p) a (operatorMultiplication p A f),
    operatorMultiplication_ae A f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', smul_apply, h₄]

/-- A symbol equal almost everywhere to a constant `T : E →L[𝕜] F` acts as `T.compLpL`. -/
theorem operatorMultiplication_of_ae_eq_const {A : Lp (E →L[𝕜] F) ∞ μ} {T : E →L[𝕜] F}
    (hA : A =ᵐ[μ] fun _ ↦ T) : operatorMultiplication p A = T.compLpL p μ := by
  ext1 f; rw [operatorMultiplication_eq_iff]
  filter_upwards [hA, T.coeFn_compLpL f] with x hx hT; rw [hx, hT]

/-- On a finite measure space, a constant continuous linear map `T` in `L∞` acts as `T.compLpL`. -/
@[simp] theorem operatorMultiplication_const [IsFiniteMeasure μ] (T : E →L[𝕜] F) :
    operatorMultiplication p (Lp.const ∞ μ T) = T.compLpL p μ :=
  operatorMultiplication_of_ae_eq_const (Lp.coeFn_const ∞ μ T)

/-- The identity symbol `1 : Lp (E →L[𝕜] E) ∞ μ` acts as the identity operator on `Lp E p μ`. -/
@[simp] theorem operatorMultiplication_one :
    operatorMultiplication p (1 : Lp (E →L[𝕜] E) ∞ μ) = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f; rw [operatorMultiplication_eq_iff, id_apply]
  filter_upwards [Lp.coeFn_one (E := E →L[𝕜] E) (μ := μ)] with x hx; simp [hx]

/-- Scalar multiples of the identity symbol via `algebraMap` act by scalar multiplication. -/
@[simp] theorem operatorMultiplication_algebraMap (c : 𝕜) :
    operatorMultiplication p (algebraMap 𝕜 (Lp (E →L[𝕜] E) ∞ μ) c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, operatorMultiplication_one]

/-- Heterogeneous composition of operator-valued `L∞` multipliers via `compL.holderL`. -/
theorem operatorMultiplication_comp_eq_operatorMultiplication_compL_holderL
    (A : Lp (F →L[𝕜] G) ∞ μ) (B : Lp (E →L[𝕜] F) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p ((compL 𝕜 E F G).holderL μ ∞ ∞ ∞ A B) := by
  ext1 f; symm; rw [comp_apply, operatorMultiplication_eq_iff]
  filter_upwards [(compL 𝕜 E F G).coeFn_holder (r := ∞) A B,
    operatorMultiplication_ae A (operatorMultiplication p B f), operatorMultiplication_ae B f]
    with x hAB hA hB
  rw [holderL_apply_apply, hAB, compL_apply, comp_apply, hA, hB]

/-- For endomorphism-valued `L∞` symbols, `compL.holderL` agrees with the ring product `A * B`. -/
theorem compL_holderL_eq_mul (A B : Lp (E →L[𝕜] E) ∞ μ) :
    (compL 𝕜 E E E).holderL μ ∞ ∞ ∞ A B = A * B := Lp.ext <| by
  filter_upwards [(compL 𝕜 E E E).coeFn_holder (r := ∞) A B, Lp.coeFn_mul A B] with x h₁ h₂
  rw [holderL_apply_apply, h₁, h₂, compL_apply, Pi.mul_apply, mul_def]

/-- Composing endomorphism-valued `L∞` multipliers multiplies their symbols in the same order. -/
theorem operatorMultiplication_comp_operatorMultiplication (A B : Lp (E →L[𝕜] E) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p (A * B) := by
  rw [operatorMultiplication_comp_eq_operatorMultiplication_compL_holderL, compL_holderL_eq_mul]

/-- Multiplication by an essentially bounded field `G` of maps, followed by multiplication by an
essentially bounded field `G'` with `G' x ∘ G x = id` almost everywhere, is the identity. -/
theorem operatorMultiplication_comp_operatorMultiplication_eq_id_of_comp_eq_id {G : α → E →L[𝕜] F}
    {G' : α → F →L[𝕜] E} (hG : MemLp G ∞ μ) (hG' : MemLp G' ∞ μ)
    (h : ∀ᵐ x ∂μ, G' x ∘L G x = ContinuousLinearMap.id 𝕜 E) :
    operatorMultiplication p (hG'.toLp G') ∘L operatorMultiplication p (hG.toLp G) =
      ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  filter_upwards [operatorMultiplication_ae (hG'.toLp G') (operatorMultiplication p (hG.toLp G) f),
    operatorMultiplication_ae (hG.toLp G) f, hG.coeFn_toLp, hG'.coeFn_toLp, h]
    with x h₁ h₂ h₃ h₄ h₅
  rw [comp_apply, h₁, h₂, h₃, h₄, ← comp_apply, h₅, id_apply, id_apply]

/-- Multiplication by an essentially bounded field `G` of maps whose pointwise inverses `G'` are
essentially bounded is invertible on `Lᵖ`. -/
theorem isInvertible_operatorMultiplication_of_comp_eq_id {G : α → E →L[𝕜] F}
    {G' : α → F →L[𝕜] E} (hG : MemLp G ∞ μ) (hG' : MemLp G' ∞ μ)
    (hG'G : ∀ᵐ x ∂μ, G' x ∘L G x = ContinuousLinearMap.id 𝕜 E)
    (hGG' : ∀ᵐ x ∂μ, G x ∘L G' x = ContinuousLinearMap.id 𝕜 F) :
    (operatorMultiplication p (hG.toLp G)).IsInvertible :=
  .of_inverse (operatorMultiplication_comp_operatorMultiplication_eq_id_of_comp_eq_id hG' hG hGG')
    (operatorMultiplication_comp_operatorMultiplication_eq_id_of_comp_eq_id hG hG' hG'G)

/-- On a σ-finite space, `‖operatorMultiplication p A‖ = ‖A‖` (`1 ≤ p ≤ ∞`). -/
@[simp] theorem norm_operatorMultiplication [SigmaFinite μ] (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ = ‖A‖ := by
  apply le_antisymm (norm_operatorMultiplication_le A); by_contra! hlt
  set c := (‖operatorMultiplication p A‖ + ‖A‖) / 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨u, t, ht, hts, hμt_pos, hμt_top⟩ :=
    exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top A hc0 (by linarith [hc_def, hlt])
  have hu_ne : u ≠ 0 := fun h ↦
    let ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hμt_pos.ne'; absurd (hts x₀ hx₀) (by simp [h])
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set f := indicatorConstLp p ht hμt_top.ne u
  set g := indicatorConstLp p ht hμt_top.ne (c * ‖u‖)
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne']
    exact mul_pos (norm_pos_iff.mpr hu_ne)
      (Real.rpow_pos_of_pos (ENNReal.toReal_pos hμt_pos.ne' hμt_top.ne) _)
  have hfg : c * ‖f‖ = ‖g‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne', norm_indicatorConstLp' hp0 hμt_pos.ne',
      Real.norm_of_nonneg (mul_nonneg hc0 (norm_nonneg u)), mul_assoc]
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖operatorMultiplication p A f x‖ := by
    filter_upwards [operatorMultiplication_ae (p := p) A f,
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := u),
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := c * ‖u‖)]
      with x hmul hf_ae hg_ae
    rw [hmul, hf_ae, hg_ae]; by_cases hx : x ∈ t
    · simpa [hx, Real.norm_of_nonneg (mul_nonneg hc0 (norm_nonneg u))] using (hts x hx).le
    · simp [hx]
  exact (not_le_of_gt (by linarith [hc_def, hlt] : ‖operatorMultiplication p A‖ < c))
    (le_of_mul_le_mul_right (hfg ▸ (Lp.norm_le_norm_of_ae_le hpoint).trans (le_opNorm _ _)) hf_pos)

/-- On a σ-finite measure space, `operatorMultiplication p` is an isometry. -/
theorem isometry_operatorMultiplication [SigmaFinite μ] :
    Isometry (operatorMultiplication p : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ) :=
  AddMonoidHomClass.isometry_of_norm _ norm_operatorMultiplication

end NormedSpace

section Indicator

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set α}

variable (𝕜 p) in
/-- Multiplication by the indicator of a measurable set `s`, as a bounded operator on `Lp E p μ`:
the Hölder product with `TauCeti.linftyIndicator μ 𝕜 s hs`. -/
def indicatorMultiplication (hs : MeasurableSet s) : Lp E p μ →L[𝕜] Lp E p μ :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜).holderL μ ∞ p p (TauCeti.linftyIndicator μ 𝕜 s hs)

/-- Applying `indicatorMultiplication` is heterogeneous `Lp` scalar multiplication by
`TauCeti.linftyIndicator μ 𝕜 s hs`. -/
theorem indicatorMultiplication_apply (hs : MeasurableSet s) (f : Lp E p μ) :
    indicatorMultiplication 𝕜 p hs f = TauCeti.linftyIndicator μ 𝕜 s hs • f := by
  rw [indicatorMultiplication, holderL_apply_apply, ContinuousLinearMap.holder_lsmul_eq_smul]

/-- `indicatorMultiplication` multiplies by the indicator of `s` almost everywhere. -/
theorem indicatorMultiplication_ae (hs : MeasurableSet s) (f : Lp E p μ) :
    indicatorMultiplication 𝕜 p hs f =ᵐ[μ] s.indicator f := by
  rw [indicatorMultiplication_apply]
  exact TauCeti.coeFn_linftyIndicator_smul hs f

/-- `indicatorMultiplication` is characterized by its almost-everywhere pointwise action. -/
theorem indicatorMultiplication_eq_iff {hs : MeasurableSet s} {f g : Lp E p μ} :
    indicatorMultiplication 𝕜 p hs f = g ↔ s.indicator f =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (indicatorMultiplication_ae hs f).symm,
    fun h ↦ Lp.ext ((indicatorMultiplication_ae hs f).trans h)⟩

/-- Almost-everywhere equal measurable sets induce the same indicator multiplication operator. -/
theorem indicatorMultiplication_congr {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s =ᵐ[μ] t) :
    indicatorMultiplication (E := E) (μ := μ) 𝕜 p hs =
      indicatorMultiplication (E := E) (μ := μ) 𝕜 p ht := by
  rw [indicatorMultiplication, indicatorMultiplication, (TauCeti.linftyIndicator_inj hs ht).mpr h]

/-- Multiplying an `Lᵖ` constant indicator of `t` by the indicator of `s` intersects the sets. -/
theorem indicatorMultiplication_indicatorConstLp {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (v : E) :
    indicatorMultiplication 𝕜 p hs (indicatorConstLp p ht hμt v) =
      indicatorConstLp p (hs.inter ht)
        (measure_ne_top_of_subset Set.inter_subset_right hμt) v := by
  rw [indicatorMultiplication_apply]
  exact TauCeti.linftyIndicator_smul_indicatorConstLp hs ht hμt v

/-- If `s ⊆ t`, multiplying an `Lᵖ` constant indicator of `t` by the indicator of `s` restricts
it to `s`. -/
theorem indicatorMultiplication_indicatorConstLp_of_subset {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (hst : s ⊆ t) (v : E) :
    indicatorMultiplication 𝕜 p hs (indicatorConstLp p ht hμt v) =
      indicatorConstLp p hs (measure_ne_top_of_subset hst hμt) v := by
  rw [indicatorMultiplication_indicatorConstLp]
  simp [Set.inter_eq_left.mpr hst]

/-- Multiplying an `Lᵖ` constant indicator of `s` by the indicator of `s` fixes it. -/
@[simp] theorem indicatorMultiplication_indicatorConstLp_self (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (v : E) :
    indicatorMultiplication 𝕜 p hs (indicatorConstLp p hs hμs v) = indicatorConstLp p hs hμs v :=
  indicatorMultiplication_indicatorConstLp_of_subset hs hs hμs Set.Subset.rfl v

/-- If two finite-measure measurable sets induce the same indicator multiplication operator on
`Lp E p μ` (for a nontrivial space `E`), then the two sets agree almost everywhere (with no
`SigmaFinite` hypothesis on `μ`). -/
theorem ae_eq_of_indicatorMultiplication_eq [Nontrivial E] {t : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (h : indicatorMultiplication (E := E) (μ := μ) 𝕜 p hs =
      indicatorMultiplication (E := E) (μ := μ) 𝕜 p ht) :
    s =ᵐ[μ] t := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hmem_of {u w : Set α} (hu : MeasurableSet u) (hμu : μ u ≠ ∞) (hw : MeasurableSet w)
      (heq : indicatorMultiplication (E := E) (μ := μ) 𝕜 p hu =
        indicatorMultiplication (E := E) (μ := μ) 𝕜 p hw) :
      ∀ᵐ x ∂μ, x ∈ u → x ∈ w := by
    have happly : indicatorConstLp p hu hμu v =
        indicatorConstLp p (hw.inter hu)
          (measure_ne_top_of_subset Set.inter_subset_right hμu) v := by
      have happly' :=
        congrArg (fun T : Lp E p μ →L[𝕜] Lp E p μ ↦ T (indicatorConstLp p hu hμu v)) heq
      simpa only [indicatorMultiplication_indicatorConstLp_self,
        indicatorMultiplication_indicatorConstLp] using happly'
    filter_upwards [Lp.ext_iff.mp happly,
      indicatorConstLp_coeFn (p := p) (hs := hu) (hμs := hμu) (c := v),
      indicatorConstLp_coeFn (p := p) (hs := hw.inter hu)
        (hμs := measure_ne_top_of_subset Set.inter_subset_right hμu) (c := v)]
      with x hxe hxu hxwu hmem
    rw [hxu, Set.indicator_of_mem hmem] at hxe
    rw [hxwu] at hxe
    by_contra hnot
    rw [Set.indicator_of_notMem fun (h' : x ∈ w ∩ u) ↦ hnot h'.1] at hxe
    exact hv hxe
  filter_upwards [hmem_of hs hμs ht h, hmem_of ht hμt hs h.symm] with x hst hts
  exact ⟨hst, hts⟩

/-- Two finite-measure measurable sets induce the same indicator multiplication operator on
`Lp E p μ` (for a nontrivial space `E`) if and only if they agree almost everywhere. -/
theorem indicatorMultiplication_inj [Nontrivial E] {t : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) :
    indicatorMultiplication (E := E) (μ := μ) 𝕜 p hs =
      indicatorMultiplication (E := E) (μ := μ) 𝕜 p ht ↔ s =ᵐ[μ] t :=
  ⟨ae_eq_of_indicatorMultiplication_eq hs hμs ht hμt, indicatorMultiplication_congr hs ht⟩

/-- If `f` vanishes almost everywhere outside `s`, then `indicatorMultiplication 𝕜 p hs f = f`. -/
theorem indicatorMultiplication_eq_self_of_ae_notMem (hs : MeasurableSet s) {f : Lp E p μ}
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    indicatorMultiplication 𝕜 p hs f = f := by
  refine indicatorMultiplication_eq_iff.mpr ?_
  filter_upwards [hf] with x hfx
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs, hfx hxs]

/-- Restricting an `Lᵖ` class to a measurable set `s` and extending back by zero to the whole
space equals `MeasureTheory.Lp.indicatorMultiplication 𝕜 p hs`. -/
theorem _root_.TauCeti.castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM {s : Set α}
    (hs : MeasurableSet s) (f : Lp E p μ) :
    TauCeti.castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s)
        (LpToLpRestrictCLM α E 𝕜 μ p s f)) =
      indicatorMultiplication 𝕜 p hs f := by
  refine Lp.ext ((TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 hs.nullMeasurableSet _).trans ?_)
  filter_upwards [(ae_restrict_iff' hs).mp (LpToLpRestrictCLM_coeFn 𝕜 s f),
    (indicatorMultiplication_ae (𝕜 := 𝕜) hs f).symm] with x hxR hind
  rw [← hind]
  by_cases hxs : x ∈ s
  · simp [hxs, hxR hxs]
  · simp [hxs]

/-- Commuting with `indicatorMultiplication` commutes its action on `Lp` functions. -/
theorem _root_.Commute.indicatorMultiplication_apply {T : Lp E p μ →L[𝕜] Lp E p μ}
    {hs : MeasurableSet s} (h : Commute T (indicatorMultiplication 𝕜 p hs)) (f : Lp E p μ) :
    T (indicatorMultiplication 𝕜 p hs f) = indicatorMultiplication 𝕜 p hs (T f) := by
  simpa only [mul_apply_eq_comp] using congr($h.eq f)

/-- Multiplication by the indicator of the whole space is the identity. -/
@[simp] theorem indicatorMultiplication_univ :
    indicatorMultiplication 𝕜 p MeasurableSet.univ = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f; rw [indicatorMultiplication_eq_iff, Set.indicator_univ, id_apply]

/-- Multiplication by the indicator of the empty set is zero. -/
@[simp] theorem indicatorMultiplication_empty :
    indicatorMultiplication 𝕜 p MeasurableSet.empty = (0 : Lp E p μ →L[𝕜] Lp E p μ) := by
  ext1 f; rw [indicatorMultiplication_eq_iff, Set.indicator_empty, zero_apply]
  exact (Lp.coeFn_zero E p μ).symm

/-- Composing indicator multiplications multiplies by the indicator of the intersection. -/
theorem indicatorMultiplication_comp_indicatorMultiplication {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    indicatorMultiplication 𝕜 p hs ∘L indicatorMultiplication 𝕜 p ht =
      (indicatorMultiplication 𝕜 p (hs.inter ht) : Lp E p μ →L[𝕜] Lp E p μ) := by
  ext1 f; rw [comp_apply, indicatorMultiplication_eq_iff]
  filter_upwards [indicatorMultiplication_ae (𝕜 := 𝕜) ht f,
    indicatorMultiplication_ae (𝕜 := 𝕜) (hs.inter ht) f] with x hx hst
  rw [hst, ← Set.indicator_indicator]
  by_cases hxs : x ∈ s <;> simp [hxs, hx]

/-- The cut-offs of an `Lᵖ` class to a measurable set and to its complement add up to the class. -/
theorem indicatorMultiplication_add_compl (hs : MeasurableSet s) (f : Lp E p μ) :
    indicatorMultiplication 𝕜 p hs f + indicatorMultiplication 𝕜 p hs.compl f = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (indicatorMultiplication 𝕜 p hs f)
      (indicatorMultiplication 𝕜 p hs.compl f),
    indicatorMultiplication_ae (𝕜 := 𝕜) hs f,
    indicatorMultiplication_ae (𝕜 := 𝕜) hs.compl f] with x hx h₁ h₂
  rw [hx, Pi.add_apply, h₁, h₂, Set.indicator_self_add_compl_apply]

/-- Applying `indicatorMultiplication` does not increase the `Lᵖ` norm. -/
theorem norm_indicatorMultiplication_apply_le (hs : MeasurableSet s) (f : Lp E p μ) :
    ‖indicatorMultiplication 𝕜 p hs f‖ ≤ ‖f‖ :=
  Lp.norm_le_norm_of_ae_le <| by
    filter_upwards [indicatorMultiplication_ae (𝕜 := 𝕜) hs f] with x hx
    rw [hx]; exact norm_indicator_le_norm_self _ _

/-- `indicatorMultiplication` is a contraction: its operator norm is at most `1`. -/
theorem norm_indicatorMultiplication_le (hs : MeasurableSet s) :
    ‖(indicatorMultiplication 𝕜 p hs : Lp E p μ →L[𝕜] Lp E p μ)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [one_mul] using norm_indicatorMultiplication_apply_le hs f

/-- The `Lʳ` seminorm of `1_s f` is the `Lʳ` seminorm of `f` on `s`, for every exponent `r`. -/
@[simp] theorem eLpNorm_indicatorMultiplication (hs : MeasurableSet s) (f : Lp E p μ) (r : ℝ≥0∞) :
    eLpNorm (indicatorMultiplication 𝕜 p hs f) r μ = eLpNorm f r (μ.restrict s) := by
  rw [eLpNorm_congr_ae (indicatorMultiplication_ae hs f),
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]

open Filter Topology in
/-- **Cut-offs to shrinking sets.** Cutting an `Lᵖ` class, `p < ∞`, off to the sets of a decreasing
family with empty intersection gives classes whose norms tend to zero: the `p`-th powers of the
norms are the measures of the sets for the finite measure `‖f‖ᵖ μ`. -/
theorem tendsto_norm_indicatorMultiplication {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] (hp : p ≠ ∞) {s : ι → Set α}
    (hs : ∀ i, MeasurableSet (s i)) (hanti : Antitone s) (hempty : ⋂ i, s i = ∅)
    (f : Lp E p μ) :
    Tendsto (fun i ↦ ‖indicatorMultiplication 𝕜 p (hs i) f‖) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [atTop.filter_eq_bot_of_isEmpty]
    exact tendsto_bot
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hpos : 0 < 1 / p.toReal := one_div_pos.2 (ENNReal.toReal_pos hp0 hp)
  -- The `p`-th powers of the norms are the measures of the sets for `‖f‖ᵖ μ`.
  set ν := μ.withDensity fun x ↦ ‖f x‖ₑ ^ p.toReal
  have hν (i : ι) :
      ‖indicatorMultiplication 𝕜 p (hs i) f‖ = (ν (s i) ^ (1 / p.toReal)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (indicatorMultiplication_ae (hs i) f),
      eLpNorm_indicator_eq_eLpNorm_restrict (hs i).nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (Lp.aestronglyMeasurable f).restrict,
      withDensity_apply _ (hs i)]
  have hfin : ν (s i₀) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ _))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp (Lp.eLpNorm_lt_top f)).ne
  have h := tendsto_measure_iInter_atTop (μ := ν) (fun i ↦ (hs i).nullMeasurableSet) hanti
    ⟨i₀, hfin⟩
  rw [hempty, measure_empty] at h
  have h' := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos hpos] at h'
  simp only [hν]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h'

open Filter Topology in
/-- On a sigma-finite measure space and for `p < ∞`, the indicator multiplications along
`spanningSets μ` converge strongly to the identity on `Lp E p μ`. -/
theorem tendsto_indicatorMultiplication_spanningSets [SigmaFinite μ] (hp : p ≠ ∞)
    (f : Lp E p μ) :
    Tendsto (fun n ↦ indicatorMultiplication 𝕜 p (measurableSet_spanningSets μ n) f)
      atTop (𝓝 f) := by
  have hmem (n : ℕ) : MemLp ((spanningSets μ n).indicator ⇑f) p μ :=
    (Lp.memLp f).indicator (measurableSet_spanningSets μ n).nullMeasurableSet
  have heq (n : ℕ) : indicatorMultiplication 𝕜 p (measurableSet_spanningSets μ n) f =
      (hmem n).toLp _ :=
    Lp.ext <| (indicatorMultiplication_ae (measurableSet_spanningSets μ n) f).trans
      (hmem n).coeFn_toLp.symm
  simp_rw [heq]
  refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le hp hmem
    EventuallyEq.rfl (fun n ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
  refine .of_forall fun x ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_mem_spanningSets μ x] with n hn
  exact (Set.indicator_of_mem hn _).symm

end Indicator

section InnerProductSpace

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {s : Set α}

/-- Multiplication by an indicator is symmetric on `L²`. -/
theorem inner_indicatorMultiplication_left (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    ⟪indicatorMultiplication 𝕜 2 hs f, g⟫_𝕜 = ⟪f, indicatorMultiplication 𝕜 2 hs g⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [indicatorMultiplication_ae (𝕜 := 𝕜) hs f,
    indicatorMultiplication_ae (𝕜 := 𝕜) hs g] with x hf hg
  by_cases hx : x ∈ s <;> simp [hf, hg, hx]

/-- Postcomposition by a skew-adjoint operator `J` (`⟪J u, v⟫ = -⟪u, J v⟫`) is skew-adjoint on
`L²`: `⟪J ∘ f, g⟫ = -⟪f, J ∘ g⟫`. -/
theorem inner_compLpL_eq_neg_inner_compLpL {J : E →L[𝕜] E}
    (hJ : ∀ u v : E, ⟪J u, v⟫_𝕜 = -⟪u, J v⟫_𝕜) (f g : Lp E 2 μ) :
    ⟪J.compLpL 2 μ f, g⟫_𝕜 = -⟪f, J.compLpL 2 μ g⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [J.coeFn_compLpL f, J.coeFn_compLpL g] with x hf hg
  rw [hf, hg, hJ]

end InnerProductSpace

section Symmetric

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] {ι : E →L[𝕜] F}

/-- If `A x` is `ι`-symmetric (`⟪A x u, ι v⟫ = ⟪ι u, A x v⟫`) for almost every `x`, multiplication
by `A` is symmetric for the pairing of `A f` with `ι ∘ g` in `L²`:
`⟪A f, ι ∘ g⟫ = ⟪ι ∘ f, A g⟫`. -/
theorem inner_operatorMultiplication_compLpL {A : Lp (E →L[𝕜] F) ∞ μ}
    (hA : ∀ᵐ x ∂μ, ∀ u v : E, ⟪A x u, ι v⟫_𝕜 = ⟪ι u, A x v⟫_𝕜) (f g : Lp E 2 μ) :
    ⟪operatorMultiplication 2 A f, ι.compLpL 2 μ g⟫_𝕜 =
      ⟪ι.compLpL 2 μ f, operatorMultiplication 2 A g⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [operatorMultiplication_ae A f, operatorMultiplication_ae A g,
    ι.coeFn_compLpL f, ι.coeFn_compLpL g, hA] with x hf hg hιf hιg hx
  rw [hf, hg, hιf, hιg, hx]

/-- For an `ι`-symmetric `B` (`⟪B u, ι v⟫ = ⟪ι u, B v⟫`), postcomposition by `B` is symmetric for
the pairing of `B ∘ f` with `ι ∘ g` in `L²`: `⟪B ∘ f, ι ∘ g⟫ = ⟪ι ∘ f, B ∘ g⟫`. -/
theorem inner_compLpL_compLpL {B : E →L[𝕜] F} (hB : ∀ u v : E, ⟪B u, ι v⟫_𝕜 = ⟪ι u, B v⟫_𝕜)
    (f g : Lp E 2 μ) :
    ⟪B.compLpL 2 μ f, ι.compLpL 2 μ g⟫_𝕜 = ⟪ι.compLpL 2 μ f, B.compLpL 2 μ g⟫_𝕜 := by
  have hB' := (memLp_top_const (μ := μ) B).coeFn_toLp
  rw [← operatorMultiplication_of_ae_eq_const (p := 2) hB']
  exact inner_operatorMultiplication_compLpL (hB'.mono fun x hx ↦ hx ▸ hB) f g

end Symmetric

section Hilbert

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On Hilbert-valued `L²`, `(operatorMultiplication 2 A)† = operatorMultiplication 2 (star A)`. -/
@[simp] theorem adjoint_operatorMultiplication (A : Lp (E →L[𝕜] E) ∞ μ) :
    adjoint (operatorMultiplication 2 A) = operatorMultiplication 2 (star A) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]; refine integral_congr_ae ?_
  filter_upwards [operatorMultiplication_ae (p := 2) (star A) f,
    operatorMultiplication_ae (p := 2) A g, Lp.coeFn_star A] with x hf hg hA
  simp [hf, hg, hA, star_eq_adjoint, adjoint_inner_left]

/-- Multiplication by an indicator is self-adjoint on Hilbert-valued `L²`. -/
@[simp] theorem adjoint_indicatorMultiplication {s : Set α} (hs : MeasurableSet s) :
    adjoint (indicatorMultiplication 𝕜 2 hs : Lp E 2 μ →L[𝕜] Lp E 2 μ) =
      indicatorMultiplication 𝕜 2 hs :=
  ((eq_adjoint_iff _ _).2 (inner_indicatorMultiplication_left hs)).symm

/-- Multiplication by an indicator is a self-adjoint operator on Hilbert-valued `L²`. -/
theorem isSelfAdjoint_indicatorMultiplication {s : Set α} (hs : MeasurableSet s) :
    IsSelfAdjoint (indicatorMultiplication 𝕜 2 hs : Lp E 2 μ →L[𝕜] Lp E 2 μ) :=
  adjoint_indicatorMultiplication hs

variable (𝕜 E μ) in
/-- Pointwise operator multiplication on `L²(μ, E)` as a unital ⋆-algebra homomorphism. -/
def operatorMultiplicationStarAlgHom :
    Lp (E →L[𝕜] E) ∞ μ →⋆ₐ[𝕜] (Lp E 2 μ →L[𝕜] Lp E 2 μ) where
  toFun A := operatorMultiplication 2 A
  map_one' := by rw [operatorMultiplication_one, ← ContinuousLinearMap.one_def]
  map_mul' _ _ := by rw [← operatorMultiplication_comp_operatorMultiplication, mul_def]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := by
    rw [operatorMultiplication_algebraMap, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.one_def]
  map_star' _ := by rw [star_eq_adjoint, adjoint_operatorMultiplication]

/-- Evaluation of `operatorMultiplicationStarAlgHom` produces `operatorMultiplication 2`. -/
@[simp] theorem operatorMultiplicationStarAlgHom_apply (A : Lp (E →L[𝕜] E) ∞ μ) :
    operatorMultiplicationStarAlgHom 𝕜 E μ A = operatorMultiplication 2 A := (rfl)

end Hilbert

end MeasureTheory.Lp

namespace ContinuousLinearMap

open MeasureTheory

variable {α E F G : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- **The adjoint of a Hölder multiplication operator.** For a continuous bilinear map
`B : E →L[ℝ] F →L[ℝ] G` into real Hilbert spaces and `b ∈ L^∞(μ; E)`, the Hilbert space adjoint
of multiplication `f ↦ B(b, f)` from `L²(μ; F)` to `L²(μ; G)` is multiplication by the pointwise
adjoints `B(b x, ·)†`. -/
@[simp] theorem adjoint_holderL_apply (B : E →L[ℝ] F →L[ℝ] G) (b : Lp E ∞ μ) (h : Lp G 2 μ) :
    adjoint (B.holderL μ ∞ 2 2 b) h = (adjointRealCLM ∘L B).holderL μ ∞ 2 2 b h := by
  refine ext_inner_right ℝ fun f ↦ ?_
  rw [adjoint_inner_left, L2.inner_def, L2.inner_def, holderL_apply_apply, holderL_apply_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_holder (r := 2) B b f, coeFn_holder (r := 2) (adjointRealCLM ∘L B) b h]
    with x h₁ h₂
  rw [h₁, h₂, comp_apply, adjointRealCLM_apply, adjoint_inner_left]

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The adjoint of a postcomposition operator.** For a bounded operator `L : E →L[𝕜] F`
between Hilbert spaces, the Hilbert space adjoint of postcomposition `f ↦ L ∘ f` from `L²(μ; E)`
to `L²(μ; F)` is postcomposition by the adjoint `L†`. -/
@[simp] theorem adjoint_compLpL (L : E →L[𝕜] F) :
    adjoint (L.compLpL 2 μ) = (adjoint L).compLpL 2 μ := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(adjoint L).coeFn_compLpL f, L.coeFn_compLpL g] with x hf hg
  rw [hf, hg, adjoint_inner_left]

end ContinuousLinearMap
