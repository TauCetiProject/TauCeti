/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# Multiplication by bounded operator fields on `Lᵖ`

Let `X` be a topological space with a Borel measure `μ` that is inner regular with respect to
compact sets on sets of finite measure, for instance the Haar measure `MeasureTheory.Measure.haar`
of a locally compact group. A uniformly bounded operator field acts on `Lᵖ` by
`MeasureTheory.Lp.mulStrong` when each fixed-vector evaluation is continuous. In particular,
a bounded continuous function `F : X →ᵇ (E →L[𝕜] E')` acts on
`Lᵖ(X, E)`, for `1 ≤ p < ∞`, by pointwise application, `f ↦ (x ↦ F x (f x))`. This file bundles
that action as `BoundedContinuousFunction.mulLp F μ p hp`, a bounded operator of norm at most
`‖F‖`. When `p = 2` and `E = E' = H` is a Hilbert space, `F ↦ F.mulLp μ 2 _` is a unital
⋆-homomorphism `BoundedContinuousFunction.mulL2StarAlgHom` from `X →ᵇ (H →L[𝕜] H)` to the bounded
operators on `L²(X, H)`. A symbol with unitary values gives a unitary operator
(`BoundedContinuousFunction.mulLp_mem_unitary`). These operators carry the coefficient
representation of the regular covariant representation of a C⋆-dynamical system on `L²(G, H)`.

The symbol is not regarded as an element of `L∞`: on a locally compact group that is not
σ-compact, a Haar measure is not σ-finite, and a continuous operator-valued function need not be
a.e. strongly measurable. Mathlib's Hölder multiplication `ContinuousLinearMap.holderL` therefore
does not apply. Each `f ∈ Lᵖ` with `p < ∞` vanishes outside a σ-finite set, however, and there
inner regularity makes `x ↦ F x (f x)` a.e. strongly measurable,
`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_apply_continuous`.
This is why `p = ∞` is excluded. For scalar symbols in `L∞`,
see `MeasureTheory.Lp.multiplicationOperator`.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {X 𝕜 E E' : Type*} [TopologicalSpace X] [MeasurableSpace X] [R1Space X] [BorelSpace X]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  (μ : Measure X) [μ.InnerRegularCompactLTTop] {p : ℝ≥0∞}

/-- A uniformly bounded, strongly continuous operator field acts pointwise on `Lᵖ`,
for `0 < p < ∞`. Strong continuity requires continuity after evaluation at each vector. -/
theorem memLp_mulStrong (F : X → E →L[𝕜] E') (hF : ∀ v, Continuous fun x ↦ F x v)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : Lp E p μ) :
    MemLp (fun x ↦ F x (f x)) p μ :=
  (Lp.memLp f).of_le_mul (c := C)
    (((Lp.memLp f).aefinStronglyMeasurable hp₀ hp).aestronglyMeasurable_apply_continuous hF
      (fun x ↦ (F x).continuous) (fun x ↦ map_zero (F x)))
    (.of_forall fun x ↦ (F x).le_of_opNorm_le (hC x) _)

variable [Fact (1 ≤ p)] in
/-- Pointwise multiplication by a uniformly bounded, strongly continuous operator field,
as a bounded linear map on `Lᵖ` for `1 ≤ p < ∞`. -/
def mulStrong (hp : p ≠ ∞) (F : X → E →L[𝕜] E') (hF : ∀ v, Continuous fun x ↦ F x v)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) : Lp E p μ →L[𝕜] Lp E' p μ :=
  let mem (f : Lp E p μ) := memLp_mulStrong μ F hF hC
    (zero_lt_one.trans_le Fact.out).ne' hp f
  LinearMap.mkContinuous
    { toFun f := (mem f).toLp _
      map_add' f g := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, map_add]
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, map_smul] }
    (max C 0) fun f ↦ Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [(mem f).coeFn_toLp] with x hx
      rw [LinearMap.coe_mk, AddHom.coe_mk, hx]
      exact (F x).le_of_opNorm_le ((hC x).trans (le_max_left _ _)) _

/-- Multiplication by a strongly continuous operator field acts by pointwise application
almost everywhere. -/
theorem coeFn_mulStrong [Fact (1 ≤ p)] (hp : p ≠ ∞) (F : X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun x ↦ F x v) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (f : Lp E p μ) :
    mulStrong μ hp F hF hC f =ᵐ[μ] fun x ↦ F x (f x) :=
  (memLp_mulStrong μ F hF hC (zero_lt_one.trans_le Fact.out).ne' hp f).coeFn_toLp

/-- The operator norm of multiplication is bounded by any nonnegative uniform bound on
the field. -/
theorem norm_mulStrong_le [Fact (1 ≤ p)] (hp : p ≠ ∞) (F : X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun x ↦ F x v) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    ‖mulStrong μ hp F hF hC‖ ≤ max C 0 := by
  unfold mulStrong
  exact LinearMap.mkContinuous_norm_le _ (le_max_right C 0) _

section Algebra

variable [Fact (1 ≤ p)] (hp : p ≠ ∞)

/-- The zero operator field acts as zero on `Lᵖ`. -/
@[simp]
theorem mulStrong_zero (h₀ : ∀ v, Continuous fun x ↦ (0 : X → E →L[𝕜] E') x v)
    {C : ℝ} (hC : ∀ x, ‖(0 : X → E →L[𝕜] E') x‖ ≤ C) :
    mulStrong μ hp (0 : X → E →L[𝕜] E') h₀ hC = 0 := by
  ext1 f
  refine Lp.ext ?_
  rw [_root_.zero_apply]
  filter_upwards [coeFn_mulStrong μ hp (0 : X → E →L[𝕜] E') h₀ hC f,
    Lp.coeFn_zero E' p μ] with x h₁ h₂
  rw [h₁, h₂]
  simp

/-- The constant identity field acts as the identity on `Lᵖ`. -/
@[simp]
theorem mulStrong_one (h₁ : ∀ v, Continuous fun x ↦ (1 : X → E →L[𝕜] E) x v)
    {C : ℝ} (hC : ∀ x, ‖(1 : X → E →L[𝕜] E) x‖ ≤ C) :
    mulStrong μ hp (1 : X → E →L[𝕜] E) h₁ hC = 1 := by
  ext1 f
  refine Lp.ext ?_
  simpa using coeFn_mulStrong μ hp (1 : X → E →L[𝕜] E) h₁ hC f

/-- The sum of two operator fields acts as the sum of their multiplication operators. -/
theorem mulStrong_add (F G : X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun x ↦ F x v) (hG : ∀ v, Continuous fun x ↦ G x v)
    (hFG : ∀ v, Continuous fun x ↦ (F + G) x v) {C D B : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) (hD : ∀ x, ‖G x‖ ≤ D) (hB : ∀ x, ‖(F + G) x‖ ≤ B) :
    mulStrong μ hp (F + G) hFG hB = mulStrong μ hp F hF hC + mulStrong μ hp G hG hD := by
  ext1 f
  refine Lp.ext ?_
  rw [_root_.add_apply]
  filter_upwards [coeFn_mulStrong μ hp _ hFG hB f, coeFn_mulStrong μ hp F hF hC f,
    coeFn_mulStrong μ hp G hG hD f, Lp.coeFn_add (mulStrong μ hp F hF hC f)
      (mulStrong μ hp G hG hD f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  simp [h₂, h₃]

/-- Scaling an operator field scales its multiplication operator by the same scalar. -/
theorem mulStrong_smul (c : 𝕜) (F : X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun x ↦ F x v) (hcF : ∀ v, Continuous fun x ↦ (c • F) x v)
    {C B : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (hB : ∀ x, ‖(c • F) x‖ ≤ B) :
    mulStrong μ hp (c • F) hcF hB = c • mulStrong μ hp F hF hC := by
  ext1 f
  refine Lp.ext ?_
  rw [_root_.smul_apply]
  filter_upwards [coeFn_mulStrong μ hp _ hcF hB f, coeFn_mulStrong μ hp F hF hC f,
    Lp.coeFn_smul c (mulStrong μ hp F hF hC f)] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

/-- Pointwise composition of operator fields acts by composing the multiplication operators
in the same order. -/
theorem mulStrong_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (F : X → E' →L[𝕜] E'') (G : X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun x ↦ F x v) (hG : ∀ v, Continuous fun x ↦ G x v)
    (hFG : ∀ v, Continuous fun x ↦ (F x).comp (G x) v) {C D B : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) (hD : ∀ x, ‖G x‖ ≤ D) (hB : ∀ x, ‖(F x).comp (G x)‖ ≤ B) :
    mulStrong μ hp (fun x ↦ (F x).comp (G x)) hFG hB =
      (mulStrong μ hp F hF hC).comp (mulStrong μ hp G hG hD) := by
  ext1 f
  refine Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [coeFn_mulStrong μ hp _ hFG hB f,
    coeFn_mulStrong μ hp F hF hC (mulStrong μ hp G hG hD f),
    coeFn_mulStrong μ hp G hG hD f] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃]

end Algebra

/-- Pointwise multiplication by a uniformly bounded family acts strongly continuously on
`Lᵖ` when the symbol is jointly continuous after evaluation at each fixed vector. The parameter
space can be arbitrary, so this also applies to nets in groups without a countability axiom. -/
theorem continuous_mulStrong_apply {Z : Type*} [TopologicalSpace Z]
    [WeaklyLocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [NormedSpace ℝ E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (F : Z → X → E →L[𝕜] E')
    (hF : ∀ v, Continuous fun q : Z × X ↦ F q.1 q.2 v)
    {C : ℝ} (hC : ∀ z x, ‖F z x‖ ≤ C) (ξ : Lp E p μ) :
    Continuous fun z ↦ mulStrong μ hp (F z)
      (fun v ↦ (hF v).comp (continuous_const.prodMk continuous_id)) (hC z) ξ := by
  let M (z : Z) := mulStrong μ hp (F z)
    (fun v ↦ (hF v).comp (continuous_const.prodMk continuous_id)) (hC z)
  have hM z (u : Lp E p μ) : M z u =ᵐ[μ] fun x ↦ F z x (u x) :=
    coeFn_mulStrong μ hp _ _ _ u
  refine ContinuousLinearMap.continuous_apply_of_dense
    (f := M) (Lp.dense_setOf_continuous_hasCompactSupport hp)
    (fun z ↦ norm_mulStrong_le μ hp _ _ (hC z)) ?_ ξ
  rintro u ⟨f, hfc, hfs, hu⟩
  have hcont : Continuous fun q : Z × X ↦ F q.1 q.2 (f q.2) :=
    AddMonoidHomClass.continuous_apply_of_bound hF
      (fun q v ↦ (F q.1 q.2).le_of_opNorm_le (hC q.1 q.2) v) (hfc.comp continuous_snd)
  refine continuous_iff_continuousAt.2 fun z₀ ↦ Metric.continuousAt_iff'.2 fun ε hε ↦ ?_
  let K := tsupport f
  have hK : IsCompact K := hfs
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  have hKμ : μ K ≠ ∞ := hK.measure_lt_top.ne
  let a := μ.real K ^ (1 / p.toReal)
  have ha : 0 ≤ a := Real.rpow_nonneg (measureReal_nonneg) _
  let δ := ε / (a + 1)
  have hδ : 0 < δ := div_pos hε (add_pos_of_nonneg_of_pos ha zero_lt_one)
  have hd : Continuous fun q : Z × X ↦ ‖F q.1 q.2 (f q.2) - F z₀ q.2 (f q.2)‖ :=
    (hcont.sub (hcont.comp (continuous_const.prodMk continuous_snd))).norm
  have hsmall : ∀ᶠ z in 𝓝 z₀, ∀ x ∈ K, ‖F z x (f x) - F z₀ x (f x)‖ < δ := by
    have he := hK.mem_prod_nhdsSet_of_forall
      (s := {q : Z × X | ‖F q.1 q.2 (f q.2) - F z₀ q.2 (f q.2)‖ < δ}) fun x _ ↦ by
        rw [← nhds_prod_eq]
        exact (hd.continuousAt (x := (z₀, x))).preimage_mem_nhds
          (Iio_mem_nhds (by simpa using hδ))
    exact (Filter.Eventually.curry he).mono fun _ hz ↦ hz.self_of_nhdsSet
  filter_upwards [hsmall] with z hz
  rw [_root_.dist_eq_norm]
  calc
    ‖M z u - M z₀ u‖ ≤ ‖indicatorConstLp p hKm hKμ δ‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [Lp.coeFn_sub (M z u) (M z₀ u), hM z u, hM z₀ u, hu,
        indicatorConstLp_coeFn (p := p) (hs := hKm) (hμs := hKμ) (c := δ)] with x hs hz' hz₀' hx hi
      rw [hs, Pi.sub_apply, hz', hz₀', hx, hi]
      by_cases hxK : x ∈ K
      · simpa [Set.indicator_of_mem hxK, Real.norm_of_nonneg hδ.le] using (hz x hxK).le
      · simp [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    _ = δ * a := by
      rw [norm_indicatorConstLp (zero_lt_one.trans_le Fact.out).ne' hp, Real.norm_of_nonneg hδ.le]
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < a + 1)]
      nlinarith

section Unitary

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A strongly continuous field of unitary operators acts unitarily on `L²`. -/
theorem mulStrong_mem_unitary (F : X → H →L[𝕜] H) (hF : ∀ v, Continuous fun x ↦ F x v)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (hU : ∀ x, F x ∈ unitary (H →L[𝕜] H)) :
    mulStrong (p := 2) μ ENNReal.ofNat_ne_top F hF hC ∈ unitary (Lp H 2 μ →L[𝕜] Lp H 2 μ) := by
  have hstar (v : H) : Continuous fun x ↦ star (F x) v := by
    refine continuous_iff_continuousAt.2 fun x ↦ Metric.continuousAt_iff'.2 fun ε hε ↦ ?_
    have h := (Metric.continuousAt_iff' (b := x)).1 (hF (star (F x) v)).continuousAt ε hε
    filter_upwards [h] with y hy
    let U : unitary (H →L[𝕜] H) := ⟨F y, hU y⟩
    have hUy : F y (star (F y) v) = v :=
      DFunLike.congr_fun (Unitary.mul_star_self_of_mem (hU y)) v
    have hUx : F x (star (F x) v) = v :=
      DFunLike.congr_fun (Unitary.mul_star_self_of_mem (hU x)) v
    have hisom : Isometry (F y) := (Unitary.linearIsometryEquiv U).isometry
    rw [← hisom.dist_eq, hUy, dist_comm]
    simpa only [hUx] using hy
  let T := mulStrong (p := 2) μ ENNReal.ofNat_ne_top F hF hC
  let S := mulStrong (p := 2) μ ENNReal.ofNat_ne_top (fun x ↦ star (F x)) hstar
    (fun x ↦ by simpa only [norm_star] using hC x)
  have hS (f : Lp H 2 μ) : S f =ᵐ[μ] fun x ↦ star (F x) (f x) :=
    coeFn_mulStrong μ ENNReal.ofNat_ne_top _ _ _ f
  have hT (f : Lp H 2 μ) : T f =ᵐ[μ] fun x ↦ F x (f x) :=
    coeFn_mulStrong μ ENNReal.ofNat_ne_top _ _ _ f
  have hadj : S = star T := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hS f, hT g] with x hx hy
    rw [hx, hy, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩
  · rw [← hadj]
    ext1 f
    refine Lp.ext ?_
    filter_upwards [hS (T f), hT f] with x hx hy
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, hx, hy, ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.mul_def, Unitary.star_mul_self_of_mem (hU x),
      one_apply_eq_self]
  · rw [← hadj]
    ext1 f
    refine Lp.ext ?_
    filter_upwards [hT (S f), hS f] with x hx hy
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, hx, hy, ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.mul_def, Unitary.mul_star_self_of_mem (hU x),
      one_apply_eq_self]

end Unitary

end MeasureTheory.Lp

namespace BoundedContinuousFunction

variable {X 𝕜 E E' : Type*} [TopologicalSpace X] [MeasurableSpace X] [R1Space X] [BorelSpace X]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {μ : Measure X} [μ.InnerRegularCompactLTTop]

/-- Pointwise application of a bounded continuous operator-valued function to an `Lᵖ` function,
`x ↦ F x (f x)`, is again in `Lᵖ` for `0 < p < ∞`. -/
theorem memLp_apply (F : X →ᵇ (E →L[𝕜] E')) {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp E p μ) : MemLp (fun x ↦ F x (f x)) p μ :=
  Lp.memLp_mulStrong μ F (fun v ↦ F.continuous.clm_apply (continuous_const (y := v)))
    F.norm_coe_le_norm hp₀ hp f

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)

variable (μ p) in
/-- Pointwise application of a bounded continuous operator-valued function `F`, as a bounded
operator `f ↦ (x ↦ F x (f x))` from `Lᵖ(X, E)` to `Lᵖ(X, E')` for `1 ≤ p < ∞`. -/
def mulLp (F : X →ᵇ (E →L[𝕜] E')) : Lp E p μ →L[𝕜] Lp E' p μ :=
  Lp.mulStrong μ hp F (fun v ↦ F.continuous.clm_apply (continuous_const (y := v)))
    F.norm_coe_le_norm

/-- The multiplication operator acts by pointwise application almost everywhere. -/
theorem coeFn_mulLp (F : X →ᵇ (E →L[𝕜] E')) (f : Lp E p μ) :
    F.mulLp μ p hp f =ᵐ[μ] fun x ↦ F x (f x) :=
  Lp.coeFn_mulStrong μ hp F (fun v ↦ F.continuous.clm_apply (continuous_const (y := v)))
    F.norm_coe_le_norm f

variable {hp}

/-- Multiplication operators are determined by their pointwise action: an `Lᵖ` class equal almost
everywhere to `x ↦ F x (f x)` is `F.mulLp μ p hp f`. -/
theorem mulLp_eq_iff {F : X →ᵇ (E →L[𝕜] E')} {f : Lp E p μ} {g : Lp E' p μ} :
    F.mulLp μ p hp f = g ↔ (fun x ↦ F x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (F.coeFn_mulLp hp f).symm, fun h ↦ Lp.ext ((F.coeFn_mulLp hp f).trans h)⟩

/-- The operator norm of a multiplication operator is at most the supremum norm of its symbol. -/
theorem norm_mulLp_le (F : X →ᵇ (E →L[𝕜] E')) : ‖F.mulLp μ p hp‖ ≤ ‖F‖ :=
  (Lp.norm_mulStrong_le μ hp F (fun v ↦ F.continuous.clm_apply (continuous_const (y := v)))
    F.norm_coe_le_norm).trans_eq (max_eq_left (norm_nonneg F))

@[simp]
theorem mulLp_zero : (0 : X →ᵇ (E →L[𝕜] E')).mulLp μ p hp = 0 := by
  unfold mulLp
  exact Lp.mulStrong_zero μ hp _ _

@[simp]
theorem mulLp_add (F G : X →ᵇ (E →L[𝕜] E')) :
    (F + G).mulLp μ p hp = F.mulLp μ p hp + G.mulLp μ p hp := by
  unfold mulLp
  exact Lp.mulStrong_add μ hp F G _ _ _ _ _ _

@[simp]
theorem mulLp_smul (c : 𝕜) (F : X →ᵇ (E →L[𝕜] E')) :
    (c • F).mulLp μ p hp = c • F.mulLp μ p hp := by
  unfold mulLp
  exact Lp.mulStrong_smul μ hp c F _ _ _ _

/-- Multiplication by the constant identity function is the identity operator. -/
@[simp]
theorem mulLp_one : (1 : X →ᵇ (E →L[𝕜] E)).mulLp μ p hp = 1 := by
  unfold mulLp
  exact Lp.mulStrong_one μ hp _ _

/-- Multiplication operators compose by pointwise composition of their symbols. -/
@[simp]
theorem mulLp_mul (F G : X →ᵇ (E →L[𝕜] E)) :
    (F * G).mulLp μ p hp = F.mulLp μ p hp * G.mulLp μ p hp := by
  unfold mulLp
  rw [ContinuousLinearMap.mul_def]
  exact Lp.mulStrong_comp μ hp F G _ _ _ _ _ _

end Lp

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The adjoint of multiplication by `F` is multiplication by the pointwise adjoint `star F`. -/
@[simp]
theorem adjoint_mulLp (F : X →ᵇ (H →L[𝕜] H)) :
    ContinuousLinearMap.adjoint (F.mulLp μ 2 ENNReal.ofNat_ne_top) =
      (star F).mulLp μ 2 ENNReal.ofNat_ne_top := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(star F).coeFn_mulLp ENNReal.ofNat_ne_top f,
    F.coeFn_mulLp ENNReal.ofNat_ne_top g] with x hF hG
  simp [hF, hG, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

variable (μ) in
/-- Multiplication of `L²(X, H)` by bounded continuous operator-valued functions, as a unital
⋆-homomorphism into the bounded operators on `L²(X, H)`. -/
def mulL2StarAlgHom : (X →ᵇ (H →L[𝕜] H)) →⋆ₐ[𝕜] (Lp H 2 μ →L[𝕜] Lp H 2 μ) where
  toFun F := F.mulLp μ 2 ENNReal.ofNat_ne_top
  map_one' := mulLp_one
  map_mul' := mulLp_mul
  map_zero' := mulLp_zero
  map_add' := mulLp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mulLp_smul, mulLp_one]
  map_star' F := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mulLp]

@[simp]
theorem mulL2StarAlgHom_apply (F : X →ᵇ (H →L[𝕜] H)) :
    mulL2StarAlgHom μ F = F.mulLp μ 2 ENNReal.ofNat_ne_top :=
  (rfl)

/-- Multiplication by a bounded continuous function with unitary values is a unitary operator on
`L²(X, H)`, so `Unitary.linearIsometryEquiv` makes it a linear isometry equivalence. -/
theorem mulLp_mem_unitary {F : X →ᵇ (H →L[𝕜] H)} (hF : ∀ x, F x ∈ unitary (H →L[𝕜] H)) :
    F.mulLp μ 2 ENNReal.ofNat_ne_top ∈ unitary (Lp H 2 μ →L[𝕜] Lp H 2 μ) :=
  Lp.mulStrong_mem_unitary μ F (fun v ↦ F.continuous.clm_apply (continuous_const (y := v)))
    F.norm_coe_le_norm hF

end Hilbert

end BoundedContinuousFunction
