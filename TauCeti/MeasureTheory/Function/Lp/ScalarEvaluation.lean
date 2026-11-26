/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# The scalar-evaluation operator of a Banach-valued function

Let `f : S → X` be a function into a normed space, and let a Banach space `Y` act on `X` by
continuous linear functionals through `ι : Y →L[𝕜] StrongDual 𝕜 X`: for instance the dual itself
with `ι` the identity, or, for `X` a dual space, a predual through its canonical embedding into
the bidual. When every scalar test `s ↦ ι y (f s)` lies in `Lᵖ(μ)`, the map `y ↦ [ι y ∘ f]` is
linear, and the closed graph theorem shows it is bounded:
`TauCeti.scalarEvalLp f ι hf : Y →L[𝕜] Lp 𝕜 p μ`. No measurability of `f` is assumed. This
operator is the starting point of weak (Dunford and Pettis) integration, where integrating its
values against scalar test functions produces functionals on `Y`.

The file records the value of the operator at each test through its `Lᵖ` class
(`TauCeti.scalarEvalLp_apply_eq_iff`), its invariance under almost-everywhere equality of the
scalar tests, its linearity in `f`, the change of tests along a bounded linear map and
compatibility with bounded linear maps on `X` through their adjoints. For `f ∈ Lᵖ(μ; X)` its norm
is at most `‖ι‖ ‖f‖_p` (`TauCeti.norm_scalarEvalLp_le`).

At `p = ∞` the scalar tests determine the essential supremum. If `f` is a.e. strongly measurable
with values a.e. in a separable subspace `E`, and the tests in `T` of norm at most one norm `E`,
then `‖f‖_∞ = sup ‖y ∘ f‖_∞` over these tests (`TauCeti.eLpNorm_top_eq_iSup_of_norming`); the
proof extracts a countable norming family on `E` with `TauCeti.exists_countable_norming_subset`.
Consequently, if `‖ι‖ ≤ 1` and the image of the unit ball of `Y` norms `E`, essential boundedness of
every `ι y ∘ f` already forces `f ∈ L∞(μ; X)` (`TauCeti.memLp_top_of_norming`), and then
`‖f‖_∞ = ‖scalarEvalLp f ι hf‖` (`TauCeti.norm_scalarEvalLp_top`). Over `ℝ` or `ℂ` the whole dual
norms `X` by the Hahn–Banach theorem, which gives `TauCeti.eLpNorm_top_eq_iSup_strongDual_apply`
and `TauCeti.memLp_top_iff_forall_strongDual_apply` for every a.e. strongly measurable `f`.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, Proposition 1.2.17 and Lemma 1.2.18.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

section NontriviallyNormedField

variable {𝕜 X W S : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {mS : MeasurableSpace S} {μ : Measure S}

section Operator

variable [CompleteSpace 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- The scalar-evaluation operator `y ↦ [ι y ∘ f]` from a Banach space `Y` of tests, acting on `X`
through `ι : Y →L[𝕜] StrongDual 𝕜 X`, to `Lᵖ(μ)`, for a function `f` all of whose scalar tests lie
in `Lᵖ(μ)`. It is a bounded operator by the closed graph theorem. -/
def scalarEvalLp (f : S → X) (ι : Y →L[𝕜] StrongDual 𝕜 X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) : Y →L[𝕜] Lp 𝕜 p μ :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := ({ toFun y := (hf y).toLp _
             map_add' y z := by
               rw [← MemLp.toLp_add]
               exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp)
             map_smul' c y := by
               rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
               exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp) } :
      Y →ₗ[𝕜] Lp 𝕜 p μ))
    fun u y g hu hg ↦ by
      -- Along a subsequence, `Lᵖ` convergence gives convergence almost everywhere.
      obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
      have hall : ∀ᵐ s ∂μ, ∀ n, (hf (u n)).toLp _ s = ι (u n) (f s) :=
        ae_all_iff.2 fun n ↦ (hf (u n)).coeFn_toLp
      refine Lp.ext ?_
      filter_upwards [hae, hall, (hf y).coeFn_toLp] with s hs hsn hsy
      refine tendsto_nhds_unique hs ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, hsn, hsy]
      exact (((ContinuousLinearMap.apply 𝕜 𝕜 (f s)).comp ι).continuous.tendsto y).comp
        (hu.comp hns.tendsto_atTop)

variable {f g : S → X} {ι : Y →L[𝕜] StrongDual 𝕜 X}
  {hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ} {hg : ∀ y, MemLp (fun s ↦ ι y (g s)) p μ}

/-- The value of the scalar-evaluation operator at `y` is the `Lᵖ` class of `s ↦ ι y (f s)`, as a
`MemLp.toLp`. -/
theorem scalarEvalLp_apply (y : Y) : scalarEvalLp f ι hf y = (hf y).toLp _ := (rfl)

/-- The value of the scalar-evaluation operator at `y` is represented by `s ↦ ι y (f s)`. -/
theorem coeFn_scalarEvalLp (y : Y) : scalarEvalLp f ι hf y =ᵐ[μ] fun s ↦ ι y (f s) :=
  (hf y).coeFn_toLp

/-- An `Lᵖ` class is the value of the scalar-evaluation operator at `y` exactly when it is
represented by `s ↦ ι y (f s)`. -/
theorem scalarEvalLp_apply_eq_iff (y : Y) (u : Lp 𝕜 p μ) :
    scalarEvalLp f ι hf y = u ↔ u =ᵐ[μ] fun s ↦ ι y (f s) := by
  refine ⟨fun h ↦ h ▸ coeFn_scalarEvalLp (hf := hf) y, fun h ↦ Lp.ext ?_⟩
  exact (coeFn_scalarEvalLp y).trans h.symm

/-- The norm of the value at `y` is the `Lᵖ` norm of the scalar test `s ↦ ι y (f s)`. -/
@[simp]
theorem norm_scalarEvalLp_apply (y : Y) :
    ‖scalarEvalLp f ι hf y‖ = (eLpNorm (fun s ↦ ι y (f s)) p μ).toReal :=
  Lp.norm_toLp _ (hf y)

/-- The scalar `Lᵖ` norms of `f` are uniformly bounded on the unit ball of `Y`, by the norm of
the scalar-evaluation operator. -/
theorem eLpNorm_apply_le_norm_scalarEvalLp_mul (y : Y) :
    eLpNorm (fun s ↦ ι y (f s)) p μ ≤ ENNReal.ofReal (‖scalarEvalLp f ι hf‖ * ‖y‖) := by
  rw [← ENNReal.ofReal_toReal (hf y).eLpNorm_ne_top, ← norm_scalarEvalLp_apply (hf := hf) y]
  exact ENNReal.ofReal_le_ofReal ((scalarEvalLp f ι hf).le_opNorm y)

/-- The scalar-evaluation operator only depends on the scalar tests up to almost-everywhere
equality. -/
theorem scalarEvalLp_congr (hfg : ∀ y, (fun s ↦ ι y (f s)) =ᵐ[μ] fun s ↦ ι y (g s)) :
    scalarEvalLp f ι hf = scalarEvalLp g ι hg :=
  ContinuousLinearMap.ext fun y ↦ MemLp.toLp_congr (hf y) (hg y) (hfg y)

/-- The scalar-evaluation operator is invariant under almost-everywhere equality of functions. -/
theorem scalarEvalLp_congr_ae (hfg : f =ᵐ[μ] g) : scalarEvalLp f ι hf = scalarEvalLp g ι hg :=
  scalarEvalLp_congr fun _ ↦ hfg.mono fun s hs ↦ by simp only [hs]

/-- The scalar-evaluation operator is additive in the function. -/
theorem scalarEvalLp_add (hfg : ∀ y, MemLp (fun s ↦ ι y ((f + g) s)) p μ) :
    scalarEvalLp (f + g) ι hfg = scalarEvalLp f ι hf + scalarEvalLp g ι hg :=
  ContinuousLinearMap.ext fun y ↦ by
    rw [add_apply, scalarEvalLp_apply, scalarEvalLp_apply,
      scalarEvalLp_apply, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp)

/-- The scalar-evaluation operator is homogeneous in the function. -/
theorem scalarEvalLp_smul (c : 𝕜) (hcf : ∀ y, MemLp (fun s ↦ ι y ((c • f) s)) p μ) :
    scalarEvalLp (c • f) ι hcf = c • scalarEvalLp f ι hf :=
  ContinuousLinearMap.ext fun y ↦ by
    rw [smul_apply, scalarEvalLp_apply, scalarEvalLp_apply,
      ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp)

/-- The scalar-evaluation operator of the zero function vanishes. -/
@[simp]
theorem scalarEvalLp_zero (h0 : ∀ y, MemLp (fun s ↦ ι y ((0 : S → X) s)) p μ) :
    scalarEvalLp 0 ι h0 = 0 :=
  ContinuousLinearMap.ext fun y ↦ (scalarEvalLp_apply_eq_iff y 0).2 <| by
    filter_upwards [Lp.coeFn_zero (E := 𝕜) (p := p) (μ := μ)] with s hs
    rw [hs]
    simp

/-- Changing the tests along a bounded linear map `κ : Z → Y` precomposes the scalar-evaluation
operator with `κ`. For `κ` the inclusion of a closed subspace this is restriction of the tests. -/
theorem scalarEvalLp_comp (κ : Z →L[𝕜] Y) :
    scalarEvalLp f (ι.comp κ) (fun z ↦ by simpa using hf (κ z)) =
      (scalarEvalLp f ι hf).comp κ :=
  ContinuousLinearMap.ext fun z ↦ by
    rw [ContinuousLinearMap.comp_apply, scalarEvalLp_apply, scalarEvalLp_apply]
    exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp)

/-- Functoriality in the target: the scalar tests `ι' v` of `A ∘ f`, for a bounded linear map
`A : X → W`, are the scalar tests of `f` by the adjoint images `ι' v ∘ A`. -/
theorem scalarEvalLp_comp_precomp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [CompleteSpace V] (A : X →L[𝕜] W) (ι' : V →L[𝕜] StrongDual 𝕜 W)
    (hAf : ∀ v, MemLp (fun s ↦ ι' v ((A ∘ f) s)) p μ) :
    scalarEvalLp (A ∘ f) ι' hAf =
      scalarEvalLp f ((ContinuousLinearMap.precomp 𝕜 A).comp ι') (fun v ↦ by simpa using hAf v) :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [scalarEvalLp_apply, scalarEvalLp_apply]
    exact MemLp.toLp_congr _ _ (.of_forall fun s ↦ by simp)

/-- For `f ∈ Lᵖ(μ; X)`, the scalar-evaluation operator has norm at most `‖ι‖ ‖f‖_p`. -/
theorem norm_scalarEvalLp_le (hf : MemLp f p μ) :
    ‖scalarEvalLp f ι (fun y ↦ (ι y).comp_memLp' hf)‖ ≤ ‖ι‖ * (eLpNorm f p μ).toReal := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  have h : scalarEvalLp f ι (fun y ↦ (ι y).comp_memLp' hf) y = (ι y).compLp (hf.toLp f) := by
    rw [scalarEvalLp_apply_eq_iff]
    filter_upwards [(ι y).coeFn_compLp (hf.toLp f), hf.coeFn_toLp] with s hs hfs
    rw [hs, hfs]
  rw [h, ← Lp.norm_toLp f hf, mul_right_comm]
  exact ((ι y).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right (ι.le_opNorm y) (norm_nonneg _))

end Operator

section Essup

/-- If `f` is a.e. strongly measurable with values almost everywhere in a separable subspace `E`,
and the members of norm at most one of a set `T` of functionals norm `E`, then the essential
supremum of `‖f‖` is the supremum of the essential suprema of its scalar tests from `T`. -/
theorem eLpNorm_top_eq_iSup_of_norming {f : S → X} (hf : AEStronglyMeasurable f μ)
    {E : Submodule 𝕜 X} (hE : IsSeparable (E : Set X)) (hfE : ∀ᵐ s ∂μ, f s ∈ E)
    {T : Set (StrongDual 𝕜 X)} (hT : ∀ x ∈ E, ∀ r < ‖x‖, ∃ y ∈ T, ‖y‖ ≤ 1 ∧ r < ‖y x‖) :
    eLpNorm f ∞ μ = ⨆ y ∈ T, ⨆ (_ : ‖y‖ ≤ 1), eLpNorm (fun s ↦ y (f s)) ∞ μ := by
  refine le_antisymm ?_ (iSup₂_le fun y _ ↦ iSup_le fun hy ↦
    eLpNorm_mono_ae (y.continuous.comp_aestronglyMeasurable hf)
      (.of_forall fun s ↦ y.le_of_opNorm_le hy (f s) |>.trans_eq (one_mul _)))
  -- Restrict the tests to `E` and extract a countable norming family.
  have := hE.separableSpace
  obtain ⟨T₀, hT₀T, hT₀c, -, hT₀⟩ := exists_countable_norming_subset
    (T := (fun y : StrongDual 𝕜 X ↦ y.comp E.subtypeL) '' {y | y ∈ T ∧ ‖y‖ ≤ 1})
    fun x r hr ↦ by
      obtain ⟨y, hyT, hy, hry⟩ := hT x x.property r hr
      refine ⟨y.comp E.subtypeL, mem_image_of_mem _ ⟨hyT, hy⟩,
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_, hry⟩
      simpa using y.le_of_opNorm_le hy x
  choose D hD hDE using fun x' : T₀ ↦ hT₀T x'.property
  have := hT₀c.to_subtype
  set M := ⨆ y ∈ T, ⨆ (_ : ‖y‖ ≤ 1), eLpNorm (fun s ↦ y (f s)) ∞ μ
  have hDM (i : T₀) : eLpNorm (fun s ↦ D i (f s)) ∞ μ ≤ M :=
    le_iSup₂_of_le (D i) (hD i).1 (le_iSup_of_le (hD i).2 le_rfl)
  have hall : ∀ᵐ s ∂μ, ∀ i : T₀, ‖D i (f s)‖ₑ ≤ eLpNorm (fun s ↦ D i (f s)) ∞ μ :=
    ae_all_iff.2 fun i ↦ ae_le_eLpNormEssSup.mono fun s hs ↦ hs.trans eLpNormEssSup_le_eLpNorm_top
  rw [eLpNorm_exponent_top hf]
  refine essSup_le_of_ae_le M ?_
  filter_upwards [hfE, hall] with s hsE hs
  -- At a good point, every value below `‖f s‖` is exceeded by some countable test.
  refine le_of_forall_lt fun c hc ↦ ?_
  lift c to ℝ≥0 using hc.ne_top
  obtain ⟨x', hx'T₀, hx'⟩ := hT₀ ⟨f s, hsE⟩ c <| by
    simpa [eNorm_eq_nnNorm, ← NNReal.coe_lt_coe] using hc
  have hx' : (c : ℝ≥0∞) < ‖D ⟨x', hx'T₀⟩ (f s)‖ₑ := by
    have h : D ⟨x', hx'T₀⟩ (f s) = x' ⟨f s, hsE⟩ :=
      DFunLike.congr_fun (hDE ⟨x', hx'T₀⟩) ⟨f s, hsE⟩
    simpa [h, eNorm_eq_nnNorm, ← NNReal.coe_lt_coe] using hx'
  exact hx'.trans_le ((hs _).trans (hDM _))

variable [CompleteSpace 𝕜] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  {f : S → X} {ι : Y →L[𝕜] StrongDual 𝕜 X} {E : Submodule 𝕜 X}

/-- The essential supremum of `‖f‖` is bounded by the norm of the scalar-evaluation operator into
`L∞(μ)`, for tests norming a separable subspace containing almost all values of `f`. -/
private theorem eLpNorm_top_le_ofReal_norm_scalarEvalLp (hf : AEStronglyMeasurable f μ)
    (hE : IsSeparable (E : Set X)) (hfE : ∀ᵐ s ∂μ, f s ∈ E) (hι : ‖ι‖ ≤ 1)
    (hιE : ∀ x ∈ E, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖)
    (hfι : ∀ y, MemLp (fun s ↦ ι y (f s)) ∞ μ) :
    eLpNorm f ∞ μ ≤ ENNReal.ofReal ‖scalarEvalLp f ι hfι‖ := by
  rw [eLpNorm_top_eq_iSup_of_norming (T := ι '' Metric.closedBall 0 1) hf hE hfE fun x hx r hr ↦ by
    obtain ⟨y, hy, hry⟩ := hιE x hx r hr
    exact ⟨ι y, mem_image_of_mem _ (mem_closedBall_zero_iff.2 hy),
      (ι.le_opNorm y).trans ((mul_le_mul hι hy (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)),
      hry⟩]
  refine iSup₂_le fun _ ⟨y, hy, hyt⟩ ↦ iSup_le fun _ ↦ ?_
  subst hyt
  refine (eLpNorm_apply_le_norm_scalarEvalLp_mul (hf := hfι) y).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.1 hy)

/-- Let `f` be a.e. strongly measurable with values almost everywhere in a separable subspace `E`,
and let `ι : Y →L[𝕜] StrongDual 𝕜 X` have norm at most one, with the images of the unit ball of `Y`
norming `E`. If every scalar test `ι y ∘ f` is essentially bounded, then so is `f`. -/
theorem memLp_top_of_norming (hf : AEStronglyMeasurable f μ) (hE : IsSeparable (E : Set X))
    (hfE : ∀ᵐ s ∂μ, f s ∈ E) (hι : ‖ι‖ ≤ 1)
    (hιE : ∀ x ∈ E, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖)
    (hfι : ∀ y, MemLp (fun s ↦ ι y (f s)) ∞ μ) : MemLp f ∞ μ :=
  memLp_iff.2 <| (eLpNorm_top_le_ofReal_norm_scalarEvalLp hf hE hfE hι hιE hfι).trans_lt
    ENNReal.ofReal_lt_top

/-- Under the hypotheses of `TauCeti.memLp_top_of_norming`, the norm of the scalar-evaluation
operator into `L∞(μ)` is the essential supremum of `‖f‖`. -/
theorem norm_scalarEvalLp_top (hf : AEStronglyMeasurable f μ) (hE : IsSeparable (E : Set X))
    (hfE : ∀ᵐ s ∂μ, f s ∈ E) (hι : ‖ι‖ ≤ 1)
    (hιE : ∀ x ∈ E, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖)
    (hfι : ∀ y, MemLp (fun s ↦ ι y (f s)) ∞ μ) :
    ‖scalarEvalLp f ι hfι‖ = (eLpNorm f ∞ μ).toReal := by
  refine le_antisymm ?_ (ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
    (eLpNorm_top_le_ofReal_norm_scalarEvalLp hf hE hfE hι hιE hfι))
  exact (norm_scalarEvalLp_le (memLp_top_of_norming hf hE hfE hι hιE hfι)).trans
    (mul_le_of_le_one_left ENNReal.toReal_nonneg hι)

end Essup

end NontriviallyNormedField

section RCLike

variable {𝕜 X S : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {mS : MeasurableSpace S} {μ : Measure S} {f : S → X}

/-- Over `ℝ` or `ℂ`, the essential supremum of `‖f‖` for an a.e. strongly measurable `f` is the
supremum of the essential suprema of its scalar tests `y ∘ f` over the closed unit ball of the
dual. -/
theorem eLpNorm_top_eq_iSup_strongDual_apply (hf : AEStronglyMeasurable f μ) :
    eLpNorm f ∞ μ = ⨆ y : StrongDual 𝕜 X, ⨆ (_ : ‖y‖ ≤ 1), eLpNorm (fun s ↦ y (f s)) ∞ μ := by
  -- Almost all values lie in the separable span of an essential range.
  have := FiniteDimensional.proper_rclike 𝕜 𝕜
  obtain ⟨t, ht, hft⟩ := hf.isSeparable_ae_range
  rw [eLpNorm_top_eq_iSup_of_norming (E := Submodule.span 𝕜 t) (T := univ) hf ht.span
    (hft.mono fun s hs ↦ Submodule.subset_span hs) fun x _ r hr ↦ by
      obtain ⟨y, hy, hyx⟩ := exists_dual_vector'' 𝕜 x
      exact ⟨y, mem_univ y, hy, by rwa [hyx, RCLike.norm_ofReal, abs_norm]⟩]
  simp

/-- Over `ℝ` or `ℂ`, an a.e. strongly measurable function is essentially bounded exactly when all
of its scalar tests are. -/
theorem memLp_top_iff_forall_strongDual_apply (hf : AEStronglyMeasurable f μ) :
    MemLp f ∞ μ ↔ ∀ y : StrongDual 𝕜 X, MemLp (fun s ↦ y (f s)) ∞ μ := by
  refine ⟨fun h y ↦ y.comp_memLp' h, fun h ↦ memLp_iff.2 ?_⟩
  rw [eLpNorm_top_eq_iSup_strongDual_apply (𝕜 := 𝕜) hf]
  refine lt_of_le_of_lt (iSup₂_le fun y hy ↦ ?_)
    (ENNReal.ofReal_lt_top (r := ‖scalarEvalLp f (ContinuousLinearMap.id 𝕜 _) h‖))
  exact (eLpNorm_apply_le_norm_scalarEvalLp_mul (f := f) (ι := ContinuousLinearMap.id 𝕜 _)
    (hf := h) y).trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (norm_nonneg _) hy))

end RCLike

end TauCeti
