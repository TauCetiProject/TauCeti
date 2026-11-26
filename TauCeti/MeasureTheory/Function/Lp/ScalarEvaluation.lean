/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Operator.Norming
public import TauCeti.MeasureTheory.Function.Lp.Operator.Orbit

/-!
# Scalar evaluations of vector-valued functions in Lᵖ

Let `ι : Y →L[𝕜] StrongDual 𝕜 X` be a bounded family of scalar tests on a normed space `X`,
indexed by a Banach space `Y`. The main examples are the whole dual and isometric copies of its
closed subspaces; another is the embedding of `X` into the dual of `X*`, whose tests are the
evaluations of dual-valued functions. Let `f : S → X` be a function such that every scalar function
`s ↦ ι y (f s)` belongs to `Lᵖ(μ)`, `1 ≤ p ≤ ∞`. The closed graph theorem makes the
scalar-evaluation map `T_f : y ↦ [ι y ∘ f]` a bounded linear operator `Y → Lᵖ(μ)`. No
measurability of `f` itself is assumed. When `ι` is contractive, this operator has norm at most
`‖f‖_p`.

At `p = ∞` the scalar tests recover the essential supremum. Suppose that `f` is almost
everywhere strongly measurable and takes values almost everywhere in a separable set `s` on which
the tests are `1`-norming: `‖x‖ = sup {‖ι y x‖ : ‖y‖ ≤ 1}` for `x ∈ s`. Then
`‖f‖_∞ = sup {‖ι y ∘ f‖_∞ : ‖y‖ ≤ 1}`, and `‖T_f‖ = ‖f‖_∞` for contractive `ι`; in
particular `f` is essentially bounded as soon as all its scalar tests are. The proof extracts
countably many norming tests on `s` from the norm-separability of the evaluation maps
`y ↦ ι y x`, `x ∈ s`, so that a single null set serves all of them. Over `ℝ` or `ℂ` the whole
dual is `1`-norming by Hahn–Banach.

## Main declarations

* `TauCeti.scalarEvalLp`: the bounded scalar-evaluation operator `Y →L[𝕜] Lp 𝕜 p μ`.
* `TauCeti.eq_scalarEvalLp_iff`: it is the unique operator with the almost everywhere formula
  `T y = ι y ∘ f`.
* `TauCeti.scalarEvalLp_comp`: compatibility with bounded maps of the target through their
  adjoints, including restriction of the tests.
* `TauCeti.eNorm_scalarEvalLp_le`: for contractive `ι`, its norm is at most `eLpNorm f p μ`.
* `TauCeti.eLpNorm_top_eq_iSup_of_norming`: `‖f‖_∞` is the supremum of the `‖ι y ∘ f‖_∞`
  over the unit ball of `Y`, for tests `1`-norming on an essential range of `f`.
* `TauCeti.eNorm_scalarEvalLp_top_of_norming` and `TauCeti.memLp_top_of_norming`: under the
  same hypotheses `‖T_f‖ = ‖f‖_∞`, and `f` is essentially bounded.
* `TauCeti.eLpNorm_top_eq_iSup_strongDual`: over `ℝ` or `ℂ`, the full dual computes `‖f‖_∞`.

## Implementation notes

The tests are indexed by an abstract Banach space `Y` with a map `ι` rather than by a submodule
of the dual. For a submodule of a space of continuous linear maps, instance search does not find
the operator norm on continuous linear maps out of it, so the norm of `T_f` could not be stated
for such a domain. The mathematical setting of a closed subspace of `X*` is the case of an
isometric `ι`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, Proposition 1.2.17 and Lemma 1.2.18.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section Operator

variable {S 𝕜 X Y Z W : Type*} [MeasurableSpace S] {μ : Measure S}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar-evaluation operator `y ↦ [ι y ∘ f]` from a Banach space `Y` of scalar tests
`ι : Y →L[𝕜] StrongDual 𝕜 X` to scalar `Lᵖ`, for a function `f` all of whose scalar tests belong
to `Lᵖ`. It is bounded by the closed graph theorem; no measurability of `f` is assumed. -/
noncomputable def scalarEvalLp (ι : Y →L[𝕜] StrongDual 𝕜 X) (f : S → X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) : Y →L[𝕜] Lp 𝕜 p μ :=
  orbitLpCLM (fun s ↦ ι.flip (f s)) fun y ↦ by
    simpa only [ContinuousLinearMap.flip_apply] using hf y

/-- The scalar-evaluation operator sends a test to the `Lᵖ` class of its composition with `f`. -/
@[simp]
theorem scalarEvalLp_apply (ι : Y →L[𝕜] StrongDual 𝕜 X) (f : S → X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (y : Y) :
    scalarEvalLp ι f hf y = (hf y).toLp fun s ↦ ι y (f s) := by
  simp only [scalarEvalLp, orbitLpCLM_apply, ContinuousLinearMap.flip_apply]

/-- A representative of `scalarEvalLp ι f hf y` agrees almost everywhere with `ι y ∘ f`. -/
theorem coeFn_scalarEvalLp (ι : Y →L[𝕜] StrongDual 𝕜 X) (f : S → X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (y : Y) :
    scalarEvalLp ι f hf y =ᵐ[μ] fun s ↦ ι y (f s) := by
  rw [scalarEvalLp_apply]
  exact (hf y).coeFn_toLp

/-- The almost everywhere formula `T y = ι y ∘ f` characterizes the scalar-evaluation
operator. -/
theorem eq_scalarEvalLp_iff (ι : Y →L[𝕜] StrongDual 𝕜 X) (f : S → X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (T : Y →L[𝕜] Lp 𝕜 p μ) :
    T = scalarEvalLp ι f hf ↔ ∀ y, T y =ᵐ[μ] fun s ↦ ι y (f s) := by
  refine ⟨fun h y ↦ h ▸ coeFn_scalarEvalLp ι f hf y, fun h ↦ ?_⟩
  ext y : 1
  exact Lp.ext ((h y).trans (coeFn_scalarEvalLp ι f hf y).symm)

/-- Functions whose scalar tests agree almost everywhere have the same scalar-evaluation
operator. The exceptional null set may depend on the test. -/
theorem scalarEvalLp_congr (ι : Y →L[𝕜] StrongDual 𝕜 X) {f g : S → X}
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (hg : ∀ y, MemLp (fun s ↦ ι y (g s)) p μ)
    (hfg : ∀ y, (fun s ↦ ι y (f s)) =ᵐ[μ] fun s ↦ ι y (g s)) :
    scalarEvalLp ι f hf = scalarEvalLp ι g hg :=
  (eq_scalarEvalLp_iff ι g hg _).2 fun y ↦ (coeFn_scalarEvalLp ι f hf y).trans (hfg y)

/-- The scalar-evaluation operator only depends on the almost everywhere class of `f`. -/
theorem scalarEvalLp_congr_ae (ι : Y →L[𝕜] StrongDual 𝕜 X) {f g : S → X}
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (hg : ∀ y, MemLp (fun s ↦ ι y (g s)) p μ)
    (hfg : f =ᵐ[μ] g) :
    scalarEvalLp ι f hf = scalarEvalLp ι g hg :=
  scalarEvalLp_congr ι hf hg fun y ↦ hfg.fun_comp (ι y)

/-- The scalar-evaluation operator of the zero function vanishes. -/
@[simp]
theorem scalarEvalLp_zero (ι : Y →L[𝕜] StrongDual 𝕜 X)
    (h : ∀ y, MemLp (fun s ↦ ι y ((0 : S → X) s)) p μ) :
    scalarEvalLp ι (0 : S → X) h = 0 := by
  refine ((eq_scalarEvalLp_iff ι _ h 0).2 fun y ↦ ?_).symm
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with s hs
  rw [zero_apply, hs, Pi.zero_apply, Pi.zero_apply, map_zero]

/-- The scalar-evaluation operator is additive in the function. -/
theorem scalarEvalLp_add (ι : Y →L[𝕜] StrongDual 𝕜 X) {f g : S → X}
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) (hg : ∀ y, MemLp (fun s ↦ ι y (g s)) p μ)
    (hfg : ∀ y, MemLp (fun s ↦ ι y ((f + g) s)) p μ) :
    scalarEvalLp ι (f + g) hfg = scalarEvalLp ι f hf + scalarEvalLp ι g hg := by
  refine ((eq_scalarEvalLp_iff ι _ hfg _).2 fun y ↦ ?_).symm
  filter_upwards [Lp.coeFn_add (scalarEvalLp ι f hf y) (scalarEvalLp ι g hg y),
    coeFn_scalarEvalLp ι f hf y, coeFn_scalarEvalLp ι g hg y] with s hs hfs hgs
  rw [add_apply, hs, Pi.add_apply, hfs, hgs, Pi.add_apply, map_add]

/-- The scalar-evaluation operator is homogeneous in the function. -/
theorem scalarEvalLp_smul (ι : Y →L[𝕜] StrongDual 𝕜 X) (c : 𝕜) {f : S → X}
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ)
    (hcf : ∀ y, MemLp (fun s ↦ ι y ((c • f) s)) p μ) :
    scalarEvalLp ι (c • f) hcf = c • scalarEvalLp ι f hf := by
  refine ((eq_scalarEvalLp_iff ι _ hcf _).2 fun y ↦ ?_).symm
  filter_upwards [Lp.coeFn_smul c (scalarEvalLp ι f hf y), coeFn_scalarEvalLp ι f hf y]
    with s hs hfs
  rw [smul_apply, hs, Pi.smul_apply, hfs, Pi.smul_apply, map_smul]

variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]

/-- Compatibility with a bounded map `T : X →L[𝕜] Z` through its adjoint. Let tests
`κ : W →L[𝕜] StrongDual 𝕜 Z` be carried by `j : W →L[𝕜] Y` onto tests of `X`, in the sense that
`ι (j w) = κ w ∘ T`. Then the operator of `T ∘ f` for the tests `κ` is the operator of `f`
composed with `j`. With `T` the identity this is restriction to a space of tests. -/
theorem scalarEvalLp_comp (ι : Y →L[𝕜] StrongDual 𝕜 X) (κ : W →L[𝕜] StrongDual 𝕜 Z)
    (T : X →L[𝕜] Z) (j : W →L[𝕜] Y) (hj : ∀ w, ι (j w) = (κ w).comp T) (f : S → X)
    (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ)
    (hTf : ∀ w, MemLp (fun s ↦ κ w (T (f s))) p μ) :
    scalarEvalLp κ (fun s ↦ T (f s)) hTf = (scalarEvalLp ι f hf).comp j := by
  refine ((eq_scalarEvalLp_iff κ _ hTf _).2 fun w ↦ ?_).symm
  filter_upwards [coeFn_scalarEvalLp ι f hf (j w)] with s hs
  rw [ContinuousLinearMap.comp_apply, hs, hj, ContinuousLinearMap.comp_apply]

/-- For contractive tests, the scalar-evaluation operator has extended norm at most
`eLpNorm f p μ`. This holds for every function `f`, the bound being trivial when `f` is not in
`Lᵖ(μ; X)`. -/
theorem eNorm_scalarEvalLp_le (ι : Y →L[𝕜] StrongDual 𝕜 X) (hι : ∀ y, ‖ι y‖ ≤ ‖y‖)
    (f : S → X) (hf : ∀ y, MemLp (fun s ↦ ι y (f s)) p μ) :
    ‖scalarEvalLp ι f hf‖ₑ ≤ eLpNorm f p μ := by
  refine ContinuousLinearMap.opENorm_le_bound _ fun y ↦ ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae (coeFn_scalarEvalLp ι f hf y), mul_comm]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p (hf y).aestronglyMeasurable
    (.of_forall fun s ↦ ?_)
  refine ((ι y).le_opENorm (f s)).trans (mul_le_mul_left ?_ _)
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hι y)

/-- For `g ∈ Lᵖ(μ; X)` and contractive tests, the scalar-evaluation operator of `g` has norm
at most `‖g‖`. -/
theorem norm_scalarEvalLp_le (ι : Y →L[𝕜] StrongDual 𝕜 X) (hι : ∀ y, ‖ι y‖ ≤ ‖y‖)
    (g : Lp X p μ) (hg : ∀ y, MemLp (fun s ↦ ι y (g s)) p μ) :
    ‖scalarEvalLp ι g hg‖ ≤ ‖g‖ := by
  rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eNorm_scalarEvalLp_le ι hι g hg)

end Operator

section Norming

variable {S 𝕜 X Y : Type*} [MeasurableSpace S] {μ : Measure S}
  [DenselyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Essential supremum by scalar tests.** Let `f` be almost everywhere strongly measurable
with values almost everywhere in a separable set `s`, and let the contractive tests
`ι : Y →L[𝕜] StrongDual 𝕜 X` be `1`-norming on `s`. Then `‖f‖_∞` is the supremum of
`‖ι y ∘ f‖_∞` over the unit ball of `Y`. -/
theorem eLpNorm_top_eq_iSup_of_norming (ι : Y →L[𝕜] StrongDual 𝕜 X) (hι : ∀ y, ‖ι y‖ ≤ ‖y‖)
    {s : Set X} {f : S → X} (hf : AEStronglyMeasurable f μ) (hs : IsSeparable s)
    (hfs : ∀ᵐ a ∂μ, f a ∈ s) (hY : ∀ x ∈ s, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖) :
    eLpNorm f ∞ μ = ⨆ (y : Y) (_ : ‖y‖ ≤ 1), eLpNorm (fun a ↦ ι y (f a)) ∞ μ := by
  set M := ⨆ (y : Y) (_ : ‖y‖ ≤ 1), eLpNorm (fun a ↦ ι y (f a)) ∞ μ
  refine le_antisymm ?_ (iSup₂_le fun y hy ↦ ?_)
  swap
  · refine eLpNorm_mono_ae ((ι y).continuous.comp_aestronglyMeasurable hf)
      (.of_forall fun a ↦ ?_)
    exact ((ι y).le_opNorm (f a)).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((hι y).trans hy))
  -- The evaluation maps `y ↦ ι y x` at points of `s` form a norm-separable family of maps on
  -- `Y`, so countably many tests in the unit ball of `Y` recover all their norms.
  obtain ⟨t, htc, htne, ht1, ht⟩ := (hs.image ι.flip.continuous).exists_countable_norming
  -- On `s`, the norm of a point is at most the norm of its evaluation map.
  have hnorm (x : X) (hx : x ∈ s) : ‖x‖ ≤ ‖ι.flip x‖ := by
    refine le_of_forall_lt fun r hr ↦ ?_
    obtain ⟨y, hy1, hry⟩ := hY x hx r hr
    calc
      r < ‖ι.flip x y‖ := by rwa [ContinuousLinearMap.flip_apply]
      _ ≤ ‖ι.flip x‖ * ‖y‖ := (ι.flip x).le_opNorm y
      _ ≤ ‖ι.flip x‖ := mul_le_of_le_one_right (norm_nonneg _) hy1
  -- One null set serves all the countably many norming tests.
  have htest : ∀ᵐ a ∂μ, ∀ y ∈ t, ‖ι y (f a)‖ₑ ≤ M := by
    refine (ae_ball_iff htc).2 fun y hyt ↦ ?_
    have hle : eLpNorm (fun a ↦ ι y (f a)) ∞ μ ≤ M :=
      le_iSup₂_of_le (f := fun (y : Y) (_ : ‖y‖ ≤ 1) ↦ eLpNorm (fun a ↦ ι y (f a)) ∞ μ)
        y (ht1 y hyt) le_rfl
    filter_upwards [ae_le_eLpNormEssSup (f := fun a ↦ ι y (f a)) (μ := μ)] with a ha
    rw [← eLpNorm_exponent_top ((ι y).continuous.comp_aestronglyMeasurable hf)] at ha
    exact ha.trans hle
  rw [eLpNorm_exponent_top hf]
  refine essSup_le_of_ae_le M ?_
  filter_upwards [htest, hfs] with a ha has
  rcases eq_or_ne M ∞ with hM | hM
  · exact hM ▸ le_top
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hM]
  refine ENNReal.ofReal_le_ofReal ((hnorm _ has).trans ?_)
  rw [ht _ (mem_image_of_mem _ has)]
  refine csSup_le (htne.image _) ?_
  rintro _ ⟨y, hyt, rfl⟩
  rw [← ENNReal.ofReal_le_iff_le_toReal hM, ofReal_norm, ContinuousLinearMap.flip_apply]
  exact ha y hyt

variable [CompleteSpace 𝕜] [CompleteSpace Y]

/-- **Norm of the scalar-evaluation operator at `p = ∞`.** If `f` is almost everywhere strongly
measurable with values almost everywhere in a separable set on which the contractive tests `ι`
are `1`-norming, then the scalar-evaluation operator `Y → L∞(μ)` has extended norm `‖f‖_∞`. -/
theorem eNorm_scalarEvalLp_top_of_norming (ι : Y →L[𝕜] StrongDual 𝕜 X)
    (hι : ∀ y, ‖ι y‖ ≤ ‖y‖) {s : Set X} {f : S → X} (hf : AEStronglyMeasurable f μ)
    (hs : IsSeparable s) (hfs : ∀ᵐ a ∂μ, f a ∈ s)
    (hY : ∀ x ∈ s, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖)
    (hfY : ∀ y, MemLp (fun a ↦ ι y (f a)) ∞ μ) :
    ‖scalarEvalLp ι f hfY‖ₑ = eLpNorm f ∞ μ := by
  refine le_antisymm (eNorm_scalarEvalLp_le ι hι f hfY) ?_
  rw [eLpNorm_top_eq_iSup_of_norming ι hι hf hs hfs hY]
  refine iSup₂_le fun y hy ↦ ?_
  have hy' : ‖y‖ₑ ≤ 1 := by
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_one.2 hy
  calc
    eLpNorm (fun a ↦ ι y (f a)) ∞ μ = ‖scalarEvalLp ι f hfY y‖ₑ := by
      rw [Lp.eNorm_def, eLpNorm_congr_ae (coeFn_scalarEvalLp ι f hfY y)]
    _ ≤ ‖scalarEvalLp ι f hfY‖ₑ * ‖y‖ₑ := ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖scalarEvalLp ι f hfY‖ₑ := mul_le_of_le_one_right' hy'

/-- **Essential boundedness from scalar tests.** If `f` is almost everywhere strongly measurable
with values almost everywhere in a separable set on which the contractive tests `ι` are
`1`-norming, and every scalar test `ι y ∘ f` is essentially bounded, then `f` is essentially
bounded. -/
theorem memLp_top_of_norming (ι : Y →L[𝕜] StrongDual 𝕜 X) (hι : ∀ y, ‖ι y‖ ≤ ‖y‖)
    {s : Set X} {f : S → X} (hf : AEStronglyMeasurable f μ) (hs : IsSeparable s)
    (hfs : ∀ᵐ a ∂μ, f a ∈ s) (hY : ∀ x ∈ s, ∀ r < ‖x‖, ∃ y, ‖y‖ ≤ 1 ∧ r < ‖ι y x‖)
    (hfY : ∀ y, MemLp (fun a ↦ ι y (f a)) ∞ μ) :
    MemLp f ∞ μ := by
  rw [memLp_iff, ← eNorm_scalarEvalLp_top_of_norming ι hι hf hs hfs hY hfY]
  exact eNorm_lt_top

end Norming

/-- Over `ℝ` or `ℂ`, the essential supremum norm of an almost everywhere strongly measurable
function is the supremum of the essential supremum norms of its compositions with functionals
of norm at most one. The whole dual is `1`-norming by Hahn–Banach. -/
theorem eLpNorm_top_eq_iSup_strongDual {S 𝕜 X : Type*} [MeasurableSpace S] {μ : Measure S}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] {f : S → X}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f ∞ μ = ⨆ (x' : StrongDual 𝕜 X) (_ : ‖x'‖ ≤ 1), eLpNorm (fun a ↦ x' (f a)) ∞ μ := by
  obtain ⟨s, hs, hfs⟩ := hf.isSeparable_ae_range
  refine eLpNorm_top_eq_iSup_of_norming (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X))
    (fun _ ↦ le_rfl) hf hs hfs fun x _ r hr ↦ ?_
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' 𝕜 x
  exact ⟨g, hg1, by simpa [hgx] using hr⟩

end TauCeti
