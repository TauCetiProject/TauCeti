/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Complex.VerticalStrip
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The complex interpolation method

For a compatible couple `(X₀, X₁)` of complex normed spaces and `0 ≤ θ ≤ 1`, Calderón's complex
interpolation space `[X₀, X₁]_θ` consists of the values `F θ` of the *admissible* functions `F`:
bounded continuous functions on the closed strip `0 ≤ re z ≤ 1` with values in the sum `X₀ + X₁`,
holomorphic in the open strip, whose restrictions `t ↦ F (j + i t)` to the two boundary lines are
continuous functions into `X_j` vanishing at infinity. The norm of `u ∈ [X₀, X₁]_θ` is the
infimum of `max_j sup_t ‖F (j + i t)‖_{X_j}` over the admissible `F` with `F θ = u`.

By Hadamard's three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`), an admissible
function is determined on the closed strip by its two boundary traces, and it is
bounded there in the sum norm by their sup norms. We therefore realise the Banach space of
admissible functions through their boundary traces:

* `CompatibleCouple.IsStripFunction F g`: `F` is admissible with boundary traces `g = (g₀, g₁)`.
  It satisfies the three-lines bound `‖F z‖ ≤ ‖g₀‖ ^ (1 - re z) * ‖g₁‖ ^ re z`
  (`CompatibleCouple.IsStripFunction.norm_le_rpow_mul_rpow`);
* `CompatibleCouple.stripTraces`: the submodule of `C₀(ℝ, X₀) × C₀(ℝ, X₁)` of the boundary
  traces of admissible functions, normed by `max ‖g₀‖ ‖g₁‖`. It is closed when `X₀` and `X₁` are
  complete (`CompatibleCouple.isClosed_stripTraces`), hence then a Banach space;
* `CompatibleCouple.stripFunction g`: the admissible function with traces `g`, extended by zero
  off the closed strip, and `CompatibleCouple.stripEval z`, the continuous linear evaluation
  `g ↦ F z`, of norm at most one;
* `CompatibleCouple.ComplexMethodSpace θ`: the quotient of `stripTraces` by the kernel of
  `stripEval θ`, with its quotient (infimum) norm, a Banach space when `X₀` and `X₁` are. The
  map `ComplexMethodSpace.toSum` embeds it injectively into the sum space without increasing
  norms, with image the values `F θ` of admissible functions
  (`ComplexMethodSpace.exists_toSum_eq_iff`), and each such `F` bounds the norm of `F θ` by the
  norm of its traces (`ComplexMethodSpace.norm_le_of_toSum_eq`);
* `ComplexMethodSpace.ofInter`: the intersection embeds with `‖x‖_θ ≤ ‖x‖_{X₀ ∩ X₁}`
  (`ComplexMethodSpace.norm_ofInter_le`), using the admissible functions `exp (δ (z - θ)²) x`
  with `δ → 0`;
* `ComplexMethodSpace.map`: continuous linear maps `T₀ : X₀ → Y₀`, `T₁ : X₁ → Y₁` that agree on the
  intersection, with norms at most `M₀, M₁ ≥ 0`, induce a map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` of norm at
  most `M₀ ^ (1 - θ) * M₁ ^ θ` (`ComplexMethodSpace.norm_map_le`), in particular of norm at most
  `‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ` (`ComplexMethodSpace.opNorm_map_le_opNorm`). The construction
  preserves identities and composition (`ComplexMethodSpace.map_id`, `ComplexMethodSpace.map_comp`)
  and commutes with the inclusions of the intersections (`ComplexMethodSpace.map_ofInter`). Thus
  the complex method is an exact interpolation functor of exponent `θ`.
* `ComplexMethodSpace.norm_refl`: for the couple `(X, X)`, the complex method gives back the norm
  of `X`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Lemma 4.1.1, Theorem 4.1.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines Filter Set Topology
open scoped ZeroAtInfty

namespace TauCeti

open Complex.HadamardThreeLines

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Admissible functions on the strip -/

/-- `F` is an *admissible function* for the complex method, with boundary traces
`g = (g₀, g₁)`: it is bounded on the closed strip `0 ≤ re z ≤ 1`, holomorphic on the open strip
and continuous up to its boundary, and its values on the boundary lines are
`F (t * I) = g₀ t ∈ X₀` and `F (1 + t * I) = g₁ t ∈ X₁`. The traces are continuous and vanish at
infinity since `g₀ : C₀(ℝ, X₀)` and `g₁ : C₀(ℝ, X₁)`. -/
structure IsStripFunction (F : ℂ → C.SumSpace) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) : Prop where
  /-- `F` is holomorphic on the open strip and continuous on the closed strip. -/
  diffContOnCl : DiffContOnCl ℂ F (verticalStrip 0 1)
  /-- `F` is bounded on the closed strip. -/
  isBounded : Bornology.IsBounded (F '' verticalClosedStrip 0 1)
  /-- On the line `re z = 0`, `F` takes the values of `g₀` in `X₀`. -/
  apply_mul_I (t : ℝ) : F (t * I) = C.fstToSum (g.1 t)
  /-- On the line `re z = 1`, `F` takes the values of `g₁` in `X₁`. -/
  apply_one_add_mul_I (t : ℝ) : F (1 + t * I) = C.sndToSum (g.2 t)

namespace IsStripFunction

variable {C} {F G : ℂ → C.SumSpace} {g h : C₀(ℝ, X₀) × C₀(ℝ, X₁)}

/-- An admissible function is bounded in norm on the closed strip. -/
theorem exists_norm_le (hF : C.IsStripFunction F g) :
    ∃ M, ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hF.isBounded
  exact ⟨M, fun z hz => hM _ (mem_image_of_mem F hz)⟩

theorem zero : C.IsStripFunction 0 0 where
  diffContOnCl := diffContOnCl_const (c := 0)
  isBounded := (Bornology.isBounded_singleton (x := 0)).subset <| by
    rintro _ ⟨z, -, rfl⟩
    rfl
  apply_mul_I _ := by simp
  apply_one_add_mul_I _ := by simp

theorem add (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G h) :
    C.IsStripFunction (F + G) (g + h) where
  diffContOnCl := hF.diffContOnCl.add hG.diffContOnCl
  isBounded := by
    obtain ⟨M, hM⟩ := hF.exists_norm_le
    obtain ⟨N, hN⟩ := hG.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨M + N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hM z hz) (hN z hz))
  apply_mul_I t := by simp [hF.apply_mul_I, hG.apply_mul_I]
  apply_one_add_mul_I t := by simp [hF.apply_one_add_mul_I, hG.apply_one_add_mul_I]

theorem const_smul (hF : C.IsStripFunction F g) (c : ℂ) : C.IsStripFunction (c • F) (c • g) where
  diffContOnCl := hF.diffContOnCl.const_smul c
  isBounded := by
    obtain ⟨M, hM⟩ := hF.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨‖c‖ * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg c)
  apply_mul_I t := by simp [hF.apply_mul_I]
  apply_one_add_mul_I t := by simp [hF.apply_one_add_mul_I]

theorem sub (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G h) :
    C.IsStripFunction (F - G) (g - h) := by
  simpa [sub_eq_add_neg] using hF.add (hG.const_smul (-1))

/-- **Three-lines bound.** On the closed strip, an admissible function with boundary traces
`(g₀, g₁)` satisfies `‖F z‖ ≤ ‖g₀‖ ^ (1 - re z) * ‖g₁‖ ^ re z`. -/
theorem norm_le_rpow_mul_rpow (hF : C.IsStripFunction F g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖F z‖ ≤ ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re := by
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    obtain ⟨M, hM⟩ := hF.exists_norm_le
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hM w hw
  refine norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hF.diffContOnCl hB
    (fun w hw => ?_) (fun w hw => ?_)
  · rw [← re_add_im w, hw, ofReal_zero, zero_add, hF.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _)
  · rw [← re_add_im w, hw, ofReal_one, hF.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _)

/-- **Maximum principle.** On the closed strip, an admissible function is bounded in the sum norm
by the norm `max ‖g₀‖ ‖g₁‖` of its boundary traces. -/
theorem norm_le (hF : C.IsStripFunction F g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖F z‖ ≤ ‖g‖ := by
  refine (hF.norm_le_rpow_mul_rpow hz).trans ?_
  calc ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re ≤ ‖g‖ ^ (1 - z.re) * ‖g‖ ^ z.re := by
        gcongr
        · exact sub_nonneg.2 hz.2
        · exact norm_fst_le g
        · exact hz.1
        · exact norm_snd_le g
    _ = ‖g‖ := by
        rw [← Real.rpow_add' (norm_nonneg g) (by simp), sub_add_cancel, Real.rpow_one]

/-- An admissible function is determined on the closed strip by its boundary traces. -/
theorem eqOn (hF : C.IsStripFunction F g) (hG : C.IsStripFunction G g) :
    EqOn F G (verticalClosedStrip 0 1) := fun z hz => by
  simpa [sub_eq_zero] using (hF.sub hG).norm_le hz

end IsStripFunction

/-! ### The space of boundary traces -/

/-- The boundary traces `(g₀, g₁)` of the admissible functions of the complex method, a submodule
of `C₀(ℝ, X₀) × C₀(ℝ, X₁)`. With the induced norm `max ‖g₀‖ ‖g₁‖` it is isometric to the space of
admissible functions with the norm `max_j sup_t ‖F (j + i t)‖_{X_j}`, since an admissible function
is determined by its traces (`CompatibleCouple.IsStripFunction.eqOn`). -/
def stripTraces : Submodule ℂ (C₀(ℝ, X₀) × C₀(ℝ, X₁)) where
  carrier := {g | ∃ F, C.IsStripFunction F g}
  add_mem' := fun ⟨F, hF⟩ ⟨G, hG⟩ => ⟨F + G, hF.add hG⟩
  zero_mem' := ⟨0, IsStripFunction.zero⟩
  smul_mem' c _ := fun ⟨F, hF⟩ => ⟨c • F, hF.const_smul c⟩

variable {C} in
theorem mem_stripTraces_iff {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} :
    g ∈ C.stripTraces ↔ ∃ F, C.IsStripFunction F g :=
  Iff.rfl

/-- The admissible function with boundary traces `g`, extended by zero off the closed strip. On
the closed strip it agrees with every admissible function with these traces
(`CompatibleCouple.stripFunction_eq`). -/
def stripFunction (g : C.stripTraces) : ℂ → C.SumSpace :=
  (verticalClosedStrip 0 1).indicator (mem_stripTraces_iff.1 g.2).choose

theorem isStripFunction_stripFunction (g : C.stripTraces) :
    C.IsStripFunction (C.stripFunction g) g := by
  have hF := (mem_stripTraces_iff.1 g.2).choose_spec
  have hEq : EqOn (C.stripFunction g) (mem_stripTraces_iff.1 g.2).choose
      (verticalClosedStrip 0 1) := fun z hz => indicator_of_mem hz _
  exact
    { diffContOnCl :=
        ⟨hF.diffContOnCl.differentiableOn.congr
            (hEq.mono (verticalStrip_subset_verticalClosedStrip 0 1)),
          hF.diffContOnCl.continuousOn.congr (hEq.mono (closure_verticalStrip_subset 0 1))⟩
      isBounded := by
        rw [hEq.image_eq]
        exact hF.isBounded
      apply_mul_I t :=
        (hEq (by simp)).trans (hF.apply_mul_I t)
      apply_one_add_mul_I t :=
        (hEq (by simp)).trans (hF.apply_one_add_mul_I t) }

variable {C} in
theorem stripFunction_eq {g : C.stripTraces} {F : ℂ → C.SumSpace} (hF : C.IsStripFunction F g)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : C.stripFunction g z = F z :=
  (C.isStripFunction_stripFunction g).eqOn hF hz

@[simp]
theorem stripFunction_mul_I (g : C.stripTraces) (t : ℝ) :
    C.stripFunction g (t * I) = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) :=
  (C.isStripFunction_stripFunction g).apply_mul_I t

@[simp]
theorem stripFunction_one_add_mul_I (g : C.stripTraces) (t : ℝ) :
    C.stripFunction g (1 + t * I) = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) :=
  (C.isStripFunction_stripFunction g).apply_one_add_mul_I t

@[simp]
theorem stripFunction_eq_zero (g : C.stripTraces) {z : ℂ} (hz : z ∉ verticalClosedStrip 0 1) :
    C.stripFunction g z = 0 :=
  indicator_of_notMem hz _

@[simp]
theorem stripFunction_zero : C.stripFunction 0 = 0 := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq IsStripFunction.zero hz
  · exact C.stripFunction_eq_zero _ hz

@[simp]
theorem stripFunction_add (g h : C.stripTraces) :
    C.stripFunction (g + h) = C.stripFunction g + C.stripFunction h := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq
      ((C.isStripFunction_stripFunction g).add (C.isStripFunction_stripFunction h)) hz
  · simp [C.stripFunction_eq_zero _ hz]

@[simp]
theorem stripFunction_smul (c : ℂ) (g : C.stripTraces) :
    C.stripFunction (c • g) = c • C.stripFunction g := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact stripFunction_eq ((C.isStripFunction_stripFunction g).const_smul c) hz
  · simp [C.stripFunction_eq_zero _ hz]

/-- The admissible function with traces `g` is bounded by `‖g‖` everywhere. -/
theorem norm_stripFunction_le (g : C.stripTraces) (z : ℂ) : ‖C.stripFunction g z‖ ≤ ‖g‖ := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact (C.isStripFunction_stripFunction g).norm_le hz
  · simp [C.stripFunction_eq_zero _ hz]

/-- Evaluation `g ↦ F z` of the admissible function with traces `g` at a point `z`, a continuous
linear map of norm at most one. It vanishes for `z` off the closed strip
(`CompatibleCouple.stripEval_eq_zero`). -/
def stripEval (z : ℂ) : C.stripTraces →L[ℂ] C.SumSpace :=
  LinearMap.mkContinuous
    { toFun g := C.stripFunction g z
      map_add' g h := by rw [stripFunction_add, Pi.add_apply]
      map_smul' c g := by rw [stripFunction_smul, Pi.smul_apply, RingHom.id_apply] }
    1 fun g => by simpa using C.norm_stripFunction_le g z

@[simp]
theorem stripEval_apply (z : ℂ) (g : C.stripTraces) : C.stripEval z g = C.stripFunction g z :=
  (rfl)

/-- Evaluation off the closed strip vanishes. -/
@[simp]
theorem stripEval_eq_zero {z : ℂ} (hz : z ∉ verticalClosedStrip 0 1) : C.stripEval z = 0 :=
  ContinuousLinearMap.ext fun g => C.stripFunction_eq_zero g hz

theorem norm_stripEval_le (z : ℂ) : ‖C.stripEval z‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    simpa using C.norm_stripFunction_le g z

/-- The boundary traces of the admissible functions form a closed subspace when `X₀` and `X₁` are
complete: a uniform limit of admissible functions on the closed strip is admissible. -/
theorem isClosed_stripTraces [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.stripTraces : Set (C₀(ℝ, X₀) × C₀(ℝ, X₁))) := by
  refine IsSeqClosed.isClosed fun {u g} hu hlim => ?_
  set F : ℕ → ℂ → C.SumSpace := fun n => C.stripFunction ⟨u n, hu n⟩
  have hF (n : ℕ) : C.IsStripFunction (F n) (u n) := C.isStripFunction_stripFunction _
  have hdist (n m : ℕ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      ‖F n z - F m z‖ ≤ ‖u n - u m‖ :=
    ((hF n).sub (hF m)).norm_le hz
  -- on the closed strip, `F n` converges pointwise, since the traces form a Cauchy sequence
  have hcauchy {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : CauchySeq fun n => F n z := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
    exact ⟨N, fun n hn => by
      rw [dist_eq_norm]
      exact (hdist n N hz).trans_lt (by simpa [dist_eq_norm] using hN n hn)⟩
  set F' : ℂ → C.SumSpace := fun z => limUnder atTop fun n => F n z
  have hlimz {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      Tendsto (fun n => F n z) atTop (𝓝 (F' z)) :=
    (hcauchy hz).tendsto_limUnder
  -- the convergence is uniform on the closed strip, with rate `‖u n - g‖`
  have hunif : TendstoUniformlyOn F F' atTop (verticalClosedStrip 0 1) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    have hg : Tendsto (fun n => ‖u n - g‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn z hz
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt ?_ hn
    exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (hlimz hz)).norm
      (tendsto_const_nhds.sub hlim).norm fun m => hdist n m hz
  have hbound {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) : ‖F' z‖ ≤ ‖g‖ :=
    le_of_tendsto_of_tendsto' (hlimz hz).norm hlim.norm fun n => (hF n).norm_le hz
  have hfst (t : ℝ) : Tendsto (fun n => (u n).1 t) atTop (𝓝 (g.1 t)) := by
    simpa [Function.comp_def] using
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto _).comp
        ((continuous_fst.tendsto g).comp hlim)
  have hsnd (t : ℝ) : Tendsto (fun n => (u n).2 t) atTop (𝓝 (g.2 t)) := by
    simpa [Function.comp_def] using
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto _).comp
        ((continuous_snd.tendsto g).comp hlim)
  -- the limit `F'` is admissible with traces `g`
  refine ⟨F', ⟨⟨?_, ?_⟩, ?_, fun t => ?_, fun t => ?_⟩⟩
  · exact (hunif.mono (verticalStrip_subset_verticalClosedStrip 0 1)).tendstoLocallyUniformlyOn
      |>.differentiableOn (.of_forall fun n => (hF n).diffContOnCl.differentiableOn)
        (isOpen_verticalStrip 0 1)
  · exact (hunif.mono (closure_verticalStrip_subset 0 1)).continuousOn
      (.of_forall fun n => (hF n).diffContOnCl.continuousOn)
  · refine isBounded_iff_forall_norm_le.2 ⟨‖g‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbound hz
  · refine tendsto_nhds_unique (hlimz (by simp)) ?_
    simp_rw [(hF _).apply_mul_I]
    exact (C.fstToSum.continuous.tendsto _).comp (hfst t)
  · refine tendsto_nhds_unique (hlimz (by simp)) ?_
    simp_rw [(hF _).apply_one_add_mul_I]
    exact (C.sndToSum.continuous.tendsto _).comp (hsnd t)

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.stripTraces :=
  C.isClosed_stripTraces.completeSpace_coe

instance (z : ℂ) : IsClosed ((C.stripEval z).ker : Set C.stripTraces) :=
  (C.stripEval z).isClosed_ker

/-! ### The complex interpolation space -/

/-- The complex interpolation space `[X₀, X₁]_θ` of the couple, for `0 ≤ θ ≤ 1`: the quotient of
the space of admissible functions (realised by their boundary traces, `stripTraces`) by those
vanishing at `θ`, with the quotient norm
`‖u‖_θ = inf {‖g‖ | F θ = u for the admissible function F with traces g}`
(`ComplexMethodSpace.norm_lt_iff`). It is a Banach space when `X₀` and `X₁` are, and it embeds
injectively into the sum space by `ComplexMethodSpace.toSum`. For `θ` outside `[0, 1]` the
evaluation `stripEval θ` vanishes, so the space is zero
(`ComplexMethodSpace.eq_zero_of_notMem`). -/
def ComplexMethodSpace (θ : ℝ) : Type _ :=
  C.stripTraces ⧸ (C.stripEval θ).ker

namespace ComplexMethodSpace

variable {C} {θ : ℝ}

instance : NormedAddCommGroup (C.ComplexMethodSpace θ) :=
  inferInstanceAs (NormedAddCommGroup (C.stripTraces ⧸ (C.stripEval θ).ker))

instance : NormedSpace ℂ (C.ComplexMethodSpace θ) :=
  inferInstanceAs (NormedSpace ℂ (C.stripTraces ⧸ (C.stripEval θ).ker))

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace (C.ComplexMethodSpace θ) :=
  inferInstanceAs (CompleteSpace (C.stripTraces ⧸ (C.stripEval θ).ker))

variable (θ) in
/-- The class in `[X₀, X₁]_θ` of the admissible function with boundary traces `g`. -/
def mk : C.stripTraces →L[ℂ] C.ComplexMethodSpace θ :=
  (C.stripEval θ).ker.mkQL

theorem mk_surjective : Function.Surjective (mk θ : C.stripTraces → C.ComplexMethodSpace θ) :=
  Submodule.mkQ_surjective _

theorem mk_eq_mk_iff {g h : C.stripTraces} :
    mk θ g = mk θ h ↔ C.stripEval θ g = C.stripEval θ h := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := C.stripEval θ g), ← map_sub]
  exact Submodule.Quotient.mk_eq_zero _

/-- The quotient norm of `[X₀, X₁]_θ`: `‖u‖_θ < r` exactly when `u` is the class of boundary
traces of norm less than `r`. -/
theorem norm_lt_iff {u : C.ComplexMethodSpace θ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ g, mk θ g = u ∧ ‖g‖ < r :=
  QuotientAddGroup.norm_lt_iff

theorem norm_mk_le (g : C.stripTraces) : ‖mk θ g‖ ≤ ‖g‖ :=
  Submodule.Quotient.norm_mk_le _ g

/-- The inclusion of `[X₀, X₁]_θ` into the sum space, `F ↦ F θ`. -/
def toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace :=
  (C.stripEval θ).ker.liftQL (C.stripEval θ) le_rfl

@[simp]
theorem toSum_mk (g : C.stripTraces) : toSum (mk θ g) = C.stripEval θ g :=
  (rfl)

theorem toSum_injective : Function.Injective (toSum : C.ComplexMethodSpace θ → C.SumSpace) := by
  intro u v huv
  obtain ⟨g, rfl⟩ := mk_surjective u
  obtain ⟨h, rfl⟩ := mk_surjective v
  exact mk_eq_mk_iff.2 (by simpa using huv)

/-- Elements of `[X₀, X₁]_θ` are determined by their images in the sum space. -/
@[ext]
theorem ext {u v : C.ComplexMethodSpace θ} (h : toSum u = toSum v) : u = v :=
  toSum_injective h

/-- For `θ` outside `[0, 1]`, the space `[X₀, X₁]_θ` is zero. -/
theorem eq_zero_of_notMem (hθ : θ ∉ Icc 0 1) (u : C.ComplexMethodSpace θ) : u = 0 := by
  ext
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [toSum_mk, C.stripEval_eq_zero (by simpa using hθ), map_zero, zero_apply]

/-- The inclusion of `[X₀, X₁]_θ` into the sum space does not increase norms. -/
theorem norm_toSum_le (u : C.ComplexMethodSpace θ) : ‖toSum u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [toSum_mk]
  exact ((C.stripEval θ).le_of_opNorm_le (C.norm_stripEval_le θ) g).trans_lt (by simpa using hg)

/-- The inclusion of `[X₀, X₁]_θ` into the sum space has operator norm at most one. -/
theorem opNorm_toSum_le : ‖(toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by simpa using norm_toSum_le u

/-- An element of the sum space lies in `[X₀, X₁]_θ` exactly when it is the value at `θ` of an
admissible function. -/
theorem exists_toSum_eq_iff (hθ : θ ∈ Icc 0 1) {u : C.SumSpace} :
    (∃ v : C.ComplexMethodSpace θ, toSum v = u) ↔
      ∃ F g, C.IsStripFunction F g ∧ F θ = u := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := mk_surjective v
    exact ⟨_, g, C.isStripFunction_stripFunction g, rfl⟩
  · rintro ⟨F, g, hF, rfl⟩
    exact ⟨mk θ ⟨g, F, hF⟩, by
      simpa using stripFunction_eq hF (by simpa using hθ)⟩

/-- For `0 ≤ θ ≤ 1`, an admissible function `F` with boundary traces `g` and `F θ = u` bounds the
norm of `u` by the norm of `g`. -/
theorem norm_le_of_toSum_eq (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g)
    (hu : toSum u = F θ) : ‖u‖ ≤ ‖g‖ := by
  have : u = mk θ ⟨g, F, hF⟩ := ext <| by
    rw [hu, toSum_mk, stripEval_apply, stripFunction_eq hF (by simpa using hθ)]
  exact this ▸ norm_mk_le _

end ComplexMethodSpace

/-! ### The intersection embeds into the complex interpolation space -/

section Inter

/-- The Gaussian factor `exp (δ (z - θ)²)`, equal to one at `θ` and decaying along vertical
lines. -/
private def gaussian (δ θ : ℝ) (z : ℂ) : ℂ :=
  exp (δ * (z - θ) ^ 2)

private theorem differentiable_gaussian (δ θ : ℝ) : Differentiable ℂ (gaussian δ θ) := by
  unfold gaussian
  fun_prop

private theorem norm_gaussian (δ θ : ℝ) (z : ℂ) :
    ‖gaussian δ θ z‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [gaussian, norm_exp]
  congr 1
  simp [sq]

private theorem norm_gaussian_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ} (hz : z.re ∈ Icc 0 1) :
    ‖gaussian δ θ z‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_gaussian]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

private theorem tendsto_norm_gaussian {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) :
    Tendsto (fun t : ℝ => ‖gaussian δ θ (a + t * I)‖) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have h : Tendsto (fun t : ℝ => δ * ((a - θ) ^ 2 - t ^ 2)) (cocompact ℝ) atBot :=
    ((tendsto_atBot_add_const_left _ ((a - θ) ^ 2)
      (tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot hδ).congr fun t => by
        simp [sub_eq_add_neg]
  have heq : (fun t : ℝ => ‖gaussian δ θ (a + t * I)‖) =
      Real.exp ∘ fun t => δ * ((a - θ) ^ 2 - t ^ 2) := by
    funext t
    simp [norm_gaussian]
  rw [heq]
  exact Real.tendsto_exp_atBot.comp h

/-- The boundary traces of the admissible function `exp (δ (z - θ)²) x`, for `x` in the
intersection. -/
private def gaussianTrace {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    C₀(ℝ, X₀) × C₀(ℝ, X₁) :=
  (⟨⟨fun t => gaussian δ θ (t * I) • C.interFst x,
      ((differentiable_gaussian δ θ).continuous.comp (by fun_prop)).smul continuous_const⟩,
      squeeze_zero_norm (fun t => (norm_smul _ _).le)
        (by simpa using (tendsto_norm_gaussian hδ θ 0).mul_const ‖C.interFst x‖)⟩,
    ⟨⟨fun t => gaussian δ θ (1 + t * I) • C.interSnd x,
      ((differentiable_gaussian δ θ).continuous.comp (by fun_prop)).smul continuous_const⟩,
      squeeze_zero_norm (fun t => (norm_smul _ _).le)
        (by simpa using (tendsto_norm_gaussian hδ θ 1).mul_const ‖C.interSnd x‖)⟩)

private theorem isStripFunction_gaussian {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    C.IsStripFunction (fun z => gaussian δ θ z • C.fstToSum (C.interFst x))
      (C.gaussianTrace hδ θ x) where
  diffContOnCl := ((differentiable_gaussian δ θ).smul_const _).diffContOnCl
  isBounded := by
    refine isBounded_iff_forall_norm_le.2
      ⟨Real.exp (δ * (|θ| + 1) ^ 2) * ‖C.fstToSum (C.interFst x)‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_gaussian_le hδ.le θ hz) (norm_nonneg _)
  apply_mul_I t := by simp [gaussianTrace]
  apply_one_add_mul_I t := by
    simpa [gaussianTrace] using congrArg (gaussian δ θ (1 + t * I) • ·) (C.fstToSum_interFst x)

private theorem gaussianTrace_mem {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    C.gaussianTrace hδ θ x ∈ C.stripTraces :=
  ⟨_, C.isStripFunction_gaussian hδ θ x⟩

omit [ContinuousAdd V] [T1Space V] in
private theorem norm_gaussianTrace_le {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    ‖C.gaussianTrace hδ θ x‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := by
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_,
    (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_⟩
  · refine (norm_smul _ _).trans_le (mul_le_mul (norm_gaussian_le hδ.le θ ?_)
      (C.norm_interFst_le x) (norm_nonneg _) (Real.exp_pos _).le)
    simp
  · refine (norm_smul _ _).trans_le (mul_le_mul (norm_gaussian_le hδ.le θ ?_)
      (C.norm_interSnd_le x) (norm_nonneg _) (Real.exp_pos _).le)
    simp

private theorem stripEval_gaussianTrace {δ : ℝ} (hδ : 0 < δ) {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (x : C.inter) :
    C.stripEval θ ⟨C.gaussianTrace hδ θ x, C.gaussianTrace_mem hδ θ x⟩ =
      C.fstToSum (C.interFst x) := by
  rw [stripEval_apply, stripFunction_eq (C.isStripFunction_gaussian hδ θ x)
    (by simpa using hθ)]
  simp [gaussian]

namespace ComplexMethodSpace

variable {C}

variable (θ : ℝ) in
/-- The inclusion of the intersection `X₀ ∩ X₁` into `[X₀, X₁]_θ`, the class of the admissible
function `exp ((z - θ)²) x`. For `0 ≤ θ ≤ 1` it lies over the inclusion of the intersection into
the sum space (`ComplexMethodSpace.toSum_ofInter`) and does not increase norms
(`ComplexMethodSpace.norm_ofInter_le`). -/
def ofInter : C.inter →L[ℂ] C.ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun x := mk θ ⟨C.gaussianTrace one_pos θ x, C.gaussianTrace_mem one_pos θ x⟩
      map_add' x y := by
        rw [← map_add]
        congr 1
        ext t <;> simp [gaussianTrace, smul_add]
      map_smul' c x := by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext t <;> simp [gaussianTrace, smul_comm (gaussian 1 θ _) c] }
    (Real.exp (1 * (|θ| + 1) ^ 2)) fun x =>
      (norm_mk_le _).trans (C.norm_gaussianTrace_le one_pos θ x)

private theorem ofInter_eq_mk {δ : ℝ} (hδ : 0 < δ) {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : C.inter) :
    ofInter θ x = mk θ ⟨C.gaussianTrace hδ θ x, C.gaussianTrace_mem hδ θ x⟩ :=
  mk_eq_mk_iff.2 <| by
    rw [C.stripEval_gaussianTrace one_pos hθ, C.stripEval_gaussianTrace hδ hθ]

/-- For `0 ≤ θ ≤ 1`, the inclusion of the intersection into `[X₀, X₁]_θ` lies over its inclusion
into the sum space. -/
@[simp]
theorem toSum_ofInter {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : C.inter) :
    toSum (ofInter θ x) = C.fstToSum (C.interFst x) := by
  rw [ofInter_eq_mk one_pos hθ, toSum_mk, C.stripEval_gaussianTrace one_pos hθ]

/-- For `0 ≤ θ ≤ 1`, the intersection embeds into `[X₀, X₁]_θ` without increasing norms:
`‖x‖_θ ≤ max ‖x‖_{X₀} ‖x‖_{X₁}`. -/
theorem norm_ofInter_le {θ : ℝ} (hθ : θ ∈ Icc 0 1) (x : C.inter) : ‖ofInter θ x‖ ≤ ‖x‖ := by
  have key (δ : ℝ) (hδ : 0 < δ) : ‖ofInter θ x‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := by
    rw [ofInter_eq_mk hδ hθ]
    exact (norm_mk_le _).trans (C.norm_gaussianTrace_le hδ θ x)
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖) (𝓝[>] 0) (𝓝 ‖x‖) := by
    have : Continuous fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖x‖ := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- For `0 ≤ θ ≤ 1`, the inclusion of the intersection into `[X₀, X₁]_θ` has operator norm at
most one. -/
theorem opNorm_ofInter_le {θ : ℝ} (hθ : θ ∈ Icc 0 1) :
    ‖(ofInter θ : C.inter →L[ℂ] C.ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_ofInter_le hθ x

/-- For the couple `(X, X)`, the norm of `[X, X]_θ` is the norm of `X`: the inclusion into the sum
space, which is `X`, is an isometry. -/
theorem norm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {θ : ℝ}
    (u : (refl ℂ X).ComplexMethodSpace θ) : ‖u‖ = ‖toSum u‖ := by
  by_cases hθ : θ ∈ Icc 0 1
  · refine le_antisymm ?_ (norm_toSum_le u)
    set x := (refl ℂ X).sumSpaceEmbed (toSum u)
    have hx : (x, x) ∈ (refl ℂ X).inter := by simp
    have hu : ofInter θ ⟨(x, x), hx⟩ = u := by
      ext
      simp [x, toSum_ofInter hθ]
    calc ‖u‖ = ‖ofInter θ ⟨(x, x), hx⟩‖ := by rw [hu]
      _ ≤ ‖(⟨(x, x), hx⟩ : (refl ℂ X).inter)‖ := norm_ofInter_le hθ _
      _ = ‖toSum u‖ := by simp [x, norm_refl_sumSpaceEmbed]
  · simp [eq_zero_of_notMem hθ u]

end ComplexMethodSpace

end Inter

/-! ### Exact interpolation of operators -/

section ScaleFactor

/-- The factor `M₀ ^ (z - 1) * M₁ ^ (-z)`, of modulus `1 / M₀` on the line `re z = 0` and
`1 / M₁` on the line `re z = 1`. -/
private def scaleFactor (M₀ M₁ : ℝ) (z : ℂ) : ℂ :=
  exp ((z - 1) * Real.log M₀ - z * Real.log M₁)

variable {M₀ M₁ : ℝ}

private theorem differentiable_scaleFactor (M₀ M₁ : ℝ) : Differentiable ℂ (scaleFactor M₀ M₁) := by
  unfold scaleFactor
  fun_prop

private theorem norm_scaleFactor (z : ℂ) :
    ‖scaleFactor M₀ M₁ z‖ = Real.exp ((z.re - 1) * Real.log M₀ - z.re * Real.log M₁) := by
  simp [scaleFactor, norm_exp]

private theorem norm_scaleFactor_le {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖scaleFactor M₀ M₁ z‖ ≤ Real.exp (|Real.log M₀| + |Real.log M₁|) := by
  rw [norm_scaleFactor]
  refine Real.exp_le_exp.2 ?_
  have hz' := mem_verticalClosedStrip_iff.1 hz
  nlinarith [hz'.1, hz'.2, neg_abs_le (Real.log M₀), le_abs_self (Real.log M₀),
    neg_abs_le (Real.log M₁), le_abs_self (Real.log M₁), abs_nonneg (Real.log M₀),
    abs_nonneg (Real.log M₁)]

private theorem norm_scaleFactor_mul_I (hM₀ : 0 < M₀) (t : ℝ) :
    ‖scaleFactor M₀ M₁ (t * I)‖ = M₀⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₀]

private theorem norm_scaleFactor_one_add_mul_I (hM₁ : 0 < M₁) (t : ℝ) :
    ‖scaleFactor M₀ M₁ (1 + t * I)‖ = M₁⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₁]

private theorem norm_scaleFactor_mul_rpow (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (θ : ℝ) :
    ‖scaleFactor M₀ M₁ θ‖ * (M₀ ^ (1 - θ) * M₁ ^ θ) = 1 := by
  rw [norm_scaleFactor, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_zero]
  congr 1
  simp only [ofReal_re]
  ring

end ScaleFactor

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace ℂ Y₁] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W]
  [T1Space W] {D : CompatibleCouple ℂ Y₀ Y₁ W}

variable {C} {θ : ℝ}

/-- Multiplying the composite of an admissible function with a map of sum spaces by an entire
function `c` bounded on the strip gives an admissible function, whose traces are those of the
original one transformed pointwise by the restrictions `A₀`, `A₁` and multiplied by `c`. -/
theorem exists_isStripFunction_smul_comp (A : C.SumSpace →L[ℂ] D.SumSpace)
    (A₀ : X₀ →L[ℂ] Y₀) (A₁ : X₁ →L[ℂ] Y₁) (hA₀ : ∀ x, A (C.fstToSum x) = D.fstToSum (A₀ x))
    (hA₁ : ∀ x, A (C.sndToSum x) = D.sndToSum (A₁ x)) {c : ℂ → ℂ} (hc : Differentiable ℂ c)
    {K : ℝ} (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) :
    ∃ g' : C₀(ℝ, Y₀) × C₀(ℝ, Y₁), D.IsStripFunction (fun z => c z • A (F z)) g' ∧
      (∀ t, g'.1 t = c (t * I) • A₀ (g.1 t)) ∧ ∀ t, g'.2 t = c (1 + t * I) • A₁ (g.2 t) := by
  have hK₀ (t : ℝ) : ‖c (t * I)‖ ≤ K := hK _ (by simp)
  have hK₁ (t : ℝ) : ‖c (1 + t * I)‖ ≤ K := hK _ (by simp)
  have hcont₀ : Continuous fun t : ℝ => c (t * I) := hc.continuous.comp (by fun_prop)
  have hcont₁ : Continuous fun t : ℝ => c (1 + t * I) := hc.continuous.comp (by fun_prop)
  refine ⟨(⟨⟨fun t => c (t * I) • A₀ (g.1 t),
      hcont₀.smul (A₀.continuous.comp (map_continuous g.1))⟩, squeeze_zero_norm (a := fun t =>
      K * (‖A₀‖ * ‖g.1 t‖)) (fun t => (norm_smul _ _).trans_le (mul_le_mul (hK₀ t)
        (A₀.le_opNorm _) (norm_nonneg _) ((norm_nonneg _).trans (hK₀ t)))) ?_⟩,
    ⟨⟨fun t => c (1 + t * I) • A₁ (g.2 t),
      hcont₁.smul (A₁.continuous.comp (map_continuous g.2))⟩, squeeze_zero_norm (a := fun t =>
      K * (‖A₁‖ * ‖g.2 t‖)) (fun t => (norm_smul _ _).trans_le (mul_le_mul (hK₁ t)
        (A₁.le_opNorm _) (norm_nonneg _) ((norm_nonneg _).trans (hK₁ t)))) ?_⟩),
    ⟨hc.diffContOnCl.smul (A.differentiable.comp_diffContOnCl hF.diffContOnCl), ?_,
      fun t => ?_, fun t => ?_⟩, fun t => rfl, fun t => rfl⟩
  · simpa using
      ((ZeroAtInftyContinuousMapClass.zero_at_infty g.1).norm.const_mul ‖A₀‖).const_mul K
  · simpa using
      ((ZeroAtInftyContinuousMapClass.zero_at_infty g.2).norm.const_mul ‖A₁‖).const_mul K
  · obtain ⟨M, hM⟩ := hF.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨K * (‖A‖ * M), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hKz := hK z hz
    exact (norm_smul _ _).trans_le (mul_le_mul hKz ((A.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg _)))
      (norm_nonneg _) ((norm_nonneg _).trans hKz))
  · simp [hF.apply_mul_I, hA₀]
  · simp [hF.apply_one_add_mul_I, hA₁]

variable (T₀ : X₀ →L[ℂ] Y₀) (T₁ : X₁ →L[ℂ] Y₁)
  (h : ∀ x : C.inter, D.fstToSum (T₀ (C.interFst x)) = D.sndToSum (T₁ (C.interSnd x)))

/-- The pointwise image of the traces of an admissible function, as needed to define
`stripTracesMap`; `isStripFunction_stripTracesMap` is its public form. -/
private theorem isStripFunction_compLeft (g : C.stripTraces) :
    D.IsStripFunction
      (fun z => C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.stripFunction g z))
      (ZeroAtInftyContinuousMap.compLeft T₀ ⟨_, T₀.le_opNorm⟩ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1,
        ZeroAtInftyContinuousMap.compLeft T₁ ⟨_, T₁.le_opNorm⟩ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2) := by
  obtain ⟨g', hg', h₀, h₁⟩ := exists_isStripFunction_smul_comp
    (C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h) T₀ T₁
    (fun x => C.sumLift_fstToSum _ _ h x) (fun x => C.sumLift_sndToSum _ _ h x) (c := 1)
    (differentiable_const 1) (K := 1) (fun _ _ => by simp) (C.isStripFunction_stripFunction g)
  have hg : g' =
      (ZeroAtInftyContinuousMap.compLeft T₀ ⟨_, T₀.le_opNorm⟩ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1,
        ZeroAtInftyContinuousMap.compLeft T₁ ⟨_, T₁.le_opNorm⟩ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2) :=
    Prod.ext (ZeroAtInftyContinuousMap.ext fun t => by simp [h₀])
      (ZeroAtInftyContinuousMap.ext fun t => by simp [h₁])
  rw [hg] at hg'
  simpa using hg'

/-- The map of boundary traces `(g₀, g₁) ↦ (T₀ ∘ g₀, T₁ ∘ g₁)` induced by continuous linear maps
`T₀`, `T₁` of the endpoints that agree on the intersection. On admissible functions it is the
composition with the map `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` of sum spaces
(`CompatibleCouple.isStripFunction_stripTracesMap`). -/
def stripTracesMap : C.stripTraces →L[ℂ] D.stripTraces :=
  (((ZeroAtInftyContinuousMap.compLeft T₀ ⟨_, T₀.le_opNorm⟩).prodMap
    (ZeroAtInftyContinuousMap.compLeft T₁ ⟨_, T₁.le_opNorm⟩)).comp
      C.stripTraces.subtypeL).codRestrict D.stripTraces fun g =>
    ⟨_, isStripFunction_compLeft T₀ T₁ h g⟩

@[simp]
theorem stripTracesMap_apply_fst (g : C.stripTraces) (t : ℝ) :
    (stripTracesMap T₀ T₁ h g : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).1 t =
      T₀ ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) :=
  ZeroAtInftyContinuousMap.compLeft_apply _ _ _ _

@[simp]
theorem stripTracesMap_apply_snd (g : C.stripTraces) (t : ℝ) :
    (stripTracesMap T₀ T₁ h g : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)).2 t =
      T₁ ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) :=
  ZeroAtInftyContinuousMap.compLeft_apply _ _ _ _

theorem isStripFunction_stripTracesMap (g : C.stripTraces) :
    D.IsStripFunction
      (fun z => C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.stripFunction g z))
      (stripTracesMap T₀ T₁ h g) :=
  isStripFunction_compLeft T₀ T₁ h g

theorem stripTracesMap_id
    (h : ∀ x : C.inter, C.fstToSum (ContinuousLinearMap.id ℂ X₀ (C.interFst x)) =
      C.sndToSum (ContinuousLinearMap.id ℂ X₁ (C.interSnd x))) :
    stripTracesMap (ContinuousLinearMap.id ℂ X₀) (ContinuousLinearMap.id ℂ X₁) h =
      ContinuousLinearMap.id ℂ C.stripTraces :=
  ContinuousLinearMap.ext fun _ => Subtype.ext <| Prod.ext
    (ZeroAtInftyContinuousMap.ext fun _ => by simp) (ZeroAtInftyContinuousMap.ext fun _ => by simp)

section Comp

variable {Z₀ Z₁ U : Type*} [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁]
  [NormedSpace ℂ Z₁] [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U]
  [T1Space U] {E : CompatibleCouple ℂ Z₀ Z₁ U} (S₀ : Y₀ →L[ℂ] Z₀) (S₁ : Y₁ →L[ℂ] Z₁)
  (hS : ∀ x : D.inter, E.fstToSum (S₀ (D.interFst x)) = E.sndToSum (S₁ (D.interSnd x)))
  (hST : ∀ x : C.inter,
    E.fstToSum (S₀.comp T₀ (C.interFst x)) = E.sndToSum (S₁.comp T₁ (C.interSnd x)))

theorem stripTracesMap_comp :
    stripTracesMap (S₀.comp T₀) (S₁.comp T₁) hST =
      (stripTracesMap S₀ S₁ hS).comp (stripTracesMap T₀ T₁ h) :=
  ContinuousLinearMap.ext fun _ => Subtype.ext <| Prod.ext
    (ZeroAtInftyContinuousMap.ext fun _ => by simp) (ZeroAtInftyContinuousMap.ext fun _ => by simp)

end Comp

/-- Evaluation commutes with the map of boundary traces. -/
theorem stripEval_stripTracesMap (z : ℂ) (g : C.stripTraces) :
    D.stripEval z (stripTracesMap T₀ T₁ h g) =
      C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (C.stripEval z g) := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · rw [stripEval_apply, stripFunction_eq (isStripFunction_stripTracesMap T₀ T₁ h g) hz,
      stripEval_apply]
  · simp [D.stripFunction_eq_zero _ hz, C.stripFunction_eq_zero _ hz]

namespace ComplexMethodSpace

variable (θ) in
/-- The map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` induced by continuous linear maps `T₀ : X₀ → Y₀`,
`T₁ : X₁ → Y₁` that agree on the intersection. It lies over the map
`x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` of sum spaces (`ComplexMethodSpace.toSum_map`), and its norm is at most
`M₀ ^ (1 - θ) * M₁ ^ θ` when `M₀`, `M₁` bound `T₀`, `T₁` (`ComplexMethodSpace.norm_map_le`). -/
def map : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ :=
  (C.stripEval θ).ker.liftQL ((mk θ).comp (stripTracesMap T₀ T₁ h)) fun g hg => by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply] at hg ⊢
    rw [← map_zero (mk (C := D) θ), mk_eq_mk_iff, stripEval_stripTracesMap, hg, map_zero,
      map_zero]

@[simp]
theorem map_mk (g : C.stripTraces) :
    map θ T₀ T₁ h (mk θ g) = mk θ (stripTracesMap T₀ T₁ h g) :=
  (rfl)

/-- The induced map lies over the map `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` of sum spaces. -/
@[simp]
theorem toSum_map (u : C.ComplexMethodSpace θ) :
    toSum (map θ T₀ T₁ h u) = C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, toSum_mk, toSum_mk, stripEval_stripTracesMap]

/-- The identity maps of the endpoints induce the identity of `[X₀, X₁]_θ`. -/
theorem map_id
    (h : ∀ x : C.inter, C.fstToSum (ContinuousLinearMap.id ℂ X₀ (C.interFst x)) =
      C.sndToSum (ContinuousLinearMap.id ℂ X₁ (C.interSnd x))) :
    map θ (ContinuousLinearMap.id ℂ X₀) (ContinuousLinearMap.id ℂ X₁) h =
      ContinuousLinearMap.id ℂ (C.ComplexMethodSpace θ) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, stripTracesMap_id, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

section Comp

variable {Z₀ Z₁ U : Type*} [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁]
  [NormedSpace ℂ Z₁] [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U]
  [T1Space U] {E : CompatibleCouple ℂ Z₀ Z₁ U} (S₀ : Y₀ →L[ℂ] Z₀) (S₁ : Y₁ →L[ℂ] Z₁)
  (hS : ∀ x : D.inter, E.fstToSum (S₀ (D.interFst x)) = E.sndToSum (S₁ (D.interSnd x)))
  (hST : ∀ x : C.inter,
    E.fstToSum (S₀.comp T₀ (C.interFst x)) = E.sndToSum (S₁.comp T₁ (C.interSnd x)))

/-- The map induced by composites of maps of the endpoints is the composite of the induced maps. -/
theorem map_comp :
    map θ (S₀.comp T₀) (S₁.comp T₁) hST = (map θ S₀ S₁ hS).comp (map θ T₀ T₁ h) := by
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, stripTracesMap_comp T₀ T₁ h S₀ S₁ hS hST, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, map_mk, map_mk]

end Comp

/-- For `0 ≤ θ ≤ 1`, the induced map commutes with the inclusions of the intersections: it sends
the class of `x ∈ X₀ ∩ X₁` to the class of the element `y ∈ Y₀ ∩ Y₁` with first coordinate
`T₀ x`. -/
theorem map_ofInter (hθ : θ ∈ Icc 0 1) {x : C.inter} {y : D.inter}
    (hy : D.interFst y = T₀ (C.interFst x)) : map θ T₀ T₁ h (ofInter θ x) = ofInter θ y := by
  ext
  rw [toSum_map, toSum_ofInter hθ, toSum_ofInter hθ, hy]
  exact C.sumLift_fstToSum _ _ h _

/-- The image of an admissible function scaled by `scaleFactor M₀ M₁` has traces of norm at most
those of the original one, so the class of `scaleFactor M₀ M₁ θ • map u` has norm at most that of
any representative of `u`. -/
private theorem norm_scaleFactor_smul_map_mk_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀)
    (hM₁ : 0 < M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    (g : C.stripTraces) : ‖scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g)‖ ≤ ‖g‖ := by
  obtain ⟨g', hg', hg'₀, hg'₁⟩ := exists_isStripFunction_smul_comp
    (C.sumLift (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) h) T₀ T₁
    (fun x => C.sumLift_fstToSum _ _ h x) (fun x => C.sumLift_sndToSum _ _ h x)
    (differentiable_scaleFactor M₀ M₁) (fun z hz => norm_scaleFactor_le hz)
    (C.isStripFunction_stripFunction g)
  have hv : mk θ ⟨g', _, hg'⟩ = scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g) :=
    ComplexMethodSpace.ext <| by
      rw [map_smul, toSum_map, toSum_mk, toSum_mk, stripEval_apply, stripEval_apply,
        stripFunction_eq hg' (by simpa using hθ)]
  have hg'g : ‖g'‖ ≤ ‖g‖ := norm_prod_le_iff.2
    ⟨(ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).2 fun t => ?_,
      (ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).2 fun t => ?_⟩
  · rw [← hv]
    exact (norm_mk_le _).trans hg'g
  · rw [hg'₀, norm_smul, norm_scaleFactor_mul_I hM₀, inv_mul_le_iff₀ hM₀]
    exact (h₀ _).trans (mul_le_mul_of_nonneg_left
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_fst_le _)) hM₀.le)
  · rw [hg'₁, norm_smul, norm_scaleFactor_one_add_mul_I hM₁, inv_mul_le_iff₀ hM₁]
    exact (h₁ _).trans (mul_le_mul_of_nonneg_left
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_snd_le _)) hM₁.le)

/-- `ComplexMethodSpace.norm_map_le` for strictly positive bounds. -/
private theorem norm_map_le_of_pos (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.ComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  set K := M₀ ^ (1 - θ) * M₁ ^ θ
  have hKpos : 0 < K := by positivity
  -- every representative `g` of `u` gives `‖map u‖ ≤ K * ‖g‖`; take the infimum over them
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ (div_pos hε hKpos))
  calc ‖map θ T₀ T₁ h (mk θ g)‖
      = K * ‖scaleFactor M₀ M₁ θ • map θ T₀ T₁ h (mk θ g)‖ := by
        rw [norm_smul, ← mul_assoc, mul_comm K, norm_scaleFactor_mul_rpow hM₀ hM₁, one_mul]
    _ ≤ K * (‖mk θ g‖ + ε / K) := mul_le_mul_of_nonneg_left
        ((norm_scaleFactor_smul_map_mk_le T₀ T₁ h hθ hM₀ hM₁ h₀ h₁ g).trans hg.le) hKpos.le
    _ = K * ‖mk θ g‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hKpos.ne']

/-- **Exact interpolation of exponent `θ`.** If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` with
`M₀, M₁ ≥ 0`, the induced map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` satisfies
`‖T u‖_θ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖_θ` for `0 ≤ θ ≤ 1`. -/
theorem norm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.ComplexMethodSpace θ) :
    ‖map θ T₀ T₁ h u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  -- apply the bound for the positive constants `M₀ + ε`, `M₁ + ε` and let `ε → 0`
  have hle (ε : ℝ) (hε : 0 < ε) :
      ‖map θ T₀ T₁ h u‖ ≤ (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖ :=
    norm_map_le_of_pos T₀ T₁ h hθ (by positivity) (by positivity)
      (fun x => (h₀ x).trans (by gcongr; linarith))
      (fun x => (h₁ x).trans (by gcongr; linarith)) u
  have hcont : Continuous fun ε : ℝ => (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * ‖u‖ :=
    (((continuous_const.add continuous_id).rpow_const fun _ => Or.inr (sub_nonneg.2 hθ.2)).mul
      ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hθ.1)).mul continuous_const
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

/-- The operator norm form of `ComplexMethodSpace.norm_map_le`. -/
theorem opNorm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖map θ T₀ T₁ h‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_map_le T₀ T₁ h hθ hM₀ hM₁ h₀ h₁)

/-- **Exact interpolation of exponent `θ`**, in terms of operator norms:
`‖T‖_θ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ` for `0 ≤ θ ≤ 1`. -/
theorem opNorm_map_le_opNorm (hθ : θ ∈ Icc 0 1) :
    ‖map θ T₀ T₁ h‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
  opNorm_map_le T₀ T₁ h hθ (norm_nonneg _) (norm_nonneg _) T₀.le_opNorm T₁.le_opNorm

end ComplexMethodSpace

end Map

end CompatibleCouple

end TauCeti
