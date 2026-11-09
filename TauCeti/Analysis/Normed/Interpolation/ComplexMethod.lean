/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Normed.Interpolation.KFunctional
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The complex interpolation method

Let `(X₀, X₁)` be a compatible couple of complex normed spaces. Calderón's space
`𝓕(X₀, X₁)` consists of the bounded functions `f` from the closed strip `0 ≤ re z ≤ 1` to the
sum space `X₀ + X₁` which are continuous on the closed strip and holomorphic inside it, whose
boundary values `t ↦ f (j + t i)` are continuous maps `ℝ → Xⱼ` tending to zero as `|t| → ∞`,
normed by `max (sup_t ‖f (t i)‖_{X₀}) (sup_t ‖f (1 + t i)‖_{X₁})`. For a real `θ`, the complex
interpolation space `[X₀, X₁]_θ` is the image of evaluation at `θ`, with the quotient norm
`‖u‖_θ = inf {‖f‖_𝓕 | f θ = u}`.

By the Hadamard three-lines theorem a function in `𝓕(X₀, X₁)` is determined by its boundary
values, and `‖f z‖ ≤ ‖f (· i)‖ ^ (1 - re z) * ‖f (1 + · i)‖ ^ re z` on the closed strip. We
therefore realise `𝓕(X₀, X₁)` as the submodule `CompatibleCouple.calderonSpace` of pairs
`(g₀, g₁) ∈ C₀(ℝ, X₀) × C₀(ℝ, X₁)` of boundary values of such a function. The product sup
norm of the pair is exactly the norm of Calderón's space, and the function itself is recovered as
`CompatibleCouple.stripExtension`. The interpolation space `CompatibleCouple.ComplexMethodSpace θ`
is the quotient of `calderonSpace` by the kernel of evaluation at `θ`.

## Main declarations

* `CompatibleCouple.IsStripExtension f g`: `f` is bounded, continuous on the closed strip,
  holomorphic inside it, and has boundary values `g`.
* `CompatibleCouple.IsStripExtension.norm_le_rpow_mul_rpow`: the three-lines bound
  `‖f z‖ ≤ ‖g₀‖ ^ (1 - re z) * ‖g₁‖ ^ re z`.
* `CompatibleCouple.calderonSpace`: Calderón's space `𝓕(X₀, X₁)`, a Banach space when `X₀` and
  `X₁` are (`CompatibleCouple.isClosed_calderonSpace`).
* `CompatibleCouple.stripExtension`, `CompatibleCouple.evalStrip`: the holomorphic function with
  given boundary values, and evaluation at a point of the strip as a continuous linear map of
  norm at most one.
* `CompatibleCouple.ComplexMethodSpace θ`: the complex interpolation space `[X₀, X₁]_θ`, a Banach
  space when `X₀` and `X₁` are. Its elements are the values `f θ` of strip extensions
  (`ComplexMethodSpace.exists_toSum_eq_iff`), and `‖u‖_θ` is the infimum of the norms of their
  boundary values (`ComplexMethodSpace.norm_lt_iff`, `ComplexMethodSpace.norm_le_of_toSum_eq`).
* `ComplexMethodSpace.toSum`: the injective inclusion into the sum space, of norm at most one.
* `ComplexMethodSpace.ofInter`: for `0 ≤ θ ≤ 1`, the inclusion of the intersection, of norm at
  most one.
* `ComplexMethodSpace.map`: a linear map `T` of sum spaces restricting to continuous linear maps
  `X₀ →L[ℂ] Y₀` and `X₁ →L[ℂ] Y₁` induces a continuous linear map of the complex interpolation
  spaces, respecting identities and composition. For `0 ≤ θ ≤ 1` and endpoint bounds `M₀`, `M₁`
  it multiplies the norm by at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`ComplexMethodSpace.norm_map_le`,
  `ComplexMethodSpace.opNorm_map_le`): the complex method is an exact interpolation functor of
  exponent `θ`.
* `ComplexMethodSpace.norm_refl`: for the couple `(X, X)`, `[X, X]_θ = X` isometrically.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Lemma 4.1.1 and Theorem 4.1.2).
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
-/

public noncomputable section

open Complex Set Filter Topology
open scoped ZeroAtInfty
open Complex.HadamardThreeLines (verticalStrip verticalClosedStrip)

namespace TauCeti

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Strip extensions -/

/-- `f : ℂ → X₀ + X₁` is a *strip extension* of the pair of boundary values
`g = (g₀, g₁) ∈ C₀(ℝ, X₀) × C₀(ℝ, X₁)`: it is bounded and continuous on the closed strip
`0 ≤ re z ≤ 1`, holomorphic on the open strip, and `f (t i) = g₀ t`, `f (1 + t i) = g₁ t` in the
sum space. Such `f` are the elements of Calderón's space `𝓕(X₀, X₁)`. -/
structure IsStripExtension (f : ℂ → C.SumSpace) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) : Prop where
  diffContOnCl : DiffContOnCl ℂ f (verticalStrip 0 1)
  bddAbove : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)
  apply_mul_I : ∀ t : ℝ, f (t * I) = C.fstToSum (g.1 t)
  apply_one_add_mul_I : ∀ t : ℝ, f (1 + t * I) = C.sndToSum (g.2 t)

namespace IsStripExtension

variable {C} {f f' : ℂ → C.SumSpace} {g g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)}

theorem zero : C.IsStripExtension 0 0 where
  diffContOnCl := diffContOnCl_const
  bddAbove := ⟨0, by rintro _ ⟨z, -, rfl⟩; simp⟩
  apply_mul_I t := by simp
  apply_one_add_mul_I t := by simp

theorem add (hf : C.IsStripExtension f g) (hf' : C.IsStripExtension f' g') :
    C.IsStripExtension (f + f') (g + g') where
  diffContOnCl := hf.diffContOnCl.add hf'.diffContOnCl
  bddAbove := by
    obtain ⟨M, hM⟩ := hf.bddAbove
    obtain ⟨M', hM'⟩ := hf'.bddAbove
    refine ⟨M + M', ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hM ⟨z, hz, rfl⟩) (hM' ⟨z, hz, rfl⟩))
  apply_mul_I t := by simp [hf.apply_mul_I, hf'.apply_mul_I]
  apply_one_add_mul_I t := by simp [hf.apply_one_add_mul_I, hf'.apply_one_add_mul_I]

theorem const_smul (hf : C.IsStripExtension f g) (c : ℂ) :
    C.IsStripExtension (c • f) (c • g) where
  diffContOnCl := hf.diffContOnCl.const_smul c
  bddAbove := by
    obtain ⟨M, hM⟩ := hf.bddAbove
    refine ⟨‖c‖ * M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hM ⟨z, hz, rfl⟩) (norm_nonneg c)
  apply_mul_I t := by simp [hf.apply_mul_I]
  apply_one_add_mul_I t := by simp [hf.apply_one_add_mul_I]

theorem neg (hf : C.IsStripExtension f g) : C.IsStripExtension (-f) (-g) := by
  simpa using hf.const_smul (-1)

theorem sub (hf : C.IsStripExtension f g) (hf' : C.IsStripExtension f' g') :
    C.IsStripExtension (f - f') (g - g') := by
  simpa [sub_eq_add_neg] using hf.add hf'.neg

/-- **Three-lines bound** for strip extensions: on the closed strip,
`‖f z‖ ≤ ‖g₀‖ ^ (1 - re z) * ‖g₁‖ ^ re z`. -/
theorem norm_le_rpow_mul_rpow (hf : C.IsStripExtension f g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖f z‖ ≤ ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re := by
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' zero_lt_one hz
    hf.diffContOnCl hf.bddAbove (a := ‖g.1‖) (b := ‖g.2‖) (fun w hw => ?_) (fun w hw => ?_)
  · simpa using h
  · rw [← re_add_im w, show w.re = 0 from hw, ofReal_zero, zero_add, hf.apply_mul_I]
    exact (C.norm_fstToSum_le _).trans (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _)
  · rw [← re_add_im w, show w.re = 1 from hw, ofReal_one, hf.apply_one_add_mul_I]
    exact (C.norm_sndToSum_le _).trans (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _)

/-- On the closed strip a strip extension is bounded by the norm of its boundary values. -/
theorem norm_le (hf : C.IsStripExtension f g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖f z‖ ≤ ‖g‖ := by
  refine (hf.norm_le_rpow_mul_rpow hz).trans ?_
  have h₁ : ‖g.1‖ ≤ ‖g‖ := norm_fst_le g
  have h₂ : ‖g.2‖ ≤ ‖g‖ := norm_snd_le g
  calc ‖g.1‖ ^ (1 - z.re) * ‖g.2‖ ^ z.re ≤ ‖g‖ ^ (1 - z.re) * ‖g‖ ^ z.re := by
        gcongr
        · exact sub_nonneg.2 hz.2
        · exact hz.1
    _ = ‖g‖ := by
        rw [← Real.rpow_add' (norm_nonneg g) (by simp), sub_add_cancel, Real.rpow_one]

/-- A strip extension is determined on the closed strip by its boundary values. -/
theorem eqOn (hf : C.IsStripExtension f g) (hf' : C.IsStripExtension f' g) :
    EqOn f f' (verticalClosedStrip 0 1) := fun z hz => by
  simpa [sub_eq_zero] using (hf.sub hf').norm_le hz

end IsStripExtension

/-! ### Calderón's space -/

/-- **Calderón's space** `𝓕(X₀, X₁)`, realised as the pairs `(g₀, g₁)` of maps vanishing at
infinity which are the boundary values of a strip extension (`IsStripExtension`). Its norm, the
product sup norm `max (sup ‖g₀‖) (sup ‖g₁‖)`, is the norm of Calderón's space. -/
def calderonSpace : Submodule ℂ (C₀(ℝ, X₀) × C₀(ℝ, X₁)) where
  carrier := {g | ∃ f, C.IsStripExtension f g}
  zero_mem' := ⟨0, .zero⟩
  add_mem' := fun ⟨f, hf⟩ ⟨f', hf'⟩ => ⟨f + f', hf.add hf'⟩
  smul_mem' c _ := fun ⟨f, hf⟩ => ⟨c • f, hf.const_smul c⟩

theorem mem_calderonSpace_iff {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} :
    g ∈ C.calderonSpace ↔ ∃ f, C.IsStripExtension f g :=
  Iff.rfl

/-- The strip extension of an element of Calderón's space, set to zero off the closed strip. -/
def stripExtension (g : C.calderonSpace) : ℂ → C.SumSpace :=
  (verticalClosedStrip 0 1).indicator (Classical.choose g.2)

variable {C}

theorem isStripExtension_stripExtension (g : C.calderonSpace) :
    C.IsStripExtension (C.stripExtension g) g := by
  obtain hf := Classical.choose_spec g.2
  have heq : EqOn (C.stripExtension g) (Classical.choose g.2) (verticalClosedStrip 0 1) :=
    fun z hz => indicator_of_mem hz _
  have hsub : verticalStrip 0 (1 : ℝ) ⊆ verticalClosedStrip 0 1 :=
    preimage_mono Ioo_subset_Icc_self
  refine ⟨⟨hf.diffContOnCl.differentiableOn.congr fun z hz => heq (hsub hz), ?_⟩, ?_, ?_, ?_⟩
  · have hcl : closure (verticalStrip 0 (1 : ℝ)) ⊆ verticalClosedStrip 0 1 :=
      closure_minimal hsub (isClosed_Icc.preimage continuous_re)
    exact hf.diffContOnCl.continuousOn.congr fun z hz => heq (hcl hz)
  · rw [(heq.comp_left (g := norm)).image_eq]
    exact hf.bddAbove
  · intro t
    rw [heq (by simp [verticalClosedStrip]), hf.apply_mul_I]
  · intro t
    rw [heq (by simp [verticalClosedStrip]), hf.apply_one_add_mul_I]

theorem IsStripExtension.eq_stripExtension {f : ℂ → C.SumSpace} {g : C.calderonSpace}
    (hf : C.IsStripExtension f g) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    f z = C.stripExtension g z :=
  hf.eqOn (isStripExtension_stripExtension g) hz

theorem stripExtension_of_notMem (g : C.calderonSpace) {z : ℂ}
    (hz : z ∉ verticalClosedStrip 0 1) : C.stripExtension g z = 0 :=
  indicator_of_notMem hz _

@[simp]
theorem stripExtension_mul_I (g : C.calderonSpace) (t : ℝ) :
    C.stripExtension g (t * I) = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t) :=
  (isStripExtension_stripExtension g).apply_mul_I t

@[simp]
theorem stripExtension_one_add_mul_I (g : C.calderonSpace) (t : ℝ) :
    C.stripExtension g (1 + t * I) = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t) :=
  (isStripExtension_stripExtension g).apply_one_add_mul_I t

theorem norm_stripExtension_le (g : C.calderonSpace) (z : ℂ) :
    ‖C.stripExtension g z‖ ≤ ‖g‖ := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact (isStripExtension_stripExtension g).norm_le hz
  · rw [stripExtension_of_notMem g hz, norm_zero]
    exact norm_nonneg g

@[simp]
theorem stripExtension_add (g g' : C.calderonSpace) :
    C.stripExtension (g + g') = C.stripExtension g + C.stripExtension g' := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact (((isStripExtension_stripExtension g).add
      (isStripExtension_stripExtension g')).eq_stripExtension (g := g + g') hz).symm
  · simp [stripExtension_of_notMem _ hz]

@[simp]
theorem stripExtension_smul (c : ℂ) (g : C.calderonSpace) :
    C.stripExtension (c • g) = c • C.stripExtension g := by
  ext z
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact (((isStripExtension_stripExtension g).const_smul c).eq_stripExtension
      (g := c • g) hz).symm
  · simp [stripExtension_of_notMem _ hz]

variable (C) in
/-- Evaluation of the strip extension at a point `z`, a continuous linear map
`𝓕(X₀, X₁) → X₀ + X₁` of norm at most one. It vanishes for `z` off the closed strip. -/
def evalStrip (z : ℂ) : C.calderonSpace →L[ℂ] C.SumSpace :=
  LinearMap.mkContinuous
    { toFun := fun g => C.stripExtension g z
      map_add' := fun g g' => by simp [stripExtension_add]
      map_smul' := fun c g => by simp [stripExtension_smul] }
    1 fun g => by simpa using norm_stripExtension_le g z

@[simp]
theorem evalStrip_apply (z : ℂ) (g : C.calderonSpace) : C.evalStrip z g = C.stripExtension g z :=
  (rfl)

theorem norm_evalStrip_le (z : ℂ) : ‖C.evalStrip z‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    simpa using norm_stripExtension_le g z

/-- A uniform limit on the closed strip of strip extensions, whose boundary values converge, is a
strip extension of the limit of the boundary values. -/
theorem IsStripExtension.of_tendstoUniformlyOn [CompleteSpace X₀] [CompleteSpace X₁] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → ℂ → C.SumSpace} {Φ : ℂ → C.SumSpace}
    {g : ι → C₀(ℝ, X₀) × C₀(ℝ, X₁)} {g' : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : ∀ i, C.IsStripExtension (F i) (g i)) (hg : Tendsto g l (𝓝 g'))
    (hFΦ : TendstoUniformlyOn F Φ l (verticalClosedStrip 0 1)) : C.IsStripExtension Φ g' := by
  have hsub : verticalStrip 0 (1 : ℝ) ⊆ verticalClosedStrip 0 1 :=
    preimage_mono Ioo_subset_Icc_self
  have hcl : closure (verticalStrip 0 (1 : ℝ)) ⊆ verticalClosedStrip 0 1 :=
    closure_minimal hsub (isClosed_Icc.preimage continuous_re)
  -- the boundary values converge pointwise
  have hbdry₀ : ∀ t, Tendsto (fun i => (g i).1 t) l (𝓝 (g'.1 t)) := fun t => by
    simpa [Function.comp_def] using ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto
      _).comp ((continuous_fst.tendsto g').comp hg)
  have hbdry₁ : ∀ t, Tendsto (fun i => (g i).2 t) l (𝓝 (g'.2 t)) := fun t => by
    simpa [Function.comp_def] using ((ZeroAtInftyContinuousMap.evalCLM ℂ t).continuous.tendsto
      _).comp ((continuous_snd.tendsto g').comp hg)
  refine ⟨⟨?_, ?_⟩, ⟨‖g'‖, ?_⟩, fun t => ?_, fun t => ?_⟩
  · exact (hFΦ.mono hsub).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun i => (hF i).diffContOnCl.differentiableOn)
      (isOpen_Ioo.preimage continuous_re)
  · exact (hFΦ.mono hcl).continuousOn
      (Eventually.of_forall fun i => (hF i).diffContOnCl.continuousOn).frequently
  · rintro _ ⟨z, hz, rfl⟩
    exact le_of_tendsto_of_tendsto' (hFΦ.tendsto_at hz).norm hg.norm fun i => (hF i).norm_le hz
  · refine tendsto_nhds_unique (hFΦ.tendsto_at (by simp [verticalClosedStrip])) ?_
    simp_rw [(hF _).apply_mul_I]
    exact (C.fstToSum.continuous.tendsto _).comp (hbdry₀ t)
  · refine tendsto_nhds_unique (hFΦ.tendsto_at (by simp [verticalClosedStrip])) ?_
    simp_rw [(hF _).apply_one_add_mul_I]
    exact (C.sndToSum.continuous.tendsto _).comp (hbdry₁ t)

variable (C) in
/-- Calderón's space is closed when `X₀` and `X₁` are complete: by the three-lines bound the
strip extensions of a convergent sequence of boundary values converge uniformly on the closed
strip, and the limit is a strip extension (`IsStripExtension.of_tendstoUniformlyOn`). -/
theorem isClosed_calderonSpace [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.calderonSpace : Set (C₀(ℝ, X₀) × C₀(ℝ, X₁))) := by
  refine IsSeqClosed.isClosed fun {g} {g'} hg hlim => ?_
  let G : ℕ → C.calderonSpace := fun n => ⟨g n, hg n⟩
  let F : ℕ → ℂ → C.SumSpace := fun n => C.stripExtension (G n)
  -- the strip extensions are uniformly Cauchy
  have hcauchy : UniformCauchySeqOn F atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn z _ => ?_⟩
    have hmn := norm_stripExtension_le (G m - G n) z
    rw [← evalStrip_apply, map_sub] at hmn
    rw [dist_eq_norm]
    calc ‖F m z - F n z‖ ≤ ‖g m - g n‖ := hmn
      _ ≤ ‖g m - g'‖ + ‖g n - g'‖ := by
          simpa [sub_sub_sub_cancel_right] using norm_sub_le (g m - g') (g n - g')
      _ < ε / 2 + ε / 2 := by
          gcongr
          · simpa [dist_eq_norm] using hN m hm
          · simpa [dist_eq_norm] using hN n hn
      _ = ε := add_halves ε
  choose Φ hΦ using fun z => cauchySeq_tendsto_of_complete (hcauchy.cauchySeq (mem_univ z))
  exact ⟨Φ, .of_tendstoUniformlyOn (fun n => isStripExtension_stripExtension (G n)) hlim
    ((hcauchy.tendstoUniformlyOn_of_tendsto fun z _ => hΦ z).mono (subset_univ _))⟩

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.calderonSpace :=
  (C.isClosed_calderonSpace).completeSpace_coe

/-! ### Gaussian strip functions -/

private theorem re_ofReal_mul_sq (δ c t : ℝ) :
    ((δ : ℂ) * ((c : ℂ) + t * I) ^ 2).re = δ * (c ^ 2 - t ^ 2) := by
  simp only [sq, mul_re, add_re, ofReal_re, ofReal_im, add_im, mul_im, I_re, I_im]
  ring

private theorem norm_exp_ofReal_mul_sq_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (δ c t : ℝ) (x : X) :
    ‖exp ((δ : ℂ) * ((c : ℂ) + t * I) ^ 2) • x‖ = Real.exp (δ * (c ^ 2 - t ^ 2)) * ‖x‖ := by
  rw [norm_smul, norm_exp, re_ofReal_mul_sq]

/-- The map `t ↦ exp (δ (c + t i) ^ 2) • x`, which vanishes at infinity for `δ > 0`. -/
private def gaussianC₀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {δ : ℝ}
    (hδ : 0 < δ) (c : ℝ) (x : X) : C₀(ℝ, X) where
  toFun t := exp ((δ : ℂ) * ((c : ℂ) + t * I) ^ 2) • x
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simp only [norm_exp_ofReal_mul_sq_smul]
    have h : Tendsto (fun t : ℝ => δ * (c ^ 2 - t ^ 2)) (cocompact ℝ) atBot := by
      have ht : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop := by
        refine ((tendsto_pow_atTop two_ne_zero).comp
          (tendsto_norm_cocompact_atTop (E := ℝ))).congr fun t => ?_
        simp [Real.norm_eq_abs, sq_abs]
      exact (tendsto_atBot_add_const_left _ (c ^ 2) (tendsto_neg_atTop_atBot.comp ht)
        |>.const_mul_atBot hδ).congr fun t => by simp [sub_eq_add_neg]
    simpa using (Real.tendsto_exp_atBot.comp h).mul_const ‖x‖

private theorem gaussianC₀_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {δ : ℝ}
    (hδ : 0 < δ) (c : ℝ) (x : X) (t : ℝ) :
    gaussianC₀ hδ c x t = exp ((δ : ℂ) * ((c : ℂ) + t * I) ^ 2) • x :=
  (rfl)

private theorem norm_gaussianC₀_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {δ : ℝ}
    (hδ : 0 < δ) (c : ℝ) (x : X) : ‖gaussianC₀ hδ c x‖ ≤ Real.exp (δ * c ^ 2) * ‖x‖ := by
  refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
  rw [gaussianC₀_apply, norm_exp_ofReal_mul_sq_smul]
  gcongr
  nlinarith [sq_nonneg t]

/-- The function `z ↦ exp (δ (z - θ) ^ 2) • x` is a strip extension of the Gaussian boundary
values of an element `x` of the intersection; it takes the value `x` at `θ`. -/
private theorem isStripExtension_gaussian {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    C.IsStripExtension (fun z => exp ((δ : ℂ) * (z - θ) ^ 2) • C.fstToSum (C.interFst x))
      (gaussianC₀ hδ (-θ) (C.interFst x), gaussianC₀ hδ (1 - θ) (C.interSnd x)) where
  diffContOnCl := (by fun_prop : Differentiable ℂ fun z : ℂ =>
    exp ((δ : ℂ) * (z - θ) ^ 2) • C.fstToSum (C.interFst x)).diffContOnCl
  bddAbove := by
    refine ⟨Real.exp (δ * (1 + |θ|) ^ 2) * ‖C.fstToSum (C.interFst x)‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z - θ = ((z.re - θ : ℝ) : ℂ) + z.im * I := by
      apply Complex.ext <;> simp
    have hre : |z.re - θ| ≤ 1 + |θ| := by
      have := abs_sub (z.re) θ
      rw [abs_of_nonneg hz.1] at this
      linarith [hz.2]
    rw [Function.comp_apply, hz', norm_smul, norm_exp, re_ofReal_mul_sq]
    gcongr
    nlinarith [sq_nonneg z.im, sq_abs (z.re - θ), abs_nonneg (z.re - θ)]
  apply_mul_I t := by
    simp only [gaussianC₀_apply, map_smul]
    congr 3
    push_cast
    ring
  apply_one_add_mul_I t := by
    simp only [gaussianC₀_apply, map_smul, ← C.fstToSum_interFst]
    congr 3
    push_cast
    ring

/-- The Gaussian elements `(t ↦ exp (δ (t i - θ) ^ 2) x, t ↦ exp (δ (1 + t i - θ) ^ 2) x)` of
Calderón's space, for `x` in the intersection. -/
private def gaussianCalderon {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) : C.inter →ₗ[ℂ] C.calderonSpace where
  toFun x := ⟨(gaussianC₀ hδ (-θ) (C.interFst x), gaussianC₀ hδ (1 - θ) (C.interSnd x)),
    ⟨_, C.isStripExtension_gaussian hδ θ x⟩⟩
  map_add' x y := by
    ext t <;> simp [gaussianC₀_apply]
  map_smul' c x := by
    ext t <;> simp [gaussianC₀_apply, smul_comm c]

private theorem norm_gaussianCalderon_le {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (x : C.inter) :
    ‖C.gaussianCalderon hδ θ x‖ ≤ Real.exp (δ * max (θ ^ 2) ((1 - θ) ^ 2)) * ‖x‖ := by
  have hM₀ : Real.exp (δ * (-θ) ^ 2) ≤ Real.exp (δ * max (θ ^ 2) ((1 - θ) ^ 2)) := by
    rw [neg_sq]
    gcongr
    exact le_max_left _ _
  have hM₁ : Real.exp (δ * (1 - θ) ^ 2) ≤ Real.exp (δ * max (θ ^ 2) ((1 - θ) ^ 2)) := by
    gcongr
    exact le_max_right _ _
  rw [← Submodule.norm_coe, norm_prod_le_iff]
  exact ⟨(norm_gaussianC₀_le hδ (-θ) (C.interFst x)).trans
      (mul_le_mul hM₀ (C.norm_interFst_le x) (norm_nonneg _) (Real.exp_pos _).le),
    (norm_gaussianC₀_le hδ (1 - θ) (C.interSnd x)).trans
      (mul_le_mul hM₁ (C.norm_interSnd_le x) (norm_nonneg _) (Real.exp_pos _).le)⟩

private theorem stripExtension_gaussianCalderon {δ : ℝ} (hδ : 0 < δ) {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    (x : C.inter) : C.stripExtension (C.gaussianCalderon hδ θ x) θ = C.fstToSum (C.interFst x) := by
  rw [← (C.isStripExtension_gaussian hδ θ x).eq_stripExtension (g := C.gaussianCalderon hδ θ x)
    (by simpa [verticalClosedStrip] using hθ)]
  simp

/-! ### The complex interpolation space -/

variable (C) in
/-- The kernel of evaluation at `θ` on Calderón's space: the elements whose strip extension
vanishes at `θ`. -/
def complexMethodKer (θ : ℝ) : Submodule ℂ C.calderonSpace :=
  (C.evalStrip θ).ker

theorem mem_complexMethodKer_iff {θ : ℝ} {g : C.calderonSpace} :
    g ∈ C.complexMethodKer θ ↔ C.stripExtension g θ = 0 :=
  Iff.rfl

instance (θ : ℝ) : IsClosed (C.complexMethodKer θ : Set C.calderonSpace) :=
  (C.evalStrip θ).isClosed_ker

variable (C) in
/-- The **complex interpolation space** `[X₀, X₁]_θ`: the quotient of Calderón's space by the
kernel of evaluation at `θ`. Its elements are the values at `θ` of strip extensions
(`ComplexMethodSpace.exists_toSum_eq_iff`), with the norm
`‖u‖_θ = inf {‖g‖ | g ∈ 𝓕(X₀, X₁), g(θ) = u}`. It is a Banach space when `X₀` and `X₁` are.
The interesting range is `0 < θ < 1`; the results below assume `0 ≤ θ ≤ 1` where needed. -/
def ComplexMethodSpace (θ : ℝ) : Type _ :=
  C.calderonSpace ⧸ C.complexMethodKer θ

namespace ComplexMethodSpace

variable {θ : ℝ}

instance : NormedAddCommGroup (C.ComplexMethodSpace θ) :=
  inferInstanceAs (NormedAddCommGroup (C.calderonSpace ⧸ C.complexMethodKer θ))

instance : NormedSpace ℂ (C.ComplexMethodSpace θ) :=
  inferInstanceAs (NormedSpace ℂ (C.calderonSpace ⧸ C.complexMethodKer θ))

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace (C.ComplexMethodSpace θ) :=
  inferInstanceAs (CompleteSpace (C.calderonSpace ⧸ C.complexMethodKer θ))

variable (θ) in
/-- The class in `[X₀, X₁]_θ` of an element of Calderón's space. -/
def mk : C.calderonSpace →L[ℂ] C.ComplexMethodSpace θ :=
  (C.complexMethodKer θ).mkQL

theorem mk_surjective : Function.Surjective (mk (C := C) θ) :=
  (C.complexMethodKer θ).mkQ_surjective

theorem mk_eq_zero_iff {g : C.calderonSpace} : mk θ g = 0 ↔ C.stripExtension g θ = 0 :=
  Submodule.Quotient.mk_eq_zero _

/-- The inclusion `[X₀, X₁]_θ → X₀ + X₁`, sending the class of `g` to the value at `θ` of its
strip extension. -/
def toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace :=
  (C.complexMethodKer θ).liftQL (C.evalStrip θ) le_rfl

@[simp]
theorem toSum_mk (g : C.calderonSpace) : toSum (mk θ g) = C.stripExtension g θ :=
  (rfl)

theorem toSum_injective : Function.Injective (toSum : C.ComplexMethodSpace θ → C.SumSpace) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Two elements of `[X₀, X₁]_θ` agree as soon as their images in the sum space do. -/
@[ext]
theorem ext {u v : C.ComplexMethodSpace θ} (h : toSum u = toSum v) : u = v :=
  toSum_injective h

/-- The norm of `[X₀, X₁]_θ` is the infimum of the norms of the representatives in Calderón's
space: strict upper bounds. -/
theorem norm_lt_iff {u : C.ComplexMethodSpace θ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ g, mk θ g = u ∧ ‖g‖ < r :=
  QuotientAddGroup.norm_lt_iff

theorem norm_mk_le (g : C.calderonSpace) : ‖mk θ g‖ ≤ ‖g‖ :=
  Submodule.Quotient.norm_mk_le _ g

/-- The inclusion into the sum space has norm at most one. -/
theorem norm_toSum_le (u : C.ComplexMethodSpace θ) : ‖toSum u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  simpa using (norm_stripExtension_le g θ).trans_lt hg

theorem opNorm_toSum_le : ‖(toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by simpa using norm_toSum_le u

/-- For `0 ≤ θ ≤ 1`, the elements of `[X₀, X₁]_θ`, viewed in the sum space, are exactly the values
at `θ` of strip extensions. -/
theorem exists_toSum_eq_iff (hθ : θ ∈ Icc 0 1) {v : C.SumSpace} :
    (∃ u : C.ComplexMethodSpace θ, toSum u = v) ↔
      ∃ f g, C.IsStripExtension f g ∧ f θ = v := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨g, rfl⟩ := mk_surjective u
    exact ⟨_, _, isStripExtension_stripExtension g, (toSum_mk g).symm⟩
  · rintro ⟨f, g, hf, rfl⟩
    exact ⟨mk θ ⟨g, f, hf⟩,
      (hf.eq_stripExtension (g := ⟨g, f, hf⟩) (by simpa [verticalClosedStrip] using hθ)).symm⟩

/-- For `0 ≤ θ ≤ 1`, a strip extension `f` with boundary values `g` and `f θ = u` bounds the norm
of `u` by the sup norm of `g`. -/
theorem norm_le_of_toSum_eq (hθ : θ ∈ Icc 0 1) {u : C.ComplexMethodSpace θ}
    {f : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hf : C.IsStripExtension f g)
    (hu : toSum u = f θ) : ‖u‖ ≤ ‖g‖ := by
  have : u = mk θ ⟨g, f, hf⟩ := ext <| hu.trans
    (hf.eq_stripExtension (g := ⟨g, f, hf⟩) (by simpa [verticalClosedStrip] using hθ))
  exact this ▸ norm_mk_le _

variable (θ) in
/-- The inclusion `X₀ ∩ X₁ → [X₀, X₁]_θ`, sending `x` to the class of the Gaussian strip function
`z ↦ exp ((z - θ) ^ 2) x`. For `0 ≤ θ ≤ 1` it lies over the inclusion of the intersection into the
sum (`toSum_ofInter`) and has norm at most one (`norm_ofInter_le`). -/
def ofInter : C.inter →L[ℂ] C.ComplexMethodSpace θ :=
  LinearMap.mkContinuous ((mk θ).toLinearMap ∘ₗ C.gaussianCalderon one_pos θ)
    (Real.exp (1 * max (θ ^ 2) ((1 - θ) ^ 2))) fun x =>
      (norm_mk_le _).trans (C.norm_gaussianCalderon_le one_pos θ x)

theorem toSum_ofInter (hθ : θ ∈ Icc 0 1) (x : C.inter) :
    toSum (ofInter θ x) = C.fstToSum (C.interFst x) :=
  C.stripExtension_gaussianCalderon one_pos hθ x

/-- For `0 ≤ θ ≤ 1`, the inclusion of the intersection has norm at most one: `‖x‖_θ ≤ ‖x‖`. -/
theorem norm_ofInter_le (hθ : θ ∈ Icc 0 1) (x : C.inter) : ‖ofInter θ x‖ ≤ ‖x‖ := by
  set M := max (θ ^ 2) ((1 - θ) ^ 2)
  -- the Gaussian with any width `δ > 0` represents the same class
  have h : ∀ δ > 0, ‖ofInter θ x‖ ≤ Real.exp (δ * M) * ‖x‖ := fun δ hδ => by
    have : ofInter θ x = mk θ (C.gaussianCalderon hδ θ x) :=
      ext <| by rw [toSum_ofInter hθ, toSum_mk, C.stripExtension_gaussianCalderon hδ hθ]
    exact this ▸ (norm_mk_le _).trans (C.norm_gaussianCalderon_le hδ θ x)
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * M) * ‖x‖) (𝓝[>] 0) (𝓝 ‖x‖) := by
    have : Continuous fun δ : ℝ => Real.exp (δ * M) * ‖x‖ := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => h δ hδ)

theorem opNorm_ofInter_le (hθ : θ ∈ Icc 0 1) :
    ‖(ofInter θ : C.inter →L[ℂ] C.ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_ofInter_le hθ x

/-- For the couple `(X, X)` and `0 ≤ θ ≤ 1`, the complex interpolation norm is the norm of `X`:
`[X, X]_θ = X` isometrically. -/
theorem norm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (hθ : θ ∈ Icc 0 1)
    (u : (refl ℂ X).ComplexMethodSpace θ) : ‖u‖ = ‖(refl ℂ X).sumSpaceEmbed (toSum u)‖ := by
  set v := (refl ℂ X).sumSpaceEmbed (toSum u)
  let x : (refl ℂ X).inter := ⟨(v, v), (refl ℂ X).mem_inter_iff.2 (by simp)⟩
  have hx : ofInter θ x = u := ext <| by
    rw [toSum_ofInter hθ, interFst_apply]
    exact refl_fstToSum_sumSpaceEmbed (toSum u)
  refine le_antisymm ?_ ?_
  · calc ‖u‖ = ‖ofInter θ x‖ := by rw [hx]
      _ ≤ ‖x‖ := norm_ofInter_le hθ x
      _ = ‖v‖ := by rw [norm_refl_inter, interFst_apply]
  · rw [norm_refl_sumSpaceEmbed]
    exact norm_toSum_le u

section Map

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W}
  (T : C.SumSpace →ₗ[ℂ] D.SumSpace) {T₀ : X₀ →L[ℂ] Y₀} {T₁ : X₁ →L[ℂ] Y₁}
  (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
  (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))

/-- Postcomposition of maps vanishing at infinity with a continuous linear map. -/
private abbrev compLeftC₀ {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (A : X →L[ℂ] Y) : C₀(ℝ, X) →L[ℂ] C₀(ℝ, Y) :=
  ZeroAtInftyContinuousMap.compLeft A ⟨‖A‖, A.le_opNorm⟩

private theorem compLeftC₀_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (A : X →L[ℂ] Y) (g : C₀(ℝ, X)) (t : ℝ) :
    compLeftC₀ A g t = A (g t) :=
  ZeroAtInftyContinuousMap.compLeft_apply _ _ _ _

private theorem norm_exp_sub_mul_I_mul (a L t : ℝ) :
    ‖exp (((a : ℂ) - t * I) * L)‖ = Real.exp (a * L) := by
  rw [norm_exp]
  simp

/-- The map `t ↦ exp ((a - t i) L) • g t` vanishing at infinity. -/
private def twistC₀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (a L : ℝ)
    (g : C₀(ℝ, X)) : C₀(ℝ, X) where
  toFun t := exp (((a : ℂ) - t * I) * L) • g t
  continuous_toFun := by
    have := map_continuous g
    fun_prop
  zero_at_infty' := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simp only [norm_smul, norm_exp_sub_mul_I_mul]
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty g)).const_mul
      (Real.exp (a * L))

private theorem twistC₀_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (a L : ℝ)
    (g : C₀(ℝ, X)) (t : ℝ) : twistC₀ a L g t = exp (((a : ℂ) - t * I) * L) • g t :=
  (rfl)

private theorem norm_twistC₀_compLeftC₀_le {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (a L : ℝ) (A : X →L[ℂ] Y)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ x, ‖A x‖ ≤ M * ‖x‖) (g : C₀(ℝ, X)) :
    ‖twistC₀ a L (compLeftC₀ A g)‖ ≤ Real.exp (a * L) * M * ‖g‖ := by
  refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_
  rw [twistC₀_apply, compLeftC₀_apply, norm_smul, norm_exp_sub_mul_I_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((h _).trans (mul_le_mul_of_nonneg_left
    (ZeroAtInftyContinuousMap.norm_coe_le_norm _ t) hM)) (Real.exp_pos _).le

/-- Multiplying a strip extension by `exp ((θ - z) L)` twists its boundary values by phases of
constant modulus `exp (θ L)` and `exp ((θ - 1) L)`, and does not change its value at `θ`. -/
private theorem isStripExtension_twist {f : ℂ → D.SumSpace}
    {g : C₀(ℝ, Y₀) × C₀(ℝ, Y₁)} (hf : D.IsStripExtension f g) (θ L : ℝ) :
    D.IsStripExtension (fun z => exp (((θ : ℂ) - z) * L) • f z)
      (twistC₀ θ L g.1, twistC₀ (θ - 1) L g.2) where
  diffContOnCl := (by fun_prop : Differentiable ℂ fun z : ℂ =>
    exp (((θ : ℂ) - z) * L)).diffContOnCl.smul hf.diffContOnCl
  bddAbove := by
    obtain ⟨B, hB⟩ := hf.bddAbove
    refine ⟨Real.exp ((|θ| + 1) * |L|) * B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hre : (((θ : ℂ) - z) * L).re ≤ (|θ| + 1) * |L| := by
      have hz' : |θ - z.re| ≤ |θ| + 1 := by
        have := abs_sub θ z.re
        rw [abs_of_nonneg hz.1] at this
        linarith [hz.2]
      calc (((θ : ℂ) - z) * L).re = (θ - z.re) * L := by simp
        _ ≤ |θ - z.re| * |L| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ (|θ| + 1) * |L| := by gcongr
    rw [Function.comp_apply, norm_smul, norm_exp]
    exact mul_le_mul (Real.exp_le_exp.2 hre) (hB ⟨z, hz, rfl⟩) (norm_nonneg _)
      (Real.exp_pos _).le
  apply_mul_I t := by rw [hf.apply_mul_I, twistC₀_apply, map_smul]
  apply_one_add_mul_I t := by
    rw [hf.apply_one_add_mul_I, twistC₀_apply, map_smul]
    congr 3
    push_cast
    ring

include hT₀ hT₁

private theorem norm_map_sumSpace_le_max (u : C.SumSpace) :
    ‖T u‖ ≤ (max ‖T₀‖ ‖T₁‖ + 1) * ‖u‖ :=
  norm_map_sumSpace_le T hT₀ hT₁ (by positivity)
    (fun x => (T₀.le_opNorm x).trans (by gcongr; linarith [le_max_left ‖T₀‖ ‖T₁‖]))
    (fun x => (T₁.le_opNorm x).trans (by gcongr; linarith [le_max_right ‖T₀‖ ‖T₁‖])) u

/-- A linear map of sum spaces restricting to continuous linear maps of the endpoints, as a
continuous linear map. -/
private def sumCLM : C.SumSpace →L[ℂ] D.SumSpace :=
  T.mkContinuous _ (norm_map_sumSpace_le_max T hT₀ hT₁)

private theorem sumCLM_apply (u : C.SumSpace) : sumCLM T hT₀ hT₁ u = T u :=
  (rfl)

/-- Composing a strip extension with a map of couples gives a strip extension. -/
private theorem isStripExtension_sumCLM_comp {f : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hf : C.IsStripExtension f g) :
    D.IsStripExtension (sumCLM T hT₀ hT₁ ∘ f) (compLeftC₀ T₀ g.1, compLeftC₀ T₁ g.2) where
  diffContOnCl := (sumCLM T hT₀ hT₁).differentiable.comp_diffContOnCl hf.diffContOnCl
  bddAbove := by
    obtain ⟨B, hB⟩ := hf.bddAbove
    refine ⟨‖sumCLM T hT₀ hT₁‖ * B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact ((sumCLM T hT₀ hT₁).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hB ⟨z, hz, rfl⟩) (norm_nonneg _))
  apply_mul_I t := by
    rw [Function.comp_apply, hf.apply_mul_I, sumCLM_apply, hT₀, compLeftC₀_apply]
  apply_one_add_mul_I t := by
    rw [Function.comp_apply, hf.apply_one_add_mul_I, sumCLM_apply, hT₁, compLeftC₀_apply]

omit hT₀ hT₁ in
private theorem norm_compLeftC₀_prod_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) :
    ‖(compLeftC₀ T₀ g.1, compLeftC₀ T₁ g.2)‖ ≤ max ‖T₀‖ ‖T₁‖ * ‖g‖ := by
  rw [norm_prod_le_iff]
  exact ⟨(ZeroAtInftyContinuousMap.norm_compLeft_apply_le T₀ (norm_nonneg _) T₀.le_opNorm _).trans
      (mul_le_mul (le_max_left _ _) (norm_fst_le g) (norm_nonneg _) (by positivity)),
    (ZeroAtInftyContinuousMap.norm_compLeft_apply_le T₁ (norm_nonneg _) T₁.le_opNorm _).trans
      (mul_le_mul (le_max_right _ _) (norm_snd_le g) (norm_nonneg _) (by positivity))⟩

/-- The map of Calderón's spaces induced by a map of couples: `(g₀, g₁) ↦ (T₀ ∘ g₀, T₁ ∘ g₁)`. -/
private def calderonMap : C.calderonSpace →L[ℂ] D.calderonSpace :=
  LinearMap.mkContinuous
    { toFun g := ⟨(compLeftC₀ T₀ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1,
          compLeftC₀ T₁ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2),
        ⟨_, isStripExtension_sumCLM_comp T hT₀ hT₁ (isStripExtension_stripExtension g)⟩⟩
      map_add' g g' := by
        ext t <;> simp
      map_smul' c g := by
        ext t <;> simp }
    (max ‖T₀‖ ‖T₁‖) fun g => norm_compLeftC₀_prod_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))

private theorem stripExtension_calderonMap (g : C.calderonSpace) (z : ℂ) :
    D.stripExtension (calderonMap T hT₀ hT₁ g) z = T (C.stripExtension g z) := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · exact ((isStripExtension_sumCLM_comp T hT₀ hT₁
      (isStripExtension_stripExtension g)).eq_stripExtension (g := calderonMap T hT₀ hT₁ g)
      hz).symm
  · rw [stripExtension_of_notMem _ hz, stripExtension_of_notMem _ hz, map_zero]

/-- The continuous linear map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` induced by a linear map `T` of sum spaces
that restricts to continuous linear maps `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁`. It lies over
`T` (`toSum_map`), and for `0 ≤ θ ≤ 1` and endpoint bounds `M₀`, `M₁` it multiplies the norm by at
most `M₀ ^ (1 - θ) * M₁ ^ θ` (`norm_map_le`). -/
def map : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ :=
  (C.complexMethodKer θ).liftQL ((mk θ).comp (calderonMap T hT₀ hT₁)) fun g hg => by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      mk_eq_zero_iff, stripExtension_calderonMap, mem_complexMethodKer_iff.1 hg, map_zero]

private theorem map_mk (g : C.calderonSpace) :
    map (θ := θ) T hT₀ hT₁ (mk θ g) = mk θ (calderonMap T hT₀ hT₁ g) :=
  (rfl)

@[simp]
theorem toSum_map (u : C.ComplexMethodSpace θ) : toSum (map T hT₀ hT₁ u) = T (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [map_mk, toSum_mk, toSum_mk, stripExtension_calderonMap]

/-- **Exactness of the complex method.** For `0 ≤ θ ≤ 1`, if `‖T₀ x‖ ≤ M₀ ‖x‖` and
`‖T₁ x‖ ≤ M₁ ‖x‖` for positive `M₀`, `M₁`, the induced map multiplies the norm by at most
`M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem norm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.ComplexMethodSpace θ) :
    ‖map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  -- the twist `exp ((θ - z) L)` turns the endpoint bounds `M₀`, `M₁` into the common bound `K`
  have hK₀ : Real.exp (θ * (Real.log M₁ - Real.log M₀)) * M₀ = M₀ ^ (1 - θ) * M₁ ^ θ := by
    rw [Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add]
    conv_lhs => rw [← Real.exp_log hM₀, ← Real.exp_add]
    rw [Real.log_exp]
    ring_nf
  have hK₁ : Real.exp ((θ - 1) * (Real.log M₁ - Real.log M₀)) * M₁ = M₀ ^ (1 - θ) * M₁ ^ θ := by
    rw [Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add]
    conv_lhs => rw [← Real.exp_log hM₁, ← Real.exp_add]
    rw [Real.log_exp]
    ring_nf
  set K := M₀ ^ (1 - θ) * M₁ ^ θ
  set L := Real.log M₁ - Real.log M₀
  refine le_of_forall_gt fun r hr => ?_
  -- choose a representative `g` of `u`, push it forward and twist it by `exp ((θ - z) L)`
  have hKpos : 0 < K := by positivity
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 ((lt_div_iff₀' hKpos).2 hr)
  have hf := isStripExtension_twist
    (isStripExtension_sumCLM_comp T hT₀ hT₁ (isStripExtension_stripExtension g)) θ L
  have hb : ‖((twistC₀ θ L (compLeftC₀ T₀ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1),
      twistC₀ (θ - 1) L (compLeftC₀ T₁ (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2)) :
        C₀(ℝ, Y₀) × C₀(ℝ, Y₁))‖ ≤ K * ‖g‖ := by
    rw [norm_prod_le_iff]
    exact ⟨(norm_twistC₀_compLeftC₀_le θ L T₀ hM₀.le h₀ _).trans
        (by rw [hK₀]; gcongr; exact norm_fst_le _),
      (norm_twistC₀_compLeftC₀_le (θ - 1) L T₁ hM₁.le h₁ _).trans
        (by rw [hK₁]; gcongr; exact norm_snd_le _)⟩
  have hval : toSum (map T hT₀ hT₁ (mk θ g)) =
      exp (((θ : ℂ) - θ) * L) • (sumCLM T hT₀ hT₁ ∘ C.stripExtension g) θ := by
    simp [sumCLM_apply]
  calc ‖map T hT₀ hT₁ (mk θ g)‖ ≤ K * ‖g‖ := (norm_le_of_toSum_eq hθ hf hval).trans hb
    _ < K * (r / K) := by gcongr
    _ = r := mul_div_cancel₀ r hKpos.ne'

/-- **Exactness of the complex method.** For `0 ≤ θ ≤ 1`, if `‖T₀ x‖ ≤ M₀ ‖x‖` and
`‖T₁ x‖ ≤ M₁ ‖x‖` for positive `M₀`, `M₁`, the induced map has norm at most
`M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem opNorm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖(map T hT₀ hT₁ : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_map_le T hT₀ hT₁ hθ hM₀ hM₁ h₀ h₁)

end Map

/-- The identity of the couple induces the identity of the complex interpolation space. -/
theorem map_id :
    map (θ := θ) (LinearMap.id : C.SumSpace →ₗ[ℂ] C.SumSpace)
      (T₀ := ContinuousLinearMap.id ℂ X₀) (T₁ := ContinuousLinearMap.id ℂ X₁)
      (fun _ => rfl) (fun _ => rfl) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun u => ext (toSum_map _ _ _ u)

variable {Y₀ Y₁ W Z₀ Z₁ U : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁] [NormedSpace ℂ Z₁]
  [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U] [T1Space U]
  {D : CompatibleCouple ℂ Y₀ Y₁ W} {E : CompatibleCouple ℂ Z₀ Z₁ U} in
/-- The map induced by a composite of maps of couples is the composite of the induced maps. -/
theorem map_comp (S : D.SumSpace →ₗ[ℂ] E.SumSpace) (T : C.SumSpace →ₗ[ℂ] D.SumSpace)
    {S₀ : Y₀ →L[ℂ] Z₀} {S₁ : Y₁ →L[ℂ] Z₁} {T₀ : X₀ →L[ℂ] Y₀} {T₁ : X₁ →L[ℂ] Y₁}
    (hS₀ : ∀ y, S (D.fstToSum y) = E.fstToSum (S₀ y))
    (hS₁ : ∀ y, S (D.sndToSum y) = E.sndToSum (S₁ y))
    (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) :
    map (θ := θ) (S ∘ₗ T) (T₀ := S₀.comp T₀) (T₁ := S₁.comp T₁)
        (fun x => by simp [hT₀, hS₀]) (fun x => by simp [hT₁, hS₁]) =
      (map S hS₀ hS₁).comp (map T hT₀ hT₁) :=
  ContinuousLinearMap.ext fun u => ext <| by
    rw [toSum_map, ContinuousLinearMap.comp_apply, toSum_map, toSum_map, LinearMap.comp_apply]

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
