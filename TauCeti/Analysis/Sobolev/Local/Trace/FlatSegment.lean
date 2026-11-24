/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.FlatTrace
public import TauCeti.Analysis.Sobolev.Local.HalfPlane
public import TauCeti.Analysis.Sobolev.Local.W1p.HalfDisc
public import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Boundary values on the real axis of local Sobolev maps on half-discs

Let `U = Ω ∩ {0 ≤ im}` be a relatively open subset of the closed upper half-plane and let
`u : ℂ → V` lie in the half-disc class `TauCeti.MemWkpLoc p U 1`, `1 ≤ p < ∞`. The totally real
boundary condition `u(s) ∈ L` for real `s ∈ U`, with `L` a closed real subspace of `V` (for instance
`ℝⁿ ⊆ ℂⁿ`), is a pointwise condition only when `u` has a representative continuous up to the real
axis, as it does for `p > 2` when `V` is finite-dimensional. For `p ≤ 2` it is a condition on
traces. This file states it through the trace on the flat segment of the model half-disc,
`TauCeti.W1p.halfDiscFlatTraceZeroSubmodule`.

For a real point `x` the affine isometry `TauCeti.halfDiscChart x`, `z ↦ (im (z - x), re (z - x))`,
takes the upper half-disc `D_r(x) ∩ {0 < im}` onto the model half-disc `TauCeti.halfDisc r`, whose
first coordinate is the normal one, and the real interval `[x - r, x + r]` onto its flat segment.
The chart geometry is in `TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Complex`.

* `TauCeti.HasZeroRealAxisTrace hp U f` says that a real function `f` has zero trace on the real
  axis inside `U`: for every real point `x` and every `r > 0` with
  `closedBall x r ∩ {0 ≤ im} ⊆ U`, the function `f` transported to `TauCeti.halfDisc r` is
  represented by an element of `W^{1,p}(halfDisc r)` whose trace vanishes on the flat segment.
* `TauCeti.HasRealAxisTraceIn hp U L u`, for `L : ClosedSubmodule ℝ V`, says that the trace of `u`
  on the real axis lies in `L`:
  `ℓ ∘ u` has zero trace for every continuous linear functional `ℓ` vanishing on `L`.

Both conditions pass to smaller sets and only depend on the almost-everywhere class of the map on
`U`; they are closed under the linear operations and under convergence in `W^{1,p}` on compact
subsets of `U` (`TauCeti.HasRealAxisTraceIn.of_tendsto`), which is how a boundary condition
survives a limit. For a representative continuous up to the real axis the condition is the
pointwise condition (`TauCeti.MemWkpLoc.hasRealAxisTraceIn_iff_of_continuousOn`), and for `p > 2`
with finite-dimensional `V`, `TauCeti.halfPlanePreciseRepresentative` is continuous up to the axis
(`TauCeti.MemWkpLoc.hasRealAxisTraceIn_iff_halfPlanePreciseRepresentative`). For `L = ker A` the
condition can be checked on the coordinates of `A ∘ u` in one basis
(`TauCeti.hasRealAxisTraceIn_ker_iff_forall_coord`); for `ℝⁿ ⊆ ℂⁿ` these are the imaginary parts
of the components (`TauCeti.hasRealAxisTraceIn_ker_im_iff`).

## Main declarations

* `TauCeti.HasZeroRealAxisTrace`, `TauCeti.HasRealAxisTraceIn`: the boundary conditions.
* `TauCeti.hasZeroRealAxisTrace_def`, `TauCeti.hasRealAxisTraceIn_def`: their defining conditions.
* `TauCeti.HasRealAxisTraceIn.mono`, `TauCeti.HasRealAxisTraceIn.congr_ae`,
  `TauCeti.HasRealAxisTraceIn.add`, `TauCeti.HasRealAxisTraceIn.const_smul`: the structure.
* `TauCeti.MemWkpLoc.hasRealAxisTraceIn_iff_of_continuousOn`,
  `TauCeti.MemWkpLoc.hasRealAxisTraceIn_iff_halfPlanePreciseRepresentative`: the pointwise reading.
* `TauCeti.HasRealAxisTraceIn.of_tendsto`: closedness under `W^{1,p}_loc` limits up to the axis.
* `TauCeti.hasRealAxisTraceIn_ker_iff_forall_coord`, `TauCeti.hasRealAxisTraceIn_ker_im_iff`:
  the coordinate form.
* `TauCeti.hasZeroRealAxisTrace_im`, `TauCeti.not_hasRealAxisTraceIn_ker_im_const_I`: the
  checks `Im z` has zero trace, and the constant `i` does not satisfy `u ∈ ℝ` on the axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (totally real boundary conditions on the half-disc).
* L. C. Evans, *Partial Differential Equations*, second edition, §5.5.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace Filter Topology Module
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Zero trace of a real function -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)

/-- **Zero trace on the real axis.** A real function `f` has zero trace on the real axis inside
`U ⊆ ℂ` if for every real point `x` and every `r > 0` with `closedBall x r ∩ {0 ≤ im} ⊆ U`, the
transported function `f ∘ (TauCeti.halfDiscChart x)⁻¹` on the model half-disc
`TauCeti.halfDisc r` is represented by an element of `W^{1,p}(halfDisc r)` with zero trace on the
flat segment. -/
def HasZeroRealAxisTrace (U : Set ℂ) (f : ℂ → ℝ) : Prop :=
  ∀ x : ℂ, x.im = 0 → ∀ r : ℝ, 0 < r → closedBall x r ∩ {z | 0 ≤ z.im} ⊆ U →
    ∃ v ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r,
      W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        fun w => f ((halfDiscChart x).symm w)

variable {hp} in
/-- The defining witnesses of zero real-axis trace, without unfolding the predicate. -/
theorem hasZeroRealAxisTrace_def (U : Set ℂ) (f : ℂ → ℝ) :
    HasZeroRealAxisTrace hp U f ↔
      ∀ x : ℂ, x.im = 0 → ∀ r : ℝ, 0 < r → closedBall x r ∩ {z | 0 ≤ z.im} ⊆ U →
        ∃ v ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r,
          W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
            fun w => f ((halfDiscChart x).symm w) :=
  Iff.rfl

variable {hp} {U U' : Set ℂ} {f g : ℂ → ℝ}

/-- Every representative of the transported function on an admissible half-disc has zero trace on
the flat segment. -/
theorem HasZeroRealAxisTrace.mem_of_value_ae_eq (h : HasZeroRealAxisTrace hp U f) {x : ℂ}
    (hx : x.im = 0) {r : ℝ} (hr : 0 < r) (hxr : closedBall x r ∩ {z | 0 ≤ z.im} ⊆ U)
    {v : W1p volume (halfDisc r) p}
    (hv : W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
      fun w => f ((halfDiscChart x).symm w)) :
    v ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r := by
  obtain ⟨v', hv'mem, hv'⟩ := h x hx r hr hxr
  rwa [W1p.ext_value (Lp.ext_iff.2 (hv.trans hv'.symm))]

/-- The zero-trace condition passes to smaller sets. -/
theorem HasZeroRealAxisTrace.mono (h : HasZeroRealAxisTrace hp U' f) (hUU' : U ⊆ U') :
    HasZeroRealAxisTrace hp U f :=
  fun x hx r hr hxr => h x hx r hr (hxr.trans hUU')

/-- The zero-trace condition only depends on the almost-everywhere class of `f` on `U`. -/
theorem HasZeroRealAxisTrace.congr_ae (h : HasZeroRealAxisTrace hp U f)
    (hfg : f =ᵐ[volume.restrict U] g) : HasZeroRealAxisTrace hp U g := by
  intro x hx r hr hxr
  obtain ⟨v, hv, hvf⟩ := h x hx r hr hxr
  exact ⟨v, hv,
    hvf.trans (ae_eq_comp_halfDiscChart_symm hx
      ((coe_upperHalfDisc_subset_closedBall_inter x r).trans hxr) hfg)⟩

/-- The zero function has zero trace. -/
@[simp]
theorem hasZeroRealAxisTrace_zero : HasZeroRealAxisTrace hp U 0 := fun _ _ r _ _ =>
  ⟨0, zero_mem _, by
    rw [W1p.value_zero]
    filter_upwards [Lp.coeFn_zero ℝ p (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))]
      with w hw
    rw [hw]
    rfl⟩

/-- The zero-trace condition is closed under addition. -/
theorem HasZeroRealAxisTrace.add (hf : HasZeroRealAxisTrace hp U f)
    (hg : HasZeroRealAxisTrace hp U g) : HasZeroRealAxisTrace hp U (f + g) := by
  intro x hx r hr hxr
  obtain ⟨v, hv, hvf⟩ := hf x hx r hr hxr
  obtain ⟨v', hv', hvg⟩ := hg x hx r hr hxr
  refine ⟨v + v', add_mem hv hv', ?_⟩
  rw [W1p.value_add]
  filter_upwards [Lp.coeFn_add (W1p.value v) (W1p.value v'), hvf, hvg] with w h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, Pi.add_apply]

/-- The zero-trace condition is closed under real multiples. -/
theorem HasZeroRealAxisTrace.const_smul (hf : HasZeroRealAxisTrace hp U f) (c : ℝ) :
    HasZeroRealAxisTrace hp U (c • f) := by
  intro x hx r hr hxr
  obtain ⟨v, hv, hvf⟩ := hf x hx r hr hxr
  refine ⟨c • v, Submodule.smul_mem _ c hv, ?_⟩
  rw [W1p.value_smul]
  filter_upwards [Lp.coeFn_smul c (W1p.value v), hvf] with w h₁ h₂
  rw [h₁, Pi.smul_apply, h₂, Pi.smul_apply]

/-- The zero-trace condition is closed under finite sums. -/
theorem HasZeroRealAxisTrace.sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℝ}
    (hf : ∀ i ∈ s, HasZeroRealAxisTrace hp U (f i)) :
    HasZeroRealAxisTrace hp U (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ### The pointwise reading for a continuous representative -/

/-- **The pointwise reading of the zero-trace condition.** Let `f ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1`
be real and agree almost everywhere on `Ω ∩ {0 ≤ im}` with a function `g` continuous there. Then
`f` has zero trace on the real axis exactly when `g` vanishes at the real points of `Ω`. -/
theorem MemWkpLoc.hasZeroRealAxisTrace_iff_of_continuousOn {Ω : Opens ℂ}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 f)
    (hg : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hfg : f =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g) :
    HasZeroRealAxisTrace hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) f ↔
      ∀ x ∈ (Ω : Set ℂ), x.im = 0 → g x = 0 := by
  -- On an admissible half-disc, the transported `g` is continuous up to the boundary.
  have key : ∀ x : ℂ, x.im = 0 → ∀ r : ℝ, 0 < r →
      closedBall x r ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} →
      ∀ v : W1p volume (halfDisc r) p,
        W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
          (fun w => f ((halfDiscChart x).symm w)) →
        (v ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
          ∀ y ∈ halfDiscFlatSegment r, g ((halfDiscChart x).symm y) = 0) := by
    intro x hx r hr hxr v hv
    refine W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn hp hr
      (hg.comp (halfDiscChart x).symm.continuous.continuousOn
        ((halfDiscChart_symm_mapsTo_closure hx).mono_right hxr))
      (hv.trans (ae_eq_comp_halfDiscChart_symm hx
        ((coe_upperHalfDisc_subset_closedBall_inter x r).trans hxr) hfg))
  constructor
  · intro h x hxΩ hx
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hxΩ
    have hxr : closedBall x (r / 2) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
      fun z hz => ⟨hrΩ (closedBall_subset_ball (by linarith) hz.1), hz.2⟩
    obtain ⟨v, hv, hvf⟩ := h x hx (r / 2) (by linarith) hxr
    have := (key x hx (r / 2) (by linarith) hxr v hvf).1 hv 0
      (mem_halfDiscFlatSegment.2 ⟨by simp; linarith, rfl⟩)
    rwa [← halfDiscChart_self x, AffineIsometryEquiv.symm_apply_apply] at this
  · intro h x hx r hr hxr
    obtain ⟨v, hv⟩ := hf.exists_w1p_halfDisc hx hxr
    refine ⟨v, (key x hx r hr hxr v hv).2 fun y hy => ?_, hv⟩
    obtain ⟨hy₁, hy₂⟩ := halfDiscChart_symm_mapsTo_flatSegment hx hy
    exact h _ (hxr ⟨hy₁, le_of_eq hy₂.symm⟩).1 hy₂

/-! ### Closedness under `W^{1,p}` limits -/

/-- **The zero-trace condition is closed under `W^{1,p}_loc` limits up to the real axis.** If real
functions `fs n` have zero trace on the real axis inside `U` and converge to `f` in `W^{1,p}(K)` for
every compact `K ⊆ U`, then `f` has zero trace on the real axis inside `U`. -/
theorem HasZeroRealAxisTrace.of_tendsto {fs : ℕ → ℂ → ℝ}
    (hfs : ∀ n, HasZeroRealAxisTrace hp U (fs n))
    (hlim : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      Tendsto (fun n => eLpNormWkp p K 1 (fs n - f)) atTop (𝓝 0)) :
    HasZeroRealAxisTrace hp U f := by
  intro x hx r hr hxr
  choose vs hvs hvsf using fun n => hfs n x hx r hr hxr
  have hK := (isCompact_closedBall x r).inter_right (t := {z : ℂ | 0 ≤ z.im})
    (isClosed_le continuous_const Complex.continuous_im)
  have hD := coe_upperHalfDisc_subset_closedBall_inter x r
  -- A representative of `fs n - f` on the model half-disc, for `n` where its norm is finite.
  have hw : ∀ n, eLpNormWkp p (closedBall x r ∩ {z | 0 ≤ z.im}) 1 (fs n - f) ≠ ∞ →
      ∃ w : W1p volume (halfDisc r) p,
        W1p.value w =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
          (fun y => (fs n - f) ((halfDiscChart x).symm y)) ∧
        ‖w‖ₑ ≤ eLpNormWkp p (closedBall x r ∩ {z | 0 ≤ z.im}) 1 (fs n - f) := fun n hn => by
    obtain ⟨w, hw, hwn⟩ := exists_w1p_halfDisc_enorm_le hx
      (ne_top_of_le_ne_top hn (eLpNormWkp_mono_set hD))
    exact ⟨w, hw, hwn.trans (eLpNormWkp_mono_set hD)⟩
  -- The limit is represented as `vs N - w` for one `N` with finite norm.
  obtain ⟨N, hN⟩ := ((hlim _ hK hxr).eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  obtain ⟨wN, hwN, -⟩ := hw N hN.ne
  set v := vs N - wN
  have hv : W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
      fun y => f ((halfDiscChart x).symm y) := by
    filter_upwards [W1p.value_sub_ae (vs N) wN, hvsf N, hwN] with y h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃, Pi.sub_apply, sub_sub_cancel]
  refine ⟨v, (W1p.isClosed_halfDiscFlatTraceZeroSubmodule hp r).mem_of_tendsto (b := atTop) ?_
    (Eventually.of_forall hvs), hv⟩
  -- `vs n - v` represents `fs n - f`, so its norm is at most the `W^{1,p}` norm of `fs n - f`.
  have hbound : ∀ n, ‖vs n - v‖ₑ ≤ eLpNormWkp p (closedBall x r ∩ {z | 0 ≤ z.im}) 1 (fs n - f) := by
    intro n
    by_cases hfin : eLpNormWkp p (closedBall x r ∩ {z | 0 ≤ z.im}) 1 (fs n - f) = ∞
    · exact hfin ▸ le_top
    obtain ⟨w, hw, hwn⟩ := hw n hfin
    refine le_of_eq_of_le (congrArg _ (W1p.ext_value (Lp.ext_iff.2 ?_))) hwn
    filter_upwards [W1p.value_sub_ae (vs n) v, hvsf n, hv, hw] with y h₁ h₂ h₃ h₄
    rw [h₁, Pi.sub_apply, h₂, h₃, h₄, Pi.sub_apply]
  have hlim' : Tendsto (fun n => ‖vs n - v‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim _ hK hxr)
      (fun _ => zero_le) hbound
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim').congr fun n => ?_)
  exact toReal_eNorm _

/-! ### Boundary values in a real subspace -/

section Subspace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {L : ClosedSubmodule ℝ V} {u u' : ℂ → V}

variable (hp) in
/-- **Boundary values in a real subspace.** The trace on the real axis inside `U ⊆ ℂ` of a map
`u : ℂ → V` lies in the closed real subspace `L` if `ℓ ∘ u` has zero trace on the real axis
(`TauCeti.HasZeroRealAxisTrace`) for every continuous linear functional `ℓ` vanishing on `L`.
Closedness is bundled because continuous annihilating functionals detect only the closure of a
subspace. For `L = ℝⁿ ⊆ ℂⁿ` this is the totally real boundary condition `u(s) ∈ ℝⁿ`
for real `s` (`TauCeti.hasRealAxisTraceIn_ker_im_iff`). -/
def HasRealAxisTraceIn (U : Set ℂ) (L : ClosedSubmodule ℝ V) (u : ℂ → V) : Prop :=
  ∀ ℓ : V →L[ℝ] ℝ, (∀ y ∈ L, ℓ y = 0) → HasZeroRealAxisTrace hp U fun z => ℓ (u z)

/-- The annihilator characterization of real-axis boundary values, without unfolding. -/
theorem hasRealAxisTraceIn_def (U : Set ℂ) (L : ClosedSubmodule ℝ V) (u : ℂ → V) :
    HasRealAxisTraceIn hp U L u ↔
      ∀ ℓ : V →L[ℝ] ℝ, (∀ y ∈ L, ℓ y = 0) →
        HasZeroRealAxisTrace hp U fun z => ℓ (u z) :=
  Iff.rfl

/-- The boundary condition passes to smaller sets. -/
theorem HasRealAxisTraceIn.mono (h : HasRealAxisTraceIn hp U' L u) (hUU' : U ⊆ U') :
    HasRealAxisTraceIn hp U L u :=
  fun ℓ hℓ => (h ℓ hℓ).mono hUU'

/-- The boundary condition only depends on the almost-everywhere class of `u` on `U`. -/
theorem HasRealAxisTraceIn.congr_ae (h : HasRealAxisTraceIn hp U L u)
    (huu' : u =ᵐ[volume.restrict U] u') : HasRealAxisTraceIn hp U L u' :=
  fun ℓ hℓ => (h ℓ hℓ).congr_ae (huu'.fun_comp ℓ)

/-- The zero map has boundary values in every closed subspace. -/
@[simp]
theorem hasRealAxisTraceIn_zero : HasRealAxisTraceIn hp U L (0 : ℂ → V) := fun ℓ _ => by
  convert (hasZeroRealAxisTrace_zero : HasZeroRealAxisTrace hp U 0) using 1
  funext z
  simp

/-- The boundary condition is closed under addition. -/
theorem HasRealAxisTraceIn.add (h : HasRealAxisTraceIn hp U L u)
    (h' : HasRealAxisTraceIn hp U L u') : HasRealAxisTraceIn hp U L (u + u') := fun ℓ hℓ => by
  convert (h ℓ hℓ).add (h' ℓ hℓ) using 1
  funext z
  simp

/-- The boundary condition is closed under real multiples. -/
theorem HasRealAxisTraceIn.const_smul (h : HasRealAxisTraceIn hp U L u) (c : ℝ) :
    HasRealAxisTraceIn hp U L (c • u) := fun ℓ hℓ => by
  convert (h ℓ hℓ).const_smul c using 1
  funext z
  simp

/-- Every map has its boundary values in the whole space. -/
@[simp]
theorem hasRealAxisTraceIn_top : HasRealAxisTraceIn hp U ⊤ u := fun ℓ hℓ => by
  have : (fun z => ℓ (u z)) = 0 := funext fun z => hℓ _ ClosedSubmodule.mem_top
  rw [this]
  exact hasZeroRealAxisTrace_zero

/-- For real functions and `L = 0`, the boundary condition is the zero-trace condition. -/
@[simp]
theorem hasRealAxisTraceIn_bot_iff {f : ℂ → ℝ} :
    HasRealAxisTraceIn hp U ⊥ f ↔ HasZeroRealAxisTrace hp U f := by
  refine ⟨fun h => h (ContinuousLinearMap.id ℝ ℝ) fun y hy => by simpa using hy,
    fun h ℓ _ => ?_⟩
  have : (fun z => ℓ (f z)) = ℓ 1 • f := funext fun z => by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one, mul_comm] using
      (map_smul ℓ (f z) (1 : ℝ))
  rw [this]
  exact h.const_smul _

/-- **The coordinate form for a kernel.** For a continuous linear map `A : V →L[ℝ] W` into a
finite-dimensional space, the boundary values of `u` lie in `ker A` exactly when those of `A ∘ u`
are zero. -/
theorem hasRealAxisTraceIn_ker_iff [FiniteDimensional ℝ W] (A : V →L[ℝ] W) :
    HasRealAxisTraceIn hp U ((⊥ : ClosedSubmodule ℝ W).comap A) u ↔
      HasRealAxisTraceIn hp U ⊥ fun z => A (u z) := by
  refine ⟨fun h μ _ => h (μ.comp A) fun y hy => by
    have hy0 : A y = 0 := ClosedSubmodule.mem_bot.1 (ClosedSubmodule.mem_comap.1 hy)
    simp only [ContinuousLinearMap.comp_apply, hy0, map_zero],
    fun h ℓ hℓ => ?_⟩
  -- A functional vanishing on `ker A` factors through `A`.
  have hmem : (ℓ : V →ₗ[ℝ] ℝ) ∈ (LinearMap.ker (A : V →ₗ[ℝ] W)).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).2 fun y hy => hℓ y
      (ClosedSubmodule.mem_comap.2 (ClosedSubmodule.mem_bot.2 (LinearMap.mem_ker.1 hy)))
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  have hfun : (fun z => ℓ (u z)) = fun z => LinearMap.toContinuousLinearMap μ (A (u z)) :=
    funext fun z => (LinearMap.congr_fun hμ (u z)).symm
  rw [hfun]
  exact h _ fun y hy => by simp [ClosedSubmodule.mem_bot.1 hy]

/-- **The coordinate form for `L = 0`.** A map into a finite-dimensional space has zero boundary
values exactly when each of its coordinates in a basis `b` has zero trace. -/
theorem hasRealAxisTraceIn_bot_iff_forall_coord {ι : Type*} [Finite ι]
    (b : Basis ι ℝ W) {w : ℂ → W} :
    HasRealAxisTraceIn hp U ⊥ w ↔ ∀ i, HasZeroRealAxisTrace hp U fun z => b.coord i (w z) := by
  have := Fintype.ofFinite ι
  have := Module.Finite.of_basis b
  refine ⟨fun h i => h (LinearMap.toContinuousLinearMap (b.coord i)) fun y hy => by
    simp [ClosedSubmodule.mem_bot.1 hy], fun h μ _ => ?_⟩
  have hfun : (fun z => μ (w z)) = ∑ i, μ (b i) • fun z => b.coord i (w z) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr (w z)]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [hfun]
  exact HasZeroRealAxisTrace.sum fun i _ => (h i).const_smul _

/-- **The coordinate form.** For `A : V →L[ℝ] W` and a basis `b` of `W`, the boundary values of
`u` lie in `ker A` exactly when each coordinate of `A ∘ u` in `b` has zero trace. -/
theorem hasRealAxisTraceIn_ker_iff_forall_coord {ι : Type*} [Finite ι]
    (A : V →L[ℝ] W) (b : Basis ι ℝ W) :
    HasRealAxisTraceIn hp U ((⊥ : ClosedSubmodule ℝ W).comap A) u ↔
      ∀ i, HasZeroRealAxisTrace hp U fun z => b.coord i (A (u z)) :=
  have := Module.Finite.of_basis b
  (hasRealAxisTraceIn_ker_iff A).trans (hasRealAxisTraceIn_bot_iff_forall_coord b)

/-- **Check: `ℝⁿ ⊆ ℂⁿ`.** For `L = ℝ^ι ⊆ ℂ^ι`, the kernel of the imaginary parts of the components,
the boundary condition says that the imaginary part of each component of `u` has zero trace. -/
theorem hasRealAxisTraceIn_ker_im_iff {ι : Type*} [Fintype ι] {u : ℂ → ι → ℂ} :
    HasRealAxisTraceIn hp U
        ((⊥ : ClosedSubmodule ℝ (ι → ℝ)).comap (ContinuousLinearMap.pi fun i =>
          Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i))) u ↔
      ∀ i, HasZeroRealAxisTrace hp U fun z => (u z i).im := by
  rw [hasRealAxisTraceIn_ker_iff_forall_coord _ (Pi.basisFun ℝ ι)]
  simp

/-- **The pointwise reading of the boundary condition.** Let `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` take
values in a real normed space and agree almost everywhere on `Ω ∩ {0 ≤ im}` with a map `g`
continuous there. Then the boundary values of `u` lie in `L` exactly when `g x ∈ L` at every real
point `x` of `Ω`. -/
theorem MemWkpLoc.hasRealAxisTraceIn_iff_of_continuousOn {Ω : Opens ℂ}
    {g : ℂ → V} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u)
    (hg : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hug : u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g) :
    HasRealAxisTraceIn hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L u ↔
      ∀ x ∈ (Ω : Set ℂ), x.im = 0 → g x ∈ L := by
  have hscalar : ∀ ℓ : V →L[ℝ] ℝ,
      HasZeroRealAxisTrace hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (fun z => ℓ (u z)) ↔
        ∀ x ∈ (Ω : Set ℂ), x.im = 0 → ℓ (g x) = 0 := fun ℓ =>
    (hu.clm_comp ℓ).hasZeroRealAxisTrace_iff_of_continuousOn (ℓ.continuous.comp_continuousOn hg)
      (hug.fun_comp ℓ)
  refine ⟨fun h x hxΩ hx => ?_, fun h ℓ hℓ => (hscalar ℓ).2 fun x hxΩ hx => hℓ _ (h x hxΩ hx)⟩
  by_contra hgx
  obtain ⟨ℓ, c, hℓL, hcx⟩ :=
    geometric_hahn_banach_closed_point L.toSubmodule.convex L.isClosed hgx
  have hℓzero (y : V) (hy : y ∈ L) : ℓ y = 0 := by
    by_contra hne
    have hb := hℓL (((c + 1) / ℓ y) • y) (L.smul_mem _ hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hb
    linarith
  have htrace := (hscalar ℓ).1 (h ℓ hℓzero) x hxΩ hx
  have hc := hℓL 0 L.zero_mem
  simp only [map_zero] at hc
  linarith

/-- **For `p > 2` the boundary condition is pointwise.** For `2 < p < ∞` and
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` with values in a finite-dimensional space, the boundary values
of `u` lie in `L` exactly when its representative `TauCeti.halfPlanePreciseRepresentative u`,
continuous up to the real axis, takes values in `L` at the real points of `Ω`. -/
theorem MemWkpLoc.hasRealAxisTraceIn_iff_halfPlanePreciseRepresentative [FiniteDimensional ℝ V]
    {Ω : Opens ℂ} (hp2 : 2 < p) (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    HasRealAxisTraceIn hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L u ↔
      ∀ x ∈ (Ω : Set ℂ), x.im = 0 → halfPlanePreciseRepresentative u x ∈ L :=
  hu.hasRealAxisTraceIn_iff_of_continuousOn (hu.continuousOn_halfPlanePreciseRepresentative hp2)
    (hu.ae_eq_halfPlanePreciseRepresentative Fact.out)

/-- **The boundary condition is closed under `W^{1,p}_loc` limits up to the real axis.** If maps
`us n` have boundary values in `L` on the real axis inside `U` and converge to `u` in `W^{1,p}(K)`
for every compact `K ⊆ U`, then the boundary values of `u` lie in `L`. This recovers the boundary
condition of a limit from the trace. -/
theorem HasRealAxisTraceIn.of_tendsto {us : ℕ → ℂ → V}
    (hus : ∀ n, HasRealAxisTraceIn hp U L (us n))
    (hlim : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      Tendsto (fun n => eLpNormWkp p K 1 (us n - u)) atTop (𝓝 0)) :
    HasRealAxisTraceIn hp U L u := by
  refine fun ℓ hℓ => HasZeroRealAxisTrace.of_tendsto (fs := fun n z => ℓ (us n z))
    (fun n => hus n ℓ hℓ) fun K hK hKU => ?_
  have hmul := ENNReal.Tendsto.const_mul (a := ‖ℓ‖ₑ) (hlim K hK hKU) (Or.inr eNorm_ne_top)
  rw [mul_zero] at hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    fun n => ?_
  have : ((fun z => ℓ (us n z)) - fun z => ℓ (u z)) = fun z => ℓ ((us n - u) z) :=
    funext fun z => by simp
  rw [this]
  exact eLpNormWkp_clm_comp_le ℓ

end Subspace

/-! ### Checks -/

/-- **Check: `Im z` has zero trace.** The function `z ↦ Im z` has zero trace on the real axis
inside every `Ω ∩ {0 ≤ im}`, so its boundary values lie in `L = 0`. -/
theorem hasZeroRealAxisTrace_im {Ω : Opens ℂ} :
    HasZeroRealAxisTrace hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Complex.im := by
  have hmem : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 Complex.im :=
    Complex.imCLM.contDiff.contDiffOn.memWkpLoc_inter_setOf_im_nonneg Ω.isOpen
  exact (hmem.hasZeroRealAxisTrace_iff_of_continuousOn Complex.continuous_im.continuousOn
    (ae_eq_refl _)).2 fun _ _ hx => hx

/-- **Check: the constant `i` violates `u ∈ ℝ`.** If `Ω` contains a real point, the constant map
`i` does not have boundary values in `ℝ ⊆ ℂ`, the kernel of the imaginary part. -/
theorem not_hasRealAxisTraceIn_ker_im_const_I {Ω : Opens ℂ} {x : ℂ} (hxΩ : x ∈ Ω)
    (hx : x.im = 0) :
    ¬ HasRealAxisTraceIn hp ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
      ((⊥ : ClosedSubmodule ℝ ℝ).comap Complex.imCLM)
      (fun _ => Complex.I) := by
  have hmem : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 (fun _ : ℂ => Complex.I) :=
    contDiffOn_const.memWkpLoc_inter_setOf_im_nonneg Ω.isOpen
  rw [hmem.hasRealAxisTraceIn_iff_of_continuousOn continuousOn_const (ae_eq_refl _)]
  intro h
  simpa using h x hxΩ hx

end TauCeti
