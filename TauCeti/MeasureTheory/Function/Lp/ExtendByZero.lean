/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Restrict
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Extension by zero between restricted `Lᵖ` spaces

An `Lᵖ` function on a null-measurable set `s` extends by zero to any larger set `t ⊇ s`, and the
extension has the *same* `Lᵖ` norm, because the added region contributes nothing.  This file
bundles that extension as a linear isometry

`TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs hst : Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t)`,

together with the almost-everywhere description of its values, `TauCeti.coeFn_extendByZeroLpₗᵢ`.

The one point that needs care is that `Lᵖ` elements are equivalence classes: `s.indicator ⇑f`
depends on the chosen representative `⇑f`, which is only pinned down `μ.restrict s`-almost
everywhere, whereas the answer must be pinned down `μ.restrict t`-almost everywhere.
`MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq₀` reconciles the two: an identity holding
`μ.restrict s`-almost everywhere survives multiplication by the indicator of `s` as an identity
against `μ`, hence against every restriction of `μ`.

## Main declarations

* `TauCeti.extendByZeroLpₗᵢ`: extension by zero as a linear isometry.
* `TauCeti.coeFn_extendByZeroLpₗᵢ` and `TauCeti.coeFn_extendByZeroLpₗᵢ_restrict`: the values of
  the extension, on `t` and back on `s`.
* `TauCeti.ae_extendByZeroLpₗᵢ_eq_of_mem` and `TauCeti.ae_extendByZeroLpₗᵢ_eq_zero_of_notMem`:
  the same values, split pointwise into the cases `x ∈ s` and `x ∉ s`.
* `TauCeti.extendByZeroLpₗᵢ_self` and `TauCeti.extendByZeroLpₗᵢ_extendByZeroLpₗᵢ`: extending
  along `s ⊆ s` is the identity, and extending twice is extending once.
* `TauCeti.extendByZeroLpₗᵢ_eq_of_ae_eq` and `TauCeti.coeFn_extendByZeroLpₗᵢ_comp`: the two ways
  an extension is recognised in practice — from a representative that already vanishes off `s`,
  and through pointwise postcomposition by a map fixing `0`.
* `TauCeti.setIntegral_extendByZeroLpₗᵢ`: integrating against the extension over `t` is
  integrating against the original function over `s`.
* `MeasureTheory.MemLp.of_restrict_of_support_subset`: the unbundled form for the whole space, a
  function supported in `s` and in `Lᵖ(s)` is in `Lᵖ`.
* `TauCeti.LpToLpRestrictCLM_castLpₗᵢ_extendByZeroLpₗᵢ` and
  `TauCeti.castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM_of_ae_compl_eq_zero`: extension by zero to
  the whole space and restriction (`LpToLpRestrictCLM`) undo each other, the second on functions
  vanishing off `s`.
* `TauCeti.tendsto_sub_castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM`: along a directed monotone
  open cover `U k` of a locally compact space, `f - 1_{U k} f → 0` in `Lᵖ` for `p < ∞`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {F : Type*} [NormedAddCommGroup F] (𝕜 : Type*)
  [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {p : ℝ≥0∞} {μ : Measure α} {s t : Set α}

/-- The indicator of `s` applied to an `Lᵖ(s)` function is in `Lᵖ(t)`, for every set `t`. -/
private theorem memLp_indicator_coeFn (hs : NullMeasurableSet s μ) (f : Lp F p (μ.restrict s)) :
    MemLp (s.indicator f) p (μ.restrict t) :=
  ((memLp_indicator_iff_restrict hs).2 (Lp.memLp f)).mono_measure Measure.restrict_le_self

/-- Extension by zero as a linear map; `TauCeti.extendByZeroLpₗᵢ` upgrades it to an isometry. -/
private def extendByZeroLpₗ (hs : NullMeasurableSet s μ) :
    Lp F p (μ.restrict s) →ₗ[𝕜] Lp F p (μ.restrict t) where
  toFun f := (memLp_indicator_coeFn hs f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ <| ae_restrict_of_ae ?_
    exact ((ae_eq_restrict_iff_indicator_ae_eq₀ hs).1 (Lp.coeFn_add f g)).trans
      (.of_eq (indicator_add' s _ _))
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ <| ae_restrict_of_ae ?_
    exact ((ae_eq_restrict_iff_indicator_ae_eq₀ hs).1 (Lp.coeFn_smul c f)).trans
      (.of_eq (indicator_const_smul s c _))

/-- The value of `extendByZeroLpₗ`, as the class of the indicator of a representative. -/
private theorem extendByZeroLpₗ_apply (hs : NullMeasurableSet s μ) (f : Lp F p (μ.restrict s)) :
    extendByZeroLpₗ 𝕜 (t := t) hs f = (memLp_indicator_coeFn hs f).toLp _ :=
  rfl

variable (μ) in
/-- **Extension by zero as a linear isometry** `Lᵖ(s) → Lᵖ(t)` for a null-measurable `s ⊆ t`: a
function on `s` is regarded as a function on the larger set `t` by declaring it zero on `t \ s`.

It is an isometry, not merely a bounded map, because the enlarged region contributes nothing to
the `Lᵖ` norm; in particular the extension is injective, so `Lᵖ(s)` really does sit inside
`Lᵖ(t)`. -/
def extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t) :
    Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t) where
  toLinearMap := extendByZeroLpₗ 𝕜 hs
  norm_map' f := by
    rw [extendByZeroLpₗ_apply, Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict (hs.mono Measure.restrict_le_self),
      Measure.restrict_restrict_of_subset hst, ← Lp.norm_def]

/-- **The extension by zero is the indicator of the original representative.** -/
theorem coeFn_extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict t] s.indicator (f : α → F) :=
  (memLp_indicator_coeFn hs f).coeFn_toLp

/-- **On `s`, the extension by zero agrees with the original function**, almost everywhere on
`t`. -/
theorem ae_extendByZeroLpₗᵢ_eq_of_mem [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    ∀ᵐ x ∂μ.restrict t, x ∈ s → extendByZeroLpₗᵢ 𝕜 μ hs hst f x = f x :=
  (coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).mono fun _ hx hxs => hx.trans (indicator_of_mem hxs _)

/-- **Off `s`, the extension by zero vanishes**, almost everywhere on `t`. -/
theorem ae_extendByZeroLpₗᵢ_eq_zero_of_notMem [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ)
    (hst : s ⊆ t) (f : Lp F p (μ.restrict s)) :
    ∀ᵐ x ∂μ.restrict t, x ∉ s → extendByZeroLpₗᵢ 𝕜 μ hs hst f x = 0 :=
  (coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).mono fun _ hx hxs => hx.trans (indicator_of_notMem hxs _)

/-- **The extension by zero restricts back to the original function.** -/
theorem coeFn_extendByZeroLpₗᵢ_restrict [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict s] (f : α → F) :=
  ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).filter_mono
    (ae_mono (Measure.restrict_mono hst le_rfl))).trans
    (indicator_ae_eq_restrict hs)

/-- **Extending by zero along `s ⊆ s` does nothing.** -/
@[simp]
theorem extendByZeroLpₗᵢ_self [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ)
    (f : Lp F p (μ.restrict s)) : extendByZeroLpₗᵢ 𝕜 μ hs Subset.rfl f = f :=
  Lp.ext (coeFn_extendByZeroLpₗᵢ_restrict 𝕜 hs Subset.rfl f)

/-- **Extending by zero twice is extending by zero once.**  Zero-extending from `s` to `t` and
then from `t` to `u` is the zero-extension from `s` to `u`. -/
@[simp]
theorem extendByZeroLpₗᵢ_extendByZeroLpₗᵢ [Fact (1 ≤ p)] {u : Set α} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t μ) (hst : s ⊆ t) (htu : t ⊆ u) (f : Lp F p (μ.restrict s)) :
    extendByZeroLpₗᵢ 𝕜 μ ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f) =
      extendByZeroLpₗᵢ 𝕜 μ hs (hst.trans htu) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f),
    ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq₀ ht).1
      (coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f)),
    coeFn_extendByZeroLpₗᵢ 𝕜 hs (hst.trans htu) f] with x h1 h2 h3
  rw [h1, h2, h3, indicator_indicator, inter_eq_self_of_subset_right hst]

/-- **Recognising an extension by zero from a common representative.**  A function `h` supported
in `s` that represents `f` on `s` and `g` on `t` exhibits `g` as the zero-extension of `f`; this
is how a function already known to vanish off `s` is transported from `Lᵖ(s)` to `Lᵖ(t)`. -/
theorem extendByZeroLpₗᵢ_eq_of_ae_eq [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t)
    {h : α → F} (hsupp : Function.support h ⊆ s) {f : Lp F p (μ.restrict s)}
    {g : Lp F p (μ.restrict t)} (hf : ∀ᵐ x ∂μ.restrict s, f x = h x)
    (hg : ∀ᵐ x ∂μ.restrict t, g x = h x) : extendByZeroLpₗᵢ 𝕜 μ hs hst f = g :=
  Lp.ext <| ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).trans <| ae_restrict_of_ae <|
    ((ae_eq_restrict_iff_indicator_ae_eq₀ hs).1 hf).trans
      (.of_eq (indicator_eq_self.2 hsupp))).trans (Filter.EventuallyEq.symm hg)

/-- **Extension by zero commutes with pointwise postcomposition by a map fixing `0`.**  If `g'` is
the pointwise image of `f` under `L`, then the extension of `g'` is the pointwise image under `L`
of the extension of `f`: off `s` both sides are `L 0 = 0`. The source and target may have
different integrability exponents. -/
theorem coeFn_extendByZeroLpₗᵢ_comp {G : Type*} [NormedAddCommGroup G] [Module 𝕜 G]
    [IsBoundedSMul 𝕜 G] {q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (L : F → G)
    (hL : L 0 = 0) {f : Lp F p (μ.restrict s)} {g' : Lp G q (μ.restrict s)}
    (hg' : ∀ᵐ x ∂μ.restrict s, g' x = L (f x)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst g' : α → G) =ᵐ[μ.restrict t]
      fun x => L (extendByZeroLpₗᵢ 𝕜 μ hs hst f x) := by
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 hs hst g', coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f,
    ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq₀ hs).1 hg')] with x h1 h2 h3
  rw [h1, h3, h2]
  exact congrFun (Set.indicator_comp_of_zero hL) x

/-- **Integrals against an extension by zero only see the original set.** For a pairing `L` with
`L x 0 = 0`, integrating `x ↦ L x (f₀ x)` over `t`, where `f₀` is the extension of `f` by zero, is
integrating `x ↦ L x (f x)` over `s`. The pairings met in weak formulations are `L x y = g x * y`
and `L x y = ⟪G x, y⟫`. -/
theorem setIntegral_extendByZeroLpₗᵢ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (L : α → F → E)
    (hL : ∀ x, L x 0 = 0)
    (f : Lp F p (μ.restrict s)) :
    ∫ x in t, L x (extendByZeroLpₗᵢ 𝕜 μ hs hst f x) ∂μ = ∫ x in s, L x (f x) ∂μ := by
  calc ∫ x in t, L x (extendByZeroLpₗᵢ 𝕜 μ hs hst f x) ∂μ
      = ∫ x in t, s.indicator (fun x => L x (f x)) x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f] with x hx
        rw [hx]
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs, indicator_of_mem hxs]
        · rw [indicator_of_notMem hxs, indicator_of_notMem hxs, hL]
    _ = ∫ x in s, L x (f x) ∂μ := by
        rw [integral_indicator₀ (hs.mono Measure.restrict_le_self),
          Measure.restrict_restrict_of_subset hst]

omit 𝕜 in
/-- A function supported in a null-measurable set `s` and in `Lᵖ(s)` is in `Lᵖ` of the whole
space: its extension by zero is itself. -/
theorem _root_.MeasureTheory.MemLp.of_restrict_of_support_subset {f : α → F}
    (hs : NullMeasurableSet s μ) (hf : MemLp f p (μ.restrict s)) (hfs : Function.support f ⊆ s) :
    MemLp f p μ := by
  rw [← indicator_eq_self.2 hfs, memLp_indicator_iff_restrict hs]
  exact hf

/-- **The extension by zero to the whole space is the indicator of the original representative.**
The extension lands in `Lᵖ(μ.restrict univ)`, which `TauCeti.castLpₗᵢ` identifies with `Lᵖ(μ)`. -/
theorem coeFn_castLpₗᵢ_extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ)
    (f : Lp F p (μ.restrict s)) :
    (castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ (extendByZeroLpₗᵢ 𝕜 μ hs (subset_univ s) f) :
      α → F) =ᵐ[μ] s.indicator (f : α → F) :=
  .trans (.of_forall fun x => coeFn_castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ _ x)
    ((coeFn_extendByZeroLpₗᵢ 𝕜 hs (subset_univ s) f).filter_mono
      (ae_mono Measure.restrict_univ.ge))

/-- **Restricting the extension by zero to the whole space gives back the function.** -/
theorem LpToLpRestrictCLM_castLpₗᵢ_extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : NullMeasurableSet s μ)
    (f : Lp F p (μ.restrict s)) :
    LpToLpRestrictCLM α F 𝕜 μ p s
      (castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ (extendByZeroLpₗᵢ 𝕜 μ hs (subset_univ s) f)) = f :=
  Lp.ext <| (LpToLpRestrictCLM_coeFn 𝕜 s _).trans <|
    ((coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 hs f).filter_mono (ae_mono Measure.restrict_le_self)).trans
      (indicator_ae_eq_restrict hs)

/-- **A function vanishing off `s` is the extension by zero of its restriction to `s`.** -/
theorem castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM_of_ae_compl_eq_zero [Fact (1 ≤ p)]
    (hs : NullMeasurableSet s μ) {f : Lp F p μ} (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (extendByZeroLpₗᵢ 𝕜 μ hs (subset_univ s) (LpToLpRestrictCLM α F 𝕜 μ p s f)) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 hs (LpToLpRestrictCLM α F 𝕜 μ p s f),
    (ae_eq_restrict_iff_indicator_ae_eq₀ hs).1 (LpToLpRestrictCLM_coeFn 𝕜 s f), hf]
    with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, h3 hx]

/-- **Exhaustion in `Lᵖ`.** Along a monotone family of open sets `U k`, indexed by a directed
order, that covers a locally compact space, the part `f - 1_{U k} f` of `f ∈ Lᵖ(μ)` outside `U k`
tends to `0` for `p < ∞`: a compactly supported approximation of `f` lies in some `U k`. -/
theorem tendsto_sub_castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM [TopologicalSpace α]
    [NormalSpace α] [R1Space α] [WeaklyLocallyCompactSpace α] [BorelSpace α] [μ.Regular]
    [NormedSpace ℝ F] [Fact (1 ≤ p)] (hp : p ≠ ∞) {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] {U : κ → Set α} (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : ⋃ k, U k = univ) (f : Lp F p μ) :
    Filter.Tendsto (fun k => f - castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (extendByZeroLpₗᵢ 𝕜 μ (hU k).nullMeasurableSet (subset_univ _)
        (LpToLpRestrictCLM α F 𝕜 μ p (U k) f))) Filter.atTop (nhds 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  -- Approximate `f` within `ε / 3` by a compactly supported `g`; its support lies in some `U k₀`.
  obtain ⟨g, hgc, hgle, -, hgmem⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 3)) (by simp [hε])
  obtain ⟨k₀, hk₀⟩ := hgc.isCompact.elim_directed_cover U hU (by rw [hcover]; exact subset_univ _)
    (fun i j => (directed_of (· ≤ ·) i j).imp fun _ hk => ⟨hmono hk.1, hmono hk.2⟩)
  have hfg : ‖f - hgmem.toLp g‖ ≤ ε / 3 := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      (Filter.EventuallyEq.rfl.sub hgmem.coeFn_toLp))]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hgle
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  set J := (castLpₗᵢ (𝕜 := 𝕜) (E := F) (p := p) Measure.restrict_univ).toLinearIsometry.comp
    (extendByZeroLpₗᵢ 𝕜 μ (hU k).nullMeasurableSet (subset_univ _))
  have hg : J (LpToLpRestrictCLM α F 𝕜 μ p (U k) (hgmem.toLp g)) = hgmem.toLp g := by
    refine castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM_of_ae_compl_eq_zero 𝕜 _ ?_
    filter_upwards [hgmem.coeFn_toLp] with x hx hxU
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport fun h => hxU (hmono hk (hk₀ h))
  have hsplit : f - J (LpToLpRestrictCLM α F 𝕜 μ p (U k) f) = (f - hgmem.toLp g) -
      J (LpToLpRestrictCLM α F 𝕜 μ p (U k) (f - hgmem.toLp g)) := by
    rw [map_sub, map_sub, hg]
    abel
  simp only [J, LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
    Function.comp_apply] at hsplit
  rw [dist_zero_right, hsplit]
  calc _ ≤ ‖f - hgmem.toLp g‖ + ‖LpToLpRestrictCLM α F 𝕜 μ p (U k) (f - hgmem.toLp g)‖ := by
        refine (norm_sub_le _ _).trans_eq ?_
        rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
    _ ≤ ε / 3 + ε / 3 := add_le_add hfg ((norm_Lp_toLp_restrict_le _ _).trans hfg)
    _ < ε := by linarith

end TauCeti
