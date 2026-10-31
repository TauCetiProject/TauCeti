/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Right translation on `Lᵖ` of a locally compact group

Let `μ` be a regular left Haar measure on a locally compact group `G`, and let
`c(g) = Measure.modularCharacter g`, so that `∫ f (x * g) dμ = c(g) ∫ f dμ`. Right translation of
functions,

```text
(R_g f)(x) = f (x * g),        R_g R_h = R_(g * h),
```

multiplies the `Lᵖ` norm by `c(g) ^ (1 / p)`, so for `p < ∞` it is an isometry only when `G` is
unimodular. It still preserves `Lᵖ` classes, so it gives a monoid homomorphism
`MeasureTheory.Lp.rightTranslation μ p 𝕜 : G →* (Lp E p μ →L[𝕜] Lp E p μ)`, which commutes with
left translation `MeasureTheory.Lp.leftTranslation`.

For `1 ≤ p < ∞` right translation is strongly continuous: `g ↦ R_g f` is continuous for every
`f`, and in particular `‖f (· * g) - f‖_p → 0` as `g → 1`. Left translation is continuous by
Mathlib's `DomMulAct` theory, which needs an invariant measure; right translation does not
preserve `μ`, so the argument is redone here. First, the right translates
`{x | x * g ∈ s}` of a measurable set of finite measure converge to `s` in measure: sandwich `s`
between a compact and an open set and use the scaling `μ {x | x * g ∈ t} = c(g) μ t`. This gives
continuity on indicators, hence on simple functions, and simple functions are dense in `Lᵖ`.
Since `c` is continuous with `c(1) = 1`, the operator norm of `R_g` is less than `2` near `1`,
which passes convergence from simple functions to all of `Lᵖ`. No σ-finiteness of `μ`, no
second countability and no separation axiom on `G` is assumed.

Continuity of right translation is the input for approximate identities on the right,
`h * k_U → h` in `L¹` for kernels `k_U` concentrating at `1`, where
`(h * k)(x) = ∫ y, h (x * y) k (y⁻¹) dμ` averages right translates of `h`.

## Main definitions

* `MeasureTheory.Lp.rightTranslation μ p 𝕜`: right translation `g ↦ R_g` on `Lp E p μ`, as a
  monoid homomorphism to continuous linear maps.

## Main results

* `MeasureTheory.eLpNorm_comp_mul_right_of_regular`: `‖f (· * g)‖_p = c(g) ^ (1 / p) ‖f‖_p`.
* `MeasureTheory.tendsto_measure_preimage_mul_right_symmDiff_of_regular`: right translates of a
  measurable set of finite measure converge to it in measure.
* `MeasureTheory.Lp.coeFn_rightTranslation`: `R_g f` is almost everywhere `x ↦ f (x * g)`.
* `MeasureTheory.Lp.norm_rightTranslation_apply`: `‖R_g f‖ = c(g) ^ (1 / p) ‖f‖`.
* `MeasureTheory.Lp.rightTranslation_leftTranslation`: right and left translations commute.
* `MeasureTheory.Lp.continuous_rightTranslation_apply`: right translation is strongly continuous
  for `p < ∞`.
* `MeasureTheory.MemLp.tendsto_eLpNorm_comp_mul_right_sub_of_regular`: `‖f (· * g) - f‖_p → 0`
  as `g → 1`, for `1 ≤ p < ∞`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, Chapter 2, for continuity of left and
  right translations in `Lᵖ` of a locally compact group.
* The density argument follows Mathlib's `MeasureTheory.Lp.compMeasurePreserving_continuous`,
  and the compact and open sandwich follows Mathlib's
  `MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero`, both by Yury Kudryashov, with the
  invariance of the measure replaced by the scaling by the modular character.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal Pointwise symmDiff

namespace MeasureTheory

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Right translation scales the `Lᵖ` seminorm by `c(g) ^ (1 / p)`, where `c` is the modular
character, for every function and every exponent. -/
theorem eLpNorm_comp_mul_right_of_regular (f : G → E) (g : G) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x * g)) p μ =
      (Measure.modularCharacter g ^ p.toReal⁻¹ : ℝ≥0) * eLpNorm f p μ := by
  have h := (MeasurableEquiv.mulRight g).measurableEmbedding.eLpNorm_map_measure (g := f) (μ := μ)
    (p := p)
  have hc : Measure.modularCharacter g ≠ 0 := (Measure.modularCharacterFun_pos g).ne'
  rw [MeasurableEquiv.coe_mulRight, Measure.map_right_mul_eq_modularCharacter_smul_of_regular,
    eLpNorm_smul_measure_of_ne_zero' hc] at h
  exact h.symm

/-- Right translation preserves `Lᵖ`. -/
theorem MemLp.comp_mul_right_of_regular {f : G → E} (hf : MemLp f p μ) (g : G) :
    MemLp (fun x => f (x * g)) p μ :=
  memLp_iff.2 <| (eLpNorm_comp_mul_right_of_regular f g p).trans_lt <|
    ENNReal.mul_lt_top ENNReal.coe_lt_top hf

/-- A function is in `Lᵖ` exactly when its right translate is. -/
@[simp]
theorem memLp_comp_mul_right_iff_of_regular {f : G → E} (g : G) :
    MemLp (fun x => f (x * g)) p μ ↔ MemLp f p μ :=
  ⟨fun h => by simpa [mul_assoc] using h.comp_mul_right_of_regular g⁻¹,
    fun h => h.comp_mul_right_of_regular g⟩

/-- The right translates `{x | x * g ∈ s}` of a measurable set of finite measure converge to `s`
in measure as `g → 1`. -/
theorem tendsto_measure_preimage_mul_right_symmDiff_of_regular {s : Set G} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : Tendsto (fun g => μ (((· * g) ⁻¹' s) ∆ s)) (𝓝 1) (𝓝 0) := by
  -- Sandwich `s` between a compact `K` and an open `U` with `μ (U \ K) ≤ 2 δ`. For `g` near `1`,
  -- the sets `K g` and `K g⁻¹` lie in `U`, so the symmetric difference of `{x | x * g ∈ s}` and
  -- `s` lies in `{x | x * g ∈ U \ K} ∪ (U \ K)`, of measure at most `(c(g) + 1) μ (U \ K)`.
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  set δ := ε / 6
  have hδ : δ ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨U, hsU, hUo, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hμs hδ
  obtain ⟨K, hKs, hKc, -, hsK⟩ := hs.exists_isCompact_isClosed_sdiff_lt hμs hδ
  have hUK : μ (U \ K) ≤ 2 * δ :=
    calc μ (U \ K) ≤ μ (U \ s ∪ s \ K) := measure_mono fun x hx => by
          by_cases h : x ∈ s <;> simp_all
      _ ≤ δ + δ := (measure_union_le _ _).trans (add_le_add hUs.le hsK.le)
      _ = 2 * δ := (two_mul δ).symm
  obtain ⟨V, hV, hKV⟩ := compact_open_separated_mul_right hKc hUo (hKs.trans hsU)
  have hc : Tendsto (fun g : G => (Measure.modularCharacter g : ℝ≥0∞)) (𝓝 1) (𝓝 1) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_coe.comp TauCeti.continuous_modularCharacter).tendsto (1 : G)
  filter_upwards [hV, inv_mem_nhds_one G hV, hc.eventually (gt_mem_nhds ENNReal.one_lt_two)]
    with g hg hg' hcg
  have hsub : ((· * g) ⁻¹' s) ∆ s ⊆ (· * g) ⁻¹' (U \ K) ∪ U \ K := by
    intro x hx
    have h₁ : x * g ∈ K → x ∈ U := fun h => by simpa using hKV (Set.mul_mem_mul h hg')
    have h₂ : x ∈ K → x * g ∈ U := fun h => hKV (Set.mul_mem_mul h hg)
    simp only [Set.mem_symmDiff, Set.mem_preimage] at hx
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_sdiff]
    grind
  calc μ (((· * g) ⁻¹' s) ∆ s)
      ≤ μ ((· * g) ⁻¹' (U \ K)) + μ (U \ K) := (measure_mono hsub).trans (measure_union_le _ _)
    _ = Measure.modularCharacter g * μ (U \ K) + μ (U \ K) := by
      rw [Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular]
    _ ≤ 2 * (2 * δ) + 2 * δ := by gcongr
    _ = 6 * (ε / 6) := by ring
    _ ≤ ε := ENNReal.mul_div_le

namespace Lp

variable (μ p)

/-- Right translation by `g` on `Lp E p μ`, as an additive map; see `Lp.rightTranslation`. -/
private def rightTranslationAddHom (g : G) : Lp E p μ →+ Lp E p μ :=
  AddMonoidHom.mk' (fun f => ((Lp.memLp f).comp_mul_right_of_regular g).toLp fun x => f (x * g))
    fun f f' => by
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _
        ((Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae_eq_comp (coeFn_add f f'))

variable {μ p}

private theorem coeFn_rightTranslationAddHom (g : G) (f : Lp E p μ) :
    rightTranslationAddHom μ p g f =ᵐ[μ] fun x => f (x * g) :=
  MemLp.coeFn_toLp ((Lp.memLp f).comp_mul_right_of_regular g)

private theorem norm_rightTranslationAddHom_apply (g : G) (f : Lp E p μ) :
    ‖rightTranslationAddHom μ p g f‖ = (Measure.modularCharacter g : ℝ) ^ p.toReal⁻¹ * ‖f‖ := by
  rw [rightTranslationAddHom, AddMonoidHom.mk'_apply, norm_toLp,
    eLpNorm_comp_mul_right_of_regular, ENNReal.toReal_mul, norm_def]
  simp

private theorem rightTranslationAddHom_indicatorConstLp {s : Set G} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : E) (g : G) (hμs' : μ ((· * g) ⁻¹' s) ≠ ∞) :
    rightTranslationAddHom μ p g (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (measurable_mul_const g hs) hμs' c := by
  refine ext ?_
  filter_upwards [coeFn_rightTranslationAddHom g (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (hs := measurable_mul_const g hs) (hμs := hμs') (c := c),
    (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae
      (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c))] with x hx hx' hx''
  rw [hx, hx', hx'']
  exact (Set.indicator_comp_right (fun x => x * g)).symm

/-- Right translates of an `Lᵖ` class converge to it as `g → 1`, for `1 ≤ p < ∞`. -/
private theorem tendsto_rightTranslationAddHom_apply_one [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp E p μ) : Tendsto (fun g => rightTranslationAddHom μ p g f) (𝓝 1) (𝓝 f) := by
  -- For simple functions this reduces, by additivity, to indicators of sets of finite measure.
  have hsimple (F : simpleFunc E p μ) :
      Tendsto (fun g => rightTranslationAddHom μ p g (F : Lp E p μ)) (𝓝 1) (𝓝 F) := by
    induction F using simpleFunc.induction (one_pos.trans_le Fact.out).ne' hp with
    | @indicatorConst c s hs hμs =>
      have hμs' (g : G) : μ ((· * g) ⁻¹' s) ≠ ∞ := by
        rw [Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top hμs.ne
      simp only [simpleFunc.coe_indicatorConst,
        rightTranslationAddHom_indicatorConstLp hs hμs.ne c _ (hμs' _)]
      exact tendsto_indicatorConstLp_set hp
        (tendsto_measure_preimage_mul_right_symmDiff_of_regular hs hμs.ne)
    | add hf hg _ ihf ihg =>
      simpa only [AddSubgroup.coe_add, map_add] using ihf.add ihg
  -- In general, approximate `f` within `ε / 4` by a simple function `F`. Near `1` the norm of
  -- `R_g` is less than `2`, and `R_g F` is within `ε / 4` of `F`.
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨F, hfF⟩ :=
    (simpleFunc.denseRange (E := E) (μ := μ) hp).exists_dist_lt f (by positivity : 0 < ε / 4)
  have hc : Tendsto (fun g : G => (Measure.modularCharacter g : ℝ) ^ p.toReal⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using ((NNReal.continuous_coe.comp TauCeti.continuous_modularCharacter).rpow_const
      fun _ => Or.inr (inv_nonneg.2 ENNReal.toReal_nonneg)).tendsto (1 : G)
  filter_upwards [hc.eventually (gt_mem_nhds one_lt_two),
    Metric.tendsto_nhds.1 (hsimple F) _ (by positivity : 0 < ε / 4)] with g hg2 hgF
  set R := rightTranslationAddHom μ p (E := E) g
  have h₁ : dist (R f) (R F) ≤ 2 * (ε / 4) := by
    rw [_root_.dist_eq_norm, ← map_sub, norm_rightTranslationAddHom_apply, ← _root_.dist_eq_norm]
    exact mul_le_mul hg2.le hfF.le dist_nonneg zero_le_two
  calc dist (R f) f ≤ dist (R f) (R F) + dist (R F) F + dist (F : Lp E p μ) f :=
        dist_triangle4 _ _ _ _
    _ < 2 * (ε / 4) + ε / 4 + ε / 4 := by
      rw [dist_comm _ f]
      exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt h₁ hgF) hfF.le
    _ = ε := by ring

variable (μ p) [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Right translation `g ↦ R_g` on `Lp E p μ` for a regular left Haar measure `μ`, where
`(R_g f)(x) = f (x * g)`, as a monoid homomorphism to continuous linear maps. -/
def rightTranslation : G →* (Lp E p μ →L[𝕜] Lp E p μ) where
  toFun g := LinearMap.mkContinuous
    { toFun := rightTranslationAddHom μ p g
      map_add' := map_add _
      map_smul' c f := by
        refine ext ?_
        filter_upwards [coeFn_rightTranslationAddHom g (c • f),
          coeFn_smul c (rightTranslationAddHom μ p g f), coeFn_rightTranslationAddHom g f,
          (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae (coeFn_smul c f)]
          with x h₁ h₂ h₃ h₄
        simp [h₁, h₂, h₃, h₄] } _
    fun f => (norm_rightTranslationAddHom_apply g f).le
  map_one' := by
    ext f : 1
    refine ext ?_
    filter_upwards [coeFn_rightTranslationAddHom 1 f] with x hx
    simp [hx]
  map_mul' g h := by
    ext f : 1
    refine ext ?_
    filter_upwards [coeFn_rightTranslationAddHom (g * h) f,
      coeFn_rightTranslationAddHom g (rightTranslationAddHom μ p h f),
      (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae
        (coeFn_rightTranslationAddHom h f)] with x hgh hg hh
    simp [hgh, hg, hh, mul_assoc]

variable {μ p 𝕜}

private theorem rightTranslation_apply_eq (g : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g f = rightTranslationAddHom μ p g f :=
  (rfl)

/-- The right translate `R_g f` is almost everywhere the function `x ↦ f (x * g)`. -/
theorem coeFn_rightTranslation (g : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g f =ᵐ[μ] fun x => f (x * g) :=
  rightTranslation_apply_eq (𝕜 := 𝕜) g f ▸ coeFn_rightTranslationAddHom g f

/-- Right translation of the class of an `Lᵖ` function is the class of its right translate. -/
theorem rightTranslation_toLp {f : G → E} (hf : MemLp f p μ) (g : G) :
    rightTranslation μ p 𝕜 g (hf.toLp f) = (hf.comp_mul_right_of_regular g).toLp
      fun x => f (x * g) := by
  refine ext ?_
  filter_upwards [coeFn_rightTranslation (𝕜 := 𝕜) g (hf.toLp f), MemLp.coeFn_toLp
    (hf.comp_mul_right_of_regular g), (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae
    (MemLp.coeFn_toLp hf)] with x hx hx' hf'
  rw [hx, hx', hf']

/-- Right translation of the indicator of a set of finite measure is the indicator of its
right translate `{x | x * g ∈ s}`. -/
theorem rightTranslation_indicatorConstLp {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : E) (g : G) (hμs' : μ ((· * g) ⁻¹' s) ≠ ∞) :
    rightTranslation μ p 𝕜 g (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (measurable_mul_const g hs) hμs' c :=
  rightTranslationAddHom_indicatorConstLp hs hμs c g hμs'

/-- Right translation by `g` multiplies `Lᵖ` norms by `c(g) ^ (1 / p)`, where `c` is the modular
character. -/
theorem norm_rightTranslation_apply (g : G) (f : Lp E p μ) :
    ‖rightTranslation μ p 𝕜 g f‖ = (Measure.modularCharacter g : ℝ) ^ p.toReal⁻¹ * ‖f‖ :=
  norm_rightTranslationAddHom_apply g f

/-- Right and left translations commute: `R_g (L_h f) = L_h (R_g f)`. -/
theorem rightTranslation_leftTranslation (g h : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g (leftTranslation μ p 𝕜 h f) =
      leftTranslation μ p 𝕜 h (rightTranslation μ p 𝕜 g f) := by
  refine ext ?_
  filter_upwards [coeFn_rightTranslation (𝕜 := 𝕜) g (leftTranslation μ p 𝕜 h f),
    coeFn_leftTranslation (𝕜 := 𝕜) h (rightTranslation μ p 𝕜 g f),
    (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae
      (coeFn_leftTranslation (𝕜 := 𝕜) h f),
    (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving.ae
      (coeFn_rightTranslation (𝕜 := 𝕜) g f)] with x hr hl hl' hr'
  rw [hr, hl, hl', hr', mul_assoc]

/-- Right translation is strongly continuous on `Lᵖ` for `p < ∞`: for each `f`, the orbit
`g ↦ R_g f` is continuous. -/
theorem continuous_rightTranslation_apply (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g => rightTranslation μ p 𝕜 g f := by
  -- Continuity at `g₀` reduces to continuity at `1`, since `R_g = R_(g₀) ∘ R_(g₀⁻¹ * g)`.
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const.mul continuous_id).tendsto (f := fun g : G => g₀⁻¹ * g) g₀
  refine (((rightTranslation μ p 𝕜 g₀).continuous.tendsto f).comp
    ((tendsto_rightTranslationAddHom_apply_one hp f).comp h)).congr fun g => ?_
  rw [Function.comp_apply, Function.comp_apply, ← rightTranslation_apply_eq (𝕜 := 𝕜),
    ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

end Lp

/-- The right translates of an `Lᵖ` function converge to it in `Lᵖ` for `1 ≤ p < ∞`, for a
regular left Haar measure. -/
theorem MemLp.tendsto_eLpNorm_comp_mul_right_sub_of_regular {f : G → E} (hf : MemLp f p μ)
    (hp₁ : 1 ≤ p) (hp : p ≠ ∞) :
    Tendsto (fun g => eLpNorm (fun x => f (x * g) - f x) p μ) (𝓝 1) (𝓝 0) := by
  have := Fact.mk hp₁
  have h := Lp.tendsto_rightTranslationAddHom_apply_one hp (hf.toLp f)
  rw [tendsto_iff_edist_tendsto_0] at h
  refine h.congr fun g => ?_
  rw [Lp.edist_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_rightTranslationAddHom g (hf.toLp f), hf.coeFn_toLp,
    (Measure.quasiMeasurePreserving_mul_right_of_regular μ g).ae hf.coeFn_toLp] with x h₁ h₂ h₃
  rw [Pi.sub_apply, h₁, h₂, h₃]

end MeasureTheory
