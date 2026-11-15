/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.Codiscrete

/-!
# The Mittag-Leffler theorem and prescribed isolated singularities on plane sets

Let `Ω ⊆ ℂ` be a set, `E ⊆ Ω` a subset discrete and relatively closed in `Ω` (expressed via
`Eᶜ ∈ codiscreteWithin Ω`), and `F` a complex Banach space. Given at each point `a ∈ E` a germ
`P a : ℂ → F` that is complex-differentiable on a punctured neighborhood of `a`, this file
constructs a single function `f : ℂ → F` complex-differentiable on `Ω \ E` such that at every
`a ∈ E` the difference `f - P a` agrees on `𝓝[≠] a` with a function analytic at `a`
(`TauCeti.exists_holomorphic_prescribed_isolated_singularities`). Both poles and essential
singularities (such as `z ↦ exp ((z - a)⁻¹)`) are permitted, and `P a` only needs to be defined
and complex-differentiable on a punctured neighborhood of `a` rather than on all of `ℂ \ {a}`.

Specializing `P a` to meromorphic germs at `a` yields the classical Mittag-Leffler theorem
(`TauCeti.exists_meromorphic_prescribed_principal_parts`), producing `f : ℂ → F` meromorphic on
`Ω` and complex-differentiable on `Ω \ E` with those prescribed singular parts; for scalar
polynomials without constant term, `TauCeti.exists_meromorphicOn_principalPart_mk_eq` realizes
prescribed algebraic principal parts `TauCeti.meromorphicGerms.principalPart`. Neither theorem
requires `Ω` itself to be open: whenever `E ⊆ Ω` satisfies `Eᶜ ∈ codiscreteWithin Ω`, the set `Ω`
avoids the closed derived set `derivedSet E` (`Ω ⊆ (derivedSet E)ᶜ`), so the open-set construction
on `(derivedSet E)ᶜ` restricts to `Ω`.

The file also establishes:
* removable-singularity patching across `Ω ∩ E`
  (`TauCeti.exists_differentiableOn_eqOn_of_analyticAt_nhdsNE`), uniqueness of solutions modulo
  functions complex-differentiable on `Ω`
  (`TauCeti.exists_differentiableOn_eqOn_sub_of_prescribed_isolated_singularities` and
  `TauCeti.exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq`), and the full affine-coset
  characterization on open sets
  (`TauCeti.prescribed_isolated_singularities_iff_exists_differentiableOn_eqOn_add`);
* functoriality of prescribed isolated singularities under pullback along non-locally-constant
  analytic maps (`TauCeti.prescribed_isolated_singularities_comp`), together with restriction to
  subsets (`TauCeti.prescribed_isolated_singularities_mono`), translation
  (`TauCeti.prescribed_isolated_singularities_comp_add_right`), and nonzero scaling
  (`TauCeti.prescribed_isolated_singularities_comp_mul_left`).

## Proof outline

On an open set `Ω`, `TauCeti.exists_hasLaurentSeriesOnAnnulus_of_eventually_differentiableAt`
extracts at each `a : E` a convergent punctured-disk Laurent series with coefficients `c a`, whose
negative part `s a := laurentNegPart (c a) a.val` (`TauCeti.laurentNegPart`) is holomorphic on all
of `ℂ \ {a.val}` (`TauCeti.HasLaurentSeriesOnAnnulus.differentiableOn_laurentNegPart`) and differs
from `P a` near `a.val` by a power-series-analytic nonnegative part. Exhausting `Ω` by compact sets
`K n` filled in `Ω` (`IsOpen.exists_isFilledIn_compact_exhaustion`), each `K n` meets `E` in a
finite set `A n : Finset E`, partitioning `E` into disjoint finite shells `B 0 = A 0` and
`B (n + 1) = A (n + 1) \ A n`. For `a ∈ B (n + 1)`, `a.val ∉ K n`, so `s a` is uniformly
approximated on `K n` by a finite polynomial in `(z - a.val)⁻¹`, which in turn is uniformly
approximated on `K n` by a function holomorphic on `Ω` via
`TauCeti.IsFilledIn.exists_differentiableOn_norm_sum_zpow_neg_sub_lt` (from
`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`). Setting `Q 0 = 0` and subtracting
holomorphic corrections `Q (n + 1)` with error `< 2⁻⁽ⁿ⁺¹⁾` on `K n` makes the series
`∑' k, ((∑ a ∈ B k, s a) - Q k)` converge uniformly on `interior (K m)` after splitting off the
first `m + 1` shells, yielding holomorphy on `Ω \ E` (`TendstoUniformlyOn.differentiableOn`) and
analyticity of each local remainder.

## Main results

* `TauCeti.exists_holomorphic_prescribed_isolated_singularities`: global realization of arbitrary
  isolated-singularity germs on `E ⊆ Ω` with `Eᶜ ∈ codiscreteWithin Ω`.
* `TauCeti.exists_meromorphic_prescribed_principal_parts`: Mittag-Leffler theorem for meromorphic
  germs.
* `TauCeti.exists_meromorphicOn_principalPart_mk_eq`: Mittag-Leffler realization of prescribed
  constant-free polynomials via `TauCeti.meromorphicGerms.principalPart`.
* `TauCeti.exists_differentiableOn_eqOn_of_analyticAt_nhdsNE`,
  `TauCeti.exists_differentiableOn_eqOn_sub_of_prescribed_isolated_singularities`,
  `TauCeti.prescribed_isolated_singularities_iff_exists_differentiableOn_eqOn_add`, and
  `TauCeti.exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq`: removable extension across
  `Ω ∩ E` and uniqueness modulo functions complex-differentiable on `Ω`.
* `TauCeti.prescribed_isolated_singularities_comp`,
  `TauCeti.prescribed_isolated_singularities_mono`,
  `TauCeti.prescribed_isolated_singularities_comp_add_right`, and
  `TauCeti.prescribed_isolated_singularities_comp_mul_left`: pullback along non-locally-constant
  analytic maps, restriction, translation, and nonzero scaling.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 12.1 and 15.7 (pp. 31, 39-40).
* J. B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978, Chapter VIII, §3.
* L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 5, §2.1.
-/

public section

open Filter Function Metric Polynomial Set Topology
open scoped ENNReal

namespace TauCeti

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Uniqueness modulo complex-differentiable functions and functoriality -/

/-- **Removable-singularity patching across a relatively closed discrete subset.** If `f : ℂ → F` is
complex-differentiable on `Ω \ E` with `Eᶜ ∈ codiscreteWithin Ω` and agrees on `𝓝[≠] a` with a
function analytic at `a` for each `a ∈ Ω ∩ E`, then `f` agrees on `Ω \ E` with a function
complex-differentiable on all of `Ω`. Neither openness of `Ω`, completeness of `F`, nor `E ⊆ Ω` is
required. -/
theorem exists_differentiableOn_eqOn_of_analyticAt_nhdsNE
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f (Ω \ E))
    (hg : ∀ a ∈ Ω ∩ E, ∃ g : ℂ → F, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g) :
    ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn f h (Ω \ E) := by
  classical
  let h : ℂ → F := fun z ↦ if hz : z ∈ Ω ∩ E then (hg z hz).choose z else f z
  have hfh : EqOn f h (Ω \ E) := fun z hz ↦ by simp [h, hz.2]
  refine ⟨h, fun z₀ hz₀ ↦ ?_, hfh⟩
  have hcod : ∀ᶠ z in 𝓝[Ω \ {z₀}] z₀, z ∉ E :=
    mem_codiscreteWithin_iff_forall_mem_nhdsWithin.mp hE z₀ hz₀
  by_cases hz₀E : z₀ ∈ E
  · have hz₀' : z₀ ∈ Ω ∩ E := ⟨hz₀, hz₀E⟩
    obtain ⟨hgan, hfg⟩ := (hg z₀ hz₀').choose_spec
    have hev : h =ᶠ[𝓝[Ω] z₀] (hg z₀ hz₀').choose := by
      have hcod' := eventually_nhdsWithin_iff.mp hcod
      have hfg' := eventuallyEq_nhdsWithin_iff.mp hfg
      refine eventuallyEq_nhdsWithin_iff.mpr ?_
      filter_upwards [hcod', hfg'] with z hzE hzf hzΩ
      rcases eq_or_ne z z₀ with rfl | hne
      · simp [h, hz₀, hz₀E]
      · have hzE' : z ∉ E := hzE ⟨hzΩ, hne⟩
        simp [h, hzE', hzf hne]
    exact hgan.differentiableAt.differentiableWithinAt.congr_of_eventuallyEq hev
      (by simp [h, hz₀, hz₀E])
  · have hE_nhds : Eᶜ ∈ 𝓝[Ω] z₀ := by
      obtain ⟨V, hVopen, hz₀V, hVsub⟩ := mem_nhdsWithin.mp hcod
      refine mem_nhdsWithin.mpr ⟨V, hVopen, hz₀V, fun z hz ↦ ?_⟩
      rcases eq_or_ne z z₀ with rfl | hne
      · exact hz₀E
      · exact hVsub ⟨hz.1, hz.2, hne⟩
    have hev : h =ᶠ[𝓝[Ω] z₀] f := by
      filter_upwards [self_mem_nhdsWithin, hE_nhds] with z hzΩ hzE using (hfh ⟨hzΩ, hzE⟩).symm
    have hdiff : DifferentiableWithinAt ℂ f Ω z₀ :=
      (hf z₀ ⟨hz₀, hz₀E⟩).mono_of_mem_nhdsWithin
        (by rw [Set.sdiff_eq]; exact inter_mem self_mem_nhdsWithin hE_nhds)
    exact hdiff.congr_of_eventuallyEq hev (hfh ⟨hz₀, hz₀E⟩).symm

/-- **Uniqueness for prescribed isolated singularities modulo functions complex-differentiable on
`Ω`.** Two solutions `f₁, f₂` on `Ω \ E` sharing the same singular germs `P` at all points of
`Ω ∩ E` differ on `Ω \ E` by the restriction of a function complex-differentiable on all of `Ω`. -/
theorem exists_differentiableOn_eqOn_sub_of_prescribed_isolated_singularities
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) {f₁ f₂ : ℂ → F} {P : E → ℂ → F}
    (hf₁ : DifferentiableOn ℂ f₁ (Ω \ E)) (hf₂ : DifferentiableOn ℂ f₂ (Ω \ E))
    (hsing₁ : ∀ a : E, a.val ∈ Ω → ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f₁ - P a =ᶠ[𝓝[≠] a.val] g)
    (hsing₂ : ∀ a : E, a.val ∈ Ω → ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f₂ - P a =ᶠ[𝓝[≠] a.val] g) :
    ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) := by
  refine exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hE (hf₁.sub hf₂) ?_
  rintro a ⟨haΩ, haE⟩
  obtain ⟨g₁, hg₁, hf₁g⟩ := hsing₁ ⟨a, haE⟩ haΩ
  obtain ⟨g₂, hg₂, hf₂g⟩ := hsing₂ ⟨a, haE⟩ haΩ
  refine ⟨g₁ - g₂, hg₁.sub hg₂, ?_⟩
  filter_upwards [hf₁g, hf₂g] with z hz₁ hz₂
  simp only [Pi.sub_apply] at hz₁ hz₂ ⊢
  rw [← sub_sub_sub_cancel_right (f₁ z) (f₂ z) (P ⟨a, haE⟩ z), hz₁, hz₂]

/-- **Pullback of prescribed isolated singularities along a non-locally-constant analytic map.**
If `φ : ℂ → ℂ` is analytic and nowhere locally constant on `Ω'` with `MapsTo φ Ω' Ω`, then
preimaging `E` preserves relative codiscreteness and pulls back a solution `(f, P)` on `Ω` to a
solution `(f ∘ φ, fun b ↦ P ⟨φ b, _⟩ ∘ φ)` on `Ω'`. -/
theorem prescribed_isolated_singularities_comp
    {Ω Ω' E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω)
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω') (hnc : ∀ z ∈ Ω', ¬EventuallyConst φ (𝓝 z))
    (hmaps : MapsTo φ Ω' Ω) {f : ℂ → F} {P : E → ℂ → F}
    (hf : DifferentiableOn ℂ f (Ω \ E))
    (hsing : ∀ a : E, a.val ∈ φ '' Ω' →
      ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g) :
    (φ ⁻¹' E)ᶜ ∈ codiscreteWithin Ω' ∧
      DifferentiableOn ℂ (f ∘ φ) (Ω' \ φ ⁻¹' E) ∧
      ∀ b (hb : b ∈ Ω' ∩ φ ⁻¹' E),
        ∃ g : ℂ → F, AnalyticAt ℂ g b ∧
          (f ∘ φ) - (P ⟨φ b, hb.2⟩ ∘ φ) =ᶠ[𝓝[≠] b] g := by
  have hcod : (φ ⁻¹' E)ᶜ ∈ codiscreteWithin Ω' :=
    hφ.preimage_mem_codiscreteWithin hnc (codiscreteWithin_mono hmaps.image_subset hE)
  have hmaps_sdiff : MapsTo φ (Ω' \ φ ⁻¹' E) (Ω \ E) := fun z hz ↦ ⟨hmaps hz.1, hz.2⟩
  refine ⟨hcod, hf.comp (hφ.differentiableOn.mono sdiff_subset) hmaps_sdiff, ?_⟩
  rintro b ⟨hbΩ', hbE⟩
  obtain ⟨g, hg, hfg⟩ := hsing ⟨φ b, hbE⟩ ⟨b, hbΩ', rfl⟩
  exact ⟨g ∘ φ, hg.comp_of_eq (hφ b hbΩ') rfl, ((hφ b hbΩ').map_nhdsNE (hnc b hbΩ')) hfg⟩

/-- **Restriction of prescribed isolated singularities** from `Ω` to any subset `Ω' ⊆ Ω`. -/
theorem prescribed_isolated_singularities_mono
    {Ω Ω' E : Set ℂ} (hΩ' : Ω' ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {f : ℂ → F} {P : E → ℂ → F} (hf : DifferentiableOn ℂ f (Ω \ E))
    (hsing : ∀ a : E, a.val ∈ Ω' →
      ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g) :
    (Ω' ∩ E)ᶜ ∈ codiscreteWithin Ω' ∧
      DifferentiableOn ℂ f (Ω' \ (Ω' ∩ E)) ∧
      ∀ a : ↑(Ω' ∩ E), ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧
        f - P ⟨a.val, a.prop.2⟩ =ᶠ[𝓝[≠] a.val] g := by
  have hcod : Eᶜ ∈ codiscreteWithin Ω' := codiscreteWithin_mono hΩ' hE
  have hcod' : (Ω' ∩ E)ᶜ ∈ codiscreteWithin Ω' := by
    filter_upwards [hcod] with z hz hz' using hz hz'.2
  refine ⟨hcod', hf.mono fun z hz ↦ ⟨hΩ' hz.1, fun hzE ↦ hz.2 ⟨hz.1, hzE⟩⟩, ?_⟩
  rintro ⟨a, haΩ', haE⟩
  exact hsing ⟨a, haE⟩ haΩ'

/-- **Translation invariance of prescribed isolated singularities** along `z ↦ z + c`. -/
theorem prescribed_isolated_singularities_comp_add_right
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) (c : ℂ)
    {f : ℂ → F} {P : E → ℂ → F} (hf : DifferentiableOn ℂ f (Ω \ E))
    (hsing : ∀ a : E, a.val ∈ Ω →
      ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g) :
    ((· + c) ⁻¹' E)ᶜ ∈ codiscreteWithin ((· + c) ⁻¹' Ω) ∧
      DifferentiableOn ℂ (fun z ↦ f (z + c)) ((· + c) ⁻¹' Ω \ (· + c) ⁻¹' E) ∧
      ∀ b (hb : b ∈ (· + c) ⁻¹' Ω ∩ (· + c) ⁻¹' E),
        ∃ g : ℂ → F, AnalyticAt ℂ g b ∧
          (fun z ↦ f (z + c) - P ⟨b + c, hb.2⟩ (z + c)) =ᶠ[𝓝[≠] b] g := by
  have hφ : AnalyticOnNhd ℂ (· + c) ((· + c) ⁻¹' Ω) :=
    fun z _ ↦ analyticAt_id.add analyticAt_const
  have hnc : ∀ z ∈ (· + c) ⁻¹' Ω, ¬EventuallyConst (· + c) (𝓝 z) := fun z _ h ↦
    let ⟨y, hy⟩ := h.eventuallyEq_const
    one_ne_zero (((hasDerivAt_id z).add_const c).unique
      ((hasDerivAt_const z y).congr_of_eventuallyEq hy))
  exact prescribed_isolated_singularities_comp hE hφ hnc (mapsTo_preimage (· + c) Ω) hf
    fun a ha ↦ hsing a ((image_preimage_subset (· + c) Ω) ha)

/-- **Nonzero scaling invariance of prescribed isolated singularities** along `z ↦ c * z`
(`c ≠ 0`). -/
theorem prescribed_isolated_singularities_comp_mul_left
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) {c : ℂ} (hc : c ≠ 0)
    {f : ℂ → F} {P : E → ℂ → F} (hf : DifferentiableOn ℂ f (Ω \ E))
    (hsing : ∀ a : E, a.val ∈ Ω →
      ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g) :
    ((c * ·) ⁻¹' E)ᶜ ∈ codiscreteWithin ((c * ·) ⁻¹' Ω) ∧
      DifferentiableOn ℂ (fun z ↦ f (c * z)) ((c * ·) ⁻¹' Ω \ (c * ·) ⁻¹' E) ∧
      ∀ b (hb : b ∈ (c * ·) ⁻¹' Ω ∩ (c * ·) ⁻¹' E),
        ∃ g : ℂ → F, AnalyticAt ℂ g b ∧
          (fun z ↦ f (c * z) - P ⟨c * b, hb.2⟩ (c * z)) =ᶠ[𝓝[≠] b] g := by
  have hφ : AnalyticOnNhd ℂ (c * ·) ((c * ·) ⁻¹' Ω) :=
    fun z _ ↦ analyticAt_const.mul analyticAt_id
  have hnc : ∀ z ∈ (c * ·) ⁻¹' Ω, ¬EventuallyConst (c * ·) (𝓝 z) := fun z _ h ↦
    let ⟨y, hy⟩ := h.eventuallyEq_const
    hc ((by simpa using (hasDerivAt_id z).const_mul c : HasDerivAt (c * ·) c z).unique
      ((hasDerivAt_const z y).congr_of_eventuallyEq hy))
  exact prescribed_isolated_singularities_comp hE hφ hnc (mapsTo_preimage (c * ·) Ω) hf
    fun a ha ↦ hsing a ((image_preimage_subset (c * ·) Ω) ha)

/-! ### Global Mittag-Leffler construction -/

section CompleteSpace

variable [CompleteSpace F]

/-- Runge approximation on a filled compact set `K ⊆ Ω` of `laurentNegPart` at a pole `a ∉ K` by a
function holomorphic on `Ω`. -/
private theorem HasLaurentSeriesOnAnnulus.exists_differentiableOn_norm_laurentNegPart_sub_lt
    {p : ℂ → F} {c : ℤ → F} {a : ℂ} {R : ℝ≥0∞} {K Ω : Set ℂ}
    (h : HasLaurentSeriesOnAnnulus p c a 0 R)
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (ha : a ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖laurentNegPart c a z - g z‖ < ε := by
  have hKr : K ⊆ (closedBall a 0)ᶜ := by
    rw [closedBall_zero]
    exact fun z hz hza ↦ ha (mem_singleton_iff.mp hza ▸ hz)
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (h.tendstoUniformlyOn_laurentNegPart_of_isCompact hK hKr) (ε / 2) (half_pos hε)).exists
  obtain ⟨g, hg, hgK⟩ := hfill.exists_differentiableOn_norm_sum_zpow_neg_sub_lt hΩ hK hKΩ ha N
    (fun k ↦ c (-((k : ℤ) + 1))) (half_pos hε)
  refine ⟨g, hg, fun z hz ↦ ?_⟩
  have h₁ : ‖laurentNegPart c a z -
      ∑ k ∈ Finset.range N, (z - a) ^ (-((k : ℤ) + 1)) • c (-((k : ℤ) + 1))‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN z hz
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (by linarith [hgK z hz])

/-- Simultaneous Runge approximation on `K ⊆ Ω` of a finite sum of `laurentNegPart`s over poles in
`S` avoiding `K`. -/
private theorem exists_differentiableOn_norm_sum_laurentNegPart_sub_lt
    {E Ω K : Set ℂ} {P : E → ℂ → F} {c : E → ℤ → F} {R : E → ℝ≥0∞}
    (hcR : ∀ a : E, HasLaurentSeriesOnAnnulus (P a) (c a) a.val 0 (R a))
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (S : Finset E) (hS : ∀ a ∈ S, a.val ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → F, DifferentiableOn ℂ G Ω ∧
      ∀ z ∈ K, ‖(∑ a ∈ S, laurentNegPart (c a) a.val z) - G z‖ < ε := by
  have hε' : 0 < ε / (S.card + 1 : ℝ) := by positivity
  choose! g hg hgK using fun (a : E) (ha : a ∈ S) ↦
    (hcR a).exists_differentiableOn_norm_laurentNegPart_sub_lt hfill hΩ hK hKΩ (hS a ha) hε'
  refine ⟨fun z ↦ ∑ a ∈ S, g a z, DifferentiableOn.fun_sum fun a ha ↦ hg a ha, fun z hz ↦ ?_⟩
  calc ‖(∑ a ∈ S, laurentNegPart (c a) a.val z) - ∑ a ∈ S, g a z‖
      = ‖∑ a ∈ S, (laurentNegPart (c a) a.val z - g a z)‖ := by rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ a ∈ S, ‖laurentNegPart (c a) a.val z - g a z‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S, (ε / (S.card + 1 : ℝ)) := Finset.sum_le_sum fun a ha ↦ (hgK a ha z hz).le
    _ = S.card * (ε / (S.card + 1 : ℝ)) := by simp
    _ < (S.card + 1 : ℝ) * (ε / (S.card + 1 : ℝ)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

/-- Core series assembly along a filled compact exhaustion `K` of an open set `Ω`: given Laurent
data `(c a, R a)` at `a : E` and the finite pole sets `A n` in `K n`, constructs `f : ℂ → F` whose
restriction to each `interior (K m)` is `∑ a ∈ A m, laurentNegPart (c a) a.val` plus a holomorphic
remainder. -/
private theorem exists_tsum_eqOn_sum_laurentNegPart_add_differentiableOn
    {Ω E : Set ℂ} (hΩ : IsOpen Ω) {K : ℕ → Set ℂ}
    (hKcpt : ∀ n, IsCompact (K n)) (hKsub : ∀ n, K n ⊆ K (n + 1)) (hKΩ : ∀ n, K n ⊆ Ω)
    (hKfill : ∀ n, IsFilledIn (K n) Ω) {A : ℕ → Finset E}
    (hA : ∀ n (a : E), a ∈ A n ↔ a.val ∈ K n)
    {P : E → ℂ → F} {c : E → ℤ → F} {R : E → ℝ≥0∞}
    (hcR : ∀ a : E, HasLaurentSeriesOnAnnulus (P a) (c a) a.val 0 (R a)) :
    ∃ f : ℂ → F, ∀ m : ℕ, ∃ H : ℂ → F, DifferentiableOn ℂ H (interior (K m)) ∧
      EqOn f ((fun z ↦ ∑ a ∈ A m, laurentNegPart (c a) a.val z) + H) (interior (K m)) := by
  classical
  have hKmono : Monotone K := monotone_nat_of_le_succ hKsub
  have hAmono : Monotone A := fun i j hij a ha ↦ (hA j a).mpr (hKmono hij ((hA i a).mp ha))
  let B : ℕ → Finset E := fun k ↦ Nat.rec (A 0) (fun n _ ↦ A (n + 1) \ A n) k
  have hB_avoid (n : ℕ) : ∀ a ∈ B (n + 1), a.val ∉ K n :=
    fun a ha haK ↦ (Finset.mem_sdiff.mp ha).2 ((hA n a).mpr haK)
  choose Q hQdiff hQlt using fun n : ℕ ↦
    exists_differentiableOn_norm_sum_laurentNegPart_sub_lt hcR (hKfill n) hΩ (hKcpt n) (hKΩ n)
      (B (n + 1)) (hB_avoid n) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))
  let Q' : ℕ → ℂ → F := fun k ↦ Nat.rec 0 (fun n _ ↦ Q n) k
  let term : ℕ → ℂ → F := fun k z ↦ (∑ a ∈ B k, laurentNegPart (c a) a.val z) - Q' k z
  refine ⟨fun z ↦ ∑' k, term k z, fun m ↦ ?_⟩
  have hsumm : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ (k + (m + 1)) :=
    (summable_nat_add_iff (m + 1)).mpr summable_geometric_two
  have hle (k : ℕ) {z : ℂ} (hz : z ∈ interior (K m)) :
      ‖term (k + (m + 1)) z‖ ≤ (1 / 2 : ℝ) ^ (k + (m + 1)) := by
    have hzK : z ∈ K (k + m) := hKmono (Nat.le_add_left m k) (interior_subset hz)
    exact (hQlt (k + m) z hzK).le
  have hterm_diff (k : ℕ) : DifferentiableOn ℂ (term (k + (m + 1))) (interior (K m)) := by
    refine (DifferentiableOn.fun_sum fun a ha ↦ ?_).sub
      ((hQdiff (k + m)).mono (interior_subset.trans (hKΩ m)))
    refine (hcR a).differentiableOn_laurentNegPart.mono fun z hz hza ↦ ?_
    exact hB_avoid (k + m) a ha
      ((mem_singleton_iff.mp (by simpa only [closedBall_zero] using hza)) ▸
        hKmono (Nat.le_add_left m k) (interior_subset hz))
  refine ⟨fun z ↦ (∑' k, term (k + (m + 1)) z) - ∑ k ∈ Finset.range (m + 1), Q' k z, ?_, ?_⟩
  · refine (TendstoUniformlyOn.differentiableOn
      (tendstoUniformlyOn_tsum hsumm fun k _ hz ↦ hle k hz)
      (Eventually.of_forall fun S ↦ DifferentiableOn.fun_sum fun k _ ↦ hterm_diff k)
      isOpen_interior).sub (DifferentiableOn.fun_sum fun k _ ↦ ?_)
    cases k with
    | zero => exact differentiableOn_const 0
    | succ n => exact (hQdiff n).mono (interior_subset.trans (hKΩ m))
  · intro z hz
    have hs : Summable fun k ↦ term k z :=
      (summable_nat_add_iff (m + 1)).mp (.of_norm_bounded hsumm fun k ↦ hle k hz)
    have hhead : ∑ k ∈ Finset.range (m + 1), term k z =
        (∑ a ∈ A m, laurentNegPart (c a) a.val z) - ∑ k ∈ Finset.range (m + 1), Q' k z := by
      rw [Finset.sum_sub_distrib, Finset.sum_range_succ']
      dsimp [B]
      simp_rw [Finset.sum_sdiff_eq_sub (hAmono (Nat.le_succ _))]
      rw [Finset.sum_range_sub (fun k ↦ ∑ a ∈ A k, laurentNegPart (c a) a.val z) m, sub_add_cancel]
    simp only [Pi.add_apply]
    rw [← hs.sum_add_tsum_nat_add (m + 1), hhead]
    abel

/-- Open-set case of `exists_holomorphic_prescribed_isolated_singularities`. -/
private theorem exists_holomorphic_prescribed_isolated_singularities_of_isOpen
    {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ → F} (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g := by
  classical
  obtain ⟨K, hKcpt, hKint, hKunion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKsub (n : ℕ) : K n ⊆ K (n + 1) := (hKint n).trans interior_subset
  have hKΩ (n : ℕ) : K n ⊆ Ω := hKunion ▸ subset_iUnion K n
  have hfin (n : ℕ) : (((↑) : E → ℂ) ⁻¹' K n).Finite := by
    have hKE : (K n ∩ E).Finite := by
      simpa only [Set.sdiff_compl] using
        (hKcpt n).finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono (hKΩ n) hE)
    exact (hKE.preimage Subtype.val_injective.injOn).subset fun a ha ↦ ⟨ha, a.prop⟩
  let A : ℕ → Finset E := fun n ↦ (hfin n).toFinset
  choose c R hcR using fun a : E ↦
    exists_hasLaurentSeriesOnAnnulus_of_eventually_differentiableAt (hP a)
  obtain ⟨f, hfK⟩ := exists_tsum_eqOn_sum_laurentNegPart_add_differentiableOn hΩ hKcpt hKsub hKΩ
    hKfill (A := A) (fun n a ↦ by simp [A]) hcR
  refine ⟨f, fun z₀ hz₀ ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨n, hz₀n⟩ := mem_iUnion.mp (hKunion ▸ hz₀.1)
    obtain ⟨H, hH, hfH⟩ := hfK (n + 1)
    have hopen : IsOpen (interior (K (n + 1)) \ E) := (Set.sdiff_eq _ _).symm ▸
      isOpen_interior.inter_of_mem_codiscreteWithin
        (codiscreteWithin_mono (interior_subset.trans (hKΩ (n + 1))) hE)
    have hsum_diff : DifferentiableOn ℂ
        ((fun z ↦ ∑ b ∈ A (n + 1), laurentNegPart (c b) b.val z) + H)
        (interior (K (n + 1)) \ E) := by
      refine (DifferentiableOn.fun_sum fun b _ ↦ ?_).add (hH.mono sdiff_subset)
      exact (hcR b).differentiableOn_laurentNegPart.mono fun z hz hzb ↦
        hz.2 ((mem_singleton_iff.mp (by simpa only [closedBall_zero] using hzb)) ▸ b.prop)
    exact ((hsum_diff.congr (hfH.mono sdiff_subset)).differentiableAt
      (hopen.mem_nhds ⟨hKint n hz₀n, hz₀.2⟩)).differentiableWithinAt
  · obtain ⟨n, han⟩ := mem_iUnion.mp (hKunion ▸ hEΩ a.prop)
    obtain ⟨H, hH, hfH⟩ := hfK (n + 1)
    have haA : a ∈ A (n + 1) := by simp [A, hKsub n han]
    have ha_int : a.val ∈ interior (K (n + 1)) := hKint n han
    refine ⟨-laurentPosPart (c a) a.val +
        (fun z ↦ (∑ b ∈ (A (n + 1)).erase a, laurentNegPart (c b) b.val z) + H z), ?_, ?_⟩
    · refine ((hcR a).analyticOnNhd_laurentPosPart a.val
          (mem_eball_self (hcR a).outerRadius_pos)).neg.add ?_
      refine (Finset.analyticAt_fun_sum _ fun b hb ↦ ?_).add
        (hH.analyticAt (isOpen_interior.mem_nhds ha_int))
      exact (hcR b).analyticOnNhd_laurentNegPart a.val
        (by simpa [closedBall_zero] using Subtype.val_injective.ne (Finset.ne_of_mem_erase hb).symm)
    · have hball : eball a.val (R a) \ closedBall a.val 0 ∈ 𝓝[≠] a.val := by
        rw [closedBall_zero]
        exact inter_mem (nhdsWithin_le_nhds
          (isOpen_eball.mem_nhds (mem_eball_self (hcR a).outerRadius_pos))) self_mem_nhdsWithin
      filter_upwards [nhdsWithin_le_nhds (isOpen_interior.mem_nhds ha_int), hball] with z hz₁ hz₂
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, hfH hz₁,
        (hcR a).eq_laurentPosPart_add_laurentNegPart hz₂,
        ← Finset.add_sum_erase (A (n + 1)) (fun b ↦ laurentNegPart (c b) b.val z) haA]
      abel

/-- **Global realization of prescribed isolated singularities.** Let `E ⊆ Ω` be discrete and
relatively closed in `Ω ⊆ ℂ` (`Eᶜ ∈ codiscreteWithin Ω`), and let `F` be a complex Banach space.
Given at each `a : E` a germ `P a : ℂ → F` complex-differentiable on a punctured neighborhood of
`a`, there exists `f : ℂ → F` complex-differentiable on `Ω \ E` such that at every `a : E` the
difference `f - P a` agrees on `𝓝[≠] a` with a function analytic at `a`. Both poles and essential
singularities are allowed, and `Ω` need not be open. -/
theorem exists_holomorphic_prescribed_isolated_singularities
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ → F} (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g := by
  let Ω₀ : Set ℂ := (derivedSet E)ᶜ
  have hΩ_sub : Ω ⊆ Ω₀ := subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f, hf, hsing⟩ := exists_holomorphic_prescribed_isolated_singularities_of_isOpen
    (isClosed_derivedSet E).isOpen_compl (hEΩ.trans hΩ_sub)
    (compl_mem_codiscreteWithin_of_subset_compl_derivedSet subset_rfl) hP
  exact ⟨f, hf.mono (sdiff_subset_sdiff hΩ_sub subset_rfl), hsing⟩

/-- **Mittag-Leffler theorem for meromorphic germs.** Let `E ⊆ Ω` satisfy
`Eᶜ ∈ codiscreteWithin Ω`, and let `F` be a complex Banach space. Given a germ `P a : ℂ → F`
meromorphic at `a` for each `a : E`, there exists `f : ℂ → F` meromorphic on `Ω` and
complex-differentiable on `Ω \ E` such that `f - P a` agrees on `𝓝[≠] a` with a function analytic
at `a` for every `a : E`. -/
theorem exists_meromorphic_prescribed_principal_parts
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ → F} (hP : ∀ a : E, MeromorphicAt (P a) a.val) :
    ∃ f : ℂ → F, MeromorphicOn f Ω ∧ DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g := by
  let Ω₀ : Set ℂ := (derivedSet E)ᶜ
  have hΩ₀_open : IsOpen Ω₀ := (isClosed_derivedSet E).isOpen_compl
  have hΩ_sub : Ω ⊆ Ω₀ := subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE
  have hE₀ : Eᶜ ∈ codiscreteWithin Ω₀ :=
    compl_mem_codiscreteWithin_of_subset_compl_derivedSet subset_rfl
  obtain ⟨f, hf₀, hsing⟩ := exists_holomorphic_prescribed_isolated_singularities_of_isOpen
    hΩ₀_open (hEΩ.trans hΩ_sub) hE₀
    fun a ↦ (hP a).eventually_analyticAt.mono fun _ hz ↦ hz.differentiableAt
  refine ⟨f, fun z hzΩ ↦ ?_, hf₀.mono (sdiff_subset_sdiff hΩ_sub subset_rfl), hsing⟩
  by_cases hzE : z ∈ E
  · obtain ⟨g, hg, hfg⟩ := hsing ⟨z, hzE⟩
    refine ((hP ⟨z, hzE⟩).add hg.meromorphicAt).congr ?_
    filter_upwards [hfg] with w hw
    simp only [Pi.add_apply, ← hw, Pi.sub_apply, add_sub_cancel]
  · have hopen : IsOpen (Ω₀ \ E) := by
      rw [Set.sdiff_eq]
      exact hΩ₀_open.inter_of_mem_codiscreteWithin hE₀
    exact (hf₀.analyticAt (hopen.mem_nhds ⟨hΩ_sub hzΩ, hzE⟩)).meromorphicAt

/-- **Characterization of all solutions on an open set.** Given a reference solution `f₀` on an
open set `Ω` with `E ⊆ Ω` and `Eᶜ ∈ codiscreteWithin Ω`, an arbitrary function `f : ℂ → F` solves
the same isolated-singularity problem if and only if it agrees on `Ω \ E` with `f₀ + h` for some
`h` holomorphic on all of `Ω`. -/
theorem prescribed_isolated_singularities_iff_exists_differentiableOn_eqOn_add
    {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ → F} {f₀ f : ℂ → F} (hf₀ : DifferentiableOn ℂ f₀ (Ω \ E))
    (hsing₀ : ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f₀ - P a =ᶠ[𝓝[≠] a.val] g) :
    (DifferentiableOn ℂ f (Ω \ E) ∧
        ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ f - P a =ᶠ[𝓝[≠] a.val] g) ↔
      ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn f (f₀ + h) (Ω \ E) := by
  refine ⟨fun ⟨hf, hsing⟩ ↦ ?_, fun ⟨h, hh, hfh⟩ ↦ ?_⟩
  · obtain ⟨h, hh, heq⟩ :=
      exists_differentiableOn_eqOn_sub_of_prescribed_isolated_singularities hE hf hf₀
        (fun a _ ↦ hsing a) (fun a _ ↦ hsing₀ a)
    refine ⟨h, hh, fun z hz ↦ ?_⟩
    simp only [Pi.add_apply, ← heq hz, Pi.sub_apply, add_sub_cancel]
  · refine ⟨(hf₀.add (hh.mono sdiff_subset)).congr hfh, fun a ↦ ?_⟩
    obtain ⟨g₀, hg₀, hfg₀⟩ := hsing₀ a
    have hE_nhds : Eᶜ ∈ 𝓝[≠] a.val := by
      have hmem := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hE a.val (hEΩ a.prop)
      filter_upwards [nhdsWithin_le_nhds (hΩ.mem_nhds (hEΩ a.prop)), hmem] with z hzΩ hz
      exact hz.resolve_right (not_not.mpr hzΩ)
    refine ⟨g₀ + h, hg₀.add (hh.analyticAt (hΩ.mem_nhds (hEΩ a.prop))), ?_⟩
    filter_upwards [nhdsWithin_le_nhds (hΩ.mem_nhds (hEΩ a.prop)), hE_nhds, hfg₀]
      with z hzΩ hzE hz₀
    simp only [Pi.sub_apply, Pi.add_apply, hfh ⟨hzΩ, hzE⟩, ← hz₀]
    abel

end CompleteSpace

end NormedSpace

/-! ### Specialization to algebraic principal parts of scalar meromorphic germs -/

/-- **Mittag-Leffler realization of prescribed polynomial principal parts.** Given `E ⊆ Ω` with
`Eᶜ ∈ codiscreteWithin Ω` and at each `a : E` a polynomial `P a : ℂ[X]` without constant term
(`(P a).coeff 0 = 0`), there exists `f : ℂ → ℂ` meromorphic on `Ω` and complex-differentiable on
`Ω \ E` whose `meromorphicGerms.principalPart` at every `a : E` is `P a`. -/
theorem exists_meromorphicOn_principalPart_mk_eq
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ[X]} (hP : ∀ a : E, (P a).coeff 0 = 0) :
    ∃ f : ℂ → ℂ, ∃ hf : MeromorphicOn f Ω, DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E,
        meromorphicGerms.principalPart (meromorphicGerms.mk f (hf a.val (hEΩ a.prop))) = P a := by
  obtain ⟨f, hfm, hf, hsing⟩ := exists_meromorphic_prescribed_principal_parts hEΩ hE
    (P := fun a z ↦ (P a).eval (z - a.val)⁻¹) fun a ↦ (P a).meromorphicAt_eval_inv_sub a.val
  refine ⟨f, hfm, hf, fun a ↦ ?_⟩
  obtain ⟨g, hg, hfg⟩ := hsing a
  refine meromorphicGerms.principalPart_eq_iff.mpr ⟨hP a, g, hg, ?_⟩
  rw [AddSubgroupClass.coe_sub, meromorphicGerms.coe_mk, Polynomial.coe_evalInvSub,
    ← Germ.coe_sub, Germ.coe_eq]
  exact hfg

/-- **Uniqueness via `meromorphicGerms.principalPart` modulo functions complex-differentiable on
`Ω`.** Two functions meromorphic on `Ω ∩ E`, complex-differentiable on `Ω \ E`
(`Eᶜ ∈ codiscreteWithin Ω`), and having the same algebraic `meromorphicGerms.principalPart` at
every point of `Ω ∩ E` differ on `Ω \ E` by a function complex-differentiable on all of `Ω`. -/
theorem exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) {f₁ f₂ : ℂ → ℂ}
    (hf₁m : MeromorphicOn f₁ (Ω ∩ E)) (hf₂m : MeromorphicOn f₂ (Ω ∩ E))
    (hf₁ : DifferentiableOn ℂ f₁ (Ω \ E)) (hf₂ : DifferentiableOn ℂ f₂ (Ω \ E))
    (hprin : ∀ a (ha : a ∈ Ω ∩ E),
      meromorphicGerms.principalPart (meromorphicGerms.mk f₁ (hf₁m a ha)) =
        meromorphicGerms.principalPart (meromorphicGerms.mk f₂ (hf₂m a ha))) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) :=
  exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hE (hf₁.sub hf₂) fun a ha ↦
    (meromorphicGerms.principalPart_mk_eq_principalPart_mk_iff
      (hf₁m a ha) (hf₂m a ha)).mp (hprin a ha)

end TauCeti
