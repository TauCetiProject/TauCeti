/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Series
public import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
import Mathlib.Topology.DerivedSet
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.Laurent.IsolatedSingularity
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.MetricSpace.EBall

/-!
# Mittag-Leffler theorem and prescribed isolated singularities on subsets of `ℂ`

Let `F` be a complex normed space. Given a subset `Ω ⊆ ℂ` and a subset `E ⊆ Ω` with no
accumulation points in `Ω` (`Eᶜ ∈ Filter.codiscreteWithin Ω`), this file develops the local
singular-part congruence relation `TauCeti.HasSameSingularPartAt` and proves that, when `F` is a
complex Banach space, arbitrary local singular behaviors at the points of `E` can be realized
simultaneously by a single global function `f : ℂ → F` complex-analytic on `Ω \ E`.

More concretely:

1. **Singular-part congruence** (`TauCeti.HasSameSingularPartAt f g c`): `f - g` agrees on `𝓝[≠] c`
   with a function analytic at `c`. This is an `F`-linear equivalence relation compatible with
   meromorphy, negative meromorphic order, negative Laurent coefficients, and
   `TauCeti.meromorphicGerms.principalPart`.
2. **Global uniqueness modulo analytic functions**
   (`TauCeti.exists_analyticOnNhd_eqOn_sub_of_hasSameSingularPartAt` and
   `TauCeti.analyticOnNhd_and_forall_hasSameSingularPartAt_iff`): any two functions analytic on
   `Ω \ E` with the same singular parts at `Ω ∩ E` differ on `Ω \ E` by a function analytic on `Ω`
   (without assuming completeness of `F`, openness of `Ω`, or discreteness of `E`).
3. **Prescribed isolated singularities and Mittag-Leffler's theorem**
   (`TauCeti.exists_holomorphic_prescribed_isolated_singularities`,
   `TauCeti.exists_meromorphic_prescribed_principal_parts`,
   `TauCeti.exists_meromorphic_hasSameSingularPartAt_eval_inv_sub`, and
   `TauCeti.exists_meromorphic_principalPart_eq`): for complete `F`, if each `a : E` carries a
   local model `P a : ℂ → F` complex-differentiable on a punctured neighborhood of `a` (including
   arbitrary essential singularities as well as poles; no vanishing orders are prescribed), there
   exists `f : ℂ → F` complex-analytic on `Ω \ E` with `HasSameSingularPartAt f (P a) a` at every
   `a : E`. When each `P a` is meromorphic at `a`, `f` is `MeromorphicOn f Ω`.

For arbitrary `Ω ⊆ ℂ` with `E ⊆ Ω` and `Eᶜ ∈ codiscreteWithin Ω`, the set `E` has no accumulation
points in `Ω`, so `Ω` is contained in the open set `(derivedSet E)ᶜ` in which `E` remains closed
and discrete. On `(derivedSet E)ᶜ`, the proof extracts the global negative Laurent part
`laurentNegPart` of each `P a` on `ℂ \ {a}`, partitions `E` along a filled compact exhaustion
(`IsOpen.exists_isFilledIn_compact_exhaustion`), and corrects each finite shell sum by a holomorphic
approximant obtained from `IsFilledIn.exists_differentiableOn_norm_inv_sub_lt` and uniform exterior
tail convergence (`HasLaurentSeriesOnAnnulus.tendstoUniformlyOn_laurentNegPart`).

## Main definitions

* `TauCeti.HasSameSingularPartAt f g c`: `f - g` agrees on `𝓝[≠] c` with a function complex-analytic
  at `c`.

## Main results

* `TauCeti.HasLaurentSeriesOnAnnulus.hasSameSingularPartAt_iff` and
  `TauCeti.meromorphicGerms.principalPart_eq_iff_hasSameSingularPartAt`: Laurent-coefficient and
  algebraic principal-part characterizations of `HasSameSingularPartAt`.
* `TauCeti.exists_analyticOnNhd_eqOn_sub_of_hasSameSingularPartAt` and
  `TauCeti.analyticOnNhd_and_forall_hasSameSingularPartAt_iff`: global uniqueness and affine-space
  description of solutions modulo `AnalyticOnNhd ℂ · Ω`.
* `TauCeti.exists_holomorphic_prescribed_isolated_singularities`: global realization of arbitrary
  punctured-neighborhood holomorphic germs (including essential singularities) at a relatively
  closed discrete subset `E ⊆ Ω`.
* `TauCeti.exists_meromorphic_prescribed_principal_parts`,
  `TauCeti.exists_meromorphic_hasSameSingularPartAt_eval_inv_sub`, and
  `TauCeti.exists_meromorphic_principalPart_eq`: Banach-valued and polynomial principal-part forms
  of Mittag-Leffler's theorem on subsets of `ℂ`.

## References

* Armin Rainer, *Advanced Complex Analysis*, Theorems 12.1 and 15.7 (singular-part realization).
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §2.1.
* John B. Conway, *Functions of One Complex Variable I*, Graduate Texts in Mathematics 11,
  Springer, 2nd edition, 1978, Chapter VIII, §3.
-/

public section

open Complex Filter Metric Polynomial Set
open scoped ENNReal NNReal Real Topology

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-! ### Singular-part congruence at a point -/

/-- Two functions `f, g : ℂ → F` have the same singular part at `c : ℂ` if their difference `f - g`
agrees on a punctured neighborhood `𝓝[≠] c` with a function complex-analytic at `c`. -/
def HasSameSingularPartAt (f g : ℂ → F) (c : ℂ) : Prop :=
  ∃ h : ℂ → F, AnalyticAt ℂ h c ∧ f - g =ᶠ[𝓝[≠] c] h

/-- Unfolded characterization of `HasSameSingularPartAt`. -/
theorem hasSameSingularPartAt_def (f g : ℂ → F) (c : ℂ) :
    HasSameSingularPartAt f g c ↔ ∃ h : ℂ → F, AnalyticAt ℂ h c ∧ f - g =ᶠ[𝓝[≠] c] h :=
  Iff.rfl

namespace HasSameSingularPartAt

/-- `HasSameSingularPartAt` is reflexive. -/
protected theorem refl (f : ℂ → F) (c : ℂ) : HasSameSingularPartAt f f c :=
  ⟨0, analyticAt_const, by simp [sub_self]⟩

/-- `HasSameSingularPartAt` is symmetric. -/
protected theorem symm {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c) :
    HasSameSingularPartAt g f c := by
  obtain ⟨k, hk, hfg⟩ := h
  refine ⟨-k, hk.neg, ?_⟩
  filter_upwards [hfg] with z hz
  simp only [Pi.sub_apply, Pi.neg_apply] at hz ⊢
  rw [← neg_sub, hz]

/-- `HasSameSingularPartAt` is transitive. -/
protected theorem trans {f₁ f₂ f₃ : ℂ → F} {c : ℂ} (h₁₂ : HasSameSingularPartAt f₁ f₂ c)
    (h₂₃ : HasSameSingularPartAt f₂ f₃ c) : HasSameSingularPartAt f₁ f₃ c := by
  obtain ⟨k₁, hk₁, heq₁⟩ := h₁₂
  obtain ⟨k₂, hk₂, heq₂⟩ := h₂₃
  refine ⟨k₁ + k₂, hk₁.add hk₂, ?_⟩
  filter_upwards [heq₁, heq₂] with z hz₁ hz₂
  simp only [Pi.sub_apply, Pi.add_apply] at hz₁ hz₂ ⊢
  rw [← hz₁, ← hz₂, sub_add_sub_cancel]

/-- Punctured-neighborhood congruence for `HasSameSingularPartAt` in both function arguments. -/
protected theorem congr {f₁ f₂ g₁ g₂ : ℂ → F} {c : ℂ} (hf : f₁ =ᶠ[𝓝[≠] c] f₂)
    (hg : g₁ =ᶠ[𝓝[≠] c] g₂) (h : HasSameSingularPartAt f₁ g₁ c) :
    HasSameSingularPartAt f₂ g₂ c := by
  obtain ⟨k, hk, heq⟩ := h
  exact ⟨k, hk, (hf.symm.sub hg.symm).trans heq⟩

/-- Addition preserves `HasSameSingularPartAt`. -/
protected theorem add {f₁ f₂ g₁ g₂ : ℂ → F} {c : ℂ} (h₁ : HasSameSingularPartAt f₁ g₁ c)
    (h₂ : HasSameSingularPartAt f₂ g₂ c) : HasSameSingularPartAt (f₁ + f₂) (g₁ + g₂) c := by
  obtain ⟨k₁, hk₁, heq₁⟩ := h₁
  obtain ⟨k₂, hk₂, heq₂⟩ := h₂
  refine ⟨k₁ + k₂, hk₁.add hk₂, ?_⟩
  filter_upwards [heq₁, heq₂] with z hz₁ hz₂
  simp only [Pi.sub_apply, Pi.add_apply] at hz₁ hz₂ ⊢
  rw [add_sub_add_comm, hz₁, hz₂]

/-- Negation preserves `HasSameSingularPartAt`. -/
protected theorem neg {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c) :
    HasSameSingularPartAt (-f) (-g) c := by
  obtain ⟨k, hk, heq⟩ := h
  refine ⟨-k, hk.neg, ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.sub_apply, Pi.neg_apply] at hz ⊢
  rw [neg_sub_neg, ← neg_sub, hz]

/-- Subtraction preserves `HasSameSingularPartAt`. -/
protected theorem sub {f₁ f₂ g₁ g₂ : ℂ → F} {c : ℂ} (h₁ : HasSameSingularPartAt f₁ g₁ c)
    (h₂ : HasSameSingularPartAt f₂ g₂ c) : HasSameSingularPartAt (f₁ - f₂) (g₁ - g₂) c := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scalar multiplication by a complex constant preserves `HasSameSingularPartAt`. -/
protected theorem const_smul {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c) (a : ℂ) :
    HasSameSingularPartAt (a • f) (a • g) c := by
  obtain ⟨k, hk, heq⟩ := h
  refine ⟨a • k, hk.const_smul, ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.sub_apply, Pi.smul_apply] at hz ⊢
  rw [← smul_sub, hz]

/-- Postcomposition with a continuous complex-linear map preserves `HasSameSingularPartAt`. -/
theorem comp_continuousLinearMap {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c)
    (L : F →L[ℂ] G) : HasSameSingularPartAt (L ∘ f) (L ∘ g) c := by
  obtain ⟨k, hk, heq⟩ := h
  refine ⟨L ∘ k, (L.analyticAt (k c)).comp hk, ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.sub_apply, Function.comp_apply] at hz ⊢
  rw [← map_sub, hz]

/-- `HasSameSingularPartAt` preserves meromorphy at `c`. -/
theorem meromorphicAt_iff {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c) :
    MeromorphicAt f c ↔ MeromorphicAt g c := by
  obtain ⟨k, hk, heq⟩ := h
  have hsub : MeromorphicAt (f - g) c := hk.meromorphicAt.congr heq.symm
  exact ⟨fun hf => (MeromorphicAt.meromorphicAt_sub_iff_meromorphicAt₁ hf).mp hsub,
    fun hg => (MeromorphicAt.meromorphicAt_sub_iff_meromorphicAt₂ hg).mp hsub⟩

/-- When `g` has strictly negative meromorphic order at `c` (a genuine pole), any `f` with the same
singular part at `c` has the same meromorphic order at `c`. -/
theorem meromorphicOrderAt_eq_of_neg {f g : ℂ → F} {c : ℂ} (h : HasSameSingularPartAt f g c)
    (hord : meromorphicOrderAt g c < 0) :
    meromorphicOrderAt f c = meromorphicOrderAt g c := by
  have hg : MeromorphicAt g c := meromorphicAt_of_meromorphicOrderAt_ne_zero hord.ne
  obtain ⟨k, hk, heq⟩ := h
  have hfg : f =ᶠ[𝓝[≠] c] g + k := by
    filter_upwards [heq] with z hz
    simp only [Pi.sub_apply, Pi.add_apply] at hz ⊢
    exact eq_add_of_sub_eq' hz
  have hlt : meromorphicOrderAt g c < meromorphicOrderAt k c :=
    hord.trans_le hk.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hfg,
    meromorphicOrderAt_add_of_ne hg hk.meromorphicAt hlt.ne, min_eq_left hlt.le]

/-- Precomposing with `z ↦ z + d` pulls back `HasSameSingularPartAt` from `c + d` to `c`. -/
theorem comp_add_const {f g : ℂ → F} {c d : ℂ} (h : HasSameSingularPartAt f g (c + d)) :
    HasSameSingularPartAt (fun z => f (z + d)) (fun z => g (z + d)) c := by
  obtain ⟨k, hk, heq⟩ := h
  refine ⟨fun z => k (z + d),
    AnalyticAt.comp (g := k) (f := fun z : ℂ => z + d) (x := c) hk
      (analyticAt_id.add analyticAt_const), ?_⟩
  have hcont : Continuous fun z : ℂ => z + d := by fun_prop
  have hmap : Tendsto (fun z : ℂ => z + d) (𝓝[≠] c) (𝓝[≠] (c + d)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hcont.tendsto c).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_iff.mpr <| Eventually.of_forall fun z hz => mt add_right_cancel hz⟩
  exact hmap.eventually heq

/-- Precomposing with `z ↦ z * a` pulls back `HasSameSingularPartAt` from `c * a` to `c`. -/
theorem comp_mul_const {f g : ℂ → F} {a c : ℂ}
    (h : HasSameSingularPartAt f g (c * a)) :
    HasSameSingularPartAt (fun z => f (z * a)) (fun z => g (z * a)) c := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨fun _ => f 0 - g 0, analyticAt_const, by simp only [mul_zero]; rfl⟩
  · obtain ⟨k, hk, heq⟩ := h
    refine ⟨fun z => k (z * a),
      AnalyticAt.comp (g := k) (f := fun z : ℂ => z * a) (x := c) hk
        (analyticAt_id.mul analyticAt_const), ?_⟩
    have hcont : Continuous fun z : ℂ => z * a := by fun_prop
    have hmap : Tendsto (fun z : ℂ => z * a) (𝓝[≠] c) (𝓝[≠] (c * a)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(hcont.tendsto c).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_iff.mpr <|
          Eventually.of_forall fun z hz => (mul_left_inj' ha).not.mpr hz⟩
    exact hmap.eventually heq

end HasSameSingularPartAt

/-- `HasSameSingularPartAt` depends only on punctured neighborhoods of `c`. -/
theorem hasSameSingularPartAt_congr {f₁ f₂ g₁ g₂ : ℂ → F} {c : ℂ}
    (hf : f₁ =ᶠ[𝓝[≠] c] f₂) (hg : g₁ =ᶠ[𝓝[≠] c] g₂) :
    HasSameSingularPartAt f₁ g₁ c ↔ HasSameSingularPartAt f₂ g₂ c :=
  ⟨fun h => h.congr hf hg, fun h => h.congr hf.symm hg.symm⟩

/-- `f` has the same singular part as `0` at `c` if and only if `f` has a removable singularity at
`c` (agrees on `𝓝[≠] c` with a function analytic at `c`). -/
@[simp]
theorem hasSameSingularPartAt_zero_right {f : ℂ → F} {c : ℂ} :
    HasSameSingularPartAt f 0 c ↔ ∃ h : ℂ → F, AnalyticAt ℂ h c ∧ f =ᶠ[𝓝[≠] c] h := by
  simp [HasSameSingularPartAt]

/-- Subtracting `g` reduces `HasSameSingularPartAt f g c` to `HasSameSingularPartAt (f - g) 0 c`. -/
theorem hasSameSingularPartAt_sub_zero_iff {f g : ℂ → F} {c : ℂ} :
    HasSameSingularPartAt (f - g) 0 c ↔ HasSameSingularPartAt f g c := by
  simp [HasSameSingularPartAt]

/-- Any function analytic at `c` has zero singular part at `c`. -/
theorem _root_.AnalyticAt.hasSameSingularPartAt_zero {f : ℂ → F} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    HasSameSingularPartAt f 0 c :=
  ⟨f, hf, by simp⟩

/-- Adding a function analytic at `c` does not change the singular part at `c`. -/
theorem _root_.AnalyticAt.hasSameSingularPartAt_add_right_iff {f g h : ℂ → F} {c : ℂ}
    (hh : AnalyticAt ℂ h c) :
    HasSameSingularPartAt (f + h) g c ↔ HasSameSingularPartAt f g c := by
  refine ⟨fun hfg => ?_, fun hfg => ?_⟩
  · simpa only [add_sub_cancel_right, sub_zero] using hfg.sub hh.hasSameSingularPartAt_zero
  · simpa only [add_zero] using hfg.add hh.hasSameSingularPartAt_zero

/-- Translation invariance of `HasSameSingularPartAt`. -/
theorem hasSameSingularPartAt_comp_add_const_iff {f g : ℂ → F} {c d : ℂ} :
    HasSameSingularPartAt (fun z => f (z + d)) (fun z => g (z + d)) c ↔
      HasSameSingularPartAt f g (c + d) :=
  ⟨fun h => by
    have h' : HasSameSingularPartAt (fun z => f (z + d)) (fun z => g (z + d)) ((c + d) + -d) := by
      rwa [add_neg_cancel_right]
    simpa only [neg_add_cancel_right] using h'.comp_add_const,
    fun h => h.comp_add_const⟩

/-- Nonzero scaling invariance of `HasSameSingularPartAt`. -/
theorem hasSameSingularPartAt_comp_mul_const_iff {f g : ℂ → F} {a c : ℂ} (ha : a ≠ 0) :
    HasSameSingularPartAt (fun z => f (z * a)) (fun z => g (z * a)) c ↔
      HasSameSingularPartAt f g (c * a) :=
  ⟨fun h => by
    have h' : HasSameSingularPartAt (fun z => f (z * a)) (fun z => g (z * a)) ((c * a) * a⁻¹) := by
      rwa [mul_inv_cancel_right₀ ha]
    simpa only [inv_mul_cancel_right₀ ha] using h'.comp_mul_const,
    fun h => h.comp_mul_const⟩

/-! ### Laurent-series and meromorphic-germ characterizations -/

namespace HasLaurentSeriesOnAnnulus

/-- For complete `F`, any function with a convergent Laurent series on `Metric.eball c R \ {c}` has
the same singular part at `c` as its negative Laurent sum `laurentNegPart a c`. -/
theorem hasSameSingularPartAt_laurentNegPart [CompleteSpace F]
    {f : ℂ → F} {a : ℤ → F} {c : ℂ} {R : ℝ≥0∞} (h : HasLaurentSeriesOnAnnulus f a c 0 R) :
    HasSameSingularPartAt f (laurentNegPart a c) c := by
  refine ⟨laurentPosPart a c, h.analyticOnNhd_laurentPosPart c (mem_eball_self h.outerRadius_pos),
    ?_⟩
  have hmem : eball c R \ closedBall c 0 ∈ 𝓝[≠] c := by
    rw [closedBall_zero]
    exact sdiff_mem_nhdsWithin_compl (isOpen_eball.mem_nhds (mem_eball_self h.outerRadius_pos)) _
  filter_upwards [hmem] with w hw
  exact sub_eq_of_eq_add (h.eq_laurentPosPart_add_laurentNegPart hw)

/-- Two functions admitting convergent Laurent series on punctured disks around `c` have the same
singular part at `c` if and only if all of their negative-degree Laurent coefficients agree. -/
theorem hasSameSingularPartAt_iff {f g : ℂ → F} {a b : ℤ → F} {c : ℂ} {R₁ R₂ : ℝ≥0∞}
    (hf : HasLaurentSeriesOnAnnulus f a c 0 R₁) (hg : HasLaurentSeriesOnAnnulus g b c 0 R₂) :
    HasSameSingularPartAt f g c ↔ ∀ k : ℕ, a (-((k : ℤ) + 1)) = b (-((k : ℤ) + 1)) := by
  let R : ℝ≥0∞ := min R₁ R₂
  have hR : ENNReal.ofReal 0 < R := by
    simpa [R] using lt_min hf.outerRadius_pos hg.outerRadius_pos
  have hsub : HasLaurentSeriesOnAnnulus (f - g) (a - b) c 0 R :=
    (hf.mono le_rfl (min_le_left _ _) hR).sub (hg.mono le_rfl (min_le_right _ _) hR)
  let L : F →L[ℂ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have hc : HasLaurentSeriesOnAnnulus (L ∘ (f - g)) (L ∘ (a - b)) c 0 R :=
    hsub.comp_continuousLinearMap L
  refine ⟨fun ⟨h, hh, heq⟩ k => ?_, fun hab => ?_⟩
  · have hLh : AnalyticAt ℂ (L ∘ h) c := (L.analyticAt (h c)).comp hh
    have hzero := hc.coeff_neg_add_one_eq_zero_of_analyticAt hLh (heq.fun_comp L) k
    exact sub_eq_zero.mp (UniformSpace.Completion.toComplₗᵢ.injective
      (hzero.trans (map_zero L).symm))
  · have hc_fp := hc.hasFPowerSeriesOnBall_update_of_neg_eq_zero fun k => by
      rw [Function.comp_apply, Pi.sub_apply, hab k, sub_self, map_zero]
    have hfp : HasFPowerSeriesOnBall (Function.update (f - g) c ((a - b) 0))
        (laurentPosPowerSeries (a - b)) c R :=
      ⟨hsub.le_radius_laurentPosPowerSeries, hsub.outerRadius_pos, fun {y} hy => by
        have hp := hc_fp.hasSum hy
        have hupd : Function.update (L ∘ (f - g)) c ((L ∘ (a - b)) 0) (c + y) =
            L (Function.update (f - g) c ((a - b) 0) (c + y)) := by
          rcases eq_or_ne y 0 with rfl | hy0
          · simp
          · have hcy : c + y ≠ c := by simpa using hy0
            rw [Function.update_of_ne hcy, Function.update_of_ne hcy, Function.comp_apply]
        rw [hupd] at hp
        exact (hasSum_iff_hasSum_compl _ _).mp
          (hp.congr_fun fun n => by simp [L, laurentPosPowerSeries_def])⟩
    exact ⟨Function.update (f - g) c ((a - b) 0), hfp.analyticAt,
      (Function.update_eventuallyEq_nhdsNE (f - g) c c ((a - b) 0)).symm⟩

end HasLaurentSeriesOnAnnulus

namespace meromorphicGerms

/-- For any representative `f` of `φ : meromorphicGerms ℂ c` and any polynomial `P : ℂ[X]`,
`principalPart φ = P` if and only if `P.coeff 0 = 0` and `f` has the same singular part at `c` as
`z ↦ P.eval (z - c)⁻¹`. -/
theorem principalPart_eq_iff_hasSameSingularPartAt {c : ℂ} {φ : meromorphicGerms ℂ c}
    {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) {P : ℂ[X]} :
    principalPart φ = P ↔
      P.coeff 0 = 0 ∧ HasSameSingularPartAt f (fun z => P.eval (z - c)⁻¹) c := by
  rw [principalPart_eq_iff, AddSubgroupClass.coe_sub, hφ, Polynomial.coe_evalInvSub,
    ← Germ.coe_sub]
  simp_rw [Germ.coe_eq, HasSameSingularPartAt]

/-- Any representative `f` of `φ : meromorphicGerms ℂ c` has the same singular part at `c` as
`z ↦ (principalPart φ).eval (z - c)⁻¹`. -/
theorem hasSameSingularPartAt_eval_inv_sub_principalPart {c : ℂ} {φ : meromorphicGerms ℂ c}
    {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) :
    HasSameSingularPartAt f (fun z => (principalPart φ).eval (z - c)⁻¹) c :=
  ((principalPart_eq_iff_hasSameSingularPartAt hφ).mp rfl).2

/-- Two meromorphic germs at `c` have equal `principalPart` if and only if their representatives
have the same singular part at `c`. -/
theorem principalPart_eq_principalPart_iff {c : ℂ} {φ ψ : meromorphicGerms ℂ c}
    {f g : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) (hψ : (ψ : Germ (𝓝[≠] c) ℂ) = g) :
    principalPart φ = principalPart ψ ↔ HasSameSingularPartAt f g c := by
  rw [principalPart_eq_iff_hasSameSingularPartAt hφ]
  refine ⟨fun ⟨_, hfp⟩ => hfp.trans (hasSameSingularPartAt_eval_inv_sub_principalPart hψ).symm,
    fun hfg => ⟨coeff_zero_principalPart ψ,
      hfg.trans (hasSameSingularPartAt_eval_inv_sub_principalPart hψ)⟩⟩

end meromorphicGerms

/-! ### Global uniqueness and affine structure of the solution space -/

/-- **Global uniqueness modulo analytic functions.** Let `Ω, E : Set ℂ` be arbitrary sets (with no
openness, inclusion, discreteness, or completeness assumptions). If `f₁, f₂ : ℂ → F` are
complex-analytic on `Ω \ E` and have the same singular part at every point of `Ω ∩ E`, then there
exists `h : ℂ → F` complex-analytic on `Ω` that agrees with `f₁ - f₂` on `Ω \ E`. -/
theorem exists_analyticOnNhd_eqOn_sub_of_hasSameSingularPartAt
    {Ω E : Set ℂ} {f₁ f₂ : ℂ → F}
    (hf₁ : AnalyticOnNhd ℂ f₁ (Ω \ E)) (hf₂ : AnalyticOnNhd ℂ f₂ (Ω \ E))
    (hsing : ∀ a ∈ Ω ∩ E, HasSameSingularPartAt f₁ f₂ a) :
    ∃ h : ℂ → F, AnalyticOnNhd ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) := by
  classical
  have hloc : ∀ x : Ω, ∃ (g : ℂ → F) (R : ℝ≥0∞), 0 < R ∧
      AnalyticAt ℂ g x ∧ ContinuousOn g (eball (x : ℂ) R) ∧
      ((x : ℂ) ∉ E → g x = (f₁ - f₂) x) ∧
      ∀ z ∈ eball (x : ℂ) R \ {(x : ℂ)}, (f₁ - f₂) z = g z := fun ⟨x, hxΩ⟩ => by
    by_cases hxE : x ∈ E
    · obtain ⟨g, ⟨p, R₁, hp⟩, heq⟩ := hsing x ⟨hxΩ, hxE⟩
      obtain ⟨ε, hε, hεeq⟩ := EMetric.mem_nhdsWithin_iff.1 heq
      exact ⟨g, min R₁ ε, lt_min hp.r_pos hε, hp.analyticAt,
        hp.continuousOn.mono (eball_subset_eball (min_le_left _ _)),
        fun hnot => False.elim (hnot hxE),
        fun z hz => hεeq ⟨eball_subset_eball (min_le_right _ _) hz.1, hz.2⟩⟩
    · obtain ⟨p, R₁, hp⟩ := (hf₁ x ⟨hxΩ, hxE⟩).sub (hf₂ x ⟨hxΩ, hxE⟩)
      exact ⟨f₁ - f₂, R₁, hp.r_pos, hp.analyticAt, hp.continuousOn, fun _ => rfl,
        fun _ _ => rfl⟩
  choose g R hR_pos hg_an hg_cont hg_val hg_eq using hloc
  have hcompat : ∀ (x y : Ω) {w : ℂ}, w ∈ eball (x : ℂ) (R x) → w ∈ eball (y : ℂ) (R y) →
      g x w = g y w := fun x y {w} hwx hwy => by
    have hmem : (eball (x : ℂ) (R x) ∩ eball (y : ℂ) (R y)) \ {(x : ℂ), (y : ℂ)} ∈ 𝓝[≠] w :=
      nhdsNE_of_nhdsNE_sdiff_finite
        (nhdsWithin_le_nhds ((isOpen_eball.inter isOpen_eball).mem_nhds ⟨hwx, hwy⟩))
        ({(x : ℂ), (y : ℂ)} : Set ℂ).toFinite
    have hev : g x =ᶠ[𝓝[≠] w] g y := by
      filter_upwards [hmem] with z ⟨⟨hzx, hzy⟩, hne⟩
      have hzx' : z ≠ (x : ℂ) := fun h => hne (Or.inl h)
      have hzy' : z ≠ (y : ℂ) := fun h => hne (Or.inr h)
      exact (hg_eq x z ⟨hzx, hzx'⟩).symm.trans (hg_eq y z ⟨hzy, hzy'⟩)
    exact tendsto_nhds_unique
      (((hg_cont x).continuousAt (isOpen_eball.mem_nhds hwx)).tendsto.mono_left nhdsWithin_le_nhds)
      ((((hg_cont y).continuousAt (isOpen_eball.mem_nhds hwy)).tendsto.mono_left
        nhdsWithin_le_nhds).congr' hev.symm)
  let h : ℂ → F := fun z => if hz : ∃ x : Ω, z ∈ eball (x : ℂ) (R x) then
    g (Classical.choose hz) z else 0
  have hh_eq : ∀ (x : Ω), EqOn h (g x) (eball (x : ℂ) (R x)) := fun x z hzx => by
    have hex : ∃ y : Ω, z ∈ eball (y : ℂ) (R y) := ⟨x, hzx⟩
    dsimp only [h]
    rw [dite_eq_left hex]
    exact hcompat (Classical.choose hex) x (Classical.choose_spec hex) hzx
  refine ⟨h, fun x hxΩ => ?_, fun x hx => ?_⟩
  · exact (hg_an ⟨x, hxΩ⟩).congr
      ((hh_eq ⟨x, hxΩ⟩).eventuallyEq_of_mem
        (isOpen_eball.mem_nhds (mem_eball_self (hR_pos ⟨x, hxΩ⟩)))).symm
  · rw [hh_eq ⟨x, hx.1⟩ (mem_eball_self (hR_pos ⟨x, hx.1⟩)), hg_val ⟨x, hx.1⟩ hx.2]

/-- **Affine characterization of the Mittag-Leffler solution space on an open set.** Let `Ω ⊆ ℂ` be
open and `Eᶜ ∈ codiscreteWithin Ω`. Given one solution `f₀ : ℂ → F` analytic on `Ω \ E` with
`HasSameSingularPartAt f₀ (P a) a` at each `a : E` lying in `Ω`, an arbitrary `f : ℂ → F` solves
the same singular-part problem if and only if `f` agrees on `Ω \ E` with `f₀ + h` for some
`h : ℂ → F` complex-analytic on `Ω`. -/
theorem analyticOnNhd_and_forall_hasSameSingularPartAt_iff
    {Ω E : Set ℂ} {P : E → ℂ → F} {f₀ f : ℂ → F} (hΩ : IsOpen Ω)
    (hE : Eᶜ ∈ codiscreteWithin Ω) (hf₀ : AnalyticOnNhd ℂ f₀ (Ω \ E))
    (hsing₀ : ∀ a : E, (a : ℂ) ∈ Ω → HasSameSingularPartAt f₀ (P a) a) :
    AnalyticOnNhd ℂ f (Ω \ E) ∧
        (∀ a : E, (a : ℂ) ∈ Ω → HasSameSingularPartAt f (P a) a) ↔
      (∃ h : ℂ → F, AnalyticOnNhd ℂ h Ω ∧ EqOn f (f₀ + h) (Ω \ E)) := by
  have hnhdsNE : ∀ x ∈ Ω, Ω \ E ∈ 𝓝[≠] x := fun x hx =>
    Filter.mem_of_superset (Filter.inter_mem (nhdsWithin_le_nhds (hΩ.mem_nhds hx))
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hE x hx))
      fun y ⟨hyΩ, hyE⟩ => ⟨hyΩ, hyE.resolve_right (not_not.mpr hyΩ)⟩
  have hopen_sdiff : IsOpen (Ω \ E) := isOpen_iff_mem_nhds.mpr fun x hx => by
    simpa only [insert_eq_of_mem hx] using insert_mem_nhds_iff.mpr (hnhdsNE x hx.1)
  refine ⟨fun ⟨hf, hsing⟩ => ?_, fun ⟨h, hh, heq⟩ => ?_⟩
  · obtain ⟨h, hh, hsub⟩ := exists_analyticOnNhd_eqOn_sub_of_hasSameSingularPartAt hf hf₀
      fun a ⟨haΩ, haE⟩ => (hsing ⟨a, haE⟩ haΩ).trans (hsing₀ ⟨a, haE⟩ haΩ).symm
    exact ⟨h, hh, fun z hz => eq_add_of_sub_eq' (hsub hz)⟩
  · refine ⟨fun z hz => ((hf₀ z hz).add (hh z hz.1)).congr
      (heq.eventuallyEq_of_mem (hopen_sdiff.mem_nhds hz)).symm, fun a haΩ => ?_⟩
    have hfeq : f =ᶠ[𝓝[≠] (a : ℂ)] f₀ + h := heq.eventuallyEq_of_mem (hnhdsNE a haΩ)
    exact ((hh a haΩ).hasSameSingularPartAt_add_right_iff.mpr (hsing₀ a haΩ)).congr hfeq.symm
      EventuallyEq.rfl

/-! ### Runge approximation of negative Laurent parts and shell construction -/

/-- Given a compact-interior exhaustion `⋃ n, K n = Ω` with `K n ⊆ interior (K (n + 1))` and shell
finsets `S k = {a : E | (a : ℂ) ∈ L (k + 1) \ L k}` for `L 0 = ∅`, `L (n + 1) = K n`, if `f` agrees
on each `interior (K m)` with `∑ a ∈ (Finset.range (m + 1)).biUnion S, s a` up to a function
analytic on `interior (K m)`, where each `s a` is analytic away from `a`, then `f` is analytic on
`Ω \ E` and has the same singular part as `s a₀` at every `a₀ : E`. -/
private theorem analyticOnNhd_and_hasSameSingularPartAt_of_local_sum
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) {K : ℕ → Set ℂ} (hKint : ∀ n, K n ⊆ interior (K (n + 1)))
    (hKunion : ⋃ n, K n = Ω) {L : ℕ → Set ℂ} (hL0 : L 0 = ∅) (hLK : ∀ n, L (n + 1) = K n)
    {S : ℕ → Finset E} (hS_mem : ∀ {k : ℕ} {a : E}, a ∈ S k ↔ (a : ℂ) ∈ L (k + 1) \ L k)
    {s : E → ℂ → F} (hs_an : ∀ a : E, AnalyticOnNhd ℂ (s a) {(a : ℂ)}ᶜ) {f : ℂ → F}
    (hloc : ∀ m : ℕ, ∃ H : ℂ → F, AnalyticOnNhd ℂ H (interior (K m)) ∧
      ∀ z ∈ interior (K m), f z = (∑ a ∈ (Finset.range (m + 1)).biUnion S, s a z) + H z) :
    AnalyticOnNhd ℂ f (Ω \ E) ∧ ∀ a₀ : E, HasSameSingularPartAt f (s a₀) a₀ := by
  classical
  refine ⟨fun z₀ ⟨hz₀Ω, hz₀E⟩ => ?_, fun a₀ => ?_⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.mp (hKunion ▸ hz₀Ω)
    have hz₀U : z₀ ∈ interior (K (n + 1)) := hKint n hn
    obtain ⟨H, hH_an, hH_eq⟩ := hloc (n + 1)
    have hsum_an : AnalyticAt ℂ (fun z => (∑ a ∈ (Finset.range (n + 2)).biUnion S, s a z) + H z)
        z₀ := (Finset.analyticAt_fun_sum _ fun a _ => hs_an a z₀ fun h => hz₀E (h ▸ a.2)).add
          (hH_an z₀ hz₀U)
    exact hsum_an.congr (Filter.eventuallyEq_of_mem (isOpen_interior.mem_nhds hz₀U)
      fun z hz => (hH_eq z hz).symm)
  · obtain ⟨n, hn⟩ := mem_iUnion.mp (hKunion ▸ hEΩ a₀.2)
    have ha₀U : (a₀ : ℂ) ∈ interior (K (n + 1)) := hKint n hn
    obtain ⟨H, hH_an, hH_eq⟩ := hloc (n + 1)
    let B : Finset E := (Finset.range (n + 2)).biUnion S
    have ha₀L : (a₀ : ℂ) ∈ L (n + 2) := hLK (n + 1) ▸ interior_subset ha₀U
    let p : ℕ → Prop := fun k => (a₀ : ℂ) ∈ L (k + 1)
    have hp : ∃ k, p k := ⟨n + 1, ha₀L⟩
    have ha₀B : a₀ ∈ B := by
      refine Finset.mem_biUnion.mpr ⟨Nat.find hp,
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.find_min' hp ha₀L)),
        hS_mem.mpr ⟨Nat.find_spec hp, ?_⟩⟩
      cases hfind : Nat.find hp with
      | zero => simp [hL0]
      | succ j => exact Nat.find_min hp (by omega)
    have hrem_an : AnalyticAt ℂ (fun z => (∑ a ∈ B.erase a₀, s a z) + H z) a₀ :=
      (Finset.analyticAt_fun_sum _ fun a ha => hs_an a a₀
        (Subtype.val_injective.ne (Finset.ne_of_mem_erase ha)).symm).add (hH_an a₀ ha₀U)
    refine ⟨_, hrem_an, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (isOpen_interior.mem_nhds ha₀U)] with z hz
    simp only [Pi.sub_apply]
    rw [hH_eq z hz, ← Finset.add_sum_erase _ _ ha₀B]
    abel

section CompleteSpace

variable [CompleteSpace F]

/-- Every function complex-differentiable on a punctured neighborhood of `c` admits a convergent
Laurent series on a punctured disk around `c`. -/
private theorem exists_hasLaurentSeriesOnAnnulus_zero
    {P : ℂ → F} {c : ℂ} (hP : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ P z) :
    ∃ (b : ℤ → F) (R : ℝ≥0∞), HasLaurentSeriesOnAnnulus P b c 0 R := by
  obtain ⟨R, hR, hdiff⟩ := EMetric.mem_nhdsWithin_iff.mp hP
  obtain ⟨ρ, -, hρ0, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.1 hR
  have hd : DifferentiableOn ℂ P (eball c R \ closedBall c 0) :=
    fun z ⟨hzR, hz0⟩ => (hdiff ⟨hzR, by simpa using hz0⟩).differentiableWithinAt
  exact ⟨circleLaurentCoeff P c ρ, R,
    hd.hasLaurentSeriesOnAnnulus le_rfl (ENNReal.ofReal_pos.mp hρ0) hρR⟩

/-- On a compact set `K ⊆ Ω` that is filled in an open set `Ω ⊆ ℂ` and avoids `c`, the negative
Laurent part `laurentNegPart a c` of any convergent punctured-disk Laurent series is uniformly
approximable by functions complex-differentiable on `Ω`. -/
private theorem exists_differentiableOn_norm_laurentNegPart_sub_lt
    {Ω K : Set ℂ} {f₀ : ℂ → F} {a : ℤ → F} {c : ℂ} {R : ℝ≥0∞}
    (hL : HasLaurentSeriesOnAnnulus f₀ a c 0 R) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω) (hc : c ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖laurentNegPart a c z - g z‖ < ε := by
  obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl c hc
  have hK_compl : K ⊆ (ball c r')ᶜ := fun z hz hzb => hball hzb hz
  have htu := Metric.tendstoUniformlyOn_iff.mp (hL.tendstoUniformlyOn_laurentNegPart hr')
    (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := htu.exists
  let φ : ℂ → F := fun w => ∑ k ∈ Finset.range N, w ^ (k + 1) • a (-((k : ℤ) + 1))
  have hφ_cont : Continuous φ := by fun_prop
  obtain ⟨δ₁, hδ₁, hφ_uc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) (r'⁻¹ + 1)).uniformContinuousOn_of_continuous
      hφ_cont.continuousOn) (ε / 2) (half_pos hε)
  obtain ⟨q, hq, hq_lt⟩ := hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ hc
    (lt_min hδ₁ zero_lt_one)
  refine ⟨fun z => φ (q z), DifferentiableOn.fun_sum fun k _ => (hq.pow (k + 1)).smul_const _,
    fun z hz => ?_⟩
  have hr'z : r' ≤ ‖z - c‖ := by
    simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hK_compl hz
  have hinv_le : ‖(z - c)⁻¹‖ ≤ r'⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hr' hr'z
  have hinv_mem : (z - c)⁻¹ ∈ closedBall (0 : ℂ) (r'⁻¹ + 1) :=
    mem_closedBall_zero_iff.mpr (by linarith)
  have hq_mem : q z ∈ closedBall (0 : ℂ) (r'⁻¹ + 1) := by
    rw [mem_closedBall_zero_iff]
    have hlt1 : ‖q z - (z - c)⁻¹‖ < 1 := by
      rw [norm_sub_rev]
      exact (hq_lt z hz).trans_le (min_le_right _ _)
    linarith [norm_sub_norm_le (q z) (z - c)⁻¹]
  have hφ_eq : φ (z - c)⁻¹ =
      ∑ k ∈ Finset.range N, (z - c) ^ (-((k : ℤ) + 1)) • a (-((k : ℤ) + 1)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.negSucc_eq, zpow_negSucc, inv_pow]
  have h₁ : ‖laurentNegPart a c z - φ (z - c)⁻¹‖ < ε / 2 := by
    rw [hφ_eq, ← dist_eq_norm]
    exact hN z (hK_compl hz)
  have h₂ : ‖φ (z - c)⁻¹ - φ (q z)‖ < ε / 2 := by
    have hd : dist (z - c)⁻¹ (q z) < δ₁ := by
      rw [dist_eq_norm]
      exact (hq_lt z hz).trans_le (min_le_left _ _)
    simpa only [dist_eq_norm, norm_sub_rev] using hφ_uc (z - c)⁻¹ hinv_mem (q z) hq_mem hd
  linarith [norm_sub_le_norm_sub_add_norm_sub (laurentNegPart a c z) (φ (z - c)⁻¹) (φ (q z))]

/-- Uniform Runge approximation on a filled compact set `K ⊆ Ω` for a finite sum of negative
Laurent parts whose poles all lie outside `K`. -/
private theorem exists_differentiableOn_norm_sum_laurentNegPart_sub_lt
    {Ω K E : Set ℂ} {P : E → ℂ → F} {coeff : E → ℤ → F} {R : E → ℝ≥0∞}
    (hL : ∀ a : E, HasLaurentSeriesOnAnnulus (P a) (coeff a) a 0 (R a))
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hfill : IsFilledIn K Ω)
    (S : Finset E) (hSK : ∀ a ∈ S, (a : ℂ) ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → F, DifferentiableOn ℂ G Ω ∧
      ∀ z ∈ K, ‖(∑ a ∈ S, laurentNegPart (coeff a) a z) - G z‖ < ε := by
  have hε' : 0 < ε / ((S.card : ℝ) + 1) := div_pos hε (by positivity)
  have hex : ∀ a : S, ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖laurentNegPart (coeff a) a z - g z‖ < ε / ((S.card : ℝ) + 1) := fun ⟨a, haS⟩ =>
    exists_differentiableOn_norm_laurentNegPart_sub_lt (hL a) hΩ hK hKΩ hfill (hSK a haS) hε'
  choose g hg_diff hg_lt using hex
  refine ⟨fun z => ∑ a ∈ S.attach, g a z,
    DifferentiableOn.fun_sum fun a _ => hg_diff a, fun z hz => ?_⟩
  rw [← S.sum_attach (fun a => laurentNegPart (coeff a) a z), ← Finset.sum_sub_distrib]
  have hle : ‖∑ a ∈ S.attach, (laurentNegPart (coeff a) (a : E) z - g a z)‖ ≤
      ∑ a ∈ S.attach, (ε / ((S.card : ℝ) + 1)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (hg_lt a z hz).le)
  rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul] at hle
  have hlt : (S.card : ℝ) * (ε / ((S.card : ℝ) + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith
  exact hle.trans_lt hlt

/-- Local decomposition of the Mittag-Leffler series `∑' k, ((∑ a ∈ S k, s a) - g k)` on an open
subset `U ⊆ L N ∩ Ω` into the finite sum over `(Finset.range N).biUnion S` plus a remainder
analytic on `U`. -/
private theorem exists_analyticOnNhd_eq_biUnion_sum_add
    {Ω E : Set ℂ} {L : ℕ → Set ℂ} {S : ℕ → Finset E} {s : E → ℂ → F} {g : ℕ → ℂ → F}
    (hL_mono : Monotone L) (hS_disj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (S i) (S j))
    (hS_avoid : ∀ k, ∀ a ∈ S k, (a : ℂ) ∉ L k)
    (hs_an : ∀ a : E, AnalyticOnNhd ℂ (s a) {(a : ℂ)}ᶜ)
    (hg_diff : ∀ k, DifferentiableOn ℂ (g k) Ω)
    (hg_lt : ∀ k, ∀ z ∈ L k, ‖(∑ a ∈ S k, s a z) - g k z‖ < (1 / 2 : ℝ) ^ k)
    (N : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUL : U ⊆ L N) (hUΩ : U ⊆ Ω) :
    ∃ H : ℂ → F, AnalyticOnNhd ℂ H U ∧
      ∀ z ∈ U, (∑' k : ℕ, ((∑ a ∈ S k, s a z) - g k z)) =
        (∑ a ∈ (Finset.range N).biUnion S, s a z) + H z := by
  let term : ℕ → ℂ → F := fun k z => (∑ a ∈ S k, s a z) - g k z
  have hsub : ∀ j : ℕ, U ⊆ L (j + N) := fun j => hUL.trans (hL_mono (Nat.le_add_left N j))
  have hsumm : Summable fun j : ℕ => (1 / 2 : ℝ) ^ (j + N) :=
    (summable_nat_add_iff N).2 summable_geometric_two
  have htail_diff : DifferentiableOn ℂ (fun z => ∑' j : ℕ, term (j + N) z) U := by
    refine (tendstoUniformlyOn_tsum_nat hsumm fun j z hz =>
      (hg_lt (j + N) z (hsub j hz)).le).differentiableOn
      (Eventually.of_forall fun M => DifferentiableOn.fun_sum fun j _ => ?_) hU
    refine (DifferentiableOn.fun_sum fun a ha => ?_).sub ((hg_diff (j + N)).mono hUΩ)
    exact ((hs_an a).mono fun z hz hza =>
      hS_avoid (j + N) a ha (hza ▸ hsub j hz)).differentiableOn
  have hH_diff : DifferentiableOn ℂ
      (fun z => (∑' j : ℕ, term (j + N) z) - ∑ k ∈ Finset.range N, g k z) U :=
    htail_diff.sub (DifferentiableOn.fun_sum fun k _ => (hg_diff k).mono hUΩ)
  refine ⟨fun z => (∑' j : ℕ, term (j + N) z) - ∑ k ∈ Finset.range N, g k z,
    fun z hz => hH_diff.analyticAt (hU.mem_nhds hz), fun z hz => ?_⟩
  have hs : Summable fun k : ℕ => term k z := (summable_nat_add_iff N).1 <|
    .of_norm_bounded hsumm fun j => (hg_lt (j + N) z (hsub j hz)).le
  rw [← hs.sum_add_tsum_nat_add N]
  have hsum_eq : ∑ k ∈ Finset.range N, term k z =
      (∑ a ∈ (Finset.range N).biUnion S, s a z) - ∑ k ∈ Finset.range N, g k z := by
    simp only [term, Finset.sum_sub_distrib]
    rw [Finset.sum_biUnion fun i _ j _ hij => hS_disj hij]
  rw [hsum_eq, sub_add_eq_add_sub, add_sub_assoc]

/-- Open-domain case of `exists_holomorphic_prescribed_isolated_singularities`, constructed via a
filled compact exhaustion and Runge-corrected Laurent negative-part shell sums. -/
private theorem exists_holomorphic_prescribed_isolated_singularities_of_isOpen
    {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] (a : ℂ), DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, AnalyticOnNhd ℂ f (Ω \ E) ∧ ∀ a : E, HasSameSingularPartAt f (P a) a := by
  classical
  choose coeff R hL using fun a : E => exists_hasLaurentSeriesOnAnnulus_zero (hP a)
  let s : E → ℂ → F := fun a => laurentNegPart (coeff a) a
  have hs_an : ∀ a : E, AnalyticOnNhd ℂ (s a) {(a : ℂ)}ᶜ := fun a => by
    simpa only [closedBall_zero] using (hL a).analyticOnNhd_laurentNegPart
  obtain ⟨K, hKcpt, hKint, hKunion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  let L : ℕ → Set ℂ := fun k => Nat.casesOn k ∅ K
  have hL_mono : Monotone L := monotone_nat_of_le_succ fun k => by
    rcases k with _ | m
    · exact empty_subset _
    · exact (hKint m).trans interior_subset
  have hL_sub : ∀ k, L k ⊆ Ω := fun k => by
    rcases k with _ | m
    · exact empty_subset _
    · exact hKunion ▸ subset_iUnion K m
  have hshell_fin : ∀ k, {a : E | (a : ℂ) ∈ L (k + 1) \ L k}.Finite := fun k =>
    (((hKcpt k).finite_sdiff_of_mem_codiscreteWithin
      (Filter.codiscreteWithin_mono (hL_sub (k + 1)) hE)).preimage
      Subtype.val_injective.injOn).subset fun a ha => ⟨ha.1, not_not.mpr a.2⟩
  let S : ℕ → Finset E := fun k => (hshell_fin k).toFinset
  have hS_mem : ∀ {k : ℕ} {a : E}, a ∈ S k ↔ (a : ℂ) ∈ L (k + 1) \ L k := by simp [S]
  have hS_disj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (S i) (S j) := fun i j hij =>
    Finset.disjoint_left.mpr fun a hai haj => hij.lt_or_gt.elim
      (fun hlt => (hS_mem.mp haj).2 (hL_mono (Nat.succ_le_of_lt hlt) (hS_mem.mp hai).1))
      (fun hgt => (hS_mem.mp hai).2 (hL_mono (Nat.succ_le_of_lt hgt) (hS_mem.mp haj).1))
  have happrox : ∀ k : ℕ, ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ L k, ‖(∑ a ∈ S k, s a z) - g z‖ < (1 / 2 : ℝ) ^ k := fun k => by
    rcases k with _ | m
    · exact ⟨0, differentiableOn_const 0, fun _ hz => False.elim hz⟩
    · exact exists_differentiableOn_norm_sum_laurentNegPart_sub_lt hL hΩ (hKcpt m)
        (hL_sub (m + 1)) (hKfill m) (S (m + 1)) (fun a ha => (hS_mem.mp ha).2) (by positivity)
  choose g hg_diff hg_lt using happrox
  let f : ℂ → F := fun z => ∑' k : ℕ, ((∑ a ∈ S k, s a z) - g k z)
  obtain ⟨hf_an, hf_s⟩ := analyticOnNhd_and_hasSameSingularPartAt_of_local_sum hEΩ hKint hKunion
    rfl (fun _ => rfl) hS_mem hs_an (f := f) fun m =>
      exists_analyticOnNhd_eq_biUnion_sum_add hL_mono hS_disj (fun k a ha => (hS_mem.mp ha).2)
        hs_an hg_diff hg_lt (m + 1) isOpen_interior interior_subset
        (interior_subset.trans (hL_sub (m + 1)))
  exact ⟨f, hf_an, fun a₀ => (hf_s a₀).trans (hL a₀).hasSameSingularPartAt_laurentNegPart.symm⟩

/-- **Global realization of prescribed isolated singularities.** Let `F` be a complex Banach space,
`Ω ⊆ ℂ` an arbitrary subset, and `E ⊆ Ω` a subset with no accumulation points in `Ω`
(`Eᶜ ∈ Filter.codiscreteWithin Ω`). Suppose each `a : E` is assigned a local model `P a : ℂ → F`
that is complex-differentiable on a punctured neighborhood of `a` (allowing poles as well as
essential singularities; no vanishing orders are prescribed). Then there exists `f : ℂ → F`
complex-analytic on `Ω \ E` such that `HasSameSingularPartAt f (P a) a` for every `a : E`. -/
theorem exists_holomorphic_prescribed_isolated_singularities
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] (a : ℂ), DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, AnalyticOnNhd ℂ f (Ω \ E) ∧ ∀ a : E, HasSameSingularPartAt f (P a) a := by
  have hΩ_sub : Ω ⊆ (derivedSet E)ᶜ := fun x hxΩ hx_acc =>
    (mem_codiscreteWithin_accPt.mp hE x hxΩ) <| by
      rwa [sdiff_compl, inter_eq_self_of_subset_right hEΩ]
  have hEΩ' : E ⊆ (derivedSet E)ᶜ := hEΩ.trans hΩ_sub
  have hE' : Eᶜ ∈ codiscreteWithin (derivedSet E)ᶜ :=
    mem_codiscreteWithin_accPt.mpr fun x hx hacc => hx <| by
      rwa [sdiff_compl, inter_eq_self_of_subset_right hEΩ'] at hacc
  obtain ⟨f, hf_an, hf_sing⟩ :=
    exists_holomorphic_prescribed_isolated_singularities_of_isOpen
      (isClosed_derivedSet E).isOpen_compl hEΩ' hE' P hP
  exact ⟨f, hf_an.mono (sdiff_subset_sdiff hΩ_sub Subset.rfl), hf_sing⟩

/-- **Mittag-Leffler theorem for Banach-valued meromorphic germs.** Let `F` be a complex Banach
space, `Ω ⊆ ℂ` an arbitrary subset, and `E ⊆ Ω` a subset with `Eᶜ ∈ Filter.codiscreteWithin Ω`.
If each `a : E` carries a local model `P a : ℂ → F` meromorphic at `a`, there exists `f : ℂ → F`
complex-analytic on `Ω \ E` and meromorphic on `Ω` such that `HasSameSingularPartAt f (P a) a` for
every `a : E`. -/
theorem exists_meromorphic_prescribed_principal_parts
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, MeromorphicAt (P a) a) :
    ∃ f : ℂ → F, AnalyticOnNhd ℂ f (Ω \ E) ∧ MeromorphicOn f Ω ∧
      ∀ a : E, HasSameSingularPartAt f (P a) a := by
  obtain ⟨f, hf_an, hf_sing⟩ := exists_holomorphic_prescribed_isolated_singularities hEΩ hE P
    fun a => (hP a).eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  refine ⟨f, hf_an, fun z hzΩ => ?_, hf_sing⟩
  by_cases hzE : z ∈ E
  · exact (hf_sing ⟨z, hzE⟩).meromorphicAt_iff.mpr (hP ⟨z, hzE⟩)
  · exact (hf_an z ⟨hzΩ, hzE⟩).meromorphicAt

end CompleteSpace

/-- **Mittag-Leffler theorem for polynomial principal parts in `(z - a)⁻¹`.** Given `E ⊆ Ω ⊆ ℂ`
with `Eᶜ ∈ Filter.codiscreteWithin Ω` and arbitrary polynomials `P : E → ℂ[X]`, there exists
`f : ℂ → ℂ` complex-analytic on `Ω \ E` and meromorphic on `Ω` with
`HasSameSingularPartAt f (fun z => (P a).eval (z - a)⁻¹) a` at every `a : E`. -/
theorem exists_meromorphic_hasSameSingularPartAt_eval_inv_sub
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω) (P : E → ℂ[X]) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Ω \ E) ∧ MeromorphicOn f Ω ∧
      ∀ a : E, HasSameSingularPartAt f (fun z => (P a).eval (z - a)⁻¹) a :=
  exists_meromorphic_prescribed_principal_parts hEΩ hE
    (fun a z => (P a).eval (z - a)⁻¹) fun a => (P a).meromorphicAt_eval_inv_sub a

/-- **Mittag-Leffler theorem for `TauCeti.meromorphicGerms.principalPart`.** Given `E ⊆ Ω ⊆ ℂ`
with `Eᶜ ∈ Filter.codiscreteWithin Ω` and polynomials `P : E → ℂ[X]` without constant term
(`(P a).coeff 0 = 0`), there exists `f : ℂ → ℂ` complex-analytic on `Ω \ E` and meromorphic on `Ω`
whose meromorphic germ at every `a : E` has `principalPart` equal to `P a`. -/
theorem exists_meromorphic_principalPart_eq
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ[X]) (hP : ∀ a : E, (P a).coeff 0 = 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Ω \ E) ∧
      ∃ hf : MeromorphicOn f Ω,
        ∀ a : E, meromorphicGerms.principalPart
          ⟨(f : Germ (𝓝[≠] (a : ℂ)) ℂ),
            coe_mem_meromorphicGerms.2 (hf a (hEΩ a.2))⟩ = P a := by
  obtain ⟨f, hf_an, hf_mero, hf_sing⟩ :=
    exists_meromorphic_hasSameSingularPartAt_eval_inv_sub hEΩ hE P
  exact ⟨f, hf_an, hf_mero, fun a =>
    (meromorphicGerms.principalPart_eq_iff_hasSameSingularPartAt rfl).mpr ⟨hP a, hf_sing a⟩⟩

end TauCeti
