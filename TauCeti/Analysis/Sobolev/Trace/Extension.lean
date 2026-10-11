/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection
public import TauCeti.Analysis.Sobolev.Trace.ZeroBoundary
public import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Extension by reflection from a half-space, and the half-space trace

Every Sobolev function on the half-space `H = normalHalfSpace a = {x | a < x.fst}` of the
Euclidean product `ℝ × E` extends to a Sobolev function on the whole space: its even reflection
across the boundary hyperplane `{a} × E`. This file packages that extension as a bounded linear
operator

`TauCeti.W1p.extendByReflectionL a : W^{1,p}(H) →L[ℝ] W^{1,p}(ℝ × E)`,

for every `1 ≤ p ≤ ∞`, with norm at most `2`, and a right inverse of restriction to `H`. Its value
is `u` on `H` and `u ∘ ρ` on the other side, where `ρ (t, y) = (2a - t, y)`; its gradient is
`∇u` on `H` and the reflected gradient `R (∇u ∘ ρ)` on the other side, `R (s, z) = (-s, z)`. The
analytic content, that this pair is a weak derivative across the hyperplane, is
`TauCeti.HasWeakFDerivOn.add_comp_normalReflection`.

Composing with the whole-space trace `TauCeti.W1p.hyperplaneTrace` gives the trace of an
arbitrary `H¹` function on the half-space, `TauCeti.W1p.halfSpaceTrace`. By the one-sided trace
estimate `TauCeti.W1p.norm_hyperplaneTrace_le_norm_restrictL` it has norm at most one, and it
agrees with the trace of every whole-space extension.

Unlike extension by zero (`TauCeti.W1p0.extendByZeroL`), which needs the zero boundary condition
of `W^{1,p}_0`, the reflection extends every Sobolev function on the half-space. The half-space
is the local model for extension and trace on domains with Lipschitz boundary.

## Main declarations

* `TauCeti.W1p.extendByReflectionL`: the extension operator, with
  `TauCeti.W1p.restrictL_extendByReflectionL`, `TauCeti.W1p.norm_extendByReflectionL_le`,
  `TauCeti.W1p.opNorm_extendByReflectionL_le`, and its value and gradient
  `TauCeti.W1p.value_extendByReflectionL_ae` and `TauCeti.W1p.gradient_extendByReflectionL_ae`.
* `TauCeti.W1p.halfSpaceTrace`: the `L²` trace on `{a} × E` of an `H¹` function on the
  half-space, with `TauCeti.W1p.norm_halfSpaceTrace_le`, `TauCeti.W1p.opNorm_halfSpaceTrace_le`,
  and `TauCeti.W1p.halfSpaceTrace_restrictL`. On `H¹₀` of the half-space it agrees with the
  zero-boundary trace (`TauCeti.W1p.halfSpaceTrace_coe_w1p0`) and so vanishes
  (`TauCeti.W1p.halfSpaceTrace_eq_zero_of_w1p0`).

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 9.2;
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.4 and §5.5.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter

namespace TauCeti

/-! ### The extension operator -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ENNReal} [Fact (1 ≤ p)]

/-- The pointwise action of the reflection on value-gradient jets: the value is kept and the
gradient is flipped. -/
private def jetFlip : Sobolev1Jet (WithLp 2 (ℝ × E)) ≃ₗᵢ[ℝ] Sobolev1Jet (WithLp 2 (ℝ × E)) :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ) (normalLinearReflection E)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem jetFlip_fst (J : Sobolev1Jet (WithLp 2 (ℝ × E))) :
    (jetFlip J).fst = J.fst := by
  simp [jetFlip]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem jetFlip_snd (J : Sobolev1Jet (WithLp 2 (ℝ × E))) :
    (jetFlip J).snd = normalLinearReflection E J.snd := by
  simp [jetFlip]

private theorem restrict_top :
    (volume : Measure (WithLp 2 (ℝ × E))).restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) :
      Set (WithLp 2 (ℝ × E))) = volume := by
  simp

private theorem ae_restrict_top :
    ae ((volume : Measure (WithLp 2 (ℝ × E))).restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) :
      Set (WithLp 2 (ℝ × E)))) = ae volume := by
  rw [restrict_top]

private theorem measurePreserving_normalReflection_top (a : ℝ) :
    MeasurePreserving (normalReflection E a)
      ((volume : Measure (WithLp 2 (ℝ × E))).restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) :
        Set (WithLp 2 (ℝ × E))))
      ((volume : Measure (WithLp 2 (ℝ × E))).restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) :
        Set (WithLp 2 (ℝ × E)))) := by
  rw [restrict_top]
  exact measurePreserving_normalReflection a

/-- Precomposition with the reflection, followed by flipping the gradient, on whole-space jets. -/
private def reflectJetL (a : ℝ) :
    Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ]
      Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
  ((jetFlip (E := E)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL p _).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (normalReflection E a)
      (measurePreserving_normalReflection_top a)).toContinuousLinearMap

private theorem coeFn_reflectJetL (a : ℝ)
    (K : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    reflectJetL a K =ᵐ[volume] fun x => jetFlip (K (normalReflection E a x)) := by
  have h := ((jetFlip (E := E)).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
    (p := p) (Lp.compMeasurePreservingₗᵢ ℝ (normalReflection E a)
      (measurePreserving_normalReflection_top a) K)).trans
    ((Lp.coeFn_compMeasurePreserving K (measurePreserving_normalReflection_top a)).fun_comp
      jetFlip)
  rw [ae_restrict_top] at h
  exact h

private theorem norm_reflectJetL_le (a : ℝ)
    (K : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    ‖reflectJetL a K‖ ≤ ‖K‖ := by
  refine (ContinuousLinearMap.norm_compLp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (jetFlip (E := E)).toLinearIsometry.norm_toContinuousLinearMap_le).trans ?_
  exact (LinearIsometry.norm_map _ K).le

/-- Extension by zero followed by adding the reflected copy, on jets. -/
private def extendJetL (a : ℝ) :
    Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p →L[ℝ]
      Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
  (ContinuousLinearMap.id ℝ _ + reflectJetL a).comp
    (Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤)).toContinuousLinearMap

private theorem extendJetL_apply (a : ℝ)
    (J : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    extendJetL a J =
      Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J +
        reflectJetL a (Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J) :=
  rfl

private theorem coeFn_extendJetL (a : ℝ)
    (J : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    extendJetL a J =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator J x +
        jetFlip ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator J
          (normalReflection E a x)) := by
  have hZ := Sobolev1JetLp.coeFn_extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J
  rw [ae_restrict_top] at hZ
  have hadd := Lp.coeFn_add
    (Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J)
    (reflectJetL a (Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J))
  rw [ae_restrict_top] at hadd
  have hρZ := (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae_eq_comp hZ
  filter_upwards [hadd, hZ, coeFn_reflectJetL a
    (Sobolev1JetLp.extendByZeroₗᵢ (le_top : normalHalfSpace (E := E) a ≤ ⊤) J), hρZ]
    with x h1 h2 h3 h4
  simp only [extendJetL, ContinuousLinearMap.comp_apply, FunLike.coe_add, Pi.add_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [h1, Pi.add_apply, h2, h3]
  simp only [Function.comp_apply] at h4
  rw [h4]

/-- The extended jet of a Sobolev function on the half-space is a Sobolev jet on the whole
space. -/
private theorem extendJetL_mem_w1pSubmodule (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    extendJetL a
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) ∈
      w1pSubmodule (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p := by
  let J := (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p)
  let H := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have hH : MeasurableSet H := (normalHalfSpace (E := E) a).isOpen.measurableSet
  let w := H.indicator fun x => (J x).fst
  let G := H.indicator fun x => (J x).snd
  have hwl : LocallyIntegrable w :=
    ((memLp_indicator_iff_restrict hH.nullMeasurableSet).2
      ((Lp.memLp (W1p.value u)).ae_eq (W1p.value_apply_ae u))).locallyIntegrable Fact.out
  have hGl : LocallyIntegrable G :=
    ((memLp_indicator_iff_restrict hH.nullMeasurableSet).2
      ((Lp.memLp (W1p.gradient u)).ae_eq (W1p.gradient_apply_ae u))).locallyIntegrable Fact.out
  have hw0 (x : WithLp 2 (ℝ × E)) (hx : x ∉ normalHalfSpace (E := E) a) : w x = 0 :=
    indicator_of_notMem hx _
  have hG0 (x : WithLp 2 (ℝ × E)) (hx : x ∉ normalHalfSpace (E := E) a) : G x = 0 :=
    indicator_of_notMem hx _
  have hweak : HasWeakFDerivOn volume (normalHalfSpace a) w fun x => innerSL ℝ (G x) := by
    refine ((W1p.hasWeakFDerivOn u).congr_ae (Filter.EventuallyEq.trans (W1p.value_apply_ae u)
      (indicator_ae_eq_restrict hH.nullMeasurableSet).symm)).congr_ae_deriv ?_
    filter_upwards [Filter.EventuallyEq.trans (W1p.gradient_apply_ae u)
      (indicator_ae_eq_restrict hH.nullMeasurableSet).symm] with x hx
    rw [hx]
  have hcore := hweak.add_comp_normalReflection hwl hGl hw0 hG0
  have hJ := coeFn_extendJetL a J
  rw [← ae_restrict_top] at hJ
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  refine (hcore.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [Sobolev1JetLp.value_apply_ae (extendJetL a J), hJ] with x h1 h2
    rw [h1, h2, WithLp.add_fst, jetFlip_fst, WithLp.fst_indicator, WithLp.fst_indicator]
  · filter_upwards [Sobolev1JetLp.gradient_apply_ae (extendJetL a J), hJ] with x h1 h2
    refine ContinuousLinearMap.ext fun v => ?_
    rw [Sobolev1JetLp.candidateWeakFDeriv_apply, innerSL_apply_apply, real_inner_comm, h1, h2,
      WithLp.add_snd, jetFlip_snd, WithLp.snd_indicator, WithLp.snd_indicator]

/-- **Extension by reflection** from the half-space `{x | a < x.fst}` to the whole space: a
Sobolev function `u` on the half-space is sent to its even reflection, equal to `u` on the
half-space and to `u ∘ ρ` on the other side, `ρ` being the reflection in `{a} × E`. It is a
right inverse of restriction (`TauCeti.W1p.restrictL_extendByReflectionL`) with norm at most `2`
(`TauCeti.W1p.norm_extendByReflectionL_le`). -/
def W1p.extendByReflectionL (a : ℝ) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p →L[ℝ]
      W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
  ContinuousLinearMap.codRestrict
    ((extendJetL (p := p) a).comp (w1pSubmodule (volume : Measure (WithLp 2 (ℝ × E)))
      (normalHalfSpace a) p).toSubmodule.subtypeL)
    (w1pSubmodule (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p).toSubmodule
    (fun u => by exact extendJetL_mem_w1pSubmodule a u)

/-- The ambient jet of the reflection extension is the extended jet. -/
private theorem coe_extendByReflectionL (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    ((W1p.extendByReflectionL a u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
      Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) =
      extendJetL a (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E)))
        (normalHalfSpace a) p) :=
  rfl

/-- Functions that agree almost everywhere on the half-space have extensions by zero that agree
almost everywhere, both directly and after precomposition with the reflection. -/
private theorem ae_indicator_eq_and_comp_normalReflection (a : ℝ) {F : Type*} [Zero F]
    {f g : WithLp 2 (ℝ × E) → F}
    (h : f =ᵐ[volume.restrict (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))] g) :
    ∀ᵐ x ∂volume,
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator g x ∧
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
            (normalReflection E a x) =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator g
            (normalReflection E a x) := by
  have hI := (ae_eq_restrict_iff_indicator_ae_eq
    (normalHalfSpace (E := E) a).isOpen.measurableSet).1 h
  filter_upwards [hI,
    (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae_eq_comp hI]
    with x h1 h2
  exact ⟨h1, h2⟩

/-- The value of the reflection extension is `u` on the half-space and `u ∘ ρ` on the other side,
almost everywhere. -/
theorem W1p.value_extendByReflectionL_ae (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    W1p.value (W1p.extendByReflectionL a u) =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (W1p.value u) x +
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (W1p.value u)
          (normalReflection E a x) := by
  have h1 := W1p.value_apply_ae (W1p.extendByReflectionL a u)
  rw [ae_restrict_top] at h1
  filter_upwards [h1, coeFn_extendJetL a (u : Sobolev1JetLp (volume : Measure
    (WithLp 2 (ℝ × E))) (normalHalfSpace a) p),
    ae_indicator_eq_and_comp_normalReflection a (W1p.value_apply_ae u)]
    with x h1 h2 ⟨h3, h3ρ⟩
  rw [h1, coe_extendByReflectionL, h2, WithLp.add_fst, jetFlip_fst, WithLp.fst_indicator,
    WithLp.fst_indicator, ← h3, ← h3ρ]

/-- The weak gradient of the reflection extension is `∇u` on the half-space and the reflected
gradient `R (∇u ∘ ρ)` on the other side, almost everywhere, where `R` negates the normal
component. -/
theorem W1p.gradient_extendByReflectionL_ae (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    W1p.gradient (W1p.extendByReflectionL a u) =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (W1p.gradient u) x +
        normalLinearReflection E ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
          (W1p.gradient u) (normalReflection E a x)) := by
  have h1 := W1p.gradient_apply_ae (W1p.extendByReflectionL a u)
  rw [ae_restrict_top] at h1
  filter_upwards [h1, coeFn_extendJetL a (u : Sobolev1JetLp (volume : Measure
    (WithLp 2 (ℝ × E))) (normalHalfSpace a) p),
    ae_indicator_eq_and_comp_normalReflection a (W1p.gradient_apply_ae u)]
    with x h1 h2 ⟨h3, h3ρ⟩
  rw [h1, coe_extendByReflectionL, h2, WithLp.add_snd, jetFlip_snd, WithLp.snd_indicator,
    WithLp.snd_indicator, ← h3, ← h3ρ]

/-- Restricting the reflection extension back to the half-space recovers the original function. -/
theorem W1p.restrictL_extendByReflectionL (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
      (W1p.extendByReflectionL a u) = u := by
  have hH : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_restrictL_ae le_top (W1p.extendByReflectionL a u),
    ae_restrict_of_ae (W1p.value_extendByReflectionL_ae a u), ae_restrict_mem hH] with x h1 h2 hx
  have hρx : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
    rw [SetLike.mem_coe, normalReflection_mem_normalHalfSpace_iff, not_lt]
    exact ((mem_normalHalfSpace a x).1 hx).le
  rw [h1, h2, indicator_of_mem hx, indicator_of_notMem hρx, add_zero]

/-- The reflection extension at most doubles the Sobolev norm. -/
theorem W1p.norm_extendByReflectionL_le (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    ‖W1p.extendByReflectionL a u‖ ≤ 2 * ‖u‖ := by
  let J := (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p)
  let Z := Sobolev1JetLp.extendByZeroₗᵢ (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p)
    (le_top : normalHalfSpace (E := E) a ≤ ⊤)
  have h1 : ‖W1p.extendByReflectionL a u‖ = ‖extendJetL a J‖ := by
    rw [← Submodule.norm_coe, coe_extendByReflectionL]
  have h2 : ‖extendJetL a J‖ ≤ ‖Z J‖ + ‖Z J‖ := by
    rw [extendJetL_apply]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_reflectJetL_le a (Z J)))
  have h3 : ‖Z J‖ = ‖u‖ := by
    rw [LinearIsometry.norm_map, Submodule.norm_coe]
  linarith

/-- The reflection extension has operator norm at most `2`. -/
theorem W1p.opNorm_extendByReflectionL_le (a : ℝ) :
    ‖W1p.extendByReflectionL (E := E) (p := p) a‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two (W1p.norm_extendByReflectionL_le a)

end Operator

/-! ### The trace of a half-space Sobolev function -/

section Trace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The `L²` trace on the boundary hyperplane `{a} × E` of an `H¹` function on the half-space
`{x | a < x.fst}`: the whole-space hyperplane trace of its reflection extension. By
`TauCeti.W1p.halfSpaceTrace_restrictL` it agrees with the trace of any whole-space extension. -/
def W1p.halfSpaceTrace (a : ℝ) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2 →L[ℝ]
      Lp ℝ 2 (volume : Measure E) :=
  (W1p.hyperplaneTrace a).comp (W1p.extendByReflectionL a)

/-- The half-space trace has operator norm at most one: the trace is controlled by the Sobolev
norm on the half-space alone. -/
theorem W1p.norm_halfSpaceTrace_le (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    ‖W1p.halfSpaceTrace a u‖ ≤ ‖u‖ :=
  (W1p.norm_hyperplaneTrace_le_norm_restrictL a (W1p.extendByReflectionL a u)).trans_eq
    (by rw [W1p.restrictL_extendByReflectionL])

/-- The half-space trace has operator norm at most one. -/
theorem W1p.opNorm_halfSpaceTrace_le (a : ℝ) : ‖W1p.halfSpaceTrace (E := E) a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using W1p.norm_halfSpaceTrace_le a u

/-- The half-space trace is the hyperplane trace of the reflection extension. -/
theorem W1p.halfSpaceTrace_apply (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    W1p.halfSpaceTrace a u = W1p.hyperplaneTrace a (W1p.extendByReflectionL a u) :=
  (rfl)

/-- The half-space trace of the restriction of a whole-space `H¹` function is its hyperplane
trace. With `TauCeti.W1p.hyperplaneTrace_ofTestFunction_apply_ae`, this identifies the trace of
the restriction of a test function with its classical boundary values. -/
theorem W1p.halfSpaceTrace_restrictL (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    W1p.halfSpaceTrace a (W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) u) =
      W1p.hyperplaneTrace a u := by
  have hle : normalHalfSpace (E := E) a ≤ ⊤ := le_top
  rw [W1p.halfSpaceTrace_apply]
  apply W1p.hyperplaneTrace_eq_of_value_ae_eq
  have h := (W1p.value_restrictL_ae hle
    (W1p.extendByReflectionL a (W1p.restrictL hle u))).symm
  rw [W1p.restrictL_extendByReflectionL] at h
  exact h.trans (W1p.value_restrictL_ae hle u)

/-- On `H¹₀` of the half-space, the half-space trace agrees with the zero-boundary trace
`TauCeti.W1p0.hyperplaneTrace`, defined through extension by zero. -/
theorem W1p.halfSpaceTrace_coe_w1p0 (a : ℝ)
    (u : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    W1p.halfSpaceTrace a (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) =
      W1p0.hyperplaneTrace (E := E) (Omega := normalHalfSpace a) a u := by
  refine (W1p.halfSpaceTrace_apply a _).trans ((W1p.hyperplaneTrace_eq_of_value_ae_eq a ?_).trans
    (W1p0.hyperplaneTrace_apply a u).symm)
  have h := (W1p.value_restrictL_ae (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
    (W1p.extendByReflectionL a
      (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2))).symm
  rw [W1p.restrictL_extendByReflectionL] at h
  refine h.trans ?_
  rw [W1p0.value_extendByZeroL]
  exact (coeFn_extendByZeroLpₗᵢ_restrict ℝ _ _ _).symm

/-- Functions in `H¹₀` of the half-space have zero half-space trace: the flat-model inclusion
`H¹₀(H) ⊆ ker(halfSpaceTrace)`. -/
theorem W1p.halfSpaceTrace_eq_zero_of_w1p0 (a : ℝ)
    (u : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    W1p.halfSpaceTrace a (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) =
      0 :=
  (W1p.halfSpaceTrace_coe_w1p0 a u).trans (W1p0.hyperplaneTrace_apply_eq_zero_of_forall_not_mem a
    (fun _ => (mem_normalHalfSpace a _).not.2 (lt_irrefl a)) u)

end Trace

end TauCeti
