/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable

/-!
# Quasiregular maps of Euclidean domains

Let `E` be a finite-dimensional real inner product space of dimension `n`, with Lebesgue measure
`volume`, and let `Ω ⊆ E` be open. A map `f : E → E` is **`K`-quasiregular on `Ω`**
(`TauCeti.IsQuasiregularOn K Ω f`) when `1 ≤ K`, `f` is continuous on `Ω`, and `f` has a weak
derivative `Du` on `Ω` (`TauCeti.HasWeakFDerivOn`) with `‖Du‖ⁿ` locally integrable on `Ω` and

`‖Du(x)‖ⁿ ≤ K det Du(x)` for almost every `x ∈ Ω`,

with the operator norm and Mathlib's `LinearMap.det`. The condition uses `det Du`, not
`|det Du|`: a quasiregular map preserves orientation almost everywhere.

## Main statements

* `TauCeti.IsQuasiregularOn.one_le`, `TauCeti.IsQuasiregularOn.continuousOn` and
  `TauCeti.IsQuasiregularOn.exists_hasWeakFDerivOn`: the parts of the definition.
* `TauCeti.IsQuasiregularOn.locallyIntegrableOn_norm_pow`,
  `TauCeti.IsQuasiregularOn.ae_norm_pow_le_mul_det` and `TauCeti.isQuasiregularOn_iff`: the
  condition does not depend on the choice of the weak derivative, since two weak derivatives agree
  almost everywhere (`TauCeti.HasWeakFDerivOn.ae_eq`).
* `TauCeti.IsQuasiregularOn.ae_det_nonneg`: a quasiregular map preserves orientation almost
  everywhere.
* `TauCeti.IsQuasiregularOn.weaken` and `TauCeti.IsQuasiregularOn.mono`: it is monotone in `K`
  and passes to open subsets.
* `TauCeti.isQuasiregularOn_iff_of_differentiableAt`: for `f` differentiable on `Ω` with locally
  integrable derivative, the weak derivative may be taken to be `fderiv ℝ f`.
* `TauCeti.not_isQuasiregularOn_of_eqOn_of_det_neg`: a map that agrees, on a nonempty open
  subset of `Ω`, with a linear map of negative determinant is not quasiregular on `Ω`.
* `TauCeti.not_isQuasiregularOn_of_eqOn_of_det_eq_zero`: a map that agrees, on a nonempty open
  subset of `Ω`, with a nonzero linear map of determinant zero is not quasiregular on `Ω`.

## Checks

* `TauCeti.isQuasiregularOn_id`: the identity is `1`-quasiregular on every open set.
* `TauCeti.not_isQuasiregularOn_fold`: the fold `x ↦ x + (|⟪u, x⟫| - ⟪u, x⟫) u` along a unit
  vector `u`, which is `(x₁, …, xₙ) ↦ (|x₁|, x₂, …, xₙ)` for `u = e₁`, is not `K`-quasiregular on
  any open set meeting `{⟪u, x⟫ < 0}`, for any `K`: there it is the reflection in `uᗮ`, whose
  determinant is `-1`. A definition with `|det Du|` would accept it with `K = 1`.

## References

* O. Martio, S. Rickman, J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969). Their analytic definition asks `f` to be ACLⁿ; here the Sobolev
  condition (a weak derivative with `‖Du‖ⁿ` locally integrable) takes its place.
* S. Rickman, *Quasiregular Mappings*, Ergebnisse der Mathematik und ihrer Grenzgebiete 26,
  Springer, 1993, Chapter I.
-/

public section

open MeasureTheory Module Set TopologicalSpace
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`K`-quasiregular maps of a Euclidean domain.** For a finite-dimensional real inner product
space `E` of dimension `n` with Lebesgue measure and `Ω ⊆ E` open, `f` is `K`-quasiregular on `Ω`
when `1 ≤ K`, `f` is continuous on `Ω`, and `f` has a weak derivative `Du` on `Ω` with `‖Du‖ⁿ`
locally integrable on `Ω` and `‖Du(x)‖ⁿ ≤ K · det Du(x)` for almost every `x ∈ Ω`, with the
operator norm. The weak derivative condition replaces the ACLⁿ condition of Martio, Rickman and
Väisälä. -/
def IsQuasiregularOn (K : ℝ) (Ω : Opens E) (f : E → E) : Prop :=
  1 ≤ K ∧ ContinuousOn f Ω ∧
    ∃ Du : E → E →L[ℝ] E, HasWeakFDerivOn volume Ω f Du ∧
      LocallyIntegrableOn (fun x ↦ ‖Du x‖ ^ finrank ℝ E) Ω volume ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set E),
        ‖Du x‖ ^ finrank ℝ E ≤ K * LinearMap.det (Du x : E →ₗ[ℝ] E)

variable {K K' : ℝ} {Ω Ω' : Opens E} {f : E → E}

/-- The constant of a `K`-quasiregular map satisfies `1 ≤ K`. -/
theorem IsQuasiregularOn.one_le (hf : IsQuasiregularOn K Ω f) : 1 ≤ K :=
  hf.1

/-- A quasiregular map is continuous on its domain. -/
theorem IsQuasiregularOn.continuousOn (hf : IsQuasiregularOn K Ω f) : ContinuousOn f Ω :=
  hf.2.1

/-- A quasiregular map has a weak derivative on its domain. -/
theorem IsQuasiregularOn.exists_hasWeakFDerivOn (hf : IsQuasiregularOn K Ω f) :
    ∃ Du : E → E →L[ℝ] E, HasWeakFDerivOn volume Ω f Du :=
  let ⟨Du, hDu, _⟩ := hf.2.2
  ⟨Du, hDu⟩

/-- For a quasiregular map, `‖Du‖ⁿ` is locally integrable for every weak derivative `Du`: two
weak derivatives agree almost everywhere on `Ω`. -/
theorem IsQuasiregularOn.locallyIntegrableOn_norm_pow (hf : IsQuasiregularOn K Ω f)
    {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du) :
    LocallyIntegrableOn (fun x ↦ ‖Du x‖ ^ finrank ℝ E) Ω volume := by
  obtain ⟨-, -, Du', hDu', hint, -⟩ := hf
  exact hint.congr ((hDu'.ae_eq hDu).mono fun x hx ↦ by simp only [hx])

/-- For a `K`-quasiregular map, `‖Du‖ⁿ ≤ K det Du` holds almost everywhere for every weak
derivative `Du`: two weak derivatives agree almost everywhere on `Ω`. -/
theorem IsQuasiregularOn.ae_norm_pow_le_mul_det (hf : IsQuasiregularOn K Ω f)
    {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du) :
    ∀ᵐ x ∂volume.restrict (Ω : Set E),
      ‖Du x‖ ^ finrank ℝ E ≤ K * LinearMap.det (Du x : E →ₗ[ℝ] E) := by
  obtain ⟨-, -, Du', hDu', -, hle⟩ := hf
  filter_upwards [hDu'.ae_eq hDu, hle] with x hx hxle
  rwa [← hx]

/-- **Quasiregularity through a given weak derivative.** If `Du` is a weak derivative of `f` on
`Ω`, then `f` is `K`-quasiregular on `Ω` exactly when `1 ≤ K`, `f` is continuous on `Ω`, `‖Du‖ⁿ` is
locally integrable on `Ω` and `‖Du‖ⁿ ≤ K det Du` almost everywhere on `Ω`. -/
theorem isQuasiregularOn_iff {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du) :
    IsQuasiregularOn K Ω f ↔ 1 ≤ K ∧ ContinuousOn f Ω ∧
      LocallyIntegrableOn (fun x ↦ ‖Du x‖ ^ finrank ℝ E) Ω volume ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set E),
        ‖Du x‖ ^ finrank ℝ E ≤ K * LinearMap.det (Du x : E →ₗ[ℝ] E) :=
  ⟨fun hf ↦ ⟨hf.one_le, hf.continuousOn, hf.locallyIntegrableOn_norm_pow hDu,
      hf.ae_norm_pow_le_mul_det hDu⟩,
    fun ⟨hK, hc, hint, hle⟩ ↦ ⟨hK, hc, Du, hDu, hint, hle⟩⟩

/-- **Quasiregular maps preserve orientation.** Every weak derivative `Du` of a quasiregular map
has `det Du ≥ 0` almost everywhere, since `0 ≤ ‖Du‖ⁿ ≤ K det Du` with `K > 0`. -/
theorem IsQuasiregularOn.ae_det_nonneg (hf : IsQuasiregularOn K Ω f)
    {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du) :
    ∀ᵐ x ∂volume.restrict (Ω : Set E), 0 ≤ LinearMap.det (Du x : E →ₗ[ℝ] E) := by
  filter_upwards [hf.ae_norm_pow_le_mul_det hDu] with x hx
  exact nonneg_of_mul_nonneg_right ((pow_nonneg (norm_nonneg _) _).trans hx)
    (zero_lt_one.trans_le hf.one_le)

/-- A `K`-quasiregular map is `K'`-quasiregular for every `K' ≥ K`: the determinant of the weak
derivative is almost everywhere nonnegative. -/
theorem IsQuasiregularOn.weaken (hf : IsQuasiregularOn K Ω f) (hKK' : K ≤ K') :
    IsQuasiregularOn K' Ω f := by
  obtain ⟨Du, hDu⟩ := hf.exists_hasWeakFDerivOn
  refine (isQuasiregularOn_iff hDu).2 ⟨hf.one_le.trans hKK', hf.continuousOn,
    hf.locallyIntegrableOn_norm_pow hDu, ?_⟩
  filter_upwards [hf.ae_norm_pow_le_mul_det hDu, hf.ae_det_nonneg hDu] with x hx hdet
  exact hx.trans (mul_le_mul_of_nonneg_right hKK' hdet)

/-- A map that is `K`-quasiregular on `Ω` is `K`-quasiregular on every open subset of `Ω`. -/
theorem IsQuasiregularOn.mono (hf : IsQuasiregularOn K Ω f) (hΩ : Ω' ≤ Ω) :
    IsQuasiregularOn K Ω' f := by
  obtain ⟨hK, hc, Du, hDu, hint, hle⟩ := hf
  exact ⟨hK, hc.mono hΩ, Du, hDu.mono hΩ, hint.mono_set hΩ,
    ae_restrict_of_ae_restrict_of_subset hΩ hle⟩

/-- **Quasiregularity of differentiable maps.** If `f` is differentiable at every point of `Ω`
and its derivative is locally integrable on `Ω`, then `f` is `K`-quasiregular on `Ω` exactly when
`1 ≤ K`, `‖Df‖ⁿ` is locally integrable on `Ω` and `‖Df(x)‖ⁿ ≤ K det Df(x)` for almost every
`x ∈ Ω`. -/
theorem isQuasiregularOn_iff_of_differentiableAt
    (hd : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ f x)
    (hDf : LocallyIntegrableOn (fderiv ℝ f) Ω volume) :
    IsQuasiregularOn K Ω f ↔ 1 ≤ K ∧
      LocallyIntegrableOn (fun x ↦ ‖fderiv ℝ f x‖ ^ finrank ℝ E) Ω volume ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set E),
        ‖fderiv ℝ f x‖ ^ finrank ℝ E ≤ K * LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E) := by
  rw [isQuasiregularOn_iff (hasWeakFDerivOn_of_differentiableOn hDf hd)]
  exact ⟨fun ⟨hK, _, hint, hle⟩ ↦ ⟨hK, hint, hle⟩, fun ⟨hK, hint, hle⟩ ↦
    ⟨hK, fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt, hint, hle⟩⟩

/-- **The identity is `1`-quasiregular** on every open set: its weak derivative is the constant
identity map, with `‖id‖ⁿ ≤ 1 = det id`. -/
theorem isQuasiregularOn_id (Ω : Opens E) : IsQuasiregularOn 1 Ω (id : E → E) := by
  have hD : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E :=
    funext fun _ ↦ fderiv_id
  refine (isQuasiregularOn_iff_of_differentiableAt (fun x _ ↦ differentiableAt_id) ?_).2
    ⟨le_rfl, ?_, .of_forall fun x ↦ ?_⟩
  · rw [hD]
    exact locallyIntegrableOn_const _
  · rw [hD]
    exact locallyIntegrableOn_const _
  · rw [hD, ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

/-- A map that agrees, on an open set `U`, with a continuous linear map `A` has the constant weak
derivative `A` on `U`. -/
private theorem hasWeakFDerivOn_const_of_eqOn {U : Opens E} {A : E →L[ℝ] E} (hfA : EqOn f A U) :
    HasWeakFDerivOn volume U f (fun _ ↦ A) :=
  hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
    (A.continuous.continuousOn.congr hfA) (locallyIntegrableOn_const A) fun _ hx ↦
      A.hasFDerivAt.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hx.1) hfA)

/-- A property that holds almost everywhere on a nonempty open set is satisfiable. -/
private theorem exists_of_ae_restrict_opens {U : Opens E} (hUne : (U : Set E).Nonempty)
    {p : E → Prop} (hp : ∀ᵐ x ∂volume.restrict (U : Set E), p x) : ∃ x, p x := by
  by_contra h
  push Not at h
  have hfalse : ∀ᵐ _ ∂volume.restrict (U : Set E), False := hp.mono h
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hfalse
  exact (U.isOpen.measure_pos volume hUne).ne' hfalse

/-- **Orientation reversal excludes quasiregularity.** If `f` agrees, on a nonempty open subset
`U` of `Ω`, with a continuous linear map `A` with `det A < 0`, then `f` is not `K`-quasiregular on
`Ω` for any `K`: on `U` the weak derivative is `A` almost everywhere, and `‖A‖ⁿ ≤ K det A < 0` is
impossible on a set of positive measure. -/
theorem not_isQuasiregularOn_of_eqOn_of_det_neg {U : Opens E} (hU : U ≤ Ω)
    (hUne : (U : Set E).Nonempty) {A : E →L[ℝ] E} (hA : LinearMap.det (A : E →ₗ[ℝ] E) < 0)
    (hfA : EqOn f A U) : ¬ IsQuasiregularOn K Ω f := by
  intro hf
  obtain ⟨Du, hDu⟩ := hf.exists_hasWeakFDerivOn
  obtain ⟨x, hx, hdet⟩ := exists_of_ae_restrict_opens hUne <|
    ((hDu.mono hU).ae_eq (hasWeakFDerivOn_const_of_eqOn hfA)).and
      (ae_restrict_of_ae_restrict_of_subset hU (hf.ae_det_nonneg hDu))
  rw [hx] at hdet
  exact hA.not_ge hdet

/-- **Degenerate linear maps exclude quasiregularity.** If `f` agrees, on a nonempty open subset
`U` of `Ω`, with a nonzero continuous linear map `A` with `det A = 0`, then `f` is not
`K`-quasiregular on `Ω` for any `K`: on `U` the weak derivative is `A` almost everywhere, and
`0 < ‖A‖ⁿ ≤ K det A = 0` is impossible on a set of positive measure. -/
theorem not_isQuasiregularOn_of_eqOn_of_det_eq_zero {U : Opens E} (hU : U ≤ Ω)
    (hUne : (U : Set E).Nonempty) {A : E →L[ℝ] E} (hA : A ≠ 0)
    (hdet : LinearMap.det (A : E →ₗ[ℝ] E) = 0) (hfA : EqOn f A U) :
    ¬ IsQuasiregularOn K Ω f := by
  intro hf
  obtain ⟨Du, hDu⟩ := hf.exists_hasWeakFDerivOn
  obtain ⟨x, hx, hle⟩ := exists_of_ae_restrict_opens hUne <|
    ((hDu.mono hU).ae_eq (hasWeakFDerivOn_const_of_eqOn hfA)).and
      (ae_restrict_of_ae_restrict_of_subset hU (hf.ae_norm_pow_le_mul_det hDu))
  rw [hx, hdet, mul_zero] at hle
  exact (pow_pos (norm_pos_iff.2 hA) _).not_ge hle

/-- **The fold is not quasiregular.** For a unit vector `u`, the fold
`x ↦ x + (|⟪u, x⟫| - ⟪u, x⟫) u`, which is `(x₁, …, xₙ) ↦ (|x₁|, x₂, …, xₙ)` for `u = e₁`, is not
`K`-quasiregular, for any `K`, on any open set `Ω` meeting the half-space `{⟪u, x⟫ < 0}`: there it
is the reflection in the hyperplane `uᗮ`, of determinant `-1`. -/
theorem not_isQuasiregularOn_fold {u : E} (hu : ‖u‖ = 1)
    (hΩ : ((Ω : Set E) ∩ {x | ⟪u, x⟫ < 0}).Nonempty) :
    ¬ IsQuasiregularOn K Ω (fun x ↦ x + (|⟪u, x⟫| - ⟪u, x⟫) • u) := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (hu ▸ one_ne_zero)
  refine not_isQuasiregularOn_of_eqOn_of_det_neg
    (U := Ω ⊓ ⟨{x | ⟪u, x⟫ < 0}, isOpen_lt (by fun_prop) continuous_const⟩) inf_le_left
    (by simpa only [Opens.coe_inf, Opens.coe_mk] using hΩ)
    (A := ((ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E)) ?_ fun x hx ↦ ?_
  · have hdet := (ℝ ∙ u)ᗮ.det_reflection
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hu0, pow_one] at hdet
    have hR : (((ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        (ℝ ∙ u)ᗮ.reflection.toLinearMap := LinearMap.ext fun x ↦ by simp
    rw [hR, hdet]
    norm_num
  · simp only [Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    have hx0 : ⟪u, x⟫ < 0 := hx.2
    simp [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
      abs_of_neg hx0, hu, sub_eq_add_neg, add_smul, two_smul]

end TauCeti
