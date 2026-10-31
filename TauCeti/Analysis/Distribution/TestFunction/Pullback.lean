/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity

/-!
# Pullback of test forms and pushforward of currents

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, and let `Φ : E → E'` be smooth
on `Ω` and *proper from `Ω` to `Ω'`*: the set `Ω ∩ Φ ⁻¹' K` is compact for every compact
`K ⊆ Ω'`. The pullback of a test `k`-form `ω` on `Ω'` is the test `k`-form on `Ω`
`(Φ^* ω) x = ω (Φ x) ∘ (DΦ x, …, DΦ x)` for `x ∈ Ω`, extended by zero off `Ω`. Nothing is
assumed about `Φ` off `Ω`, so `Φ` may be a chart transition or a smooth map defined only on `Ω`.

The pullback `TestFunction.pullbackCLM` is continuous for the LF topology of test functions. So
the pushforward of a current `T` on `Ω` (a continuous linear functional on test forms) is the
current `Φ_# T = T ∘ Φ^*` on `Ω'`. Pullback commutes with the exterior derivative, hence
pushforward commutes with the boundary `∂T = T ∘ d`. A bound `‖DΦ‖ ≤ L` on `Ω` gives
`M(Φ_# T) ≤ L ^ k M(T)`.

## Main declarations

* `TestFunction.pullbackCLM`: the pullback of test forms along a smooth map proper from `Ω` to
  `Ω'`, as a continuous linear map.
* `TestFunction.pullbackCLM_apply_of_mem`, `TestFunction.pullbackCLM_apply_of_notMem`: its values.
* `TestFunction.tsupport_pullbackCLM_subset`: `supp Φ^* ω ⊆ Ω ∩ Φ ⁻¹' supp ω`.
* `TestFunction.pullbackCLM_id`, `TestFunction.pullbackCLM_comp`: functoriality; the identity
  map pulls back by extension by zero.
* `TestFunction.extDerivCLM_pullbackCLM`: `d (Φ^* ω) = Φ^* (d ω)`.
* `ContinuousLinearMap.comp_pullbackCLM_comp_extDerivCLM`: `∂ (Φ_# T) = Φ_# (∂ T)`.
* `Distribution.mass_comp_pullbackCLM_le`: `M(Φ_# T) ≤ L ^ k M(T)` when `‖DΦ‖ ≤ L` on `Ω`.

## Implementation notes

Continuity is checked on each space of tests supported in a fixed compact `K ⊆ Ω'`, whose
pullbacks are supported in the compact set `Ω ∩ Φ ⁻¹' K`. There the derivatives of `Φ^* ω` are
bounded by those of `ω`, through the Leibniz bound `norm_iteratedFDerivWithin_clm_apply` and the
Faà di Bruno bound `norm_iteratedFDerivWithin_comp_le`. The pointwise naturality of the exterior
derivative is Mathlib's `extDeriv_pullback`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the pushforward of a current).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Set Filter TopologicalSpace ContinuousAlternatingMap
open scoped Distributions Topology Nat NNReal ENNReal BoundedContinuousFunction

namespace TestFunction

variable {E E' E'' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {Φ : E → E'} {k : ℕ}

section Pointwise

/-- The pointwise pullback of a `k`-form `ω` on `E'` along `Φ`, extended by zero off `Ω`. -/
private def pullbackFun (Ω : Opens E) (Φ : E → E') (ω : E' → E' [⋀^Fin k]→L[ℝ] F) :
    E → E [⋀^Fin k]→L[ℝ] F :=
  (Ω : Set E).indicator fun x ↦ compContinuousLinearMapCLM (fderiv ℝ Φ x) (ω (Φ x))

/-- On `Ω`, the pullback is given by the formula without extension by zero. -/
private theorem pullbackFun_eventuallyEq {ω : E' → E' [⋀^Fin k]→L[ℝ] F} {x : E} (hx : x ∈ Ω) :
    pullbackFun Ω Φ ω =ᶠ[𝓝 x] fun y ↦ compContinuousLinearMapCLM (fderiv ℝ Φ y) (ω (Φ y)) := by
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  exact indicator_of_mem hy _

private theorem pullbackFun_add (ω η : E' → E' [⋀^Fin k]→L[ℝ] F) :
    pullbackFun Ω Φ (ω + η) = pullbackFun Ω Φ ω + pullbackFun Ω Φ η := by
  ext x : 1
  by_cases hx : x ∈ Ω <;> simp [pullbackFun, hx, -compContinuousLinearMapCLM_apply]

private theorem pullbackFun_smul (c : ℝ) (ω : E' → E' [⋀^Fin k]→L[ℝ] F) :
    pullbackFun Ω Φ (c • ω) = c • pullbackFun Ω Φ ω := by
  ext x : 1
  by_cases hx : x ∈ Ω <;> simp [pullbackFun, hx, -compContinuousLinearMapCLM_apply]

private theorem support_pullbackFun_subset (ω : E' → E' [⋀^Fin k]→L[ℝ] F) :
    Function.support (pullbackFun Ω Φ ω) ⊆ Ω ∩ Φ ⁻¹' Function.support ω := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · refine ⟨hxΩ, fun h ↦ hx ?_⟩
    simp [pullbackFun, hxΩ, h, -compContinuousLinearMapCLM_apply]
  · exact absurd (indicator_of_notMem hxΩ _) hx

/-- The pointwise pullback of a smooth form is smooth, provided that its support near `Ω` lies in
a compact subset of `Ω`. -/
private theorem contDiff_pullbackFun (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    {ω : E' → E' [⋀^Fin k]→L[ℝ] F} (hω : ContDiff ℝ (⊤ : ℕ∞) ω) {C : Set E} (hC : IsCompact C)
    (hCΩ : C ⊆ Ω) (hsupp : (Ω : Set E) ∩ Φ ⁻¹' Function.support ω ⊆ C) :
    ContDiff ℝ (⊤ : ℕ∞) (pullbackFun Ω Φ ω) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ Ω
  · exact ((hΦ.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)).differentialForm_pullback
      hω.contDiffAt |>.congr_of_eventuallyEq (pullbackFun_eventuallyEq hx)
  · -- Off `Ω`, the point lies outside the closed set `C`, near which the pullback vanishes.
    refine (contDiffAt_const (c := 0)).congr_of_eventuallyEq ?_
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds fun h ↦ hx (hCΩ h)] with y hy
    exact Function.notMem_support.1 fun h ↦ hy (hsupp (support_pullbackFun_subset ω h))

/-- On a compact subset of `Ω`, the `i`-th derivative of a pullback is bounded by a constant
times a bound for the first `i` derivatives of the form. -/
private theorem exists_norm_iteratedFDeriv_pullbackFun_le (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    {C : Set E} (hC : IsCompact C) (hCΩ : C ⊆ Ω) (i : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ω : E' → E' [⋀^Fin k]→L[ℝ] F), ContDiff ℝ (⊤ : ℕ∞) ω → ∀ B : ℝ,
      (∀ j ≤ i, ∀ y, ‖iteratedFDeriv ℝ j ω y‖ ≤ B) →
      ∀ x ∈ C, ‖iteratedFDeriv ℝ i (pullbackFun Ω Φ ω) x‖ ≤ A * B := by
  have hM : ContDiffOn ℝ (⊤ : ℕ∞) (fun y ↦ (compContinuousLinearMapCLM (fderiv ℝ Φ y) :
      (E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)) Ω :=
    (contDiff_compContinuousLinearMapCLM _).comp_contDiffOn
      (hΦ.fderiv_of_isOpen Ω.isOpen (by simp))
  -- Bounds on `C` for the derivatives of `y ↦ (DΦ y)^*` and of `Φ`; the latter are made uniform
  -- in the order `l ≤ i`, as the Faà di Bruno bound requires.
  choose R₁ hR₁ using fun j ↦ hC.exists_bound_of_continuousOn
    ((hM.continuousOn_iteratedFDerivWithin (m := j) (by simp) Ω.isOpen.uniqueDiffOn).mono hCΩ)
  choose R₂ hR₂ using fun l ↦ hC.exists_bound_of_continuousOn
    ((hΦ.continuousOn_iteratedFDerivWithin (m := l) (by simp) Ω.isOpen.uniqueDiffOn).mono hCΩ)
  set D := 1 + ∑ l ∈ Finset.range (i + 1), |R₂ l|
  have hD1 : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  have hD {l : ℕ} (hl : l ≤ i) {x : E} (hx : x ∈ C) :
      ‖iteratedFDerivWithin ℝ l Φ Ω x‖ ≤ D :=
    (hR₂ l x hx).trans <| (le_abs_self _).trans <|
      (Finset.single_le_sum (f := fun l ↦ |R₂ l|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hl))).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * |R₁ j| * ((i - j)! * D ^ (i - j)),
    Finset.sum_nonneg fun j _ ↦ by positivity, fun ω hω B hB x hx ↦ ?_⟩
  have hxΩ : x ∈ Ω := hCΩ hx
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  rw [((pullbackFun_eventuallyEq hxΩ).iteratedFDeriv ℝ i).eq_of_nhds,
    ← iteratedFDerivWithin_of_isOpen i Ω.isOpen hxΩ, Finset.sum_mul]
  refine (norm_iteratedFDerivWithin_clm_apply hM (hω.comp_contDiffOn hΦ)
    Ω.isOpen.uniqueDiffOn hxΩ (by simp)).trans (Finset.sum_le_sum fun j hj ↦ ?_)
  have hj : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  -- Faà di Bruno: the derivatives of `ω ∘ Φ` are controlled by those of `ω` and of `Φ`.
  have hcomp : ‖iteratedFDerivWithin ℝ (i - j) (ω ∘ Φ) Ω x‖ ≤ (i - j)! * B * D ^ (i - j) :=
    norm_iteratedFDerivWithin_comp_le hω.contDiffOn hΦ (by simp) uniqueDiffOn_univ
      Ω.isOpen.uniqueDiffOn (mapsTo_univ _ _) hxΩ
      (fun l hl ↦ by rw [iteratedFDerivWithin_univ]; exact hB l (by omega) _)
      (fun l hl _ ↦ (hD (by omega) hx).trans (le_self_pow₀ hD1 (by omega)))
  calc (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j _ Ω x‖ *
        ‖iteratedFDerivWithin ℝ (i - j) (fun y ↦ ω (Φ y)) Ω x‖
      ≤ (i.choose j : ℝ) * |R₁ j| * ((i - j)! * B * D ^ (i - j)) := by
        gcongr
        exacts [(hR₁ j x hx).trans (le_abs_self _), hcomp]
    _ = (i.choose j : ℝ) * |R₁ j| * ((i - j)! * D ^ (i - j)) * B := by ring

end Pointwise

section SupportedIn

/-- The pullback of tests supported in a compact `K ⊆ Ω'`, which are supported in the compact
set `Ω ∩ Φ ⁻¹' K`. -/
private def pullbackSupportedInCLM (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    (hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K))
    (K : Compacts E') (hK : (K : Set E') ⊆ Ω') :
    𝓓_{K}(E', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ]
      𝓓_{⟨(Ω : Set E) ∩ Φ ⁻¹' K, hΦp K K.isCompact hK⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
  letI P : 𝓓_{K}(E', E' [⋀^Fin k]→L[ℝ] F) →ₗ[ℝ]
      𝓓_{⟨(Ω : Set E) ∩ Φ ⁻¹' K, hΦp K K.isCompact hK⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
    { toFun ω := ⟨pullbackFun Ω Φ ω,
        contDiff_pullbackFun hΦ ω.contDiff (hΦp K K.isCompact hK) inter_subset_left
          (inter_subset_inter_right _ (preimage_mono ω.support_subset)),
        fun x hx ↦ Function.notMem_support.1 fun h ↦ hx <| inter_subset_inter_right _
          (preimage_mono ω.support_subset) (support_pullbackFun_subset _ h)⟩
      map_add' ω η := ContDiffMapSupportedIn.ext fun x ↦ congrFun (pullbackFun_add ω η) x
      map_smul' c ω := ContDiffMapSupportedIn.ext fun x ↦ congrFun (pullbackFun_smul c ω) x }
  { toLinearMap := P
    cont := by
      -- As in `ContDiffMapSupportedIn.mkCLM`: bound each seminorm of the image by finitely many
      -- seminorms of the source.
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      obtain ⟨A, hA, h⟩ := exists_norm_iteratedFDeriv_pullbackFun_le (k := k) (F := F) hΦ
        (hΦp K K.isCompact hK) inter_subset_left i
      refine ⟨Finset.range (i + 1), A, fun ω ↦ ((P ω).seminorm_le_iff ℝ
        (mul_nonneg hA (apply_nonneg _ _)) i).2 fun _ x hx ↦
          h ω ω.contDiff _ (fun j hj y ↦ ?_) x hx⟩
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hj))) }

end SupportedIn

/-- The **pullback** of test `k`-forms along a map `Φ` that is smooth on `Ω` and proper from `Ω`
to `Ω'` (the set `Ω ∩ Φ ⁻¹' K` is compact for every compact `K ⊆ Ω'`), as a continuous linear
map. On `Ω` it is `(Φ^* ω) x = ω (Φ x) ∘ (DΦ x, …, DΦ x)`, see
`TestFunction.pullbackCLM_apply_of_mem`, and it vanishes off `Ω`. Precomposing a current on `Ω`
with it gives the pushforward current on `Ω'`. -/
def pullbackCLM (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    (hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)) :
    𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  letI T (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    haveI hC := hΦp _ ω.hasCompactSupport ω.tsupport_subset
    haveI hsupp : Function.support (pullbackFun Ω Φ ω) ⊆ (Ω : Set E) ∩ Φ ⁻¹' tsupport ω :=
      (support_pullbackFun_subset _).trans
        (inter_subset_inter_right _ (preimage_mono (subset_tsupport _)))
    ⟨pullbackFun Ω Φ ω,
      contDiff_pullbackFun hΦ ω.contDiff hC inter_subset_left
        (inter_subset_inter_right _ (preimage_mono (subset_tsupport _))),
      hC.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp hC.isClosed),
      (closure_minimal hsupp hC.isClosed).trans inter_subset_left⟩
  TestFunction.limitCLM ℝ T
    (fun K hK ↦ ofSupportedInCLM ℝ inter_subset_left ∘L pullbackSupportedInCLM hΦ hΦp K hK)
    (fun _ _ _ ↦ rfl)

variable {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
  {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}

/-- The pullback of a test form is the pointwise pullback, extended by zero off `Ω`. -/
theorem coe_pullbackCLM (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    ⇑(pullbackCLM Φ hΦ hΦp ω) =
      (Ω : Set E).indicator fun x ↦ (ω (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x) :=
  (rfl)

/-- On `Ω`, the pullback is `(Φ^* ω) x = ω (Φ x) ∘ (DΦ x, …, DΦ x)`. -/
@[simp]
theorem pullbackCLM_apply_of_mem (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) {x : E} (hx : x ∈ Ω) :
    pullbackCLM Φ hΦ hΦp ω x = (ω (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x) := by
  rw [coe_pullbackCLM, indicator_of_mem hx]

/-- Off `Ω`, the pullback vanishes. -/
@[simp]
theorem pullbackCLM_apply_of_notMem (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) {x : E} (hx : x ∉ Ω) :
    pullbackCLM Φ hΦ hΦp ω x = 0 := by
  rw [coe_pullbackCLM, indicator_of_notMem hx]

/-- The support of a pullback lies over the support of the form. -/
theorem tsupport_pullbackCLM_subset (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    tsupport (pullbackCLM Φ hΦ hΦp ω) ⊆ (Ω : Set E) ∩ Φ ⁻¹' tsupport ω :=
  closure_minimal ((support_pullbackFun_subset _).trans
      (inter_subset_inter_right _ (preimage_mono (subset_tsupport _))))
    (hΦp _ ω.hasCompactSupport ω.tsupport_subset).isClosed

/-- The pointwise norm of a pullback of a `k`-form is at most `‖ω (Φ x)‖ ‖DΦ x‖ ^ k`. -/
theorem norm_pullbackCLM_apply_le (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) (x : E) :
    ‖pullbackCLM Φ hΦ hΦp ω x‖ ≤ ‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k := by
  by_cases hx : x ∈ Ω
  · simpa [hx] using norm_compContinuousLinearMap_le (ω (Φ x)) (fderiv ℝ Φ x)
  · rw [pullbackCLM_apply_of_notMem ω hx, norm_zero]
    positivity

/-- Pulling back along the identity of `E` from `Ω' ⊆ Ω` is extension by zero. -/
theorem pullbackCLM_id {Ω' : Opens E} (h : Ω' ≤ Ω)
    (hp : ∀ K : Set E, IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ id ⁻¹' K)) :
    (pullbackCLM id contDiffOn_id hp : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) = monoCLM ℝ := by
  ext ω x : 2
  by_cases hx : x ∈ Ω
  · ext v
    simp [hx, h]
  · simp [hx, h, image_eq_zero_of_notMem_tsupport fun hx' ↦ hx (h (ω.tsupport_subset hx'))]

/-- **Functoriality of pullback**: `(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*` when `Φ` maps `Ω` into `Ω'`. -/
theorem pullbackCLM_comp {Ψ : E' → E''} (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω')
    (hΨp : ∀ K : Set E'', IsCompact K → K ⊆ Ω'' → IsCompact ((Ω' : Set E') ∩ Ψ ⁻¹' K))
    (hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω)
    (hΨΦp : ∀ K : Set E'', IsCompact K → K ⊆ Ω'' → IsCompact ((Ω : Set E) ∩ (Ψ ∘ Φ) ⁻¹' K))
    (hmaps : MapsTo Φ Ω Ω') :
    (pullbackCLM (Ψ ∘ Φ) hΨΦ hΨΦp : 𝓓(Ω'', E'' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM Φ hΦ hΦp ∘L pullbackCLM Ψ hΨ hΨp := by
  ext ω x : 2
  by_cases hx : x ∈ Ω
  · have hΦx : DifferentiableAt ℝ Φ x :=
      (hΦ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hΨx : DifferentiableAt ℝ Ψ (Φ x) :=
      (hΨ.contDiffAt (Ω'.isOpen.mem_nhds (hmaps hx))).differentiableAt (by simp)
    have hx' : Φ x ∈ Ω' := hmaps hx
    rw [ContinuousLinearMap.comp_apply, pullbackCLM_apply_of_mem _ hx,
      pullbackCLM_apply_of_mem _ hx, pullbackCLM_apply_of_mem _ hx', fderiv_comp x hΨx hΦx]
    ext v
    simp [Function.comp_def]
  · simp [hx]

/-- **Naturality of the exterior derivative**: `d (Φ^* ω) = Φ^* (d ω)`. -/
theorem extDerivCLM_pullbackCLM (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (pullbackCLM Φ hΦ hΦp ω) = pullbackCLM Φ hΦ hΦp (extDerivCLM ω) := by
  ext x : 1
  by_cases hx : x ∈ Ω
  · have heq : ⇑(pullbackCLM Φ hΦ hΦp ω) =ᶠ[𝓝 x]
        fun y ↦ (ω (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y) := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy using pullbackCLM_apply_of_mem ω hy
    rw [extDerivCLM_apply, pullbackCLM_apply_of_mem _ hx, extDerivCLM_apply, heq.extDeriv_eq]
    exact extDeriv_pullback (ω.contDiff.differentiable (by simp) _)
      (hΦ.contDiffAt (Ω.isOpen.mem_nhds hx)) (by simp)
  · rw [pullbackCLM_apply_of_notMem _ hx, image_eq_zero_of_notMem_tsupport fun hx' ↦
      hx (inter_subset_left (tsupport_pullbackCLM_subset ω (tsupport_extDerivCLM_subset _ hx')))]

/-- **Naturality of the exterior derivative**, as an identity of continuous linear maps. -/
theorem pullbackCLM_comp_extDerivCLM :
    (pullbackCLM Φ hΦ hΦp ∘L extDerivCLM : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      extDerivCLM ∘L pullbackCLM Φ hΦ hΦp := by
  ext ω : 1
  exact (extDerivCLM_pullbackCLM ω).symm

end TestFunction

namespace ContinuousLinearMap

open TestFunction

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {Ω : Opens E} {Ω' : Opens E'} {Φ : E → E'} {k : ℕ} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
  {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}

/-- **Pushforward commutes with the boundary**: for a current `T` on `Ω`, the pushforward
`Φ_# T = T ∘ Φ^*` satisfies `∂ (Φ_# T) = Φ_# (∂ T)`, where `∂ T = T ∘ d`. -/
theorem comp_pullbackCLM_comp_extDerivCLM (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L pullbackCLM Φ hΦ hΦp) ∘L extDerivCLM = (T ∘L extDerivCLM) ∘L pullbackCLM Φ hΦ hΦp := by
  rw [comp_assoc, pullbackCLM_comp_extDerivCLM, comp_assoc]

end ContinuousLinearMap

namespace Distribution

open TestFunction

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {Ω' : Opens E'} {Φ : E → E'} {k : ℕ} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
  {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
  {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
  [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]

/-- **The mass of a pushforward**: if `‖DΦ‖ ≤ L` on `Ω`, then the pushforward `T ∘ Φ^*` of a
`k`-current `T` has mass at most `L ^ k` times the mass of `T`. -/
theorem mass_comp_pullbackCLM_le (T : 𝓕) {L : ℝ≥0} (hL : ∀ x ∈ Ω, ‖fderiv ℝ Φ x‖ ≤ L) :
    mass (T ∘ pullbackCLM Φ hΦ hΦp) ≤ (L : ℝ≥0∞) ^ k * mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hb : ‖(pullbackCLM Φ hΦ hΦp ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤ L ^ k := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [coe_toBoundedContinuousFunction]
    by_cases hx : x ∈ Ω
    · refine (norm_pullbackCLM_apply_le ω x).trans ?_
      calc ‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k ≤ 1 * (L : ℝ) ^ k := by
            gcongr
            exacts [hω _, hL x hx]
        _ = L ^ k := one_mul _
    · simp [hx]
  calc ‖T (pullbackCLM Φ hΦ hΦp ω)‖ₑ
      ≤ mass T * ‖(pullbackCLM Φ hΦ hΦp ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ :=
        enorm_apply_le_mass_mul T _
    _ ≤ mass T * (L : ℝ≥0∞) ^ k := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow L.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal hb
    _ = (L : ℝ≥0∞) ^ k * mass T := mul_comm _ _

end Distribution
