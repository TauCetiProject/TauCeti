/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.PoincareHomotopy
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The Euclidean cone over a compactly supported current

Let `Ω` be an open subset of a finite-dimensional real normed space `E` and let `x₀ : E` be a
cone apex. For a `k`-current `T` on `Ω` whose distributional support `dsupport T` is a compact
subset of `Ω`, there exists a scalar cutoff `χ : 𝓓(Ω, ℝ)` equal to `1` on a neighbourhood of
`dsupport T`. Pairing `T` with `TestFunction.smulPoincareHomotopyCLM x₀ χ` produces the
`(k + 1)`-current

`(cone x₀ T) ω = T (χ • poincareHomotopy x₀ ω)`,

which is independent of the choice of cutoff (`Distribution.cone_eq`) by localization of
currents along `dsupport T`. When no such cutoff exists, `cone x₀ T` takes the junk value `0`,
matching the convention of `Distribution.augmentation`.

By the tube lemma along `[0, 1]`, the support of `cone x₀ T` is compact and lies in the geometric
cone `⋃ x ∈ dsupport T, segment ℝ x₀ x` (`Distribution.dsupport_cone_subset`,
`Distribution.isCompact_dsupport_cone`). Crucially, the cone operator itself and its boundary
identities on `𝓓(Ω, …)` require only that `dsupport T` be a compact subset of `Ω`, whereas for
`cone x₀ T` to be compactly supported *inside* `Ω` one needs the geometric cone over `dsupport T`
to lie in `Ω` (`∀ x ∈ dsupport T, segment ℝ x₀ x ⊆ Ω`, in particular when `Ω` is star-convex with
respect to `x₀`).

The Poincaré homotopy identities on test forms dualize to the **homotopy boundary formulas**:

* in positive degree `k + 1`: `∂ (cone x₀ T) + cone x₀ (∂ T) = T`, so `∂ (cone x₀ T) = T`
  whenever `T` is a cycle (`∂ T = 0`);
* in degree zero: `(∂ (cone x₀ T)) ω = T ω - augmentation T (ω x₀)` (while retaining the ordinary
  zero boundary `∂₀ = 0` on `0`-currents). When `x₀ ∈ Ω`, the cone fills `T` (`∂ (cone x₀ T) = T`)
  if and only if `T` has augmentation zero (`Distribution.cone_comp_extDerivCLM_finZero_eq_iff`).

In particular, a nonzero degree-zero point current `δ_p` (`p ∈ Ω`) satisfies
`∂ (cone x₀ δ_p) = δ_p - δ_{x₀}` and cannot be filled by `cone x₀` when `x₀ ∈ Ω`, whereas an
augmented-zero two-point difference `δ_q - δ_p` (`p, q ∈ Ω`) is filled by `cone x₀ (δ_q - δ_p)`.

## Main declarations

* `Distribution.cone`: the Euclidean cone `(k + 1)`-current with apex `x₀` over a `k`-current `T`.
* `Distribution.cone_eq`, `Distribution.cone_comp_monoCLM`: independence of the cutoff `χ` and
  compatibility with restriction to smaller open neighbourhoods of `dsupport T`.
* `Distribution.cone_smul`, `Distribution.cone_neg`, `Distribution.cone_add`,
  `Distribution.cone_sub`: linearity on currents with compact support in `Ω`.
* `Distribution.dsupport_cone_subset`, `Distribution.isCompact_dsupport_cone`,
  `Distribution.dsupport_cone_subset_of_segment_subset`, `StarConvex.dsupport_cone_subset`:
  compactness and exact geometric cone control of `dsupport (cone x₀ T)`.
* `Distribution.cone_comp_extDerivCLM_add_cone_comp_extDerivCLM`,
  `Distribution.cone_comp_extDerivCLM`, `Distribution.cone_comp_extDerivCLM_of_eq_zero`:
  positive-degree boundary homotopy formula and cycle filling.
* `Distribution.cone_comp_extDerivCLM_finZero_apply`,
  `Distribution.cone_comp_extDerivCLM_finZero_real_apply`,
  `Distribution.cone_comp_extDerivCLM_finZero_eq_iff`,
  `Distribution.cone_comp_extDerivCLM_finZero_real_eq_iff`: degree-zero boundary formula with the
  augmentation defect and iff characterization of cone filling.
* `Distribution.cone_comp_evalCLM_apply`, `Distribution.cone_comp_evalCLM_finZero_comp_extDerivCLM`,
  `Distribution.cone_sub_comp_evalCLM_finZero_comp_extDerivCLM`: explicit evaluation and filling
  on degree-zero point currents and two-point differences.
* `Distribution.not_exists_comp_extDerivCLM_eq_of_augmentation_ne_zero`,
  `Distribution.not_exists_comp_extDerivCLM_eq_comp_evalCLM`: augmentation obstruction to
  compactly supported filling, in particular for nonzero point currents.
* `StarConvex.exists_isCompact_dsupport_comp_extDerivCLM_eq_iff`,
  `StarConvex.exists_isCompact_dsupport_comp_extDerivCLM_finZero_eq_iff`: Poincaré
  characterization of compactly supported currents admitting compactly supported fillings on a
  star-convex open set (closedness in positive degree, zero augmentation in degree zero).

## References

* H. Federer, *Geometric Measure Theory*, §4.1.11 (cones over currents and homotopy formulas).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Set TopologicalSpace TauCeti
open scoped Distributions Topology BoundedContinuousFunction

/-- The union of segments `[x₀, x]` over a compact set `K` in a real normed space is compact. -/
private theorem isCompact_biUnion_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ : E) {K : Set E} (hK : IsCompact K) : IsCompact (⋃ x ∈ K, segment ℝ x₀ x) := by
  have heq : (⋃ x ∈ K, segment ℝ x₀ x) =
      (fun p : E × ℝ ↦ AffineMap.lineMap x₀ p.1 p.2) '' (K ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    simp only [mem_iUnion, exists_prop, segment_eq_image_lineMap, mem_image, mem_prod]
    exact ⟨fun ⟨x, hx, t, ht, hxt⟩ ↦ ⟨(x, t), ⟨hx, ht⟩, hxt⟩,
      fun ⟨⟨x, t⟩, ⟨hx, ht⟩, hxt⟩ ↦ ⟨x, hx, t, ht, hxt⟩⟩
  rw [heq]
  have hcont : Continuous (fun p : E × ℝ ↦ AffineMap.lineMap x₀ p.1 p.2) := by
    simp only [AffineMap.lineMap_apply_module']
    exact (continuous_snd.smul (continuous_fst.sub continuous_const)).add continuous_const
  exact (hK.prod isCompact_Icc).image hcont

namespace Distribution

section Defs

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace V] [AddCommMonoid V] [Module ℝ V]
  {Ω : Opens E} {k : ℕ}

open Classical in
/-- The **Euclidean cone** with apex `x₀` over a `k`-current `T` on `Ω`: the `(k + 1)`-current
`T ∘L smulPoincareHomotopyCLM x₀ χ`, where `χ : 𝓓(Ω, ℝ)` is a test function equal to `1` on a
neighbourhood of `dsupport T`. When `E` is finite-dimensional, it is independent of the choice of
`χ` (`Distribution.cone_eq`), and such a cutoff exists whenever `dsupport T` is a compact subset
of `Ω`. It is `0` when no such cutoff exists. -/
def cone (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V :=
  if h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 then
    T ∘L TestFunction.smulPoincareHomotopyCLM x₀ h.choose
  else 0

/-- The cone is zero when no test function on `Ω` equals `1` near `dsupport T`. -/
@[simp]
theorem cone_of_not_exists (x₀ : E) {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (h : ¬∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    cone x₀ T = 0 := by
  rw [cone, dite_eq_right h]

@[simp]
theorem cone_zero (x₀ : E) :
    cone x₀ (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) = 0 := by
  unfold cone
  split_ifs
  · exact zero_comp _
  · rfl

end Defs

section Group

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  {Ω : Opens E} {k : ℕ}

/-- **Independence of the cutoff.** For any test function `χ : 𝓓(Ω, ℝ)` equal to `1` on a
neighbourhood of `dsupport T`, `cone x₀ T` is `T ∘L smulPoincareHomotopyCLM x₀ χ`. -/
theorem cone_eq (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    cone x₀ T = T ∘L TestFunction.smulPoincareHomotopyCLM x₀ χ := by
  have h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := ⟨χ, hχ⟩
  rw [cone, dite_eq_left h]
  ext ω
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [h.choose_spec, hχ] with x h₁ h₂
  simp [h₁, h₂]

theorem cone_apply (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    cone x₀ T ω = T (TestFunction.smulPoincareHomotopyCLM x₀ χ ω) := by
  rw [cone_eq x₀ T hχ, comp_apply]

/-- **Locality under open restriction.** If `U ≤ Ω` and `dsupport T` is a compact subset of `U`,
then restricting `cone x₀ T` from `Ω` to `U` agrees with the cone on `U` of the restriction of `T`
to `U`. -/
theorem cone_comp_monoCLM (x₀ : E) {U : Opens E} (hUΩ : U ≤ Ω)
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTU : dsupport T ⊆ U) :
    (cone x₀ T) ∘L TestFunction.monoCLM ℝ =
      cone x₀ (T ∘L (TestFunction.monoCLM ℝ : 𝓓(U, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) := by
  obtain ⟨ψ, hψ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTU
  let χ : 𝓓(Ω, ℝ) := TestFunction.monoCLM ℝ ψ
  have hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 :=
    hψ.mono fun x hx ↦ by simp [χ, TestFunction.monoCLM_apply, hUΩ, hx]
  have hsub : dsupport (T ∘L (TestFunction.monoCLM ℝ : 𝓓(U, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ⊆
      dsupport T := by
    refine compl_subset_compl.1 fun x hx ↦ ?_
    rw [mem_compl_iff, notMem_dsupport_iff] at hx ⊢
    obtain ⟨W, hW, hWo, hxW⟩ := hx
    refine ⟨W, fun ω hω ↦ hW (TestFunction.monoCLM ℝ ω) ?_, hWo, hxW⟩
    simpa [TestFunction.monoCLM_apply, hUΩ] using hω
  rw [cone_eq x₀ T hχ, cone_eq x₀ _ (hψ.filter_mono (nhdsSet_mono hsub))]
  ext ω
  simp only [comp_apply]
  congr 1
  refine TestFunction.ext fun y ↦ ?_
  have hω : ((TestFunction.monoCLM ℝ ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
      E → E [⋀^Fin (k + 1)]→L[ℝ] F) = ω := by
    funext z
    simp [TestFunction.monoCLM_apply, hUΩ]
  simp [χ, TestFunction.monoCLM_apply, hUΩ, hω]

/-- **Support of the Euclidean cone.** The distributional support of `cone x₀ T` lies in the
geometric cone `⋃ x ∈ dsupport T, segment ℝ x₀ x`. No compactness hypothesis is needed: when no
cutoff exists on `Ω`, `cone x₀ T = 0`, and when a cutoff exists, `dsupport T` is automatically a
compact subset of its support. -/
theorem dsupport_cone_subset (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    dsupport (cone x₀ T) ⊆ ⋃ x ∈ dsupport T, segment ℝ x₀ x := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    have hTsub : dsupport T ⊆ tsupport χ := fun x hx ↦
      subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx])
    have hTc : IsCompact (dsupport T) :=
      χ.hasCompactSupport.of_isClosed_subset isClosed_dsupport hTsub
    have hK : IsCompact (⋃ x ∈ dsupport T, segment ℝ x₀ x) := isCompact_biUnion_segment x₀ hTc
    refine compl_subset_compl.1 fun y hy ↦ ?_
    rw [mem_compl_iff, notMem_dsupport_iff]
    refine ⟨(⋃ x ∈ dsupport T, segment ℝ x₀ x)ᶜ, fun ω hω ↦ ?_, hK.isClosed.isOpen_compl, hy⟩
    rw [cone_apply x₀ T hχ ω, ← map_zero T]
    exact map_eq_map_of_eventuallyEq T <|
      TestFunction.smulPoincareHomotopyCLM_eventuallyEq_zero_of_disjoint x₀ χ
        (disjoint_compl_left.mono_left hω)
  · rw [cone_of_not_exists x₀ h, (dsupport_eq_empty_iff (0 : _ →L[ℝ] V)).2 rfl]
    exact empty_subset _

/-- The distributional support of `cone x₀ T` is always compact. -/
theorem isCompact_dsupport_cone (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    IsCompact (dsupport (cone x₀ T)) := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    have hTsub : dsupport T ⊆ tsupport χ := fun x hx ↦
      subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx])
    have hTc : IsCompact (dsupport T) :=
      χ.hasCompactSupport.of_isClosed_subset isClosed_dsupport hTsub
    exact (isCompact_biUnion_segment x₀ hTc).of_isClosed_subset isClosed_dsupport
      (dsupport_cone_subset x₀ T)
  · rw [cone_of_not_exists x₀ h, (dsupport_eq_empty_iff (0 : _ →L[ℝ] V)).2 rfl]
    exact isCompact_empty

/-- If every segment `[x₀, x]` from the apex to a point of `dsupport T` lies in `Ω`, then
`cone x₀ T` is supported inside `Ω`. -/
theorem dsupport_cone_subset_of_segment_subset (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hseg : ∀ x ∈ dsupport T, segment ℝ x₀ x ⊆ Ω) :
    dsupport (cone x₀ T) ⊆ Ω :=
  (dsupport_cone_subset x₀ T).trans (iUnion₂_subset hseg)

theorem cone_smul [ContinuousConstSMul ℝ V] (x₀ : E) (a : ℝ)
    (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    cone x₀ (a • T) = a • cone x₀ T := by
  have hsub : dsupport (a • T) ⊆ dsupport T :=
    dsupport_subset_dsupport fun _ _ h ω hω ↦ by simp [h ω hω]
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    rw [cone_eq x₀ (a • T) (hχ.filter_mono (nhdsSet_mono hsub)), cone_eq x₀ T hχ, smul_comp]
  have h0 : a • (0 : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) = 0 := by ext; simp
  rw [cone_of_not_exists x₀ h, h0]
  rcases eq_or_ne a 0 with rfl | ha
  · have h0T : (0 : ℝ) • T = 0 := by ext; simp
    rw [h0T, cone_zero]
  have hsup : dsupport T ⊆ dsupport (a • T) :=
    dsupport_subset_dsupport fun _ _ h' ω hω ↦ by simpa [ha] using h' ω hω
  rw [cone_of_not_exists x₀ (hsub.antisymm hsup ▸ h)]

/-- **Homotopy boundary formula in degree zero.** For a `0`-current `T` on `Ω` whose support is a
compact subset of `Ω`, `(∂ (cone x₀ T)) ω = T ω - augmentation T (ω x₀)`. -/
theorem cone_comp_extDerivCLM_finZero_apply (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) :
    ((cone x₀ T) ∘L TestFunction.extDerivCLM) ω = T ω - augmentation T (ω x₀) := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  rw [comp_apply, cone_apply x₀ T hχ,
    map_eq_map_of_eventuallyEq T
      (TestFunction.smulPoincareHomotopyCLM_extDerivCLM_finZero_eventuallyEq x₀ hχ ω),
    map_sub, augmentation_eq T hχ (ω x₀)]

/-- Scalar `0`-current specialization of `Distribution.cone_comp_extDerivCLM_finZero_apply`: the
augmentation defect is `(ω x₀ ![]) • augmentation T 1`, where `1` is the unit constant `0`-form. -/
theorem cone_comp_extDerivCLM_finZero_real_apply (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ)) :
    ((cone x₀ T) ∘L TestFunction.extDerivCLM) ω =
      T ω - (ω x₀ ![]) •
        augmentation T (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1) := by
  let c₁ := ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
  have hω : ω x₀ = (ω x₀ ![]) • c₁ := by
    ext v
    simp [c₁, Subsingleton.elim v ![]]
  have haug : augmentation T (ω x₀) = (ω x₀ ![]) • augmentation T c₁ := by
    rw [← augmentation_smul_right, ← hω]
  rw [cone_comp_extDerivCLM_finZero_apply x₀ hT hTΩ ω, haug]

/-- If a `0`-current `T` with compact support in `Ω` has augmentation zero at every constant
`0`-form, then `cone x₀ T` fills `T`: `∂ (cone x₀ T) = T`. -/
theorem cone_comp_extDerivCLM_finZero_of_augmentation_eq_zero (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (haug : ∀ c, augmentation T c = 0) :
    (cone x₀ T) ∘L TestFunction.extDerivCLM = T := by
  ext ω
  rw [cone_comp_extDerivCLM_finZero_apply x₀ hT hTΩ ω, haug (ω x₀), sub_zero]

/-- **Characterization of degree-zero cone filling.** When the apex `x₀` belongs to `Ω` and `T` is
a `0`-current whose support is a compact subset of `Ω`, the cone `cone x₀ T` fills `T`
(`∂ (cone x₀ T) = T`) if and only if `T` has augmentation zero at every constant `0`-form. -/
theorem cone_comp_extDerivCLM_finZero_eq_iff {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (cone x₀ T) ∘L TestFunction.extDerivCLM = T ↔ ∀ c, augmentation T c = 0 := by
  refine ⟨fun h c ↦ ?_, cone_comp_extDerivCLM_finZero_of_augmentation_eq_zero x₀ hT hTΩ⟩
  obtain ⟨ψ, hψ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) isCompact_singleton
    (singleton_subset_iff.2 hx₀)
  have hψx₀ : ψ x₀ = 1 := hψ.self_of_nhdsSet x₀ rfl
  let ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) := TestFunction.postcompCLM (toSpanSingleton ℝ c) ψ
  have hωx₀ : ω x₀ = c := by simp [ω, hψx₀]
  have heval := congrArg (· ω) h
  rw [cone_comp_extDerivCLM_finZero_apply x₀ hT hTΩ ω, hωx₀, sub_eq_self] at heval
  exact heval

/-- Scalar `0`-current characterization of cone filling: when `x₀ ∈ Ω`, `∂ (cone x₀ T) = T` if and
only if the augmentation of `T` on the unit constant `0`-form vanishes. -/
theorem cone_comp_extDerivCLM_finZero_real_eq_iff {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (cone x₀ T) ∘L TestFunction.extDerivCLM = T ↔
      augmentation T (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1) = 0 := by
  rw [cone_comp_extDerivCLM_finZero_eq_iff hx₀ hT hTΩ]
  refine ⟨fun h ↦ h _, fun h c ↦ ?_⟩
  have hc : c = (c ![]) • ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ) := by
    ext v
    simp [Subsingleton.elim v ![]]
  rw [hc, augmentation_smul_right, h, smul_zero]

/-! ### Point currents and two-point differences -/

/-- Evaluating `cone x₀` on a point current `ω ↦ ℓ (ω p)` (`p ∈ Ω`) gives the radial integral
`ℓ (poincareHomotopy x₀ ω p)` along `[x₀, p]`. -/
theorem cone_comp_evalCLM_apply (x₀ : E) {p : E} (hp : p ∈ Ω)
    (ℓ : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    cone x₀ (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
      (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ω =
      ℓ (poincareHomotopy x₀ ω p) := by
  set δp := ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
    (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)
  have hsub : dsupport δp ⊆ {p} := by
    have hcoe : ⇑δp = fun φ ↦ ℓ.toAddMonoidHom (φ p) := rfl
    rw [hcoe]
    exact dsupport_apply_apply_subset ℓ.toAddMonoidHom
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) isCompact_singleton
    (singleton_subset_iff.2 hp)
  have hχp : χ p = 1 := hχ.self_of_nhdsSet p rfl
  rw [cone_apply x₀ δp (hχ.filter_mono (nhdsSet_mono hsub)) ω]
  simp [δp, hχp]

/-- The cone with apex `x₀ ∈ Ω` over a point current at `x₀` itself vanishes. -/
theorem cone_comp_evalCLM_self {x₀ : E} (hx₀ : x₀ ∈ Ω) (ℓ : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    cone x₀ (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ x₀ ∘L
      (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) = 0 := by
  ext ω
  rw [cone_comp_evalCLM_apply x₀ hx₀ ℓ ω, poincareHomotopy_self, map_zero, zero_apply]

section TopologicalAddGroup

variable [IsTopologicalAddGroup V]

theorem cone_neg (x₀ : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    cone x₀ (-T) = -cone x₀ T := by
  have hsup : dsupport (-T) = dsupport T :=
    (dsupport_subset_dsupport fun _ _ h ω hω ↦ by simp [h ω hω]).antisymm
      (dsupport_subset_dsupport fun _ _ h ω hω ↦ by simpa using h ω hω)
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    rw [cone_eq x₀ (-T) (hsup ▸ hχ), cone_eq x₀ T hχ, neg_comp]
  · rw [cone_of_not_exists x₀ (hsup ▸ h), cone_of_not_exists x₀ h, neg_zero]

theorem cone_add (x₀ : E) {T S : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hS : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) :
    cone x₀ (T + S) = cone x₀ T + cone x₀ S := by
  obtain ⟨χ, hχ, -⟩ :=
    TestFunction.exists_eventually_eq_one (n := ⊤) (hT.union hS) (union_subset hTΩ hSΩ)
  have hsum : dsupport (T + S) ⊆ dsupport T ∪ dsupport S := by
    rw [FunLike.coe_add]
    exact dsupport_add_subset T S
  rw [cone_eq x₀ (T + S) (hχ.filter_mono (nhdsSet_mono hsum)),
    cone_eq x₀ T (hχ.filter_mono (nhdsSet_mono subset_union_left)),
    cone_eq x₀ S (hχ.filter_mono (nhdsSet_mono subset_union_right)), add_comp]

theorem cone_sub (x₀ : E) {T S : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hS : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) :
    cone x₀ (T - S) = cone x₀ T - cone x₀ S := by
  have hneg : dsupport (-S) = dsupport S :=
    (dsupport_subset_dsupport fun _ _ h ω hω ↦ by simp [h ω hω]).antisymm
      (dsupport_subset_dsupport fun _ _ h ω hω ↦ by simpa using h ω hω)
  rw [sub_eq_add_neg, cone_add x₀ hT hTΩ (hneg ▸ hS) (hneg ▸ hSΩ), cone_neg, ← sub_eq_add_neg]

/-- **Homotopy boundary formula in positive degree.** For a `(k + 1)`-current `T` on `Ω` whose
support is a compact subset of `Ω`, `∂ (cone x₀ T) + cone x₀ (∂ T) = T`, where `∂ S = S ∘L d`. -/
theorem cone_comp_extDerivCLM_add_cone_comp_extDerivCLM (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    ((cone x₀ T) ∘L TestFunction.extDerivCLM) + cone x₀ (T ∘L TestFunction.extDerivCLM) = T := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTΩ
  have hsub : dsupport (T ∘L TestFunction.extDerivCLM) ⊆ dsupport T := by
    rw [coe_comp]
    exact dsupport_comp_extDerivCLM_subset T
  have hχ' : ∀ᶠ x in 𝓝ˢ (dsupport (T ∘L TestFunction.extDerivCLM)), χ x = 1 :=
    hχ.filter_mono (nhdsSet_mono hsub)
  rw [cone_eq x₀ T hχ, cone_eq x₀ (T ∘L TestFunction.extDerivCLM) hχ']
  ext ω
  simp only [add_apply, comp_apply, ← map_add]
  exact map_eq_map_of_eventuallyEq T <|
    (TestFunction.extDerivCLM_smulPoincareHomotopyCLM_add_eventuallyEq x₀ hχ ω).mono
      fun y hy ↦ by simpa [add_comm] using hy

/-- Rearranged positive-degree boundary formula: `∂ (cone x₀ T) = T - cone x₀ (∂ T)`. -/
theorem cone_comp_extDerivCLM (x₀ : E) {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (cone x₀ T) ∘L TestFunction.extDerivCLM = T - cone x₀ (T ∘L TestFunction.extDerivCLM) :=
  eq_sub_of_add_eq (cone_comp_extDerivCLM_add_cone_comp_extDerivCLM x₀ hT hTΩ)

/-- **Cycle filling in positive degree.** If `T` is a closed `(k + 1)`-current (`∂ T = 0`) whose
support is a compact subset of `Ω`, then `∂ (cone x₀ T) = T`. When in addition every segment
`[x₀, x]` for `x ∈ dsupport T` lies in `Ω`, `cone x₀ T` is compactly supported in `Ω` by
`Distribution.isCompact_dsupport_cone` and `Distribution.dsupport_cone_subset_of_segment_subset`. -/
theorem cone_comp_extDerivCLM_of_eq_zero (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hcycle : T ∘L TestFunction.extDerivCLM = 0) :
    (cone x₀ T) ∘L TestFunction.extDerivCLM = T := by
  rw [cone_comp_extDerivCLM x₀ hT hTΩ, hcycle, cone_zero, sub_zero]

/-- **Boundary of the cone over a degree-zero point current.** For `p ∈ Ω`, the cone with apex `x₀`
over the point `0`-current `δ_p : ω ↦ ℓ (ω p)` has boundary `δ_p - δ_{x₀}`: the augmentation of
`δ_p` produces an opposite point mass at the apex `x₀`. -/
theorem cone_comp_evalCLM_finZero_comp_extDerivCLM (x₀ : E) {p : E} (hp : p ∈ Ω)
    (ℓ : (E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) :
    (cone x₀ (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
        (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _))) ∘L
      TestFunction.extDerivCLM =
      (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
        TestFunction.toBoundedContinuousFunctionCLM ℝ) -
      (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ x₀ ∘L
        TestFunction.toBoundedContinuousFunctionCLM ℝ) := by
  set δp := ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
    (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _)
  have hcoe : ⇑δp = fun φ ↦ ℓ.toAddMonoidHom (φ p) := rfl
  have hsub : dsupport δp ⊆ {p} := hcoe ▸ dsupport_apply_apply_subset ℓ.toAddMonoidHom
  have hc : IsCompact (dsupport δp) := isCompact_singleton.of_isClosed_subset isClosed_dsupport hsub
  have hΩ : dsupport δp ⊆ Ω := hsub.trans (singleton_subset_iff.2 hp)
  ext ω
  rw [cone_comp_extDerivCLM_finZero_apply x₀ hc hΩ ω, hcoe,
    augmentation_apply_apply hp ℓ.toAddMonoidHom (ω x₀)]
  rfl

/-- **Cone filling of an augmented-zero two-point difference.** For `p, q ∈ Ω` and any linear map
`ℓ` on `0`-forms, the two-point difference `δ_q - δ_p` has augmentation zero and is filled by its
Euclidean cone: `∂ (cone x₀ (δ_q - δ_p)) = δ_q - δ_p`. -/
theorem cone_sub_comp_evalCLM_finZero_comp_extDerivCLM (x₀ : E) {p q : E}
    (hp : p ∈ Ω) (hq : q ∈ Ω) (ℓ : (E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) :
    (cone x₀
        ((ℓ ∘L BoundedContinuousFunction.evalCLM ℝ q ∘L
            (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _)) -
          (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
            TestFunction.toBoundedContinuousFunctionCLM ℝ))) ∘L
      TestFunction.extDerivCLM =
      (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ q ∘L
        TestFunction.toBoundedContinuousFunctionCLM ℝ) -
      (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
        TestFunction.toBoundedContinuousFunctionCLM ℝ) := by
  set δ : E → 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V := fun z ↦
    ℓ ∘L BoundedContinuousFunction.evalCLM ℝ z ∘L TestFunction.toBoundedContinuousFunctionCLM ℝ
  have hsub (z : E) : dsupport (δ z) ⊆ {z} :=
    dsupport_apply_apply_subset (Ω := Ω) (n := ⊤) (x := z) ℓ.toAddMonoidHom
  have hc (z : E) : IsCompact (dsupport (δ z)) :=
    isCompact_singleton.of_isClosed_subset isClosed_dsupport (hsub z)
  rw [cone_sub x₀ (hc q) ((hsub q).trans (singleton_subset_iff.2 hq))
    (hc p) ((hsub p).trans (singleton_subset_iff.2 hp)),
    sub_comp, cone_comp_evalCLM_finZero_comp_extDerivCLM x₀ hq ℓ,
    cone_comp_evalCLM_finZero_comp_extDerivCLM x₀ hp ℓ, sub_sub_sub_cancel_right]

end TopologicalAddGroup

end Group

section Obstruction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  {Ω : Opens E} {k : ℕ}

/-- **Augmentation obstruction to compactly supported filling.** A `k`-current `T` whose
augmentation is nonzero at some constant `k`-form cannot equal `Q ∘L extDerivCLM` for any
`(k + 1)`-current `Q` with compact support in `Ω` (in particular at `k = 0`, where the ordinary
boundary `∂₀ T` of every `0`-current is zero). -/
theorem not_exists_comp_extDerivCLM_eq_of_augmentation_ne_zero
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    {c : E [⋀^Fin k]→L[ℝ] F} (haug : augmentation T c ≠ 0) :
    ¬∃ Q : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V,
      IsCompact (dsupport Q) ∧ dsupport Q ⊆ Ω ∧ Q ∘L TestFunction.extDerivCLM = T := by
  rintro ⟨Q, hQc, hQΩ, rfl⟩
  exact haug (augmentation_comp_extDerivCLM Q hQc hQΩ c)

/-- A single point `k`-current `ω ↦ ℓ (ω p)` at `p ∈ Ω` with `ℓ ≠ 0` has nonzero augmentation and
therefore admits no compactly supported `(k + 1)`-current filling on `Ω`. -/
theorem not_exists_comp_extDerivCLM_eq_comp_evalCLM {p : E} (hp : p ∈ Ω)
    {ℓ : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V} (hℓ : ℓ ≠ 0) :
    ¬∃ Q : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V,
      IsCompact (dsupport Q) ∧ dsupport Q ⊆ Ω ∧
        Q ∘L TestFunction.extDerivCLM =
          ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
            TestFunction.toBoundedContinuousFunctionCLM ℝ := by
  have ⟨c, hc⟩ : ∃ c, ℓ c ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext h)
  set δp : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V :=
    ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L TestFunction.toBoundedContinuousFunctionCLM ℝ
  refine not_exists_comp_extDerivCLM_eq_of_augmentation_ne_zero (T := δp) (c := c) ?_
  have hcoe : (δp : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) → V) = fun φ ↦ ℓ.toAddMonoidHom (φ p) := rfl
  rw [hcoe, augmentation_apply_apply hp ℓ.toAddMonoidHom c]
  exact hc

end Obstruction

end Distribution

namespace StarConvex

open Distribution

/-- If the open set `Ω` is star-convex with respect to `x₀`, then `cone x₀ T` is supported inside
`Ω` for every current `T` on `Ω`. -/
theorem dsupport_cone_subset {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V] {Ω : Opens E} {k : ℕ} {x₀ : E}
    (hΩ : StarConvex ℝ x₀ (Ω : Set E)) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    dsupport (cone x₀ T) ⊆ Ω := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨χ, hχ⟩ := h
    have hTΩ : dsupport T ⊆ Ω := fun x hx ↦
      χ.tsupport_subset (subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx]))
    exact dsupport_cone_subset_of_segment_subset x₀ fun x hx ↦ hΩ.segment_subset (hTΩ hx)
  · rw [cone_of_not_exists x₀ h, (dsupport_eq_empty_iff (0 : _ →L[ℝ] V)).2 rfl]
    exact empty_subset _

/-- **Compactly supported Poincaré lemma in positive degree.** On an open set `Ω` star-convex with
respect to `x₀`, a `(k + 1)`-current `T` with compact support in `Ω` admits a `(k + 2)`-current
filling with compact support in `Ω` if and only if `∂ T = 0`. -/
theorem exists_isCompact_dsupport_comp_extDerivCLM_eq_iff {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace V] [AddCommGroup V] [IsTopologicalAddGroup V] [Module ℝ V]
    {Ω : Opens E} {k : ℕ} {x₀ : E} (hΩ : StarConvex ℝ x₀ (Ω : Set E))
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (∃ Q : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] V,
      IsCompact (dsupport Q) ∧ dsupport Q ⊆ Ω ∧ Q ∘L TestFunction.extDerivCLM = T) ↔
      T ∘L TestFunction.extDerivCLM = 0 := by
  refine ⟨?_, fun hcycle ↦ ⟨cone x₀ T, isCompact_dsupport_cone x₀ T, hΩ.dsupport_cone_subset T,
    cone_comp_extDerivCLM_of_eq_zero x₀ hT hTΩ hcycle⟩⟩
  rintro ⟨Q, -, -, rfl⟩
  rw [comp_assoc, TestFunction.extDerivCLM_comp_extDerivCLM, comp_zero]

/-- **Compactly supported Poincaré lemma in degree zero.** On an open set `Ω` star-convex with
respect to `x₀`, a `0`-current `T` with compact support in `Ω` admits a `1`-current filling with
compact support in `Ω` if and only if its augmentation vanishes on every constant `0`-form. -/
theorem exists_isCompact_dsupport_comp_extDerivCLM_finZero_eq_iff {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    {Ω : Opens E} {x₀ : E} (hΩ : StarConvex ℝ x₀ (Ω : Set E))
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    (∃ Q : 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] F) →L[ℝ] V,
      IsCompact (dsupport Q) ∧ dsupport Q ⊆ Ω ∧ Q ∘L TestFunction.extDerivCLM = T) ↔
      ∀ c, augmentation T c = 0 := by
  refine ⟨fun ⟨Q, hQc, hQΩ, hQT⟩ c ↦ ?_, fun haug ↦
    ⟨cone x₀ T, isCompact_dsupport_cone x₀ T, hΩ.dsupport_cone_subset T,
      cone_comp_extDerivCLM_finZero_of_augmentation_eq_zero x₀ hT hTΩ haug⟩⟩
  rw [← hQT]
  exact augmentation_comp_extDerivCLM Q hQc hQΩ c

end StarConvex
