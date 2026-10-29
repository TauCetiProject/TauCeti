/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differential forms on nested open subsets

For open subsets `U ≤ W` of a manifold, a rough form on `W` restricts to `U` by pullback along the
inclusion `TopologicalSpace.Opens.inclusion`. The differential of that inclusion is the identity of
the model space, so restriction does not change the values of the form
(`TauCeti.mpullback_inclusion_apply`), and the charts of `U` are restrictions of those of `W`, so
the coordinate expressions agree near every point of `U`.

Consequently regularity of forms is local (`TauCeti.contMDiffAt_mpullback_inclusion_iff`): a form
on `W` is `C^n` as soon as its restrictions to the members of an open cover of `W` are
(`TauCeti.IsSmoothForm.of_mpullback_inclusion`). Conversely, a form on `U` extends by zero to `W`
(`TauCeti.RoughForm.extendByZero`), and the extension is `C^n` when it vanishes near every point
of `W` outside `U` (`TauCeti.IsSmoothForm.extendByZero`); this applies in particular to the
product of a form with a cut-off function (`TauCeti.IsSmoothForm.extendByZero_smul`), and, on a
Hausdorff manifold, to every compactly supported form on `U`, whose extension vanishes near the
points outside `U` (`TauCeti.RoughForm.eventually_extendByZero_eq_zero`) and is again compactly
supported (`TauCeti.RoughForm.isCompact_tsupport_extendByZero`).

The exterior derivative is local, so, without any regularity assumption, it commutes with
restriction to an open subset (`TauCeti.mpullback_inclusion_mextDeriv`) and with extension by zero
whenever the extension vanishes near every point of `W` outside `U`
(`TauCeti.RoughForm.mextDeriv_extendByZero`).

These are the gluing and cut-off steps of the Mayer–Vietoris sequence of de Rham cohomology, and
the extension step of its compactly supported variant.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
-/

public section

noncomputable section

open Set Filter TopologicalSpace Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Restricting a form to a smaller open subset does not change its value at any point. -/
theorem mpullback_inclusion_apply {U W : Opens M} (h : U ≤ W) (γ : RoughForm I W F k) (x : U) :
    mpullback I I (Opens.inclusion h) γ x = γ (Opens.inclusion h x) := by
  ext v
  rw [mpullback_apply]
  simp only [Manifold.mfderiv_inclusion_apply]
  rfl

/-- The extension by zero of a rough form on an open subset `U` to an open subset `W`: it agrees
with the form at the points of `W` lying in `U` and vanishes at the others. -/
def RoughForm.extendByZero {U : Opens M} (W : Opens M) (ω : RoughForm I U F k) :
    RoughForm I W F k := by
  classical
  exact fun x ↦ if hx : (x : M) ∈ U then ω ⟨x, hx⟩ else 0

namespace RoughForm

/-- The extension by zero agrees with the form on the smaller open subset. -/
@[simp]
theorem extendByZero_inclusion {U W : Opens M} (h : U ≤ W) (ω : RoughForm I U F k) (x : U) :
    extendByZero W ω (Opens.inclusion h x) = ω x := by
  simp only [extendByZero, Opens.inclusion]
  exact dite_eq_left x.2

/-- The extension by zero agrees with the form at the points of the smaller open subset. -/
theorem extendByZero_apply_of_mem {U W : Opens M} (ω : RoughForm I U F k) {x : W}
    (hx : (x : M) ∈ U) : extendByZero W ω x = ω ⟨x, hx⟩ := by
  simp only [extendByZero]
  exact dite_eq_left hx

/-- The extension by zero vanishes outside the smaller open subset. -/
theorem extendByZero_apply_of_notMem {U W : Opens M} (ω : RoughForm I U F k)
    {x : W} (hx : (x : M) ∉ U) : extendByZero W ω x = 0 := by
  simp only [extendByZero]
  exact dite_eq_right hx

/-- Restricting the extension by zero recovers the original form. -/
@[simp]
theorem mpullback_inclusion_extendByZero {U W : Opens M} (h : U ≤ W) (ω : RoughForm I U F k) :
    mpullback I I (Opens.inclusion h) (extendByZero W ω) = ω := by
  funext x
  rw [mpullback_inclusion_apply, extendByZero_inclusion]

/-- Extension by zero from an open subset to itself is the identity. -/
@[simp]
theorem extendByZero_self {U : Opens M} (ω : RoughForm I U F k) : extendByZero U ω = ω :=
  funext (extendByZero_inclusion le_rfl ω)

/-- Extending by zero in two steps along `U ≤ V ≤ W` is extending by zero from `U` to `W`. -/
theorem extendByZero_extendByZero {U V : Opens M} (h : U ≤ V) (W : Opens M)
    (ω : RoughForm I U F k) : extendByZero W (extendByZero V ω) = extendByZero W ω := by
  funext x
  by_cases hU : (x : M) ∈ U
  · rw [extendByZero_apply_of_mem _ (h hU)]
    exact (extendByZero_apply_of_mem (x := ⟨x, h hU⟩) ω hU).trans
      (extendByZero_apply_of_mem _ hU).symm
  · rw [extendByZero_apply_of_notMem _ hU]
    by_cases hV : (x : M) ∈ V
    · rw [extendByZero_apply_of_mem _ hV]
      exact extendByZero_apply_of_notMem (x := ⟨x, hV⟩) ω hU
    · exact extendByZero_apply_of_notMem _ hV

/-- Extension by zero of the zero form is zero. -/
@[simp]
theorem extendByZero_zero {U : Opens M} (W : Opens M) :
    extendByZero W (0 : RoughForm I U F k) = 0 := by
  funext x
  by_cases hx : (x : M) ∈ U
  · rw [extendByZero_apply_of_mem _ hx]
    -- The fibres of `U` at `⟨x, hx⟩` and of `W` at `x` are both the model fibre, so the remaining
    -- pointwise identity holds by unfolding the operations on dependent functions.
    rfl
  · exact extendByZero_apply_of_notMem _ hx

/-- Extension by zero is additive. -/
@[simp]
theorem extendByZero_add {U : Opens M} (W : Opens M) (ω η : RoughForm I U F k) :
    extendByZero W (ω + η) = extendByZero W ω + extendByZero W η := by
  funext x
  by_cases hx : (x : M) ∈ U
  · rw [Pi.add_apply, extendByZero_apply_of_mem _ hx, extendByZero_apply_of_mem _ hx,
      extendByZero_apply_of_mem _ hx]
    -- The fibres of `U` at `⟨x, hx⟩` and of `W` at `x` are both the model fibre, so the remaining
    -- pointwise identity holds by unfolding the operations on dependent functions.
    rfl
  · rw [Pi.add_apply, extendByZero_apply_of_notMem _ hx, extendByZero_apply_of_notMem _ hx,
      extendByZero_apply_of_notMem _ hx, add_zero]

/-- Extension by zero commutes with multiplication by a constant. -/
@[simp]
theorem extendByZero_smul {U : Opens M} (W : Opens M) (c : ℝ) (ω : RoughForm I U F k) :
    extendByZero W (c • ω) = c • extendByZero W ω := by
  funext x
  by_cases hx : (x : M) ∈ U
  · rw [Pi.smul_apply, extendByZero_apply_of_mem _ hx, extendByZero_apply_of_mem _ hx]
    -- The fibres of `U` at `⟨x, hx⟩` and of `W` at `x` are both the model fibre, so the remaining
    -- pointwise identity holds by unfolding the operations on dependent functions.
    rfl
  · rw [Pi.smul_apply, extendByZero_apply_of_notMem _ hx, extendByZero_apply_of_notMem _ hx,
      smul_zero]

/-- Viewed as a function to the model fibre, the extension by zero is `Function.extend` along the
inclusion, so Mathlib's support theory for `Function.extend` applies to it. -/
private theorem extendByZero_eq_extend {U W : Opens M} (h : U ≤ W) (ω : RoughForm I U F k) :
    (extendByZero W ω : W → E [⋀^Fin k]→L[ℝ] F) =
      Function.extend (Opens.inclusion h) (ω : U → E [⋀^Fin k]→L[ℝ] F)
        (0 : W → E [⋀^Fin k]→L[ℝ] F) := by
  funext x
  by_cases hx : (x : M) ∈ U
  · exact (extendByZero_inclusion h ω ⟨x, hx⟩).trans
      ((Set.inclusion_injective h).extend_apply _ (0 : W → E [⋀^Fin k]→L[ℝ] F) ⟨x, hx⟩).symm
  · have hxr : ¬∃ y, Opens.inclusion h y = x := by
      rintro ⟨y, rfl⟩
      exact hx y.2
    exact (extendByZero_apply_of_notMem ω hx).trans
      (Function.extend_apply' (γ := E [⋀^Fin k]→L[ℝ] F) (f := Opens.inclusion h) ω 0 x hxr).symm

section T2

variable [T2Space M]

/-- On a Hausdorff manifold, the extension by zero of a compactly supported form on an open subset
`U ≤ W` is supported in the image of the support of the form. -/
theorem tsupport_extendByZero_subset {U W : Opens M} (h : U ≤ W) {ω : RoughForm I U F k}
    (hω : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω)) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (extendByZero W ω) ⊆
      Opens.inclusion h '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω := by
  rw [extendByZero_eq_extend h]
  exact HasCompactSupport.tsupport_extend_zero_subset hω (continuous_inclusion h)

/-- On a Hausdorff manifold, the extension by zero of a compactly supported form on an open subset
`U ≤ W` is compactly supported. -/
theorem isCompact_tsupport_extendByZero {U W : Opens M} (h : U ≤ W) {ω : RoughForm I U F k}
    (hω : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (extendByZero W ω)) := by
  rw [extendByZero_eq_extend h]
  exact HasCompactSupport.extend_zero hω (continuous_inclusion h)

/-- On a Hausdorff manifold, the extension by zero of a compactly supported form on an open subset
`U ≤ W` vanishes near every point of `W` outside `U`. -/
theorem eventually_extendByZero_eq_zero {U W : Opens M} (h : U ≤ W) {ω : RoughForm I U F k}
    (hω : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω)) {x : W} (hx : (x : M) ∉ U) :
    ∀ᶠ y in 𝓝 x, extendByZero W ω y = 0 := by
  have hxs : x ∉ _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (extendByZero W ω) :=
    fun hxs ↦ hx <| by
      obtain ⟨y, -, rfl⟩ := tsupport_extendByZero_subset h hω hxs
      exact y.2
  filter_upwards [(_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) _).isOpen_compl.mem_nhds
    hxs] with y hy
  exact _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin k]→L[ℝ] F) hy

end T2

/-- Restricting the extension by zero to an open subset `V ≤ W` is the extension by zero to `V`. -/
@[simp]
theorem mpullback_inclusion_extendByZero_eq_extendByZero {U V W : Opens M} (h : V ≤ W)
    (ω : RoughForm I U F k) :
    mpullback I I (Opens.inclusion h) (extendByZero W ω) = extendByZero V ω := by
  funext x
  rw [mpullback_inclusion_apply]
  -- Both sides test membership of the same underlying point of `M` in `U`.
  rfl

/-- The extension by zero of the product of a form on `U ≤ W` with a function on `W` vanishes near
every point of `W` outside `U` near which the function vanishes. -/
theorem eventually_extendByZero_smul_eq_zero {U W : Opens M} (h : U ≤ W) (ω : RoughForm I U F k)
    {g : W → ℝ} {x : W} (hx : ∀ᶠ y in 𝓝 x, g y = 0) :
    ∀ᶠ y in 𝓝 x, extendByZero W (fun y : U ↦ g (Opens.inclusion h y) • ω y) y = 0 := by
  filter_upwards [hx] with y hy
  by_cases hyU : (y : M) ∈ U
  · obtain ⟨y, rfl⟩ : ∃ y' : U, Opens.inclusion h y' = y := ⟨⟨y, hyU⟩, Subtype.ext rfl⟩
    rw [extendByZero_inclusion]
    exact (congrArg (· • ω y) hy).trans (zero_smul ℝ _)
  · exact extendByZero_apply_of_notMem _ hyU


end RoughForm

variable [IsManifold I 1 M]

/-- Near the chart image of a point of an open subset `U ≤ W`, the coordinate expression of the
restriction of a form on `W` agrees with that of the form itself. -/
theorem RoughForm.inChartAt_mpullback_inclusion_eventuallyEq {U W : Opens M} (h : U ≤ W)
    (γ : RoughForm I W F k) (x : U) :
    (mpullback I I (Opens.inclusion h) γ).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      γ.inChartAt (Opens.inclusion h x) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin x,
    nhdsWithin_le_nhds (extChartAt_inclusion_symm_eventuallyEq (I := I) h x).eventually_nhds]
    with z hz hev
  have hev' : (extChartAt I (Opens.inclusion h x)).symm =ᶠ[𝓝 z]
      Opens.inclusion h ∘ (extChartAt I x).symm := hev
  have hmf : mfderivWithin 𝓘(ℝ, E) I (Opens.inclusion h ∘ (extChartAt I x).symm) (range I) z =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I (Opens.inclusion h x)).symm (range I) z :=
    (hev'.filter_mono nhdsWithin_le_nhds).symm.mfderivWithin_eq hev'.self_of_nhds.symm
  rw [inChartAt_mpullback γ _ x hz ((contMDiff_inclusion h).mdifferentiableAt one_ne_zero), hmf,
    ← Function.comp_apply (f := Opens.inclusion h), ← hev'.self_of_nhds]
  ext v
  exact (inChartAt_apply γ (Opens.inclusion h x) z v).symm

/-- Restriction to a smaller open subset commutes with the exterior derivative, with no regularity
assumption: near every point of the smaller subset both are computed from the same coordinate
expression. -/
theorem mpullback_inclusion_mextDeriv {U W : Opens M} (h : U ≤ W) (γ : RoughForm I W F k) :
    mpullback I I (Opens.inclusion h) (mextDeriv γ) =
      mextDeriv (mpullback I I (Opens.inclusion h) γ) := by
  funext x
  have heq := RoughForm.inChartAt_mpullback_inclusion_eventuallyEq h γ x
  rw [mpullback_inclusion_apply, mextDeriv_def, mextDeriv_def, extChartAt_inclusion_self]
  exact (heq.extDerivWithin_eq (heq.self_of_nhdsWithin (mem_range_self _))).symm

/-- The exterior derivative commutes with extension by zero from an open subset `U ≤ W`, provided
the extension vanishes near every point of `W` outside `U`. No regularity is needed. -/
theorem RoughForm.mextDeriv_extendByZero {U W : Opens M} (h : U ≤ W) {ω : RoughForm I U F k}
    (hzero : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, RoughForm.extendByZero W ω y = 0) :
    mextDeriv (RoughForm.extendByZero W ω) = RoughForm.extendByZero W (mextDeriv ω) := by
  funext x
  by_cases hx : (x : M) ∈ U
  · obtain ⟨x, rfl⟩ : ∃ x' : U, Opens.inclusion h x' = x := ⟨⟨x, hx⟩, rfl⟩
    rw [RoughForm.extendByZero_inclusion,
      ← mpullback_inclusion_apply h (mextDeriv (RoughForm.extendByZero W ω)),
      mpullback_inclusion_mextDeriv, RoughForm.mpullback_inclusion_extendByZero]
  · rw [RoughForm.extendByZero_apply_of_notMem _ hx]
    have hz : ∀ᶠ y in 𝓝 x, RoughForm.extendByZero W ω y = (0 : RoughForm I W F k) y :=
      hzero x hx
    rw [mextDeriv_congr_of_eventuallyEq hz, mextDeriv_zero]
    -- The value of the zero form at `x` is zero; the fibres differ only by the dependent typing.
    rfl

/-- Regularity of a form at a point of an open subset is regularity of its restriction there. -/
theorem contMDiffAt_mpullback_inclusion_iff {U W : Opens M} (h : U ≤ W) {n : WithTop ℕ∞}
    (γ : RoughForm I W F k) (x : U) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I (Opens.inclusion h) γ y))
        x ↔
      ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (γ y)) (Opens.inclusion h x) := by
  have heq := RoughForm.inChartAt_mpullback_inclusion_eventuallyEq h γ x
  have hpt : extChartAt I x x ∈ range I := mem_range_self _
  refine ⟨fun hx ↦ contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_,
    fun hx ↦ contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_⟩
  · have hc := RoughForm.contDiffWithinAt_inChartAt _ hx.contMDiffWithinAt (s := univ)
    rw [preimage_univ, univ_inter] at hc
    rw [extChartAt_inclusion_self]
    exact hc.congr_of_eventuallyEq heq.symm (heq.self_of_nhdsWithin hpt).symm
  · have hc := RoughForm.contDiffWithinAt_inChartAt _ hx.contMDiffWithinAt (s := univ)
    rw [preimage_univ, univ_inter, extChartAt_inclusion_self] at hc
    exact hc.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hpt)

/-- A form on an open subset `W` is `C^n` when its restrictions to the members of a family of open
subsets of `W` covering it are `C^n`. -/
theorem IsSmoothForm.of_mpullback_inclusion {W : Opens M} {ι : Type*} {U : ι → Opens M}
    (hU : ∀ i, U i ≤ W) (hcover : ∀ x : W, ∃ i, (x : M) ∈ U i) {n : WithTop ℕ∞}
    {γ : RoughForm I W F k}
    (hγ : ∀ i, IsSmoothForm I n (mpullback I I (Opens.inclusion (hU i)) γ)) :
    IsSmoothForm I n γ := by
  rw [isSmoothForm_def]
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact (contMDiffAt_mpullback_inclusion_iff (hU i) γ ⟨x, hi⟩).mp ((hγ i).contMDiff _)

/-- A form on the union of two open subsets is `C^n` when both restrictions are `C^n`. -/
theorem IsSmoothForm.of_mpullback_inclusion_sup {U V : Opens M} {n : WithTop ℕ∞}
    {γ : RoughForm I (U ⊔ V : Opens M) F k}
    (hU : IsSmoothForm I n (mpullback I I (Opens.inclusion le_sup_left) γ))
    (hV : IsSmoothForm I n (mpullback I I (Opens.inclusion le_sup_right) γ)) :
    IsSmoothForm I n γ := by
  refine IsSmoothForm.of_mpullback_inclusion (U := fun b : Bool ↦ cond b U V)
    (fun b ↦ by cases b <;> simp) (fun x ↦ ?_) fun b ↦ ?_
  · rcases Opens.mem_sup.mp x.2 with hx | hx
    exacts [⟨true, hx⟩, ⟨false, hx⟩]
  · cases b
    · exact hV
    · exact hU

/-- The extension by zero of a `C^n` form on an open subset `U ≤ W` is `C^n`, provided it vanishes
near every point of `W` outside `U`. -/
theorem IsSmoothForm.extendByZero {U W : Opens M} (h : U ≤ W) {n : WithTop ℕ∞}
    {ω : RoughForm I U F k} (hω : IsSmoothForm I n ω)
    (hzero : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, RoughForm.extendByZero W ω y = 0) :
    IsSmoothForm I n (RoughForm.extendByZero W ω) := by
  rw [isSmoothForm_def]
  intro x
  by_cases hx : (x : M) ∈ U
  · refine (contMDiffAt_mpullback_inclusion_iff h _ ⟨x, hx⟩).mp ?_
    rw [RoughForm.mpullback_inclusion_extendByZero]
    exact hω.contMDiff _
  · refine ((IsSmoothForm.zero (I := I) (M := W) (F := F) (k := k) n).contMDiff x)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hzero x hx] with y hy
    rw [hy]
    rfl

/-- Multiplying a `C^n` form on an open subset `U ≤ W` by a `C^n` function on `W` that vanishes near
every point of `W` outside `U`, and extending by zero, gives a `C^n` form on `W`. -/
theorem IsSmoothForm.extendByZero_smul {U W : Opens M} (h : U ≤ W) {n : WithTop ℕ∞}
    {ω : RoughForm I U F k} (hω : IsSmoothForm I n ω) {g : W → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) n g) (hzero : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, g y = 0) :
    IsSmoothForm I n
      (RoughForm.extendByZero W fun y : U ↦ g (Opens.inclusion h y) • ω y) := by
  exact (hω.fun_smul (hg.comp (contMDiff_inclusion h))).extendByZero h
    (fun x hx ↦ RoughForm.eventually_extendByZero_smul_eq_zero h ω (hzero x hx))

end TauCeti
