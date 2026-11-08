/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Pullback of forms along local diffeomorphisms

Pullback along a map `f` only sees the value of a form at `f x` through the derivative of `f`
at `x`. When that derivative is surjective, the pullback at `x` therefore determines the form at
`f x` (`TauCeti.mpullback_apply_eq_mpullback_apply_iff`), so pullback along a surjective local
diffeomorphism is injective (`IsLocalDiffeomorph.mpullback_injective`).

Regularity transfers in both directions as well. Near `f x`, a form `ω` is the pullback of
`f^* ω` along a local inverse of `f`, so `ω` is `C^m` near `f x` exactly when `f^* ω` is `C^m`
near `x`, for a `C^n` local diffeomorphism with `m + 1 ≤ n`
(`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`). For a surjective local diffeomorphism
this gives `IsLocalDiffeomorph.isSmoothForm_mpullback_iff`, and, since pullback commutes with the
exterior derivative, a smooth form is closed exactly when its pullback is
(`IsLocalDiffeomorph.isClosed_mpullback_iff`).

These facts are what let forms on a covering space whose deck group acts transitively on each
fibre descend to the base when they are invariant under the deck group. Given a family of
self-maps of the source lying over `f` and transitive on its fibres, a form invariant under the
family is basic for `f` (`IsLocalDiffeomorph.isBasic_of_mpullback_eq`), so it is the pullback of
its descent `TauCeti.RoughForm.descendedForm`. Hence a form is a pullback along `f` exactly
when it is invariant under the family (`IsLocalDiffeomorph.exists_mpullback_eq_iff`). For a
surjective smooth local diffeomorphism the descended form of a smooth form is smooth
(`IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`).

A pullback identity between coordinate expressions in a chart is carried to the manifold by
conjugating with the chart
(`TauCeti.RoughForm.exists_partialDiffeomorph_mpullback_eq_of_inChartAt`).

## Main results

* `IsLocalDiffeomorph.mpullback_injective`: pullback along a surjective local diffeomorphism is
  injective.
* `IsLocalDiffeomorphAt.mpullback_apply_eq_zero_iff`: a pullback along a local diffeomorphism
  vanishes at a point exactly when the form vanishes at its image.
* `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`,
  `IsLocalDiffeomorph.isSmoothForm_mpullback_iff`: a form is `C^m` exactly when its pullback
  along a (surjective) `C^n` local diffeomorphism is, for `m + 1 ≤ n`.
* `IsLocalDiffeomorph.isClosed_mpullback_iff`: a smooth form is closed exactly when its pullback
  along a surjective smooth local diffeomorphism is.
* `IsLocalDiffeomorph.isBasic_of_mpullback_eq`: a form invariant under a family of maps over a
  local diffeomorphism that is transitive on its fibres is basic for it.
* `IsLocalDiffeomorph.exists_mpullback_eq_iff`,
  `IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff`: a (smooth) form is the pullback of a
  (smooth) form along a local diffeomorphism exactly when it is invariant under a family of maps
  over it that is transitive on its fibres.
* `TauCeti.RoughForm.exists_partialDiffeomorph_mpullback_eq_of_inChartAt`: a partial
  diffeomorphism of the model space relating the coordinate expressions of two forms in a chart
  gives a partial diffeomorphism of the manifold relating the forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {m n : WithTop ℕ∞} {f g : M → M'} {x : M}

open TauCeti

/-- Pullback along a surjective `C^n` local diffeomorphism, `n ≠ 0`, is injective on rough
forms. -/
theorem IsLocalDiffeomorph.mpullback_injective (hf : IsLocalDiffeomorph I I' n f) (hn : n ≠ 0)
    (hsurj : Function.Surjective f) :
    Function.Injective (mpullback I I' f : RoughForm I' M' F k → RoughForm I M F k) :=
  mpullback_injective_of_surjective hsurj fun x ↦ (hf.isInvertible_mfderiv hn x).surjective

/-- A form pulled back along a `C^n` local diffeomorphism at `x`, `n ≠ 0`, vanishes at `x` exactly
when the form vanishes at `f x`. -/
theorem IsLocalDiffeomorphAt.mpullback_apply_eq_zero_iff (hf : IsLocalDiffeomorphAt I I' n f x)
    (hn : n ≠ 0) {ω : RoughForm I' M' F k} : mpullback I I' f ω x = 0 ↔ ω (f x) = 0 := by
  simpa only [mpullback_zero, Pi.zero_apply] using
    mpullback_apply_eq_mpullback_apply_iff (ω := ω) (η := 0) (hf.isInvertible_mfderiv hn).surjective

section Descent

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Let `f` be a `C^n` local diffeomorphism, `n ≠ 0`, and let `σ` be a family of differentiable
self-maps of `M` over `f` (`f ∘ σ i = f`) that is transitive on the fibres of `f`. Then a form
invariant under every `σ i` is basic for `f`. -/
theorem IsLocalDiffeomorph.isBasic_of_mpullback_eq {ι : Type*} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) {σ : ι → M → M} (hσ : ∀ i, MDifferentiable I I (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : RoughForm I M V k} (hα : ∀ i, mpullback I I (σ i) α = α) : RoughForm.IsBasic I' f α := by
  refine RoughForm.isBasic_iff.mpr fun x y hxy v w hvw ↦ ?_
  have hinj (z : M) := (hf.isInvertible_mfderiv hn z).injective
  -- `x` is `y` or `σ i y` for some `i`; `tangentSpaceCast` is the identity of the model space.
  rcases hσf y x hxy.symm with rfl | ⟨i, rfl⟩
  · exact congrArg _ (funext fun j ↦ hinj _ (hvw j))
  · rw [← congrFun (hα i) y, mpullback_apply]
    refine congrArg _ (funext fun j ↦ hinj _ ?_)
    -- By the chain rule, `df_y` factors through the derivative of `σ i`.
    have hcomp := mfderiv_comp y (hf.mdifferentiable hn (σ i y)) (hσ i y)
    rw [hfσ i] at hcomp
    exact (hvw j).trans (congrArg (· (w j)) hcomp)

/-- **Descent of forms along a local diffeomorphism.** Let `f` be a `C^n` local diffeomorphism,
`n ≠ 0`, and let `σ` be a family of differentiable self-maps of `M` over `f` (`f ∘ σ i = f`) that
is transitive on the fibres of `f`: two points with the same image are equal or are related by
some `σ i`. Then a form on `M` is the pullback of a form on `M'` exactly when it is invariant
under every `σ i`. For a covering map whose deck transformations act transitively on each fibre,
one can take the `σ i` to be the deck transformations. -/
theorem IsLocalDiffeomorph.exists_mpullback_eq_iff {ι : Type*} (hf : IsLocalDiffeomorph I I' n f)
    (hn : n ≠ 0) {σ : ι → M → M} (hσ : ∀ i, MDifferentiable I I (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : RoughForm I M V k} :
    (∃ ω : RoughForm I' M' V k, mpullback I I' f ω = α) ↔ ∀ i, mpullback I I (σ i) α = α := by
  refine ⟨?_, fun hα ↦ (RoughForm.exists_mpullback_eq_iff_isBasic fun x ↦
    .of_isInvertible (hf.isInvertible_mfderiv hn x)).mpr
      (hf.isBasic_of_mpullback_eq hn hσ hfσ hσf hα)⟩
  rintro ⟨ω, rfl⟩ i
  rw [← mpullback_comp (hσ i) (hf.mdifferentiable hn), hfσ i]

end Descent

/-- For a `C^n` local diffeomorphism `f` at `x` and `m + 1 ≤ n`, a form is a `C^m` section near
`f x` exactly when its pullback along `f` is a `C^m` section near `x`. -/
theorem IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hf : IsLocalDiffeomorphAt I I' n f x) (hmn : m + 1 ≤ n)
    {ω : RoughForm I' M' F k} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (mpullback I I' f ω y)) x ↔
      ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
        (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) (f x) :=
  -- Near `f x`, the form `ω` is the pullback of `f^* ω` along the local inverse of `f`.
  contMDiffAt_mpullback_form_iff_of_section hf.localInverse_open_source hf.localInverse_mem_source
    (hf.localInverse_left_inv hf.localInverse_mem_target) hf.contMDiffOn_localInverse
    (fun _ hy ↦ hf.localInverse_right_inv hy) hf.contMDiffAt hmn

/-- For a surjective `C^n` local diffeomorphism `f` and `m + 1 ≤ n`, a form is `C^m` exactly when
its pullback along `f` is. -/
theorem IsLocalDiffeomorph.isSmoothForm_mpullback_iff [IsManifold I 1 M] [IsManifold I' 1 M']
    (hf : IsLocalDiffeomorph I I' n f) (hsurj : Function.Surjective f) (hmn : m + 1 ≤ n)
    {ω : RoughForm I' M' F k} :
    IsSmoothForm I m (mpullback I I' f ω) ↔ IsSmoothForm I' m ω := by
  simp only [isSmoothForm_def]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ((hf x).contMDiffAt_mpullback_form_iff hmn).mpr (h (f x))⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hf x).contMDiffAt_mpullback_form_iff hmn).mp (h x)

open scoped ContDiff in
/-- **Descent of smooth forms along a surjective local diffeomorphism.** For a surjective smooth
local diffeomorphism `f` and a family of smooth self-maps `σ i` of `M` over `f` that is transitive
on the fibres of `f`, a smooth form on `M` is the pullback of a smooth form on `M'` exactly when it
is invariant under every `σ i`. -/
theorem IsLocalDiffeomorph.exists_smoothForm_mpullback_eq_iff [IsManifold I ∞ M]
    [IsManifold I' ∞ M'] {ι : Type*} (hf : IsLocalDiffeomorph I I' ∞ f)
    (hsurj : Function.Surjective f) {σ : ι → M → M} (hσ : ∀ i, ContMDiff I I ∞ (σ i))
    (hfσ : ∀ i, f ∘ σ i = f) (hσf : ∀ x y, f x = f y → x = y ∨ ∃ i, σ i x = y)
    {α : SmoothForm I M F k} :
    (∃ β : SmoothForm I' M' F k, SmoothForm.mpullback f hf.contMDiff β = α) ↔
      ∀ i, SmoothForm.mpullback (σ i) (hσ i) α = α := by
  simp only [Subtype.ext_iff, SmoothForm.coe_mpullback]
  rw [← hf.exists_mpullback_eq_iff (by simp) (fun i ↦ (hσ i).mdifferentiable (by simp)) hfσ hσf]
  refine ⟨fun ⟨β, hβ⟩ ↦ ⟨β.1, hβ⟩, fun ⟨β, hβ⟩ ↦ ⟨⟨β, ?_⟩, hβ⟩⟩
  -- The descended rough form is smooth because its pullback `α` is.
  exact IsSmoothForm.mem_smoothBundleForms
    ((hf.isSmoothForm_mpullback_iff hsurj (by simp)).mp (hβ ▸ α.isSmoothForm))

open scoped ContDiff in
/-- For a surjective smooth local diffeomorphism `f`, a smooth form is closed exactly when its
pullback along `f` is. -/
theorem IsLocalDiffeomorph.isClosed_mpullback_iff [IsManifold I 2 M] [IsManifold I' 2 M']
    (hf : IsLocalDiffeomorph I I' ∞ f) (hsurj : Function.Surjective f)
    {φ : SmoothForm I' M' F k} : (SmoothForm.mpullback f hf.contMDiff φ).IsClosed ↔ φ.IsClosed :=
  SmoothForm.isClosed_mpullback_iff_of_surjective hf.contMDiff hsurj
    fun x ↦ (hf.isInvertible_mfderiv (by simp) x).surjective

namespace TauCeti.RoughForm

/-- **Transport through a chart.** Let `φ` be the preferred chart at `x₀`, and let `Φf` be a `C^n`
partial diffeomorphism of the model space, `1 ≤ n`, which pulls the coordinate expression of `ω₁`
in `φ` back to that of `ω₀` on its source. Then `φ⁻¹ ∘ Φf ∘ φ`, defined where `φ` and `Φf` take
values in the interior of the chart target, is a `C^n` partial diffeomorphism of `M` which pulls
`ω₁` back to `ω₀` on its source. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_inChartAt [IsManifold I n M] (hn : 1 ≤ n)
    {ω₀ ω₁ : RoughForm I M F k} (x₀ : M) (Φf : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n)
    (hpb : ∀ z ∈ Φf.source,
      (ω₁.inChartAt x₀ (Φf z)).compContinuousLinearMap (fderiv ℝ Φf z) = ω₀.inChartAt x₀ z) :
    ∃ Φ : PartialDiffeomorph I I M M n, (∀ x, x ∈ Φ.source ↔
        (x ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ x ∈ interior (extChartAt I x₀).target) ∧
          extChartAt I x₀ x ∈ Φf.source ∧
            Φf (extChartAt I x₀ x) ∈ interior (extChartAt I x₀).target) ∧
      (∀ x, Φ x = (extChartAt I x₀).symm (Φf (extChartAt I x₀ x))) ∧
      ∀ x ∈ Φ.source, mpullback I I Φ ω₁ x = ω₀ x := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  set φ := extChartAt I x₀ with hφ
  let e₀ := extChartPartialDiffeomorph I n x₀
  let Φ : PartialDiffeomorph I I M M n := e₀.trans (Φf.trans e₀.symm)
  have hΦeq : Φ.toPartialEquiv =
      e₀.toPartialEquiv.trans (Φf.toPartialEquiv.trans e₀.toPartialEquiv.symm) := by
    simp only [Φ, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv]
  have hΦ (x : M) : Φ x = φ.symm (Φf (φ x)) := by
    rw [hΦeq]
    simp [e₀, hφ]
  have hΦsrc (x : M) : x ∈ Φ.source ↔ (x ∈ φ.source ∧ φ x ∈ interior φ.target) ∧
      φ x ∈ Φf.source ∧ Φf (φ x) ∈ interior φ.target := by
    rw [hΦeq]
    simp [e₀, hφ, extChartPartialDiffeomorph_source]
  refine ⟨Φ, hΦsrc, hΦ, fun x hx ↦ ?_⟩
  obtain ⟨⟨hxs, -⟩, hxf, hfW⟩ := (hΦsrc x).1 hx
  have hΦxs : Φ x ∈ φ.source := hΦ x ▸ φ.map_target (interior_subset hfW)
  have hφΦ : φ (Φ x) = Φf (φ x) := by rw [hΦ, φ.right_inv (interior_subset hfW)]
  have hφd (z : M) (hz : z ∈ φ.source) : MDifferentiableAt I 𝓘(ℝ, E) φ z :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := I)])
  -- The chain rule for `φ ∘ Φ = Φf ∘ φ`, valid near `x`.
  have hloc : φ ∘ Φ =ᶠ[𝓝 x] Φf ∘ φ :=
    eventually_of_mem (Φ.open_source.mem_nhds hx) fun x' hx' ↦ by
      obtain ⟨-, -, hW'⟩ := (hΦsrc x').1 hx'
      rw [Function.comp_apply, hΦ, φ.right_inv (interior_subset hW'), Function.comp_apply]
  have hchain (w : TangentSpace I x) :
      mvfderiv I φ (Φ x) (mfderiv I I Φ x w) = fderiv ℝ Φf (φ x) (mvfderiv I φ x w) := by
    rw [← mvfderiv_comp_apply x (hφd _ hΦxs) (Φ.mdifferentiableAt hn0 hx),
      hloc.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt
        (mdifferentiableAt_iff_differentiableAt.1 (Φf.mdifferentiableAt hn0 hxf))
        (hφd x hxs)]
  ext v
  have h := congrArg (fun A : E [⋀^Fin k]→L[ℝ] F ↦ A (fun j ↦ mvfderiv I φ x (v j)))
    (hpb (φ x) hxf)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] at h
  rw [mpullback_apply, apply_eq_inChartAt_mvfderiv ω₁ hΦxs, apply_eq_inChartAt_mvfderiv ω₀ hxs,
    ← hφ, hφΦ]
  simp only [hchain]
  exact h

end TauCeti.RoughForm
