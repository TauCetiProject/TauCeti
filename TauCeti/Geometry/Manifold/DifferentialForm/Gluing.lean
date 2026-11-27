/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartialDiffeomorph
public import TauCeti.Geometry.Manifold.Gluing.PartialDiffeomorph

/-!
# Gluing differential forms along a partial diffeomorphism

Let `Φ : Y ⇀ X` be a partial diffeomorphism between manifolds modelled on the same space, from an
open subset of `Y` onto an open subset of `X`, and let `Z` be the gluing of `X` and `Y` along `Φ`
(`OpenPartialHomeomorph.glueData`), with its canonical open embeddings `ι_X : X → Z` and
`ι_Y : Y → Z`. Give `Z` a manifold structure for which `ι_X` and `ι_Y` are local diffeomorphisms,
for instance the glued atlas (`PartialDiffeomorph.isLocalDiffeomorph_glueInl`,
`PartialDiffeomorph.isLocalDiffeomorph_glueInr`).

A form `α` on `X` and a form `β` on `Y` that agree on the overlap, `Φ^* α = β` on the source of
`Φ`, glue to a unique form on `Z` restricting to `α` on `X` and to `β` on `Y`
(`PartialDiffeomorph.glueRoughForm`). At a point of `ι_X(X)` it is `α` read through the inverse of
the derivative of `ι_X` (`TauCeti.RoughForm.descendedForm`), and elsewhere it is `β` read through
the inverse of the derivative of `ι_Y`. Its pullbacks along the two embeddings are `α` and `β`
(`PartialDiffeomorph.mpullback_glueInl_glueRoughForm`,
`PartialDiffeomorph.mpullback_glueInr_glueRoughForm`), and a form on `Z` is determined by these
two pullbacks (`PartialDiffeomorph.roughForm_ext`). Smoothness is local, and `ι_X` and `ι_Y` are
local diffeomorphisms, so the glued form of two smooth forms is smooth
(`PartialDiffeomorph.glueForm`). It commutes with the exterior derivative
(`PartialDiffeomorph.mextDerivₗ_glueForm`), and it is closed exactly when both forms are
(`PartialDiffeomorph.isClosed_glueForm_iff`).

The intended application is the completion `W ∪ ([1, ∞) × ∂W)` of a Liouville domain `W`,
glued from the interior of `W` and the cylinder `ℝ × ∂W` along the Liouville flow of the boundary,
once the two are modelled on the same space. In the coordinate `t = log r`, the Liouville flow
pulls the primitive `λ` of the domain back to the symplectization form `eᵗ λ|_{∂W}`
(`TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`), so `λ` and `eᵗ λ|_{∂W}` glue to the
primitive of the completion, which is `r λ|_{∂W}` on its cylindrical end.

## Main definitions

* `PartialDiffeomorph.glueRoughForm Φ α β`: the form on the gluing along `Φ` restricting to `α`
  and to `β`.
* `PartialDiffeomorph.glueForm Φ α β`: the same for smooth forms, as a smooth form.

## Main results

* `PartialDiffeomorph.mpullback_glueInl_glueRoughForm`,
  `PartialDiffeomorph.mpullback_glueInr_glueRoughForm`: the glued form restricts to `α` and to
  `β`.
* `PartialDiffeomorph.mpullback_mpullback_glueInl_apply`: the restrictions of a form on the
  gluing agree on the overlap.
* `PartialDiffeomorph.roughForm_ext`, `PartialDiffeomorph.eq_glueRoughForm_iff`,
  `PartialDiffeomorph.eq_glueForm_iff`: the glued form is the unique form with these
  restrictions.
* `PartialDiffeomorph.isSmoothForm_glueRoughForm`: forms of class `C^m` glue to a form of class
  `C^m`.
* `PartialDiffeomorph.mextDerivₗ_glueForm`: the exterior derivative of the glued form is the
  glued form of the exterior derivatives.
* `PartialDiffeomorph.isClosed_glueForm_iff`: the glued form is closed exactly when both forms
  are.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 14 (pullbacks of differential forms).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain).
-/

public section

noncomputable section

open Set Filter Function TauCeti OpenPartialHomeomorph
open scoped Manifold Topology ContDiff

namespace PartialDiffeomorph

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [ChartedSpace H Y] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-! ### Rough forms -/

section Rough

variable {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I I Y X n)
  [ChartedSpace H Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]

open scoped Classical in
/-- **The form glued from `α` on `X` and `β` on `Y`** on the gluing of `X` and `Y` along `Φ`: at a
point in the image of `X` it is `α` read through the inverse of the derivative of the canonical map
of `X`, and elsewhere it is `β` read through the inverse of the derivative of the canonical map of
`Y`. When `Φ^* α = β` on the source of `Φ` and the canonical maps are local diffeomorphisms, it is
the unique form restricting to `α` on `X` and to `β` on `Y`
(`PartialDiffeomorph.eq_glueRoughForm_iff`). -/
def glueRoughForm (α : RoughForm I X F k) (β : RoughForm I Y F k) :
    RoughForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k := fun p ↦
  if p ∈ range Φ.toOpenPartialHomeomorph.glueInl then
    RoughForm.descendedForm I I Φ.toOpenPartialHomeomorph.glueInl α p
  else RoughForm.descendedForm I I Φ.toOpenPartialHomeomorph.glueInr β p

variable {Φ}

variable {α : RoughForm I X F k} {β : RoughForm I Y F k}

/-- At a point in the image of `X`, the glued form is `α` read through the inverse of the
derivative of the canonical map of `X`. -/
theorem glueRoughForm_apply_of_mem_range {p : Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued}
    (hp : p ∈ range Φ.toOpenPartialHomeomorph.glueInl) :
    Φ.glueRoughForm α β p = RoughForm.descendedForm I I Φ.toOpenPartialHomeomorph.glueInl α p :=
  ite_eq_left hp

/-- At a point outside the image of `X`, the glued form is `β` read through the inverse of the
derivative of the canonical map of `Y`. -/
theorem glueRoughForm_apply_of_notMem_range
    {p : Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued}
    (hp : p ∉ range Φ.toOpenPartialHomeomorph.glueInl) :
    Φ.glueRoughForm α β p = RoughForm.descendedForm I I Φ.toOpenPartialHomeomorph.glueInr β p :=
  ite_eq_right hp

/-- **The glued form restricts to `α` on `X`.** -/
@[simp]
theorem mpullback_glueInl_glueRoughForm
    (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl) (hn : n ≠ 0) :
    mpullback I I Φ.toOpenPartialHomeomorph.glueInl (Φ.glueRoughForm α β) = α := by
  funext x
  rw [mpullback_apply_congr (glueRoughForm_apply_of_mem_range (mem_range_self x)),
    hl.mpullback_descendedForm_of_injective hn (isOpenEmbedding_glueInl _).injective]

/-- Pullback along the canonical map of `X` followed by `Φ` is pullback along the canonical map of
`Y`, on the source of `Φ`: the two maps agree on this open set. -/
theorem mpullback_mpullback_glueInl_apply
    (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl) (hn : n ≠ 0)
    (σ : RoughForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k) {y : Y}
    (hy : y ∈ Φ.source) :
    mpullback I I Φ (mpullback I I Φ.toOpenPartialHomeomorph.glueInl σ) y =
      mpullback I I Φ.toOpenPartialHomeomorph.glueInr σ y := by
  have heq : (Φ.toOpenPartialHomeomorph.glueInl ∘ Φ : Y → _) =ᶠ[𝓝 y]
      Φ.toOpenPartialHomeomorph.glueInr :=
    eventually_of_mem (Φ.open_source.mem_nhds hy) fun z hz ↦ glueInl_apply_eq_glueInr hz
  rw [← heq.mpullback_eq, mpullback_comp_at (Φ.mdifferentiableAt hn hy)
    ((hl _).mdifferentiableAt hn)]

/-- **The glued form restricts to `β` on `Y`**, when `α` and `β` agree on the overlap. -/
@[simp]
theorem mpullback_glueInr_glueRoughForm
    (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl)
    (hr : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInr) (hn : n ≠ 0)
    (hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α y = β y) :
    mpullback I I Φ.toOpenPartialHomeomorph.glueInr (Φ.glueRoughForm α β) = β := by
  funext y
  by_cases hy : y ∈ Φ.source
  · rw [← mpullback_mpullback_glueInl_apply hl hn _ hy, mpullback_glueInl_glueRoughForm hl hn,
      hαβ y hy]
  · -- Outside the source of `Φ`, the point `ι_Y y` is not in the image of `X`.
    have hyX : Φ.toOpenPartialHomeomorph.glueInr y ∉ range Φ.toOpenPartialHomeomorph.glueInl :=
      fun ⟨x, hx⟩ ↦ hy (glueInl_eq_glueInr_iff.1 hx).1
    rw [mpullback_apply_congr (glueRoughForm_apply_of_notMem_range hyX),
      hr.mpullback_descendedForm_of_injective hn (isOpenEmbedding_glueInr _).injective]

/-- **Forms on the gluing are determined by their restrictions** to `X` and to `Y`. -/
theorem roughForm_ext (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl)
    (hr : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInr) (hn : n ≠ 0)
    {σ σ' : RoughForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k}
    (hX : mpullback I I Φ.toOpenPartialHomeomorph.glueInl σ =
      mpullback I I Φ.toOpenPartialHomeomorph.glueInl σ')
    (hY : mpullback I I Φ.toOpenPartialHomeomorph.glueInr σ =
      mpullback I I Φ.toOpenPartialHomeomorph.glueInr σ') : σ = σ' := by
  funext p
  rcases exists_glueInl_eq_or_exists_glueInr_eq _ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (mpullback_apply_eq_mpullback_apply_iff (hl x |>.isInvertible_mfderiv hn).surjective).1
      (congrFun hX x)
  · exact (mpullback_apply_eq_mpullback_apply_iff (hr y |>.isInvertible_mfderiv hn).surjective).1
      (congrFun hY y)

/-- **The glued form is the unique form restricting to `α` on `X` and to `β` on `Y`.** -/
theorem eq_glueRoughForm_iff (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl)
    (hr : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInr) (hn : n ≠ 0)
    (hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α y = β y)
    {σ : RoughForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k} :
    σ = Φ.glueRoughForm α β ↔ mpullback I I Φ.toOpenPartialHomeomorph.glueInl σ = α ∧
      mpullback I I Φ.toOpenPartialHomeomorph.glueInr σ = β := by
  refine ⟨?_, fun ⟨hX, hY⟩ ↦ roughForm_ext hl hr hn ?_ ?_⟩
  · rintro rfl
    exact ⟨mpullback_glueInl_glueRoughForm hl hn, mpullback_glueInr_glueRoughForm hl hr hn hαβ⟩
  · rw [hX, mpullback_glueInl_glueRoughForm hl hn]
  · rw [hY, mpullback_glueInr_glueRoughForm hl hr hn hαβ]

/-- **Forms of class `C^m` glue to a form of class `C^m`**, for `m + 1 ≤ n`: near each point of
the gluing, the glued form is the pullback of `α` or of `β` along a local inverse of a canonical
map. -/
theorem isSmoothForm_glueRoughForm [IsManifold I 1 X] [IsManifold I 1 Y]
    [IsManifold I 1 Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued] {m : WithTop ℕ∞}
    (hmn : m + 1 ≤ n) (hl : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInl)
    (hr : IsLocalDiffeomorph I I n Φ.toOpenPartialHomeomorph.glueInr)
    (hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α y = β y) (hα : IsSmoothForm I m α)
    (hβ : IsSmoothForm I m β) : IsSmoothForm I m (Φ.glueRoughForm α β) := by
  have hn : n ≠ 0 := ne_bot_of_le_ne_bot (by simp) hmn
  rw [isSmoothForm_def]
  intro p
  rcases exists_glueInl_eq_or_exists_glueInr_eq _ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · refine ((hl x).contMDiffAt_mpullback_form_iff hmn).1 ?_
    rw [mpullback_glueInl_glueRoughForm hl hn]
    exact hα.contMDiff x
  · refine ((hr y).contMDiffAt_mpullback_form_iff hmn).1 ?_
    rw [mpullback_glueInr_glueRoughForm hl hr hn hαβ]
    exact hβ.contMDiff y

end Rough

/-! ### Smooth forms -/

section Smooth

variable (Φ : PartialDiffeomorph I I Y X ∞) [IsManifold I ∞ X] [IsManifold I ∞ Y]

variable [ChartedSpace H Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
  [IsManifold I ∞ Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]

/-- **The smooth form glued from `α` on `X` and `β` on `Y`**, two smooth forms that agree on the
overlap, `Φ^* α = β` on the source of `Φ`: the unique smooth form on the gluing along `Φ`
restricting to `α` on `X` and to `β` on `Y` (`PartialDiffeomorph.eq_glueForm_iff`). -/
def glueForm (hl : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInl)
    (hr : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInr) (α : SmoothForm I X F k)
    (β : SmoothForm I Y F k)
    (hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α.val y = β.val y) :
    SmoothForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k :=
  ⟨Φ.glueRoughForm α.val β.val, IsSmoothForm.mem_smoothBundleForms <|
    isSmoothForm_glueRoughForm (by simp) hl hr hαβ α.isSmoothForm β.isSmoothForm⟩

variable {Φ} {hl : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInl}
  {hr : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInr}
  {α : SmoothForm I X F k} {β : SmoothForm I Y F k}
  {hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α.val y = β.val y}

/-- The underlying rough form of the glued smooth form is the glued rough form. -/
@[simp]
theorem coe_glueForm : (Φ.glueForm hl hr α β hαβ).val = Φ.glueRoughForm α.val β.val := (rfl)

/-- **The glued smooth form restricts to `α` on `X`.** -/
@[simp]
theorem mpullback_glueInl_glueForm :
    SmoothForm.mpullback Φ.toOpenPartialHomeomorph.glueInl hl.contMDiff
      (Φ.glueForm hl hr α β hαβ) = α :=
  Subtype.ext <| (SmoothForm.coe_mpullback _ _ _).trans <|
    mpullback_glueInl_glueRoughForm hl (by simp)

/-- **The glued smooth form restricts to `β` on `Y`.** -/
@[simp]
theorem mpullback_glueInr_glueForm :
    SmoothForm.mpullback Φ.toOpenPartialHomeomorph.glueInr hr.contMDiff
      (Φ.glueForm hl hr α β hαβ) = β :=
  Subtype.ext <| (SmoothForm.coe_mpullback _ _ _).trans <|
    mpullback_glueInr_glueRoughForm hl hr (by simp) hαβ

/-- **The glued smooth form is the unique smooth form restricting to `α` on `X` and to `β` on
`Y`.** -/
theorem eq_glueForm_iff
    {σ : SmoothForm I Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued F k} :
    σ = Φ.glueForm hl hr α β hαβ ↔
      SmoothForm.mpullback Φ.toOpenPartialHomeomorph.glueInl hl.contMDiff σ = α ∧
        SmoothForm.mpullback Φ.toOpenPartialHomeomorph.glueInr hr.contMDiff σ = β := by
  rw [Subtype.ext_iff, coe_glueForm, eq_glueRoughForm_iff hl hr (by simp) hαβ, Subtype.ext_iff,
    Subtype.ext_iff, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]

/-- **The exterior derivative of the glued form is the glued form of the exterior derivatives.** -/
theorem mextDerivₗ_glueForm :
    mextDerivₗ I k (Φ.glueForm hl hr α β hαβ) =
      Φ.glueForm hl hr (mextDerivₗ I k α) (mextDerivₗ I k β)
        fun _ ↦ Φ.mpullback_mextDerivₗ_apply hαβ := by
  rw [eq_glueForm_iff, ← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_glueInl_glueForm, mpullback_glueInr_glueForm]
  exact ⟨rfl, rfl⟩

/-- **The glued form is closed exactly when both forms are closed.** -/
@[simp]
theorem isClosed_glueForm_iff : (Φ.glueForm hl hr α β hαβ).IsClosed ↔ α.IsClosed ∧ β.IsClosed := by
  simp only [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, mextDerivₗ_glueForm]
  rw [eq_comm, eq_glueForm_iff]
  simp [eq_comm]

end Smooth

end PartialDiffeomorph
