/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Sylvester equations for partial linear maps

The domain-aware Sylvester equation `A X - X B = C` for partially defined
operators `A` and `B` and bounded maps `X` and `C`.

The equation requires `X` to carry the domain of `B` into that of `A`.
It specializes the ordinary bounded Sylvester equation and is preserved by
addition, negation, subtraction, and scalar multiplication of solutions and
right-hand sides.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean`.
-/

public section

namespace LinearPMap

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A domain-aware Sylvester equation `A X - X B = C`: `X` maps the domain
of `B` into the domain of `A`, and the operator identity holds there. -/
structure SylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X C : F →L[𝕜] E) : Prop where
  /-- The bounded unknown carries the domain of `B` into that of `A`. -/
  mapsTo_domain : ∀ x : B.domain, X (x : F) ∈ A.domain
  /-- The Sylvester identity on vectors in the domain of `B`. -/
  equation : ∀ x : B.domain,
    A ⟨X (x : F), mapsTo_domain x⟩ - X (B x) = C (x : F)

namespace SylvesterEquation

/-- An ordinary bounded Sylvester equation induces an equation between the
corresponding full-domain partial operators. -/
theorem ofBounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    SylvesterEquation
      (A.toLinearMap.toPMap ⊤) (B.toLinearMap.toPMap ⊤) X C := by
  refine { mapsTo_domain := ?_, equation := ?_ }
  · intro x
    simp
  · intro x
    have hx := congrArg (fun T : F →L[𝕜] E => T (x : F)) hEq
    -- A continuous linear map embedded as `toPMap ⊤` has the full domain.
    -- Evaluating that partial map on its domain subtype is definitionally
    -- the original bounded-map application; `change` exposes this equality.
    change A (X (x : F)) - X (B (x : F)) = C (x : F)
    simpa only [_root_.sub_apply, ContinuousLinearMap.comp_apply] using hx

/-- The domain-aware equation for full-domain partial operators is equivalent
to the ordinary bounded Sylvester equation. -/
@[simp] theorem ofBounded_iff
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E} :
    SylvesterEquation (A.toLinearMap.toPMap ⊤) (B.toLinearMap.toPMap ⊤) X C ↔
      A ∘L X - X ∘L B = C := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    have hx : (x : F) ∈ (B.toLinearMap.toPMap ⊤).domain := by simp
    have hpoint : A (X x) - X (B x) = C x := by
      -- Full-domain `toPMap ⊤` applications reduce definitionally to the
      -- bounded maps, just as in `ofBounded`.
      exact h.equation ⟨x, hx⟩
    simpa only [_root_.sub_apply, ContinuousLinearMap.comp_apply] using hpoint
  · exact ofBounded

/-- The zero map solves the homogeneous domain-aware equation. -/
theorem zero (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    SylvesterEquation A B 0 0 := by
  refine ⟨?_, ?_⟩
  · intro x
    simp
  · intro x
    -- The zero bounded map evaluates to zero. The zero vector supplied with
    -- the domain-transport proof is definitionally `0` in `A.domain`.
    change A (0 : A.domain) - 0 = (0 : E)
    simp

/-- Domain-aware Sylvester equations are preserved by addition. -/
theorem add {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X + Y) (C + D) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    have hxY : Y (x : F) ∈ A.domain := hY.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    let uY : A.domain := ⟨Y (x : F), hxY⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    have hEqY : A uY - Y (B x) = D (x : F) := by
      simpa [uY] using hY.equation x
    -- Addition of continuous maps is pointwise. The domain member made from
    -- `hX.mapsTo_domain` and `hY.mapsTo_domain` is definitionally `uX + uY`.
    change A (uX + uY) - (X (B x) + Y (B x)) = C (x : F) + D (x : F)
    calc
      A (uX + uY) - (X (B x) + Y (B x)) =
          (A uX - X (B x)) + (A uY - Y (B x)) := by
            rw [_root_.LinearPMap.map_add A uX uY]
            abel
      _ = C (x : F) + D (x : F) := by rw [hEqX, hEqY]

/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) :
    SylvesterEquation A B (-X) (-C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.neg_mem (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- Negating the continuous maps is pointwise, and the domain witness
    -- supplied by `neg_mem` is definitionally the subtype vector `-uX`.
    change A (-uX) - (-X (B x)) = -C (x : F)
    calc
      A (-uX) - (-X (B x)) = -(A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_neg A uX]
        abel
      _ = -C (x : F) := by rw [hEqX]

/-- Domain-aware Sylvester equations are preserved by subtraction. -/
theorem sub {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X - Y) (C - D) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

/-- Domain-aware Sylvester equations are preserved by scalar multiplication. -/
theorem smul {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) (c : 𝕜) :
    SylvesterEquation A B (c • X) (c • C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.smul_mem c (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- Scalar multiplication of continuous maps is pointwise, and the domain
    -- member supplied by `smul_mem` is definitionally the vector `c • uX`.
    change A (c • uX) - c • X (B x) = c • C (x : F)
    calc
      A (c • uX) - c • X (B x) = c • (A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_smul A c uX, smul_sub]
      _ = c • C (x : F) := by rw [hEqX]

end SylvesterEquation
end LinearPMap
