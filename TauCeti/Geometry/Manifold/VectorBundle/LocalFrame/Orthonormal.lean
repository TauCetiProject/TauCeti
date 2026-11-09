/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Coefficients in orthonormal local frames

The coefficient functionals of an orthonormal local frame are its metric duals. This lets
local-frame connection and curvature coefficients be read as inner products.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace IsLocalFrameOn

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace 𝕜 (V x)]
  [FiberBundle F V]
  {ι : Type*} [Finite ι] {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}
  (hs : IsLocalFrameOn I F n s u) {x : M}

/-- The coefficients of an orthonormal local frame are its metric duals. Only orthonormality
at the point is needed. -/
theorem coeff_eq_inner (hx : x ∈ u) (ho : Orthonormal 𝕜 (fun i ↦ s i x))
    (i : ι) (v : V x) : hs.coeff i x v = inner 𝕜 (s i x) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hexp : v = ∑ j, hs.coeff j x v • s j x := by
    simpa only [FiberBundle.extend_apply_self] using
      hs.coeff_sum_eq (FiberBundle.extend F v) hx
  have h := ho.inner_right_fintype (fun j ↦ hs.coeff j x v) i
  rw [← hexp] at h
  exact h.symm

end IsLocalFrameOn
