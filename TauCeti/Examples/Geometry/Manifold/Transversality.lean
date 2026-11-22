/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Transversality.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.Incidence.FiniteDimensional

/-!
# Examples: transversality of a map to a map

These examples test `TauCeti.IsTransverseAt` on maps between real lines, with the point `Unit`,
over the zero-dimensional model `𝓘(ℝ, Unit)`, as the source of the constant map `0`:

* the constant map `1` is transverse to `0` at every point, vacuously, although its differential
  is not surjective, so a definition asking for a surjective differential would reject it;
* the zero map is transverse to the identity at every point, so the differential of the second
  map counts;
* `t ↦ t ^ 2` is transverse to `0` exactly away from `0`, so the predicate is not always true;
* the slices of the family `(t, p) ↦ t ^ 2 + p` are transverse to `0` at every point exactly when
  `p ≠ 0`, in agreement with regular incidence parameters;
* translating both maps by `1` does not change transversality.
-/

public section

open Function Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti.TransversalityExamples

/-- `t ↦ t ^ 2` is transverse to the constant map `0` at `x` exactly when `x ≠ 0`. -/
theorem isTransverseAt_sq_zero_iff (x : ℝ) :
    IsTransverseAt 𝓘(ℝ) 𝓘(ℝ, Unit) (fun t : ℝ ↦ t ^ 2) (fun _ : Unit ↦ (0 : ℝ)) x ↔ x ≠ 0 := by
  rw [isTransverseAt_modelWithCornersSelf_iff]
  refine ⟨?_, fun hx y hy ↦ (hx (pow_eq_zero_iff two_ne_zero |>.1 hy)).elim⟩
  rintro h rfl
  have hd : fderiv ℝ (fun t : ℝ ↦ t ^ 2) 0 = 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).hasFDerivAt.fderiv
  obtain ⟨⟨u, v⟩, huv⟩ := h () (by simp) 1
  simp [hd] at huv

-- The constant `1` misses the constant `0`, so it is transverse to it at every point.
example (x : ℝ) :
    IsTransverseAt 𝓘(ℝ) 𝓘(ℝ, Unit) (fun _ : ℝ ↦ (1 : ℝ)) (fun _ : Unit ↦ (0 : ℝ)) x :=
  isTransverseAt_of_notMem_range (by simp)

-- The differential of the constant `1` is not surjective.
example (x : ℝ) : ¬Surjective (mvfderiv 𝓘(ℝ) (fun _ : ℝ ↦ (1 : ℝ)) x) := by
  rw [mvfderiv_const]
  intro h
  obtain ⟨u, hu⟩ := h 1
  simp at hu

-- The zero map is transverse to the identity at every point.
example (x : ℝ) : IsTransverseAt 𝓘(ℝ) 𝓘(ℝ) (fun _ : ℝ ↦ (0 : ℝ)) id x := by
  rw [isTransverseAt_modelWithCornersSelf_iff]
  exact fun _ _ v ↦ ⟨(0, -v), by simp⟩

-- The slices of `(t, p) ↦ t ^ 2 + p` are transverse to `0` everywhere exactly when `p ≠ 0`.
example (p : ℝ) :
    (∀ x, IsTransverseAt 𝓘(ℝ) 𝓘(ℝ, Unit) (fun t : ℝ ↦ t ^ 2 + p) (fun _ : Unit ↦ (0 : ℝ)) x) ↔
      p ≠ 0 := by
  have hF : Differentiable ℝ fun z : ℝ × ℝ ↦ z.1 ^ 2 + z.2 := by fun_prop
  rw [← isRegularIncidenceParameter_sq_add_zero_iff,
    isRegularIncidenceParameter_iff_forall_isTransverseAt (fun x _ _ ↦ hF (x, p))
      fun _ _ _ ↦ differentiableAt_const _]

-- Translating both maps by `1`, an affine isomorphism of `ℝ`, does not change transversality.
example (x : ℝ) :
    IsTransverseAt 𝓘(ℝ) 𝓘(ℝ, Unit)
      (Diffeomorph.smulAdd ∞ (1 : ℝ) 1 one_ne_zero ∘ fun t : ℝ ↦ t ^ 2)
      (Diffeomorph.smulAdd ∞ (1 : ℝ) 1 one_ne_zero ∘ fun _ : Unit ↦ (0 : ℝ)) x ↔ x ≠ 0 := by
  rw [Diffeomorph.isTransverseAt_comp_iff _ (by simp), isTransverseAt_sq_zero_iff]

end TauCeti.TransversalityExamples
