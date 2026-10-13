/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Support of manifold differential forms

A rough form has dependent tangent-space fibers. Its topological support is the closure of
the points where its value is nonzero. Scalar localization restricts this support to the
intersection of the scalar support and the form support.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The topological support of a rough differential form, closed by convention. -/
def tsupport (φ : RoughForm I M F k) : Set M := closure {x | φ x ≠ 0}

/-- The topological support is the closure of the nonzero values in the actual tangent fibers. -/
theorem tsupport_def (φ : RoughForm I M F k) :
    φ.tsupport = closure {x | φ x ≠ 0} := (rfl)

/-- Every nonzero value belongs to the form's topological support. -/
theorem mem_tsupport_of_ne_zero {φ : RoughForm I M F k} {x : M} (hx : φ x ≠ 0) :
    x ∈ φ.tsupport := subset_closure hx

/-- A form vanishes outside its topological support. -/
theorem eq_zero_of_notMem_tsupport {φ : RoughForm I M F k} {x : M} (hx : x ∉ φ.tsupport) :
    φ x = 0 := by
  by_contra h
  exact hx (mem_tsupport_of_ne_zero h)

/-- Form supports are closed, without a continuity hypothesis. -/
theorem isClosed_tsupport (φ : RoughForm I M F k) : IsClosed φ.tsupport := isClosed_closure

@[simp]
theorem tsupport_zero : (0 : RoughForm I M F k).tsupport = ∅ := by
  simp [tsupport]

/-- Scalar localization cannot enlarge the form support. -/
theorem tsupport_fun_smul_subset_right (f : M → ℝ) (φ : RoughForm I M F k) :
    tsupport (fun x ↦ f x • φ x : RoughForm I M F k) ⊆ φ.tsupport := by
  apply closure_mono
  intro x hx
  exact fun h ↦ hx (by simp [h])

/-- Scalar localization cannot enlarge the scalar support. -/
theorem tsupport_fun_smul_subset_left (f : M → ℝ) (φ : RoughForm I M F k) :
    tsupport (fun x ↦ f x • φ x : RoughForm I M F k) ⊆ _root_.tsupport f := by
  apply closure_mono
  intro x hx
  exact fun h ↦ hx (by simp [h])

/-- Compact support is preserved by arbitrary scalar localization. -/
theorem isCompact_tsupport_fun_smul {φ : RoughForm I M F k}
    (hc : IsCompact φ.tsupport) (f : M → ℝ) :
    IsCompact (tsupport (fun x ↦ f x • φ x : RoughForm I M F k)) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fun_smul_subset_right f φ)

end TauCeti.RoughForm
