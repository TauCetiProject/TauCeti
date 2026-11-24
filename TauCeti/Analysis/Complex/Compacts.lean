/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Compact sets of the real line as compact sets of `ℂ`

A compact set `K` of the real line is a compact set `TopologicalSpace.Compacts.ofReal K` of the
complex plane, its image under the inclusion `ℝ → ℂ`. Its points are the complex numbers with
imaginary part `0` and real part in `K` (`TopologicalSpace.Compacts.mem_ofReal_iff`).
-/

public section

namespace TopologicalSpace.Compacts

/-- A compact set of the real line, as a compact set of `ℂ`. -/
noncomputable def ofReal (K : Compacts ℝ) : Compacts ℂ :=
  K.map ((↑) : ℝ → ℂ) Complex.continuous_ofReal

@[simp, norm_cast]
theorem coe_ofReal (K : Compacts ℝ) : (K.ofReal : Set ℂ) = ((↑) : ℝ → ℂ) '' K :=
  coe_map _ K

/-- A complex number lies in the image of a compact set `K` of the real line exactly when it is
real with real part in `K`. -/
@[simp]
theorem mem_ofReal_iff {K : Compacts ℝ} {z : ℂ} : z ∈ K.ofReal ↔ z.im = 0 ∧ z.re ∈ K := by
  rw [← SetLike.mem_coe, coe_ofReal]
  refine ⟨?_, fun ⟨him, hre⟩ => ⟨z.re, hre, Complex.ext rfl him.symm⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨Complex.ofReal_im x, hx⟩

end TopologicalSpace.Compacts
