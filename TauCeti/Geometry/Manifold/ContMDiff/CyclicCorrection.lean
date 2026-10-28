/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.BirkhoffSum.Cyclic
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Regularity of cyclic translation normalization

The explicit weighted orbit correction `TauCeti.cyclicCorrection` is `C^n` whenever the base
map and translation section are `C^n`. Thus the orbit-sum criterion for normalizing a cyclic
translation to an invariant section is sufficient with the same regularity as the input.
For complex manifolds and `n = ω` this gives a holomorphic correction; for `𝕜 = ℝ` it gives
smooth corrections. No compactness or finite-dimensionality of the target space is needed.

This is the regularity part of the finite cyclic averaging calculation used for logarithmic
transforms; see Barth--Hulek--Peters--Van de Ven, *Compact Complex Surfaces*, second edition,
Chapter V, section on logarithmic transformations.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ∞ω}

/-- The weighted cyclic orbit correction preserves `C^n` regularity, including complex
analytic regularity when `𝕜 = ℂ` and `n = ω`. -/
theorem contMDiff_cyclicCorrection {r : X → X} {b : X → E}
    (hr : ContMDiff I I n r) (hb : ContMDiff I 𝓘(𝕜, E) n b) (m : ℕ) :
    ContMDiff I 𝓘(𝕜, E) n (cyclicCorrection 𝕜 r b m) := by
  rw [funext (cyclicCorrection_apply r b m)]
  simp_rw [← Nat.cast_smul_eq_nsmul 𝕜]
  exact (contMDiff_const (I' := 𝓘(𝕜))).smul
    (ContMDiff.sum fun j _ ↦ (contMDiff_const (I' := 𝓘(𝕜))).smul (hb.comp (hr.iterate j)))

/-- A `C^n` cyclic translation section can be normalized to an invariant section by a `C^n`
change of fibre coordinates exactly when its orbit sum is `m` times the prescribed invariant
section `a`. -/
theorem exists_contMDiff_add_apply_sub_eq_iff {r : X → X} {b a : X → E} {m : ℕ}
    (hr : ContMDiff I I n r) (hb : ContMDiff I 𝓘(𝕜, E) n b)
    (hperiod : r^[m] = id) (hm : (m : 𝕜) ≠ 0) (ha : a ∘ r = a) :
    (∃ c : X → E, ContMDiff I 𝓘(𝕜, E) n c ∧ ∀ x, b x + c (r x) - c x = a x) ↔
      ∀ x, birkhoffSum r b m x = m • a x := by
  constructor
  · rintro ⟨c, -, hc⟩
    exact (exists_add_apply_sub_eq_iff (𝕜 := 𝕜) r b a hperiod hm ha).mp ⟨c, hc⟩
  · intro hsum
    exact ⟨cyclicCorrection 𝕜 r b m, contMDiff_cyclicCorrection hr hb m,
      add_cyclicCorrection_apply_sub r b a hperiod hm hsum⟩

end TauCeti
