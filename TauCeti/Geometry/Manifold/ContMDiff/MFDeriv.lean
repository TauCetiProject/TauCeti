/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Joint regularity of derivatives in vector-space families

For a jointly `C^m` family of maps from a normed space to another normed space, the derivative
in the vector-space variable is jointly `C^n` when `n + 1 ≤ m`. The parameter may range over
a manifold. Iterating, the `i`-th derivative in the vector-space variable loses `i` orders of
joint regularity; the order `i` counts only derivatives in that variable. This supplies derivative
regularity for parameter-dependent coordinate formulas, including the Christoffel symbols of a
metric family and every finite jet of its coefficients.

## Main results

* `ContMDiffAt.fderiv_right`: the derivative in the vector-space variable of a jointly `C^m`
  family is jointly `C^n` when `n + 1 ≤ m`.
* `ContMDiffAt.iteratedFDeriv_right`: the `i`-th iterated derivative in the vector-space variable
  of a jointly `C^n` family is jointly `C^m` when `m + i ≤ n`.

## Formal sources

* Mathlib's `ContMDiffAt.mfderiv` and `ContDiffAt.iteratedFDeriv_right`.
-/

public section

open scoped ContDiff Manifold


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 G H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → F} {m n : ℕ∞ω} {z : P × E}

/-- The derivative in the vector-space variable of a jointly `C^m` family is jointly `C^n`
at a point when `n + 1 ≤ m`. No finite-dimensionality or completeness is required. -/
theorem ContMDiffAt.fderiv_right
    (hg : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) :
    ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, E →L[𝕜] F) n
      (fun q : P × E ↦ fderiv 𝕜 (g q.1) q.2) z := by
  have hfamily : ContMDiffAt ((J.prod 𝓘(𝕜, E)).prod 𝓘(𝕜, E)) 𝓘(𝕜, F) m
      (fun q : (P × E) × E ↦ g q.1.1 q.2) (z, z.2) :=
    hg.comp (z, z.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hfamily.mfderiv (fun q : P × E ↦ g q.1) Prod.snd contMDiffAt_snd hnm
  convert h using 1
  ext q : 1
  -- `mfderiv` uses the normed-space instances on tangent fibres, whereas the model-space
  -- lemma uses those on E and F. `erw` unfolds these fibre instances; `rw` cannot match them.
  erw [inTangentCoordinates_model_space (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, F))]
  exact (mfderiv_eq_fderiv (𝕜 := 𝕜) (f := g q.1) (x := q.2)).symm

/-- The `i`-th iterated derivative in the vector-space variable of a jointly `C^n` family is
jointly `C^m` at a point when `m + i ≤ n`. -/
theorem ContMDiffAt.iteratedFDeriv_right {i : ℕ}
    (hg : ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) n (Function.uncurry g) z)
    (hmn : m + i ≤ n) :
    ContMDiffAt (J.prod 𝓘(𝕜, E)) 𝓘(𝕜, E [×i]→L[𝕜] F) m
      (fun q : P × E ↦ iteratedFDeriv 𝕜 i (g q.1) q.2) z := by
  induction i generalizing m with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.contDiff.contMDiff.contMDiffAt.comp z
      (hg.of_le (by simpa using hmn))
  | succ i ih =>
    have hi := ih (m := m + 1) (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm 1 (i : ℕ∞ω)] using hmn)
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) ↦ E) F).symm.contDiff
      |>.contMDiff.contMDiffAt.comp z
        (hi.fderiv_right (g := fun p ↦ iteratedFDeriv 𝕜 i (g p)) le_rfl)
