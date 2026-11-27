/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.SardSmale
public import TauCeti.Examples.Analysis.Calculus.Sard
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Fredholm.Basic

/-!
# Checks of the Sard–Smale theorem

The Sard–Smale theorem `TauCeti.isMeagre_image_criticalPoints_of_isFredholm` says that the
critical values of a `C^k` Fredholm map on a Lindelöf set are meagre, provided
`k > max (i, 0)` at each point, where `i = dim ker - dim coker` is the index of the derivative.
Its hypothesis is written `i.toNat + 1 ≤ k`. This file tests the statement on three maps between
Euclidean spaces, where the derivative is Fredholm of index `0`, `-1` and `2`. Each case separates
the index from a quantity that could be confused with it.

* **Index zero.** The identity of `ℝ` has derivative the identity, Fredholm of index `0`, so
  `k = 1` suffices; its critical image is empty.
* **Negative index.** The derivative of the line `t ↦ (t, 0)` in the plane has kernel of
  dimension `0` and cokernel of dimension `1`, so its index is `-1` and `C¹` suffices. Every point
  is critical, since an operator of negative index is never onto: the regular part of every fibre
  is empty (`TauCeti.SardSmaleExample.setOf_eq_and_surjective_fderiv_line_eq_empty`). The critical
  image is the whole line `ℝ × {0}`, which is closed with empty interior, hence nowhere dense and
  meagre.
* **Index above the kernel bound.** The zero map `ℝ³ → ℝ` has derivative with kernel of dimension
  `3` and cokernel of dimension `1`, so its index is `2`, not the dimension `3` of its kernel. The
  hypothesis holds at `k = 3` and fails at `k = 2`
  (`TauCeti.SardSmaleExample.sardSmale_hypothesis_zero_iff`). The critical image is `{0}`, a
  nowhere dense set.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. **87** (1965),
  861–866.
-/

public section

open Function Module Set
open scoped ContDiff

namespace TauCeti.SardSmaleExample

open SardExample

/-! ### The identity of `ℝ` -/

/-- The derivative of the identity of `ℝ` is Fredholm. -/
theorem isFredholm_fderiv_id (x : ℝ) : (fderiv ℝ (id : ℝ → ℝ) x).IsFredholm := by
  rw [fderiv_id]
  exact .id

/-- The derivative of the identity of `ℝ` has index `0`. -/
theorem index_fderiv_id (x : ℝ) : (fderiv ℝ (id : ℝ → ℝ) x).index = 0 := by
  rw [fderiv_id, ContinuousLinearMap.index_id]

/-- The Sard–Smale theorem applies to the identity of `ℝ` at `k = 1`, since `1 > max (0, 0)`. Its
critical image is empty (`TauCeti.SardExample.criticalPoints_id`). -/
example : IsMeagre ((id : ℝ → ℝ) '' (univ ∩ {x | ¬ Surjective (fderiv ℝ id x)})) :=
  isMeagre_image_criticalPoints_of_isFredholm (n := 1) (fun _ _ ↦ contDiff_id.contDiffAt)
    (fun x _ ↦ isFredholm_fderiv_id x) fun x _ ↦ by simp

/-! ### The line `t ↦ (t, 0)` in the plane -/

/-- The derivative of the line `t ↦ (t, 0)` is Fredholm, as is every operator between
finite-dimensional spaces. -/
theorem isFredholm_fderiv_line (t : ℝ) :
    (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t).IsFredholm :=
  ContinuousLinearMap.isFredholm_of_finiteDimensional _

/-- The derivative of the line `t ↦ (t, 0)` has index `1 - 2 = -1`. -/
theorem index_fderiv_line (t : ℝ) : (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t).index = -1 := by
  rw [ContinuousLinearMap.index_eq_of_finiteDimensional]
  simp

/-- The derivative of the line `t ↦ (t, 0)` is injective: its kernel has dimension `0`. -/
theorem finrank_ker_fderiv_line (t : ℝ) :
    finrank ℝ (LinearMap.ker (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t : ℝ →ₗ[ℝ] ℝ × ℝ)) = 0 := by
  rw [(hasFDerivAt_prodMk_left t (0 : ℝ)).fderiv, Submodule.finrank_eq_zero,
    LinearMap.ker_eq_bot]
  exact fun a b h ↦ by simpa using h

/-- The derivative of the line `t ↦ (t, 0)` has cokernel of dimension `1`. -/
theorem finrank_coker_fderiv_line (t : ℝ) :
    finrank ℝ ((ℝ × ℝ) ⧸
      LinearMap.range (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t : ℝ →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  have h := ContinuousLinearMap.index_eq_finrank_sub (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)
  rw [index_fderiv_line] at h
  have hker := finrank_ker_fderiv_line t
  omega

/-- **A regular fibre of negative index is empty.** No derivative of the line `t ↦ (t, 0)` is onto,
since it has index `-1` while a surjective operator has index the dimension of its kernel. So for
every value `y` the regular points of the fibre over `y` form the empty set. -/
theorem setOf_eq_and_surjective_fderiv_line_eq_empty (y : ℝ × ℝ) :
    {t : ℝ | (t, (0 : ℝ)) = y ∧ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)} = ∅ := by
  refine eq_empty_of_forall_notMem fun t ⟨_, hsurj⟩ ↦ ?_
  have h := (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t).index_of_surjective hsurj
  rw [index_fderiv_line] at h
  omega

/-- The critical image of the line `t ↦ (t, 0)`, the whole line `ℝ × {0}`, is closed with empty
interior, hence nowhere dense. -/
theorem isNowhereDense_image_criticalPoints_line :
    IsNowhereDense ((fun s : ℝ ↦ (s, (0 : ℝ))) ''
      {t | ¬ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)}) := by
  rw [image_criticalPoints_line, (isClosed_univ.prod isClosed_singleton).isNowhereDense_iff,
    interior_prod_eq, interior_singleton, prod_empty]

/-- The Sard–Smale theorem applies to the line `t ↦ (t, 0)` at `k = 1`, since its index `-1` is
negative: the critical image, the whole line, is meagre. -/
example : IsMeagre ((fun s : ℝ ↦ (s, (0 : ℝ))) ''
    (univ ∩ {t | ¬ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)})) :=
  isMeagre_image_criticalPoints_of_isFredholm (n := 1)
    (fun _ _ ↦ (contDiff_prodMk_left (0 : ℝ)).contDiffAt)
    (fun t _ ↦ isFredholm_fderiv_line t) fun t _ ↦ by simp [index_fderiv_line]

/-! ### The zero map `ℝ³ → ℝ` -/

/-- The derivative of the zero map `ℝ³ → ℝ` is the zero operator. -/
theorem fderiv_zero_map (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x = 0 :=
  fderiv_const_apply 0

/-- The derivative of the zero map `ℝ³ → ℝ` has index `3 - 1 = 2`. -/
theorem index_fderiv_zero_map (x : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x).index = 2 := by
  rw [fderiv_zero_map, ContinuousLinearMap.index_zero]
  simp

/-- The derivative of the zero map `ℝ³ → ℝ` has kernel of dimension `3`, which is not its index:
its cokernel has dimension `1`. -/
theorem finrank_ker_fderiv_zero_map (x : EuclideanSpace ℝ (Fin 3)) :
    finrank ℝ (LinearMap.ker (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) = 3 := by
  rw [fderiv_zero_map, ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero, finrank_top,
    finrank_euclideanSpace_fin]

/-- The derivative of the zero map `ℝ³ → ℝ` has cokernel of dimension `1`. -/
theorem finrank_coker_fderiv_zero_map (x : EuclideanSpace ℝ (Fin 3)) :
    finrank ℝ (ℝ ⧸ LinearMap.range (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) = 1 := by
  have h := ContinuousLinearMap.index_eq_finrank_sub
    (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x)
  rw [index_fderiv_zero_map] at h
  have hker := finrank_ker_fderiv_zero_map x
  omega

/-- For the zero map `ℝ³ → ℝ`, of index `2`, the hypothesis `i.toNat + 1 ≤ k` of the Sard–Smale
theorem reads `3 ≤ k`: it holds at `k = 3` and fails at `k = 2`. -/
theorem sardSmale_hypothesis_zero_iff (x : EuclideanSpace ℝ (Fin 3)) {k : ℕ∞ω} :
    (((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤ k ↔
      3 ≤ k := by
  rw [index_fderiv_zero_map]
  norm_num

/-- At `k = 2` the hypothesis of the Sard–Smale theorem fails for the zero map `ℝ³ → ℝ`. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    ¬ (((fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x).index.toNat + 1 : ℕ) : ℕ∞ω) ≤
      2 := by
  rw [sardSmale_hypothesis_zero_iff]
  decide

/-- The critical image of the zero map `ℝ³ → ℝ` is `{0}`
(`TauCeti.SardExample.image_criticalPoints_const`), a nowhere dense subset of `ℝ`. -/
theorem isNowhereDense_image_criticalPoints_zero_map :
    IsNowhereDense ((fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) ''
      {x | ¬ Surjective (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x)}) := by
  rw [image_criticalPoints_const, isClosed_singleton.isNowhereDense_iff, interior_singleton]

/-- The Sard–Smale theorem applies to the zero map `ℝ³ → ℝ` at `k = 3`: its critical image `{0}`
is meagre. -/
example : IsMeagre ((fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) ''
    (univ ∩ {x | ¬ Surjective (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ (0 : ℝ)) x)})) :=
  isMeagre_image_criticalPoints_of_isFredholm (n := 3) (fun _ _ ↦ contDiff_const.contDiffAt)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    fun x _ ↦ (sardSmale_hypothesis_zero_iff x).2 le_rfl

end TauCeti.SardSmaleExample
