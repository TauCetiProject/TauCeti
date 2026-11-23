/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
public import TauCeti.Analysis.InnerProductSpace.Gram.Fischer

/-!
# Gram determinants of a family completed by a second family

Let `u` be a finite family spanning a subspace `W` of an inner product space, and let `v` be a
second finite family. The Gram determinant of the concatenated family `(u, v)` is the Gram
determinant of `u` times the Gram determinant of the projections of the `v j` to `Wᗮ`
(`Matrix.det_gram_sumElim_eq_mul_det_gram_starProjection`). Subtracting from each `v j` its
component in `W`, a combination of the `u i`, is a block unitriangular change of family, and the
resulting family is the orthogonal concatenation of `u` and the projected family, whose Gram matrix
is block diagonal.

This is the Gram-matrix form of the statement that the volume of a parallelepiped is the volume of
a face times the height over it. Applied to a lattice basis whose first vectors span a subspace
`W`, it computes the covolume of the projection of the lattice to `Wᗮ`. No independence or
finite-dimensionality hypothesis is needed, and either family may be empty.

## Main results

* `Matrix.det_gram_sumElim_eq_mul_det_gram_starProjection`: if `span (range u) = W`, then
  `det (gram (Sum.elim u v)) = det (gram u) * det (gram (fun j ↦ Wᗮ.starProjection (v j)))`.

## References

* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in ℝⁿ*, Q. J. Math. 74
  (2023), 1253–1294, Proposition B.4, p. 1290.
-/

public section

open Submodule
open scoped InnerProductSpace

namespace Matrix

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The Gram determinant of a completed family.** If a finite family `u` spans `W`, then the Gram
determinant of the concatenation of `u` and `v` is the Gram determinant of `u` times the Gram
determinant of the orthogonal projections of the `v j` to `Wᗮ`. -/
theorem det_gram_sumElim_eq_mul_det_gram_starProjection (u : ι → E) (v : κ → E)
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] (hu : span 𝕜 (Set.range u) = W) :
    (gram 𝕜 (Sum.elim u v)).det =
      (gram 𝕜 u).det * (gram 𝕜 fun j ↦ Wᗮ.starProjection (v j)).det := by
  -- The component of each `v j` in `W` is a combination `∑ i, a j i • u i`.
  have hmem (j : κ) : W.starProjection (v j) ∈ span 𝕜 (Set.range u) :=
    hu ▸ W.starProjection_apply_mem (v j)
  choose a ha using fun j ↦ (mem_span_range_iff_exists_fun 𝕜).1 (hmem j)
  -- Subtracting these components is a block unitriangular change of family.
  have hchange : Sum.elim u v = fun x ↦
      ∑ y, fromBlocks (1 : Matrix ι ι 𝕜) 0 (of a) 1 x y •
        Sum.elim u (fun j ↦ Wᗮ.starProjection (v j)) y := by
    ext (i | j)
    · simp [Fintype.sum_sum_type, Matrix.one_apply]
    · simp [Fintype.sum_sum_type, Matrix.one_apply, ha]
  have hdet : (fromBlocks (1 : Matrix ι ι 𝕜) 0 (of a) 1).det = 1 := by
    simp
  -- The changed family is an orthogonal concatenation, with block diagonal Gram matrix.
  have horth : (of fun i j ↦ ⟪u i, Wᗮ.starProjection (v j)⟫_𝕜) = 0 := by
    ext i j
    exact inner_right_of_mem_orthogonal (hu ▸ subset_span ⟨i, rfl⟩)
      (Wᗮ.starProjection_apply_mem (v j))
  rw [hchange, det_gram_sum_smul_of_det_eq_one hdet, gram_sumElim, horth, conjTranspose_zero,
    det_fromBlocks_zero₂₁]

end Matrix
