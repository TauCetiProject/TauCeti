/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The orthogonal complement of the last vector of an orthonormal basis

An orthonormal basis `b` indexed by `Fin (n + 1)` restricts to an orthonormal basis
`b.orthogonalLast`, indexed by `Fin n`, of the orthogonal complement of its last vector: its
`i`-th vector is `b i.castSucc`.  Unlike Mathlib's
`OrthonormalBasis.fromOrthogonalSpanSingleton`, which chooses some orthonormal basis of the
orthogonal complement of a nonzero vector, this basis is determined by `b`.

Iterating it peels the vectors of `b` off one at a time, last to first.  This is how a basis of a
Euclidean space determines compatible bases of the successive equators of its unit sphere, along
which the homology of spheres is computed by induction on the dimension.

## Main declarations

* `OrthonormalBasis.apply_castSucc_mem_orthogonal_singleton_last`: the vectors `b i.castSucc`
  are orthogonal to the last vector of `b`.
* `OrthonormalBasis.orthogonalLast`: the orthonormal basis of the orthogonal complement of the
  last vector of `b` given by its remaining vectors, with
  `OrthonormalBasis.coe_orthogonalLast_apply` computing its vectors.
-/

public section

open Module

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- Every vector of an orthonormal basis other than the last one is orthogonal to the last
one. -/
theorem apply_castSucc_mem_orthogonal_singleton_last (b : OrthonormalBasis (Fin (n + 1)) 𝕜 E)
    (i : Fin n) :
    b i.castSucc ∈ (𝕜 ∙ b (Fin.last n))ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.2
    (b.orthonormal.2 (Fin.castSucc_ne_last i).symm)

/-- The orthonormal basis of the orthogonal complement of the last vector of an orthonormal basis
`b`, given by the remaining vectors of `b` in their order: its `i`-th vector is `b i.castSucc`
(`OrthonormalBasis.coe_orthogonalLast_apply`). -/
noncomputable def orthogonalLast (b : OrthonormalBasis (Fin (n + 1)) 𝕜 E) :
    OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ b (Fin.last n))ᗮ :=
  have hon : Orthonormal 𝕜 fun i : Fin n ↦
      (⟨b i.castSucc, b.apply_castSucc_mem_orthogonal_singleton_last i⟩ :
        (𝕜 ∙ b (Fin.last n))ᗮ) :=
    orthonormal_iff_ite.2 fun i j ↦ by simp [orthonormal_iff_ite.1 b.orthonormal]
  have : Fact (finrank 𝕜 E = n + 1) := ⟨by simp [finrank_eq_card_basis b.toBasis]⟩
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ n
  -- `n` orthonormal vectors span the `n`-dimensional orthogonal complement.
  OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin,
      Submodule.finrank_orthogonal_span_singleton (n := n) (b.orthonormal.ne_zero _)])).ge

/-- The `i`-th vector of `b.orthogonalLast` is `b i.castSucc`. -/
@[simp]
theorem coe_orthogonalLast_apply (b : OrthonormalBasis (Fin (n + 1)) 𝕜 E) (i : Fin n) :
    (b.orthogonalLast i : E) = b i.castSucc := by
  rw [orthogonalLast, OrthonormalBasis.coe_mk]

end OrthonormalBasis
