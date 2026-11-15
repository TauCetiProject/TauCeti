/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.RepresentationTheory.Basic

/-!
# Symmetric operators from unitary representations

Let `σ` be a representation of a group `G` on an inner product space over `𝕜 = ℝ` or `ℂ`, and
suppose `σ` is unitary: every `σ g` preserves the inner product. Then the adjoint of `σ g` is
`σ g⁻¹`, so a group-algebra element `a`, a finitely supported combination of group elements, acts
by the symmetric operator `σ(a) = ∑_g a(g) σ(g)` whenever its coefficients satisfy
`a(g⁻¹) = conj (a(g))` for every `g`. If `a` is moreover idempotent, `σ(a)` is a symmetric
projection, which by `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range` is the
orthogonal projection onto its range.

This is how group-algebra idempotents become orthogonal projectors: it applies to the primitive
central idempotents of a complex group algebra, whose coefficients have this symmetry because
inversion conjugates character values, and verbatim over `ℝ` to real idempotents such as those of
real-valued linear characters.

## Main statements

* `Representation.isSymmetric_asAlgebraHom`: a conjugate-symmetric group-algebra element acts by a
  symmetric operator in a unitary representation.
* `Representation.isSymmetricProjection_asAlgebraHom`: a conjugate-symmetric idempotent acts by a
  symmetric projection.
-/

public section

open scoped InnerProductSpace MonoidAlgebra

namespace Representation

/-! ### Symmetric operators from a unitary representation -/

section Unitary

variable {𝕜 G W : Type*} [RCLike 𝕜] [Group G]
  [SeminormedAddCommGroup W] [InnerProductSpace 𝕜 W] (σ : Representation 𝕜 G W)

/-- **A conjugate-symmetric group-algebra element acts by a symmetric operator in a unitary
representation.** If every `σ g` preserves the inner product, the adjoint of `σ g` is `σ g⁻¹`, so
`∑_g a(g) σ(g)` is symmetric as soon as `a(g⁻¹) = conj (a(g))` for every `g`. -/
theorem isSymmetric_asAlgebraHom (hσ : ∀ g v w, ⟪σ g v, σ g w⟫_𝕜 = ⟪v, w⟫_𝕜) {a : 𝕜[G]}
    (ha : ∀ g, a.coeff g⁻¹ = star (a.coeff g)) : (σ.asAlgebraHom a).IsSymmetric := by
  intro v w
  -- The support of `a` is closed under inversion, so inversion reindexes the two sums.
  have hsupp : ∀ g ∈ a.coeff.support, g⁻¹ ∈ a.coeff.support := fun g hg => by
    rw [Finsupp.mem_support_iff, ha, star_ne_zero]
    exact Finsupp.mem_support_iff.mp hg
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_nbij' (·⁻¹) (·⁻¹) hsupp hsupp (by simp) (by simp) fun g _ => ?_
  have hinv : ⟪v, σ g⁻¹ w⟫_𝕜 = ⟪σ g v, w⟫_𝕜 := by
    rw [← hσ g, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  simp [ha, hinv]

/-- **A conjugate-symmetric idempotent of the group algebra acts by a symmetric projection** in a
unitary representation, that is, by an orthogonal projection
(`LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range`). -/
theorem isSymmetricProjection_asAlgebraHom (hσ : ∀ g v w, ⟪σ g v, σ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
    {a : 𝕜[G]} (ha : ∀ g, a.coeff g⁻¹ = star (a.coeff g)) (he : IsIdempotentElem a) :
    (σ.asAlgebraHom a).IsSymmetricProjection :=
  ⟨he.map σ.asAlgebraHom, σ.isSymmetric_asAlgebraHom hσ ha⟩

end Unitary

end Representation

