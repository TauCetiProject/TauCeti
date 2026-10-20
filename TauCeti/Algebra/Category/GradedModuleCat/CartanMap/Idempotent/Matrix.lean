/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective

/-!
# The graded Cartan matrix of an algebra with split degree-zero part

Let `A` be a nonnegatively graded finite-dimensional algebra whose degree-zero piece is spanned by
a complete family of orthogonal nonzero idempotents `eᵢ`, as for the path-length grading of the
path algebra of a finite acyclic quiver or of its quotient by a homogeneous ideal inside the arrow
ideal. Such an algebra carries two canonical Laurent bases: the projective classes `[A eᵢ]` of
`K₀^gr(proj A)` (`TauCeti.gradedIdempotentProjectiveBasis`) and the head classes `[Sᵢ]` of
`G₀^gr(mod A)` (`TauCeti.gradedIdempotentHeadBasis`).

In these bases the graded Cartan matrix has no hypotheses left: the coefficient of `qᵖ` in its
`(i, j)` entry is `dim_k(eᵢ A eⱼ ∩ 𝒜 p)`, the graded multiplicity of `Sᵢ{p}` in `A eⱼ`. The
entries have no negative powers of `q` and constant term `δᵢⱼ`, so the matrix is congruent to
the identity modulo `q`.

The two bases are also the input of the projective/simple duality and of the relation between the
graded Cartan matrix and the q-Euler matrix: `TauCeti.gradedIdempotentProjectiveBasis_apply`
supplies the hypothesis, that the projective basis vectors are the classes `[A eᵢ]`, of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one` and
`TauCeti.gradedProjectiveExtEuler_basis_eq_dualBasis`.

## Main results

* `TauCeti.coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis`: the coefficient of `qᵖ` in
  the `(i, j)` entry is `dim_k(eᵢ A eⱼ ∩ 𝒜 p)`.
* `TauCeti.coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis_of_neg`: negative-degree
  coefficients vanish.
* `TauCeti.coeff_zero_gradedCartanMatrix_gradedIdempotentProjectiveBasis`: the constant term of
  the `(i, j)` entry is `δᵢⱼ`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Sections 2.3--2.4, for graded
  projectives and graded simple modules.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix over `ℤ[q,q⁻¹]`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜) (hneg : ∀ p < 0, 𝒜 p = ⊥)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) (hne : ∀ i, e i ≠ 0)

/-- **The graded Cartan matrix in the canonical bases counts graded corner dimensions.** In the
projective basis `[A eⱼ]` and the head basis `[Sᵢ]`, the coefficient of `qᵖ` in the `(i, j)`
entry of the graded Cartan matrix is `dim_k(eᵢ A eⱼ ∩ 𝒜 p)`. -/
theorem coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis (i j : I) (p : ℤ) :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
        (gradedIdempotentHeadBasis hneg he he₀ hspan hne) i j).coeff p =
      Module.finrank k ↥(cornerSubmodule k (e i) (e j) ⊓ 𝒜 p) := by
  refine coeff_gradedCartanMatrix_of_ofIdeal_span_singleton _ _ he.idem he₀ (fun i i' h => ?_)
    (fun i => ?_) j (he.idem j) (hI j) (gradedIdempotentProjectiveBasis_apply he he₀ hI hneg hspan
      hne j) i p
  · beta_reduce
    rw [← gradedIdempotentHeadBasis_repr_apply hneg he he₀ hspan hne, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne h]
  · rw [← gradedIdempotentHeadBasis_repr_apply hneg he he₀ hspan hne, Module.Basis.repr_self,
      Finsupp.single_eq_same]

/-- The entries of the graded Cartan matrix in the canonical bases have no negative powers
of `q`. -/
theorem coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis_of_neg (i j : I) {p : ℤ}
    (hp : p < 0) :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
        (gradedIdempotentHeadBasis hneg he he₀ hspan hne) i j).coeff p = 0 := by
  rw [coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis, hneg p hp, inf_bot_eq,
    finrank_bot, Nat.cast_zero]

/-- **The graded Cartan matrix in the canonical bases is the identity modulo `q`**: the constant
term of its `(i, j)` entry is `1` if `i = j` and `0` otherwise. -/
theorem coeff_zero_gradedCartanMatrix_gradedIdempotentProjectiveBasis [DecidableEq I] (i j : I) :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
        (gradedIdempotentHeadBasis hneg he he₀ hspan hne) i j).coeff 0 =
      if i = j then 1 else 0 := by
  rw [coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis]
  split_ifs with hij
  · subst hij
    rw [cornerSubmodule_inf_zero_eq_span_singleton he₀ he.toOrthogonalIdempotents hspan,
      finrank_span_singleton (hne i), Nat.cast_one]
  · have hbot : cornerSubmodule k (e i) (e j) ⊓ 𝒜 0 = ⊥ :=
      (Submodule.eq_bot_iff _).2 fun x hx => by
        by_contra hx₀
        exact lt_irrefl 0
          (pos_of_mem_cornerSubmodule_inf he.toOrthogonalIdempotents hneg hspan hij hx hx₀)
    rw [hbot, finrank_bot, Nat.cast_zero]

end TauCeti
