/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.EulerAdmissible
import TauCeti.RingTheory.GradedAlgebra.Semisimple

/-!
# The graded Cartan matrix in idempotent bases

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

Over a field that does not split the simple modules, let the degree-zero piece instead be a
semisimple ring and let the `eᵢ` be primitive with pairwise nonisomorphic left ideals `A eᵢ`. In
the bases `TauCeti.gradedIdempotentProjectiveBasisOfPrimitive` and
`TauCeti.gradedIdempotentHeadBasisOfPrimitive`, the corner dimension `dim_k(eᵢ A eⱼ ∩ 𝒜 p)` is
then `dim_k End_A(Sᵢ)` times the coefficient of `qᵖ`. Also in this generality, the negative-degree
coefficients vanish and the constant coefficient matrix is the identity: the quotient `A eᵢ ⟶ Sᵢ`
is an isomorphism in degree zero, so the division-endomorphism dimensions cancel.

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
* `TauCeti.finrank_end_mul_coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive`:
  for primitive idempotents over a semisimple degree-zero part, `dim_k End_A(Sᵢ)` times the
  coefficient of `qᵖ` in the `(i, j)` entry is `dim_k(eᵢ A eⱼ ∩ 𝒜 p)`.
* `TauCeti.isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasis`: if every pair of graded
  heads `(Sᵢ, Sⱼ)` is graded Euler-admissible, the graded Cartan matrix has unit determinant.
  Contrapositively, a graded Cartan determinant that is not a unit of `ℤ[q,q⁻¹]` exhibits a pair
  of graded heads that is not graded Euler-admissible.
* `TauCeti.isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive`: the same
  for primitive idempotents over a field that need not split the simple modules.

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

/-! ### Primitive idempotents over a semisimple degree-zero part -/

section Primitive

variable [IsSemisimpleRing (𝒜 0)] (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

/-- **The graded Cartan matrix in the canonical bases over a nonsplitting field.** For a complete
family of orthogonal primitive idempotents `eᵢ` of degree zero with pairwise nonisomorphic left
ideals, over a nonnegatively graded algebra with semisimple degree-zero part, take the projective
basis `[A eⱼ]` and the head basis `[Sᵢ]`. The coefficient of `qᵖ` in the `(i, j)` entry of the
graded Cartan matrix, multiplied by `dim_k End_A(Sᵢ)`, is `dim_k(eᵢ A eⱼ ∩ 𝒜 p)`. -/
theorem finrank_end_mul_coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive
    (i j : I) (p : ℤ) :
    (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) *
        (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI hprim hnoniso)
          (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso) i j).coeff p =
      Module.finrank k ↥(cornerSubmodule k (e i) (e j) ⊓ 𝒜 p) := by
  rw [gradedCartanMatrix_apply, gradedIdempotentProjectiveBasisOfPrimitive_apply he he₀ hI hprim
    hnoniso j, gradedCartanMap_of]
  -- The `eᵢ`-coordinate of `[A eⱼ]` is `dim_k End_A(Sᵢ)` times its `i`th head-basis coordinate.
  have h := congrArg (fun f : LaurentPolynomial ℤ => f.coeff p)
    (gradedIdempotentCoordinate_eq_mul_gradedIdempotentHeadBasisOfPrimitive_repr hneg he he₀ hprim
      hnoniso (LaurentK0.of _ ⟨_, gradedFiniteProjectiveModules_le_finiteModules _
        (gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem j) (hI j))⟩) i)
  rw [gradedIdempotentCoordinate_of, ← LaurentPolynomial.smul_eq_C_mul,
    GradedModuleCat.coeff_smulGradedDimension_ofIdeal_span_singleton (he.idem i) (he₀ i)
      (he.idem j) (hI j)] at h
  simpa only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using h.symm

/-- Negative coefficients of the Cartan matrix in primitive-idempotent bases vanish over any
field, not only a splitting field. -/
theorem coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive_of_neg
    (i j : I) {p : ℤ} (hp : p < 0) :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI hprim hnoniso)
      (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso) i j).coeff p = 0 := by
  have hd : (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) ≠ 0 := by
    intro hd
    apply smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero
    rw [smulGradedDimension_gradedPositiveMulQuotient_self hneg (hprim i) (he₀ i), hd, map_zero]
  apply (mul_eq_zero.mp ?_).resolve_left hd
  rw [finrank_end_mul_coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive,
    hneg p hp, inf_bot_eq, finrank_bot, Nat.cast_zero]

/-- The graded Cartan matrix in primitive-idempotent bases is the identity in degree zero,
even over a nonsplitting field. The division-endomorphism dimensions cancel on both sides. -/
theorem coeff_zero_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive
    [DecidableEq I] (i j : I) :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI hprim hnoniso)
      (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso) i j).coeff 0 =
        if i = j then 1 else 0 := by
  have hd : (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) ≠ 0 := by
    intro hd
    apply smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero
    rw [smulGradedDimension_gradedPositiveMulQuotient_self hneg (hprim i) (he₀ i), hd, map_zero]
  have hdim := (LinearEquiv.ofBijective
    (GradedModuleCat.smulPieceMap (e i) (gradedPositiveMulQuotientπ (he₀ j)) 0)
    (bijective_smulPieceMap_gradedPositiveMulQuotientπ_zero hneg (he₀ j) (e i) (he₀ i))).finrank_eq
  have hhead : (gradedPositiveMulQuotient 𝒜 (he₀ j)).smulGradedDimension (e i) =
      if i = j then LaurentPolynomial.C
        (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) else 0 := by
    split_ifs with hij
    · subst j
      exact smulGradedDimension_gradedPositiveMulQuotient_self hneg (hprim i) (he₀ i)
    · exact pairwise_smulGradedDimension_gradedPositiveMulQuotient_eq_zero
        hneg he₀ hprim hnoniso hij
  apply mul_left_cancel₀ hd
  rw [finrank_end_mul_coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive,
    ← GradedModuleCat.coeff_smulGradedDimension_ofIdeal_span_singleton (he.idem i) (he₀ i)
      (he.idem j) (hI j), GradedModuleCat.coeff_smulGradedDimension, hdim,
    ← GradedModuleCat.coeff_smulGradedDimension, hhead]
  split_ifs <;> simp

end Primitive

/-! ### Unimodularity -/

variable [DecidableEq I] [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

/-- **Graded Cartan unimodularity follows from admissibility of the graded heads.** If every
pair `(Sᵢ, Sⱼ)` of graded heads of the `A eᵢ` is graded Euler-admissible, then the graded Cartan
matrix in the canonical bases has unit determinant in `ℤ[q,q⁻¹]`. -/
theorem isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasis
    (h : ∀ i j, IsGradedEulerAdmissible.{uA} k (GradedModuleCat.shift 𝒜)
      (gradedPositiveMulQuotient 𝒜 (he₀ i)) (gradedPositiveMulQuotient 𝒜 (he₀ j))) :
    IsUnit (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
      (gradedIdempotentHeadBasis hneg he he₀ hspan hne)).det := by
  -- The degree-zero part is semisimple and the heads form an exhaustive family of graded simples.
  have := isSemisimpleRing_gradeZero_of_completeOrthogonalIdempotents he he₀ hspan
  exact isUnit_det_gradedCartanMatrix_of_isGradedEulerAdmissible hneg
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan) h _ _

section Primitive

variable [IsSemisimpleRing (𝒜 0)] (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

/-- **Graded Cartan unimodularity over a nonsplitting field.** For a complete family of orthogonal
primitive idempotents `eᵢ` of degree zero with pairwise nonisomorphic left ideals, over a
nonnegatively graded algebra with semisimple degree-zero part, if every pair `(Sᵢ, Sⱼ)` of graded
heads of the `A eᵢ` is graded Euler-admissible, then the graded Cartan matrix in the bases
`[A eⱼ]` and `[Sᵢ]` has unit determinant in `ℤ[q,q⁻¹]`. -/
theorem isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive
    (h : ∀ i j, IsGradedEulerAdmissible.{uA} k (GradedModuleCat.shift 𝒜)
      (gradedPositiveMulQuotient 𝒜 (he₀ i)) (gradedPositiveMulQuotient 𝒜 (he₀ j))) :
    IsUnit (gradedCartanMatrix 𝒜
      (gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI hprim hnoniso)
      (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso)).det :=
  isUnit_det_gradedCartanMatrix_of_isGradedEulerAdmissible hneg
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim) h _ _

end Primitive

end TauCeti
