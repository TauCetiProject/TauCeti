/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero
import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Cartan
import TauCeti.Algebra.Lie.Subalgebra.Normalizer
import TauCeti.Algebra.Lie.Symplectic.Killing
import TauCeti.LinearAlgebra.JordanChevalley.AdjointPair

/-!
# Nondegenerate families of quadratic forms are commuting and semisimple

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of the symplectic Lie algebra
`sp(V, ω)`. This file shows that such a Cartan subalgebra is **toral**: its elements commute and
are semisimple endomorphisms of `V`. Hence:

* a nondegenerate family is a Poisson-commuting family
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.quadraticPoissonBracket_eq_zero`),
  which the definition does not require, so the forms in its span pairwise Poisson-commute
  (`TauCeti.SymplecticForm.quadraticPoissonBracket_eq_zero_of_mem_span`);
* every form in the span of a nondegenerate family has a semisimple Hamiltonian endomorphism
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd`);
* a form whose Poisson brackets with the members of a nondegenerate family lie in its span lies
  in the span itself
  (`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_mem_span`), since
  the Cartan subalgebra is self-normalizing; in particular a form Poisson-commuting with every
  member lies in the span
  (`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero`), so the
  span is the Poisson centralizer of the family
  (`IsNondegenerateQuadraticFamily.mem_span_iff_forall_quadraticPoissonBracket_eq_zero`). This is
  the normalizer criterion
  `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_iff_forall_mem_span` of
  `TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero`, whose Poisson-commutation
  hypothesis a nondegenerate family satisfies automatically.

At a nondegenerate rank-zero point `x` of a `C²` map `F`, the family is that of the Hessians of the
functions `ℓ ∘ F`, whose Hamiltonian endomorphisms are the linearizations at `x` of the Hamiltonian
vector fields of `ℓ ∘ F`. These linearizations are therefore semisimple and pairwise commuting
(`TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint.isSemisimple_fderiv_hamiltonianVectorField`,
`TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint.commute_fderiv_hamiltonianVectorField`), even
when the components of `F` are not assumed to Poisson-commute.

Williamson's classification of the Cartan subalgebras of `sp(V, ω)` starts from this: commuting
semisimple endomorphisms are simultaneously reduced, over `ℂ`, to their eigenvalues `±a`, `±i b`
and `±a ± i b`, which give the hyperbolic, elliptic and focus-focus blocks.

Over `ℝ` the Cartan subalgebras of `sp(V, ω)` need not be split, so Mathlib's toral theorem for
Killing Lie algebras (`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`), which
assumes a triangularizable action, does not apply. Instead:

* `sp(V, ω)` has trivial radical, hence nondegenerate Killing form
  (`TauCeti.SymplecticForm.hasTrivialRadical_skewAdjointLieSubalgebra`, from
  `LinearMap.BilinForm.IsAlt.hasTrivialRadical_skewAdjointLieSubalgebra`);
* it contains the Jordan–Chevalley parts of its elements, since those of a skew-adjoint
  endomorphism are skew-adjoint (`LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`);
* a Cartan subalgebra of a Killing Lie algebra of endomorphisms with this closure property is
  toral (`LieSubalgebra.isSemisimple_of_mem_isCartanSubalgebra`,
  `LieSubalgebra.commute_of_mem_isCartanSubalgebra`).

## Main results

* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.quadraticPoissonBracket_eq_zero`: a
  nondegenerate family is Poisson-commuting.
* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd`: their
  Hamiltonian endomorphisms are semisimple.
* `IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_mem_span`,
  `IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero`,
  `IsNondegenerateQuadraticFamily.mem_span_iff_forall_quadraticPoissonBracket_eq_zero`: the span of
  a nondegenerate family is its own Poisson normalizer and centralizer.
* `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint.isSemisimple_fderiv_hamiltonianVectorField`,
  `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint.commute_fderiv_hamiltonianVectorField`: the
  linearized Hamiltonian vector fields at a nondegenerate rank-zero point are semisimple and
  commute.
* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_eq_of_span_le`: a nondegenerate
  family is maximal among Poisson-commuting families, since its Cartan subalgebra is
  self-normalizing.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §15.3
  (Cartan subalgebras of semisimple Lie algebras are toral).
-/

public section

open LieAlgebra LieSubalgebra Module

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The symplectic Lie algebra `sp(V, ω)` has trivial radical, so its Killing form is
nondegenerate. -/
instance hasTrivialRadical_skewAdjointLieSubalgebra (ω : SymplecticForm V) :
    HasTrivialRadical ℝ (skewAdjointLieSubalgebra ω.toBilinForm) :=
  ω.isAlt.hasTrivialRadical_skewAdjointLieSubalgebra ω.nondegenerate

namespace IsNondegenerateQuadraticFamily

variable {ω : SymplecticForm V} {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **A nondegenerate family is Poisson-commuting**: the Cartan subalgebra of `sp(V, ω)`
generated by a nondegenerate family is abelian. Forms in the span of the family then
Poisson-commute by `TauCeti.SymplecticForm.quadraticPoissonBracket_eq_zero_of_mem_span`. -/
theorem quadraticPoissonBracket_eq_zero (h : ω.IsNondegenerateQuadraticFamily Q) (i j : ι) :
    ω.quadraticPoissonBracket (Q i) (Q j) = 0 := by
  have := (isNondegenerateQuadraticFamily_iff Q).1 h
  rw [quadraticPoissonBracket_eq_zero_iff, ← coe_hamiltonianEndEquiv_apply,
    ← coe_hamiltonianEndEquiv_apply]
  exact commute_of_mem_isCartanSubalgebra _
    (hamiltonianEndEquiv_mem_lieSpan_of_mem_span (Submodule.subset_span ⟨i, rfl⟩))
    (hamiltonianEndEquiv_mem_lieSpan_of_mem_span (Submodule.subset_span ⟨j, rfl⟩))

/-- **A nondegenerate family spans its own normalizer.** A quadratic form whose Poisson brackets
with the members of a nondegenerate family all lie in the span of the family lies in that span
itself: the Cartan subalgebra of `sp(V, ω)` generated by the family is self-normalizing. This is
`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_iff_forall_mem_span`, whose
Poisson-commutation hypothesis holds by `quadraticPoissonBracket_eq_zero`. -/
theorem mem_span_of_forall_quadraticPoissonBracket_mem_span
    (h : ω.IsNondegenerateQuadraticFamily Q) {R : QuadraticForm ℝ V}
    (hR : ∀ i, ω.quadraticPoissonBracket R (Q i) ∈ Submodule.span ℝ (Set.range Q)) :
    R ∈ Submodule.span ℝ (Set.range Q) :=
  (isNondegenerateQuadraticFamily_iff_forall_mem_span h.quadraticPoissonBracket_eq_zero).1 h R hR

/-- **A nondegenerate family spans its own centralizer.** A quadratic form Poisson-commuting with
every member of a nondegenerate family lies in the span of the family: the Cartan subalgebra of
`sp(V, ω)` generated by the family is abelian and self-normalizing, so it contains every element
commuting with it. -/
theorem mem_span_of_forall_quadraticPoissonBracket_eq_zero
    (h : ω.IsNondegenerateQuadraticFamily Q) {R : QuadraticForm ℝ V}
    (hR : ∀ i, ω.quadraticPoissonBracket R (Q i) = 0) : R ∈ Submodule.span ℝ (Set.range Q) :=
  h.mem_span_of_forall_quadraticPoissonBracket_mem_span fun i ↦ hR i ▸ zero_mem _

/-- **The span of a nondegenerate family is its Poisson centralizer**: a quadratic form lies in
the span of a nondegenerate family exactly when it Poisson-commutes with every member. -/
theorem mem_span_iff_forall_quadraticPoissonBracket_eq_zero
    (h : ω.IsNondegenerateQuadraticFamily Q) {R : QuadraticForm ℝ V} :
    R ∈ Submodule.span ℝ (Set.range Q) ↔ ∀ i, ω.quadraticPoissonBracket R (Q i) = 0 :=
  ⟨fun hR i ↦ ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hR
    (Submodule.subset_span ⟨i, rfl⟩), h.mem_span_of_forall_quadraticPoissonBracket_eq_zero⟩

/-- **Forms in the span of a nondegenerate family have semisimple Hamiltonian endomorphisms**:
the Cartan subalgebra of `sp(V, ω)` generated by a nondegenerate family consists of semisimple
endomorphisms of `V`. -/
theorem isSemisimple_hamiltonianEnd (h : ω.IsNondegenerateQuadraticFamily Q)
    {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
    (ω.hamiltonianEnd R).IsSemisimple := by
  have := (isNondegenerateQuadraticFamily_iff Q).1 h
  rw [← coe_hamiltonianEndEquiv_apply]
  refine isSemisimple_of_mem_isCartanSubalgebra _ (fun n s hc hn hs hns ↦ ?_)
    (hamiltonianEndEquiv_mem_lieSpan_of_mem_span hR)
  -- `sp(V, ω)` contains the nilpotent part of each of its elements.
  exact (LinearMap.mem_skewAdjointSubmodule _).2 <|
    LinearMap.IsSkewAdjoint.of_isNilpotent_of_add ω.nondegenerate.2 hc hn hs <|
      (LinearMap.mem_skewAdjointSubmodule _).1 hns

/-- **A nondegenerate family is maximal among Poisson-commuting families.** If the span of a
nondegenerate family `Q` lies in the span of a Poisson-commuting family `Q'`, the two spans are
equal: a Cartan subalgebra of `sp(V, ω)` is not properly contained in an abelian subalgebra, since
such a subalgebra normalizes it. -/
theorem span_eq_of_span_le {κ : Type*} {Q' : κ → QuadraticForm ℝ V}
    (h : ω.IsNondegenerateQuadraticFamily Q)
    (hQ' : ∀ k l, ω.quadraticPoissonBracket (Q' k) (Q' l) = 0)
    (hle : Submodule.span ℝ (Set.range Q) ≤ Submodule.span ℝ (Set.range Q')) :
    Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range Q') := by
  have hC := (isNondegenerateQuadraticFamily_iff Q).1 h
  set L := lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
    (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))
  set L' := lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
    (Set.range fun k ↦ ω.hamiltonianEndEquiv (Q' k))
  -- The Lie subalgebra `L'` generated by the commuting family `Q'` is abelian and contains the
  -- self-normalizing `L`, so the two are equal.
  have hab : IsLieAbelian L' := isLieAbelian_lieSpan_hamiltonianEndEquiv hQ'
  have hLL' : L = L' := eq_of_le_of_isLieAbelian_of_normalizer_eq (lieSpan_le.2 <| by
    rintro _ ⟨i, rfl⟩
    exact hamiltonianEndEquiv_mem_lieSpan_of_mem_span (hle (Submodule.subset_span ⟨i, rfl⟩)))
    hC.self_normalizing
  refine le_antisymm hle (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact (hamiltonianEndEquiv_mem_lieSpan_iff h.quadraticPoissonBracket_eq_zero).1
    (hLL'.ge (subset_lieSpan ⟨k, rfl⟩))

end IsNondegenerateQuadraticFamily

/-! ### Nondegenerate rank-zero points -/

namespace IsNondegenerateRankZeroPoint

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {ω : SymplecticForm E} {F : E → G} {x : E}

/-- **The linearized Hamiltonian vector fields at a nondegenerate rank-zero point are
semisimple.** For every linear functional `ℓ`, the linearization at `x` of the Hamiltonian vector
field of `ℓ ∘ F` is a semisimple endomorphism. -/
theorem isSemisimple_fderiv_hamiltonianVectorField (h : ω.IsNondegenerateRankZeroPoint F x)
    (ℓ : G →L[ℝ] ℝ) :
    Module.End.IsSemisimple (fderiv ℝ (ω.hamiltonianVectorField (ℓ ∘ F)) x : Module.End ℝ E) := by
  rw [ω.fderiv_hamiltonianVectorField (ℓ.contDiff.contDiffAt.comp x h.contDiffAt)]
  exact h.isNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ℓ, rfl⟩))

/-- **The linearized Hamiltonian vector fields at a nondegenerate rank-zero point commute.** No
Poisson-commutation of the components of `F` is assumed: it holds to second order at `x` because
the Hessians generate a Cartan subalgebra of `sp(E, ω)`. -/
theorem commute_fderiv_hamiltonianVectorField (h : ω.IsNondegenerateRankZeroPoint F x)
    (ℓ ℓ' : G →L[ℝ] ℝ) :
    Commute (fderiv ℝ (ω.hamiltonianVectorField (ℓ ∘ F)) x : Module.End ℝ E)
      (fderiv ℝ (ω.hamiltonianVectorField (ℓ' ∘ F)) x : Module.End ℝ E) := by
  rw [ω.fderiv_hamiltonianVectorField (ℓ.contDiff.contDiffAt.comp x h.contDiffAt),
    ω.fderiv_hamiltonianVectorField (ℓ'.contDiff.contDiffAt.comp x h.contDiffAt),
    ← quadraticPoissonBracket_eq_zero_iff]
  exact ω.quadraticPoissonBracket_eq_zero_of_mem_span
    h.isNondegenerateQuadraticFamily.quadraticPoissonBracket_eq_zero
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ℓ, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ℓ', rfl⟩))

end IsNondegenerateRankZeroPoint

end TauCeti.SymplecticForm
