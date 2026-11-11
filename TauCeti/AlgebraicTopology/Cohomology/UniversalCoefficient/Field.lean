/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# Universal coefficients over a field

Over a field `k` every module is free, so the singular homology `Hₙ(X; k)` of a space `X` is
projective in every degree and the universal coefficient theorem with projective homology
(`TopCat.singularKroneckerEquivOfProjectiveHomology`) applies with no hypothesis on `X`: the
`Ext¹` term vanishes and the Kronecker map identifies singular cohomology with the dual of singular
homology,

`Hⁿ(X; k) ≃ₗ[k] Module.Dual k (Hₙ(X; k))`.

The identification is the Kronecker pairing, so it is natural in `X`: the pull-back along a
continuous map corresponds to the transpose of the push-forward on homology.  Consequently
`Hⁿ(X; k)` is finite-dimensional exactly when `Hₙ(X; k)` is, and the two have the same `finrank`
(both are zero in the infinite-dimensional case).  The same holds for the relative cohomology and
homology of a topological pair.  For an arbitrary coefficient module `M` the isomorphism
`Hⁿ(X; k, M) ≃ₗ[k] (Hₙ(X; k) ⟶ M)` is `TopCat.singularKroneckerEquivOfProjectiveHomology` itself,
whose projectivity hypotheses are found by instance search over a field.

## Main declarations

* `TopCat.singularCohomologyDualEquiv`: the natural isomorphism
  `Hⁿ(X; k) ≃ₗ[k] Module.Dual k (Hₙ(X; k))`, characterized by
  `TopCat.singularCohomologyDualEquiv_apply` and
  `TopCat.singularKronecker_singularCohomologyDualEquiv_symm`, with naturality
  `TopCat.singularCohomologyDualEquiv_singularCohomologyMap`.
* `TopCat.finrank_singularCohomology` and `TopCat.finite_singularCohomology_iff`: cohomology and
  homology over a field have the same `finrank` (zero when infinite-dimensional) and are
  finite-dimensional together.
* `TopPair.singularCohomologyDualEquiv`, its naturality
  `TopPair.singularCohomologyDualEquiv_singularCohomologyMap`, `TopPair.finrank_singularCohomology`
  and `TopPair.finite_singularCohomology_iff`: the same for relative cohomology of a pair.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2 and the discussion of field coefficients following it.
-/

public section

noncomputable section

open CategoryTheory Module AlgebraicTopology

universe w

variable {k : Type w} [Field k]

namespace TopCat

variable (X : TopCat.{w})

/-- **The universal coefficient theorem over a field**: singular cohomology with coefficients in
a field `k` is the dual of singular homology, `Hⁿ(X; k) ≃ₗ[k] Module.Dual k (Hₙ(X; k))`.  It sends
a class to the linear form underlying its Kronecker pairing
(`TopCat.singularCohomologyDualEquiv_apply`). -/
def singularCohomologyDualEquiv (n : ℕ) :
    X.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n ≃ₗ[k]
      Dual k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (ModuleCat.of k k)).obj X) :=
  X.singularKroneckerEquivOfProjectiveHomology _ _ n ≪≫ₗ ModuleCat.homLinearEquiv

/-- The equivalence `TopCat.singularCohomologyDualEquiv` is the Kronecker map. -/
@[simp]
lemma singularCohomologyDualEquiv_apply (n : ℕ)
    (α : X.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) :
    X.singularCohomologyDualEquiv n α = (X.singularKronecker k n α).hom := by
  rw [singularCohomologyDualEquiv, LinearEquiv.trans_apply,
    singularKroneckerEquivOfProjectiveHomology_apply]
  exact ModuleCat.homLinearEquiv_apply _

/-- The inverse of `TopCat.singularCohomologyDualEquiv` sends a linear form `φ` to the class whose
Kronecker pairing is `φ`. -/
@[simp]
lemma singularKronecker_singularCohomologyDualEquiv_symm (n : ℕ)
    (φ : Dual k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (ModuleCat.of k k)).obj X)) :
    X.singularKronecker k n ((X.singularCohomologyDualEquiv n).symm φ) = ModuleCat.ofHom φ := by
  ext x
  rw [← singularCohomologyDualEquiv_apply, LinearEquiv.apply_symm_apply, ModuleCat.hom_ofHom]

variable {X} in
/-- **Naturality of the universal coefficient isomorphism over a field**: for a continuous map
`f : X ⟶ Y`, the linear form of the pull-back `f^*α` is the transpose of
`f_* : Hₙ(X; k) ⟶ Hₙ(Y; k)` applied to the linear form of `α`. -/
lemma singularCohomologyDualEquiv_singularCohomologyMap {Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (α : Y.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) :
    X.singularCohomologyDualEquiv n (TopCat.singularCohomologyMap f n α) =
      Dual.transpose (((singularHomologyFunctor (ModuleCat.{w} k) n).obj
        (ModuleCat.of k k)).map f).hom (Y.singularCohomologyDualEquiv n α) := by
  simp [singularKronecker_naturality, Dual.transpose_apply]

/-- Over a field, singular cohomology and singular homology have the same `finrank` in every
degree.  When `Hₙ(X; k)` is infinite-dimensional both sides have `finrank` zero; their cardinal
dimensions then need not agree. -/
@[simp]
theorem finrank_singularCohomology (n : ℕ) :
    finrank k (X.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) =
      finrank k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (ModuleCat.of k k)).obj X) :=
  (X.singularCohomologyDualEquiv n).finrank_eq.trans Subspace.dual_finrank_eq

/-- Over a field, singular cohomology is finite-dimensional in a given degree exactly when singular
homology is. -/
theorem finite_singularCohomology_iff (n : ℕ) :
    Module.Finite k (X.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) ↔
      Module.Finite k
        (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (ModuleCat.of k k)).obj X) :=
  (Module.Finite.equiv_iff (X.singularCohomologyDualEquiv n)).trans (finite_dual_iff k)

end TopCat

namespace TopPair

variable (P : TopPair.{w})

/-- **The relative universal coefficient theorem over a field**: the relative singular cohomology
of a pair with coefficients in a field `k` is the dual of its relative singular homology,
`Hⁿ(X, A; k) ≃ₗ[k] Module.Dual k (Hₙ(X, A; k))`.  It sends a class to the linear form underlying
its relative Kronecker pairing (`TopPair.singularCohomologyDualEquiv_apply`). -/
def singularCohomologyDualEquiv (n : ℕ) :
    P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n ≃ₗ[k]
      Dual k (P.singularHomology (C := ModuleCat.{w} k) (ModuleCat.of k k) n) :=
  P.singularKroneckerEquivOfProjectiveHomology _ _ n ≪≫ₗ ModuleCat.homLinearEquiv

/-- The equivalence `TopPair.singularCohomologyDualEquiv` is the relative Kronecker map. -/
@[simp]
lemma singularCohomologyDualEquiv_apply (n : ℕ)
    (α : P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) :
    P.singularCohomologyDualEquiv n α = (P.singularKronecker k n α).hom := by
  rw [singularCohomologyDualEquiv, LinearEquiv.trans_apply,
    singularKroneckerEquivOfProjectiveHomology_apply]
  exact ModuleCat.homLinearEquiv_apply _

/-- The inverse of `TopPair.singularCohomologyDualEquiv` sends a linear form `φ` to the class whose
Kronecker pairing is `φ`. -/
@[simp]
lemma singularKronecker_singularCohomologyDualEquiv_symm (n : ℕ)
    (φ : Dual k (P.singularHomology (C := ModuleCat.{w} k) (ModuleCat.of k k) n)) :
    P.singularKronecker k n ((P.singularCohomologyDualEquiv n).symm φ) = ModuleCat.ofHom φ := by
  ext x
  rw [← singularCohomologyDualEquiv_apply, LinearEquiv.apply_symm_apply, ModuleCat.hom_ofHom]

variable {P} in
/-- **Naturality of the relative universal coefficient isomorphism over a field**: for a map of
pairs `f : P ⟶ P'`, the linear form of the pull-back `f^*α` is the transpose of
`f_* : Hₙ(X, A; k) ⟶ Hₙ(X', A'; k)` applied to the linear form of `α`. -/
lemma singularCohomologyDualEquiv_singularCohomologyMap {P' : TopPair.{w}} (f : P ⟶ P') (n : ℕ)
    (α : P'.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) :
    P.singularCohomologyDualEquiv n (TopPair.singularCohomologyMap f n α) =
      Dual.transpose (TopPair.singularHomologyMap f (ModuleCat.of k k) n).hom
        (P'.singularCohomologyDualEquiv n α) := by
  simp [singularKronecker_naturality, Dual.transpose_apply]

/-- Over a field, relative singular cohomology and relative singular homology of a pair have the
same `finrank` in every degree.  When `Hₙ(X, A; k)` is infinite-dimensional both sides have
`finrank` zero; their cardinal dimensions then need not agree. -/
@[simp]
theorem finrank_singularCohomology (n : ℕ) :
    finrank k (P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) =
      finrank k (P.singularHomology (C := ModuleCat.{w} k) (ModuleCat.of k k) n) :=
  (P.singularCohomologyDualEquiv n).finrank_eq.trans Subspace.dual_finrank_eq

/-- Over a field, relative singular cohomology is finite-dimensional in a given degree exactly when
relative singular homology is. -/
theorem finite_singularCohomology_iff (n : ℕ) :
    Module.Finite k (P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) ↔
      Module.Finite k (P.singularHomology (C := ModuleCat.{w} k) (ModuleCat.of k k) n) :=
  (Module.Finite.equiv_iff (P.singularCohomologyDualEquiv n)).trans (finite_dual_iff k)

end TopPair
