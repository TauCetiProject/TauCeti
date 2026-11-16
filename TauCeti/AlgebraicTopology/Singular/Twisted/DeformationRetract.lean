/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple
public import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Relative twisted homology of deformation retracts and triples

If the inclusion `B ↪ A` of a topological pair `(A, B)` is a homotopy equivalence — for instance,
when `A` deformation retracts onto `B` — then `C(B; L|_B) ⟶ C(A; L)` is a quasi-isomorphism, so the
relative twisted chain complex `C(A, B; L)` is acyclic
(`acyclic_twistedChainComplex_of_homotopyEquiv`) and `Hₖ(A, B; L) = 0`. For a triple `(X, A, B)`
whose inner inclusion `B ↪ A` is a homotopy equivalence, acyclicity of `C(A, B; L|_A)` makes
`C(X, B; L) ⟶ C(X, A; L)` (`TauCeti.TopTriple.twistedChainComplexTotalToOuter`) a quasi-isomorphism
for every local coefficient system `L` on `X`, without cofibration or pointwise-fixing hypotheses.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.LocalCoefficientSystem

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- If the subspace inclusion of a pair `(A, B)` is a homotopy equivalence, its relative twisted
chain complex `C(A, B; L)` is acyclic for every local coefficient system `L` on `A`. -/
theorem acyclic_twistedChainComplex_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) :
    (P.twistedChainComplex L).Acyclic := by
  have h := e.quasiIso_twistedChainComplexMap L; rw [he, TopCat.ofHom_hom] at h
  exact (P.shortExact_twistedChainComplexShortComplex L).quasiIso_f_iff.1 h

/-- If the subspace inclusion of a pair `(A, B)` is a homotopy equivalence, its relative twisted
homology vanishes in every degree. -/
theorem isZero_twistedHomology_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_homotopyEquiv L e he k).isZero_homology

/-- If the ambient space of a pair `(A, B)` deformation retracts onto `B`, its relative twisted
chain complex `C(A, B; L)` is acyclic. -/
theorem acyclic_twistedChainComplex_of_deformationRetraction (r : C(P.fst, P.snd))
    (hr : Function.LeftInverse r P.map.hom)
    (hH : (P.map.hom.comp r).Homotopic (ContinuousMap.id P.fst)) :
    (P.twistedChainComplex L).Acyclic :=
  P.acyclic_twistedChainComplex_of_homotopyEquiv L
    (.ofDeformationRetraction P.map.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun P.map.hom r hr hH)

/-- If the ambient space of a pair `(A, B)` deformation retracts onto `B`, its relative twisted
homology vanishes in every degree. -/
theorem isZero_twistedHomology_of_deformationRetraction (r : C(P.fst, P.snd))
    (hr : Function.LeftInverse r P.map.hom)
    (hH : (P.map.hom.comp r).Homotopic (ContinuousMap.id P.fst)) (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_deformationRetraction L r hr hH k).isZero_homology

end TopPair

namespace TauCeti.TopTriple

variable {R : Type u} [Ring R]

section General

variable (T : TopTriple.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R T.fst)

/-- **Replacing a subspace by a homotopy-equivalent larger subspace.** For a triple `(X, A, B)`
whose inner inclusion `B ↪ A` is a homotopy equivalence, the quotient map
`C(X, B; L) ⟶ C(X, A; L)` is a quasi-isomorphism for every local coefficient system `L` on `X`. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  (T.shortExact_twistedChainComplexShortComplex L).quasiIso_g_iff.2
    ((innerPair.obj T).acyclic_twistedChainComplex_of_homotopyEquiv
      ((outerPair.obj T).subspaceSystem L) e he)

/-- For a triple `(X, A, B)` whose inner inclusion `B ↪ A` is a homotopy equivalence, the quotient
map `Hₖ(X, B; L) ⟶ Hₖ(X, A; L)` is an isomorphism in every degree. -/
theorem isIso_twistedHomologyTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) := by
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L e he; infer_instance

/-- For a triple `(X, A, B)` where `A` deformation retracts onto `B`, the quotient map
`C(X, B; L) ⟶ C(X, A; L)` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction
    (r : C(T.snd, T.thd)) (hr : Function.LeftInverse r T.innerMap.hom)
    (hH : (T.innerMap.hom.comp r).Homotopic (ContinuousMap.id T.snd)) :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofDeformationRetraction T.innerMap.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun T.innerMap.hom r hr hH)

/-- For a triple `(X, A, B)` where `A` deformation retracts onto `B`, the quotient map
`Hₖ(X, B; L) ⟶ Hₖ(X, A; L)` is an isomorphism in every degree. -/
theorem isIso_twistedHomologyTotalToOuter_of_deformationRetraction
    (r : C(T.snd, T.thd)) (hr : Function.LeftInverse r T.innerMap.hom)
    (hH : (T.innerMap.hom.comp r).Homotopic (ContinuousMap.id T.snd)) (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) := by
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH
  infer_instance

end General

section Subsets

variable {X : TopCat.{v}} {A B : Set X} (hBA : B ⊆ A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- For subsets `B ⊆ A` of `X`, if `A` deformation retracts onto `B`, then the quotient map
`C(X, B; L) ⟶ C(X, A; L)` is a quasi-isomorphism for every local coefficient system `L` on `X`. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction
    (r : C(A, B)) (hr : ∀ b, r (ContinuousMap.inclusion hBA b) = b)
    (hH : ((ContinuousMap.inclusion hBA).comp r).Homotopic (ContinuousMap.id A)) :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH

/-- For subsets `B ⊆ A` of `X`, if `A` deformation retracts onto `B`, then the quotient map
`Hₖ(X, B; L) ⟶ Hₖ(X, A; L)` is an isomorphism in every degree. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_deformationRetraction
    (r : C(A, B)) (hr : ∀ b, r (ContinuousMap.inclusion hBA b) = b)
    (hH : ((ContinuousMap.inclusion hBA).comp r).Homotopic (ContinuousMap.id A)) (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) := by
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction hBA L r hr hH
  infer_instance

/-- For subsets `B ⊆ A` of `X`, a deformation retraction in the weak sense of `A` onto `B`
makes the quotient map `C(X, B; L) ⟶ C(X, A; L)` a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction
    (H : unitInterval × A → X) (hH : Continuous H) (hHA : ∀ p, H p ∈ A)
    (h₀ : ∀ x : A, H (0, x) = x) (h₁ : ∀ x : A, H (1, x) ∈ B)
    (hHB : ∀ t (x : A), (x : X) ∈ B → H (t, x) ∈ B) :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofWeakDeformationRetraction hBA H hH hHA h₀ h₁ hHB)
    (ContinuousMap.ext fun b ↦ Subtype.ext
      (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply hBA H hH hHA h₀ h₁ hHB b))

/-- For subsets `B ⊆ A` of `X`, a deformation retraction in the weak sense of `A` onto `B`
makes the quotient map `Hₖ(X, B; L) ⟶ Hₖ(X, A; L)` an isomorphism in every degree. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_weakDeformationRetraction
    (H : unitInterval × A → X) (hH : Continuous H) (hHA : ∀ p, H p ∈ A)
    (h₀ : ∀ x : A, H (0, x) = x) (h₁ : ∀ x : A, H (1, x) ∈ B)
    (hHB : ∀ t (x : A), (x : X) ∈ B → H (t, x) ∈ B) (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) := by
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction
    hBA L H hH hHA h₀ h₁ hHB
  infer_instance

end Subsets

end TauCeti.TopTriple
