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

If `B ↪ A` is a homotopy equivalence (e.g. a deformation retraction), then `C(A, B; L)` is acyclic
and `Hₖ(A, B; L) = 0`, and for a triple `(X, A, B)` the quotient map `C(X, B; L) ⟶ C(X, A; L)`
(`TauCeti.TopTriple.twistedChainComplexTotalToOuter`) is a quasi-isomorphism for every `L` on `X`.
-/

public section
noncomputable section
open CategoryTheory Limits TauCeti TauCeti.LocalCoefficientSystem
universe u v w

namespace TopPair
variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- If `P.map` is a homotopy equivalence, `P.twistedChainComplex L` is acyclic. -/
theorem acyclic_twistedChainComplex_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) :
    (P.twistedChainComplex L).Acyclic := by
  have h := e.quasiIso_twistedChainComplexMap L; rw [he, TopCat.ofHom_hom] at h
  exact (P.shortExact_twistedChainComplexShortComplex L).quasiIso_f_iff.1 h
/-- Relative twisted homology vanishes when `P.map` is a homotopy equivalence. -/
theorem isZero_twistedHomology_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst) (he : e.toFun = P.map.hom) (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_homotopyEquiv L e he k).isZero_homology

section DR
variable (r : C(P.fst, P.snd)) (hr : Function.LeftInverse r P.map.hom)
  (hH : (P.map.hom.comp r).Homotopic (ContinuousMap.id P.fst))
include r hr hH
/-- If `P.fst` deformation retracts onto `P.snd`, `P.twistedChainComplex L` is acyclic. -/
theorem acyclic_twistedChainComplex_of_deformationRetraction :
    (P.twistedChainComplex L).Acyclic :=
  P.acyclic_twistedChainComplex_of_homotopyEquiv L (.ofDeformationRetraction P.map.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun P.map.hom r hr hH)
/-- Relative twisted homology vanishes when `P.fst` deformation retracts onto `P.snd`. -/
theorem isZero_twistedHomology_of_deformationRetraction (k : ℕ) :
    IsZero (P.twistedHomology L k) :=
  (P.acyclic_twistedChainComplex_of_deformationRetraction L r hr hH k).isZero_homology
end DR
end TopPair

namespace TauCeti.TopTriple
variable {R : Type u} [Ring R]

section General
variable (T : TopTriple.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R T.fst)
/-- If `T.innerMap` is a homotopy equivalence, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  (T.shortExact_twistedChainComplexShortComplex L).quasiIso_g_iff.2
    ((innerPair.obj T).acyclic_twistedChainComplex_of_homotopyEquiv
      ((outerPair.obj T).subspaceSystem L) e he)
/-- Homology isomorphism induced by `quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv`. -/
theorem isIso_twistedHomologyTotalToOuter_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv T.thd T.snd) (he : e.toFun = T.innerMap.hom) (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) :=
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L e he; inferInstance

section DR
variable (r : C(T.snd, T.thd)) (hr : Function.LeftInverse r T.innerMap.hom)
  (hH : (T.innerMap.hom.comp r).Homotopic (ContinuousMap.id T.snd))
include r hr hH
/-- If `T.snd` deformation retracts onto `T.thd`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction :
    QuasiIso (T.twistedChainComplexTotalToOuter L) :=
  T.quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofDeformationRetraction T.innerMap.hom r hr hH)
    (ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun T.innerMap.hom r hr hH)
/-- Homology isomorphism for `quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction`. -/
theorem isIso_twistedHomologyTotalToOuter_of_deformationRetraction (k : ℕ) :
    IsIso (T.twistedHomologyTotalToOuter L k) :=
  have := T.quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH
  inferInstance
end DR
end General
section Subsets
variable {X : TopCat.{v}} {A B : Set X} (hBA : B ⊆ A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X)
section DeformationRetraction
variable (r : C(A, B)) (hr : ∀ b, r (ContinuousMap.inclusion hBA b) = b)
  (hH : ((ContinuousMap.inclusion hBA).comp r).Homotopic (ContinuousMap.id A))
include r hr hH
/-- Under a deformation retraction of `A` onto `B`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_deformationRetraction L r hr hH
/-- Homology isomorphism for `ofSubset` under a deformation retraction of `A` onto `B`. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_deformationRetraction (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) :=
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction hBA L r hr hH
  inferInstance
end DeformationRetraction
section WeakDeformationRetraction
variable (H : unitInterval × A → X) (hH : Continuous H) (hHA : ∀ p, H p ∈ A)
  (h₀ : ∀ x : A, H (0, x) = x) (h₁ : ∀ x : A, H (1, x) ∈ B)
  (hHB : ∀ t (x : A), (x : X) ∈ B → H (t, x) ∈ B)
include H hH hHA h₀ h₁ hHB
/-- Under a weak deformation retraction of `A` to `B`, `C(X, B; L) ⟶ C(X, A; L)` is a quasi-iso. -/
theorem quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction :
    QuasiIso ((ofSubset hBA).twistedChainComplexTotalToOuter L) :=
  (ofSubset hBA).quasiIso_twistedChainComplexTotalToOuter_of_homotopyEquiv L
    (.ofWeakDeformationRetraction hBA H hH hHA h₀ h₁ hHB)
    (ContinuousMap.ext fun b ↦ Subtype.ext
      (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply hBA H hH hHA h₀ h₁ hHB b))
/-- Homology isomorphism for `ofSubset` under a weak deformation retraction of `A` onto `B`. -/
theorem isIso_twistedHomologyTotalToOuter_ofSubset_of_weakDeformationRetraction (k : ℕ) :
    IsIso ((ofSubset hBA).twistedHomologyTotalToOuter L k) :=
  have := quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_weakDeformationRetraction
    hBA L H hH hHA h₀ h₁ hHB; inferInstance
end WeakDeformationRetraction
end Subsets
end TauCeti.TopTriple
