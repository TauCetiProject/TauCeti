/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Relative twisted homology and homotopy equivalences

A map of topological pairs whose ambient and subspace components are homotopy equivalences
induces a quasi-isomorphism of relative singular chains with local coefficients. The source
coefficients are the pullback of the target system along the ambient map. The inverses need not
commute with the inclusions. In particular, a homotopy inverse in the category of pairs suffices.
Neither pair needs to be a cofibration or have CW type.

The proof applies the comparison theorem for short exact sequences of chain complexes to the
native twisted pair sequences. On subspace chains, the canonical comparison between restriction
and pullback precedes the map induced by the subspace component. Absolute homotopy invariance
supplies the other two quasi-isomorphisms. All resulting homology isomorphisms are induced by
the specified map of pairs.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* The absolute local-coefficient homotopy invariance construction in
  `TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance` and Mathlib's
  `HomologicalComplex.HomologySequence.quasiIso_τ₃`.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {P Q : TopPair.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)

/-- A map of pairs whose two components are homotopy equivalences induces a quasi-isomorphism of
relative singular chains with local coefficients. No compatibility of the inverses is needed. -/
theorem quasiIso_relativeTwistedChainComplexMap (f : P ⟶ Q)
    (e : ContinuousMap.HomotopyEquiv P.fst Q.fst)
    (eSub : ContinuousMap.HomotopyEquiv P.snd Q.snd)
    (he : e.toFun = (TopPair.Hom.fst f).hom)
    (heSub : eSub.toFun = (TopPair.Hom.snd f).hom) :
    QuasiIso (TopPair.twistedChainComplexMap f L) := by
  have hAmbient : QuasiIso (LocalCoefficientSystem.twistedChainComplexMap
      (TopPair.Hom.fst f) L) := by
    have h := e.quasiIso_twistedChainComplexMap L
    rw [he, TopCat.ofHom_hom] at h
    exact h
  have hSubspace : QuasiIso (TopPair.twistedSubspaceChainComplexMap f L) := by
    have : QuasiIso (LocalCoefficientSystem.twistedChainComplexMap
        (TopPair.Hom.snd f) (Q.subspaceSystem L)) := by
      have h := eSub.quasiIso_twistedChainComplexMap (Q.subspaceSystem L)
      rw [heSub, TopCat.ofHom_hom] at h
      exact h
    rw [TopPair.twistedSubspaceChainComplexMap_def]
    infer_instance
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (TopPair.twistedChainComplexShortComplexMap f L)
    (P.shortExact_twistedChainComplexShortComplex _)
    (Q.shortExact_twistedChainComplexShortComplex L)
  simp only [TopPair.twistedChainComplexShortComplexMap_τ₁,
    TopPair.twistedChainComplexShortComplexMap_τ₂,
    TopPair.twistedChainComplexShortComplexMap_τ₃] at h
  exact h hSubspace hAmbient

/-- A map of pairs whose components are homotopy equivalences induces isomorphisms on relative
singular homology with local coefficients in every degree, including degree zero. -/
theorem isIso_relativeTwistedHomologyMap (f : P ⟶ Q)
    (e : ContinuousMap.HomotopyEquiv P.fst Q.fst)
    (eSub : ContinuousMap.HomotopyEquiv P.snd Q.snd)
    (he : e.toFun = (TopPair.Hom.fst f).hom)
    (heSub : eSub.toFun = (TopPair.Hom.snd f).hom) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap f L n) := by
  have := L.quasiIso_relativeTwistedChainComplexMap f e eSub he heSub
  infer_instance

/-- A homotopy inverse of a map of pairs makes its induced relative twisted homology map an
isomorphism, with the source system pulled back along its ambient component. -/
theorem isIso_relativeTwistedHomologyMap_of_homotopyInverse (f : P ⟶ Q) (g : Q ⟶ P)
    (H : TopPair.Homotopic (f ≫ g) (𝟙 P))
    (K : TopPair.Homotopic (g ≫ f) (𝟙 Q)) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap f L n) := by
  let e : ContinuousMap.HomotopyEquiv P.fst Q.fst :=
    { toFun := (TopPair.Hom.fst f).hom
      invFun := (TopPair.Hom.fst g).hom
      left_inv := ⟨H.some.fst⟩
      right_inv := ⟨K.some.fst⟩ }
  let eSub : ContinuousMap.HomotopyEquiv P.snd Q.snd :=
    { toFun := (TopPair.Hom.snd f).hom
      invFun := (TopPair.Hom.snd g).hom
      left_inv := ⟨H.some.snd⟩
      right_inv := ⟨K.some.snd⟩ }
  exact L.isIso_relativeTwistedHomologyMap f e eSub rfl rfl n

end TauCeti.LocalCoefficientSystem
