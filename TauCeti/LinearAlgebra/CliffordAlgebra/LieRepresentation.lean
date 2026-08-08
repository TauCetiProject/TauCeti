/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.QuadraticRealization

/-!
# Lie representations induced from Clifford modules

A Lie homomorphism into the skew-adjoint endomorphisms of a nondegenerate quadratic module
lifts through the quadratic realization in its Clifford algebra. Composing this lift with any
Clifford action makes the target Clifford module a module for the original Lie algebra.

## Main results

* `TauCeti.CliffordAlgebra.cliffordInducedRep`: the induced Lie representation on a Clifford
  module.
* `TauCeti.CliffordAlgebra.cliffordInducedRep_apply`: its defining equation.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, "Every Clifford module is a `𝔤`-module".
-/

public section

open CliffordAlgebra

universe u v w x

namespace TauCeti.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie representation on a Clifford module induced through the quadratic realization. -/
noncomputable def cliffordInducedRep {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) : L →ₗ⁅K⁆ Module.End K S :=
  ρ.toLieHom.comp <|
    (quadraticLieSubalgebra Q).incl.comp <|
      (soEquivQuadratic Q hQ).toLieHom.comp θ

/-- The induced representation acts through the quadratic realization and the Clifford action. -/
@[simp]
theorem cliffordInducedRep_apply {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) (y : L) :
    cliffordInducedRep Q hQ θ ρ y = ρ ↑(soEquivQuadratic Q hQ (θ y)) := by
  rfl

end TauCeti.CliffordAlgebra
