/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.A1.Basic
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Self-injectivity of the preprojective algebra of `A₁`

The preprojective algebra of the one-vertex quiver is the coefficient ring. When this ring is
semisimple, so is the preprojective algebra, and every module over it is injective. In particular,
its regular module is injective. This supplies the rank-one case of self-injectivity for finite
ADE preprojective algebras.

The algebra comparison is `TauCeti.preprojectiveAlgebraEquivA1`; the preprojective presentation
follows Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1.
-/

public section

namespace TauCeti

/-- The `A₁` preprojective algebra is semisimple when the coefficient ring is semisimple. -/
theorem isSemisimpleRing_preprojectiveAlgebra_A1 (k : Type*) [CommRing k]
    [IsSemisimpleRing k] :
    IsSemisimpleRing (preprojectiveAlgebra k preprojectiveA1Quiver) :=
  (preprojectiveAlgebraEquivA1 k).symm.toRingEquiv.isSemisimpleRing

/-- The regular left module of the `A₁` preprojective algebra is injective. -/
theorem moduleInjective_preprojectiveAlgebra_A1 (k : Type*) [CommRing k]
    [IsSemisimpleRing k] :
    Module.Injective (preprojectiveAlgebra k preprojectiveA1Quiver)
      (preprojectiveAlgebra k preprojectiveA1Quiver) := by
  have h := isSemisimpleRing_preprojectiveAlgebra_A1 k
  exact @Module.injective_of_isSemisimpleRing _ _ h _ _ _

end TauCeti
