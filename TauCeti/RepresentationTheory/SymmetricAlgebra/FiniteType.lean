/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType
import TauCeti.RingTheory.Invariant.FiniteType

/-!
# Noether finiteness for the invariants of a finite linear group

Let a finite group `G` act linearly on a finitely generated module `M` over a commutative ring `R`,
and so on the symmetric algebra `S = Sym M`, with invariant subalgebra `A = Sym(M)^G`. Then `S` is
a finite `A`-module, and over a Noetherian base `A` is a finitely generated `R`-algebra (Noether's
finiteness theorem). Both facts are the general results for fixed subalgebras of finite groups,
transported along `Representation.symmetricAlgebraInvariants_eq_fixedPoints`.

## Main results

* `Representation.moduleFinite_symmetricAlgebraInvariants`: `Sym M` is a finite module over the
  invariant subalgebra.
* `Representation.finiteType_symmetricAlgebraInvariants`: over a Noetherian base, the invariant
  subalgebra is of finite type.

## References

* H. Derksen, G. Kemper, *Computational Invariant Theory*, Springer (2002), Chapter 2.
-/

public section

namespace Representation

variable {R G M : Type*} [CommRing R] [Group G] [Finite G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- For a finite group acting on a finitely generated module `M`, the symmetric algebra `Sym M` is
a finite module over the invariant subalgebra. -/
instance moduleFinite_symmetricAlgebraInvariants [Module.Finite R M] :
    Module.Finite ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  ρ.symmetricAlgebraInvariants_eq_fixedPoints ▸
    TauCeti.FixedPoints.moduleFinite_subalgebra R (SymmetricAlgebra R M) G

/-- **Noether's finiteness theorem** for the invariants of a finite group acting on a finitely
generated module over a Noetherian ring: the invariant subalgebra is of finite type. -/
instance finiteType_symmetricAlgebraInvariants [IsNoetherianRing R] [Module.Finite R M] :
    Algebra.FiniteType R ρ.symmetricAlgebraInvariants :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  ρ.symmetricAlgebraInvariants_eq_fixedPoints ▸
    TauCeti.FixedPoints.finiteType_subalgebra R (SymmetricAlgebra R M) G

end Representation
