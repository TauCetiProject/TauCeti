/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Reducedness of symmetric algebras

The symmetric algebra of a free module over a reduced commutative ring is a polynomial algebra
(`SymmetricAlgebra.equivMvPolynomial`), hence reduced. A projective module is a direct summand of
a free module, and a split injection of modules induces an injection of symmetric algebras, so
the symmetric algebra of a projective module over a reduced commutative ring is reduced too. This
covers the coordinate algebra `SymmetricAlgebra R R` of the additive group `𝔾ₐ`.

Some hypothesis on the module is needed: over `R = ℚ[t]` the symmetric algebra of `R ⧸ (t²)` is
`R[x] ⧸ (t² x)`, in which `t x` is a nonzero nilpotent.
-/

public section

namespace TauCeti.SymmetricAlgebra

/-- The symmetric algebra of a projective module over a reduced commutative ring is reduced: it
embeds into the symmetric algebra of a free module, a polynomial algebra. -/
instance instIsReduced {R M : Type*} [CommRing R] [IsReduced R] [AddCommMonoid M] [Module R M]
    [Module.Projective R M] : IsReduced (SymmetricAlgebra R M) := by
  obtain ⟨s, hs⟩ := Module.projective_def.1 ‹Module.Projective R M›
  let e := SymmetricAlgebra.equivMvPolynomial (Finsupp.basisSingleOne (R := R) (ι := M))
  exact isReduced_of_injective ((e : _ →ₐ[R] MvPolynomial M R).comp (SymmetricAlgebra.map R s))
    (e.injective.comp (SymmetricAlgebra.map_injective_of_leftInverse R s _ hs))

end TauCeti.SymmetricAlgebra
