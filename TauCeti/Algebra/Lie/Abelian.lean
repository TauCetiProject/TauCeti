/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# The abelian Lie algebra on a module

`TauCeti.AbelianLieAlgebra M` equips an additive group with the zero Lie bracket, retaining
its module structure. This allows a vector space, for example a space of extra central
directions, to occur as an abelian factor in a product of Lie algebras.
-/

public section

namespace TauCeti

/-- An additive group regarded as a Lie algebra with zero bracket. -/
@[expose]
def AbelianLieAlgebra (M : Type*) := M

namespace AbelianLieAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

instance : AddCommGroup (AbelianLieAlgebra M) := inferInstanceAs (AddCommGroup M)

instance : Module R (AbelianLieAlgebra M) := inferInstanceAs (Module R M)

instance : LieRing (AbelianLieAlgebra M) where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add _).symm
  lie_add _ _ _ := (zero_add _).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add _).symm

instance : LieAlgebra R (AbelianLieAlgebra M) where
  lie_smul _ _ _ := (smul_zero _).symm

instance : IsLieAbelian (AbelianLieAlgebra M) := ⟨fun _ _ => rfl⟩

/-- The underlying module of the abelian Lie algebra is the original module. -/
def equiv : AbelianLieAlgebra M ≃ₗ[R] M := LinearEquiv.refl R M

end AbelianLieAlgebra

end TauCeti
