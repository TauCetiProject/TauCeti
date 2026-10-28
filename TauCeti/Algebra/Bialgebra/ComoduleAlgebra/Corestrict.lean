/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict

/-!
# Corestriction of comodule algebras

A bialgebra morphism corestricts a comodule algebra by applying that morphism to the
coefficient factor of the coaction. In particular, a quotient of a coordinate Hopf algebra
restricts the regular action to the closed subgroup it represents. This uses the comodule
corestriction `Comodule.Corestrict`, retaining the original algebra structure.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

variable {R H K A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring K] [Bialgebra R K] [Semiring A] [Algebra R A] [ComoduleAlgebra R H A]

/-- Corestriction of a comodule algebra along a bialgebra morphism. -/
@[implicit_reducible]
noncomputable def Corestrict (f : H →ₐc[R] K) : ComoduleAlgebra R K A where
  toComodule := Comodule.Corestrict f.toCoalgHom
  coact_one := by
    rw [Comodule.corestrict_coact_apply, coact_one]
    exact (Algebra.TensorProduct.map (AlgHom.id R A) f.toAlgHom).map_one
  coact_mul a b := by
    rw [Comodule.corestrict_coact_apply, coact_mul,
      Comodule.corestrict_coact_apply, Comodule.corestrict_coact_apply]
    exact (Algebra.TensorProduct.map (AlgHom.id R A) f.toAlgHom).map_mul _ _

/-- The underlying comodule of a corestricted comodule algebra is its corestriction. -/
theorem toComodule_corestrict (f : H →ₐc[R] K) :
    (Corestrict (A := A) f).toComodule = Comodule.Corestrict f.toCoalgHom := by
  rfl

/-- The corestricted coaction applies `id ⊗ f` to the original coaction. -/
theorem corestrict_coact_apply (f : H →ₐc[R] K) (a : A) :
    letI := Corestrict (A := A) f
    Comodule.coact (R := R) (C := K) a =
      Algebra.TensorProduct.map (AlgHom.id R A) f.toAlgHom
        (Comodule.coact (R := R) (C := H) a) := by
  rw [toComodule_corestrict, Comodule.corestrict_coact_apply]
  exact (DFunLike.congr_fun
    (Algebra.TensorProduct.toLinearMap_map (AlgHom.id R A) f.toAlgHom) _).symm

/-- The corestricted algebra coaction is the original coaction followed by `id ⊗ f`. -/
@[simp]
theorem corestrict_coactAlgHom (f : H →ₐc[R] K) :
    letI := Corestrict (A := A) f
    coactAlgHom R K A =
      (Algebra.TensorProduct.map (AlgHom.id R A) f.toAlgHom).comp (coactAlgHom R H A) := by
  ext a
  simp only [coactAlgHom_apply, AlgHom.comp_apply, corestrict_coact_apply]

end TauCeti.ComoduleAlgebra
