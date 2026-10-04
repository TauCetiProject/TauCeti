/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict

/-!
# Coalgebra morphisms as morphisms of regular comodules

A coalgebra morphism `f : C → D` is a morphism of right `D`-comodules from the regular
`C`-comodule corestricted along `f` to the regular `D`-comodule. Thus kernels of restriction
maps on coordinate coalgebras can be treated as invariant subspaces, using the comodule
kernel API rather than proving tensor-product stability separately.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open TauCeti

namespace CoalgHom

universe u v w

variable {R : Type u} {C : Type v} {D : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

/-- A coalgebra morphism as a morphism from its corestricted regular source comodule to
its regular target comodule. -/
def toComoduleHom (f : C →ₗc[R] D) :
    letI : Comodule R D C := Comodule.Corestrict f
    Comodule.Hom R D C D := by
  letI : Comodule R D C := Comodule.Corestrict f
  exact
    { toLinearMap := f.toLinearMap
      map_coact := by
        ext c
        simp only [LinearMap.comp_apply, Comodule.corestrict_coact_apply,
          Comodule.instSelf_coact, TensorProduct.map_map, LinearMap.comp_id,
          LinearMap.id_comp]
        exact CoalgHomClass.map_comp_comul_apply f c }

/-- The underlying linear map of the regular-comodule morphism is the coalgebra map. -/
@[simp]
theorem toComoduleHom_toLinearMap (f : C →ₗc[R] D) :
    letI : Comodule R D C := Comodule.Corestrict f
    f.toComoduleHom.toLinearMap = f.toLinearMap :=
  (rfl)

/-- The regular-comodule morphism evaluates as the coalgebra map. -/
@[simp]
theorem toComoduleHom_apply (f : C →ₗc[R] D) (c : C) :
    letI : Comodule R D C := Comodule.Corestrict f
    f.toComoduleHom c = f c :=
  (rfl)

end CoalgHom
