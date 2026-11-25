/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Base change of Picard groups

For a ring homomorphism `f : R →+* S`, Mathlib's `CommRing.Pic.mapRingHom f` sends the class of an
invertible `R`-module `M` to the class of `S ⊗[R] M`. This file identifies the base change through
a spanning semilinear map, and packages the base change along a ring isomorphism as an isomorphism
of Picard groups.

## Main declarations

* `CommRing.Pic.mapRingHom_mk_eq_mk`: if an `f`-semilinear map `M → N` to an invertible module
  spans it, then `N` represents the base change of `M` along `f` in the Picard group.
* `CommRing.Pic.mapRingEquiv`: the isomorphism of Picard groups induced by a ring isomorphism.
-/

public section

noncomputable section

open Module TensorProduct

namespace CommRing.Pic

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}
  {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
  [AddCommMonoid N] [Module S N] [Module.Invertible S N]

/-- Let `f : R →+* S`, let `M` be an invertible `R`-module and `N` an invertible `S`-module. If an
`f`-semilinear map `g : M → N` has image spanning `N` over `S`, then `N` represents the base
change of `M` along `f` in the Picard group of `S`. -/
theorem mapRingHom_mk_eq_mk (g : M →ₛₗ[f] N) (hg : Submodule.span S (Set.range g) = ⊤) :
    mapRingHom f (Pic.mk R M) = Pic.mk S N := by
  algebraize [f]
  let := Module.restrictScalars R S N
  have := IsScalarTower.restrictScalars R S N
  let l : M →ₗ[R] N :=
    { toFun := g, map_add' := g.map_add
      map_smul' r x := by
        rw [g.map_smulₛₗ, RingHom.id_apply, ← algebraMap_smul S r (g x),
          RingHom.algebraMap_toAlgebra] }
  have hl : Function.Surjective (l.liftBaseChange S) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [l]⟩
  rw [← RingHom.algebraMap_toAlgebra f, mapRingHom_algebraMap, mapAlgebra_apply, mk_eq_mk_iff]
  exact ⟨AlgebraTensorModule.congr (.refl S S) (mk.linearEquiv R M) ≪≫ₗ
    .ofBijective _ (Module.Invertible.bijective_of_surjective hl)⟩

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism of Picard groups, sending the class of
an invertible module `M` to the class of `S ⊗[R] M`. -/
def mapRingEquiv (e : R ≃+* S) : Pic R ≃* Pic S :=
  MonoidHom.toMulEquiv (mapRingHom e) (mapRingHom e.symm)
    (by rw [mapRingHom_comp_mapRingHom, RingEquiv.symm_comp, mapRingHom_id])
    (by rw [mapRingHom_comp_mapRingHom, RingEquiv.comp_symm, mapRingHom_id])

@[simp]
theorem mapRingEquiv_apply (e : R ≃+* S) (L : Pic R) : mapRingEquiv e L = mapRingHom e L :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) : (mapRingEquiv e).symm = mapRingEquiv e.symm :=
  (rfl)

end CommRing.Pic
