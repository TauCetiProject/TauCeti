/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Localization

/-!
# Symmetric powers of sections on basic affine opens

For a quasicoherent module `M`, an affine open `U`, and a regular function `f` on `U`, the
restriction from `Symⁿ Γ(M,U)` to `Symⁿ Γ(M,D(f))` is localization at the powers of `f`.
The symmetric powers use the respective rings of regular functions, and the map is the actual
restriction of `PresheafOfModulesOfCommRing.symmetricPower`.

This computes the sectionwise symmetric-power presheaf on an affine basis. It does not identify
the symmetric power of sections with sections of the sheafified symmetric power on arbitrary
opens. The computation supplies the localization compatibility used in that affine comparison.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- On the basic opens of an affine open, the restriction in the sectionwise symmetric-power
presheaf of a quasicoherent module is localization at the defining function.
This holds in every degree, without any freeness or finiteness assumption on the module. -/
theorem isLocalizedModule_symmetricPower_map_basicOpen [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (f : Γ(X, U)) (n : ℕ) :
    IsLocalizedModule (.powers f)
      (((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val).map
        (homOfLE (X.basicOpen_le f)).op).hom := by
  let : IsLocalization (.powers f) Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  -- The section-carrier bookkeeping follows
  -- `Scheme.Modules.isLocalizedModule_exteriorPower_map_basicOpen`.
  -- Keep the section carriers and their restriction-of-scalars structures explicit: these
  -- determine the dependent homogeneous-submodule carriers in the presheaf restriction map.
  let N := PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (.op (X.basicOpen f))
  let N₀ := PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (.op U)
  let NR : Module Γ(X, U) N := Module.compHom N (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let NT : @IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) N _ N.isModule.toSMul NR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : N₀ →ₗ[Γ(X, U)] N :=
    (PresheafOfModulesOfCommRing.map (R := X.presheaf) M.val
      (homOfLE (X.basicOpen_le f)).op).hom
  have hφ : φ = M.basicOpenRestrict f := by
    ext m
    exact (M.basicOpenRestrict_apply f m).symm
  let : IsLocalizedModule (.powers f) φ := hφ.symm ▸
    M.isLocalizedModule_basicOpenRestrict hU f
  let φ' : N₀ →ₛₗ[algebraMap Γ(X, U) Γ(X, X.basicOpen f)] N :=
    (ModuleCat.semilinearMapAddEquiv
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom N₀ N).symm
        (PresheafOfModulesOfCommRing.map (R := X.presheaf) M.val
          (homOfLE (X.basicOpen_le f)).op)
  exact @LinearMap.isLocalizedModule_symmetricPower Γ(X, U) Γ(X, X.basicOpen f) N₀ N
    _ _ _ _ N₀.isModule _ NR N.isModule NT φ (.powers f) _ _ n _ _ φ' (fun _ ↦ rfl) _
    (fun x ↦ PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply (R := X.presheaf)
      n M.val (homOfLE (X.basicOpen_le f)).op x)

end AlgebraicGeometry.Scheme.Modules
