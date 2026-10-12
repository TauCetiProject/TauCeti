/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import TauCeti.LinearAlgebra.ExteriorPower.Localization

/-!
# Exterior powers of sections on basic affine opens

For a quasicoherent module `M`, an affine open `U`, and a regular function `f` on `U`, the
restriction from `⋀ⁿ Γ(M,U)` to `⋀ⁿ Γ(M,D(f))` is localization at the powers of `f`.
Here the two exterior powers use the respective rings of regular functions. The restriction
is the actual map of `PresheafOfModulesOfCommRing.exteriorPower`, which sends each wedge of
sections to the wedge of their restrictions.

This is an affine-local computation of the sectionwise exterior-power presheaf. It does not
identify sections of the sheafification with exterior powers of sections on arbitrary opens.
The section localization `Scheme.Modules.isLocalizedModule_basicOpenRestrict` induces this
comparison via `LinearMap.isLocalizedModule_exteriorPower`.

## References

* [The Stacks Project, Lemma 10.13.6](https://stacks.math.columbia.edu/tag/0C6F).
* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- The actual sectionwise exterior-power restriction to a basic open of an affine open is
localization at the powers of the defining function. No finiteness assumption on the
quasicoherent module or flatness assumption on its sections is needed. -/
theorem isLocalizedModule_exteriorPower_map_basicOpen [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (f : Γ(X, U)) (n : ℕ) :
    IsLocalizedModule (.powers f)
      (((PresheafOfModulesOfCommRing.exteriorPower (R := X.presheaf) n).obj M.val).map
        (homOfLE (X.basicOpen_le f)).op).hom := by
  let : IsLocalization (.powers f) Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  -- Name the actual `ModuleCat` section carriers and their scalar projections: replacing
  -- them by inferred section instances can change the dependent exterior-power carriers.
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
  exact @LinearMap.isLocalizedModule_exteriorPower Γ(X, U) Γ(X, X.basicOpen f) N₀ N
    _ _ _ _ N₀.isModule _ NR N.isModule NT φ (.powers f) _ _ n _ _ _
    (fun m ↦ PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk (R := X.presheaf)
      n M.val (homOfLE (X.basicOpen_le f)).op m)

end AlgebraicGeometry.Scheme.Modules
