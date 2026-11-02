/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Pushforward of quasi-coherent modules along quasi-compact quasi-separated morphisms

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes and let `M` be a
quasi-coherent `𝒪_X`-module. Then the pushforward `f_* M` is quasi-coherent. No Noetherian,
finiteness or affineness hypothesis is needed.

Quasi-coherence of `f_* M` is checked on the affine opens `V` of `Y`: for `g ∈ Γ(Y, V)`, the
sections of `f_* M` over `Y.basicOpen g` must be the localization at `g` of its sections over
`V` (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_isLocalizedModule`). These are the
sections of `M` over `f ⁻¹ᵁ V` and over `f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g)`. The
open `f ⁻¹ᵁ V` is quasi-compact and quasi-separated, so the qcqs lemma for quasi-coherent
modules (`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`)
applies.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_pushforward`: the
  localization property on `Y.basicOpen g` of a pushforward follows from that of `M` on
  `X.basicOpen (f.app V g)`;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`: pushforward along a
  quasi-compact quasi-separated morphism preserves quasi-coherence.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.8(c).
* The Stacks Project, Lemma 26.24.1 (Tag 01LC).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (M : X.Modules) (f : X ⟶ Y)

/-- Let `f : X ⟶ Y`, `V` an open of `Y` and `g ∈ Γ(Y, V)`. If the sections of `M` over
`X.basicOpen (f.app V g)` are the localization at `f.app V g` of its sections over `f ⁻¹ᵁ V`,
then the sections of `f_* M` over `Y.basicOpen g` are the localization at `g` of its sections
over `V`. -/
theorem isLocalizedModule_basicOpenRestrict_pushforward {V : Y.Opens} (g : Γ(Y, V))
    [IsLocalizedModule.Away (f.app V g) (M.basicOpenRestrict (f.app V g))] :
    IsLocalizedModule.Away g (((pushforward f).obj M).basicOpenRestrict g) := by
  have hD : X.basicOpen (f.app V g) = f ⁻¹ᵁ Y.basicOpen g := (Scheme.preimage_basicOpen f g).symm
  -- Through `f.app V`, `M.basicOpenRestrict (f.app V g)` is a localization at `g` over `Γ(Y, V)`.
  algebraize [(f.app V).hom]
  let : Module Γ(Y, V) Γ(M, f ⁻¹ᵁ V) := Module.compHom _ (f.app V).hom
  let : Module Γ(Y, V) Γ(M, X.basicOpen (f.app V g)) := Module.compHom _ (f.app V).hom
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(M, f ⁻¹ᵁ V) := ⟨fun _ _ _ ↦ mul_smul _ _ _⟩
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(M, X.basicOpen (f.app V g)) :=
    ⟨fun _ _ _ ↦ mul_smul _ _ _⟩
  have := IsLocalizedModule.restrictScalars_powers g (M.basicOpenRestrict (f.app V g))
  -- Restriction from `f ⁻¹ᵁ Y.basicOpen g` to the equal open `X.basicOpen (f.app V g)`.
  let e₀ : Γ(M, f ⁻¹ᵁ Y.basicOpen g) ⟶ Γ(M, X.basicOpen (f.app V g)) :=
    M.presheaf.map (homOfLE hD.le).op
  -- Up to `e₀`, a function `r` on `V` acts on both sides through `f.app V r`.
  let e : Γ((pushforward f).obj M, Y.basicOpen g) →ₗ[Γ(Y, V)] Γ(M, X.basicOpen (f.app V g)) :=
    { toFun := e₀
      map_add' := map_add _
      map_smul' r x := by
        rw [← IsScalarTower.algebraMap_smul Γ(Y, Y.basicOpen g) r x,
          TauCeti.AlgebraicGeometry.pushforward_obj_smul, M.map_smul, RingHom.id_apply,
          ← IsScalarTower.algebraMap_smul Γ(X, f ⁻¹ᵁ V) r (e₀ x), basicOpen_smul_def]
        congr 1
        simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Category.assoc,
          f.naturality_assoc, ← Functor.map_comp]
        -- Both sides restrict `f.app V r` between the same opens; morphisms of opens are unique.
        rfl }
  have he_apply (y) : e y = e₀ y := rfl
  have he : Function.Bijective e := by
    have : IsIso (homOfLE hD.le) := homOfLE_isIso_of_eq _ hD
    exact ConcreteCategory.bijective_of_isIso e₀
  refine (IsLocalizedModule.comp_iff_of_bijective_left (S := .powers g) e he).1 ?_
  -- Up to `e`, the restriction maps of `f_* M` and of `M` agree.
  have hcomp : e ∘ₗ ((pushforward f).obj M).basicOpenRestrict g =
      (M.basicOpenRestrict (f.app V g)).restrictScalars Γ(Y, V) := by
    ext x
    -- `x` is a section of `M` over `f ⁻¹ᵁ V`, and both sides are restrictions of it.
    refine Eq.trans ?_ ((LinearMap.restrictScalars_apply Γ(Y, V) _
      (show Γ(M, f ⁻¹ᵁ V) from x)).trans (M.basicOpenRestrict_apply _ _)).symm
    rw [LinearMap.comp_apply, he_apply, basicOpenRestrict_apply]
    dsimp only [pushforward_obj_presheaf_map]
    -- State the composite with the objects of `M`, so that `Functor.map_comp` applies.
    refine (ConcreteCategory.comp_apply
      (M.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE _)).op) e₀ x).symm.trans ?_
    rw [← Functor.map_comp]
    -- Both sides restrict `x` between the same opens; morphisms of opens are unique.
    rfl
  rw [hcomp]
  exact this

/-- **Pushforward along a quasi-compact quasi-separated morphism preserves quasi-coherence.** -/
instance isQuasicoherent_pushforward [M.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    ((pushforward f).obj M).IsQuasicoherent :=
  ((pushforward f).obj M).isQuasicoherent_iff_isLocalizedModule.2 fun V hV g ↦
    have := M.isLocalizedModule_basicOpenRestrict_of_qcqs (f.isCompact_preimage hV.isCompact)
      (f.isQuasiSeparated_preimage hV.isQuasiSeparated) (f.app V g)
    M.isLocalizedModule_basicOpenRestrict_pushforward f g

end AlgebraicGeometry.Scheme.Modules
