/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.AlgebraicGeometry.AffineScheme

/-!
# Stalks of quasi-coherent modules

Let `M` be an `𝒪_X`-module on a scheme `X`, let `U` be an open of `X` and let `x ∈ U`. Taking
germs is a `Γ(X, U)`-linear map `Γ(M, U) → M_x` (`Scheme.Modules.germLinearMap`). If `M` is
quasi-coherent and `U` is affine, this map is the localization of `Γ(M, U)` at the prime
ideal `𝔭_x ⊂ Γ(X, U)` of `x` (`Scheme.Modules.isLocalizedModule_germLinearMap`). This is the module
counterpart of `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` for the structure sheaf, and
the scheme-level form of the fact that the stalk of `M~` at `𝔭` is `M_𝔭` (Hartshorne,
Proposition II.5.1(b)). Since `𝒪_{X,x}` is the localization of `Γ(X, U)` at the same prime, the
germ map also exhibits `M_x` as the base change `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`
(`Scheme.Modules.isBaseChange_germLinearMap`).

The proof reduces to sections over basic opens: every germ is the germ of a section over a basic
open `D(f) ∋ x`, and sections over `D(f)` are the localization of `Γ(M, U)` at `f`
(`Scheme.Modules.isLocalizedModule_basicOpenRestrict`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germLinearMap`: for quasi-coherent `M` and
  affine `U`, the germ map is the localization at the prime ideal of `x`;
* `AlgebraicGeometry.Scheme.Modules.isBaseChange_germLinearMap`: for quasi-coherent `M` and affine
  `U`, the germ map exhibits `M_x` as `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.1(b).
* The Stacks Project, [Tag 01HR](https://stacks.math.columbia.edu/tag/01HR).
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- The germ at `x` of a section over a basic open `X.basicOpen f ∋ x`, multiplied by a function
on `U` through the `Γ(X, U)`-module structure of `Γ(M, X.basicOpen f)`, is the germ of the
function times the germ of the section. -/
private lemma germ_basicOpen_smul (f : Γ(X, U)) (x : U) (hx : (x : X) ∈ X.basicOpen f)
    (r : Γ(X, U)) (m : Γ(M, X.basicOpen f)) :
    M.presheaf.germ _ x hx (r • m) = r • M.presheaf.germ _ x hx m := by
  rw [basicOpen_smul_def, germ_smul, ← algebraMap_smul_stalk, TopCat.Presheaf.stalk_open_algebraMap]
  congr 1
  exact TopCat.Presheaf.germ_res_apply ..

/-- **Stalks of a quasi-coherent module are localizations.** For a quasi-coherent `𝒪_X`-module
`M`, an affine open `U` and a point `x ∈ U`, the germ map `Γ(M, U) → M_x` is the localization of
`Γ(M, U)` at the prime ideal of `Γ(X, U)` corresponding to `x`. -/
theorem isLocalizedModule_germLinearMap [M.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (M.germLinearMap x) where
  map_units s := by
    have := hU.isLocalization_stalk x
    -- A function outside the prime ideal acts on `M_x` through a unit of `𝒪_{X,x}`.
    obtain ⟨u, hu⟩ := IsLocalization.map_units (X.presheaf.stalk x) s
    have h : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) (M.presheaf.stalk x)) s) = (u • ·) :=
      funext fun m ↦ by
        rw [Module.algebraMap_end_apply, ← algebraMap_smul_stalk, ← hu, Units.smul_def]
    rw [Module.End.isUnit_iff, h]
    exact MulAction.bijective u
  surj y := by
    -- Write `y` as the germ of a section over a basic open `D(f) ∋ x`, and that section as a
    -- fraction with denominator a power of `f`.
    obtain ⟨V, hxV, m, rfl⟩ := M.presheaf.exists_germ_eq y
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ x.2
    have := M.isLocalizedModule_basicOpenRestrict hU f
    obtain ⟨⟨n, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (M.basicOpenRestrict f) (M.presheaf.map (homOfLE hfV).op m)
    refine ⟨⟨n, ⟨f ^ k, pow_mem ((hU.mem_basicOpen_iff_notMem_primeIdealOf x.2 f).1 hxf) k⟩⟩, ?_⟩
    have h' := congrArg (M.presheaf.germ _ x hxf) h
    rw [Submonoid.smul_def, germ_basicOpen_smul, basicOpenRestrict_apply,
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h'
    rw [Submonoid.smul_def, germLinearMap_apply]
    exact h'
  exists_of_eq {m₁ m₂} h := by
    -- Equal germs agree on a basic open `D(f) ∋ x`, so they agree in `Γ(M, U)` after
    -- multiplication by a power of `f`.
    rw [germLinearMap_apply, germLinearMap_apply] at h
    obtain ⟨W, hxW, i₁, i₂, hW⟩ := M.presheaf.germ_eq x x.2 x.2 m₁ m₂ h
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ x.2
    have hres : M.basicOpenRestrict f m₁ = M.basicOpenRestrict f m₂ := by
      -- Morphisms of opens are unique, so both restrictions factor through `W`.
      have e₁ : (homOfLE (X.basicOpen_le f)).op = i₁.op ≫ (homOfLE hfW).op :=
        Subsingleton.elim _ _
      have e₂ : (homOfLE (X.basicOpen_le f)).op = i₂.op ≫ (homOfLE hfW).op :=
        Subsingleton.elim _ _
      rw [basicOpenRestrict_apply, basicOpenRestrict_apply]
      nth_rw 1 [e₁]
      rw [e₂, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, hW]
    have := M.isLocalizedModule_basicOpenRestrict hU f
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) hres
    exact ⟨⟨f ^ k, pow_mem ((hU.mem_basicOpen_iff_notMem_primeIdealOf x.2 f).1 hxf) k⟩, hk⟩

/-- For a quasi-coherent `𝒪_X`-module `M`, an affine open `U` and `x ∈ U`, the germ map
`Γ(M, U) → M_x` exhibits the stalk `M_x` as the base change `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`. -/
theorem isBaseChange_germLinearMap [M.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.presheaf.stalk x) (M.germLinearMap x) :=
  have := hU.isLocalization_stalk x
  have := M.isLocalizedModule_germLinearMap hU x
  IsLocalizedModule.isBaseChange (hU.primeIdealOf x).asIdeal.primeCompl _ _

end AlgebraicGeometry.Scheme.Modules
