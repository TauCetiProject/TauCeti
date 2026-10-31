/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Stalk

/-!
# Stalks of quasi-coherent modules

For a point `x` of an affine open `U` of a scheme `X`, the stalk `M_x` of a quasi-coherent
`𝒪_X`-module `M` is the localization of the sections `Γ(M, U)` at the prime ideal of `Γ(X, U)`
corresponding to `x`, through the germ map (Hartshorne, Proposition II.5.1(b)). Equivalently, the
germ map exhibits `M_x` as the base change `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`, since the local ring
`𝒪_{X,x}` is itself that localization of `Γ(X, U)` (Mathlib's
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`).

This is the affine computation of the stalks of a quasi-coherent module, and so of its fibres
`M_x ⊗ κ(x)` at points.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germₗ`: for quasi-coherent `M` and affine
  `U`, the germ map `Γ(M, U) → M_x` (`AlgebraicGeometry.Scheme.Modules.germₗ`) is the
  localization at the prime ideal of `x`;
* `AlgebraicGeometry.Scheme.Modules.isBaseChange_germₗ`: equivalently, it is the base change along
  `Γ(X, U) ⟶ 𝒪_{X,x}`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.1(b) and Lemma II.5.3.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (x : U)

variable {M x}

/-- If `x` lies in the basic open of `f ∈ Γ(X, U)`, the powers of `f` avoid the prime ideal of
`Γ(X, U)` corresponding to `x`. -/
private lemma mem_primeCompl_of_mem_powers (hU : IsAffineOpen U) {f c : Γ(X, U)}
    (hx : (x : X) ∈ X.basicOpen f) (hc : c ∈ Submonoid.powers f) :
    c ∈ (hU.primeIdealOf x).asIdeal.primeCompl := by
  have := hU.isLocalization_stalk x
  obtain ⟨n, rfl⟩ := hc
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x), map_pow]
  exact ((X.mem_basicOpen' f x).1 hx).pow n

variable (M x)

/-- **Stalks of quasi-coherent modules are localizations.** For a quasi-coherent `𝒪_X`-module `M`
and a point `x` of an affine open `U`, the germ map `Γ(M, U) → M_x` is the localization at the
prime ideal of `Γ(X, U)` corresponding to `x`. -/
theorem isLocalizedModule_germₗ [M.IsQuasicoherent] (hU : IsAffineOpen U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (M.germₗ x) where
  map_units s := by
    have := hU.isLocalization_stalk x
    -- `s` acts on `M_x` through its germ, which is a unit of `𝒪_{X,x}`.
    obtain ⟨u, hu⟩ := IsLocalization.map_units (X.presheaf.stalk x) s
    have key (m : M.presheaf.stalk x) :
        algebraMap Γ(X, U) (Module.End Γ(X, U) (M.presheaf.stalk x)) s m =
          (u : X.presheaf.stalk x) • m := by
      rw [Module.algebraMap_end_apply, section_smul_stalk_def, hu,
        TopCat.Presheaf.stalk_open_algebraMap]
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b h ↦ ?_, fun b ↦ ⟨(↑u⁻¹ : X.presheaf.stalk x) • b, ?_⟩⟩
    · rw [key, key] at h
      simpa only [smul_smul, Units.inv_mul, one_smul] using
        congrArg ((↑u⁻¹ : X.presheaf.stalk x) • ·) h
    · rw [key, smul_smul, Units.mul_inv, one_smul]
  surj y := by
    obtain ⟨V, hxV, m, rfl⟩ := M.presheaf.exists_germ_eq y
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ x.2
    have := M.isLocalizedModule_basicOpenRestrict hU f
    obtain ⟨⟨a, c⟩, hac⟩ := IsLocalizedModule.surj (Submonoid.powers f) (M.basicOpenRestrict f)
      (M.presheaf.map (homOfLE hfV).op m)
    refine ⟨⟨a, ⟨c, mem_primeCompl_of_mem_powers hU hxf c.2⟩⟩, ?_⟩
    -- Take germs at `x` of the equation `c • m|_{D(f)} = a|_{D(f)}` over `D(f)`.
    have h := congrArg (M.presheaf.germ (X.basicOpen f) x hxf) hac
    rw [basicOpenRestrict_apply, M.presheaf.germ_res_apply, Submonoid.smul_def,
      basicOpen_smul_def, M.germ_smul, M.presheaf.germ_res_apply,
      X.presheaf.germ_res_apply] at h
    rw [germₗ_apply, Submonoid.smul_def, section_smul_stalk_def]
    exact h
  exists_of_eq {a b} h := by
    rw [germₗ_apply, germₗ_apply] at h
    obtain ⟨W, hxW, iU, iU', hab⟩ := M.presheaf.germ_eq x x.2 x.2 a b h
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ x.2
    have := M.isLocalizedModule_basicOpenRestrict hU f
    -- Restriction to `D(f)` factors through the neighbourhood `W` where `a` and `b` agree.
    have hres (i : W ⟶ U) (m : Γ(M, U)) :
        M.basicOpenRestrict f m = M.presheaf.map (homOfLE hfW).op (M.presheaf.map i.op m) := by
      rw [basicOpenRestrict_apply, ← M.presheaf.map_comp_apply, ← op_comp]
      rfl
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := M.basicOpenRestrict f) (x₁ := a) (x₂ := b) (by rw [hres iU, hres iU', hab])
    exact ⟨⟨c, mem_primeCompl_of_mem_powers hU hxf c.2⟩, hc⟩

/-- **Stalks of quasi-coherent modules by base change.** For a quasi-coherent `𝒪_X`-module `M`
and a point `x` of an affine open `U`, the germ map `Γ(M, U) → M_x` exhibits `M_x` as the base
change `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(M, U)`. -/
theorem isBaseChange_germₗ [M.IsQuasicoherent] (hU : IsAffineOpen U) :
    IsBaseChange (X.presheaf.stalk x) (M.germₗ x) :=
  have := hU.isLocalization_stalk x
  have := M.isLocalizedModule_germₗ x hU
  IsLocalizedModule.isBaseChange (hU.primeIdealOf x).asIdeal.primeCompl _ _

end AlgebraicGeometry.Scheme.Modules
