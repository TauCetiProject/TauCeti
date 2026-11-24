/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Stalk maps of morphisms of `𝒪_X`-modules

A morphism `φ : M ⟶ N` of `𝒪_X`-modules induces, at every point `x`, a map of stalks
`M_x → N_x` sending the germ of a section `m` to the germ of `φ m`. It is `𝒪_{X,x}`-linear
(`AlgebraicGeometry.Scheme.Modules.Hom.stalkₗ`).

An epimorphism between quasi-coherent modules is surjective on sections over affine opens, and so
on every stalk (`AlgebraicGeometry.Scheme.Modules.Hom.stalkₗ_surjective_of_epi`).
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The map on stalks at `x` of a morphism `φ : M ⟶ N` of `𝒪_X`-modules, as an
`𝒪_{X,x}`-linear map `M_x → N_x`. -/
def Hom.stalkₗ (φ : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor _ x).map φ.mapPresheaf
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, b, rfl⟩ := M.presheaf.exists_germ_eq m
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx a,
      ← M.presheaf.germ_res_apply (homOfLE inf_le_right) x hx b, ← M.germ_smul, RingHom.id_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
      mapPresheaf_app, Hom.app_smul, N.germ_smul]

/-- The stalk map sends the germ of a section `m` to the germ of `φ m`. -/
@[simp]
theorem Hom.stalkₗ_germ (φ : M ⟶ N) (U : X.Opens) (x : X) (hx : x ∈ U) (m : Γ(M, U)) :
    φ.stalkₗ x (M.presheaf.germ U x hx m) = N.presheaf.germ U x hx (φ.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf m

/-- An epimorphism between quasi-coherent `𝒪_X`-modules is surjective on every stalk. -/
theorem Hom.stalkₗ_surjective_of_epi (φ : M ⟶ N) [Epi φ] [M.IsQuasicoherent]
    [N.IsQuasicoherent] (x : X) : Function.Surjective (φ.stalkₗ x) := by
  intro n
  obtain ⟨U, hxU, s, rfl⟩ := N.presheaf.exists_germ_eq n
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨m, hm⟩ :=
    φ.app_surjective_of_epi_of_isAffineOpen V hV (N.presheaf.map (homOfLE hVU).op s)
  refine ⟨M.presheaf.germ V x hxV m, ?_⟩
  rw [stalkₗ_germ, hm]
  exact TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hVU) x hxV s

end AlgebraicGeometry.Scheme.Modules
