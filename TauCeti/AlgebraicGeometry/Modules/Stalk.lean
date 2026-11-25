/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.CommRingCat
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Module structures on scheme-module stalks

The stalk of an `𝒪_X`-module carries the action of the original commutative local ring
`𝒪_{X,x}`. This exposes Mathlib's presheaf stalk action through the scheme-module presentation.

For a point `x` of an open `U`, the stalk `M_x` is also a `Γ(X, U)`-module through the germ map
`Γ(X, U) ⟶ 𝒪_{X,x}` (`AlgebraicGeometry.Scheme.Modules.moduleSectionStalk`), and the germ map
`Γ(M, U) → M_x` is `Γ(X, U)`-linear (`AlgebraicGeometry.Scheme.Modules.germₗ`).

A morphism `φ : M ⟶ N` of `𝒪_X`-modules induces, at every point `x`, an `𝒪_{X,x}`-linear map of
stalks `M_x → N_x` sending the germ of a section `m` to the germ of `φ m`
(`AlgebraicGeometry.Scheme.Modules.Hom.stalkₗ`). An epimorphism of `𝒪_X`-modules is surjective on
every stalk (`AlgebraicGeometry.Scheme.Modules.Hom.stalkₗ_surjective_of_epi`).

A morphism of `𝒪_X`-modules which is surjective on sections over every open contained in `U` has
a cokernel with zero stalks at the points of `U`
(`AlgebraicGeometry.Scheme.Modules.Hom.subsingleton_stalk_cokernel_of_surjective_app`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (x : X)

/-- The stalk of a scheme module is a module over the scheme's commutative local ring. -/
instance stalkModule : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  let Q : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) := M.val
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) Q.presheaf x))

/-- The module germ of a scalar multiple is the local-ring germ acting on the module germ. -/
theorem germ_smul (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(M, U)) :
    M.presheaf.germ U x hx (r • m) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx m :=
  M.val.germ_smul (R := X.presheaf) x U hx r m

section Section

variable {U : X.Opens} (x : U)

/-- For a point `x` of an open `U`, the stalk `M_x` is a `Γ(X, U)`-module through the germ map
`Γ(X, U) ⟶ 𝒪_{X,x}`, which is Mathlib's algebra structure
`TopCat.Presheaf.algebra_section_stalk`. -/
instance moduleSectionStalk : Module Γ(X, U) (M.presheaf.stalk x) :=
  Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk x))

/-- The `Γ(X, U)`-module structure on `M_x` factors through the local ring `𝒪_{X,x}`. -/
instance isScalarTower_sectionStalk :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  IsScalarTower.of_compHom _ _ _

/-- A function `r` on `U` acts on the stalk `M_x` through its germ at `x`. -/
lemma section_smul_stalk_def (r : Γ(X, U)) (m : M.presheaf.stalk x) :
    r • m = X.presheaf.germ U x x.property r • m :=
  (rfl)

/-- The germ map `Γ(M, U) → M_x` at a point `x` of `U`, as a `Γ(X, U)`-linear map. This is the
linear form of `PresheafOfModules.germSemilinear`, which is semilinear along
`Γ(X, U) ⟶ 𝒪_{X,x}`; localization of modules is phrased for linear maps. -/
def germₗ : Γ(M, U) →ₗ[Γ(X, U)] M.presheaf.stalk x where
  toFun := M.presheaf.germ U x x.property
  map_add' := map_add _
  map_smul' r m := M.germ_smul x U x.property r m

@[simp]
lemma germₗ_apply (m : Γ(M, U)) : M.germₗ x m = M.presheaf.germ U x x.property m :=
  (rfl)

end Section

/-- If a morphism of `𝒪_X`-modules is surjective on sections over every open contained in `U`, its
cokernel has zero stalks at the points of `U`. -/
theorem Hom.subsingleton_stalk_cokernel_of_surjective_app {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) {U : X.Opens} {x : X} (hx : x ∈ U)
    (hφ : ∀ W ≤ U, Function.Surjective (φ.app W)) :
    Subsingleton ((cokernel φ).presheaf.stalk x) := by
  refine subsingleton_of_forall_eq 0 fun a ↦ ?_
  obtain ⟨W, hxW, τ, rfl⟩ := (cokernel φ).presheaf.exists_germ_eq a
  -- The cokernel map is locally surjective, so near `x` the section `τ` lifts to `N`.
  let F := TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X
  have : Sheaf.IsLocallySurjective (F.map (cokernel.π φ)) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := _)).mpr inferInstance
  obtain ⟨V, j, ⟨m, hm⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (F.map (cokernel.π φ)).hom τ x hxW
  -- On `V ⊓ U` the lift is in the image of `φ`, so `τ` vanishes there.
  let k : V ⊓ U ⟶ V := homOfLE inf_le_left
  obtain ⟨b, hb⟩ := hφ (V ⊓ U) inf_le_right (N.presheaf.map k.op m)
  have hzero : (cokernel φ).presheaf.map (k ≫ j).op τ = 0 := by
    have hnat : (cokernel.π φ).app (V ⊓ U) (N.presheaf.map k.op m) =
        (cokernel φ).presheaf.map k.op ((cokernel.π φ).app V m) :=
      (cokernel.π φ).mapPresheaf.naturality_apply k.op m
    have hcomp : (cokernel.π φ).app (V ⊓ U) (φ.app (V ⊓ U) b) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, cokernel.condition]
      simp
    rw [← hb, hcomp] at hnat
    -- `hm` says that the lift `m` maps to the restriction of `τ` to `V`.
    have hm' : (cokernel.π φ).app V m = (cokernel φ).presheaf.map j.op τ := hm
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hm', ← hnat]
  rw [← (cokernel φ).presheaf.germ_res_apply (k ≫ j) x ⟨hxV, hx⟩, hzero, map_zero]

section Hom

variable {M} {N P : X.Modules}

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

/-- The underlying function of the linear stalk map is the stalk functor applied to the morphism
of underlying presheaves. -/
theorem Hom.coe_stalkₗ (φ : M ⟶ N) (x : X) :
    ⇑(φ.stalkₗ x) = (TopCat.Presheaf.stalkFunctor _ x).map φ.mapPresheaf :=
  (rfl)

/-- The stalk map sends the germ of a section `m` to the germ of `φ m`. -/
@[simp]
theorem Hom.stalkₗ_germ (φ : M ⟶ N) (U : X.Opens) (x : X) (hx : x ∈ U) (m : Γ(M, U)) :
    φ.stalkₗ x (M.presheaf.germ U x hx m) = N.presheaf.germ U x hx (φ.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf m

/-- The stalk map of the identity is the identity. -/
@[simp]
theorem Hom.stalkₗ_id (x : X) : (𝟙 M : M ⟶ M).stalkₗ x = LinearMap.id := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  simp

/-- The stalk map of the zero morphism is zero. -/
@[simp]
theorem Hom.stalkₗ_zero (x : X) : (0 : M ⟶ N).stalkₗ x = 0 := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  simp

/-- The stalk map of a composite is the composite of the stalk maps. -/
@[simp]
theorem Hom.stalkₗ_comp (φ : M ⟶ N) (ψ : N ⟶ P) (x : X) :
    (φ ≫ ψ).stalkₗ x = ψ.stalkₗ x ∘ₗ φ.stalkₗ x := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  simp

/-- An epimorphism of `𝒪_X`-modules is surjective on every stalk. -/
theorem Hom.stalkₗ_surjective_of_epi (φ : M ⟶ N) [Epi φ] (x : X) :
    Function.Surjective (φ.stalkₗ x) := by
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map φ)).mpr inferInstance
  rw [TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf_map_hom] at h
  rw [Hom.coe_stalkₗ]
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp h x

end Hom

end AlgebraicGeometry.Scheme.Modules
