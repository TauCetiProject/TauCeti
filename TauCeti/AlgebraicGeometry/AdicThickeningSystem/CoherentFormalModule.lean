/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.FormalCompletion
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Coherent formal modules on adic thickening systems

A *coherent formal module* on an adic thickening system `𝔛 = (X n, ι n)` is an inverse system of
modules: a finitely presented `𝒪_{X n}`-module `F n` on every level, together with isomorphisms
`ι n ^* F (n + 1) ≅ F n` identifying each level with the reduction of the next one. Morphisms are
families of linear maps `F n ⟶ G n` compatible with these isomorphisms. For the formal completion
`X/V(I)` of a scheme `X` along `V(I)`, these are the systems `(F n)` with `F n` a finitely
presented module on `V(I ^ (n + 1))` and `F (n + 1) / I ^ (n + 1) F (n + 1) ≅ F n`. When `X` is
locally Noetherian, finitely presented and coherent modules agree, and this recovers the category
`Coh(X, I)` of coherent modules on `X/V(I)` used in the theorem on formal functions and in
Grothendieck's existence theorem (Stacks, Section 30.23); for general `X` the definition packages
finitely presented systems.

The category `CoherentFormalModule 𝔛` is preadditive, with sums and differences of morphisms
computed levelwise. The *completion functor*
`Scheme.formalCompletion.completionFunctor X I`, from finitely presented `𝒪_X`-modules to
coherent formal modules on `X.formalCompletion I`, sends `M` to the system of its restrictions
`M / I ^ (n + 1) M` to the infinitesimal neighbourhoods `V(I ^ (n + 1))`, i.e. to the pullbacks of
`M` along the closed immersions `V(I ^ (n + 1)) ⟶ X`; it is additive. Finite presentation is the
condition preserved by pullback along arbitrary morphisms of schemes, which is why the levels are
required to be finitely presented rather than merely coherent.

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule`: inverse systems of
  finitely presented modules on the levels of an adic thickening system.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Hom`: compatible families of
  linear maps, making `CoherentFormalModule 𝔛` a preadditive category.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.isoMk`: an isomorphism of
  coherent formal modules from compatible levelwise isomorphisms; a morphism is an isomorphism iff
  it is one at every level (`CoherentFormalModule.isIso_iff_forall_isIso_app`).
* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctor`: the completion functor from
  finitely presented `𝒪_X`-modules to coherent formal modules on the formal completion.

## References

* [Stacks Project, Section 30.23](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem

/-- A *coherent formal module* on an adic thickening system `𝔛`: a finitely presented
`𝒪_{X n}`-module `obj n` on each level, with isomorphisms `ι n ^* obj (n + 1) ≅ obj n` identifying
each level with the reduction of the next. -/
structure CoherentFormalModule (𝔛 : AdicThickeningSystem.{u}) where
  /-- The module on the `n`-th level `X n` of the system. -/
  obj : ∀ n, (𝔛.X n).Modules
  /-- Every level is a finitely presented module. -/
  isFinitePresentation : ∀ n, (obj n).IsFinitePresentation
  /-- The reduction of the module at level `n + 1` to level `n` is the module at level `n`. -/
  transitionIso : ∀ n, (Scheme.Modules.pullback (𝔛.ι n)).obj (obj (n + 1)) ≅ obj n

attribute [instance] CoherentFormalModule.isFinitePresentation

namespace CoherentFormalModule

variable {𝔛 : AdicThickeningSystem.{u}}

/-- A morphism of coherent formal modules is a family of linear maps `app n : M.obj n ⟶ N.obj n`
compatible with the reduction isomorphisms. -/
@[ext]
structure Hom (M N : CoherentFormalModule 𝔛) where
  /-- The component at level `n`. -/
  app : ∀ n, M.obj n ⟶ N.obj n
  /-- The reduction of the component at level `n + 1` is the component at level `n`. -/
  naturality : ∀ n, (Scheme.Modules.pullback (𝔛.ι n)).map (app (n + 1)) ≫
    (N.transitionIso n).hom = (M.transitionIso n).hom ≫ app n := by cat_disch

attribute [reassoc (attr := simp)] Hom.naturality

instance : Category (CoherentFormalModule 𝔛) where
  Hom := Hom
  id M := { app n := 𝟙 (M.obj n) }
  comp f g :=
    { app n := f.app n ≫ g.app n
      naturality n := by simp }

@[ext]
theorem hom_ext {M N : CoherentFormalModule 𝔛} {f g : M ⟶ N} (h : ∀ n, f.app n = g.app n) :
    f = g :=
  Hom.ext (funext h)

@[simp]
theorem id_app (M : CoherentFormalModule 𝔛) (n : ℕ) : (𝟙 M : M ⟶ M).app n = 𝟙 (M.obj n) :=
  (rfl)

@[reassoc, simp]
theorem comp_app {M N P : CoherentFormalModule 𝔛} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n :=
  (rfl)

/-- The inverse of a reduction isomorphism is compatible with the components of a morphism. -/
@[reassoc (attr := simp)]
theorem Hom.transitionIso_inv_naturality {M N : CoherentFormalModule 𝔛} (f : M ⟶ N) (n : ℕ) :
    (M.transitionIso n).inv ≫ (Scheme.Modules.pullback (𝔛.ι n)).map (f.app (n + 1)) =
      f.app n ≫ (N.transitionIso n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← f.naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Construct an isomorphism of coherent formal modules from levelwise isomorphisms compatible with
the reduction isomorphisms. -/
def isoMk {M N : CoherentFormalModule 𝔛} (e : ∀ n, M.obj n ≅ N.obj n)
    (h : ∀ n, (Scheme.Modules.pullback (𝔛.ι n)).map (e (n + 1)).hom ≫ (N.transitionIso n).hom =
      (M.transitionIso n).hom ≫ (e n).hom := by cat_disch) : M ≅ N where
  hom :=
    { app n := (e n).hom
      naturality := h }
  inv :=
    { app n := (e n).inv
      naturality n := by
        rw [Iso.eq_comp_inv, Category.assoc, ← h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp] }

@[simp]
theorem isoMk_hom_app {M N : CoherentFormalModule 𝔛} (e : ∀ n, M.obj n ≅ N.obj n)
    (h : ∀ n, (Scheme.Modules.pullback (𝔛.ι n)).map (e (n + 1)).hom ≫ (N.transitionIso n).hom =
      (M.transitionIso n).hom ≫ (e n).hom) (n : ℕ) :
    (isoMk e h).hom.app n = (e n).hom :=
  (rfl)

@[simp]
theorem isoMk_inv_app {M N : CoherentFormalModule 𝔛} (e : ∀ n, M.obj n ≅ N.obj n)
    (h : ∀ n, (Scheme.Modules.pullback (𝔛.ι n)).map (e (n + 1)).hom ≫ (N.transitionIso n).hom =
      (M.transitionIso n).hom ≫ (e n).hom) (n : ℕ) :
    (isoMk e h).inv.app n = (e n).inv :=
  (rfl)

/-- The component isomorphism at level `n` induced by an isomorphism of coherent formal modules. -/
def appIso {M N : CoherentFormalModule 𝔛} (e : M ≅ N) (n : ℕ) : M.obj n ≅ N.obj n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

@[simp]
theorem appIso_hom {M N : CoherentFormalModule 𝔛} (e : M ≅ N) (n : ℕ) :
    (appIso e n).hom = e.hom.app n :=
  (rfl)

@[simp]
theorem appIso_inv {M N : CoherentFormalModule 𝔛} (e : M ≅ N) (n : ℕ) :
    (appIso e n).inv = e.inv.app n :=
  (rfl)

instance isIso_app_of_isIso {M N : CoherentFormalModule 𝔛} (f : M ⟶ N) [IsIso f] (n : ℕ) :
    IsIso (f.app n) :=
  (appIso (asIso f) n).isIso_hom

/-- A morphism of coherent formal modules is an isomorphism if and only if each levelwise component
is an isomorphism of modules. -/
theorem isIso_iff_forall_isIso_app {M N : CoherentFormalModule 𝔛} (f : M ⟶ N) :
    IsIso f ↔ ∀ n, IsIso (f.app n) :=
  ⟨fun _ n ↦ inferInstance, fun h ↦
    ⟨(isoMk (fun n ↦ @asIso _ _ _ _ (f.app n) (h n)) f.naturality).inv, by ext; simp, by ext; simp⟩⟩

/-! ### The preadditive structure -/

section Preadditive

noncomputable section

variable {M N : CoherentFormalModule 𝔛}

instance : Zero (M ⟶ N) where
  zero := { app _ := 0 }

instance : Add (M ⟶ N) where
  add f g := { app n := f.app n + g.app n }

instance : Neg (M ⟶ N) where
  neg f := { app n := -f.app n }

instance : Sub (M ⟶ N) where
  sub f g := { app n := f.app n - g.app n }

instance : SMul ℕ (M ⟶ N) where
  smul k f := { app n := k • f.app n }

instance : SMul ℤ (M ⟶ N) where
  smul k f := { app n := k • f.app n }

@[simp]
theorem zero_app (n : ℕ) : (0 : M ⟶ N).app n = 0 :=
  (rfl)

@[simp]
theorem add_app (f g : M ⟶ N) (n : ℕ) : (f + g).app n = f.app n + g.app n :=
  (rfl)

@[simp]
theorem neg_app (f : M ⟶ N) (n : ℕ) : (-f).app n = -f.app n :=
  (rfl)

@[simp]
theorem sub_app (f g : M ⟶ N) (n : ℕ) : (f - g).app n = f.app n - g.app n :=
  (rfl)

@[simp]
theorem nsmul_app (k : ℕ) (f : M ⟶ N) (n : ℕ) : (k • f).app n = k • f.app n :=
  (rfl)

@[simp]
theorem zsmul_app (k : ℤ) (f : M ⟶ N) (n : ℕ) : (k • f).app n = k • f.app n :=
  (rfl)

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f : M ⟶ N ↦ f.app)
    (fun _ _ h ↦ hom_ext (congrFun h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Preadditive (CoherentFormalModule 𝔛) where
  add_comp _ _ _ _ _ _ := hom_ext fun _ ↦ Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ ↦ Preadditive.comp_add _ _ _ _ _ _

end

end Preadditive

end CoherentFormalModule

end TauCeti.AlgebraicGeometry.AdicThickeningSystem

/-! ### The completion functor -/

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The completion functor `M ↦ (M / I ^ (n + 1) M)ₙ` from finitely presented `𝒪_X`-modules to
coherent formal modules on the formal completion `X/V(I)`: its `n`-th level is the pullback of `M`
along the closed immersion `V(I ^ (n + 1)) ⟶ X`, and its reduction isomorphisms come from
`V(I ^ (n + 1)) ⟶ V(I ^ (n + 2)) ⟶ X` being the closed immersion `V(I ^ (n + 1)) ⟶ X`. -/
-- `@[expose]` is forced by dependent typing: without the levels of `(completionFunctor X I).obj M`
-- reducing definitionally to pullbacks of `M`, `completionFunctor_obj_transitionIso` and
-- `completionFunctor_map_app` do not typecheck.
@[expose]
noncomputable def completionFunctor :
    FinitelyPresentedSheaf X ⥤ CoherentFormalModule (X.formalCompletion I) where
  obj M :=
    { obj n := (Modules.pullback (toScheme X I n)).obj M.obj
      isFinitePresentation _ := Modules.isFinitePresentation_pullback _ (M := M.obj)
      transitionIso n :=
        (Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (ι_toScheme X I n)).app M.obj }
  map φ :=
    { app n := (Modules.pullback (toScheme X I n)).map φ.hom
      naturality n :=
        (Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (ι_toScheme X I n)).hom.naturality
          φ.hom }
  map_id M := CoherentFormalModule.hom_ext fun _ ↦ (Modules.pullback _).map_id M.obj
  map_comp φ ψ := CoherentFormalModule.hom_ext fun _ ↦ (Modules.pullback _).map_comp φ.hom ψ.hom

@[simp]
theorem completionFunctor_obj_obj (M : FinitelyPresentedSheaf X) (n : ℕ) :
    ((completionFunctor X I).obj M).obj n = (Modules.pullback (toScheme X I n)).obj M.obj :=
  (rfl)

@[simp]
theorem completionFunctor_obj_transitionIso (M : FinitelyPresentedSheaf X) (n : ℕ) :
    ((completionFunctor X I).obj M).transitionIso n =
      (Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (ι_toScheme X I n)).app M.obj :=
  (rfl)

@[simp]
theorem completionFunctor_map_app {M N : FinitelyPresentedSheaf X} (φ : M ⟶ N) (n : ℕ) :
    ((completionFunctor X I).map φ).app n = (Modules.pullback (toScheme X I n)).map φ.hom :=
  (rfl)

/-- The completion functor is additive, since pullback of modules is additive at every level. -/
instance completionFunctor_additive : (completionFunctor X I).Additive where
  map_add := CoherentFormalModule.hom_ext fun _ ↦ (Modules.pullback _).map_add

end AlgebraicGeometry.Scheme.formalCompletion
