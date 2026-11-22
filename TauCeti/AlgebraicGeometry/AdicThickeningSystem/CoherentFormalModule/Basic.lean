/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.FormalCompletion
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

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
computed levelwise. It has cokernels, also computed levelwise: the cokernel of a morphism of
finitely presented modules is finitely presented, and pullback along the transition maps preserves
cokernels, being a left adjoint. Consequently a morphism is an epimorphism if and only if it is one
at every level. Kernels are not computed levelwise, since pullback is only right exact; for the
formal completion of a Noetherian scheme the category is nevertheless abelian
(Stacks, Lemma 30.23.2). The *completion functor*
`Scheme.formalCompletion.completionFunctor X I`, from finitely presented `𝒪_X`-modules to
coherent formal modules on `X.formalCompletion I`, sends `M` to the system of its restrictions
`M / I ^ (n + 1) M` to the infinitesimal neighbourhoods `V(I ^ (n + 1))`, i.e. to the pullbacks of
`M` along the closed immersions `V(I ^ (n + 1)) ⟶ X`; it is additive, and restricts to finite
locally free sheaves as `Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I`. Finite
presentation is the condition preserved by pullback along arbitrary morphisms of schemes, which is
why the levels are required to be finitely presented rather than merely coherent.

Coherent formal modules pull back along morphisms `g : 𝔛 ⟶ 𝔜` of adic thickening systems, level by
level. Pulling back along the morphism of formal completions induced by the inclusion of an open
subscheme `U ⊆ X` restricts a coherent formal module on `X/V(I)` to `U/V(I|_U)`, and being an
isomorphism is a local property: a morphism of coherent formal modules on `X/V(I)` is an
isomorphism as soon as its restrictions to the members of an open cover of `X` are. This is how
statements about the category of coherent formal modules on the formal completion of a Noetherian
scheme reduce to affine opens, where it is described by finite modules over the completed ring
(Stacks, Lemmas 30.23.1 and 30.23.2).

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule`: inverse systems of
  finitely presented modules on the levels of an adic thickening system.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Hom`: compatible families of
  linear maps, making `CoherentFormalModule 𝔛` a preadditive category.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.isoMk`: an isomorphism of
  coherent formal modules from compatible levelwise isomorphisms; a morphism is an isomorphism iff
  it is one at every level (`CoherentFormalModule.isIso_iff_forall_isIso_app`).
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.cokernelCocone`: the
  levelwise cokernel of a morphism, a cokernel by
  `CoherentFormalModule.cokernelIsColimit`; a morphism is an epimorphism if and only if it is one at
  every level (`CoherentFormalModule.epi_iff_forall_epi_app`).
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.pullback`: the pullback of
  coherent formal modules along a morphism of adic thickening systems, an additive functor
  preserving epimorphisms, equipped with identity and composition isomorphisms (`pullbackId`,
  `pullbackComp`) and inducing an equivalence along isomorphisms (`pullbackEquiv`).
* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctor`: the completion functor from
  finitely presented `𝒪_X`-modules to coherent formal modules on the formal completion, an
  equivalence for the zero ideal sheaf `⊥` (`isEquivalence_completionFunctor_bot`).
* `AlgebraicGeometry.Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor`: its restriction
  to `FiniteLocallyFreeSheaf X`.

## Main results

* `CoherentFormalModule.isIso_iff_of_isOpenCover_opensRange`: a morphism of coherent formal
  modules is an isomorphism if and only if its pullbacks along a family of morphisms of adic
  thickening systems that are levelwise open covers are.
* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_of_isFiniteLocallyFree`: under faithfulness of
  `finiteLocallyFreeCompletionFunctor X I`, morphisms of finite locally free `𝒪_X`-modules are
  determined by their pullbacks to all levels of `X.formalCompletion I`.
* `AlgebraicGeometry.Scheme.formalCompletion.isIso_iff_of_isOpenCover`: a morphism of coherent
  formal modules on `X/V(I)` is an isomorphism if and only if its restrictions to the formal
  completions of the members of an open cover of `X` are.
* `AlgebraicGeometry.Scheme.formalCompletion.isEquivalence_completionFunctor_bot`: completing along
  `V(⊥) = X` induces an equivalence of categories on every scheme `X`.

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

/-- Evaluation of a coherent formal module on `𝔛` at level `n`. -/
-- `@[expose]` is forced by dependent typing: `(eval 𝔛 n).obj M` must reduce definitionally to
-- `M.obj n` so that `eval_map` and lifted functor properties typecheck.
@[expose, simps]
def eval (𝔛 : AdicThickeningSystem.{u}) (n : ℕ) :
    CoherentFormalModule 𝔛 ⥤ (𝔛.X n).Modules where
  obj M := M.obj n
  map f := f.app n

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

/-- A coherent formal module is zero if and only if each of its levels is zero. -/
theorem isZero_iff_forall_isZero_obj (M : CoherentFormalModule 𝔛) :
    IsZero M ↔ ∀ n, IsZero (M.obj n) := by
  simp only [IsZero.iff_id_eq_zero]
  exact ⟨fun h n ↦ by rw [← id_app, h, zero_app], fun h ↦ hom_ext fun n ↦ by simp [h n]⟩

end

end Preadditive

/-! ### Cokernels -/

section Cokernels

noncomputable section

variable {M N : CoherentFormalModule 𝔛} (f : M ⟶ N)

/-- The reduction isomorphisms of the levelwise cokernel: pullback along `ι n` preserves the
cokernel of `f.app (n + 1)`, which the reduction isomorphisms of `M` and `N` then identify with the
cokernel of `f.app n`. -/
def cokernelTransitionIso (n : ℕ) :
    (Scheme.Modules.pullback (𝔛.ι n)).obj (cokernel (f.app (n + 1))) ≅ cokernel (f.app n) :=
  PreservesCokernel.iso _ _ ≪≫
    cokernel.mapIso _ _ (M.transitionIso n) (N.transitionIso n) (f.naturality n)

@[reassoc (attr := simp)]
theorem map_π_cokernelTransitionIso_hom (n : ℕ) :
    (Scheme.Modules.pullback (𝔛.ι n)).map (cokernel.π (f.app (n + 1))) ≫
        (cokernelTransitionIso f n).hom =
      (N.transitionIso n).hom ≫ cokernel.π (f.app n) := by
  simp [cokernelTransitionIso]

/-- The cokernel of a morphism `f : M ⟶ N` of coherent formal modules, computed levelwise: its
`n`-th level is the cokernel of `f.app n`, which is finitely presented, and its reduction
isomorphisms come from pullback along `ι n` preserving cokernels. -/
-- `@[expose]` is forced by dependent typing: without the levels of `(cokernelCocone f).pt`
-- reducing definitionally to `cokernel (f.app n)`, `cokernelCocone_pt_transitionIso` and
-- `cokernelCocone_π_app` do not typecheck.
@[expose]
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ
    (Z := ⟨fun n ↦ cokernel (f.app n), fun n ↦
      have := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj n)
      have := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (M.obj n)
      inferInstance, cokernelTransitionIso f⟩)
    { app n := cokernel.π (f.app n) } (by ext n; simp)

@[simp]
theorem cokernelCocone_pt_obj (n : ℕ) : (cokernelCocone f).pt.obj n = cokernel (f.app n) :=
  (rfl)

@[simp]
theorem cokernelCocone_pt_transitionIso (n : ℕ) :
    (cokernelCocone f).pt.transitionIso n = cokernelTransitionIso f n :=
  (rfl)

@[simp]
theorem cokernelCocone_π_app (n : ℕ) :
    (Cofork.π (cokernelCocone f)).app n = cokernel.π (f.app n) :=
  (rfl)

private lemma π_app_comp_eq_zero (s : CokernelCofork f) (n : ℕ) :
    f.app n ≫ (Cofork.π s).app n = 0 := by
  rw [← comp_app, CokernelCofork.condition, zero_app]

/-- The levelwise descents through the cokernels of a cokernel cofork are compatible with the
reduction isomorphisms. -/
private lemma desc_naturality (s : CokernelCofork f) (n : ℕ) :
    (Scheme.Modules.pullback (𝔛.ι n)).map
        (cokernel.desc (f.app (n + 1)) ((Cofork.π s).app (n + 1)) (π_app_comp_eq_zero f s _)) ≫
        (s.pt.transitionIso n).hom =
      (cokernelTransitionIso f n).hom ≫
        cokernel.desc (f.app n) ((Cofork.π s).app n) (π_app_comp_eq_zero f s n) := by
  refine (cancel_epi ((Scheme.Modules.pullback (𝔛.ι n)).map (cokernel.π (f.app (n + 1))))).mp ?_
  rw [← Functor.map_comp_assoc, cokernel.π_desc, map_π_cokernelTransitionIso_hom_assoc,
    cokernel.π_desc, Hom.naturality]

/-- The levelwise cokernel is a cokernel in the category of coherent formal modules. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s ↦
      { app n := cokernel.desc (f.app n) ((Cofork.π s).app n) (π_app_comp_eq_zero f s n)
        naturality := desc_naturality f s })
    (fun s ↦ hom_ext fun n ↦ cokernel.π_desc _ _ _)
    (fun s m hm ↦ hom_ext fun n ↦ (cancel_epi (cokernel.π (f.app n))).mp <| by
      rw [cokernel.π_desc]
      exact congrArg (·.app n) hm)

instance : HasCokernels (CoherentFormalModule 𝔛) where
  has_colimit f := ⟨⟨_, cokernelIsColimit f⟩⟩

/-- A morphism of coherent formal modules is an epimorphism if and only if it is one at every
level. -/
theorem epi_iff_forall_epi_app : Epi f ↔ ∀ n, Epi (f.app n) := by
  rw [Preadditive.epi_iff_isZero_cokernel' _ (cokernelIsColimit f), isZero_iff_forall_isZero_obj]
  exact forall_congr' fun n ↦ (Preadditive.epi_iff_isZero_cokernel (f.app n)).symm

end

end Cokernels

/-! ### Pullback along morphisms of adic thickening systems -/

section Pullback

noncomputable section

variable {𝔜 : AdicThickeningSystem.{u}}

/-- The pullback of a coherent formal module on `𝔜` along a morphism `g : 𝔛 ⟶ 𝔜` of adic
thickening systems: its `n`-th level is the pullback of the `n`-th level along `g.app n`, which is
finitely presented, and its reduction isomorphisms are those of the original module, transported
along the squares `𝔛.ι n ≫ g.app (n + 1) = g.app n ≫ 𝔜.ι n`. For the morphism of formal
completions induced by an open immersion, this is the restriction of a coherent formal module to an
open subscheme. -/
-- `@[expose]` is forced by dependent typing: without the levels of `(pullback g).obj M` reducing
-- definitionally to pullbacks of the levels of `M`, `pullback_obj_transitionIso_hom` and
-- `pullback_map_app` do not typecheck.
@[expose]
def pullback (g : 𝔛 ⟶ 𝔜) : CoherentFormalModule 𝔜 ⥤ CoherentFormalModule 𝔛 where
  obj M :=
    { obj n := (Scheme.Modules.pullback (g.app n)).obj (M.obj n)
      isFinitePresentation _ := inferInstance
      transitionIso n :=
        (Scheme.Modules.pullbackSquareIso (g.naturality n)).app (M.obj (n + 1)) ≪≫
          (Scheme.Modules.pullback (g.app n)).mapIso (M.transitionIso n) }
  map {M N} φ :=
    { app n := (Scheme.Modules.pullback (g.app n)).map (φ.app n)
      naturality n := by
        simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
        rw [← Functor.comp_map, NatTrans.naturality_assoc, Functor.comp_map, ← Functor.map_comp,
          Hom.naturality, Functor.map_comp] }
  map_id M := hom_ext fun n ↦ (Scheme.Modules.pullback (g.app n)).map_id (M.obj n)
  map_comp φ ψ := hom_ext fun n ↦
    (Scheme.Modules.pullback (g.app n)).map_comp (φ.app n) (ψ.app n)

@[simp]
theorem pullback_obj_obj (g : 𝔛 ⟶ 𝔜) (M : CoherentFormalModule 𝔜) (n : ℕ) :
    ((pullback g).obj M).obj n = (Scheme.Modules.pullback (g.app n)).obj (M.obj n) :=
  (rfl)

@[simp]
theorem pullback_obj_transitionIso_hom (g : 𝔛 ⟶ 𝔜) (M : CoherentFormalModule 𝔜) (n : ℕ) :
    (((pullback g).obj M).transitionIso n).hom =
      (Scheme.Modules.pullbackComp (𝔛.ι n) (g.app (n + 1))).hom.app (M.obj (n + 1)) ≫
        (Scheme.Modules.pullbackCongr (g.naturality n)).hom.app (M.obj (n + 1)) ≫
          (Scheme.Modules.pullbackComp (g.app n) (𝔜.ι n)).inv.app (M.obj (n + 1)) ≫
            (Scheme.Modules.pullback (g.app n)).map (M.transitionIso n).hom := by
  simp [pullback]

@[simp]
theorem pullback_map_app (g : 𝔛 ⟶ 𝔜) {M N : CoherentFormalModule 𝔜} (φ : M ⟶ N) (n : ℕ) :
    ((pullback g).map φ).app n = (Scheme.Modules.pullback (g.app n)).map (φ.app n) :=
  (rfl)

/-- Pullback of coherent formal modules is additive, since pullback of modules is additive at
every level. -/
instance pullback_additive (g : 𝔛 ⟶ 𝔜) : (pullback g).Additive where
  map_add := hom_ext fun _ ↦ (Scheme.Modules.pullback _).map_add

/-- Pullback of coherent formal modules preserves epimorphisms, since these are the levelwise
epimorphisms and pullback of modules is a left adjoint. -/
instance pullback_preservesEpimorphisms (g : 𝔛 ⟶ 𝔜) : (pullback g).PreservesEpimorphisms where
  preserves φ _ := (epi_iff_forall_epi_app _).mpr fun n ↦ by
    have := (epi_iff_forall_epi_app φ).mp ‹_› n
    exact Functor.map_epi (Scheme.Modules.pullback (g.app n)) (φ.app n)

/-- **Isomorphisms of coherent formal modules are local.** Let `g i : 𝔘 i ⟶ 𝔛` be morphisms of
adic thickening systems such that at every level `n` the components `(g i).app n` are open
immersions whose images cover `𝔛.X n`. Then a morphism of coherent formal modules on `𝔛` is an
isomorphism if and only if its pullbacks along all `g i` are. -/
theorem isIso_iff_of_isOpenCover_opensRange {ι : Type*} {𝔘 : ι → AdicThickeningSystem.{u}}
    (g : ∀ i, 𝔘 i ⟶ 𝔛) [∀ i n, IsOpenImmersion ((g i).app n)]
    (hg : ∀ n, TopologicalSpace.IsOpenCover fun i ↦ ((g i).app n).opensRange)
    {M N : CoherentFormalModule 𝔛} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso ((pullback (g i)).map φ) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ (isIso_iff_forall_isIso_app φ).mpr fun n ↦ ?_⟩
  refine (Scheme.Modules.isIso_iff_of_isOpenCover_opensRange _ (hg n) _).mpr fun i ↦ ?_
  rw [← pullback_map_app]
  exact (isIso_iff_forall_isIso_app _).mp (h i) n

/-- Equal morphisms of adic thickening systems induce naturally isomorphic pullback functors. -/
def pullbackCongr {f g : 𝔛 ⟶ 𝔜} (h : f = g) : pullback f ≅ pullback g :=
  eqToIso (h ▸ rfl)

@[simp]
theorem pullbackCongr_hom_app_app {f g : 𝔛 ⟶ 𝔜} (h : f = g) (M : CoherentFormalModule 𝔜) (n : ℕ) :
    ((pullbackCongr h).hom.app M).app n =
      (Scheme.Modules.pullbackCongr (congrArg (·.app n) h)).hom.app (M.obj n) := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, id_app,
    Scheme.Modules.pullbackCongr]
  rfl

@[simp]
theorem pullbackCongr_inv_app_app {f g : 𝔛 ⟶ 𝔜} (h : f = g) (M : CoherentFormalModule 𝔜) (n : ℕ) :
    ((pullbackCongr h).inv.app M).app n =
      (Scheme.Modules.pullbackCongr (congrArg (·.app n) h)).inv.app (M.obj n) := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, id_app,
    Scheme.Modules.pullbackCongr]
  rfl

/-- Pulling coherent formal modules back along the identity morphism of an adic thickening system
is naturally isomorphic to the identity functor. -/
def pullbackId (𝔛 : AdicThickeningSystem.{u}) :
    pullback (𝟙 𝔛) ≅ 𝟭 (CoherentFormalModule 𝔛) :=
  NatIso.ofComponents
    (fun M ↦ isoMk
      (fun n ↦ (Scheme.Modules.pullbackCongr (AdicThickeningSystem.id_app 𝔛 n)).app (M.obj n) ≪≫
        (Scheme.Modules.pullbackId (𝔛.X n)).app (M.obj n))
      fun n ↦ by
        have w : 𝔛.ι n ≫ 𝟙 (𝔛.X (n + 1)) = 𝟙 (𝔛.X n) ≫ 𝔛.ι n := by simp
        simp only [pullback, Functor.id_obj, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Functor.map_comp, Category.assoc]
        rw [← Scheme.Modules.pullbackSquareIso_id_hom_app_assoc (𝔛.ι n) w (M.obj (n + 1))
            (M.transitionIso n).hom,
          Scheme.Modules.pullbackSquareIso_congr_assoc (AdicThickeningSystem.id_app 𝔛 n)
            (AdicThickeningSystem.id_app 𝔛 (n + 1))
            (AdicThickeningSystem.Hom.naturality (𝟙 𝔛) n) w (M.obj (n + 1)),
          (Scheme.Modules.pullbackCongr
            (AdicThickeningSystem.id_app 𝔛 n)).hom.naturality_assoc (M.transitionIso n).hom,
          (Scheme.Modules.pullbackId (𝔛.X n)).hom.naturality (M.transitionIso n).hom,
          Functor.id_map])
    fun φ ↦ hom_ext fun n ↦ by
      simp only [pullback, Functor.id_obj, Functor.id_map, comp_app, isoMk_hom_app, Iso.trans_hom,
        Iso.app_hom, Category.assoc]
      rw [(Scheme.Modules.pullbackCongr (AdicThickeningSystem.id_app 𝔛 n)).hom.naturality_assoc,
        (Scheme.Modules.pullbackId (𝔛.X n)).hom.naturality, Functor.id_map]

@[simp]
theorem pullbackId_hom_app_app (𝔛 : AdicThickeningSystem.{u}) (M : CoherentFormalModule 𝔛)
    (n : ℕ) :
    ((pullbackId 𝔛).hom.app M).app n =
      (Scheme.Modules.pullbackCongr (AdicThickeningSystem.id_app 𝔛 n)).hom.app (M.obj n) ≫
        (Scheme.Modules.pullbackId (𝔛.X n)).hom.app (M.obj n) := by
  rfl

@[simp]
theorem pullbackId_inv_app_app (𝔛 : AdicThickeningSystem.{u}) (M : CoherentFormalModule 𝔛)
    (n : ℕ) :
    ((pullbackId 𝔛).inv.app M).app n =
      (Scheme.Modules.pullbackId (𝔛.X n)).inv.app (M.obj n) ≫
        (Scheme.Modules.pullbackCongr (AdicThickeningSystem.id_app 𝔛 n)).inv.app (M.obj n) := by
  rfl

/-- Pulling coherent formal modules back along a composite `f ≫ g` is naturally isomorphic to
pulling back along `g` and then along `f`. -/
def pullbackComp {𝔗 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔗) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun M ↦ isoMk
      (fun n ↦ (Scheme.Modules.pullbackComp (f.app n) (g.app n)).app (M.obj n) ≪≫
        (Scheme.Modules.pullbackCongr (AdicThickeningSystem.comp_app f g n).symm).app (M.obj n))
      fun n ↦ by
        have wfg : 𝔛.ι n ≫ (f.app (n + 1) ≫ g.app (n + 1)) =
            (f.app n ≫ g.app n) ≫ 𝔗.ι n := by
          rw [← Category.assoc, f.naturality n, Category.assoc, g.naturality n, Category.assoc]
        simp only [pullback, Functor.comp_obj, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
          Functor.map_comp, Category.assoc]
        rw [Scheme.Modules.pullbackSquareIso_congr_assoc
            (AdicThickeningSystem.comp_app f g n).symm
            (AdicThickeningSystem.comp_app f g (n + 1)).symm wfg
            (AdicThickeningSystem.Hom.naturality (f ≫ g) n) (M.obj (n + 1)),
          Scheme.Modules.pullback_map_pullbackComp_hom_app_comp_pullbackSquareIso_hom_app_assoc
            (f.naturality n) (g.naturality n) wfg (M.obj (n + 1)),
          ← (Scheme.Modules.pullbackCongr
            (AdicThickeningSystem.comp_app f g n).symm).hom.naturality (M.transitionIso n).hom,
          ← (Scheme.Modules.pullbackComp (f.app n) (g.app n)).hom.naturality_assoc
            (M.transitionIso n).hom,
          Functor.comp_map])
    fun φ ↦ hom_ext fun n ↦ by
      simp only [pullback, Functor.comp_obj, Functor.comp_map, comp_app, isoMk_hom_app,
        Iso.trans_hom, Iso.app_hom, Category.assoc]
      rw [← Functor.comp_map,
        (Scheme.Modules.pullbackComp (f.app n) (g.app n)).hom.naturality_assoc,
        (Scheme.Modules.pullbackCongr
          (AdicThickeningSystem.comp_app f g n).symm).hom.naturality]

@[simp]
theorem pullbackComp_hom_app_app {𝔗 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔗)
    (M : CoherentFormalModule 𝔗) (n : ℕ) :
    ((pullbackComp f g).hom.app M).app n =
      (Scheme.Modules.pullbackComp (f.app n) (g.app n)).hom.app (M.obj n) ≫
        (Scheme.Modules.pullbackCongr (AdicThickeningSystem.comp_app f g n).symm).hom.app
          (M.obj n) := by
  rfl

@[simp]
theorem pullbackComp_inv_app_app {𝔗 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔗)
    (M : CoherentFormalModule 𝔗) (n : ℕ) :
    ((pullbackComp f g).inv.app M).app n =
      (Scheme.Modules.pullbackCongr (AdicThickeningSystem.comp_app f g n).symm).inv.app
          (M.obj n) ≫
        (Scheme.Modules.pullbackComp (f.app n) (g.app n)).inv.app (M.obj n) := by
  rfl

/-- `pullbackCongr` along `rfl` is the identity isomorphism. -/
@[simp]
theorem pullbackCongr_refl (f : 𝔛 ⟶ 𝔜) : pullbackCongr (rfl : f = f) = Iso.refl _ := by
  simp [pullbackCongr]

/-- `pullbackCongr` respects transitivity of morphism equalities. -/
theorem pullbackCongr_trans {f g h : 𝔛 ⟶ 𝔜} (h₁ : f = g) (h₂ : g = h) :
    pullbackCongr (h₁.trans h₂) = pullbackCongr h₁ ≪≫ pullbackCongr h₂ := by
  subst h₁ h₂
  simp [pullbackCongr]

/-- Compatibility of `pullbackComp` with replacing the first morphism by an equal one. -/
@[reassoc]
theorem pullbackCongr_hom_whiskerLeft_pullbackComp_hom {𝔗 : AdicThickeningSystem.{u}}
    {f f' : 𝔛 ⟶ 𝔜} (hf : f = f') (g : 𝔜 ⟶ 𝔗) :
    Functor.whiskerLeft (pullback g) (pullbackCongr hf).hom ≫ (pullbackComp f' g).hom =
      (pullbackComp f g).hom ≫ (pullbackCongr (congrArg (· ≫ g) hf)).hom := by
  subst hf
  simp

/-- Compatibility of `pullbackComp` with replacing the second morphism by an equal one. -/
@[reassoc]
theorem pullbackComp_hom_comp_pullbackCongr_hom {𝔗 : AdicThickeningSystem.{u}}
    (f : 𝔛 ⟶ 𝔜) {g g' : 𝔜 ⟶ 𝔗} (hg : g = g') :
    Functor.whiskerRight (pullbackCongr hg).hom (pullback f) ≫ (pullbackComp f g').hom =
      (pullbackComp f g).hom ≫ (pullbackCongr (congrArg (f ≫ ·) hg)).hom := by
  subst hg
  simp

/-- Associativity of pullback of coherent formal modules: the two ways of identifying
`pullback h ⋙ pullback g ⋙ pullback f` with `pullback (f ≫ g ≫ h)` agree. -/
@[reassoc]
theorem pullbackComp_assoc {𝔗 𝔘 : AdicThickeningSystem.{u}}
    (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔗) (h : 𝔗 ⟶ 𝔘) :
    Functor.whiskerLeft (pullback h) (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom ≫
        (pullbackCongr (Category.assoc f g h)).hom =
      (Functor.associator (pullback h) (pullback g) (pullback f)).inv ≫
        Functor.whiskerRight (pullbackComp g h).hom (pullback f) ≫
          (pullbackComp f (g ≫ h)).hom := by
  refine NatTrans.ext (funext fun M ↦ hom_ext fun n ↦ ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_obj, pullback]
  simp only [Category.id_comp, comp_app, pullbackComp_hom_app_app,
    pullbackCongr_hom_app_app, Functor.map_comp, Category.assoc]
  rw [Scheme.Modules.pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc]
  have hr : (Scheme.Modules.pullback (f.app n)).map
        ((Scheme.Modules.pullbackCongr (AdicThickeningSystem.comp_app g h n).symm).hom.app
          (M.obj n)) ≫
      (Scheme.Modules.pullbackComp (f.app n) ((g ≫ h).app n)).hom.app (M.obj n) =
    (Scheme.Modules.pullbackComp (f.app n) (g.app n ≫ h.app n)).hom.app (M.obj n) ≫
      eqToHom (by rw [AdicThickeningSystem.comp_app]) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp (f.app n) (g.app n ≫ h.app n)).inv.app
      (M.obj n)), Iso.inv_hom_id_app_assoc]
    rw [Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% hr,
    Scheme.Modules.pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc]
  simp [Scheme.Modules.pullbackCongr]

/-- Component form of `pullbackComp_assoc` at a coherent formal module `M`. -/
@[reassoc]
theorem pullbackComp_assoc_app {𝔗 𝔘 : AdicThickeningSystem.{u}}
    (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔗) (h : 𝔗 ⟶ 𝔘) (M : CoherentFormalModule 𝔘) :
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M ≫
        (pullbackCongr (Category.assoc f g h)).hom.app M =
      (pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M := by
  simpa using NatTrans.congr_app (pullbackComp_assoc f g h) M

/-- Left unitality of pullback of coherent formal modules: `pullbackComp f (𝟙 𝔜)` agrees with
`pullbackId 𝔜` up to `pullbackCongr (Category.comp_id f)`. -/
@[reassoc]
theorem pullbackComp_id (f : 𝔛 ⟶ 𝔜) :
    (pullbackComp f (𝟙 𝔜)).hom ≫ (pullbackCongr (Category.comp_id f)).hom =
      Functor.whiskerRight (pullbackId 𝔜).hom (pullback f) ≫
        (Functor.leftUnitor (pullback f)).hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine hom_ext fun n ↦ ?_
  dsimp only [Functor.comp_obj, pullback]
  simp only [comp_app, pullbackComp_hom_app_app,
    pullbackCongr_hom_app_app, pullbackId_hom_app_app, Functor.map_comp,
    Category.assoc]
  have hid := Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app
    (f.app n) (AdicThickeningSystem.id_app 𝔜 n) (M.obj n)
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (f.app n)
    ((𝟙 𝔜 : 𝔜 ⟶ 𝔜).app n)).inv.app (M.obj n)), Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hid, Scheme.Modules.pseudofunctor_left_unitality_app]
  simp [Scheme.Modules.pullbackCongr]

/-- Component form of `pullbackComp_id` at a coherent formal module `M`. -/
@[reassoc]
theorem pullbackComp_id_app (f : 𝔛 ⟶ 𝔜) (M : CoherentFormalModule 𝔜) :
    (pullbackComp f (𝟙 𝔜)).hom.app M ≫ (pullbackCongr (Category.comp_id f)).hom.app M =
      (pullback f).map ((pullbackId 𝔜).hom.app M) := by
  simpa using NatTrans.congr_app (pullbackComp_id f) M

/-- Right unitality of pullback of coherent formal modules: `pullbackComp (𝟙 𝔛) f` agrees with
`pullbackId 𝔛` up to `pullbackCongr (Category.id_comp f)`. -/
@[reassoc]
theorem pullback_id_comp (f : 𝔛 ⟶ 𝔜) :
    (pullbackComp (𝟙 𝔛) f).hom ≫ (pullbackCongr (Category.id_comp f)).hom =
      Functor.whiskerLeft (pullback f) (pullbackId 𝔛).hom ≫
        (Functor.rightUnitor (pullback f)).hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine hom_ext fun n ↦ ?_
  dsimp only [Functor.comp_obj, pullback]
  simp only [comp_app, pullbackComp_hom_app_app,
    pullbackCongr_hom_app_app, pullbackId_hom_app_app, Category.assoc]
  rw [← cancel_epi ((Scheme.Modules.pullbackCongr (AdicThickeningSystem.id_app 𝔛 n).symm).hom.app
    ((Scheme.Modules.pullback (f.app n)).obj (M.obj n)))]
  rw [Scheme.Modules.pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc
    (AdicThickeningSystem.id_app 𝔛 n).symm (f.app n) (M.obj n)]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 (𝔛.X n)) (f.app n)).inv.app (M.obj n)),
    Iso.inv_hom_id_app_assoc]
  have hid := Scheme.Modules.pseudofunctor_right_unitality_app (f.app n) (M.obj n)
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, NatTrans.id_app,
    eqToHom_refl, Category.id_comp] at hid ⊢
  rw [hid]
  simp

/-- Component form of `pullback_id_comp` at a coherent formal module `M`. -/
@[reassoc]
theorem pullback_id_comp_app (f : 𝔛 ⟶ 𝔜) (M : CoherentFormalModule 𝔜) :
    (pullbackComp (𝟙 𝔛) f).hom.app M ≫ (pullbackCongr (Category.id_comp f)).hom.app M =
      (pullbackId 𝔛).hom.app ((pullback f).obj M) := by
  simpa using NatTrans.congr_app (pullback_id_comp f) M

/-- An isomorphism `e : 𝔛 ≅ 𝔜` of adic thickening systems induces an equivalence of categories of
coherent formal modules by pullback along `e.hom` and `e.inv`. -/
-- `@[expose]` is forced by dependent typing: clients must identify the types of
-- `(pullbackEquiv e).unitIso` and `(pullbackEquiv e).counitIso` with the pullback coherence
-- isomorphisms.
@[expose]
def pullbackEquiv (e : 𝔛 ≅ 𝔜) : CoherentFormalModule 𝔜 ≌ CoherentFormalModule 𝔛 :=
  CategoryTheory.Equivalence.mk' (pullback e.hom) (pullback e.inv)
    ((pullbackId 𝔜).symm ≪≫ pullbackCongr e.inv_hom_id.symm ≪≫ (pullbackComp e.inv e.hom).symm)
    (pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId 𝔛)
    fun M ↦ hom_ext fun n ↦ by
      have htri := (Scheme.Modules.pullbackEquiv
        { hom := e.hom.app n
          inv := e.inv.app n
          hom_inv_id := congrArg (·.app n) e.hom_inv_id
          inv_hom_id := congrArg (·.app n) e.inv_hom_id }).functor_unitIso_comp (M.obj n)
      dsimp only [CategoryTheory.Equivalence.unit, CategoryTheory.Equivalence.counit,
        Scheme.Modules.pullbackEquiv] at htri
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, comp_app, pullback_map_app,
        pullbackId_inv_app_app, pullbackId_hom_app_app, pullbackComp_hom_app_app,
        pullbackComp_inv_app_app, pullbackCongr_hom_app_app, Functor.map_comp,
        Category.assoc] at htri ⊢
      simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app,
        eqToHom_refl] at htri ⊢
      exact htri

@[simp]
theorem pullbackEquiv_functor (e : 𝔛 ≅ 𝔜) : (pullbackEquiv e).functor = pullback e.hom := by
  rfl

@[simp]
theorem pullbackEquiv_inverse (e : 𝔛 ≅ 𝔜) : (pullbackEquiv e).inverse = pullback e.inv := by
  rfl

/-- The unit isomorphism of `pullbackEquiv e` is the pullback coherence isomorphism
`(pullbackId 𝔜).symm ≪≫ pullbackCongr e.inv_hom_id.symm ≪≫ (pullbackComp e.inv e.hom).symm`. -/
theorem pullbackEquiv_unitIso (e : 𝔛 ≅ 𝔜) :
    (pullbackEquiv e).unitIso =
      (pullbackId 𝔜).symm ≪≫ pullbackCongr e.inv_hom_id.symm ≪≫ (pullbackComp e.inv e.hom).symm :=
  (rfl)

/-- The counit isomorphism of `pullbackEquiv e` is the pullback coherence isomorphism
`pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId 𝔛`. -/
theorem pullbackEquiv_counitIso (e : 𝔛 ≅ 𝔜) :
    (pullbackEquiv e).counitIso =
      pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId 𝔛 :=
  (rfl)

/-- On components, the unit of `pullbackEquiv e` factors through `pullbackId`, `pullbackCongr`,
and `pullbackComp`. -/
@[simp]
theorem pullbackEquiv_unitIso_hom_app (e : 𝔛 ≅ 𝔜) (M : CoherentFormalModule 𝔜) :
    (pullbackEquiv e).unitIso.hom.app M =
      (pullbackId 𝔜).inv.app M ≫ (pullbackCongr e.inv_hom_id.symm).hom.app M ≫
        (pullbackComp e.inv e.hom).inv.app M :=
  (rfl)

/-- On components, the inverse unit of `pullbackEquiv e` factors through `pullbackComp`,
`pullbackCongr`, and `pullbackId`. -/
@[simp]
theorem pullbackEquiv_unitIso_inv_app (e : 𝔛 ≅ 𝔜) (M : CoherentFormalModule 𝔜) :
    (pullbackEquiv e).unitIso.inv.app M =
      (pullbackComp e.inv e.hom).hom.app M ≫ (pullbackCongr e.inv_hom_id.symm).inv.app M ≫
        (pullbackId 𝔜).hom.app M :=
  (rfl)

/-- On components, the counit of `pullbackEquiv e` factors through `pullbackComp`, `pullbackCongr`,
and `pullbackId`. -/
@[simp]
theorem pullbackEquiv_counitIso_hom_app (e : 𝔛 ≅ 𝔜) (M : CoherentFormalModule 𝔛) :
    (pullbackEquiv e).counitIso.hom.app M =
      (pullbackComp e.hom e.inv).hom.app M ≫ (pullbackCongr e.hom_inv_id).hom.app M ≫
        (pullbackId 𝔛).hom.app M :=
  (rfl)

/-- On components, the inverse counit of `pullbackEquiv e` factors through `pullbackId`,
`pullbackCongr`, and `pullbackComp`. -/
@[simp]
theorem pullbackEquiv_counitIso_inv_app (e : 𝔛 ≅ 𝔜) (M : CoherentFormalModule 𝔛) :
    (pullbackEquiv e).counitIso.inv.app M =
      (pullbackId 𝔛).inv.app M ≫ (pullbackCongr e.hom_inv_id).inv.app M ≫
        (pullbackComp e.hom e.inv).inv.app M :=
  (rfl)

instance isEquivalence_pullback (g : 𝔛 ⟶ 𝔜) [IsIso g] : (pullback g).IsEquivalence :=
  (pullbackEquiv (asIso g)).isEquivalence_functor

end

end Pullback

end CoherentFormalModule

end TauCeti.AlgebraicGeometry.AdicThickeningSystem

/-! ### The completion functor -/

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

section General

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

/-- The restriction of `completionFunctor X I` to finite locally free sheaves on `X`, sending `E`
to the coherent formal module `(E / I ^ (n + 1) E)ₙ` on `X.formalCompletion I`. Because this is an
abbreviation for `FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ completionFunctor X I`, `Full`
and `Faithful` instances on `completionFunctor X I` restrict automatically to
`finiteLocallyFreeCompletionFunctor X I`. -/
noncomputable abbrev finiteLocallyFreeCompletionFunctor :
    FiniteLocallyFreeSheaf X ⥤ CoherentFormalModule (X.formalCompletion I) :=
  FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ completionFunctor X I

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, two morphisms between finite locally
free `𝒪_X`-modules are equal as soon as their pullbacks to all levels `V(I ^ (n + 1))` of the
formal completion agree. -/
theorem hom_ext_of_isFiniteLocallyFree {X : Scheme.{u}} (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {M N : X.Modules} (hM : Modules.isFiniteLocallyFree X M)
    (hN : Modules.isFiniteLocallyFree X N) {f g : M ⟶ N}
    (h : ∀ n, (Modules.pullback (toScheme X I n)).map f =
      (Modules.pullback (toScheme X I n)).map g) :
    f = g := by
  let E : FiniteLocallyFreeSheaf X := ⟨M, hM⟩
  let F : FiniteLocallyFreeSheaf X := ⟨N, hN⟩
  let fE : E ⟶ F := ObjectProperty.homMk f
  let gE : E ⟶ F := ObjectProperty.homMk g
  have hfg : (finiteLocallyFreeCompletionFunctor X I).map fE =
      (finiteLocallyFreeCompletionFunctor X I).map gE :=
    CoherentFormalModule.hom_ext h
  exact congrArg (·.hom) ((finiteLocallyFreeCompletionFunctor X I).map_injective hfg)

/-- **Isomorphisms of coherent formal modules on a formal completion are local on the scheme.** For
an open cover `U` of `X`, a morphism of coherent formal modules on `X/V(I)` is an isomorphism if
and only if its restrictions to the formal completions `U i/V(I|_{U i})` are. -/
theorem isIso_iff_of_isOpenCover {ι : Type*} {U : ι → X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) {M N : CoherentFormalModule (X.formalCompletion I)}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso ((CoherentFormalModule.pullback (map (I := I.comap (U i).ι)
      (U i).ι le_rfl)).map φ) :=
  CoherentFormalModule.isIso_iff_of_isOpenCover_opensRange _ (fun n ↦ by
    simp only [opensRange_map_app, Scheme.Opens.opensRange_ι]
    exact hU.comap (toScheme X I n).base.hom) φ

end General

section Bot

variable (X : Scheme.{u})

instance faithful_completionFunctor_bot : (completionFunctor X ⊥).Faithful where
  map_injective {_ _} _ _ h :=
    ObjectProperty.hom_ext _ <|
      (Modules.pullback (toScheme X ⊥ 0)).map_injective (congrArg (·.app 0) h)

instance full_completionFunctor_bot : (completionFunctor X ⊥).Full where
  map_surjective {M N} f := by
    let g : M ⟶ N := ObjectProperty.homMk ((Modules.pullback (toScheme X ⊥ 0)).preimage (f.app 0))
    refine ⟨g, CoherentFormalModule.hom_ext fun n ↦ ?_⟩
    induction n with
    | zero => exact (Modules.pullback (toScheme X ⊥ 0)).map_preimage (f.app 0)
    | succ n ih =>
      refine (Modules.pullback ((X.formalCompletion ⊥).ι n)).map_injective
        ((cancel_mono (((completionFunctor X ⊥).obj N).transitionIso n).hom).mp ?_)
      exact (((completionFunctor X ⊥).map g).naturality n).trans
        ((congrArg (fun u ↦ (((completionFunctor X ⊥).obj M).transitionIso n).hom ≫ u) ih).trans
          (f.naturality n).symm)

/-- Recovering a finitely presented `𝒪_X`-module from a coherent formal module on `X/V(⊥)` by
evaluating at level `0` and pulling back along `inv (toScheme X ⊥ 0)`. -/
-- `@[expose]` is forced by dependent typing: `((completionFunctorBotInv X).obj N).obj` must reduce
-- definitionally to `(Modules.pullback (inv (toScheme X ⊥ 0))).obj (N.obj 0)` so that
-- `completionFunctorBotInv_map_hom` typechecks.
@[expose, simps! obj_obj map_hom]
noncomputable def completionFunctorBotInv :
    CoherentFormalModule (X.formalCompletion ⊥) ⥤ FinitelyPresentedSheaf X :=
  (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).lift
    (CoherentFormalModule.eval (X.formalCompletion ⊥) 0 ⋙
      Modules.pullback (inv (toScheme X ⊥ 0)))
    fun N ↦ Modules.isFinitePresentation_pullback _ (M := N.obj 0)

/-- Composing `completionFunctorBotInv X` with the inclusion into `X.Modules` gives evaluation at
level `0` followed by pullback along `inv (toScheme X ⊥ 0)`. -/
theorem completionFunctorBotInv_comp_ι :
    completionFunctorBotInv X ⋙ ObjectProperty.ι _ =
      CoherentFormalModule.eval (X.formalCompletion ⊥) 0 ⋙
        Modules.pullback (inv (toScheme X ⊥ 0)) :=
  (rfl)

private noncomputable def botCompletionLevelIso (N : CoherentFormalModule (X.formalCompletion ⊥)) :
    ∀ n, ((completionFunctor X ⊥).obj ((completionFunctorBotInv X).obj N)).obj n ≅ N.obj n
  | 0 => (Modules.pullbackComp (toScheme X ⊥ 0) (inv (toScheme X ⊥ 0)) ≪≫
      Modules.pullbackCongr (IsIso.hom_inv_id (toScheme X ⊥ 0)) ≪≫
      Modules.pullbackId _).app (N.obj 0)
  | n + 1 =>
    (Functor.FullyFaithful.ofFullyFaithful
      (Modules.pullback ((X.formalCompletion ⊥).ι n))).preimageIso
        ((((completionFunctor X ⊥).obj _).transitionIso n) ≪≫ botCompletionLevelIso N n ≪≫
          (N.transitionIso n).symm)

private lemma botCompletionLevelIso_naturality
    {M N : CoherentFormalModule (X.formalCompletion ⊥)} (φ : M ⟶ N) (n : ℕ) :
    ((completionFunctor X ⊥).map ((completionFunctorBotInv X).map φ)).app n ≫
        (botCompletionLevelIso X N n).hom =
      (botCompletionLevelIso X M n).hom ≫ φ.app n := by
  induction n with
  | zero =>
    exact (Modules.pullbackComp (toScheme X ⊥ 0) (inv (toScheme X ⊥ 0)) ≪≫
      Modules.pullbackCongr (IsIso.hom_inv_id (toScheme X ⊥ 0)) ≪≫
      Modules.pullbackId _).hom.naturality (φ.app 0)
  | succ n ih =>
    refine (Modules.pullback ((X.formalCompletion ⊥).ι n)).map_injective ?_
    have hpre (P : CoherentFormalModule (X.formalCompletion ⊥)) :
        (Modules.pullback ((X.formalCompletion ⊥).ι n)).map
            (botCompletionLevelIso X P (n + 1)).hom =
          (((completionFunctor X ⊥).obj ((completionFunctorBotInv X).obj P)).transitionIso n).hom ≫
            (botCompletionLevelIso X P n).hom ≫ (P.transitionIso n).inv :=
      (Functor.FullyFaithful.ofFullyFaithful
        (Modules.pullback ((X.formalCompletion ⊥).ι n))).map_preimage _
    rw [Functor.map_comp, Functor.map_comp, hpre N, hpre M,
      CoherentFormalModule.Hom.naturality_assoc, Category.assoc,
      ← Category.assoc ((completionFunctor X ⊥).map ((completionFunctorBotInv X).map φ) |>.app n),
      ih, Category.assoc, Category.assoc, ← CoherentFormalModule.Hom.transitionIso_inv_naturality,
      ← Category.assoc, ← Category.assoc]

private noncomputable def botCompletionCounitIso :
    completionFunctorBotInv X ⋙ completionFunctor X ⊥ ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun N ↦ CoherentFormalModule.isoMk (botCompletionLevelIso X N) fun n ↦ by
      have h := (Functor.FullyFaithful.ofFullyFaithful
        (Modules.pullback ((X.formalCompletion ⊥).ι n))).map_preimage
          ((((completionFunctor X ⊥).obj _).transitionIso n) ≪≫ botCompletionLevelIso X N n ≪≫
            (N.transitionIso n).symm).hom
      dsimp only [Functor.comp_obj]
      refine (congrArg (· ≫ (N.transitionIso n).hom) h).trans ?_
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id])
    fun φ ↦ CoherentFormalModule.hom_ext (botCompletionLevelIso_naturality X φ)

instance essSurj_completionFunctor_bot : (completionFunctor X ⊥).EssSurj where
  mem_essImage N :=
    ⟨(completionFunctorBotInv X).obj N, ⟨(botCompletionCounitIso X).app N⟩⟩

/-- On any scheme `X`, completing along the zero ideal sheaf `⊥` (`V(⊥) = X`) is an equivalence of
categories. -/
instance isEquivalence_completionFunctor_bot : (completionFunctor X ⊥).IsEquivalence where

/-- The chosen inverse `(completionFunctor X ⊥).inv` of zero-ideal completion is naturally
isomorphic to `completionFunctorBotInv X`, which evaluates at level `0` and pulls back along
`inv (toScheme X ⊥ 0)`. -/
noncomputable def completionFunctorBotInvIso :
    (completionFunctor X ⊥).inv ≅ completionFunctorBotInv X :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (botCompletionCounitIso X).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (completionFunctor X ⊥).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- On underlying `X.Modules`, `(completionFunctor X ⊥).inv` is naturally isomorphic to evaluation
at level `0` followed by pullback along `inv (toScheme X ⊥ 0)`. -/
noncomputable def completionFunctorBotInvCompιIso :
    (completionFunctor X ⊥).inv ⋙ ObjectProperty.ι _ ≅
      CoherentFormalModule.eval (X.formalCompletion ⊥) 0 ⋙
        Modules.pullback (inv (toScheme X ⊥ 0)) :=
  Functor.isoWhiskerRight (completionFunctorBotInvIso X) _

end Bot

end AlgebraicGeometry.Scheme.formalCompletion
