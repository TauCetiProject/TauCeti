/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
public import TauCeti.Topology.Sheaves.Flasque.Locality
public import TauCeti.Topology.Sheaves.Flasque.Module

/-!
# Flasque resolutions compute the derived functors of global sections

Let `R` be a commutative ring and `X` a topological space. Flasque sheaves of `R`-modules form a
class adapted to the global sections functor `Γ`, in the sense of
`TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`: injective sheaves are flasque, the
cokernel of a monomorphism between flasque sheaves is flasque, and `Γ` keeps a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `F₁` flasque exact, since sections of `F₃` lift to `F₂`. Hence a
flasque resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` computes the right derived functors of `Γ`:
`RⁿΓ(F) ≅ Hⁿ(Γ(K))`. No hypothesis is made on `X`.

The right derived functors of `Γ` are Mathlib's `CategoryTheory.Functor.rightDerived`, defined
through injective resolutions. Additivity of `Γ`, which they require, is kept as an instance
argument.

## Main definitions and results

* `CategoryTheory.ShortComplex.ShortExact.map_Γ_of_isFlasque`: `Γ` keeps a short exact sequence
  of sheaves of `R`-modules whose first term is flasque short exact, over any ring `R`.
* `CategoryTheory.Sheaf.isFlasque`: flasque sheaves, as a class of objects closed under
  isomorphisms.
* `CategoryTheory.Sheaf.quasiIso_map_Γ_of_isFlasque`: for a flasque resolution `K` and a
  comparison map `φ : K ⟶ I` to an injective resolution, `Γ(φ)` is a quasi-isomorphism.
* `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque`: `RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque
  resolution `K` of `F`, characterized through any injective resolution and comparison map by
  `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A and
  Lemma III.2.4.
* The Stacks Project, Cohomology of Sheaves, Lemma 20.12.3 (tag 09SY), and Derived Categories,
  Lemma 13.15.6 (tag 05T8).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace CochainComplex

universe u

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

/-- **Global sections are exact on flasque kernels.** If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact
sequence of sheaves of `R`-modules with `F₁` flasque, then
`0 ⟶ Γ(F₁) ⟶ Γ(F₂) ⟶ Γ(F₃) ⟶ 0` is short exact. -/
theorem map_Γ_of_isFlasque
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hS : S.ShortExact) [TopCat.Presheaf.IsFlasque S.X₁.obj] :
    (S.map (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact := by
  obtain ⟨h, hm⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).1 inferInstance S hS
  refine ShortComplex.ShortExact.mk' h hm ?_
  -- `Γ` is the functor of sections over `X`, on which `F₂ ⟶ F₃` is surjective
  let e := Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R) isTerminalTop
  have : Epi (((sheafSections _ _).obj (Opposite.op ⊤)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).2 (hS.surjective_app_of_isFlasque (Opposite.op ⊤))
  have hg : (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map S.g =
      e.hom.app _ ≫ ((sheafSections _ _).obj (Opposite.op ⊤)).map S.g ≫ e.inv.app _ := by
    rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  dsimp
  rw [hg]
  infer_instance

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.Sheaf

/-- Flasque sheaves on `X` with values in `A`, as a class of objects. -/
def isFlasque (X : TopCat.{u}) (A : Type*) [Category* A] :
    ObjectProperty (Sheaf (Opens.grothendieckTopology X) A) :=
  fun G ↦ TopCat.Presheaf.IsFlasque G.obj

/-- A sheaf satisfies `isFlasque` exactly when its underlying presheaf is flasque. -/
@[simp]
lemma isFlasque_iff {X : TopCat.{u}} {A : Type*} [Category* A]
    {G : Sheaf (Opens.grothendieckTopology X) A} :
    isFlasque X A G ↔ TopCat.Presheaf.IsFlasque G.obj :=
  Iff.rfl

/-- A sheaf isomorphic to a flasque sheaf is flasque. -/
instance {X : TopCat.{u}} {A : Type*} [Category* A] :
    (isFlasque X A).IsClosedUnderIsomorphisms where
  of_iso e h := @TopCat.Presheaf.IsFlasque.of_iso _ _ _ _ _ ((sheafToPresheaf _ _).mapIso e) h

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

variable {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι] (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

omit [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive] in
private lemma isFlasque_X₃
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (h₂ : isFlasque X _ S.X₂) : isFlasque X _ S.X₃ :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := h₁
  have : TopCat.Presheaf.IsFlasque S.X₂.obj := h₂
  hS.isFlasque_X₃_of_isFlasque

private lemma shortExact_map_Γ_of_isFlasque
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (_ : isFlasque X _ S.X₂) :
    (S.map (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := h₁
  hS.map_Γ_of_isFlasque

include hK in
/-- **Flasque resolutions compute the derived functors of global sections.** For a flasque
resolution `ι : F[0] ⟶ K` of a sheaf of `R`-modules `F` and a morphism `φ : K ⟶ I` compatible
with `ι` and an injective resolution `I` of `F`, the map of global sections `Γ(K) ⟶ Γ(I)` is a
quasi-isomorphism. -/
theorem quasiIso_map_Γ_of_isFlasque (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex)
    (hφ : ι ≫ φ = I.ι) :
    QuasiIso (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).map
      φ) :=
  InjectiveResolution.quasiIso_map_of_comp_eq (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) (fun _ _ ↦ isFlasque_of_injective_moduleCat _) isFlasque_X₃
    shortExact_map_Γ_of_isFlasque ι hK I φ hφ

include hK in
/-- **`RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque resolution `K` of `F`.** The isomorphism is induced by
global sections of any comparison map from `K` to an injective resolution of `F`
(`CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap`). -/
noncomputable def rightDerivedΓObjIsoOfIsFlasque (n : ℕ) :
    ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj K) :=
  Functor.rightDerivedObjIsoOfResolution (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) (fun _ _ ↦ isFlasque_of_injective_moduleCat _) isFlasque_X₃
    shortExact_map_Γ_of_isFlasque ι hK n

/-- The isomorphism `rightDerivedΓObjIsoOfIsFlasque` is compatible with the identification of
`RⁿΓ(F)` through any injective resolution `I` of `F` and any comparison map `φ : K ⟶ I`. -/
@[reassoc]
lemma rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap (n : ℕ) (I : InjectiveResolution F)
    (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    (rightDerivedΓObjIsoOfIsFlasque ι hK n).hom ≫
      (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _) ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ =
          (I.isoRightDerivedObj (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom :=
  Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap _ _ _ _ _ ι hK n I φ hφ

end CategoryTheory.Sheaf
