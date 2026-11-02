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

## Main results

* `CategoryTheory.Sheaf.shortExact_map_Γ_of_isFlasque`: `Γ` keeps a short exact sequence of
  sheaves of `R`-modules whose first term is flasque short exact.
* `CategoryTheory.Sheaf.quasiIso_map_Γ_of_isFlasque`: for a flasque resolution `K` and a
  comparison map `φ : K ⟶ I` to an injective resolution, `Γ(φ)` is a quasi-isomorphism.
* `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque`: `RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque
  resolution `K` of `F`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A and
  Lemma III.2.4.
* The Stacks Project, Cohomology of Sheaves, Lemma 20.12.3 (tag 09SY), and Derived Categories,
  Lemma 13.15.6 (tag 05T8).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace CochainComplex

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

/-- **Global sections are exact on flasque kernels.** If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact
sequence of sheaves of `R`-modules with `F₁` flasque, then
`0 ⟶ Γ(F₁) ⟶ Γ(F₂) ⟶ Γ(F₃) ⟶ 0` is short exact. -/
theorem shortExact_map_Γ_of_isFlasque
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hS : S.ShortExact) [TopCat.Presheaf.IsFlasque S.X₁.obj] :
    (S.map (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact := by
  obtain ⟨h, hm⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).1 inferInstance S hS
  refine ShortComplex.ShortExact.mk' h hm ?_
  -- `Γ` is the functor of sections over `X`, on which `F₂ ⟶ F₃` is surjective
  let e := ΓNatIsoSheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R) isTerminalTop
  have : Epi (((sheafSections _ _).obj (op ⊤)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).2 (hS.surjective_app_of_isFlasque (op ⊤))
  have hg : (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map S.g =
      e.hom.app _ ≫ ((sheafSections _ _).obj (op ⊤)).map S.g ≫ e.inv.app _ := by
    rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  dsimp
  rw [hg]
  infer_instance

variable {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι] (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

/-- Flasque sheaves, as a class of objects closed under isomorphisms. -/
private abbrev isFlasqueProperty :
    ObjectProperty (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  fun G ↦ TopCat.Presheaf.IsFlasque G.obj

private instance : (isFlasqueProperty (X := X) (R := R)).IsClosedUnderIsomorphisms where
  of_iso e h := @TopCat.Presheaf.IsFlasque.of_iso _ _ _ _ _ ((sheafToPresheaf _ _).mapIso e) h

omit [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive] in
private lemma isFlasqueProperty_X₃
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasqueProperty S.X₁) (h₂ : isFlasqueProperty S.X₂) : isFlasqueProperty S.X₃ :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := h₁
  have : TopCat.Presheaf.IsFlasque S.X₂.obj := h₂
  hS.isFlasque_X₃_of_isFlasque

private lemma shortExact_map_Γ_of_isFlasqueProperty
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasqueProperty S.X₁) (_ : isFlasqueProperty S.X₂) :
    (S.map (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := h₁
  shortExact_map_Γ_of_isFlasque hS

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
    isFlasqueProperty
    (fun _ _ ↦ isFlasque_of_injective_moduleCat _) isFlasqueProperty_X₃
    shortExact_map_Γ_of_isFlasqueProperty ι hK I φ hφ

include hK in
/-- **`RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque resolution `K` of `F`.** The isomorphism is induced by
global sections of any comparison map from `K` to an injective resolution of `F`
(`CategoryTheory.Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap`). -/
noncomputable def rightDerivedΓObjIsoOfIsFlasque (n : ℕ) :
    ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj K) :=
  Functor.rightDerivedObjIsoOfResolution (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    isFlasqueProperty
    (fun _ _ ↦ isFlasque_of_injective_moduleCat _) isFlasqueProperty_X₃
    shortExact_map_Γ_of_isFlasqueProperty ι hK n

end CategoryTheory.Sheaf
