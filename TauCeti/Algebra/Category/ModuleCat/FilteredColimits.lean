/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.Algebra.Category.Grp.FilteredColimits
public import TauCeti.Algebra.Category.ModuleCat.Colimits

/-!
# Filtered colimits of modules with independent universe levels

The forgetful functor from `ModuleCat.{u} R` to `Type u` preserves filtered colimits with no
constraint between the ring universe `v` and the module universe `u`
(`ModuleCat.forget_preservesFilteredColimits`), factoring through `AddCommGrpCat.{u}`.

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). It is the criterion for abelian groups,
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`, reflected along the forgetful functor to
`AddCommGrpCat`, which reflects colimits whatever the universes of the ring and the modules. This
covers modules of chains with local coefficients, whose universe is that of the space rather than
that of the ring. Over a directed order, injectivity only needs checking on elements mapped to zero
in the apex (`TauCeti.ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero`).

Conversely, every element of a filtered colimit of modules comes from some member of the diagram
(`TauCeti.ModuleCat.colimit_exists_rep`), again with no universe constraints. Finally, a family
of bilinear maps `M j × N j → P j` natural in `j` induces a bilinear map of the filtered colimits,
`TauCeti.ModuleCat.colimitMap₂`, computed on the images of two elements by multiplying them at any
common later member of the diagram (`TauCeti.ModuleCat.colimitMap₂_ι_ι`), and bilinear/trilinear
maps out of filtered colimits are determined on tuples from a single member
(`TauCeti.ModuleCat.colimit_bilinear_ext`, `TauCeti.ModuleCat.colimit_trilinear_ext`).
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits with no constraint between the ring universe
and the module universe. -/
instance forget_preservesFilteredColimits (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u} R)) where
  preserves_filtered_colimits _ _ _ :=
    Limits.comp_preservesColimitsOfShape
      (CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (CategoryTheory.forget AddCommGrpCat.{u})

end ModuleCat

namespace TauCeti.ModuleCat

universe u v w

section ColimitExt

variable {R : Type*} [Ring R] {J : Type u} [Category.{w} J] {F : J ⥤ _root_.ModuleCat.{v} R}

/-- A cocone on a diagram of modules is colimiting as soon as its legs are jointly surjective and
any two elements with the same image in the apex have a common image somewhere deeper in the
diagram. There are no universe bounds on the index category, the ring or the modules. -/
def isColimitOfJointlySurjective (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  let Φ := forget₂ (_root_.ModuleCat.{v} R) _root_.AddCommGrpCat.{v}
  let hc : IsColimit (Φ.mapCocone t) :=
    AddCommGrpCat.isColimitOfJointlySurjective (Φ.mapCocone t) hsurj hinj
  have : HasColimit (F ⋙ Φ) := ⟨⟨_, hc⟩⟩
  exact isColimitOfReflects Φ hc

/-- A cocone on a diagram of modules indexed by a directed order is colimiting as soon as its legs
are jointly surjective and every element mapped to zero in the apex is already mapped to zero
somewhere further along the diagram. -/
def isColimitOfJointlySurjectiveOfMapEqZero {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
    {F : ι ⥤ _root_.ModuleCat.{v} R} (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : ι) (y : F.obj j), (t.ι.app j).hom y = x)
    (hzero : ∀ (i : ι) (x : F.obj i), (t.ι.app i).hom x = 0 →
      ∃ (j : ι) (hij : i ≤ j), (F.map (homOfLE hij)).hom x = 0) :
    IsColimit t :=
  isColimitOfJointlySurjective t hsurj fun i j xi xj hij ↦ by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    -- the difference of the two images at a common upper bound vanishes in the apex
    obtain ⟨m, hlm, hm⟩ := hzero l ((F.map (homOfLE hil)).hom xi - (F.map (homOfLE hjl)).hom xj)
      (by rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, Cocone.w,
        ← ConcreteCategory.comp_apply, Cocone.w])
    refine ⟨m, homOfLE (hil.trans hlm), homOfLE (hjl.trans hlm), ?_⟩
    rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← F.map_comp, ← F.map_comp] at hm

end ColimitExt

section FilteredBilinear

open IsFiltered

variable {R : Type*} [CommRing R] {J : Type u} [Category.{w} J] [IsFilteredOrEmpty J]

/-- Two `R`-bilinear maps out of filtered colimits of `R`-modules agree if they agree on pairs
coming from the same index `j : J`. -/
theorem colimit_bilinear_ext {F G : J ⥤ _root_.ModuleCat.{v} R} [HasColimit F] [HasColimit G]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Φ Ψ : ↑(colimit F) →ₗ[R] ↑(colimit G) →ₗ[R] M}
    (h : ∀ j (x : F.obj j) (y : G.obj j),
      Φ ((colimit.ι F j).hom x) ((colimit.ι G j).hom y) =
        Ψ ((colimit.ι F j).hom x) ((colimit.ι G j).hom y)) :
    Φ = Ψ :=
  colimit_linearMap_ext fun i x ↦ colimit_linearMap_ext fun j y ↦ by
    rw [← colimit.w F (leftToMax i j), ← colimit.w G (rightToMax i j),
      _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
    exact h (max i j) _ _

/-- Two `R`-trilinear maps out of filtered colimits of `R`-modules agree if they agree on triples
coming from the same index `j : J`. -/
theorem colimit_trilinear_ext {F₁ F₂ F₃ : J ⥤ _root_.ModuleCat.{v} R}
    [HasColimit F₁] [HasColimit F₂] [HasColimit F₃]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Φ Ψ : ↑(colimit F₁) →ₗ[R] ↑(colimit F₂) →ₗ[R] ↑(colimit F₃) →ₗ[R] M}
    (h : ∀ j (x : F₁.obj j) (y : F₂.obj j) (z : F₃.obj j),
      Φ ((colimit.ι F₁ j).hom x) ((colimit.ι F₂ j).hom y) ((colimit.ι F₃ j).hom z) =
        Ψ ((colimit.ι F₁ j).hom x) ((colimit.ι F₂ j).hom y) ((colimit.ι F₃ j).hom z)) :
    Φ = Ψ :=
  colimit_bilinear_ext fun m x y ↦ colimit_linearMap_ext fun i₃ z ↦ by
    rw [← colimit.w F₁ (leftToMax m i₃), ← colimit.w F₂ (leftToMax m i₃),
      ← colimit.w F₃ (rightToMax m i₃), _root_.ModuleCat.comp_apply,
      _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
    exact h (max m i₃) _ _ _

end FilteredBilinear

/-! ### Elements and bilinear maps of filtered colimits -/

section Bilinear

open IsFiltered

variable {R : Type*} [Ring R] {J : Type u} [Category.{w} J] {F : J ⥤ _root_.ModuleCat.{v} R}

/-- **Every element of a filtered colimit of modules comes from some member of the diagram.**
There are no universe bounds on the index category, the ring or the modules; unlike
`CategoryTheory.Limits.Concrete.colimit_exists_rep`, no instance that the forgetful functor
preserves the colimit is needed. -/
theorem colimit_exists_rep [IsFiltered J] [HasColimit F] (x : ↑(colimit F)) :
    ∃ (j : J) (y : F.obj j), (colimit.ι F j).hom y = x := by
  -- the ranges of the legs span the colimit, and they are directed
  have hmem : x ∈ ⨆ j, LinearMap.range (colimit.ι F j).hom :=
    (iSup_range_eq_top_of_isColimit (colimit.isColimit F)).ge Submodule.mem_top
  have hdir : Directed (· ≤ ·) fun j ↦ LinearMap.range (colimit.ι F j).hom := fun i j ↦
    ⟨IsFiltered.max i j,
      by
        rintro _ ⟨y, rfl⟩
        exact ⟨(F.map (leftToMax i j)).hom y, by rw [← ConcreteCategory.comp_apply, colimit.w]⟩,
      by
        rintro _ ⟨y, rfl⟩
        exact ⟨(F.map (rightToMax i j)).hom y, by rw [← ConcreteCategory.comp_apply, colimit.w]⟩⟩
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨j, y, hy⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hmem
  exact ⟨j, y, hy⟩

end Bilinear

end TauCeti.ModuleCat

namespace TauCeti.ModuleCat

section Bilinear

open IsFiltered _root_.ModuleCat

universe u v w

variable {R : Type*} [CommRing R] {J : Type u} [Category.{w} J] [IsFilteredOrEmpty J]
  {M N P : J ⥤ _root_.ModuleCat.{v} R} (μ : ∀ j, M.obj j →ₗ[R] N.obj j →ₗ[R] P.obj j)
  (hμ : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : M.obj j) (y : N.obj j),
    μ k ((M.map f).hom x) ((N.map f).hom y) = (P.map f).hom (μ j x y))

omit [IsFilteredOrEmpty J] in
include hμ in
/-- Moving the product of two elements along `α : l ⟶ l'` is the product of the moved elements. -/
private lemma μ_map_comp_map_comp {j k l l' : J} (f : j ⟶ l) (g : k ⟶ l) (α : l ⟶ l')
    (x : M.obj j) (y : N.obj k) :
    μ l' ((M.map (f ≫ α)).hom x) ((N.map (g ≫ α)).hom y) =
      (P.map α).hom (μ l ((M.map f).hom x) ((N.map g).hom y)) := by
  rw [M.map_comp, N.map_comp, _root_.ModuleCat.hom_comp, _root_.ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hμ]

include hμ in
/-- The image in the colimit of the product of two elements, after moving them to a common later
member of the diagram, does not depend on that member. -/
private lemma colimit_ι_μ_eq [HasColimit P] {j k l l' : J} (f : j ⟶ l) (g : k ⟶ l)
    (f' : j ⟶ l') (g' : k ⟶ l') (x : M.obj j) (y : N.obj k) :
    (colimit.ι P l).hom (μ l ((M.map f).hom x) ((N.map g).hom y)) =
      (colimit.ι P l').hom (μ l' ((M.map f').hom x) ((N.map g').hom y)) := by
  -- move both products to a common later member `s`, where the two routes agree
  obtain ⟨s, α, β, hf, hg⟩ := bowtie f f' g g'
  rw [← colimit.w P α, ← colimit.w P β, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← μ_map_comp_map_comp μ hμ, ← μ_map_comp_map_comp μ hμ, hf, hg]

/-- The product of an element of `M j` and an element of `N k`, computed at the chosen common
later member `max j k` and mapped to the colimit of `P`. -/
private noncomputable def colimitPairing [HasColimit P] (j k : J) :
    M.obj j →ₗ[R] N.obj k →ₗ[R] ↑(colimit P) :=
  ((μ (max j k)).compl₁₂ (M.map (leftToMax j k)).hom (N.map (rightToMax j k)).hom).compr₂
    (colimit.ι P (max j k)).hom

include hμ in
private lemma colimitPairing_apply [HasColimit P] {j k l : J} (f : j ⟶ l) (g : k ⟶ l)
    (x : M.obj j) (y : N.obj k) :
    colimitPairing μ j k x y = (colimit.ι P l).hom (μ l ((M.map f).hom x) ((N.map g).hom y)) :=
  colimit_ι_μ_eq μ hμ _ _ f g x y

include hμ in
/-- For a fixed element of `M j`, its products with the elements of the colimit of `N`. -/
private noncomputable def colimitMap₂Aux [HasColimit N] [HasColimit P] (j : J) :
    M.obj j →ₗ[R] ↑(colimit N) →ₗ[R] ↑(colimit P) :=
  (colimit.desc N
    { pt := .of R (M.obj j →ₗ[R] ↑(colimit P))
      ι :=
        { app k := _root_.ModuleCat.ofHom (colimitPairing μ j k).flip
          naturality k k' g := by
            refine _root_.ModuleCat.hom_ext (LinearMap.ext fun y ↦ LinearMap.ext fun x ↦ ?_)
            dsimp
            -- compute both products at the common later member `max j k'`
            rw [colimitPairing_apply μ hμ (leftToMax j k') (rightToMax j k') x,
              colimitPairing_apply μ hμ (leftToMax j k') (g ≫ rightToMax j k') x y, N.map_comp,
              _root_.ModuleCat.hom_comp, LinearMap.comp_apply] } }).hom.flip

private lemma colimitMap₂Aux_apply [HasColimit N] [HasColimit P] (j k : J) (x : M.obj j)
    (y : N.obj k) :
    colimitMap₂Aux μ hμ j x ((colimit.ι N k).hom y) = colimitPairing μ j k x y := by
  simp [colimitMap₂Aux, ← ConcreteCategory.comp_apply]

include hμ in
/-- **Bilinear maps of filtered colimits of modules.** A family of bilinear maps
`μ j : M j × N j → P j`, natural in `j`, induces a bilinear map `colim M × colim N → colim P` of
the colimits over a filtered index category. It sends the images of `x : M j` and `y : N k` to the
image of the product of `x` and `y` computed at any common later member of the diagram
(`TauCeti.ModuleCat.colimitMap₂_ι_ι`). -/
noncomputable def colimitMap₂ [HasColimit M] [HasColimit N] [HasColimit P] :
    ↑(colimit M) →ₗ[R] ↑(colimit N) →ₗ[R] ↑(colimit P) :=
  (colimit.desc M
    { pt := .of R (↑(colimit N) →ₗ[R] ↑(colimit P))
      ι :=
        { app j := _root_.ModuleCat.ofHom (colimitMap₂Aux μ hμ j)
          naturality j j' f := by
            refine _root_.ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
            dsimp
            -- two linear maps out of the colimit of `N` agree on the image of every member
            refine colimit_linearMap_ext fun k y ↦ ?_
            simp only [colimitMap₂Aux_apply]
            -- compute both products at the common later member `max j' k`
            rw [colimitPairing_apply μ hμ (leftToMax j' k) (rightToMax j' k),
              colimitPairing_apply μ hμ (f ≫ leftToMax j' k) (rightToMax j' k), M.map_comp,
              _root_.ModuleCat.hom_comp, LinearMap.comp_apply] } }).hom

include hμ in
/-- **The bilinear map of colimits on images.** `colimitMap₂ μ hμ` sends the images of `x : M j`
and `y : N k` to the image of `μ l x y`, after moving `x` and `y` to any common later member `l`
of the diagram. -/
theorem colimitMap₂_ι_ι [HasColimit M] [HasColimit N] [HasColimit P] {j k l : J} (f : j ⟶ l)
    (g : k ⟶ l) (x : M.obj j) (y : N.obj k) :
    colimitMap₂ μ hμ ((colimit.ι M j).hom x) ((colimit.ι N k).hom y) =
      (colimit.ι P l).hom (μ l ((M.map f).hom x) ((N.map g).hom y)) := by
  rw [colimitMap₂, ← ConcreteCategory.comp_apply, colimit.ι_desc]
  exact (colimitMap₂Aux_apply μ hμ j k x y).trans (colimitPairing_apply μ hμ f g x y)

include hμ in
/-- `colimitMap₂ μ hμ` sends the images of `x : M j` and `y : N j` to the image of `μ j x y`. -/
@[simp]
theorem colimitMap₂_ι [HasColimit M] [HasColimit N] [HasColimit P] (j : J) (x : M.obj j)
    (y : N.obj j) :
    colimitMap₂ μ hμ ((colimit.ι M j).hom x) ((colimit.ι N j).hom y) =
      (colimit.ι P j).hom (μ j x y) := by
  simp [colimitMap₂_ι_ι μ hμ (𝟙 j) (𝟙 j)]

end Bilinear

end TauCeti.ModuleCat
