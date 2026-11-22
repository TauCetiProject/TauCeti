/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Cohomology of the truncations of the canonical t-structure

For the canonical t-structure `DerivedCategory.TStructure.t` on the derived category `D(C)` of an
abelian category, an object is `≥ n` (resp. `≤ n`) exactly when its cohomology vanishes in
degrees `< n` (resp. `> n`) (Mathlib's `DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`).
This file records how the truncation functors act on cohomology and identifies the objects of the
heart with the objects of `C`.

* The map `τ_{<n} X ⟶ X` induces an isomorphism on `Hᵠ` for `q < n`
  (`DerivedCategory.isIso_homologyFunctor_map_truncLTι_app`), and the map `X ⟶ τ_{≥n} X` induces an
  isomorphism on `Hᵠ` for `n ≤ q` (`DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app`). Both
  follow from the long exact cohomology sequence of the truncation triangle.
* An object `Y` that is both `≥ q` and `≤ q` is isomorphic to its cohomology `Hᵠ(Y)` placed in
  degree `q` (`DerivedCategory.isoSingleFunctorHomology`), by an isomorphism which induces the
  canonical one on `Hᵠ` (`DerivedCategory.homologyFunctor_map_isoSingleFunctorHomology_hom`).
  This determines it, and it is natural in `Y`
  (`DerivedCategory.isoSingleFunctorHomology_hom_naturality`).
* Combining the two, `Hᵠ(τ_{≥q} τ_{<q+1} X) ≅ Hᵠ(X)` (`DerivedCategory.homologyTruncGETruncLTIso`),
  and the truncation `τ_{≥q} τ_{<q+1} X` is `Hᵠ(X)` placed in degree `q`
  (`DerivedCategory.truncGETruncLTIsoSingleFunctor`), naturally in `X`
  (`DerivedCategory.truncGETruncLTIsoSingleFunctor_hom_naturality`). This is the identification of
  the `t`-cohomology objects of `X` with its cohomology, which computes the first page of the
  spectral sequence of the truncations of `X`.

## References

* A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100 (1982), §1.3.
-/

public section

open CategoryTheory Limits Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open TStructure

/-- The map `τ_{<n} X ⟶ X` induces an isomorphism on `Hᵠ` for `q < n`. -/
lemma isIso_homologyFunctor_map_truncLTι_app (X : DerivedCategory C) {q n : ℤ} (hqn : q < n) :
    IsIso ((homologyFunctor C q).map ((t.truncLTι n).app X)) := by
  have hT := t.triangleLTGE_distinguished n X
  have h₀ : IsZero ((homologyFunctor C q).obj ((t.truncGE n).obj X)) :=
    isZero_of_isGE _ n q hqn
  have h₁ : IsZero ((homologyFunctor C (q - 1)).obj ((t.truncGE n).obj X)) :=
    isZero_of_isGE _ n (q - 1) (by lia)
  have : Mono ((homologyFunctor C q).map ((t.truncLTι n).app X)) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (q - 1) q).2 (h₁.eq_of_src _ _)
  have : Epi ((homologyFunctor C q).map ((t.truncLTι n).app X)) :=
    (HomologySequence.epi_homologyMap_mor₁_iff _ hT q).2 (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The map `X ⟶ τ_{≥n} X` induces an isomorphism on `Hᵠ` for `n ≤ q`. -/
lemma isIso_homologyFunctor_map_truncGEπ_app (X : DerivedCategory C) {q n : ℤ} (hnq : n ≤ q) :
    IsIso ((homologyFunctor C q).map ((t.truncGEπ n).app X)) := by
  have hT := t.triangleLTGE_distinguished n X
  have h₀ : IsZero ((homologyFunctor C q).obj ((t.truncLT n).obj X)) :=
    isZero_of_isLE _ (n - 1) q (by lia)
  have h₁ : IsZero ((homologyFunctor C (q + 1)).obj ((t.truncLT n).obj X)) :=
    isZero_of_isLE _ (n - 1) (q + 1) (by lia)
  have : Mono ((homologyFunctor C q).map ((t.truncGEπ n).app X)) :=
    (HomologySequence.mono_homologyMap_mor₂_iff _ hT q).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C q).map ((t.truncGEπ n).app X)) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT q (q + 1)).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

section Heart

variable {Y : DerivedCategory C} {q : ℤ}

/-- An isomorphism `Y ≅ B[-q]` gives an isomorphism `Y ≅ Hᵠ(Y)[-q]`, by transporting `B` to
`Hᵠ(Y)` along the isomorphism induced on `Hᵠ`. -/
private noncomputable def isoSingleFunctorHomologyOfIso {B : C}
    (e : Y ≅ (singleFunctor C q).obj B) :
    Y ≅ (singleFunctor C q).obj ((homologyFunctor C q).obj Y) :=
  e ≪≫ (singleFunctor C q).mapIso
    (((singleFunctorCompHomologyFunctorIso C q).app B).symm ≪≫ (homologyFunctor C q).mapIso e.symm)

private lemma homologyFunctor_map_isoSingleFunctorHomologyOfIso_hom {B : C}
    (e : Y ≅ (singleFunctor C q).obj B) :
    (homologyFunctor C q).map (isoSingleFunctorHomologyOfIso e).hom ≫
      (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj Y) = 𝟙 _ := by
  have h₁ := (singleFunctorCompHomologyFunctorIso C q).hom.naturality
    ((homologyFunctor C q).map e.inv)
  have h₂ := (singleFunctorCompHomologyFunctorIso C q).hom.naturality
    ((singleFunctorCompHomologyFunctorIso C q).inv.app B)
  dsimp at h₁ h₂
  simp only [isoSingleFunctorHomologyOfIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc, h₁, reassoc_of% h₂, Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp]

variable (Y q) [Y.IsGE q] [Y.IsLE q]

/-- An object `Y` of the derived category which is both `≥ q` and `≤ q` is isomorphic to its
cohomology `Hᵠ(Y)` placed in degree `q`. The isomorphism induces the inverse of the canonical
isomorphism `Hᵠ(Hᵠ(Y)[-q]) ≅ Hᵠ(Y)` on `Hᵠ` (`homologyFunctor_map_isoSingleFunctorHomology_hom`),
which determines it (`hom_ext_of_isGE_of_isLE`). -/
noncomputable def isoSingleFunctorHomology :
    Y ≅ (singleFunctor C q).obj ((homologyFunctor C q).obj Y) :=
  isoSingleFunctorHomologyOfIso (Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE q).choose_spec.some

/-- The isomorphism `isoSingleFunctorHomology` induces on `Hᵠ` the inverse of the canonical
isomorphism `Hᵠ(Hᵠ(Y)[-q]) ≅ Hᵠ(Y)`. -/
@[reassoc (attr := simp)]
lemma homologyFunctor_map_isoSingleFunctorHomology_hom :
    (homologyFunctor C q).map (isoSingleFunctorHomology Y q).hom ≫
      (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj Y) = 𝟙 _ :=
  homologyFunctor_map_isoSingleFunctorHomologyOfIso_hom _

variable {Y q}

/-- Two morphisms from an object `Y` which is `≥ q` and `≤ q` to an object placed in degree `q`
agree when they agree on `Hᵠ`. -/
lemma hom_ext_of_isGE_of_isLE {B : C} {f g : Y ⟶ (singleFunctor C q).obj B}
    (h : (homologyFunctor C q).map f = (homologyFunctor C q).map g) : f = g := by
  rw [← cancel_epi (isoSingleFunctorHomology Y q).inv]
  obtain ⟨f', hf'⟩ := (singleFunctor C q).map_surjective ((isoSingleFunctorHomology Y q).inv ≫ f)
  obtain ⟨g', hg'⟩ := (singleFunctor C q).map_surjective ((isoSingleFunctorHomology Y q).inv ≫ g)
  rw [← hf', ← hg']
  congr 1
  have hf := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C q) f'
  have hg := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C q) g'
  dsimp at hf hg
  rw [← hf, ← hg, hf', hg', Functor.map_comp, Functor.map_comp, h]

/-- A morphism `Hᵠ(Y) ⟶ B` placed in degree `q`, precomposed with `isoSingleFunctorHomology`,
induces the given morphism on `Hᵠ`. -/
@[reassoc]
lemma homologyFunctor_map_isoSingleFunctorHomology_hom_comp {B : C}
    (φ : (homologyFunctor C q).obj Y ⟶ B) :
    (homologyFunctor C q).map ((isoSingleFunctorHomology Y q).hom ≫ (singleFunctor C q).map φ) ≫
      (singleFunctorCompHomologyFunctorIso C q).hom.app B = φ := by
  have := (singleFunctorCompHomologyFunctorIso C q).hom.naturality φ
  dsimp at this
  rw [Functor.map_comp, Category.assoc, this,
    homologyFunctor_map_isoSingleFunctorHomology_hom_assoc]

/-- The isomorphism `isoSingleFunctorHomology` is natural. -/
@[reassoc]
lemma isoSingleFunctorHomology_hom_naturality {Y' : DerivedCategory C} [Y'.IsGE q] [Y'.IsLE q]
    (f : Y ⟶ Y') :
    f ≫ (isoSingleFunctorHomology Y' q).hom =
      (isoSingleFunctorHomology Y q).hom ≫
        (singleFunctor C q).map ((homologyFunctor C q).map f) := by
  apply hom_ext_of_isGE_of_isLE
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C q).hom.app _),
    homologyFunctor_map_isoSingleFunctorHomology_hom_comp, Functor.map_comp, Category.assoc,
    homologyFunctor_map_isoSingleFunctorHomology_hom, Category.comp_id]

end Heart

/-- The cohomology `Hᵠ(τ_{≥q} τ_{<q+1} X)` is `Hᵠ(X)`, through the maps
`τ_{≥q} τ_{<q+1} X ⟵ τ_{<q+1} X ⟶ X`
(`homologyFunctor_map_truncGEπ_app_comp_homologyTruncGETruncLTIso_hom`). -/
noncomputable def homologyTruncGETruncLTIso (X : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C q).obj ((t.truncGE q).obj ((t.truncLT (q + 1)).obj X)) ≅
      (homologyFunctor C q).obj X :=
  have := isIso_homologyFunctor_map_truncGEπ_app ((t.truncLT (q + 1)).obj X) (le_refl q)
  have := isIso_homologyFunctor_map_truncLTι_app X (lt_add_one q)
  (asIso ((homologyFunctor C q).map ((t.truncGEπ q).app _))).symm ≪≫
    asIso ((homologyFunctor C q).map ((t.truncLTι (q + 1)).app X))

/-- The isomorphism `homologyTruncGETruncLTIso` composed with the map induced by
`τ_{<q+1} X ⟶ τ_{≥q} τ_{<q+1} X` is the map induced by `τ_{<q+1} X ⟶ X`. -/
@[reassoc (attr := simp)]
lemma homologyFunctor_map_truncGEπ_app_comp_homologyTruncGETruncLTIso_hom
    (X : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C q).map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj X)) ≫
      (homologyTruncGETruncLTIso X q).hom =
      (homologyFunctor C q).map ((t.truncLTι (q + 1)).app X) := by
  simp [homologyTruncGETruncLTIso]

/-- The isomorphism `homologyTruncGETruncLTIso` is natural in `X`. -/
@[reassoc]
lemma homologyTruncGETruncLTIso_hom_naturality {X X' : DerivedCategory C} (f : X ⟶ X') (q : ℤ) :
    (homologyFunctor C q).map ((t.truncGE q).map ((t.truncLT (q + 1)).map f)) ≫
        (homologyTruncGETruncLTIso X' q).hom =
      (homologyTruncGETruncLTIso X q).hom ≫ (homologyFunctor C q).map f := by
  have := isIso_homologyFunctor_map_truncGEπ_app ((t.truncLT (q + 1)).obj X) (le_refl q)
  rw [← cancel_epi ((homologyFunctor C q).map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj X))),
    homologyFunctor_map_truncGEπ_app_comp_homologyTruncGETruncLTIso_hom_assoc]
  -- Both sides are induced by `τ_{<q+1} X ⟶ X'`: use the naturality of `X ⟶ τ_{≥q} X`, then that
  -- of `τ_{<q+1} X ⟶ X`.
  calc _ = (homologyFunctor C q).map ((t.truncLT (q + 1)).map f) ≫
          (homologyFunctor C q).map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj X')) ≫
            (homologyTruncGETruncLTIso X' q).hom := by
        simp only [← Functor.map_comp_assoc, t.truncGEπ_naturality]
    _ = (homologyFunctor C q).map ((t.truncLT (q + 1)).map f ≫ (t.truncLTι (q + 1)).app X') := by
        simp
    _ = _ := by simp

/-- The truncation `τ_{≥q} τ_{<q+1} X` is the cohomology `Hᵠ(X)` placed in degree `q`. On `Hᵠ` it
induces `homologyTruncGETruncLTIso` (`homologyFunctor_map_truncGETruncLTIsoSingleFunctor_hom`). -/
noncomputable def truncGETruncLTIsoSingleFunctor (X : DerivedCategory C) (q : ℤ) :
    (t.truncGE q).obj ((t.truncLT (q + 1)).obj X) ≅
      (singleFunctor C q).obj ((homologyFunctor C q).obj X) :=
  isoSingleFunctorHomology _ q ≪≫ (singleFunctor C q).mapIso (homologyTruncGETruncLTIso X q)

/-- On `Hᵠ`, the isomorphism `truncGETruncLTIsoSingleFunctor` induces
`homologyTruncGETruncLTIso`. -/
@[reassoc (attr := simp)]
lemma homologyFunctor_map_truncGETruncLTIsoSingleFunctor_hom (X : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C q).map (truncGETruncLTIsoSingleFunctor X q).hom ≫
        (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj X) =
      (homologyTruncGETruncLTIso X q).hom :=
  homologyFunctor_map_isoSingleFunctorHomology_hom_comp _

/-- The isomorphism `truncGETruncLTIsoSingleFunctor` is natural in `X`. -/
@[reassoc]
lemma truncGETruncLTIsoSingleFunctor_hom_naturality {X X' : DerivedCategory C} (f : X ⟶ X')
    (q : ℤ) :
    (t.truncGE q).map ((t.truncLT (q + 1)).map f) ≫ (truncGETruncLTIsoSingleFunctor X' q).hom =
      (truncGETruncLTIsoSingleFunctor X q).hom ≫
        (singleFunctor C q).map ((homologyFunctor C q).map f) := by
  apply hom_ext_of_isGE_of_isLE
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C q).hom.app _), Functor.map_comp,
    Category.assoc, homologyFunctor_map_truncGETruncLTIsoSingleFunctor_hom,
    homologyTruncGETruncLTIso_hom_naturality, Functor.map_comp, Category.assoc]
  have := (singleFunctorCompHomologyFunctorIso C q).hom.naturality ((homologyFunctor C q).map f)
  dsimp at this
  rw [this, homologyFunctor_map_truncGETruncLTIsoSingleFunctor_hom_assoc]

end DerivedCategory
