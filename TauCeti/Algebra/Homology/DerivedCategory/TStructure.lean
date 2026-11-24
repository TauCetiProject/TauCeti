/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import TauCeti.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Cohomology of canonical truncations in the derived category

For the canonical t-structure `DerivedCategory.TStructure.t` on the derived category `D(C)` of an
abelian category, an object is `≥ n` (resp. `≤ n`) exactly when its cohomology vanishes in
degrees `< n` (resp. `> n`) (Mathlib's `DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`).
This file records how the truncation functors act on cohomology, identifies the objects of the
heart with the objects of `C`, and provides morphism-factorization and cohomology-bijectivity
results for truncated objects.

* The map `τ_{<n} X ⟶ X` induces an isomorphism on `Hᵠ` for `q < n`
  (`DerivedCategory.isIso_homologyFunctor_map_truncLTι_app`), the map `τ_{≤n} X ⟶ X` induces an
  isomorphism on `Hⁱ` for `i ≤ n` (`DerivedCategory.isIso_homologyFunctor_map_truncLEι`), and the
  map `X ⟶ τ_{≥n} X` induces an isomorphism on `Hᵠ` for `n ≤ q`
  (`DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app`). All follow from the long exact
  cohomology sequence of the truncation triangle.
* An object `Y` that is both `≥ q` and `≤ q` is isomorphic to its cohomology `Hᵠ(Y)` placed in
  degree `q` (`DerivedCategory.isoSingleFunctorHomology`), by an isomorphism which induces the
  canonical one on `Hᵠ` (`DerivedCategory.homologyFunctor_map_isoSingleFunctorHomology_hom`).
  This determines it, since morphisms from an object `≤ q` to an object placed in degree `q` are
  determined on `Hᵠ` (`DerivedCategory.hom_ext_of_isLE`), and it is natural in `Y`
  (`DerivedCategory.isoSingleFunctorHomology_hom_naturality`).
* Combining the two, `Hᵠ(τ_{≥q} τ_{<q+1} X) ≅ Hᵠ(X)` (`DerivedCategory.homologyTruncGETruncLTIso`),
  and the truncation `τ_{≥q} τ_{<q+1} X` is `Hᵠ(X)` placed in degree `q`
  (`DerivedCategory.truncGETruncLTIsoSingleFunctor`), naturally in `X`
  (`DerivedCategory.truncGETruncLTIsoSingleFunctor_hom_naturality`). This is the identification of
  the `t`-cohomology objects of `X` with its cohomology, which computes the first page of the
  spectral sequence of the truncations of `X`.
* `DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`: when `X` is `≤ n` and `Y`
  is `≥ n`, the functor `H^n` induces a bijection `(X ⟶ Y) → (H^n(X) ⟶ H^n(Y))`.
* `DerivedCategory.homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE`: in particular, under
  `X.IsLE n` and `Y.IsGE n`, a morphism `f : X ⟶ Y` vanishes if and only if `H^n(f) = 0`.
* `DerivedCategory.exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero` and
  `DerivedCategory.exists_truncGEπ_comp_of_isGE_of_homologyFunctor_map_eq_zero`: when
  `X.IsLE b₁` and `H^{b₁}(f) = 0`, `f : X ⟶ Y` factors through `τ_{≤ b₀} Y ⟶ Y` (`b₀ + 1 = b₁`);
  dually, when `Y.IsGE a₀` and `H^{a₀}(f) = 0`, `f` factors through `X ⟶ τ_{≥ a₁} X`
  (`a₀ + 1 = a₁`).

The isomorphism lemmas allow degreewise finiteness of cohomology to pass to truncations
(`TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`), while the factorization lemmas drive
ghost-nilpotence inductions (`TauCeti.Algebra.Homology.DerivedCategory.CohomologyAction`).

## References

* A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100 (1982), §1.3.
-/

public section

open CategoryTheory Limits Pretriangulated Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

section

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
which determines it (`hom_ext_of_isLE`). -/
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
agree when they agree on `Hᵠ`; see `hom_ext_of_isLE` for objects that are only `≤ q`. -/
private lemma hom_ext_of_isGE_of_isLE {B : C} {f g : Y ⟶ (singleFunctor C q).obj B}
    (h : (homologyFunctor C q).map f = (homologyFunctor C q).map g) : f = g := by
  rw [← cancel_epi (isoSingleFunctorHomology Y q).inv]
  obtain ⟨f', hf'⟩ := (singleFunctor C q).map_surjective ((isoSingleFunctorHomology Y q).inv ≫ f)
  obtain ⟨g', hg'⟩ := (singleFunctor C q).map_surjective ((isoSingleFunctorHomology Y q).inv ≫ g)
  -- The functor `B ↦ Hᵠ(B[-q])` is faithful, being isomorphic to the identity.
  have := Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso C q).symm
  have hfg : f' = g' := (singleFunctor C q ⋙ homologyFunctor C q).map_injective
    (by rw [Functor.comp_map, Functor.comp_map, hf', hg', Functor.map_comp, Functor.map_comp, h])
  rw [← hf', ← hg', hfg]

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

/-- Two morphisms from an object `Y` which is `≤ q` to an object placed in degree `q` agree when
they agree on `Hᵠ`: both factor through `Y ⟶ τ_{≥q} Y`, which induces an isomorphism on `Hᵠ`, and
`τ_{≥q} Y` is both `≥ q` and `≤ q`. -/
lemma hom_ext_of_isLE {Y : DerivedCategory C} {q : ℤ} [Y.IsLE q] {B : C}
    {f g : Y ⟶ (singleFunctor C q).obj B}
    (h : (homologyFunctor C q).map f = (homologyFunctor C q).map g) : f = g := by
  have := isIso_homologyFunctor_map_truncGEπ_app Y (le_refl q)
  have hfg : t.descTruncGE f q = t.descTruncGE g q := hom_ext_of_isGE_of_isLE (by
    rw [← cancel_epi ((homologyFunctor C q).map ((t.truncGEπ q).app Y)), ← Functor.map_comp,
      ← Functor.map_comp, t.π_descTruncGE, t.π_descTruncGE, h])
  rw [← t.π_descTruncGE f q, ← t.π_descTruncGE g q, hfg]

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
  simp only [truncGETruncLTIsoSingleFunctor, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, isoSingleFunctorHomology_hom_naturality_assoc, ← Functor.map_comp,
    homologyTruncGETruncLTIso_hom_naturality]

end

/-- For `i ≤ n`, the canonical truncation morphism `(τ_{≤ n} X) ⟶ X` induces an isomorphism on
`i`-th cohomology. -/
theorem isIso_homologyFunctor_map_truncLEι (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLEι n).app X)) := by
  let T := (TStructure.t.triangleLEGE n (n + 1) rfl).obj X
  have hT : T ∈ distTriang (DerivedCategory C) :=
    TStructure.t.triangleLEGE_distinguished n (n + 1) rfl X
  have hEpi : Epi ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (isZero_of_isGE T.obj₃ (n + 1) i (by omega)).eq_of_tgt _ _
  have hMono : Mono ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ (n + 1) (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₁)

/-- If `X` is concentrated in degrees `≤ n` and `Y` in degrees `≥ n`, then `H^n` induces a
bijection `(X ⟶ Y) → ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y)`. -/
theorem homologyFunctor_map_bijective_of_isLE_of_isGE (X Y : DerivedCategory C) (n : ℤ)
    [X.IsLE n] [Y.IsGE n] :
    Function.Bijective ((homologyFunctor C n).map :
      (X ⟶ Y) → ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y)) := by
  have : IsIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)) :=
    isIso_homologyFunctor_map_truncGEπ_app X le_rfl
  have : IsIso ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y)) :=
    isIso_homologyFunctor_map_truncLEι Y n n le_rfl
  obtain ⟨A, ⟨eA⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncGE n).obj X) n
  obtain ⟨B, ⟨eB⟩⟩ :=
    exists_iso_singleFunctor_obj_of_isGE_of_isLE ((TStructure.t.truncLE n).obj Y) n
  let eX : (homologyFunctor C n).obj X ≅ A :=
    asIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X)) ≪≫
      (homologyFunctor C n).mapIso eA ≪≫ (singleFunctorCompHomologyFunctorIso C n).app A
  let eY : B ≅ (homologyFunctor C n).obj Y :=
    ((singleFunctorCompHomologyFunctorIso C n).app B).symm ≪≫
      (homologyFunctor C n).mapIso eB.symm ≪≫
      asIso ((homologyFunctor C n).map ((TStructure.t.truncLEι n).app Y))
  have hmap : ∀ u : A ⟶ B,
      (homologyFunctor C n).map ((TStructure.t.truncGEπ n).app X ≫ eA.hom ≫
        (singleFunctor C n).map u ≫ eB.inv ≫ (TStructure.t.truncLEι n).app Y) =
        eX.hom ≫ u ≫ eY.hom := by
    intro u
    have hnat : ((singleFunctorCompHomologyFunctorIso C n).hom.app A) ≫ u ≫
        ((singleFunctorCompHomologyFunctorIso C n).inv.app B) =
        (homologyFunctor C n).map ((singleFunctor C n).map u) := by
      have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality u
      simp only [Functor.comp_map, Functor.id_map] at h
      rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    simp [eX, eY, ← hnat, Category.assoc]
  let invMap : ((homologyFunctor C n).obj X ⟶ (homologyFunctor C n).obj Y) → (X ⟶ Y) :=
    fun φ ↦ (TStructure.t.truncGEπ n).app X ≫ eA.hom ≫
      (singleFunctor C n).map (eX.inv ≫ φ ≫ eY.inv) ≫ eB.inv ≫ (TStructure.t.truncLEι n).app Y
  refine Function.bijective_iff_has_inverse.mpr ⟨invMap, fun f ↦ ?_, fun φ ↦ ?_⟩
  · let g : (TStructure.t.truncGE n).obj X ⟶ (TStructure.t.truncLE n).obj Y :=
      TStructure.t.liftTruncLE (TStructure.t.descTruncGE f n) n
    have hfg : (TStructure.t.truncGEπ n).app X ≫ g ≫ (TStructure.t.truncLEι n).app Y = f := by
      simp [g]
    obtain ⟨u, hu⟩ := (singleFunctor C n).map_surjective (eA.inv ≫ g ≫ eB.hom)
    have hf : (TStructure.t.truncGEπ n).app X ≫ eA.hom ≫ (singleFunctor C n).map u ≫
        eB.inv ≫ (TStructure.t.truncLEι n).app Y = f := by
      rw [hu]
      simpa [Category.assoc] using hfg
    rw [← hf]
    dsimp only [invMap]
    rw [hmap u]
    simp
  · dsimp only [invMap]
    rw [hmap]
    simp

/-- If `X` is concentrated in degrees `≤ n` and `Y` in degrees `≥ n`, then a morphism `f : X ⟶ Y`
is zero if and only if it induces zero on `H^n`. -/
theorem homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE {X Y : DerivedCategory C}
    (f : X ⟶ Y) (n : ℤ) [X.IsLE n] [Y.IsGE n] :
    (homologyFunctor C n).map f = 0 ↔ f = 0 :=
  ⟨fun hf ↦ (homologyFunctor_map_bijective_of_isLE_of_isGE X Y n).injective (by simpa using hf),
    fun hf ↦ by simp [hf]⟩

/-- If `X` is concentrated in degrees `≤ b₁` and `f : X ⟶ Y` induces zero on `H^{b₁}`, then `f`
factors through `(τ_{≤ b₀} Y) ⟶ Y` whenever `b₀ + 1 = b₁`. -/
theorem exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero {X Y : DerivedCategory C}
    (f : X ⟶ Y) (b₀ b₁ : ℤ) [X.IsLE b₁] (hf : (homologyFunctor C b₁).map f = 0)
    (hb : b₀ + 1 = b₁ := by lia) :
    ∃ g : X ⟶ (TStructure.t.truncLE b₀).obj Y,
      g ≫ (TStructure.t.truncLEι b₀).app Y = f := by
  have hcomp : f ≫ (TStructure.t.truncGEπ b₁).app Y = 0 := by
    rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ b₁, Functor.map_comp, hf, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _
    (TStructure.t.triangleLEGE_distinguished b₀ b₁ hb Y) f hcomp
  exact ⟨g, hg.symm⟩

/-- If `Y` is concentrated in degrees `≥ a₀` and `f : X ⟶ Y` induces zero on `H^{a₀}`, then `f`
factors through `X ⟶ (τ_{≥ a₁} X)` whenever `a₀ + 1 = a₁`. -/
theorem exists_truncGEπ_comp_of_isGE_of_homologyFunctor_map_eq_zero {X Y : DerivedCategory C}
    (f : X ⟶ Y) (a₀ a₁ : ℤ) [Y.IsGE a₀] (hf : (homologyFunctor C a₀).map f = 0)
    (ha : a₀ + 1 = a₁ := by lia) :
    ∃ g : (TStructure.t.truncGE a₁).obj X ⟶ Y,
      (TStructure.t.truncGEπ a₁).app X ≫ g = f := by
  have hcomp : (TStructure.t.truncLEι a₀).app X ≫ f = 0 := by
    rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ a₀, Functor.map_comp, hf, comp_zero]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _
    (TStructure.t.triangleLEGE_distinguished a₀ a₁ ha X) f hcomp
  exact ⟨g, hg.symm⟩

end DerivedCategory
