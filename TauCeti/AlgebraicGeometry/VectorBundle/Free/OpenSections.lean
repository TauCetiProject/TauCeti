/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.VectorBundle.Free.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Sections of a finite free sheaf over an open

Let `I` be a finite type and `X` a scheme. Over every open `U` of `X`, the sections of the free
sheaf `𝒪_X^I` are the `I`-indexed families of functions on `U`:

`Γ(𝒪_X^I, U) ≃ₗ[Γ(X, U)] (I → Γ(X, U))`

(`FiniteLocallyFreeSheaf.freeSectionsLinearEquiv`). It is the comparison of two limits: the
additive sections functor carries the biproduct `𝒪_X^I` (`FiniteLocallyFreeSheaf.freeBicone`) to
a biproduct of `Γ(X, U)`-modules, and `I → Γ(X, U)` is the product in `ModuleCat`. A section `s`
goes to the family of its components `π_i s`, and a family `v` to `∑ i, ι_i (v i)`, where `ι_i`
and `π_i` are the basis inclusions and coordinate projections of `𝒪_X^I`.
So `Γ(𝒪_X^I, U)` is a finite free `Γ(X, U)`-module, of rank `#I` when `Γ(X, U)` is nontrivial
(that is, when `U` is nonempty), and of rank `#I` at every prime of `Γ(X, U)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.freeSectionsLinearEquiv`: sections of `𝒪_X^I`
  over `U` are `I`-indexed families of sections of `𝒪_X` over `U`.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.freeSectionsLinearEquiv_map`: this
  identification is compatible with restriction to a smaller open.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.free_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finrank_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rankAtStalk_freeSections`: these sections form
  a finite free module, of rank `#I` when `Γ(X, U)` is nontrivial, and of rank `#I` at every
  prime.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry Scheme.Modules

section Sections

variable {X : Scheme.{u}} (I : Type u) [Fintype I] (U : X.Opens)

/-- The `i`-th coordinate of a section of `𝒪_X^I` over `U`, as a `Γ(X, U)`-linear map. -/
abbrev freeSectionsπ (i : I) : Γ((free X I).obj, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  ((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).π i)).hom

/-- The `i`-th basis inclusion of sections of `𝒪_X` over `U` into sections of `𝒪_X^I`, as a
`Γ(X, U)`-linear map. -/
abbrev freeSectionsι (i : I) : Γ(X, U) →ₗ[Γ(X, U)] Γ((free X I).obj, U) :=
  ((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).ι i)).hom

/-- The composite of the `i`-th basis inclusion and the `j`-th coordinate is the image of the
biproduct composite `ι_i ≫ π_j` under the sections functor. -/
private lemma freeSectionsπ_comp_freeSectionsι (i j : I) :
    (freeSectionsπ I U j).comp (freeSectionsι I U i) =
      ((Scheme.Modules.sectionsFunctor U).map
        ((freeBicone X I).ι i ≫ (freeBicone X I).π j)).hom := by
  rw [Functor.map_comp, ModuleCat.hom_comp]
  -- The two sides now agree up to the domains `Γ(𝒪_X^I, U)` and `Γ(X, U)` of the abbreviations
  -- `freeSectionsπ`, `freeSectionsι` versus `sectionsFunctor` objects (`sectionsFunctor_obj` is
  -- `rfl`), which `rw`'s reducible closing `rfl` does not see through.
  exact rfl

/-- The `i`-th coordinate of the `i`-th basis inclusion is the identity. -/
@[simp]
lemma freeSectionsπ_freeSectionsι_self (i : I) (r : Γ(X, U)) :
    freeSectionsπ I U i (freeSectionsι I U i r) = r := by
  rw [← LinearMap.comp_apply, freeSectionsπ_comp_freeSectionsι, bicone_ι_π_self,
    CategoryTheory.Functor.map_id]
  -- `r` is an element of the sections functor's object, as `sectionsFunctor_obj` is `rfl`.
  exact ModuleCat.id_apply ((Scheme.Modules.sectionsFunctor U).obj (𝟙_ X.Modules)) r

/-- The `j`-th coordinate of the `i`-th basis inclusion vanishes for `i ≠ j`. -/
@[simp]
lemma freeSectionsπ_freeSectionsι_of_ne {i j : I} (h : i ≠ j) (r : Γ(X, U)) :
    freeSectionsπ I U j (freeSectionsι I U i r) = 0 := by
  rw [← LinearMap.comp_apply, freeSectionsπ_comp_freeSectionsι, bicone_ι_π_ne _ h,
    Functor.map_zero, ModuleCat.hom_zero]
  -- As in `freeSectionsπ_freeSectionsι_self`.
  exact LinearMap.zero_apply (M := (Scheme.Modules.sectionsFunctor U).obj (𝟙_ X.Modules))
    (M₂ := (Scheme.Modules.sectionsFunctor U).obj (𝟙_ X.Modules)) r

/-- **Sections of a finite free sheaf over an open.** For a finite type `I` and an open `U` of
`X`, the sections of `𝒪_X^I` over `U` are the `I`-indexed families of sections of `𝒪_X` over `U`:
a section goes to its coordinates, and a family `v` to `∑ i, ι_i (v i)`. It compares the image of
the biproduct `freeBicone` under the additive sections functor with the product in `ModuleCat`. -/
def freeSectionsLinearEquiv : Γ((free X I).obj, U) ≃ₗ[Γ(X, U)] (I → Γ(X, U)) :=
  (IsLimit.conePointUniqueUpToIso
    (isBilimitOfPreserves (Scheme.Modules.sectionsFunctor U) (isBilimitFreeBicone X I)).isLimit
    (ModuleCat.HasLimit.productLimitCone fun _ : I ↦ ModuleCat.of Γ(X, U) Γ(X, U)).isLimit)
    |>.toLinearEquiv

@[simp]
lemma freeSectionsLinearEquiv_apply (s : Γ((free X I).obj, U)) (i : I) :
    freeSectionsLinearEquiv I U s i = freeSectionsπ I U i s :=
  -- The comparison triangle at `i`, evaluated at `s`: the `i`-th leg of `productLimitCone` is
  -- `LinearMap.proj i`, and that of the image of `freeBicone` is `freeSectionsπ I U i`.
  congr(ModuleCat.Hom.hom $(IsLimit.conePointUniqueUpToIso_hom_comp
    (isBilimitOfPreserves (Scheme.Modules.sectionsFunctor U) (isBilimitFreeBicone X I)).isLimit
    (ModuleCat.HasLimit.productLimitCone fun _ : I ↦ ModuleCat.of Γ(X, U) Γ(X, U)).isLimit
    ⟨i⟩) s)

/-- The equivalence sends the `i`-th basis inclusion of `r` to the family `Pi.single i r`. -/
@[simp]
lemma freeSectionsLinearEquiv_freeSectionsι [DecidableEq I] (i : I) (r : Γ(X, U)) :
    freeSectionsLinearEquiv I U (freeSectionsι I U i r) = Pi.single i r := by
  ext j
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

lemma freeSectionsLinearEquiv_symm_apply (v : I → Γ(X, U)) :
    (freeSectionsLinearEquiv I U).symm v = ∑ i, freeSectionsι I U i (v i) := by
  classical
  rw [LinearEquiv.symm_apply_eq, map_sum]
  simp only [freeSectionsLinearEquiv_freeSectionsι, Finset.univ_sum_single]

/-- The inverse equivalence sends the family `Pi.single i r` to the `i`-th basis inclusion of `r`.
-/
@[simp]
lemma freeSectionsLinearEquiv_symm_single [DecidableEq I] (i : I) (r : Γ(X, U)) :
    (freeSectionsLinearEquiv I U).symm (Pi.single i r) = freeSectionsι I U i r := by
  rw [LinearEquiv.symm_apply_eq, freeSectionsLinearEquiv_freeSectionsι]

/-- The coordinates of sections of `𝒪_X^I` commute with restriction to a smaller open. -/
@[simp]
lemma freeSectionsπ_map {V : X.Opens} (f : V ⟶ U) (i : I) (s : Γ((free X I).obj, U)) :
    freeSectionsπ I V i ((free X I).obj.presheaf.map f.op s) =
      X.presheaf.map f.op (freeSectionsπ I U i s) :=
  -- Naturality of the projection `π_i : 𝒪_X^I ⟶ 𝒪_X`; the restriction maps of the module `𝒪_X`
  -- are those of the structure sheaf by definition (`Scheme.Modules.presheaf_unit_map_apply`).
  PresheafOfModules.naturality_apply ((freeBicone X I).π i).val f.op s

/-- The basis inclusions of sections of `𝒪_X^I` commute with restriction to a smaller open. -/
@[simp]
lemma map_freeSectionsι {V : X.Opens} (f : V ⟶ U) (i : I) (r : Γ(X, U)) :
    (free X I).obj.presheaf.map f.op (freeSectionsι I U i r) =
      freeSectionsι I V i (X.presheaf.map f.op r) :=
  -- Naturality of the inclusion `ι_i : 𝒪_X ⟶ 𝒪_X^I`, as in `freeSectionsπ_map`.
  (PresheafOfModules.naturality_apply ((freeBicone X I).ι i).val f.op r).symm

/-- The equivalence is compatible with restriction: restricting a section of `𝒪_X^I` from `U` to a
smaller open `V` restricts each of its coordinates. -/
lemma freeSectionsLinearEquiv_map {V : X.Opens} (f : V ⟶ U) (s : Γ((free X I).obj, U)) :
    freeSectionsLinearEquiv I V ((free X I).obj.presheaf.map f.op s) =
      fun i ↦ X.presheaf.map f.op (freeSectionsLinearEquiv I U s i) := by
  ext i
  simp

end Sections

section Finite

variable {X : Scheme.{u}} (I : Type u) [Finite I] (U : X.Opens)

/-- The sections of a finite free sheaf over an open form a free module. -/
instance free_freeSections : Module.Free Γ(X, U) Γ((free X I).obj, U) :=
  have := Fintype.ofFinite I
  Module.Free.of_equiv (freeSectionsLinearEquiv I U).symm

/-- The sections of a finite free sheaf over an open form a finite module. -/
instance finite_freeSections : Module.Finite Γ(X, U) Γ((free X I).obj, U) :=
  have := Fintype.ofFinite I
  Module.Finite.equiv (freeSectionsLinearEquiv I U).symm

/-- Over an open with nonzero functions, the sections of `𝒪_X^I` have rank `#I`. -/
@[simp]
theorem finrank_freeSections [Nontrivial Γ(X, U)] :
    Module.finrank Γ(X, U) Γ((free X I).obj, U) = Nat.card I := by
  have := Fintype.ofFinite I
  rw [Nat.card_eq_fintype_card, (freeSectionsLinearEquiv I U).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

/-- At every prime of `Γ(X, U)`, the sections of `𝒪_X^I` over `U` have rank `#I`. -/
theorem rankAtStalk_freeSections (p : PrimeSpectrum Γ(X, U)) :
    Module.rankAtStalk (R := Γ(X, U)) Γ((free X I).obj, U) p = Nat.card I := by
  have : Nontrivial Γ(X, U) := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_freeSections, Pi.natCast_apply,
    Nat.cast_id]

end Finite

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
