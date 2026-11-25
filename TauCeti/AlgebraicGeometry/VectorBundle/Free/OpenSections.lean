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

/-- The `i`-th coordinate of the `i`-th basis inclusion is the identity. -/
@[simp]
lemma freeSectionsπ_freeSectionsι_self (i : I) (r : Γ(X, U)) :
    freeSectionsπ I U i (freeSectionsι I U i r) = r := by
  -- Stated over the sections functor's own objects, so that the rewrites are well typed; `r`
  -- fits since `sectionsFunctor_obj` holds by `rfl`.
  have h (r' : (Scheme.Modules.sectionsFunctor U).obj (𝟙_ X.Modules)) :
      ((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).π i)).hom
        (((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).ι i)).hom r') = r' := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, bicone_ι_π_self,
      CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]
  exact h r

/-- The `j`-th coordinate of the `i`-th basis inclusion vanishes for `i ≠ j`. -/
@[simp]
lemma freeSectionsπ_freeSectionsι_of_ne {i j : I} (h : i ≠ j) (r : Γ(X, U)) :
    freeSectionsπ I U j (freeSectionsι I U i r) = 0 := by
  -- As in `freeSectionsπ_freeSectionsι_self`.
  have h (r' : (Scheme.Modules.sectionsFunctor U).obj (𝟙_ X.Modules)) :
      ((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).π j)).hom
        (((Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).ι i)).hom r') = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, bicone_ι_π_ne _ h,
      Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact h r

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
  (rfl)

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
