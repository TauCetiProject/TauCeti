/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.VectorBundle.Free.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Sections of a finite free sheaf over an open

Let `I` be a finite type and `X` a scheme. Over every open `U` of `X`, the sections of the free
sheaf `𝒪_X^I` are the `I`-indexed families of functions on `U`:

`Γ(𝒪_X^I, U) ≃ₗ[Γ(X, U)] (I → Γ(X, U))`

(`FiniteLocallyFreeSheaf.freeSectionsLinearEquiv`). A section `s` goes to the family of its
components `π_i s`, and a family `v` to `∑ i, ι_i (v i)`, where `ι_i` and `π_i` are the basis
inclusions and coordinate projections of the biproduct `𝒪_X^I`
(`FiniteLocallyFreeSheaf.freeBicone`).
So `Γ(𝒪_X^I, U)` is a free `Γ(X, U)`-module of rank `#I`, and its rank at every prime of
`Γ(X, U)` is `#I`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.freeSectionsLinearEquiv`: sections of `𝒪_X^I`
  over `U` are `I`-indexed families of sections of `𝒪_X` over `U`.
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.free_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finrank_freeSections`,
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rankAtStalk_freeSections`: these sections form
  a finite free module of rank `#I`, of rank `#I` at every prime.
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
lemma freeSectionsπ_freeSectionsι_self (i : I) (r : Γ(X, U)) :
    freeSectionsπ I U i (freeSectionsι I U i r) = r := by
  have h := congrArg (fun f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules ↦
      ((Scheme.Modules.sectionsFunctor U).map f).hom r)
    (bicone_ι_π_self (freeBicone X I) i)
  exact h

/-- The `j`-th coordinate of the `i`-th basis inclusion vanishes for `i ≠ j`. -/
lemma freeSectionsπ_freeSectionsι_of_ne {i j : I} (h : i ≠ j) (r : Γ(X, U)) :
    freeSectionsπ I U j (freeSectionsι I U i r) = 0 := by
  have h := congrArg (fun f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules ↦
      ((Scheme.Modules.sectionsFunctor U).map f).hom r)
    (bicone_ι_π_ne (freeBicone X I) h)
  exact h

/-- The basis inclusions and the coordinates of `𝒪_X^I` over `U` compose to the identity:
`∑ i, ι_i ∘ π_i = id`. -/
lemma sum_freeSectionsι_comp_freeSectionsπ :
    ∑ i, freeSectionsι I U i ∘ₗ freeSectionsπ I U i = LinearMap.id := by
  have key : ∑ i, (Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).π i) ≫
      (Scheme.Modules.sectionsFunctor U).map ((freeBicone X I).ι i) = 𝟙 _ :=
    (Finset.sum_congr rfl fun i _ ↦ (Functor.map_comp _ _ _).symm).trans <|
      (Functor.map_sum _ _ _).symm.trans <|
        (congrArg _ (IsBilimit.total (isBilimitFreeBicone X I))).trans
          (CategoryTheory.Functor.map_id _ _)
  exact (ModuleCat.hom_sum _ _).symm.trans (congrArg ModuleCat.Hom.hom key)

/-- A section of `𝒪_X^I` is the sum of the basis inclusions of its coordinates. -/
lemma sum_freeSectionsι_freeSectionsπ (s : Γ((free X I).obj, U)) :
    ∑ i, freeSectionsι I U i (freeSectionsπ I U i s) = s := by
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (sum_freeSectionsι_comp_freeSectionsπ I U) s

/-- **Sections of a finite free sheaf over an open.** For a finite type `I` and an open `U` of
`X`, the sections of `𝒪_X^I` over `U` are the `I`-indexed families of sections of `𝒪_X` over `U`:
a section goes to its coordinates, and a family `v` to `∑ i, ι_i (v i)`. -/
@[expose] def freeSectionsLinearEquiv : Γ((free X I).obj, U) ≃ₗ[Γ(X, U)] (I → Γ(X, U)) where
  __ := LinearMap.pi fun i ↦ freeSectionsπ I U i
  invFun v := ∑ i, freeSectionsι I U i (v i)
  left_inv s := sum_freeSectionsι_freeSectionsπ I U s
  right_inv v := funext fun j ↦ by
    change freeSectionsπ I U j (∑ i, freeSectionsι I U i (v i)) = v j
    rw [map_sum, Finset.sum_eq_single j
      (fun i _ hij ↦ freeSectionsπ_freeSectionsι_of_ne I U hij _)
      (fun h ↦ absurd (Finset.mem_univ j) h), freeSectionsπ_freeSectionsι_self]

@[simp]
lemma freeSectionsLinearEquiv_apply (s : Γ((free X I).obj, U)) (i : I) :
    freeSectionsLinearEquiv I U s i = freeSectionsπ I U i s :=
  rfl

lemma freeSectionsLinearEquiv_symm_apply (v : I → Γ(X, U)) :
    (freeSectionsLinearEquiv I U).symm v = ∑ i, freeSectionsι I U i (v i) :=
  rfl

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
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_freeSections]
  rfl

end Finite

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
