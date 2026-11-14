/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Functoriality of group cohomology

This file evaluates Mathlib's pullbacks `groupCohomology.mapCocycles₁` and
`groupCohomology.mapCocycles₂` of a `1`-cocycle and a `2`-cocycle along a compatible pair
`(f, φ)` at group elements, without unfolding the cochain map.

It also records that `Hⁿ(G, -)` is an additive functor on `Rep k G`, so that the map
`groupCohomology.map (MonoidHom.id G) φ n` induced by a morphism `φ` of representations is
additive in `φ`. Consequently cohomology commutes with binary biproducts: if `c` is a biproduct
bicone of `A` and `B`, for instance the concrete product `Rep.binaryBicone A B` on `A × B`, the
maps induced by its projections identify `Hⁿ(G, c.pt)` with `Hⁿ(G, A) × Hⁿ(G, B)`, and the maps
induced by its inclusions give the inverse.

## Main statements

* `TauCeti.groupCohomology.mapCocycles₁_apply`: the value of a pulled-back `1`-cocycle.
* `TauCeti.groupCohomology.mapCocycles₂_apply`: the value of a pulled-back `2`-cocycle.
* `TauCeti.groupCohomology.map_id_add` and `TauCeti.groupCohomology.map_id_nsmul`: the map induced
  on cohomology is additive in the morphism of representations.
* `groupCohomology.nsmul_eq_zero_of_forall_nsmul_eq_zero` and
  `groupCohomology.natCard_coe_nsmul_eq_zero`: a natural number annihilating a
  representation annihilates its cohomology in every degree; in particular `Nat.card A` does.
* `TauCeti.groupCohomology.nsmul_bijective`: bijective multiplication by a natural number on a
  representation induces bijective multiplication on its cohomology in every degree.
* `CategoryTheory.Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv`: the cohomology of a
  biproduct is the product of the cohomologies.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- The pullback of a `1`-cocycle `c` along a compatible pair `(f, φ)` takes the value
`φ (c (f g))` at `g`. Not `@[simp]`: `simp` first rewrites the left-hand side by Mathlib's
`groupCohomology.coe_mapCocycles₁`. -/
theorem mapCocycles₁_apply {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (φ : res f A ⟶ B) (c : cocycles₁ A) (g : G) :
    (mapCocycles₁ f φ c : G → B) g = φ.hom (c (f g)) :=
  (rfl)

/-- The pullback of a `2`-cocycle `c` along a compatible pair `(f, φ)` takes the value
`φ (c (f g₁, f g₂))` at `(g₁, g₂)`. Not `@[simp]`: `simp` first rewrites the left-hand side by
Mathlib's `groupCohomology.coe_mapCocycles₂`. -/
theorem mapCocycles₂_apply {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (φ : res f A ⟶ B) (c : cocycles₂ A) (q : G × G) :
    (mapCocycles₂ f φ c : G × G → B) q = φ.hom (c (f q.1, f q.2)) :=
  (rfl)

/-- `Hⁿ(G, -)` is an additive functor: the map induced on cohomology by a sum of morphisms of
representations is the sum of the induced maps. -/
instance (n : ℕ) : (functor k G n).Additive where
  map_add := (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) _ n).map_add

/-- The map induced on `Hⁿ(G, -)` by a sum `φ + ψ` of morphisms of representations is the sum of
the maps induced by `φ` and `ψ`. -/
@[simp]
theorem map_id_add {A B : Rep k G} (φ ψ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) (φ + ψ) n = map (MonoidHom.id G) φ n + map (MonoidHom.id G) ψ n :=
  (functor k G n).map_add

/-- The map induced on `Hⁿ(G, -)` by the zero morphism of representations is zero. -/
@[simp]
theorem map_id_zero (A B : Rep k G) (n : ℕ) : map (MonoidHom.id G) (0 : A ⟶ B) n = 0 :=
  (functor k G n).map_zero A B

/-- The map induced on `Hⁿ(G, -)` by a natural-number multiple `m • φ` of a morphism of
representations is `m` times the map induced by `φ`. -/
@[simp]
theorem map_id_nsmul {A B : Rep k G} (m : ℕ) (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) (m • φ) n = m • map (MonoidHom.id G) φ n :=
  (functor k G n).map_nsmul

/-- If multiplication by `m : ℕ` is bijective on `A`, then it is bijective on `Hⁿ(G, A)` in every
degree `n`. -/
theorem nsmul_bijective {A : Rep k G} {m : ℕ}
    (hA : Function.Bijective fun a : A ↦ m • a) (n : ℕ) :
    Function.Bijective fun x : groupCohomology A n ↦ m • x := by
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofBijective (m • LinearMap.id) hA
  let eA : A ≅ A := Rep.mkIso (.mk e fun g ↦ LinearMap.ext fun x ↦ by simp [e])
  have heA : eA.hom = m • 𝟙 A :=
    Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ ↦ rfl
  have hfun : (fun x : groupCohomology A n ↦ m • x) =
      ⇑((functor k G n).mapIso eA).toLinearEquiv := by
    ext x
    change m • x = ((((functor k G n).mapIso eA).hom).hom) x
    rw [CategoryTheory.Functor.mapIso_hom, functor_map, heA, map_id_nsmul, map_id]
    rfl
  exact hfun ▸ ((functor k G n).mapIso eA).toLinearEquiv.bijective

end TauCeti.groupCohomology

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- If `m : ℕ` annihilates every element of the representation `A`, then `m` annihilates
`Hⁿ(G, A)` in every degree `n`. -/
theorem nsmul_eq_zero_of_forall_nsmul_eq_zero {A : Rep k G} {m : ℕ}
    (hA : ∀ a : A, m • a = 0) {n : ℕ} (x : groupCohomology A n) : m • x = 0 := by
  have h0 : m • (𝟙 A : A ⟶ A) = 0 :=
    Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext hA
  simpa using congr((map (MonoidHom.id G) $h0 n).hom x)

/-- The cardinality of the underlying module of `A` annihilates `Hⁿ(G, A)` in every degree `n`
(when `A` is infinite, `Nat.card A = 0` and the statement is trivial). -/
theorem natCard_coe_nsmul_eq_zero {A : Rep k G} {n : ℕ} (x : groupCohomology A n) :
    Nat.card A • x = 0 :=
  nsmul_eq_zero_of_forall_nsmul_eq_zero (fun _ ↦ card_nsmul_eq_zero') x

end groupCohomology

namespace CategoryTheory.Limits.BinaryBicone.IsBilimit

open _root_.groupCohomology TauCeti.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

section Biproduct

variable {A B : Rep k G} {c : BinaryBicone A B}

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- **Cohomology of a biproduct.** If `c` is a biproduct bicone of the representations `A` and
`B`, the maps induced by its projections identify `Hⁿ(G, c.pt)` with `Hⁿ(G, A) × Hⁿ(G, B)`. The
inverse sends `(a, b)` to the sum of the images of `a` and `b` under the maps induced by the
inclusions of `c`. It is the comparison of the image of `c` under the additive functor
`Hⁿ(G, -)`, a biproduct by `isBinaryBilimitOfPreserves`, with the product of modules. -/
noncomputable def groupCohomologyProdEquiv (hc : c.IsBilimit) (n : ℕ) :
    groupCohomology c.pt n ≃ₗ[k] groupCohomology A n × groupCohomology B n :=
  (IsLimit.conePointUniqueUpToIso (isBinaryBilimitOfPreserves (functor k G n) hc).isLimit
    (ModuleCat.binaryProductLimitCone _ _).isLimit).toLinearEquiv

/-- The identification of the cohomology of a biproduct with a product is given by the maps
induced by the projections. -/
@[simp]
theorem groupCohomologyProdEquiv_apply (hc : c.IsBilimit) (n : ℕ) (x : groupCohomology c.pt n) :
    groupCohomologyProdEquiv hc n x =
      (map (MonoidHom.id G) c.fst n x, map (MonoidHom.id G) c.snd n x) := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryBilimitOfPreserves (functor k G n) hc).isLimit
    (ModuleCat.binaryProductLimitCone _ _).isLimit
  exact Prod.ext congr(($(h ⟨.left⟩)).hom x) congr(($(h ⟨.right⟩)).hom x)

/-- The first component of the identification of the cohomology of a biproduct with a product is
the map induced by the first projection. -/
theorem groupCohomologyProdEquiv_apply_fst (hc : c.IsBilimit) (n : ℕ) (x : groupCohomology c.pt n) :
    (groupCohomologyProdEquiv hc n x).1 = map (MonoidHom.id G) c.fst n x :=
  congrArg _root_.Prod.fst (groupCohomologyProdEquiv_apply hc n x)

/-- The second component of the identification of the cohomology of a biproduct with a product
is the map induced by the second projection. -/
theorem groupCohomologyProdEquiv_apply_snd (hc : c.IsBilimit) (n : ℕ) (x : groupCohomology c.pt n) :
    (groupCohomologyProdEquiv hc n x).2 = map (MonoidHom.id G) c.snd n x :=
  congrArg _root_.Prod.snd (groupCohomologyProdEquiv_apply hc n x)

/-- The inverse of the identification of the cohomology of a biproduct with a product is the sum
of the maps induced by the inclusions. -/
@[simp]
theorem groupCohomologyProdEquiv_symm_apply (hc : c.IsBilimit) (n : ℕ)
    (y : groupCohomology A n × groupCohomology B n) :
    (groupCohomologyProdEquiv hc n).symm y =
      map (MonoidHom.id G) c.inl n y.1 + map (MonoidHom.id G) c.inr n y.2 := by
  rw [LinearEquiv.symm_apply_eq, groupCohomologyProdEquiv_apply]
  have h₁ := congr((map (MonoidHom.id G) $(c.inl_fst) n).hom y.1)
  have h₂ := congr((map (MonoidHom.id G) $(c.inr_fst) n).hom y.2)
  have h₃ := congr((map (MonoidHom.id G) $(c.inl_snd) n).hom y.1)
  have h₄ := congr((map (MonoidHom.id G) $(c.inr_snd) n).hom y.2)
  simp only [map_id_comp, map_id, map_id_zero, ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

end Biproduct

end CategoryTheory.Limits.BinaryBicone.IsBilimit
