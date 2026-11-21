/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.Algebra.Homology.Linear
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Functoriality of group cohomology

This file evaluates Mathlib's pullbacks `groupCohomology.mapCocycles₁` and
`groupCohomology.mapCocycles₂` of a `1`-cocycle and a `2`-cocycle along a compatible pair
`(f, φ)` at group elements, without unfolding the cochain map.

It also records that `cochainsFunctor k G` and `Hⁿ(G, -)` are additive, `k`-linear functors on
`Rep k G`, so that the map `groupCohomology.map (MonoidHom.id G) φ n` induced by a morphism `φ` of
representations is `k`-linear in `φ`. Consequently a scalar that annihilates `A` annihilates
`Hⁿ(G, A)` in every degree (in particular `Nat.card A` annihilates `Hⁿ(G, A)`), a scalar acting
bijectively on `A` acts bijectively on `Hⁿ(G, A)`, and cohomology commutes with binary biproducts:
if `c` is a biproduct bicone of `A` and `B`, for instance the concrete product
`Rep.binaryBicone A B` on `A × B`, the maps induced by its projections identify `Hⁿ(G, c.pt)` with
`Hⁿ(G, A) × Hⁿ(G, B)`, and the maps induced by its inclusions give the inverse.

## Main statements

* `TauCeti.groupCohomology.mapCocycles₁_apply`: the value of a pulled-back `1`-cocycle.
* `TauCeti.groupCohomology.mapCocycles₂_apply`: the value of a pulled-back `2`-cocycle.
* `TauCeti.groupCohomology.map_id_add`, `TauCeti.groupCohomology.map_id_nsmul` and
  `TauCeti.groupCohomology.map_id_smul`: the map induced on cohomology is `k`-linear in the
  morphism of representations.
* `groupCohomology.nsmul_eq_zero_of_forall_nsmul_eq_zero`,
  `groupCohomology.smul_eq_zero_of_forall_smul_eq_zero` and
  `groupCohomology.natCard_V_nsmul_eq_zero`: scalars annihilating `A` (in particular `Nat.card A`)
  annihilate `Hⁿ(G, A)` in every degree.
* `TauCeti.groupCohomology.smul_bijective` and `TauCeti.groupCohomology.nsmul_bijective`: a
  bijective scalar action on `A` induces a bijective scalar action on `Hⁿ(G, A)`.
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

/-- Inhomogeneous cochains form a `k`-linear functor of the representation. -/
instance : (cochainsFunctor k G).Linear k where

/-- `Hⁿ(G, -)` is an additive functor: the map induced on cohomology by a sum of morphisms of
representations is the sum of the induced maps. -/
instance (n : ℕ) : (functor k G n).Additive where
  map_add := (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) _ n).map_add

/-- `Hⁿ(G, -)` is a `k`-linear functor: the map induced on cohomology by a scalar multiple of a
morphism of representations is the scalar multiple of the induced map. -/
instance (n : ℕ) : (functor k G n).Linear k where
  map_smul f r :=
    (cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) _ n).map_smul r f

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
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofBijective ((m : k) • LinearMap.id)
    (by simpa only [LinearMap.coe_smul, LinearMap.id_coe, Pi.smul_def, id_eq,
      Nat.cast_smul_eq_nsmul] using hA)
  let eA : A ≅ A := Rep.mkIso (.mk e fun g ↦ LinearMap.ext fun x ↦ by simp [e])
  have heA : eA.hom = (m : k) • 𝟙 A := by
    ext x
    simp [eA, e, Rep.smul_hom]
  have hmap : map (MonoidHom.id G) eA.hom n = (m : k) • 𝟙 (groupCohomology A n) := by
    rw [heA, Nat.cast_smul_eq_nsmul, map_id_nsmul, map_id, Nat.cast_smul_eq_nsmul]
  have hfun : (fun x : groupCohomology A n ↦ m • x) =
      ⇑((functor k G n).mapIso eA).toLinearEquiv := by
    ext x
    rw [Iso.toLinearEquiv_apply, CategoryTheory.Functor.mapIso_hom, functor_map, hmap]
    simp [Nat.cast_smul_eq_nsmul]
  exact hfun ▸ ((functor k G n).mapIso eA).toLinearEquiv.bijective

/-- The map induced on `Hⁿ(G, -)` by a scalar multiple `c • φ` of a morphism of representations is
`c` times the map induced by `φ`. -/
@[simp]
theorem map_id_smul {A B : Rep k G} (c : k) (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) (c • φ) n = c • map (MonoidHom.id G) φ n :=
  (functor k G n).map_smul c φ

/-- A scalar `c : k` acting bijectively on `A` acts bijectively on `Hⁿ(G, A)` in every degree
`n`. -/
theorem smul_bijective (c : k) (A : Rep k G)
    (hA : Function.Bijective fun a : A ↦ c • a) (n : ℕ) :
    Function.Bijective fun x : groupCohomology A n ↦ c • x := by
  have : IsIso ((forget (Rep k G)).map (c • 𝟙 A)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 <| by
      convert hA using 1
      ext a
      simp [Rep.smul_hom]
  have : IsIso (c • 𝟙 A) := isIso_of_reflects_iso _ (forget (Rep k G))
  have : IsIso (c • 𝟙 (groupCohomology A n)) :=
    CategoryTheory.Functor.isIso_smul_id_obj (functor k G n) c A
  have hfun : (fun x : groupCohomology A n ↦ c • x) = ⇑(c • 𝟙 (groupCohomology A n)) :=
    funext fun x ↦ by simp
  exact hfun ▸ ConcreteCategory.bijective_of_isIso (c • 𝟙 (groupCohomology A n))

end TauCeti.groupCohomology

namespace groupCohomology

open TauCeti.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- If `m : ℕ` annihilates every element of the representation `A`, then `m` annihilates
`Hⁿ(G, A)` in every degree `n`. -/
theorem nsmul_eq_zero_of_forall_nsmul_eq_zero {A : Rep k G} {m : ℕ}
    (hA : ∀ a : A, m • a = 0) {n : ℕ} (x : groupCohomology A n) : m • x = 0 := by
  have h0 : m • (𝟙 A : A ⟶ A) = 0 :=
    Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext hA
  simpa using congr((map (MonoidHom.id G) $h0 n).hom x)

/-- A scalar `c : k` that annihilates every element of `A` annihilates `Hⁿ(G, A)` in every degree
`n`. -/
theorem smul_eq_zero_of_forall_smul_eq_zero {A : Rep k G} {c : k} {n : ℕ}
    (hA : ∀ a : A, c • a = 0) (x : groupCohomology A n) : c • x = 0 := by
  have hc : c • (𝟙 A : A ⟶ A) = 0 := by
    ext a
    simp [Rep.smul_hom, hA a]
  simpa [hc] using congrArg (fun f ↦ f.hom x) (map_id_smul c (𝟙 A) n).symm

/-- `Hⁿ(G, A)` is annihilated by `Nat.card A` in every degree `n`. When `A` is infinite,
`Nat.card A = 0` and both sides vanish trivially. -/
@[simp]
theorem natCard_V_nsmul_eq_zero {A : Rep k G} {n : ℕ} (x : groupCohomology A n) :
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
