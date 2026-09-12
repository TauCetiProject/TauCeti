/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Tate cohomology along an isomorphism of finite groups

Mathlib's Tate cohomology of a finite group is functorial in the coefficient representation, but
the group is fixed throughout. This file supplies the missing variance in the group for the case
of an isomorphism. A **compatible pair** consists of a group isomorphism `e : G ≃* H` and a
linear map `φ` between the coefficient modules of `M : Rep R G` and `N : Rep R H` satisfying

`φ ∘ ρ g = σ (e g) ∘ φ`.

Such a pair induces a map of Tate complexes, hence a map
`tateCohomology M n ⟶ tateCohomology N n` in every integer degree, and that map is an
isomorphism as soon as `φ` is.

The construction connects the two halves of the Tate complex: on the chain half it is Mathlib's
`groupHomology.chainsMap` along `e`, on the cochain half it is `groupCohomology.cochainsMap`
along `e.symm`, and the two agree on the Tate norm because `e` permutes the group, so the norm
`∑ g, ρ g` is carried to `∑ h, σ h`. In the degrees where Mathlib identifies Tate cohomology
with ordinary group cohomology or homology, the construction is the ordinary change-of-group map
of that theory.

The main application is conjugation: for an element of a group acting on a normal layer of a
class formation, conjugation is an isomorphism of finite Galois groups covered by an isomorphism
of coefficient modules, and the class-formation axioms compare the invariants of a layer with the
invariants of its conjugate through the resulting map in degree two.

## Main definitions

* `TauCeti.TateCohomology.IsCompatible`: the compatibility relation between a group isomorphism
  and a map of coefficient modules.
* `TauCeti.TateCohomology.IsCompatible.complexMap`: the induced map of Tate complexes.
* `TauCeti.TateCohomology.map`: the induced map in a single integer degree.
* `TauCeti.TateCohomology.mapIso`: the induced isomorphism, for `φ` a linear equivalence.
* `TauCeti.TateCohomology.resIso`: the packaged natural isomorphism
  `Res(e) ⋙ tateCohomologyFunctor n ≅ tateCohomologyFunctor n`.

## Main results

* `TauCeti.TateCohomology.IsCompatible.complexMap_refl`: along the identity isomorphism the
  construction is Mathlib's coefficient functoriality.
* `TauCeti.TateCohomology.map_id` and `TauCeti.TateCohomology.map_comp`: functoriality in the
  compatible pair.
* `TauCeti.TateCohomology.map_comp_isoGroupCohomology_hom`: in positive degrees the construction
  is `groupCohomology.map` along `e.symm`.
* `TauCeti.TateCohomology.map_comp_isoGroupHomology_hom`: in degrees at most `-2` it is
  `groupHomology.map` along `e`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Chapter I, §5.
-/

public noncomputable section

universe u

open CategoryTheory

namespace TauCeti.TateCohomology

variable {R G H K : Type u} [CommRing R] [Group G] [Group H] [Group K]
  {M : Rep R G} {N : Rep R H} {P : Rep R K}

/-- A group isomorphism `e : G ≃* H` and a linear map `φ` between the coefficient modules of
`M : Rep R G` and `N : Rep R H` are **compatible** when `φ ∘ ρ g = σ (e g) ∘ φ` for every `g`.
Such a pair is what carries the Tate cohomology of `M` to that of `N`.

Use `TauCeti.TateCohomology.isCompatible_iff` to build or to destructure such a pair. -/
def IsCompatible (e : G ≃* H) (φ : M.V →ₗ[R] N.V) : Prop :=
  ∀ g, φ ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ φ

/-- The defining intertwining condition of a compatible pair. -/
theorem isCompatible_iff {e : G ≃* H} {φ : M.V →ₗ[R] N.V} :
    IsCompatible e φ ↔ ∀ g, φ ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ φ := Iff.rfl

namespace IsCompatible

variable {e : G ≃* H} {φ : M.V →ₗ[R] N.V}

/-- A compatible pair read as a morphism `M ⟶ Res(e)(N)` of `G`-representations. This is the
datum that `groupHomology.chainsMap` consumes. -/
def toRes (hφ : IsCompatible e φ) : M ⟶ Rep.res (e : G →* H) N := Rep.ofHom ⟨φ, hφ⟩

/-- A compatible pair read as a morphism `Res(e⁻¹)(M) ⟶ N` of `H`-representations. This is the
datum that `groupCohomology.cochainsMap` consumes. -/
def ofRes (hφ : IsCompatible e φ) : Rep.res (e.symm : H →* G) M ⟶ N :=
  Rep.ofHom ⟨φ, fun h ↦ by simpa using hφ (e.symm h)⟩

@[simp] theorem toRes_hom_toLinearMap (hφ : IsCompatible e φ) :
    hφ.toRes.hom.toLinearMap = φ := by simp [toRes]

@[simp] theorem ofRes_hom_toLinearMap (hφ : IsCompatible e φ) :
    hφ.ofRes.hom.toLinearMap = φ := by simp [ofRes]

/-- **Compatible pairs compose.** -/
theorem trans (hφ : IsCompatible e φ) {e₂ : H ≃* K} {ψ : N.V →ₗ[R] P.V}
    (hψ : IsCompatible e₂ ψ) : IsCompatible (e.trans e₂) (ψ ∘ₗ φ) := fun g ↦ by
  rw [LinearMap.comp_assoc, hφ g, ← LinearMap.comp_assoc, hψ (e g), LinearMap.comp_assoc]
  rfl

/-- **The inverse of a compatible pair whose linear part is an equivalence is compatible.** -/
theorem symm {e' : M.V ≃ₗ[R] N.V} (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) :
    IsCompatible e.symm (e'.symm : N.V →ₗ[R] M.V) := fun h ↦ by
  rw [e'.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc, he (e.symm h)]
  ext x
  simp

end IsCompatible

/-- The identity of a representation is compatible with the identity of its group. -/
theorem isCompatible_id :
    IsCompatible (MulEquiv.refl G) (LinearMap.id : M.V →ₗ[R] M.V) := fun g ↦ by simp

/-- Restricting the coefficients along `e` and comparing back by the identity is a compatible
pair. -/
theorem isCompatible_res (e : G ≃* H) (N : Rep R H) :
    IsCompatible (M := Rep.res (e : G →* H) N) e
      ((LinearEquiv.refl R N.V : N.V →ₗ[R] N.V) :
        (Rep.res (e : G →* H) N).V →ₗ[R] N.V) := fun g ↦ by
  ext x
  simp

section Complex

variable [Fintype G] [Fintype H] {e : G ≃* H} {φ : M.V →ₗ[R] N.V}

namespace IsCompatible

/-- **A compatible pair intertwines the two norm maps.** The group isomorphism permutes the
summands of `∑ g, ρ g`. -/
theorem comp_norm (hφ : IsCompatible e φ) : φ ∘ₗ M.ρ.norm = N.ρ.norm ∘ₗ φ := by
  ext x
  simpa [Representation.norm] using
    Fintype.sum_equiv e.toEquiv (fun g ↦ φ (M.ρ g x)) (fun h ↦ N.ρ h (φ x))
      fun g ↦ congr($(hφ g) x)

/-- The square joining the chain half of the Tate complex to its cochain half commutes for a
compatible pair: this is `IsCompatible.comp_norm` in degree zero. -/
theorem chainsMap_comp_d₀ (hφ : IsCompatible e φ) :
    (groupHomology.chainsMap (e : G →* H) hφ.toRes).f 0 ≫ (tateComplexConnectData N).d₀ =
      (tateComplexConnectData M).d₀ ≫
        (groupCohomology.cochainsMap (e.symm : H →* G) hφ.ofRes).f 0 := by
  simp only [tateComplexConnectData_d₀]
  ext x m y
  simp only [groupHomology.lsingle_comp_chainsMap_f_assoc, MonoidHom.coe_coe, ModuleCat.ofHom_comp,
    Category.assoc, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, Finsupp.lsingle_apply, Rep.tateNorm_eq, groupCohomology.cochainsMap_f,
    toRes, ofRes, Finsupp.lsum_single, LinearMap.pi_apply, LinearMap.compLeft_apply,
    LinearMap.funLeft_apply]
  exact congr($(hφ.comp_norm) m).symm

/-- **The map of Tate complexes attached to a compatible pair.** On the chain half it is
`groupHomology.chainsMap` along `e`, on the cochain half `groupCohomology.cochainsMap` along
`e.symm`. -/
def complexMap (hφ : IsCompatible e φ) : tateComplex M ⟶ tateComplex N :=
  (tateComplexConnectData M).map (tateComplexConnectData N)
    (groupHomology.chainsMap (e : G →* H) hφ.toRes)
    (groupCohomology.cochainsMap (e.symm : H →* G) hφ.ofRes)
    hφ.chainsMap_comp_d₀

end IsCompatible

end Complex

section Degrees

variable [Fintype G] [Fintype H] [Fintype K]

namespace IsCompatible

/-- The map of Tate complexes depends only on the compatible pair, not on the compatibility
proof. -/
theorem complexMap_congr {e₁ e₂ : G ≃* H} {φ₁ φ₂ : M.V →ₗ[R] N.V}
    {h₁ : IsCompatible e₁ φ₁} {h₂ : IsCompatible e₂ φ₂} (he : e₁ = e₂) (hφ : φ₁ = φ₂) :
    h₁.complexMap = h₂.complexMap := by
  subst he; subst hφ; rfl

/-- **Along the identity isomorphism the construction is Mathlib's coefficient
functoriality.** -/
theorem complexMap_refl {M N : Rep R G} {φ : M.V →ₗ[R] N.V}
    (hφ : IsCompatible (MulEquiv.refl G) φ) :
    hφ.complexMap = tateComplex.map (Rep.ofHom ⟨φ, isCompatible_iff.mp hφ⟩) := by
  rw [complexMap]
  rfl

/-- The identity compatible pair induces the identity of Tate complexes. -/
@[simp] theorem complexMap_id : (isCompatible_id (M := M)).complexMap = 𝟙 (tateComplex M) :=
  (tateComplexFunctor R G).map_id M

/-- **The construction is functorial in the compatible pair.** -/
theorem complexMap_comp {e₁ : G ≃* H} {e₂ : H ≃* K} {φ : M.V →ₗ[R] N.V}
    (hφ : IsCompatible e₁ φ) {ψ : N.V →ₗ[R] P.V} (hψ : IsCompatible e₂ ψ) :
    hφ.complexMap ≫ hψ.complexMap = (hφ.trans hψ).complexMap := by
  refine (CochainComplex.ConnectData.map_comp_map ..).trans ?_
  congr 1
  exact (groupHomology.chainsMap_comp _ _ _ _).symm

end IsCompatible

/-- **The isomorphism of Tate complexes attached to a compatible pair whose linear part is an
equivalence.** -/
def complexMapIso {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) : tateComplex M ≅ tateComplex N where
  hom := he.complexMap
  inv := he.symm.complexMap
  hom_inv_id := (IsCompatible.complexMap_comp ..).trans
    ((IsCompatible.complexMap_congr (by simp) (by ext x; simp)).trans
      IsCompatible.complexMap_id)
  inv_hom_id := (IsCompatible.complexMap_comp ..).trans
    ((IsCompatible.complexMap_congr (by simp) (by ext x; simp)).trans
      IsCompatible.complexMap_id)

@[simp] theorem complexMapIso_hom {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) : (complexMapIso he).hom = he.complexMap := by
  rw [complexMapIso]

@[simp] theorem complexMapIso_inv {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) :
    (complexMapIso he).inv = he.symm.complexMap := by
  rw [complexMapIso]

/-- **Tate cohomology along a compatible pair**, in a single integer degree. -/
def map {e : G ≃* H} {φ : M.V →ₗ[R] N.V} (hφ : IsCompatible e φ) (n : ℤ) :
    tateCohomology M n ⟶ tateCohomology N n :=
  HomologicalComplex.homologyMap hφ.complexMap n

/-- `TauCeti.TateCohomology.map` is the homology map of `IsCompatible.complexMap`. This records
the body of `map`, whose definition is not exported. -/
theorem map_def {e : G ≃* H} {φ : M.V →ₗ[R] N.V} (hφ : IsCompatible e φ) (n : ℤ) :
    map hφ n = HomologicalComplex.homologyMap hφ.complexMap n := by rw [map]

/-- **Tate cohomology along a compatible pair whose linear part is an equivalence** is an
isomorphism in every integer degree. -/
def mapIso {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V} (he : IsCompatible e (e' : M.V →ₗ[R] N.V))
    (n : ℤ) : tateCohomology M n ≅ tateCohomology N n :=
  HomologicalComplex.homologyMapIso (complexMapIso he) n

@[simp] theorem mapIso_hom {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    (mapIso he n).hom = map he n := by
  rw [mapIso, HomologicalComplex.homologyMapIso_hom, complexMapIso_hom, map_def]

@[simp] theorem mapIso_inv {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    (mapIso he n).inv = map he.symm n := by
  rw [mapIso, HomologicalComplex.homologyMapIso_inv, complexMapIso_inv, map_def]

/-- Tate cohomology in a fixed degree depends only on the compatible pair. -/
theorem map_congr {e₁ e₂ : G ≃* H} {φ₁ φ₂ : M.V →ₗ[R] N.V} {h₁ : IsCompatible e₁ φ₁}
    {h₂ : IsCompatible e₂ φ₂} (he : e₁ = e₂) (hφ : φ₁ = φ₂) (n : ℤ) :
    map h₁ n = map h₂ n := by
  rw [map_def, map_def, IsCompatible.complexMap_congr he hφ]

/-- Along the identity isomorphism, Tate cohomology of a compatible pair is Mathlib's coefficient
functoriality. -/
theorem map_refl {M N : Rep R G} {φ : M.V →ₗ[R] N.V} (hφ : IsCompatible (MulEquiv.refl G) φ)
    (n : ℤ) :
    map hφ n = (tateCohomologyFunctor n).map (Rep.ofHom ⟨φ, isCompatible_iff.mp hφ⟩) := by
  rw [map_def, IsCompatible.complexMap_refl]
  exact (HomologicalComplex.homologyFunctor_map (ModuleCat R) (ComplexShape.up ℤ) n _).symm

/-- The identity compatible pair induces the identity in every degree. -/
@[simp] theorem map_id (n : ℤ) :
    map (isCompatible_id (M := M)) n = 𝟙 (tateCohomology M n) := by
  rw [map_def, IsCompatible.complexMap_id]
  exact HomologicalComplex.homologyMap_id _ _

/-- **Tate cohomology is functorial in the compatible pair**, in every degree. -/
theorem map_comp {e₁ : G ≃* H} {e₂ : H ≃* K} {φ : M.V →ₗ[R] N.V} (hφ : IsCompatible e₁ φ)
    {ψ : N.V →ₗ[R] P.V} (hψ : IsCompatible e₂ ψ) (n : ℤ) :
    map hφ n ≫ map hψ n = map (hφ.trans hψ) n := by
  rw [map_def, map_def, map_def, ← IsCompatible.complexMap_comp hφ hψ,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- **In positive degrees the construction is the ordinary cohomological change-of-group map**
along `e.symm`, read through Mathlib's comparison between Tate and group cohomology. -/
theorem map_comp_isoGroupCohomology_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : IsCompatible e φ) (n : ℕ) [NeZero n] :
    map hφ (n : ℤ) ≫ (_root_.TateCohomology.isoGroupCohomology n).hom.app N =
      (_root_.TateCohomology.isoGroupCohomology n).hom.app M ≫
        groupCohomology.map (e.symm : H →* G) hφ.ofRes n := by
  have key : HomologicalComplex.homologyMap hφ.complexMap (n : ℤ) ≫
      ((tateComplexConnectData N).homologyIsoPos n (n : ℤ) rfl).hom =
        ((tateComplexConnectData M).homologyIsoPos n (n : ℤ) rfl).hom ≫
          HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap (e.symm : H →* G) hφ.ofRes) n := by
    rw [IsCompatible.complexMap, CochainComplex.ConnectData.homologyMap_map_of_eq_succ
      (n := n) (m := (n : ℤ)) (hmn := rfl)]
    simp
  rw [map_def]
  -- What is left is Mathlib's own unfoldings, all of which cross `tateCohomologyFunctor`, a
  -- semireducible `def`: `isoGroupCohomology` is `homologyIsoPos` componentwise,
  -- `groupCohomology.map` is `homologyMap` of `cochainsMap`, and `tateCohomology M n` is the
  -- homology of `tateComplex M`.
  -- `rw`/`simp` cannot cross them, because their motives are ill-typed at `implicit` transparency.
  exact key

/-- **In degrees at most `-2` the construction is the ordinary homological change-of-group map**
along `e`, read through Mathlib's comparison between Tate cohomology and group homology. -/
theorem map_comp_isoGroupHomology_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V} (hφ : IsCompatible e φ)
    (m : ℤ) (n : ℕ) (hmn : m = -(n + 1)) [NeZero n] :
    map hφ m ≫ (_root_.TateCohomology.isoGroupHomology m n hmn).hom.app N =
      (_root_.TateCohomology.isoGroupHomology m n hmn).hom.app M ≫
        groupHomology.map (e : G →* H) hφ.toRes n := by
  have key : HomologicalComplex.homologyMap hφ.complexMap m ≫
      ((tateComplexConnectData N).homologyIsoNeg n m hmn).hom =
        ((tateComplexConnectData M).homologyIsoNeg n m hmn).hom ≫
          HomologicalComplex.homologyMap (groupHomology.chainsMap (e : G →* H) hφ.toRes) n := by
    rw [IsCompatible.complexMap, CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ
      (n := n) (m := m) (hmn := hmn)]
    simp
  rw [map_def]
  -- As above: `isoGroupHomology` is `homologyIsoNeg` componentwise, `groupHomology.map` is
  -- `homologyMap` of `chainsMap`, and `tateCohomology M m` is the homology of `tateComplex M`.
  exact key

/-- **Restricting the coefficients along an isomorphism of finite groups does not change Tate
cohomology**, naturally in the coefficients. -/
def resIso (e : G ≃* H) (n : ℤ) :
    Rep.resFunctor (e : G →* H) ⋙ tateCohomologyFunctor (R := R) (G := G) n ≅
      tateCohomologyFunctor n :=
  NatIso.ofComponents (fun N ↦ mapIso (isCompatible_res e N) n)
    fun {N N'} ψ ↦ by
      have hψ : IsCompatible (MulEquiv.refl H) ψ.hom.toLinearMap := ψ.hom.isIntertwining'
      have hres : IsCompatible (M := Rep.res (e : G →* H) N) (N := Rep.res (e : G →* H) N')
          (MulEquiv.refl G)
          (ψ.hom.toLinearMap : (Rep.res (e : G →* H) N).V →ₗ[R] (Rep.res (e : G →* H) N').V) :=
        fun g ↦ hψ (e g)
      have key : map hres n ≫ map (isCompatible_res e N') n =
          map (isCompatible_res e N) n ≫ map hψ n := by
        rw [map_comp, map_comp]
        exact map_congr (by ext x; rfl) (by ext x; rfl) n
      exact key

@[simp] theorem resIso_hom_app (e : G ≃* H) (n : ℤ) (N : Rep R H) :
    (resIso e n).hom.app N = (mapIso (isCompatible_res e N) n).hom := by
  rw [resIso]
  -- `NatIso.ofComponents_hom_app` is not usable as a rewrite here: its motive is ill-typed at
  -- `implicit` transparency, because `tateCohomologyFunctor` is a semireducible `def`.
  rfl

@[simp] theorem resIso_inv_app (e : G ≃* H) (n : ℤ) (N : Rep R H) :
    (resIso e n).inv.app N = (mapIso (isCompatible_res e N) n).inv := by
  rw [resIso]
  -- As above for `NatIso.ofComponents_inv_app`.
  rfl

/-- Tate cohomology groups matched by a compatible pair whose linear part is an equivalence have
the same cardinality. -/
theorem natCard_tateCohomology_eq {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : IsCompatible e (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    Nat.card (tateCohomology M n) = Nat.card (tateCohomology N n) :=
  Nat.card_congr (mapIso he n).toLinearEquiv.toEquiv

end Degrees

end TateCohomology

end TauCeti
