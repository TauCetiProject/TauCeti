/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.RepresentationTheory.AsModule

/-!
# Coinduction: exactness and coextension of scalars

Coinduction along a subgroup preserves short exact sequences of representations. Unlike
coinduction along an arbitrary homomorphism, subgroup coinduction preserves epimorphisms;
together with its right adjoint structure this gives exactness, without a finite-index
assumption. This allows connecting maps to be compared through Shapiro's isomorphism.

On the module side, coinduction along a monoid homomorphism `φ : H →* G` is coextension of
scalars along `MonoidAlgebra.mapDomainRingHom k φ : k[H] →+* k[G]`: the `k[G]`-module
`Hom_{k[H]}(k[G], V)` of Mathlib's `ModuleCat.coextendScalars` is isomorphic to the module of
Mathlib's coinduced representation `Representation.coind φ ρ`, by evaluation at the group
elements (`Representation.coextendScalarsEquivCoind`). This transports statements about
coextension of scalars on module categories, such as its action on Grothendieck groups of group
algebras, to coinduced and induced representations.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6 and §9.
-/

public section

open CategoryTheory

namespace Rep

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- Coinduction acts additively on coefficient maps. -/
instance {H : Type u} [Group H] (φ : H →* G) :
    (coindFunctor.{u} R φ).Additive where
  map_add := by intro X Y f g; ext x; rfl

/-- Subgroup coinduction preserves homology of short complexes of representations. -/
noncomputable instance (H : Subgroup G) :
    (coindFunctor.{u} R H.subtype).PreservesHomology :=
  (coindFunctor.{u} R H.subtype).preservesHomology_of_preservesEpis_and_kernels

/-- Subgroup coinduction is exact, so also preserves finite colimits. -/
instance (H : Subgroup G) :
    Limits.PreservesFiniteColimits (coindFunctor.{u} R H.subtype) :=
  (coindFunctor.{u} R H.subtype).preservesFiniteColimits_of_preservesHomology

end Rep

namespace Representation

open scoped MonoidAlgebra

universe u

variable {k H G : Type u} [CommRing k] [Monoid H] [Monoid G] (φ : H →* G) {V : Type u}
  [AddCommGroup V] [Module k V] (ρ : Representation k H V)

/-- The value at `a : k[G]` of an element of `Hom_{k[H]}(k[G], V)`, as a vector of `V`. -/
private noncomputable def coextendEv
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (a : k[G]) : V :=
  ρ.asModuleEquiv (ModuleCat.CoextendScalars.equiv _ _ x a)

variable {φ ρ}

private theorem coextendEv_add
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (a b : k[G]) :
    coextendEv φ ρ x (a + b) = coextendEv φ ρ x a + coextendEv φ ρ x b :=
  congrArg ρ.asModuleEquiv (map_add (ModuleCat.CoextendScalars.equiv _ _ x)
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a) b)

private theorem coextendEv_zero
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) :
    coextendEv φ ρ x 0 = 0 :=
  congrArg ρ.asModuleEquiv (map_zero (ModuleCat.CoextendScalars.equiv _ _ x))

-- `k[H]` acts on the source `k[G]` through `mapDomainRingHom k φ`, and `x` is `k[H]`-linear.
private theorem coextendEv_mapDomain_mul
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (r : k[H]) (a : k[G]) :
    coextendEv φ ρ x (MonoidAlgebra.mapDomainRingHom k φ r * a) =
      ρ.asAlgebraHom r (coextendEv φ ρ x a) :=
  congrArg ρ.asModuleEquiv (map_smul (ModuleCat.CoextendScalars.equiv _ _ x) r
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a))

private theorem coextendEv_single
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (g : G) (c : k) :
    coextendEv φ ρ x (.single g c) = c • coextendEv φ ρ x (.single g 1) := by
  have : (MonoidAlgebra.single g c : k[G]) =
      MonoidAlgebra.mapDomainRingHom k φ (.single 1 c) * .single g 1 := by
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.single_mul_single]
  rw [this, coextendEv_mapDomain_mul, asAlgebraHom_single, map_one]
  rfl

private theorem coextendEv_ext
    {x y : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)}
    (h : ∀ g : G, coextendEv φ ρ x (.single g 1) = coextendEv φ ρ y (.single g 1)) : x = y := by
  refine ModuleCat.CoextendScalars.ext (LinearMap.ext fun a ↦ ?_)
  -- Restate the goal through `coextendEv`, whose lemmas handle the change of carrier.
  change coextendEv φ ρ x a = coextendEv φ ρ y a
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [coextendEv_zero, coextendEv_zero]
  | add a b ha hb => rw [coextendEv_add, coextendEv_add, ha, hb]
  | single g c => rw [coextendEv_single x, coextendEv_single y, h]

variable (φ ρ)

/-- Evaluation of `x : Hom_{k[H]}(k[G], V)` at the group elements, as an element of the coinduced
representation. -/
private noncomputable def coextendScalarsEval
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) : coindV φ ρ :=
  ⟨fun g ↦ coextendEv φ ρ x (.single g 1), fun h g ↦ by
    have : (MonoidAlgebra.single (φ h * g) (1 : k) : k[G]) =
        MonoidAlgebra.mapDomainRingHom k φ (.single h 1) * .single g 1 := by
      simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.single_mul_single]
    simp only [this, coextendEv_mapDomain_mul, asAlgebraHom_single_one]⟩

/-- The `k`-linear map `k[G] → V` sending `single g c` to `c • F g`. -/
private noncomputable def coindVLinearCombination (F : coindV φ ρ) : k[G] →ₗ[k] V :=
  Finsupp.linearCombination k F.1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem coindVLinearCombination_single (F : coindV φ ρ) (g : G) (c : k) :
    coindVLinearCombination φ ρ F (.single g c) = c • F.1 g := by
  simp [coindVLinearCombination]

private theorem coindVLinearCombination_mapDomain_mul (F : coindV φ ρ) (r : k[H]) (a : k[G]) :
    coindVLinearCombination φ ρ F (MonoidAlgebra.mapDomainRingHom k φ r * a) =
      ρ.asAlgebraHom r (coindVLinearCombination φ ρ F a) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r r' hr hr' => simp only [map_add, add_mul, hr, hr', LinearMap.add_apply]
  | single h c =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a a' ha ha' => simp only [map_add, mul_add, ha, ha']
    | single g d =>
      simp [coindVLinearCombination_single, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.single_mul_single, F.2 h g, smul_smul, mul_comm]

/-- The `k[H]`-linear map `k[G] → V` extending a coinduced function `k`-linearly. -/
private noncomputable def coindVToCoextendScalars (F : coindV φ ρ) :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) :=
  (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun := fun a ↦ ρ.asModuleEquiv.symm (coindVLinearCombination φ ρ F a)
      map_add' := fun a b ↦ (congrArg ρ.asModuleEquiv.symm
        (map_add (coindVLinearCombination φ ρ F) a b)).trans (map_add _ _ _)
      map_smul' := fun r a ↦
        congrArg ρ.asModuleEquiv.symm (coindVLinearCombination_mapDomain_mul φ ρ F r a) }

private theorem coextendEv_coindVToCoextendScalars (F : coindV φ ρ) (a : k[G]) :
    coextendEv φ ρ (coindVToCoextendScalars φ ρ F) a = coindVLinearCombination φ ρ F a :=
  (rfl)

/-- **Coinduction is coextension of scalars.** For a monoid homomorphism `φ : H →* G` and a
representation `ρ` of `H` on `V`, the `k[G]`-module `Hom_{k[H]}(k[G], V)`, with `k[H]` acting on
`k[G]` through `φ`, is isomorphic to the module of Mathlib's coinduced representation
`Representation.coind φ ρ`: a homomorphism `x` corresponds to the function `g ↦ x (single g 1)`.
-/
noncomputable def coextendScalarsEquivCoind :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (coind φ ρ).asModule where
  toFun x := (coind φ ρ).asModuleEquiv.symm (coextendScalarsEval φ ρ x)
  invFun F := coindVToCoextendScalars φ ρ ((coind φ ρ).asModuleEquiv F)
  map_add' x y := by
    rw [← map_add]
    congr 1
  map_smul' r x := by
    apply (coind φ ρ).asModuleEquiv.injective
    rw [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext g'
    -- `k[G]` acts on `Hom_{k[H]}(k[G], V)` by right multiplication on the source, so the value
    -- at `g'` of `r • x` is the value of `x` at `single g' 1 * r`.
    change coextendEv φ ρ x (.single g' 1 * r) = _
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp [coextendEv_zero]
    | add r r' hr hr' => simp [mul_add, coextendEv_add, hr, hr']
    | single g c =>
      rw [MonoidAlgebra.single_mul_single, one_mul, coextendEv_single, RingHom.id_apply,
        asAlgebraHom_single]
      rfl
  -- Both inverse laws reduce to `coindVLinearCombination_single` at `c = 1`; the identifications
  -- `asModuleEquiv` are identity maps.
  left_inv x := coextendEv_ext fun g ↦
    (coindVLinearCombination_single φ ρ _ g 1).trans (one_smul k _)
  right_inv F := (coind φ ρ).asModuleEquiv.injective <| Subtype.ext <| funext fun g ↦
    (coindVLinearCombination_single φ ρ _ g 1).trans (one_smul k _)

/-- `Representation.coextendScalarsEquivCoind` evaluates a homomorphism at the group elements. -/
@[simp]
theorem coextendScalarsEquivCoind_apply
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (g : G) :
    Subtype.val (p := (· ∈ coindV φ ρ)) (coextendScalarsEquivCoind φ ρ x) g =
      (x (.single g 1) : V) :=
  (rfl)

end Representation
