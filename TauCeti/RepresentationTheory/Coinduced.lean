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
public import TauCeti.RepresentationTheory.OfMulAction

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

universe u v w

-- The carrier `V` lives in `Type (max u v)`, the universe of `k[G]`, as Mathlib's `Rep.coindIso`
-- requires.
variable {k : Type u} {H : Type w} {G : Type v} [CommRing k] [Monoid H] [Monoid G] (φ : H →* G)
  {V : Type (max u v)} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

-- `k[H]` acts on the source `k[G]` through `mapDomainRingHom k φ`, and `x` is `k[H]`-linear.
private theorem coextendScalars_apply_mapDomain_mul
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (r : k[H]) (a : k[G]) :
    ρ.asModuleEquiv (x (MonoidAlgebra.mapDomainRingHom k φ r * a)) =
      ρ.asAlgebraHom r (ρ.asModuleEquiv (x a)) :=
  congrArg ρ.asModuleEquiv (map_smul (ModuleCat.CoextendScalars.equiv _ _ x) r
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a))

/-- The endomorphism of the left regular representation `k[G]` corresponding to `single g 1`
under `Rep.leftRegularHomEquiv` is right multiplication by `single g 1`. -/
theorem _root_.Rep.leftRegularHomEquiv_symm_single_one_apply (g : G) (a : k[G]) :
    ((Rep.leftRegularHomEquiv (Rep.leftRegular k G)).symm (.single g 1)).hom a =
      a * .single g 1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb, add_mul]
  | single g' c =>
    rw [← mul_one c, ← smul_eq_mul, ← MonoidAlgebra.smul_single, map_smul,
      Rep.leftRegularHomEquiv_symm_single]
    simp [MonoidAlgebra.single_mul_single]

/-- `k[G]` acts on the coinduced representation `Representation.coind' φ A`, whose elements are
the morphisms `Rep.res φ (Rep.leftRegular k G) ⟶ A`, by right multiplication on the source
`k[G]`. -/
theorem coind'_asAlgebraHom_hom_apply (A : Rep k H) (r : k[G])
    (f : Rep.res φ (Rep.leftRegular k G) ⟶ A) (a : k[G]) :
    ((coind' φ A).asAlgebraHom r f).hom a = f.hom (a * r) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r r' hr hr' => simp [Rep.add_hom, hr, hr', mul_add]
  | single g c =>
    rw [← mul_one c, ← smul_eq_mul, ← MonoidAlgebra.smul_single, map_smul, mul_smul_comm,
      map_smul, asAlgebraHom_single_one, ← Rep.leftRegularHomEquiv_symm_single_one_apply]
    rfl

/-- A `k[H]`-linear map `k[G] → V` is an `H`-equivariant `k`-linear map from the restriction of
the left regular representation of `G`. -/
private noncomputable def coextendScalarsEquivCoind' :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (Rep.coind' φ (Rep.of ρ)).ρ.asModule where
  toFun x := Rep.ofHom
    { toFun a := ρ.asModuleEquiv (x a)
      map_add' a b := congrArg ρ.asModuleEquiv (map_add (ModuleCat.CoextendScalars.equiv _ _ x)
        (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
          (ModuleCat.of k[G] k[G])) from a) b)
      map_smul' c a := by
        -- `k`-linearity is `k[H]`-linearity at the scalars `single 1 c`.
        have : c • a = MonoidAlgebra.mapDomainRingHom k φ (.single 1 c) * a := by
          ext; simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_single_one_mul]
        rw [this, coextendScalars_apply_mapDomain_mul, asAlgebraHom_single, map_one]
        rfl
      isIntertwining' h := LinearMap.ext fun a ↦ by
        have := coextendScalars_apply_mapDomain_mul φ ρ x (.single h 1) a
        rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
          TauCeti.single_mul_eq_smul_ofMulAction, one_smul, asAlgebraHom_single_one] at this
        exact this }
  invFun f := (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun a := ρ.asModuleEquiv.symm (f.hom a)
      map_add' := map_add f.hom.toLinearMap
      map_smul' r a := by
        -- `r : k[H]` acts on the source `k[G]` through `mapDomainRingHom k φ`, and on the target
        -- through `ρ.asAlgebraHom`.
        change f.hom (MonoidAlgebra.mapDomainRingHom k φ r * show k[G] from a) =
          ρ.asAlgebraHom r (f.hom a)
        induction r using MonoidAlgebra.induction_linear with
        | zero => rw [map_zero, zero_mul, map_zero, map_zero, LinearMap.zero_apply]
        | add r r' hr hr' => rw [map_add, add_mul, map_add, hr, hr', map_add, LinearMap.add_apply]
        | single h c =>
          rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
            TauCeti.single_mul_eq_smul_ofMulAction, map_smul, asAlgebraHom_single]
          exact congrArg (c • ·) (Rep.hom_comm_apply f h a) }
  map_add' x y := rfl
  map_smul' r x := Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun a ↦ by
    -- `r • f` in the module of `coind'` is `(coind' φ _).asAlgebraHom r f`.
    change _ = ((coind' φ (Rep.of ρ)).asAlgebraHom r _).hom a
    rw [coind'_asAlgebraHom_hom_apply]
    rfl
  left_inv x := rfl
  right_inv f := rfl

/-- **Coinduction is coextension of scalars.** For a monoid homomorphism `φ : H →* G` and a
representation `ρ` of `H` on `V`, the `k[G]`-module `Hom_{k[H]}(k[G], V)`, with `k[H]` acting on
`k[G]` through `φ`, is isomorphic to the module of Mathlib's coinduced representation
`Representation.coind φ ρ`: a homomorphism `x` corresponds to the function `g ↦ x (single g 1)`.
It is Mathlib's `Rep.coindIso` read through the identification of `k[H]`-linear maps
`k[G] → V` with the morphisms of `Rep.coind' φ`. -/
noncomputable def coextendScalarsEquivCoind :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (coind φ ρ).asModule :=
  (coextendScalarsEquivCoind' φ ρ).trans
    (TauCeti.Representation.asModuleLinearEquivOfEquiv
      (equivOfIso (Rep.coindIso φ (Rep.of ρ)).symm))

/-- `Representation.coextendScalarsEquivCoind` evaluates a homomorphism at the group elements. -/
@[simp]
theorem coextendScalarsEquivCoind_apply
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (g : G) :
    Subtype.val (p := (· ∈ coindV φ ρ)) (coextendScalarsEquivCoind φ ρ x) g =
      (x (.single g 1) : V) := by
  rw [coextendScalarsEquivCoind, LinearEquiv.trans_apply,
    TauCeti.Representation.asModuleLinearEquivOfEquiv_apply]
  rfl

/-- The inverse of `Representation.coextendScalarsEquivCoind` sends a coinduced function `y` to
the homomorphism taking the value `y g` at `single g 1`. -/
@[simp]
theorem coextendScalarsEquivCoind_symm_apply_single (y : (coind φ ρ).asModule) (g : G) :
    ((coextendScalarsEquivCoind φ ρ).symm y (.single g 1) : V) =
      Subtype.val (p := (· ∈ coindV φ ρ)) y g := by
  conv_rhs => rw [← (coextendScalarsEquivCoind φ ρ).apply_symm_apply y]
  rw [coextendScalarsEquivCoind_apply]

end Representation
