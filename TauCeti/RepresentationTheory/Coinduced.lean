/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.OfMulAction
public import TauCeti.GroupTheory.GroupAction.PiTransport

/-!
# Coinduction: exactness and coextension of scalars

Coinduction along a subgroup preserves short exact sequences of representations. Unlike
coinduction along an arbitrary homomorphism, subgroup coinduction preserves epimorphisms;
together with its right adjoint structure this gives exactness, without a finite-index
assumption. This allows connecting maps to be compared through Shapiro's isomorphism.

On the module side, coinduction along a monoid homomorphism `φ : H →* G` is coextension of
scalars along `MonoidAlgebra.mapDomainRingHom k φ : k[H] →+* k[G]`: the `k[G]`-module
`Hom_{k[H]}(k[G], V)` of Mathlib's `ModuleCat.coextendScalars` is isomorphic to the module of
Mathlib's coinduced representation `Representation.coind φ ρ`, by evaluation at the
monoid elements (`Representation.coextendScalarsEquivCoind`). This transports statements about
coextension of scalars on module categories, such as its action on Grothendieck groups of group
algebras, to coinduced and induced representations.

If a representation `B` of `G` decomposes as a product whose factors `G` permutes transitively,
the map from `B` to the representation coinduced from the stabilizer of one factor, adjoint to the
projection to that factor, is bijective (`TauCeti.resCoindToHom_bijective_of_transport`). This
identifies the units of a semi-local algebra `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` with a representation
coinduced from a decomposition group.

Mathlib's coinduced action is evaluated by `Representation.coind_apply_coe_apply`:
`(h • f) h₁ = f (h₁ * h)`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6 and §9.
-/

public section

open CategoryTheory

namespace Rep

universe u v w t

variable {R : Type u} [CommRing R]

/-- Coinduction acts additively on coefficient maps. -/
instance {G : Type v} {H : Type w} [Monoid G] [Monoid H] (φ : H →* G) :
    (coindFunctor.{t} R φ).Additive where
  map_add := by intro X Y f g; ext x; rfl

variable {G : Type v} [Group G]

/-- Subgroup coinduction preserves homology of short complexes of representations. -/
noncomputable instance (H : Subgroup G) :
    (coindFunctor.{max v t} R H.subtype).PreservesHomology :=
  (coindFunctor.{max v t} R H.subtype).preservesHomology_of_preservesEpis_and_kernels

/-- Subgroup coinduction is exact, so also preserves finite colimits. -/
instance (H : Subgroup G) :
    Limits.PreservesFiniteColimits (coindFunctor.{max v t} R H.subtype) :=
  (coindFunctor.{max v t} R H.subtype).preservesFiniteColimits_of_preservesHomology

end Rep

namespace Representation

section Apply

variable {k G H V : Type*} [Semiring k] [Monoid G] [Monoid H] [AddCommMonoid V] [Module k V]

-- Not `@[simp]`: simp first unfolds the action `coind φ ρ h` through `Representation.coind_apply`,
-- so the left-hand side is not in simp-normal form (`simpNF`).
/-- The coinduced action translates the argument of a function: `(h • f) h₁ = f (h₁ * h)`. -/
theorem coind_apply_coe_apply (φ : G →* H) (ρ : Representation k G V) (f : coindV φ ρ)
    (h h₁ : H) : ((coind φ ρ h) f).1 h₁ = f.1 (h₁ * h) :=
  rfl

end Apply

open scoped MonoidAlgebra

universe u v w

-- The carrier `V` lives in `Type (max u v)`, the universe of `k[G]`, as Mathlib's `Rep.coindIso`
-- requires.
variable {k : Type u} {H : Type w} {G : Type v} [CommRing k] [Monoid H] [Monoid G] (φ : H →* G)
  {V : Type (max u v)} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

-- The explicit source type selects the restricted `k[H]`-action, so `x` is `k[H]`-linear.
private theorem coextendScalars_apply_mapDomain_mul
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (r : k[H]) (a : k[G]) :
    ρ.asModuleEquiv (x (MonoidAlgebra.mapDomainRingHom k φ r * a)) =
      ρ.asAlgebraHom r (ρ.asModuleEquiv (x a)) :=
  congrArg ρ.asModuleEquiv (map_smul (ModuleCat.CoextendScalars.equiv _ _ x) r
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a))

/-- `k[G]` acts on the coinduced representation `Representation.coind' φ A`, whose elements are
the morphisms `Rep.res φ (Rep.leftRegular k G) ⟶ A`, by right multiplication on the source
`k[G]`. -/
@[simp↓]
theorem coind'_asAlgebraHom_hom_apply (A : Rep k H) (r : k[G])
    (f : Rep.res φ (Rep.leftRegular k G) ⟶ A) (a : k[G]) :
    ((coind' φ A).asAlgebraHom r f).hom a = f.hom (a * r) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, asAlgebraHom_single_one, coind'_apply_apply,
      Rep.hom_comp, IntertwiningMap.comp_apply]
    apply congrArg f.hom
    rw [← IntertwiningMap.toLinearMap_apply, Rep.resMap_hom_toLinearMap,
      IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe,
      Rep.leftRegularHomEquiv_symm_apply]
  | add r r' hr hr' => simp [Rep.add_hom, hr, hr', mul_add]
  | smul c r hr =>
    simp only [map_smul, LinearMap.smul_apply, Rep.smul_hom, IntertwiningMap.coe_smul,
      Pi.smul_apply, mul_smul_comm, hr]

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

/-- `Representation.coextendScalarsEquivCoind` evaluates a homomorphism at the monoid elements. -/
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

namespace TauCeti

variable {G P ι : Type*} [Group G] [MulAction G P] {p : ι → P} {M : ι → Type*}
  (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j) {w : ι}

/-- **Coinduction from a stabilizer.** Let `B` be a representation of `G` that decomposes as a
product `∏_{i : ι} M i` on which `g` carries the factor at `i` to the factor at `j` along
`T g : M i ≃ M j` whenever `p j = g • p i`, and let `A` be a representation of the stabilizer of
`p w` whose underlying type is identified with `M w`, the action of the stabilizer being given by
`T`. If `G` permutes the factors transitively, every element of `G` carries some factor to `w`,
and the transport maps compose, then the map `B ⟶ Coind A` adjoint to the projection
`f : B ⟶ A` to the factor at `w` is bijective. -/
theorem resCoindToHom_bijective_of_transport {k : Type*} [CommRing k] {B : Rep k G}
    {A : Rep k (MulAction.stabilizer G (p w))}
    (f : Rep.res (MulAction.stabilizer G (p w)).subtype B ⟶ A) (e : B ≃ ∀ i, M i)
    (he : ∀ (g : G) (x : B) {i j : ι} (h : p j = g • p i), e (B.ρ g x) j = T g h (e x i))
    (eA : A ≃ M w) (hf : ∀ x, eA (f.hom x) = e x w)
    (hA : ∀ (d : MulAction.stabilizer G (p w)) (a : A),
      eA (A.ρ d a) = T d (MulAction.mem_stabilizer_iff.mp d.2).symm (eA a))
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i) :
    Function.Bijective (Rep.resCoindToHom _ B A f).hom := by
  refine ⟨fun x x' h ↦ eq_of_forall_transport_component_eq e T he htrans fun g ↦ ?_,
    fun F ↦ ?_⟩
  · rw [← hf, ← hf]
    exact congrArg (fun F ↦ eA (F.1 g)) h
  obtain ⟨x, hx⟩ := exists_forall_transport_component_eq e T he hT htrans hsurj
    (fun g ↦ eA (F.1 g)) fun d hd g ↦ by
      have hF := F.2 ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩ g
      simp only [Subgroup.subtype_apply] at hF
      rw [hF, hA]
  exact ⟨x, Subtype.ext <| funext fun g ↦ eA.injective <| (hf _).trans (hx g)⟩

end TauCeti
