/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Pushing coefficients of a monoid algebra forward along a map

Functoriality of `MonoidAlgebra.mapDomain`, the map `R[M] → R[N]` induced by a map `M → N` of the
index types, in the form of the corresponding `Finsupp.mapDomain` lemmas: the identity induces the
identity, a composite induces the composite, a surjection induces a surjection, and an injection
induces a map whose image consists of the elements supported on its range. Mathlib states
the first two only for the bundled ring and algebra homomorphisms `mapDomainRingHom` and
`mapDomainAlgHom`; the unbundled forms are what a computation with the coefficients of an
inverse system of group algebras uses. Also: the image of `mapDomain f` commutes with a monomial
`single n r` as soon as every `f m` commutes with `n` and `r` is central, so on an `R[N]`-module on
which `R[M]` acts through `mapDomain ι` for `ι : M →* N`, the action of `single n 1` is
`R[M]`-linear when `n` commutes with the image of `ι`; and the algebra map `lift F` out of `k[N]`
induced by a monoid homomorphism `F` restricts along `mapDomain φ` to `lift` of the composite
`F ∘ φ`.

## Main results

* `MonoidAlgebra.mapDomain_id`, `MonoidAlgebra.mapDomain_mapDomain`: the functor laws, with
  additive forms `AddMonoidAlgebra.mapDomain_id` and `AddMonoidAlgebra.mapDomain_mapDomain`.
* `MonoidAlgebra.mapDomain_surjective`: the map induced by a surjection is surjective, with
  additive form `AddMonoidAlgebra.mapDomain_surjective`.
* `MonoidAlgebra.mem_range_mapDomain_iff`: the image of the map induced by an injection consists of
  the elements supported on its range, with additive form
  `AddMonoidAlgebra.mem_range_mapDomain_iff`.
* `MonoidAlgebra.mapDomain_commute_single`: the image of `mapDomain f` commutes with `single n r`
  when the values of `f` commute with `n` and `r` is central, with additive form
  `AddMonoidAlgebra.mapDomain_commute_single`.
* `MonoidHom.singleSMulLinearMap`: for `ι : M →* N` and `n` commuting with the image of `ι`, the
  action of `single n 1` on an `R[N]`-module on which `R[M]` acts through `mapDomain ι`, as an
  `R[M]`-linear endomorphism.
* `MonoidAlgebra.lift_mapDomain`: `lift F ∘ mapDomain φ = lift (F ∘ φ)`.
* `MonoidAlgebra.mapDomainRingEquiv_eq_mapDomain`: the ring isomorphism induced by a monoid
  isomorphism `e` is `mapDomain e`, with additive form
  `AddMonoidAlgebra.mapDomainRingEquiv_eq_mapDomain`.
* `MonoidAlgebra.coeff_mul_mapDomainRingEquiv_inv_one`: for a commutative group `G`, the
  coefficient of the identity in `x * σ x` is the sum of the squares of the coefficients of `x`,
  where `σ` is the involution of `R[G]` induced by inversion.
-/

public section

namespace MonoidAlgebra

variable {R : Type*} [Semiring R] {M N O : Type*}

/-- Pushing the coefficients forward along the identity does nothing. -/
@[to_additive (attr := simp)
/-- Pushing the coefficients forward along the identity does nothing. -/]
theorem mapDomain_id (x : MonoidAlgebra R M) : mapDomain id x = x :=
  ext <| by rw [coeff_mapDomain, Finsupp.mapDomain_id]

/-- Pushing the coefficients forward along two maps in turn is pushing them forward along the
composite. -/
@[to_additive (attr := simp)
/-- Pushing the coefficients forward along two maps in turn is pushing them forward along the
composite. -/]
theorem mapDomain_mapDomain (f : M → N) (g : N → O) (x : MonoidAlgebra R M) :
    mapDomain g (mapDomain f x) = mapDomain (g ∘ f) x :=
  ext <| by rw [coeff_mapDomain, coeff_mapDomain, coeff_mapDomain, Finsupp.mapDomain_comp]

/-- Pushing the coefficients forward along a surjection is surjective. -/
@[to_additive
/-- Pushing the coefficients forward along a surjection is surjective. -/]
theorem mapDomain_surjective {f : M → N} (hf : Function.Surjective f) :
    Function.Surjective (mapDomain (R := R) f) := fun y ↦ by
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  exact ⟨ofCoeff x, ext <| by rw [coeff_mapDomain, coeff_ofCoeff, hx]⟩

/-- For an injective map `f`, an element lies in the image of `mapDomain f` exactly when its
support lies in the range of `f`. -/
@[to_additive
/-- For an injective map `f`, an element lies in the image of `mapDomain f` exactly when its
support lies in the range of `f`. -/]
theorem mem_range_mapDomain_iff {f : M → N} (hf : Function.Injective f) (x : MonoidAlgebra R N) :
    x ∈ Set.range (mapDomain (R := R) f) ↔ ∀ n ∈ x.coeff.support, n ∈ Set.range f := by
  have hsupp : (∀ n ∈ x.coeff.support, n ∈ Set.range f) ↔ ∀ n ∉ Set.range f, x.coeff n = 0 :=
    forall_congr' fun n ↦ by rw [Finsupp.mem_support_iff, not_imp_comm]
  rw [hsupp, ← Finsupp.mem_range_mapDomain_iff _ hf x.coeff]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨y.coeff, by rw [← hy, coeff_mapDomain]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  exact ⟨ofCoeff y, ext <| by rw [coeff_mapDomain, coeff_ofCoeff, hy]⟩

/-- The image of `mapDomain f` commutes with the monomial `single n r` when every value of `f`
commutes with `n` and `r` is central. -/
@[to_additive (dont_translate := R) mapDomain_commute_single
/-- The image of `mapDomain f` commutes with the monomial `single n r` when every value of `f`
additively commutes with `n` and `r` is central. -/]
theorem mapDomain_commute_single [Mul N] {f : M → N} {n : N} {r : R} (hm : ∀ m, Commute (f m) n)
    (hr : ∀ s, Commute s r) (x : MonoidAlgebra R M) : Commute (mapDomain f x) (single n r) := by
  induction x using induction_linear with
  | zero => rw [mapDomain_zero]; exact Commute.zero_left _
  | add x y hx hy => rw [mapDomain_add]; exact hx.add_left hy
  | single m s => rw [mapDomain_single]; exact single_commute_single (hm m) (hr s)

section SingleSMul

variable [Monoid M] [Monoid N] (ι : M →* N) {n : N} (hn : ∀ m, Commute (ι m) n) (X : Type*)
  [AddCommMonoid X] [Module (MonoidAlgebra R N) X] [Module (MonoidAlgebra R M) X]
  (hact : ∀ (r : MonoidAlgebra R M) (x : X), r • x = mapDomain ι r • x)

/-- The action of `single n 1` on an `R[N]`-module `X`, as an `R[M]`-linear endomorphism, when `n`
commutes with the image of `ι : M →* N` and `R[M]` acts on `X` through `mapDomain ι`. -/
noncomputable def _root_.MonoidHom.singleSMulLinearMap : X →ₗ[MonoidAlgebra R M] X where
  toFun x := (single n 1 : MonoidAlgebra R N) • x
  map_add' := smul_add _
  map_smul' r x := by
    rw [RingHom.id_apply, hact, hact, ← mul_smul, ← mul_smul,
      (mapDomain_commute_single hn (fun _ ↦ Commute.one_right _) r).eq]

/-- `MonoidHom.singleSMulLinearMap` acts as `single n 1`. -/
@[simp]
theorem _root_.MonoidHom.singleSMulLinearMap_apply (x : X) :
    ι.singleSMulLinearMap hn X hact x = (single n 1 : MonoidAlgebra R N) • x :=
  (rfl)

end SingleSMul

/-- The algebra map out of `k[N]` induced by a monoid homomorphism `F : N →* A`, after the map
induced by `φ : M →* N`, is the algebra map induced by `F ∘ φ`. -/
@[simp]
theorem lift_mapDomain {k A : Type*} [CommSemiring k] [Monoid M] [Monoid N] [Semiring A]
    [Algebra k A] (F : N →* A) (φ : M →* N) (x : MonoidAlgebra k M) :
    lift k A N F (mapDomain φ x) = lift k A M (F.comp φ) x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapDomain_add, map_add, map_add, hx, hy]
  | single m r => simp [lift_single]

/-- The ring isomorphism induced by an isomorphism of monoids is `mapDomain` along it. -/
@[to_additive (dont_translate := R)
/-- The ring isomorphism induced by an isomorphism of additive monoids is `mapDomain` along it. -/]
theorem mapDomainRingEquiv_eq_mapDomain [Monoid M] [Monoid N] (e : M ≃* N)
    (x : MonoidAlgebra R M) : mapDomainRingEquiv R e x = mapDomain e x :=
  ext <| by
    rw [coeff_mapDomainRingEquiv, coeff_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
      MulEquiv.coe_toEquiv]

section Group

variable {R G : Type*} [Semiring R] [CommGroup G]

/-- The coefficient of the identity in `x * σ x`, where `σ x` is the image of `x` under the
involution induced by inversion, is the sum of the squares of the coefficients of `x`. -/
@[to_additive (dont_translate := R) coeff_mul_mapDomainRingEquiv_neg_zero
/-- The coefficient of zero in `x * σ x`, where `σ x` is the image of `x` under the involution
induced by negation, is the sum of the squares of the coefficients of `x`. -/]
theorem coeff_mul_mapDomainRingEquiv_inv_one (x : MonoidAlgebra R G) :
    (x * mapDomainRingEquiv R (MulEquiv.inv G) x).coeff 1 =
      ∑ g ∈ x.coeff.support, x.coeff g * x.coeff g := by
  simp [coeff_mul_apply_left, Finsupp.sum]

end Group

end MonoidAlgebra
