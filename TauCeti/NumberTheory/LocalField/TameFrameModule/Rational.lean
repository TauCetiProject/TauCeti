/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.MonoidAlgebra.Eigenvector
public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.Algebra.Module.Presentation.Basic
public import TauCeti.NumberTheory.LocalField.TameFrameModule.Basic
public import TauCeti.RingTheory.Flat.FractionRing
public import TauCeti.RingTheory.SimpleModule.RegularCancellation
public import TauCeti.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Rational structure of the tame-frame module

This file identifies the tame-frame module `M₀ = R[G]² / R[G]·(σ - a, τ - b)` after extension of
scalars to a field. The single relation defines a map

`R[G] → R[G]²,  x ↦ x · (σ - a, τ - b)`.

For elements `σ, τ` of finite order, natural-number exponents, and a coefficient ring `R` of
characteristic zero without zero divisors (such as `ℤ_p`), nonzero finite cardinality of the sharp
quotient `R[G] / (σ - a, τ - b)` implies that this map is injective. Over a field `k` in which
`#G` is nonzero, an injective tame-frame relation map presents one copy of the regular
representation `k[G]`: this is the cancellation theorem
`TauCeti.nonempty_quotient_span_singleton_linearEquiv_of_injective` for the semisimple ring
`k[G]` (Maschke) applied to the defining relation.

The same cancellation applies after a flat base change `R → k` to a field in which `#G` is
nonzero: the base change `M₀ ⊗[R] k` of the integral tame-frame module is the base change
`R[G] ⊗[R] k` of the group ring, as a left `R[G]`-module
(`TauCeti.nonempty_quotient_span_singleton_tensor_linearEquiv_of_injective`). For `R = ℤ_p` and
`k = ℚ_p` this is the rationalisation `M₀ ⊗ ℚ_p ≃ ℚ_p[G]` of the tame-frame module of a finite
tame layer of local fields, whose sharp exponents are supplied by
`TauCeti.exists_tameFrame_exponents`.

## Main results

* `TauCeti.tameFrameRelationMap_injective_of_card_ne_zero`: sharp finite quotient implies
  injectivity, for instance over `ℤ_p` with `G` finite.
* `TauCeti.nonempty_tameFrameModule_linearEquiv_of_relationMap_injective`: under Maschke's
  condition, an injective tame-frame relation map presents the regular representation.
* `TauCeti.nonempty_tameFrameModule_tensor_linearEquiv_of_relationMap_injective`: after a flat
  base change to a field satisfying Maschke's condition, an injective tame-frame relation map
  presents the base change of the group ring.
* `TauCeti.nonempty_tameFrameModule_tensorRat_linearEquiv`: the rationalisation
  `M₀ ⊗[ℤ_p] ℚ_p ≃ ℤ_p[G] ⊗[ℤ_p] ℚ_p` of the tame-frame module with sharp exponents.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra _root_.TensorProduct

universe u v

variable {G : Type v}

/-- Let `R` be a commutative ring of characteristic zero without zero divisors, and let `σ, τ`
have finite order. For natural numbers `a, b`, nonzero finite cardinality of the sharp quotient
`R[G] / (σ - a, τ - b)` implies that the tame-frame relation map is injective. For `R = ℤ_p` and
finite `G` this is the integral injectivity input for the rational tame-frame computation. -/
theorem tameFrameRelationMap_injective_of_card_ne_zero [Monoid G] {R : Type u} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {σ τ : G} (hσ : IsOfFinOrder σ) (hτ : IsOfFinOrder τ)
    {a b : ℕ}
    (hcard : Nat.card (MonoidAlgebra R G ⧸ Ideal.span
      {single σ (1 : R) - single 1 (a : R), single τ (1 : R) - single 1 (b : R)}) ≠ 0) :
    Function.Injective (tameFrameRelationMap R G σ τ (a : R) (b : R)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  by_contra hx0
  have hσx : x * (single σ (1 : R) - single 1 (a : R)) = 0 := by
    simpa using congrArg (fun y : Fin 2 →₀ MonoidAlgebra R G ↦ y 0) hx
  have hτx : x * (single τ (1 : R) - single 1 (b : R)) = 0 := by
    simpa using congrArg (fun y : Fin 2 →₀ MonoidAlgebra R G ↦ y 1) hx
  have ha := nat_eq_one_of_mul_single_sub_eq_zero hx0 hσ hσx
  have hb := nat_eq_one_of_mul_single_sub_eq_zero hx0 hτ hτx
  subst a
  subst b
  rw [Nat.cast_one] at hcard
  let I : Ideal (MonoidAlgebra R G) := Ideal.span
    {single σ (1 : R) - single 1 (1 : R), single τ (1 : R) - single 1 (1 : R)}
  have hI : I ≤ RingHom.ker (MonoidAlgebra.augmentation R G) := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    all_goals simp
  let A := MonoidAlgebra R G
  let _ : Module A R := Module.compHom R (MonoidAlgebra.augmentation R G)
  let aug : A →ₗ[A] R := {
    toFun := MonoidAlgebra.augmentation R G
    map_add' := map_add _
    map_smul' r x := map_mul _ r x }
  have hker : LinearMap.ker aug = RingHom.ker (MonoidAlgebra.augmentation R G) := by
    ext z
    simp [aug]
  have hIaug : I ≤ LinearMap.ker aug := hker ▸ hI
  let q : (A ⧸ I) →ₗ[A] R := Submodule.liftQ I aug hIaug
  have hq : Function.Surjective q := by
    intro r
    refine ⟨Submodule.Quotient.mk (single 1 r), ?_⟩
    simp [q, aug]
  let _ : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero hcard
  have : Finite R := Finite.of_surjective q hq
  exact not_finite R

variable {k : Type u} [Field k]

/-- Let `G` be finite and suppose that its cardinality is nonzero in `k`. If the tame-frame
relation map is injective, then the tame-frame module is linearly equivalent to the regular
representation `k[G]`. -/
theorem nonempty_tameFrameModule_linearEquiv_of_relationMap_injective [Group G] [Finite G]
    [NeZero (Nat.card G : k)]
    (σ τ : G) (a b : k) (hinj : Function.Injective (tameFrameRelationMap k G σ τ a b)) :
    Nonempty (TameFrameModule k G σ τ a b ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G) := by
  let A := MonoidAlgebra k G
  let v : Fin 2 →₀ A := (tameFrameRelations k G σ τ a b).relation ()
  have hmap : tameFrameRelationMap k G σ τ a b = LinearMap.toSpanSingleton A (Fin 2 →₀ A) v :=
    LinearMap.ext fun x ↦ by rw [tameFrameRelationMap_apply, LinearMap.toSpanSingleton_apply]
  obtain ⟨e⟩ := nonempty_quotient_span_singleton_linearEquiv_of_injective v
    (hmap ▸ hinj)
  -- `TameFrameModule` is the quotient by the span of the relations, which is the range of the
  -- relation map.
  have hspan :
      Submodule.span A (Set.range (tameFrameRelations k G σ τ a b).relation) =
        Submodule.span A {v} := by
    rw [← range_tameFrameRelationMap, hmap, LinearMap.range_toSpanSingleton]
  exact ⟨(Submodule.quotEquivOfEq _ _ hspan).trans e⟩

/-- **The base change of the tame-frame module to a field is the regular representation.** Let
`G` be finite, `R` a commutative ring and `k` a flat `R`-algebra which is a field in which the
order of `G` is nonzero. If the integral tame-frame relation map is injective, then the base change
`M₀ ⊗[R] k` of the tame-frame module is linearly equivalent, as a left `R[G]`-module, to the base
change `R[G] ⊗[R] k` of the group ring. -/
theorem nonempty_tameFrameModule_tensor_linearEquiv_of_relationMap_injective [Group G] [Finite G]
    {R : Type*} [CommRing R] [Algebra R k] [Module.Flat R k] [NeZero (Nat.card G : k)]
    (σ τ : G) (a b : R)
    (hinj : Function.Injective (tameFrameRelationMap R G σ τ a b)) :
    Nonempty ((TameFrameModule R G σ τ a b ⊗[R] k) ≃ₗ[MonoidAlgebra R G]
      (MonoidAlgebra R G ⊗[R] k)) := by
  let A := MonoidAlgebra R G
  let v : Fin 2 →₀ A := (tameFrameRelations R G σ τ a b).relation ()
  have hmap : tameFrameRelationMap R G σ τ a b = LinearMap.toSpanSingleton A (Fin 2 →₀ A) v :=
    LinearMap.ext fun x ↦ by rw [tameFrameRelationMap_apply, LinearMap.toSpanSingleton_apply]
  obtain ⟨e⟩ := nonempty_quotient_span_singleton_tensor_linearEquiv_of_injective (R := R) k v
    (hmap ▸ hinj)
  -- `TameFrameModule` is the quotient by the span of the relations, which is the range of the
  -- relation map.
  have hspan :
      Submodule.span A (Set.range (tameFrameRelations R G σ τ a b).relation) =
        Submodule.span A {v} := by
    rw [← range_tameFrameRelationMap, hmap, LinearMap.range_toSpanSingleton]
  exact ⟨(AlgebraTensorModule.congr (Submodule.quotEquivOfEq _ _ hspan)
    (LinearEquiv.refl R k)).trans e⟩

/-- **The rationalisation of the tame-frame module with sharp exponents.** Let `G` be a finite
group, `σ, τ : G`, and `a, b` natural numbers for which the quotient `ℤ_p[G] / (σ - a, τ - b)` is
finite, as the sharp exponents of a tame frame provide. Then
`M₀ ⊗[ℤ_p] ℚ_p ≃ ℤ_p[G] ⊗[ℤ_p] ℚ_p` as left `ℤ_p[G]`-modules: the rationalised tame-frame module
is the regular representation `ℚ_p[G]`. -/
theorem nonempty_tameFrameModule_tensorRat_linearEquiv {p : ℕ} [Fact p.Prime] [Group G]
    [Finite G] (σ τ : G) (a b : ℕ)
    (hcard : Nat.card (MonoidAlgebra ℤ_[p] G ⧸ Ideal.span
      {single σ (1 : ℤ_[p]) - a, single τ (1 : ℤ_[p]) - b}) ≠ 0) :
    Nonempty ((TameFrameModule ℤ_[p] G σ τ (a : ℤ_[p]) (b : ℤ_[p]) ⊗[ℤ_[p]] ℚ_[p])
      ≃ₗ[MonoidAlgebra ℤ_[p] G] (MonoidAlgebra ℤ_[p] G ⊗[ℤ_[p]] ℚ_[p])) := by
  simp only [natCast_def] at hcard
  exact nonempty_tameFrameModule_tensor_linearEquiv_of_relationMap_injective (k := ℚ_[p]) σ τ _ _
    (tameFrameRelationMap_injective_of_card_ne_zero (isOfFinOrder_of_finite σ)
      (isOfFinOrder_of_finite τ) hcard)

end TauCeti
