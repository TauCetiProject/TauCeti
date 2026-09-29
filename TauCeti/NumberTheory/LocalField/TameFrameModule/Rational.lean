/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Eigenvector
public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.Algebra.MonoidAlgebra.RegularCancellation
public import TauCeti.NumberTheory.LocalField.TameFrameModule.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Rational structure of the tame-frame module

This file establishes the algebraic input for the rational tame-frame computation. The single
relation defines a map

`R[G] → R[G]²,  x ↦ x · (σ - a, τ - b)`.

For a finite group and natural-number exponents, nonzero finite cardinality of the sharp quotient
`ℤ_p[G] / (σ - a, τ - b)` implies that this map is injective. Over a field whose characteristic
does not divide `#G`, an injective tame-frame relation map presents one copy of the regular
representation `k[G]`: this is the Maschke cancellation theorem
`TauCeti.MonoidAlgebra.nonempty_quotient_span_singleton_linearEquiv_of_injective` applied to the
defining relation.

These results supply the injectivity and cancellation inputs used to identify the rationalized
integral tame-frame module after equivariant scalar extension from `ℤ_p` to `ℚ_p`.

## Main results

* `TauCeti.tameFrameRelationMap_injective_of_card_ne_zero`: sharp finite quotient implies
  injectivity over `ℤ_p`.
* `TauCeti.nonempty_tameFrameModule_linearEquiv_of_relationMap_injective`: under Maschke's
  condition, an injective tame-frame relation map presents the regular representation.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

universe u v

variable {G : Type v} [Group G]

variable {p : ℕ} [Fact p.Prime]

/-- For a finite group `G` and natural numbers `a, b`, nonzero finite cardinality of the sharp
quotient `ℤ_p[G] / (σ - a, τ - b)` implies that the tame-frame relation map is injective. This is
the integral injectivity input for the rational tame-frame computation. -/
theorem tameFrameRelationMap_injective_of_card_ne_zero [Finite G]
    (σ τ : G) (a b : ℕ)
    (hcard : Nat.card (MonoidAlgebra ℤ_[p] G ⧸ Ideal.span
      {single σ (1 : ℤ_[p]) - single 1 (a : ℤ_[p]),
        single τ (1 : ℤ_[p]) - single 1 (b : ℤ_[p])}) ≠ 0) :
    Function.Injective (tameFrameRelationMap ℤ_[p] G σ τ (a : ℤ_[p]) (b : ℤ_[p])) := by
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  by_contra hx0
  have hσ : x * (single σ (1 : ℤ_[p]) - single 1 (a : ℤ_[p])) = 0 := by
    simpa using congrArg (fun y : Fin 2 →₀ MonoidAlgebra ℤ_[p] G ↦ y 0) hx
  have hτ : x * (single τ (1 : ℤ_[p]) - single 1 (b : ℤ_[p])) = 0 := by
    simpa using congrArg (fun y : Fin 2 →₀ MonoidAlgebra ℤ_[p] G ↦ y 1) hx
  have ha := MonoidAlgebra.nat_eq_one_of_mul_single_sub_eq_zero hx0 (isOfFinOrder_of_finite σ) hσ
  have hb := MonoidAlgebra.nat_eq_one_of_mul_single_sub_eq_zero hx0 (isOfFinOrder_of_finite τ) hτ
  subst a
  subst b
  let I : Ideal (MonoidAlgebra ℤ_[p] G) := Ideal.span
    {single σ (1 : ℤ_[p]) - single 1 (1 : ℤ_[p]),
      single τ (1 : ℤ_[p]) - single 1 (1 : ℤ_[p])}
  have hI : I ≤ RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] G) := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    all_goals simp
  let A := MonoidAlgebra ℤ_[p] G
  let _ : Module A ℤ_[p] := Module.compHom ℤ_[p] (MonoidAlgebra.augmentation ℤ_[p] G)
  let aug : A →ₗ[A] ℤ_[p] := {
    toFun := MonoidAlgebra.augmentation ℤ_[p] G
    map_add' := map_add _
    map_smul' r x := map_mul _ r x }
  have hker : LinearMap.ker aug = RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] G) := by
    ext z
    simp [aug]
  have hIaug : I ≤ LinearMap.ker aug := hker ▸ hI
  let q : (A ⧸ I) →ₗ[A] ℤ_[p] := Submodule.liftQ I aug hIaug
  have hq : Function.Surjective q := by
    intro r
    refine ⟨Submodule.Quotient.mk (single 1 r), ?_⟩
    simp [q, aug]
  let _ : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero hcard
  have : Finite ℤ_[p] := Finite.of_surjective q hq
  exact not_finite ℤ_[p]

variable {k : Type u} [Field k]

/-- Let `G` be finite and suppose that its cardinality is nonzero in `k`. If the tame-frame
relation map is injective, then the tame-frame module is linearly equivalent to the regular
representation `k[G]`. -/
theorem nonempty_tameFrameModule_linearEquiv_of_relationMap_injective [Finite G]
    [NeZero (Nat.card G : k)]
    (σ τ : G) (a b : k) (hinj : Function.Injective (tameFrameRelationMap k G σ τ a b)) :
    Nonempty (TameFrameModule k G σ τ a b ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G) := by
  let A := MonoidAlgebra k G
  let v : Fin 2 →₀ A := (tameFrameRelations k G σ τ a b).relation ()
  have hmap : tameFrameRelationMap k G σ τ a b = LinearMap.toSpanSingleton A (Fin 2 →₀ A) v :=
    LinearMap.ext fun x ↦ by rw [tameFrameRelationMap_apply, LinearMap.toSpanSingleton_apply]
  obtain ⟨e⟩ := MonoidAlgebra.nonempty_quotient_span_singleton_linearEquiv_of_injective v
    (hmap ▸ hinj)
  -- `TameFrameModule` is the quotient by the span of the relations, which is the range of the
  -- relation map.
  have hspan :
      Submodule.span A (Set.range (tameFrameRelations k G σ τ a b).relation) =
        Submodule.span A {v} := by
    rw [← range_tameFrameRelationMap, hmap, LinearMap.range_toSpanSingleton]
  exact ⟨(Submodule.quotEquivOfEq _ _ hspan).trans e⟩

end TauCeti
