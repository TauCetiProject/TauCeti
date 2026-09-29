/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.NumberTheory.LocalField.TameFrameModule.Basic
public import TauCeti.RingTheory.KrullSchmidt.Cancellation
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RepresentationTheory.Maschke

/-!
# Rational structure of the tame-frame module

This file proves the algebraic core of the rational tame-frame computation. The single relation
defines a map

`R[G] → R[G]²,  x ↦ x · (σ - a, τ - b)`.

Over `ℤ_p`, finiteness of the sharp quotient `R[G] / (σ - a, τ - b)` forces this map to be
injective. Indeed, an element in its kernel forces both natural-number exponents to equal one;
the augmentation then exhibits the sharp quotient as infinite, a contradiction. Over any field
whose characteristic does not divide `#G`, Maschke's theorem splits the image of an injective
relation map, and finite-length cancellation identifies the quotient with one copy of the regular
representation.

The later local-field theorem obtains the rationalized integral tame-frame module by applying
these results through equivariant scalar extension from `ℤ_p` to `ℚ_p`.

## Main results

* `TauCeti.tameFrameRelationMap`: the one-relation map defining the tame-frame module.
* `TauCeti.tameFrameRelationMap_injective_of_card_ne_zero`: sharp finite quotient implies
  injectivity over `ℤ_p`.
* `TauCeti.tameFrameModule_linearEquiv_of_relationMap_injective`: under Maschke's condition, an
  injective relation map has cokernel isomorphic to the regular representation.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

universe u v

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The left `R[G]`-linear map whose cokernel is the tame-frame module: it sends `x` to
`x · (σ - a, τ - b)`. -/
noncomputable def tameFrameRelationMap (R : Type u) [CommRing R] (G : Type v) [Group G]
    (σ τ : G) (a b : R) :
    MonoidAlgebra R G →ₗ[MonoidAlgebra R G] (Fin 2 →₀ MonoidAlgebra R G) :=
  LinearMap.toSpanSingleton (MonoidAlgebra R G) _
    ((tameFrameRelations R G σ τ a b).relation ())

/-- The zeroth coordinate of the tame-frame relation map is right multiplication by `σ - a`. -/
@[simp]
theorem tameFrameRelationMap_apply_zero (σ τ : G) (a b : R) (x : MonoidAlgebra R G) :
    tameFrameRelationMap R G σ τ a b x 0 =
      x * (single σ 1 - single 1 a) := by
  simp [tameFrameRelationMap, LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The first coordinate of the tame-frame relation map is right multiplication by `τ - b`. -/
@[simp]
theorem tameFrameRelationMap_apply_one (σ τ : G) (a b : R) (x : MonoidAlgebra R G) :
    tameFrameRelationMap R G σ τ a b x 1 =
      x * (single τ 1 - single 1 b) := by
  simp [tameFrameRelationMap, LinearMap.toSpanSingleton_apply, smul_eq_mul]

variable {p : ℕ} [Fact p.Prime]

private theorem nat_eq_one_of_mul_single_sub_eq_zero [Finite G]
    (x : MonoidAlgebra ℤ_[p] G) (hx : x ≠ 0) (g : G) (a : ℕ)
    (h : x * (single g (1 : ℤ_[p]) - single 1 (a : ℤ_[p])) = 0) : a = 1 := by
  have hmul : x * single g (1 : ℤ_[p]) = (a : ℤ_[p]) • x := by
    rw [mul_sub, sub_eq_zero] at h
    rw [← single_one_comm] at h
    refine h.trans ?_
    ext i
    rw [coeff_single_one_mul, coeff_smul_apply]
    rfl
  have hpow (n : ℕ) :
      x * single (g ^ n) (1 : ℤ_[p]) = ((a : ℤ_[p]) ^ n) • x := by
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul, ← one_def, mul_one]
    | succ n ih =>
      rw [pow_succ, ← of_apply ℤ_[p] G (g ^ n * g), map_mul, of_apply, of_apply,
        ← mul_assoc, ih, smul_mul_assoc, hmul, smul_smul, pow_succ]
  have ha : (a : ℤ_[p]) ^ orderOf g = 1 := by
    have hfix := hpow (orderOf g)
    rw [pow_orderOf_eq_one, ← one_def, mul_one] at hfix
    obtain ⟨i, hi⟩ : ∃ i, x.coeff i ≠ 0 := by
      by_contra hall
      apply hx
      ext i
      simpa using not_exists.mp hall i
    have hi' := congrArg (fun y : MonoidAlgebra ℤ_[p] G ↦ y.coeff i) hfix
    rw [coeff_smul_apply, smul_eq_mul] at hi'
    exact mul_right_cancel₀ hi (by simpa only [one_mul] using hi'.symm)
  have ha' : a ^ orderOf g = 1 := by exact_mod_cast ha
  exact (Nat.pow_eq_one.mp ha').resolve_right (orderOf_pos g).ne'

/-- If the quotient by the two tame-frame relations has nonzero finite cardinality, then the
relation map over `ℤ_p[G]` is injective. This is the injectivity input in the rational
tame-frame computation.

The natural-number condition on `a` and `b` is essential to the proof: finite order of `σ` and
`τ` turns a nonzero kernel element into the equalities `a = b = 1`. In that remaining case the
augmentation descends to a surjection from the quotient onto the infinite ring `ℤ_p`. -/
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
  have ha := nat_eq_one_of_mul_single_sub_eq_zero x hx0 σ a hσ
  have hb := nat_eq_one_of_mul_single_sub_eq_zero x hx0 τ b hτ
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
  let q : (A ⧸ I) →ₗ[A] ℤ_[p] := Submodule.liftQ I aug fun z hz ↦ by
    change MonoidAlgebra.augmentation ℤ_[p] G z = 0
    exact RingHom.mem_ker.mp (hI hz)
  have hq : Function.Surjective q := by
    intro r
    refine ⟨Submodule.Quotient.mk (single 1 r), ?_⟩
    simp [q, aug]
  let _ : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero hcard
  have : Finite ℤ_[p] := Finite.of_surjective q hq
  exact not_finite ℤ_[p]

variable {k : Type u} [Field k]

/-- When the characteristic of a field does not divide `#G`, the tame-frame module is one regular
representation whenever its relation map is injective.

Maschke's theorem supplies a complement `Q` to the copy of `k[G]` generated by the relation in
`k[G]²`. Thus `k[G] × Q ≃ k[G] × k[G]`; finite-length cancellation gives `Q ≃ k[G]`, and
the quotient by the relation is `Q`. -/
theorem tameFrameModule_linearEquiv_of_relationMap_injective [Finite G]
    [NeZero (Nat.card G : k)]
    (σ τ : G) (a b : k) (hinj : Function.Injective (tameFrameRelationMap k G σ τ a b)) :
    Nonempty (TameFrameModule k G σ τ a b ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G) := by
  let A := MonoidAlgebra k G
  let V := Fin 2 →₀ A
  let v : V := (tameFrameRelations k G σ τ a b).relation ()
  let S : Submodule A V := Submodule.span A {v}
  obtain ⟨Q, hSQ⟩ := MonoidAlgebra.Submodule.exists_isCompl S
  let eS : A ≃ₗ[A] S :=
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton A V v) hinj).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton v))
  let eV : V ≃ₗ[A] A × A :=
    (Finsupp.linearEquivFunOnFinite A A (Fin 2)).trans (LinearEquiv.finTwoArrow A A)
  let eProd :=
    (eS.prodCongr (LinearEquiv.refl A Q)).trans
      ((Submodule.prodEquivOfIsCompl S Q hSQ).trans eV)
  have hA : IsFiniteLength A A := by
    apply (IsSemisimpleModule.finite_tfae (R := A) (M := A)).out 1 4 |>.mp
    infer_instance
  obtain ⟨eQ⟩ := nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength
    (A := A) (M := Q) (N := A) (P := A) hA
    ⟨(LinearEquiv.prodComm A Q A).trans eProd⟩
  change Nonempty ((V ⧸ Submodule.span A (Set.range fun _ : Unit ↦ v)) ≃ₗ[A] A)
  have hrange : Set.range (fun _ : Unit ↦ v) = {v} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨(), h.symm⟩⟩
  rw [hrange]
  exact ⟨(S.quotientEquivOfIsCompl Q hSQ).trans eQ⟩

end TauCeti
