/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Frobenius between quotient rings

Let `A` be a commutative ring, `p` a prime and `I, J` ideals of `A` with `p ∈ J` and `x ^ p ∈ J`
for every `x ∈ I`. Then `x ↦ x ^ p` induces a ring homomorphism `A ⧸ I →+* A ⧸ J`: it is the
`p`-th power map `TauCeti.powRingHom` of `A ⧸ J`, in which `p` vanishes, composed with the
projection `A → A ⧸ J`, and it kills `I`. No ring in sight need have characteristic `p`, so this is
not an instance of Mathlib's `frobenius`.

The main case is `I = (ϖ)` and `J = (ϖ ^ p)` for an element `ϖ` with `ϖ ^ p ∣ p`, the map
`A ⧸ ϖ → A ⧸ ϖ ^ p` whose bijectivity on the power-bounded subring defines perfectoid Tate rings
(Scholze, *Étale cohomology of diamonds*, Definition 3.1). When `A` is integrally closed in a ring
in which `ϖ` becomes a unit, this map is automatically injective.

## Main definitions

* `Ideal.frobeniusQuot`: the ring homomorphism `A ⧸ I →+* A ⧸ J`, `[x] ↦ [x ^ p]`.
* `TauCeti.frobeniusModPow`: its specialisation `A ⧸ (ϖ) →+* A ⧸ (ϖ ^ p)` for `ϖ ^ p ∣ p`.

## Main results

* `Ideal.frobeniusQuot_surjective_iff`, `Ideal.frobeniusQuot_injective_iff`: elementwise forms of
  surjectivity and injectivity.
* `TauCeti.frobeniusModPow_surjective_iff`, `TauCeti.frobeniusModPow_injective_iff`: the same for
  `frobeniusModPow`, as divisibility conditions.
* `TauCeti.frobeniusModPow_injective`: `frobeniusModPow` is injective when `A` is integrally closed
  in an algebra in which `ϖ` is a unit.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1 and Remark 3.2.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A] (I J : Ideal A) (p : ℕ) [Fact p.Prime]

/-- The Frobenius `A ⧸ I →+* A ⧸ J`, `[x] ↦ [x ^ p]`, for ideals `I, J` with `p ∈ J` and
`x ^ p ∈ J` for every `x ∈ I`. -/
noncomputable def frobeniusQuot (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J) :
    A ⧸ I →+* A ⧸ J :=
  Quotient.lift I ((TauCeti.powRingHom (A ⧸ J) p
      (by rw [← map_natCast (Quotient.mk J), Quotient.eq_zero_iff_mem]; exact hpJ)).comp
        (Quotient.mk J))
    fun x hx ↦ by
      rw [RingHom.comp_apply, TauCeti.powRingHom_apply, ← map_pow, Quotient.eq_zero_iff_mem]
      exact hIJ x hx

variable {I J p} (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J)

/-- `frobeniusQuot` sends the class of `x` to the class of `x ^ p`. -/
@[simp]
theorem frobeniusQuot_mk (x : A) :
    frobeniusQuot I J p hpJ hIJ (Quotient.mk I x) = Quotient.mk J (x ^ p) := by
  rw [frobeniusQuot, Quotient.lift_mk, RingHom.comp_apply, TauCeti.powRingHom_apply, map_pow]

/-- `[x] ↦ [x ^ p]` is surjective exactly when every element is a `p`-th power modulo `J`. -/
theorem frobeniusQuot_surjective_iff :
    Function.Surjective (frobeniusQuot I J p hpJ hIJ) ↔ ∀ x : A, ∃ y, x - y ^ p ∈ J := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h (Quotient.mk J x)
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
    rw [frobeniusQuot_mk, eq_comm, Quotient.eq] at hy
    exact ⟨y, hy⟩
  · intro x
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := h x
    exact ⟨Quotient.mk I y, by rw [frobeniusQuot_mk, eq_comm, Quotient.eq]; exact hy⟩

/-- `[x] ↦ [x ^ p]` is injective exactly when `y ^ p ∈ J` forces `y ∈ I`. -/
theorem frobeniusQuot_injective_iff :
    Function.Injective (frobeniusQuot I J p hpJ hIJ) ↔ ∀ y : A, y ^ p ∈ J → y ∈ I := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [← Quotient.eq_zero_iff_mem]
    exact h _ (by rwa [frobeniusQuot_mk, Quotient.eq_zero_iff_mem])
  · obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
    rw [frobeniusQuot_mk, Quotient.eq_zero_iff_mem] at hy
    exact Quotient.eq_zero_iff_mem.mpr (h y hy)

end Ideal

namespace TauCeti

open Ideal

variable {A : Type*} [CommRing A] {ϖ : A} (p : ℕ) [Fact p.Prime]

/-- The Frobenius `A ⧸ (ϖ) →+* A ⧸ (ϖ ^ p)`, `[x] ↦ [x ^ p]`, for an element `ϖ` with
`ϖ ^ p ∣ p`. -/
noncomputable def frobeniusModPow (h : ϖ ^ p ∣ (p : A)) :
    A ⧸ span {ϖ} →+* A ⧸ span {ϖ ^ p} :=
  frobeniusQuot _ _ p (mem_span_singleton.mpr h) fun x hx ↦ by
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hx
    exact mem_span_singleton.mpr ⟨c ^ p, mul_pow ϖ c p⟩

variable {p} (h : ϖ ^ p ∣ (p : A))

/-- `frobeniusModPow` sends the class of `x` to the class of `x ^ p`. -/
@[simp]
theorem frobeniusModPow_mk (x : A) :
    frobeniusModPow p h (Quotient.mk _ x) = Quotient.mk _ (x ^ p) :=
  frobeniusQuot_mk _ _ x

/-- Frobenius `A ⧸ (ϖ) → A ⧸ (ϖ ^ p)` is surjective exactly when every element is a `p`-th power
modulo `ϖ ^ p`. -/
theorem frobeniusModPow_surjective_iff :
    Function.Surjective (frobeniusModPow p h) ↔ ∀ x : A, ∃ y, ϖ ^ p ∣ x - y ^ p := by
  simp_rw [← mem_span_singleton]
  exact frobeniusQuot_surjective_iff _ _

/-- Frobenius `A ⧸ (ϖ) → A ⧸ (ϖ ^ p)` is injective exactly when `ϖ ^ p ∣ y ^ p` forces
`ϖ ∣ y`. -/
theorem frobeniusModPow_injective_iff :
    Function.Injective (frobeniusModPow p h) ↔ ∀ y : A, ϖ ^ p ∣ y ^ p → ϖ ∣ y := by
  simp_rw [← mem_span_singleton]
  exact frobeniusQuot_injective_iff _ _

/-- If `A` is integrally closed in an `A`-algebra `B` in which `ϖ` is a unit, then Frobenius
`A ⧸ (ϖ) → A ⧸ (ϖ ^ p)` is injective: `ϖ ^ p ∣ y ^ p` makes `(y / ϖ) ^ p` lie in `A`, so `y / ϖ`
is integral over `A` and lies in `A` (Scholze, *Étale cohomology of diamonds*, Remark 3.2). -/
theorem frobeniusModPow_injective {B : Type*} [CommRing B] [Algebra A B]
    [IsIntegrallyClosedIn A B] (hϖ : IsUnit (algebraMap A B ϖ)) :
    Function.Injective (frobeniusModPow p h) :=
  (frobeniusModPow_injective_iff h).mpr fun _ ↦
    (IsIntegrallyClosedIn.pow_dvd_pow_iff (NeZero.ne p) hϖ).mp

end TauCeti
