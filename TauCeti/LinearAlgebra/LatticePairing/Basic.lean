/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Integral pairings of two lattices and their cokernels

A *lattice pairing* is an integral bilinear map `u : Y × X → ℤ` between two `ℤ`-modules, with no
symmetry assumed and with `X` and `Y` allowed to differ. It is recorded curried, as
`Y →ₗ[ℤ] X →ₗ[ℤ] ℤ`, so the pairing *is* its adjoint `u♯ : Y → Hom(X, ℤ)`, `y ↦ (x ↦ u y x)`;
the transposed pairing is Mathlib's `LinearMap.flip`. The cokernel `Hom(X, ℤ) / u♯(Y)` of the
adjoint is `componentGroup u`. The pairing is *nondegenerate* when its adjoint is injective with
finite cokernel.

The motivating example is the monodromy pairing `X_{A^∨} × X_A → ℤ` between the toric character
lattices of a semistable abelian variety `A` and of its dual over a henselian discrete valuation
ring. It is nondegenerate, and Grothendieck identifies its cokernel with the geometric component
group of the Néron model of `A`. For a Tate curve with parameter of valuation `n` the pairing is
`rankOne n`, `(y, x) ↦ n y x` on `ℤ × ℤ`. This file computes the cokernel of `rankOne n` as
`ℤ / n`. Every class there is a *rank-one class* `rankOneClass n r`, the class of `x ↦ r x`, and
the class vanishes exactly when `n ∣ r`; the same holds for the transposed pairing.

The finite `ℚ / ℤ`-valued pairing between the cokernels of a nondegenerate lattice pairing and
of its transpose is constructed in `TauCeti.LinearAlgebra.LatticePairing.Discriminant`.

## Main declarations

* `TauCeti.LatticePairing X Y`: integral pairings `Y × X → ℤ`, curried.
* `TauCeti.LatticePairing.componentGroup`: the cokernel of the adjoint.
* `TauCeti.LatticePairing.IsNondegenerate`: injective adjoint with finite cokernel.
* `TauCeti.LatticePairing.natCard_smul_mem_range`: the order of the cokernel times any
  functional lies in the image of the adjoint.
* `TauCeti.LatticePairing.rankOne`: the pairing `(y, x) ↦ n y x` on `ℤ × ℤ`.
* `TauCeti.LatticePairing.rankOneClass`, `TauCeti.LatticePairing.rankOneDualClass`: the classes
  of `x ↦ r x` in the cokernels of `rankOne n` and of its transpose.
* `TauCeti.LatticePairing.natCard_componentGroup_rankOne`: the cokernel of `rankOne n` has
  `|n|` elements, and it is infinite for `n = 0`.

## References

* A. Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX, §§10–11.
-/

public section

namespace TauCeti

universe u v

/-- An integral pairing `Y × X → ℤ` of two `ℤ`-modules, written curried. A term
`u : LatticePairing X Y` is at once the pairing, `u y x`, and its adjoint
`u♯ : Y → Hom(X, ℤ)`; its transpose `X × Y → ℤ` is `u.flip`. -/
abbrev LatticePairing (X : Type u) (Y : Type v) [AddCommGroup X] [AddCommGroup Y] :
    Type (max u v) :=
  Y →ₗ[ℤ] X →ₗ[ℤ] ℤ

namespace LatticePairing

variable {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]

/-- The cokernel `Hom(X, ℤ) / u♯(Y)` of the adjoint of a lattice pairing. For the monodromy
pairing of a semistable abelian variety this is the geometric component group of its Néron
model. -/
abbrev componentGroup (u : LatticePairing X Y) : Type u :=
  (X →ₗ[ℤ] ℤ) ⧸ LinearMap.range u

/-- A lattice pairing is nondegenerate when its adjoint `u♯ : Y → Hom(X, ℤ)` is injective with
finite cokernel. -/
class IsNondegenerate (u : LatticePairing X Y) : Prop where
  /-- The adjoint `u♯ : Y → Hom(X, ℤ)` is injective. -/
  injective : Function.Injective u
  /-- The cokernel of the adjoint is finite. -/
  finite_componentGroup : Finite u.componentGroup

attribute [instance] IsNondegenerate.finite_componentGroup

/-- The order of the cokernel of the adjoint kills it: that order times any functional on `X` is
the adjoint of a vector of `Y`. For an infinite cokernel this holds through the junk value
`Nat.card = 0`. -/
theorem natCard_smul_mem_range (u : LatticePairing X Y) (a : X →ₗ[ℤ] ℤ) :
    Nat.card u.componentGroup • a ∈ LinearMap.range u := by
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact card_nsmul_eq_zero'

/-! ### The rank-one pairings -/

/-- The rank-one lattice pairing `(y, x) ↦ n y x` on `ℤ × ℤ`; `n` may vanish. Unlike the rank-one
integral lattice `TauCeti.IntegralLattice.rankOne`, which is a symmetric lattice in `ℚ` with a
`ℚ`-valued form, this is an integral pairing `ℤ × ℤ → ℤ` between two copies of `ℤ`. -/
def rankOne (n : ℤ) : LatticePairing ℤ ℤ :=
  n • LinearMap.mul ℤ ℤ

@[simp]
theorem rankOne_apply (n y x : ℤ) : rankOne n y x = n * y * x := by
  simp [rankOne, mul_assoc]

/-- The rank-one pairing is symmetric: it is its own transpose. -/
@[simp]
theorem flip_rankOne (n : ℤ) : (rankOne n).flip = rankOne n := by
  ext
  simp

/-- A functional `f : ℤ → ℤ` is in the image of the adjoint of `rankOne n` exactly when `n`
divides `f 1`. -/
theorem mem_range_rankOne_iff (n : ℤ) (f : ℤ →ₗ[ℤ] ℤ) :
    f ∈ LinearMap.range (rankOne n) ↔ n ∣ f 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, LinearMap.ext_ring ?_⟩
    simp [hy]

/-- The class in the cokernel of `rankOne n` of the functional `x ↦ r x`. -/
def rankOneClass (n : ℤ) : ℤ →ₗ[ℤ] (rankOne n).componentGroup :=
  (LinearMap.range (rankOne n)).mkQ ∘ₗ LinearMap.mul ℤ ℤ

/-- The class in the cokernel of the transpose of `rankOne n` of the functional `y ↦ s y`. -/
def rankOneDualClass (n : ℤ) : ℤ →ₗ[ℤ] componentGroup (rankOne n).flip :=
  (LinearMap.range (rankOne n).flip).mkQ ∘ₗ LinearMap.mul ℤ ℤ

theorem rankOneClass_apply (n r : ℤ) :
    rankOneClass n r = Submodule.Quotient.mk (LinearMap.mul ℤ ℤ r) :=
  (rfl)

theorem rankOneDualClass_apply (n s : ℤ) :
    rankOneDualClass n s = Submodule.Quotient.mk (LinearMap.mul ℤ ℤ s) :=
  (rfl)

private theorem mul_mem_range_rankOne_iff (n r : ℤ) :
    LinearMap.mul ℤ ℤ r ∈ LinearMap.range (rankOne n) ↔ n ∣ r := by
  rw [mem_range_rankOne_iff]
  simp

/-- The rank-one class of `r` vanishes exactly when `n` divides `r`. -/
@[simp]
theorem rankOneClass_eq_zero_iff (n r : ℤ) : rankOneClass n r = 0 ↔ n ∣ r := by
  rw [rankOneClass_apply, Submodule.Quotient.mk_eq_zero, mul_mem_range_rankOne_iff]

/-- The rank-one dual class of `s` vanishes exactly when `n` divides `s`. -/
@[simp]
theorem rankOneDualClass_eq_zero_iff (n s : ℤ) : rankOneDualClass n s = 0 ↔ n ∣ s := by
  rw [rankOneDualClass_apply, Submodule.Quotient.mk_eq_zero, flip_rankOne,
    mul_mem_range_rankOne_iff]

/-- Two rank-one classes agree exactly when their representatives are congruent modulo `n`. -/
theorem rankOneClass_eq_iff (n r r' : ℤ) : rankOneClass n r = rankOneClass n r' ↔ n ∣ r - r' := by
  rw [← sub_eq_zero, ← map_sub, rankOneClass_eq_zero_iff]

/-- Two rank-one dual classes agree exactly when their representatives are congruent modulo
`n`. -/
theorem rankOneDualClass_eq_iff (n s s' : ℤ) :
    rankOneDualClass n s = rankOneDualClass n s' ↔ n ∣ s - s' := by
  rw [← sub_eq_zero, ← map_sub, rankOneDualClass_eq_zero_iff]

/-- Every class in a quotient of `ℤ →ₗ[ℤ] ℤ` is the class of some `x ↦ r x`. -/
private theorem mkQ_comp_mul_surjective (p : Submodule ℤ (ℤ →ₗ[ℤ] ℤ)) :
    Function.Surjective (p.mkQ ∘ₗ LinearMap.mul ℤ ℤ) := by
  intro c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  refine ⟨f 1, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact LinearMap.ext_ring (by simp)

/-- Every class in the cokernel of `rankOne n` is a rank-one class. -/
theorem rankOneClass_surjective (n : ℤ) : Function.Surjective (rankOneClass n) :=
  mkQ_comp_mul_surjective _

/-- Every class in the cokernel of the transpose of `rankOne n` is a rank-one dual class. -/
theorem rankOneDualClass_surjective (n : ℤ) : Function.Surjective (rankOneDualClass n) :=
  mkQ_comp_mul_surjective _

/-- The cokernel of `rankOne n` is `ℤ / n`, of order `|n|`; for `n = 0` it is `ℤ`, which is
infinite, so its `Nat.card` is `0`. -/
@[simp]
theorem natCard_componentGroup_rankOne (n : ℤ) :
    Nat.card (rankOne n).componentGroup = n.natAbs := by
  have hker : LinearMap.ker (rankOneClass n) = Ideal.span {n} := by
    ext r
    simp [Ideal.mem_span_singleton]
  rw [← Nat.card_congr ((rankOneClass n).quotKerEquivOfSurjective
      (rankOneClass_surjective n)).toEquiv, hker,
    Nat.card_congr (Int.quotientSpanEquivZMod n).toEquiv, Nat.card_zmod]

/-- The rank-one pairing with nonzero coefficient is nondegenerate. -/
instance (n : ℤ) [NeZero n] : (rankOne n).IsNondegenerate where
  injective y y' h := by
    simpa [NeZero.ne n] using LinearMap.congr_fun h 1
  finite_componentGroup := Nat.finite_of_card_ne_zero <| by
    rw [natCard_componentGroup_rankOne]
    exact Int.natAbs_ne_zero.mpr (NeZero.ne n)

end LatticePairing

end TauCeti
