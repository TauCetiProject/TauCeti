/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Stable equivalence of modules

Two modules `P` and `Q` over a semiring `R` are *stably equivalent* if `P × Rⁿ` and `Q × Rⁿ` are
`R`-linearly isomorphic for some natural number `n`; the same finite free module is added on both
sides. For finitely generated projective modules this is the relation identifying two modules in
the split Grothendieck group `K₀(R)`: equality of classes in a group completion is witnessed by a
common summand, and a finitely generated projective summand can be enlarged to a finite free one.
Stable equivalence to `Rᵐ` is the stable freeness that measures the classes `[P] - m[R]` in
locally free class groups of orders.

This file develops the relation for an arbitrary semiring `R`, with no commutativity or finiteness
hypotheses: it is an equivalence relation, it is implied by linear isomorphism, it is compatible
with binary products, and any finite free module can serve as the common summand. Over a ring with
the strong rank condition, stably equivalent free modules have the same rank, so for instance the
zero module and `ℤ` are not stably equivalent over `ℤ`.

## Main definitions

* `TauCeti.StableEquivalent R P Q`: `P × (Fin n → R) ≃ₗ[R] Q × (Fin n → R)` for some `n : ℕ`.

## Main results

* `TauCeti.StableEquivalent.refl`, `TauCeti.StableEquivalent.symm`,
  `TauCeti.StableEquivalent.trans`: stable equivalence is an equivalence relation.
* `TauCeti.StableEquivalent.of_equiv`: linearly isomorphic modules are stably equivalent.
* `TauCeti.StableEquivalent.prod`: stable equivalence is compatible with binary products.
* `TauCeti.StableEquivalent.of_prod_equiv_prod`: a linear isomorphism `P × F ≃ₗ[R] Q × F` with
  `F` finite free shows that `P` and `Q` are stably equivalent.
* `TauCeti.StableEquivalent.exists_forall_ge`: the common free summand may be taken arbitrarily
  large.
* `TauCeti.stableEquivalent_fin_fun_iff`: `P` is stably equivalent to `Rᵐ` if and only if
  `P × Rᵏ ≃ₗ[R] Rᵐ⁺ᵏ` for some `k`; such a `P` is stably free (`StableEquivalent.isStablyFree`).
* `TauCeti.StableEquivalent.lift_rank_eq`, `TauCeti.StableEquivalent.finrank_eq`: over a ring
  with the strong rank condition, stably equivalent free modules have the same rank.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society (2013), Chapter II, §1, Proposition 1.1 and
  Corollary 1.3, and §2, p. 5.
-/

public section

universe u v w x

namespace TauCeti

open Module

section Semiring

variable (R : Type u) [Semiring R] (P : Type v) (Q : Type w) (T : Type x)
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q] [AddCommMonoid T] [Module R T]

/-- Two `R`-modules `P` and `Q` are *stably equivalent* if `P × Rⁿ` and `Q × Rⁿ` are
`R`-linearly isomorphic for some natural number `n`. The same finite free module `Rⁿ` is added
to both sides. -/
def StableEquivalent : Prop :=
  ∃ n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R] (Q × (Fin n → R)))

variable {R P Q T}

/-- Unfolding `StableEquivalent`: a natural number `n` and a linear isomorphism
`P × Rⁿ ≃ₗ[R] Q × Rⁿ`. -/
theorem stableEquivalent_iff :
    StableEquivalent R P Q ↔ ∃ n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R] (Q × (Fin n → R))) :=
  Iff.rfl

/-- Swap the two free summands of `(M × A) × B`. -/
private def prodPadComm (M A B : Type*) [AddCommMonoid M] [Module R M] [AddCommMonoid A]
    [Module R A] [AddCommMonoid B] [Module R B] : ((M × A) × B) ≃ₗ[R] ((M × B) × A) :=
  (LinearEquiv.prodAssoc R M A B).trans <|
    ((LinearEquiv.refl R M).prodCongr (LinearEquiv.prodComm R A B)).trans
      (LinearEquiv.prodAssoc R M B A).symm

/-- `Rⁿ⁺ᵏ` splits as `Rⁿ × Rᵏ`. -/
private def finFunAddEquiv (n k : ℕ) : (Fin (n + k) → R) ≃ₗ[R] (Fin n → R) × (Fin k → R) :=
  (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)

namespace StableEquivalent

/-- Linearly isomorphic modules are stably equivalent, with no free summand. -/
theorem of_equiv (e : P ≃ₗ[R] Q) : StableEquivalent R P Q :=
  ⟨0, ⟨e.prodCongr (LinearEquiv.refl R _)⟩⟩

variable (R P) in
/-- Every module is stably equivalent to itself. -/
theorem refl : StableEquivalent R P P :=
  of_equiv (LinearEquiv.refl R P)

/-- Stable equivalence is symmetric. -/
theorem symm (h : StableEquivalent R P Q) : StableEquivalent R Q P :=
  let ⟨n, ⟨e⟩⟩ := h
  ⟨n, ⟨e.symm⟩⟩

/-- Stable equivalence is symmetric, stated as an `Iff`. -/
theorem comm : StableEquivalent R P Q ↔ StableEquivalent R Q P :=
  ⟨symm, symm⟩

/-- A linear isomorphism `P × F ≃ₗ[R] Q × F` with `F` finite free shows that `P` and `Q` are
stably equivalent: the common summand need only be isomorphic to some `Rⁿ`. -/
theorem of_prod_equiv_prod {F : Type*} [AddCommMonoid F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (e : (P × F) ≃ₗ[R] (Q × F)) : StableEquivalent R P Q :=
  -- A finite basis of `F` identifies it with `Rᵏ`.
  let f : F ≃ₗ[R] (Fin _ → R) := (Module.Free.chooseBasis R F).equivFun.trans
    (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)
  ⟨_, ⟨(((LinearEquiv.refl R P).prodCongr f).symm.trans e).trans
    ((LinearEquiv.refl R Q).prodCongr f)⟩⟩

/-- Stable equivalence is transitive. -/
theorem trans (h₁ : StableEquivalent R P Q) (h₂ : StableEquivalent R Q T) :
    StableEquivalent R P T := by
  obtain ⟨n, ⟨e₁⟩⟩ := h₁
  obtain ⟨m, ⟨e₂⟩⟩ := h₂
  -- `P × (Rⁿ × Rᵐ) ≃ (Q × Rⁿ) × Rᵐ ≃ (Q × Rᵐ) × Rⁿ ≃ (T × Rᵐ) × Rⁿ ≃ T × (Rⁿ × Rᵐ)`.
  refine of_prod_equiv_prod (F := (Fin n → R) × (Fin m → R)) <|
    (LinearEquiv.prodAssoc R P _ _).symm.trans <|
      (e₁.prodCongr (LinearEquiv.refl R _)).trans <| (prodPadComm Q _ _).trans <|
        (e₂.prodCongr (LinearEquiv.refl R _)).trans <| (prodPadComm T _ _).trans <|
          LinearEquiv.prodAssoc R T _ _

/-- Stable equivalence is compatible with binary products. -/
theorem prod {P' : Type*} {Q' : Type*} [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q']
    [Module R Q'] (h : StableEquivalent R P Q) (h' : StableEquivalent R P' Q') :
    StableEquivalent R (P × P') (Q × Q') := by
  obtain ⟨n, ⟨e⟩⟩ := h
  obtain ⟨m, ⟨e'⟩⟩ := h'
  refine of_prod_equiv_prod (F := (Fin n → R) × (Fin m → R)) <|
    (LinearEquiv.prodProdProdComm R P P' _ _).trans <|
      (e.prodCongr e').trans (LinearEquiv.prodProdProdComm R Q _ Q' _)

/-- The common free summand of a stable equivalence may be taken as large as desired. -/
theorem exists_forall_ge (h : StableEquivalent R P Q) :
    ∃ n : ℕ, ∀ m ≥ n, Nonempty ((P × (Fin m → R)) ≃ₗ[R] (Q × (Fin m → R))) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  let f := (LinearEquiv.refl R P).prodCongr (finFunAddEquiv n k)
  let g := (LinearEquiv.refl R Q).prodCongr (finFunAddEquiv (R := R) n k)
  exact ⟨f.trans <| (LinearEquiv.prodAssoc R P _ _).symm.trans <|
    (e.prodCongr (LinearEquiv.refl R _)).trans <| (LinearEquiv.prodAssoc R Q _ _).trans g.symm⟩

end StableEquivalent

/-- A module `P` is stably equivalent to `Rᵐ` if and only if `P × Rᵏ ≃ₗ[R] Rᵐ⁺ᵏ` for some
natural number `k`. -/
theorem stableEquivalent_fin_fun_iff {m : ℕ} :
    StableEquivalent R P (Fin m → R) ↔
      ∃ k : ℕ, Nonempty ((P × (Fin k → R)) ≃ₗ[R] (Fin (m + k) → R)) :=
  exists_congr fun k =>
    ⟨fun ⟨e⟩ => ⟨e.trans (finFunAddEquiv m k).symm⟩, fun ⟨e⟩ => ⟨e.trans (finFunAddEquiv m k)⟩⟩

end Semiring

section Ring

variable {R : Type u} [Ring R] {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

namespace StableEquivalent

/-- A module that is stably equivalent to `Rᵐ` is stably free in Mathlib's sense. -/
theorem isStablyFree {m : ℕ} (h : StableEquivalent R P (Fin m → R)) : IsStablyFree R P := by
  obtain ⟨k, ⟨e⟩⟩ := stableEquivalent_fin_fun_iff.mp h
  have : Module.Free R (P × (Fin k → R)) := Module.Free.of_equiv e.symm
  exact IsStablyFree.of_free_prod R P (Fin k → R)

end StableEquivalent

end Ring

section StrongRankCondition

variable {R : Type u} [Semiring R] {P : Type v} {Q : Type w} [AddCommMonoid P] [Module R P]
  [AddCommMonoid Q] [Module R Q]

namespace StableEquivalent

variable [StrongRankCondition R] [Module.Free R P] [Module.Free R Q]

/-- Over a ring with the strong rank condition, stably equivalent free modules have the same
rank. -/
theorem lift_rank_eq (h : StableEquivalent R P Q) :
    Cardinal.lift.{w} (Module.rank R P) = Cardinal.lift.{v} (Module.rank R Q) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  have := e.lift_rank_eq
  simp only [rank_prod, rank_fin_fun, Cardinal.lift_add, Cardinal.lift_lift,
    Cardinal.lift_natCast, Cardinal.add_nat_inj] at this
  exact Cardinal.lift_umax_eq.{v, w, u}.mp this

/-- Over a ring with the strong rank condition, stably equivalent free modules have the same
`finrank`. -/
theorem finrank_eq (h : StableEquivalent R P Q) : finrank R P = finrank R Q := by
  unfold finrank
  rw [← Cardinal.toNat_lift.{w}, h.lift_rank_eq, Cardinal.toNat_lift]

end StableEquivalent

end StrongRankCondition

/-- Over `ℤ`, the zero module and `ℤ` are not stably equivalent: their ranks differ. -/
example : ¬ StableEquivalent ℤ (Fin 0 → ℤ) ℤ := fun h => by
  simpa using h.finrank_eq

end TauCeti
