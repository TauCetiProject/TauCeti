/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Order.DirectedInverseSystem

/-!
# Composites and functoriality of `⋆`-algebra homomorphisms

A sequence of ⋆-algebra homomorphisms `f n : A n →⋆ₐ[R] A (n + 1)` determines, for `i ≤ j`, the
composite `A i →⋆ₐ[R] A j` of `f i, …, f (j - 1)`. These composites form a directed system over
`ℕ`, which is how sequential inductive limits are usually presented. This is the ⋆-algebra
homomorphism version of Mathlib's `FirstOrder.Language.DirectedSystem.natLERec` and
`FirstOrder.Language.DirectedSystem.natLERec.directedSystem` (`Mathlib.ModelTheory.DirectLimit`),
whose construction through `Nat.leRecOn` it follows.

This file also records basic functoriality and injectivity lemmas for forgetting unitality on
`StarAlgHom`, together with injectivity and unitary-conjugacy transport along
`StarAlgEquiv.arrowCongr` and `StarAlgEquiv.arrowCongr'`.

## Main definitions

* `StarAlgHom.natLERec f i j h`: the composite `A i →⋆ₐ[R] A j` of the maps `f k` for
  `i ≤ k < j`.

## Main statements

* `StarAlgHom.natLERec_self_succ`: the composite from a stage to the next one is `f`.
* `StarAlgHom.natLERec_comp`: the composites compose.
* `StarAlgHom.natLERec.directedSystem`: the composites form a directed system.
* `StarAlgHom.natLERec_injective`: the composites of injective maps are injective.
* `StarAlgHom.toNonUnitalStarAlgHom_id`: forgetting unitality sends `StarAlgHom.id` to
  `NonUnitalStarAlgHom.id`.
* `StarAlgHom.toNonUnitalStarAlgHom_comp`: forgetting unitality preserves composition.
* `StarAlgHom.toNonUnitalStarAlgHom_injective`: forgetting unitality is injective.
* `StarAlgEquiv.arrowCongr'_injective_iff`, `StarAlgEquiv.arrowCongr_injective_iff`: conjugating
  by `⋆`-algebra equivalences preserves injectivity.
* `StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff`,
  `StarAlgEquiv.exists_unitary_conj_arrowCongr_iff`: conjugating by `⋆`-algebra equivalences
  preserves unitary conjugacy in the target.
-/

public section

namespace StarAlgHom

section NatLERec

variable {R : Type*} {A : ℕ → Type*} [CommSemiring R] [∀ n, Semiring (A n)]
  [∀ n, Algebra R (A n)] [∀ n, Star (A n)] (f : ∀ n, A n →⋆ₐ[R] A (n + 1))

/-- For a sequence of ⋆-algebra homomorphisms `f n : A n → A (n + 1)` and `i ≤ j`, the composite
`A i → A j` of the maps `f k` for `i ≤ k < j`. -/
def natLERec (i j : ℕ) (h : i ≤ j) : A i →⋆ₐ[R] A j :=
  Nat.leRecOn h (fun {k} g ↦ (f k).comp g) (StarAlgHom.id R _)

/-- The composite from a stage to itself is the identity. -/
@[simp]
theorem natLERec_self (i : ℕ) : natLERec f i i le_rfl = StarAlgHom.id R _ :=
  Nat.leRecOn_self _

/-- The composite to the stage after `k` is `f k` after the composite to `k`. -/
theorem natLERec_succ {i k : ℕ} (h : i ≤ k) :
    natLERec f i (k + 1) (h.trans k.le_succ) = (f k).comp (natLERec f i k h) :=
  Nat.leRecOn_succ h _

/-- The composite from a stage to the next one is the map `f` at that stage. -/
@[simp]
theorem natLERec_self_succ (n : ℕ) (h : n ≤ n + 1) : natLERec f n (n + 1) h = f n := by
  rw [natLERec_succ f le_rfl, natLERec_self, StarAlgHom.comp_id]

/-- The composites compose. -/
theorem natLERec_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (natLERec f j k hjk).comp (natLERec f i j hij) = natLERec f i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [natLERec_self, StarAlgHom.id_comp]
  | succ k hjk ih => rw [natLERec_succ f hjk, natLERec_succ f (hij.trans hjk),
      StarAlgHom.comp_assoc, ih]

/-- The composites of a sequence of ⋆-algebra homomorphisms form a directed system. -/
instance natLERec.directedSystem : DirectedSystem A fun i j h ↦ natLERec f i j h where
  map_self i a := by rw [natLERec_self, StarAlgHom.coe_id, id_eq]
  map_map k j i hij hjk a := by rw [← natLERec_comp f hij hjk, StarAlgHom.comp_apply]

variable {f} in
/-- The composites of injective ⋆-algebra homomorphisms are injective. -/
theorem natLERec_injective (hf : ∀ n, Function.Injective (f n)) (i j : ℕ) (h : i ≤ j) :
    Function.Injective (natLERec f i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [natLERec_self]; exact Function.injective_id
  | succ k hik ih => rw [natLERec_succ f hik]; exact (hf k).comp ih

end NatLERec

section ToNonUnitalStarAlgHom

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- Forgetting unitality sends the identity `StarAlgHom` to the identity `NonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_id :
    (StarAlgHom.id R A).toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id R A :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality preserves composition of `StarAlgHom`s. -/
@[simp]
theorem toNonUnitalStarAlgHom_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) :
    (f.comp g).toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom.comp g.toNonUnitalStarAlgHom :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality on `StarAlgHom` is injective. -/
theorem toNonUnitalStarAlgHom_injective :
    Function.Injective (toNonUnitalStarAlgHom (R := R) (A := A) (B := B)) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

end ToNonUnitalStarAlgHom

end StarAlgHom

namespace StarAlgEquiv

section NonUnitalArrowCongr

variable {R A₁ A₂ A₁' A₂' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']

/-- Conjugating a non-unital `⋆`-algebra homomorphism by `⋆`-algebra equivalences preserves
injectivity. -/
theorem arrowCongr'_injective_iff
    [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
    [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₙₐ[R] A₂) :
    Function.Injective (e₁.arrowCongr' e₂ f) ↔ Function.Injective f := by
  refine ⟨fun h x y hxy ↦ ?_, fun h ↦ e₂.injective.comp (h.comp e₁.symm.injective)⟩
  have h' := congrArg e₁.symm (h (a₁ := e₁ x) (a₂ := e₁ y) (by simp [hxy]))
  simpa using h'

/-- Conjugating non-unital `⋆`-algebra homomorphisms by `⋆`-algebra equivalences preserves unitary
conjugacy in the target. -/
theorem exists_unitary_conj_arrowCongr'_iff
    [Semiring A₂] [DistribMulAction R A₂] [StarMul A₂]
    [Semiring A₂'] [DistribMulAction R A₂'] [StarMul A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (φ ψ : A₁ →⋆ₙₐ[R] A₂) :
    (∃ u : unitary A₂', ∀ x, (u : A₂') * e₁.arrowCongr' e₂ φ x * star (u : A₂') =
        e₁.arrowCongr' e₂ ψ x) ↔
      ∃ u : unitary A₂, ∀ x, (u : A₂) * φ x * star (u : A₂) = ψ x := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨⟨e₂.symm u, Unitary.map_mem e₂.symm u.prop⟩, fun x ↦ ?_⟩,
    fun ⟨u, hu⟩ ↦ ⟨⟨e₂ u, Unitary.map_mem e₂ u.prop⟩, fun x ↦ ?_⟩⟩
  · simpa only [arrowCongr'_apply, NonUnitalStarAlgHom.comp_apply, toNonUnitalStarAlgHom_apply,
      map_mul, map_star, symm_apply_apply] using congrArg e₂.symm (hu (e₁ x))
  · simpa only [arrowCongr'_apply, NonUnitalStarAlgHom.comp_apply, toNonUnitalStarAlgHom_apply,
      map_mul, map_star] using congrArg e₂ (hu (e₁.symm x))

end NonUnitalArrowCongr

section UnitalArrowCongr

variable {R A₁ A₂ A₁' A₂' : Type*} [CommSemiring R]
  [Semiring A₁] [Algebra R A₁] [Star A₁]
  [Semiring A₁'] [Algebra R A₁'] [Star A₁']

/-- Forgetting unitality intertwines `StarAlgEquiv.arrowCongr` with `StarAlgEquiv.arrowCongr'`. -/
theorem toNonUnitalStarAlgHom_arrowCongr
    [Semiring A₂] [Algebra R A₂] [Star A₂]
    [Semiring A₂'] [Algebra R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₐ[R] A₂) :
    (e₁.arrowCongr e₂ f).toNonUnitalStarAlgHom = e₁.arrowCongr' e₂ f.toNonUnitalStarAlgHom :=
  rfl

/-- Conjugating a unital `⋆`-algebra homomorphism by `⋆`-algebra equivalences preserves
injectivity. -/
theorem arrowCongr_injective_iff
    [Semiring A₂] [Algebra R A₂] [Star A₂]
    [Semiring A₂'] [Algebra R A₂'] [Star A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (f : A₁ →⋆ₐ[R] A₂) :
    Function.Injective (e₁.arrowCongr e₂ f) ↔ Function.Injective f :=
  arrowCongr'_injective_iff e₁ e₂ f.toNonUnitalStarAlgHom

/-- Conjugating unital `⋆`-algebra homomorphisms by `⋆`-algebra equivalences preserves unitary
conjugacy in the target. -/
theorem exists_unitary_conj_arrowCongr_iff
    [Semiring A₂] [Algebra R A₂] [StarMul A₂]
    [Semiring A₂'] [Algebra R A₂'] [StarMul A₂']
    (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (φ ψ : A₁ →⋆ₐ[R] A₂) :
    (∃ u : unitary A₂', ∀ x, (u : A₂') * e₁.arrowCongr e₂ φ x * star (u : A₂') =
        e₁.arrowCongr e₂ ψ x) ↔
      ∃ u : unitary A₂, ∀ x, (u : A₂) * φ x * star (u : A₂) = ψ x :=
  exists_unitary_conj_arrowCongr'_iff e₁ e₂ φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom

end UnitalArrowCongr

end StarAlgEquiv
