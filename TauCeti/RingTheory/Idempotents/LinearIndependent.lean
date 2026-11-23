/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal nonzero idempotents are linearly independent

Let `k` be a ring whose multiplication cancels (`IsCancelMulZero`, so in particular any integral
domain), let `A` be a ring that is a torsion-free `k`-module -- no nonzero scalar annihilates a
nonzero element -- on which `k` acts compatibly with multiplication (`IsScalarTower k A A`, as for
any `k`-algebra), and let `e : ι → A` be a family of pairwise orthogonal idempotents, none of them
zero.
Then the `eᵢ` are linearly independent over `k`: multiplying a vanishing combination
`∑ᵢ gᵢ • eᵢ = 0` by `e_j` kills every term but the `j`-th, which orthogonality and idempotence
leave as `g_j • e_j = 0`.

Mathlib has orthogonal families of idempotents (`OrthogonalIdempotents`, in
`Mathlib/RingTheory/Idempotents.lean`) and the ring-theoretic decompositions they generate, but
records nothing about their linear independence, which is what makes a complete orthogonal family
of the right size a *basis*.

## Main results

* `OrthogonalIdempotents.linearIndependent`: **a family of pairwise orthogonal nonzero
  idempotents is linearly independent.**
* `OrthogonalIdempotents.linearIndependent_sigma`: cornerwise linearly independent families form
  one linearly independent family (over any semiring).
-/

public section

/-- **A family of pairwise orthogonal nonzero idempotents of a ring `A` is linearly independent**
over a ring `k` with cancellative multiplication, provided `A` is a torsion-free `k`-module on which
`k` acts compatibly with multiplication (for example, a torsion-free `k`-algebra). -/
theorem OrthogonalIdempotents.linearIndependent {k A ι : Type*} [Ring k] [IsCancelMulZero k]
    [Ring A] [Module k A] [IsScalarTower k A A] [Module.IsTorsionFree k A] {e : ι → A}
    (he : OrthogonalIdempotents e) (he₀ : ∀ i, e i ≠ 0) : LinearIndependent k e := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  simpa [Finset.sum_mul, smul_mul_assoc, he.mul_eq, he₀ j, hj] using congrArg (· * e j) hg

/-- Cutting an element `x` of the `(j, i)`-corner of an orthogonal family (`e j * x = x` and
`x * e i = x`) by two members of the family leaves `x` when those members are `e j` and `e i`,
and gives `0` otherwise. -/
theorem OrthogonalIdempotents.mul_mul_eq_ite {A ι : Type*} [Semiring A] {e : ι → A}
    (he : OrthogonalIdempotents e) {i j i' j' : ι} {x : A} (hl : e j * x = x) (hr : x * e i = x)
    [Decidable (j' = j ∧ i' = i)] :
    e j' * x * e i' = if j' = j ∧ i' = i then x else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hl, hr]
  · rcases not_and_or.mp h with hj | hi
    · rw [← hl]
      simp only [← mul_assoc, he.ortho hj, zero_mul]
    · rw [← hr]
      simp only [mul_assoc, he.ortho (Ne.symm hi), mul_zero]

/-- Let `e` be an orthogonal family of idempotents in a semiring `A`, and for each pair `i, j` let
`f i j` be a family in the `(j, i)`-corner (`e j * x = x` and `x * e i = x`). If every `f i j` is
linearly independent over a semiring `k`, then so is the combined family indexed by
`Σ i j, α i j`. -/
theorem OrthogonalIdempotents.linearIndependent_sigma {k A ι : Type*} [Semiring k] [Semiring A]
    [Module k A] [SMulCommClass k A A] [IsScalarTower k A A] {e : ι → A}
    (he : OrthogonalIdempotents e) {α : ι → ι → Type*} (f : ∀ i j, α i j → A)
    (hl : ∀ i j (a : α i j), e j * f i j a = f i j a)
    (hr : ∀ i j (a : α i j), f i j a * e i = f i j a)
    (hind : ∀ i j, LinearIndependent k (f i j)) :
    LinearIndependent k fun a : (Σ i j : ι, α i j) => f a.1 a.2.1 a.2.2 := by
  classical
  rw [linearIndependent_iff'ₛ]
  rintro s g₁ g₂ hg ⟨i₀, j₀, a₀⟩ ha₀
  have hmk : Function.Injective fun a : α i₀ j₀ => (⟨i₀, j₀, a⟩ : Σ i j : ι, α i j) :=
    sigma_mk_injective.comp sigma_mk_injective
  -- Cutting a combination by `e j₀` and `e i₀` keeps exactly its `(i₀, j₀)`-corner terms.
  have hcut (g : (Σ i j : ι, α i j) → k) : e j₀ * (∑ x ∈ s, g x • f x.1 x.2.1 x.2.2) * e i₀ =
      ∑ a ∈ s.preimage _ hmk.injOn, g ⟨i₀, j₀, a⟩ • f i₀ j₀ a := by
    rw [Finset.sum_preimage' _ s hmk.injOn (fun x => g x • f x.1 x.2.1 x.2.2), Finset.sum_filter,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ⟨i, j, a⟩ _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, he.mul_mul_eq_ite (hl i j a) (hr i j a)]
    by_cases hij : j₀ = j ∧ i₀ = i
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · have : ∀ b : α i₀ j₀, (⟨i₀, j₀, b⟩ : Σ i j : ι, α i j) ≠ ⟨i, j, a⟩ := by
        rintro b ⟨⟩
        simp at hij
      simp [hij, this]
  exact linearIndependent_iff'ₛ.mp (hind i₀ j₀) _ _ _ ((hcut g₁).symm.trans (by rw [hg, hcut])) a₀
    (by simpa using ha₀)
