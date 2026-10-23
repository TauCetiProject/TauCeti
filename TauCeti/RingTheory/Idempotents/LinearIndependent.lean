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
  one linearly independent family.
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

/-- Cutting an element of the `(j, i)`-corner by two members of an orthogonal family keeps it
exactly when those members are `e j` and `e i`, and kills it otherwise. -/
theorem OrthogonalIdempotents.mul_mul_eq_ite {A ι : Type*} [Semiring A] {e : ι → A}
    (he : OrthogonalIdempotents e) {α : ι → ι → Type*} (f : ∀ i j, α i j → A)
    (hl : ∀ i j (a : α i j), e j * f i j a = f i j a)
    (hr : ∀ i j (a : α i j), f i j a * e i = f i j a)
    {i j i' j' : ι} (a : α i j) [Decidable (j' = j ∧ i' = i)] :
    e j' * f i j a * e i' = if j' = j ∧ i' = i then f i j a else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hl, hr]
  · rcases not_and_or.mp h with hj | hi
    · rw [← hl i j a]
      simp only [← mul_assoc, he.ortho hj, zero_mul]
    · rw [← hr i j a]
      simp only [mul_assoc, he.ortho (Ne.symm hi), mul_zero]

/-- If each family in the `(j, i)`-corner is linearly independent, their union over all pairs of
orthogonal idempotents is linearly independent. -/
theorem OrthogonalIdempotents.linearIndependent_sigma {k A ι : Type*} [Ring k] [Ring A]
    [Module k A] [SMulCommClass k A A] [IsScalarTower k A A] {e : ι → A}
    (he : OrthogonalIdempotents e) {α : ι → ι → Type*} (f : ∀ i j, α i j → A)
    (hl : ∀ i j (a : α i j), e j * f i j a = f i j a)
    (hr : ∀ i j (a : α i j), f i j a * e i = f i j a)
    (hind : ∀ i j, LinearIndependent k (f i j)) :
    LinearIndependent k fun a : (Σ i j : ι, α i j) => f a.1 a.2.1 a.2.2 := by
  classical
  rw [linearIndependent_iff']
  rintro s g hg ⟨i₀, j₀, a₀⟩ ha₀
  let sigmaMk : α i₀ j₀ → Σ i j : ι, α i j := fun a => ⟨i₀, j₀, a⟩
  have hsigmaMk : Function.Injective sigmaMk := fun a b h => by simpa [sigmaMk] using h
  have hcut : ∑ a ∈ s.preimage sigmaMk hsigmaMk.injOn, g (sigmaMk a) • f i₀ j₀ a = 0 := by
    have h := congrArg (fun y => e j₀ * y * e i₀) hg
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_zero,
      zero_mul] at h
    rw [Finset.sum_preimage' sigmaMk s hsigmaMk.injOn
      (fun x => g x • f x.1 x.2.1 x.2.2), Finset.sum_filter]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans h
    obtain ⟨i, j, a⟩ := x
    rw [he.mul_mul_eq_ite f hl hr a]
    by_cases hij : j₀ = j ∧ i₀ = i
    · obtain ⟨rfl, rfl⟩ := hij
      simp [sigmaMk]
    · have hx : (⟨i, j, a⟩ : Σ i j : ι, α i j) ∉ Set.range sigmaMk := by
        rintro ⟨b, hb⟩
        exact hij (by cases hb; simp)
      simp [hij, hx]
  exact linearIndependent_iff'.mp (hind i₀ j₀) _ _ hcut a₀ (by simpa [sigmaMk] using ha₀)
