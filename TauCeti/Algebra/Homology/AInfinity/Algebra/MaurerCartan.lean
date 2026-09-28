/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG

/-!
# Maurer--Cartan elements of `A∞` algebras

For an `A∞` algebra with operations `mₙ` of degree `2 - n`, a degree-one element `α` is a
**Maurer--Cartan element** when

`∑_{n ≥ 1} (-1)^{n(n-1)/2} mₙ(α, …, α) = 0`.

Maurer--Cartan elements are the input for twisting an `A∞` structure and, in the strict case, for
twisted complexes.  On a bare graded module this sum has no meaning unless it is finite, so this
file works in the arity-nilpotent regime: `IsMaurerCartan` asks for an explicit bound beyond which
every `mₙ(α, …, α)` vanishes, and for the finite sum up to that bound to vanish.  The truncated sum
is `maurerCartanSum`, and it no longer changes once the bound is reached, so the equation can be
tested at any bound (`isMaurerCartan_iff`).  Complete filtered algebras, where the sum converges
without being finite, need a filtration and are not treated here.

The sign `(-1)^{n(n-1)/2}` is the Koszul sign of `s^{⊗n}` on `n` letters of degree one, for the
degree-`-1` suspension `s`.  Consequently, under the suspended Taylor map of the bar construction,
`(sα)^{⊗n}` goes to exactly the signed term of the unsuspended sum
(`taylor_of_tprod_const`), and the Maurer--Cartan equation is the sign-free equation
`b(∑ₙ (sα)^{⊗n}) = 0` in the letter component (`isMaurerCartan_iff_taylor`).

For a DG algebra, `m₁ = d`, `m₂` is the product and higher operations vanish, so the equation
reads `dα - α² = 0` (`IsNonUnitalDGAlgebra.isMaurerCartan_toAInfinityAlgebra_iff`).  Its negative
`δ = -α` satisfies the familiar twisting equation `dδ + δ² = 0`
(`IsNonUnitalDGAlgebra.isMaurerCartan_toAInfinityAlgebra_neg_iff`).

## Main definitions

* `TauCeti.AInfinityAlgebra.maurerCartanSum`: the truncated Maurer--Cartan sum.
* `TauCeti.AInfinityAlgebra.IsMaurerCartan`: a degree-one element satisfying the Maurer--Cartan
  equation, with an explicit arity bound making the sum finite.

## Main results

* `TauCeti.AInfinityAlgebra.maurerCartanSum_eq_of_le`: the truncated sum is constant beyond an
  arity bound.
* `TauCeti.AInfinityAlgebra.isMaurerCartan_iff`: the Maurer--Cartan equation may be tested at any
  arity bound.
* `TauCeti.AInfinityAlgebra.isMaurerCartan_iff_taylor`: the equivalent sign-free equation for the
  suspended Taylor map on the truncated sum of tensor powers of `α`.
* `TauCeti.AInfinityAlgebra.IsMaurerCartan.map`: strict morphisms preserve Maurer--Cartan elements.
* `TauCeti.IsNonUnitalDGAlgebra.isMaurerCartan_toAInfinityAlgebra_iff` and
  `TauCeti.IsNonUnitalDGAlgebra.isMaurerCartan_toAInfinityAlgebra_neg_iff`: in a DG algebra the
  equation is `dα = α²`, equivalently `dδ + δ² = 0` for `δ = -α`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.6, equation (7.1).
-/

public section

namespace TauCeti

universe uR uA uB

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- The truncated Maurer--Cartan sum `∑_{n < N} (-1)^{n(n-1)/2} mₙ(α, …, α)`.  The sign is
written with `n.choose 2 = n(n-1)/2`, and the arity-zero term vanishes because `m 0 = 0`. -/
def maurerCartanSum (α : A) (N : ℕ) : A :=
  ∑ n ∈ Finset.range N, negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α

theorem maurerCartanSum_def (α : A) (N : ℕ) :
    𝒜.maurerCartanSum α N =
      ∑ n ∈ Finset.range N, negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α := (rfl)

@[simp]
theorem maurerCartanSum_zero (α : A) : 𝒜.maurerCartanSum α 0 = 0 := by
  simp [maurerCartanSum_def]

@[simp]
theorem maurerCartanSum_succ (α : A) (N : ℕ) :
    𝒜.maurerCartanSum α (N + 1) =
      𝒜.maurerCartanSum α N + negOnePowCast R (N.choose 2) • 𝒜.m N fun _ ↦ α := by
  rw [maurerCartanSum_def, maurerCartanSum_def, Finset.sum_range_succ]

/-- Once every `mₙ(α, …, α)` with `N ≤ n` vanishes, the truncated sum stops changing. -/
theorem maurerCartanSum_eq_of_le {α : A} {N M : ℕ}
    (hN : ∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) (hNM : N ≤ M) :
    𝒜.maurerCartanSum α M = 𝒜.maurerCartanSum α N := by
  rw [maurerCartanSum_def, maurerCartanSum_def]
  exact Finset.eventually_constant_sum (fun n hn ↦ by rw [hN n hn, smul_zero]) hNM

/-- A **Maurer--Cartan element** of an `A∞` algebra, in the arity-nilpotent regime: an element `α`
of degree one such that `mₙ(α, …, α)` vanishes for all `n` beyond some bound `N`, and

`∑_{n < N} (-1)^{n(n-1)/2} mₙ(α, …, α) = 0`.

By `maurerCartanSum_eq_of_le`, the equation does not depend on the chosen bound; see
`isMaurerCartan_iff`. -/
structure IsMaurerCartan (α : A) : Prop where
  /-- A Maurer--Cartan element has degree one. -/
  mem_piece_one : α ∈ 𝒜.grading.piece 1
  /-- The operations vanish on `α` in all large arities, and the resulting finite sum vanishes. -/
  exists_bound : ∃ N, (∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) ∧ 𝒜.maurerCartanSum α N = 0

variable {𝒜}

/-- The Maurer--Cartan equation holds at every arity bound, not only the recorded one. -/
theorem IsMaurerCartan.maurerCartanSum_eq_zero {α : A} (h : 𝒜.IsMaurerCartan α) {N : ℕ}
    (hN : ∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) : 𝒜.maurerCartanSum α N = 0 := by
  obtain ⟨M, hM, hsum⟩ := h.exists_bound
  rw [← 𝒜.maurerCartanSum_eq_of_le hN (le_max_left N M),
    𝒜.maurerCartanSum_eq_of_le hM (le_max_right N M), hsum]

/-- Given an arity bound for `α`, the element `α` is Maurer--Cartan exactly when it has degree one
and the truncated sum at that bound vanishes. -/
theorem isMaurerCartan_iff {α : A} {N : ℕ} (hN : ∀ n, N ≤ n → 𝒜.m n (fun _ ↦ α) = 0) :
    𝒜.IsMaurerCartan α ↔ α ∈ 𝒜.grading.piece 1 ∧ 𝒜.maurerCartanSum α N = 0 :=
  ⟨fun h ↦ ⟨h.mem_piece_one, h.maurerCartanSum_eq_zero hN⟩,
    fun h ↦ ⟨h.1, N, hN, h.2⟩⟩

variable (𝒜) in
/-- Zero is a Maurer--Cartan element. -/
@[simp]
theorem isMaurerCartan_zero : 𝒜.IsMaurerCartan 0 := by
  have hm : ∀ n, 𝒜.m n (fun _ ↦ (0 : A)) = 0 := by
    intro n
    rcases n with _ | n
    · simp
    · exact (𝒜.m (n + 1)).map_zero
  exact ⟨zero_mem _, 0, fun n _ ↦ hm n, 𝒜.maurerCartanSum_zero 0⟩

/-! ### The suspended form of the equation -/

variable (𝒜) in
/-- On `n` copies of a degree-one element the suspended Taylor map is the unsuspended operation
with the Maurer--Cartan sign: the Koszul sign of `s^{⊗n}` on letters of degree one is
`(-1)^{n(n-1)/2}`. -/
theorem taylor_of_tprod_const {α : A} (hα : α ∈ 𝒜.grading.piece 1) (n : ℕ) (hn : 0 < n) :
    𝒜.taylor (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun _ ↦ α)) =
      negOnePowCast R (n.choose 2) • 𝒜.m n fun _ ↦ α := by
  have h := (AInfinity.isSuspension_def _ _ _).1 𝒜.taylor_isSuspension n hn (fun _ ↦ 1)
    (fun _ ↦ α) (fun _ _ ↦ hα)
  rw [AInfinity.evalNat_suspend, MultilinearMap.suspExp_const, mul_one,
    MultilinearMap.evalNat_def] at h
  exact h

variable (𝒜) in
/-- The suspended Taylor map sends the truncated sum `∑_{1 ≤ n ≤ N} (sα)^{⊗n}` of tensor powers of
a degree-one element to the truncated Maurer--Cartan sum.  By
`AInfinityAlgebra.letter_comp_barDifferential`, this is the letter component of the bar
differential of that sum. -/
theorem taylor_sum_of_tprod_const {α : A} (hα : α ∈ 𝒜.grading.piece 1) (N : ℕ) :
    𝒜.taylor (∑ n ∈ Finset.range N,
        ReducedTensorWords.of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R fun _ ↦ α)) =
      𝒜.maurerCartanSum α (N + 1) := by
  rw [map_sum, maurerCartanSum_def, Finset.sum_range_succ']
  simp [𝒜.taylor_of_tprod_const hα]

/-- Given an arity bound `N + 1` for `α`, the Maurer--Cartan equation is the sign-free suspended
equation: the Taylor map vanishes on `∑_{1 ≤ n ≤ N} (sα)^{⊗n}`. -/
theorem isMaurerCartan_iff_taylor {α : A} {N : ℕ}
    (hN : ∀ n, N + 1 ≤ n → 𝒜.m n (fun _ ↦ α) = 0) :
    𝒜.IsMaurerCartan α ↔ α ∈ 𝒜.grading.piece 1 ∧
      𝒜.taylor (∑ n ∈ Finset.range N,
        ReducedTensorWords.of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R fun _ ↦ α)) = 0 := by
  rw [isMaurerCartan_iff hN]
  exact and_congr_right fun hα ↦ by rw [𝒜.taylor_sum_of_tprod_const hα]

end AInfinityAlgebra

/-! ### Functoriality along strict morphisms -/

section Strict

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- A strict morphism commutes with the truncated Maurer--Cartan sums. -/
@[simp]
theorem AInfinityStrictHom.map_maurerCartanSum (f : AInfinityStrictHom 𝒜 ℬ) (α : A) (N : ℕ) :
    f (𝒜.maurerCartanSum α N) = ℬ.maurerCartanSum (f α) N := by
  simp [AInfinityAlgebra.maurerCartanSum_def, map_sum]

/-- A strict morphism sends Maurer--Cartan elements to Maurer--Cartan elements. -/
theorem AInfinityAlgebra.IsMaurerCartan.map {α : A} (h : 𝒜.IsMaurerCartan α)
    (f : AInfinityStrictHom 𝒜 ℬ) : ℬ.IsMaurerCartan (f α) := by
  obtain ⟨N, hN, hsum⟩ := h.exists_bound
  refine ⟨f.map_mem h.mem_piece_one, N, fun n hn ↦ ?_, ?_⟩
  · rw [← f.map_m, hN n hn, map_zero]
  · rw [← f.map_maurerCartanSum, hsum, map_zero]

end Strict

/-! ### Differential graded algebras -/

namespace IsNonUnitalDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A}

/-- The arity bound `3` makes the Maurer--Cartan sum of a DG algebra `dα - α²`. -/
theorem maurerCartanSum_toAInfinityAlgebra (h : IsNonUnitalDGAlgebra 𝒜 d) (α : A) {N : ℕ}
    (hN : 3 ≤ N) : h.toAInfinityAlgebra.maurerCartanSum α N = d α - α * α := by
  rw [h.toAInfinityAlgebra.maurerCartanSum_eq_of_le
    (fun n hn ↦ by rw [h.toAInfinityAlgebra_m_of_three_le hn, _root_.zero_apply]) hN]
  simp [sub_eq_add_neg]

/-- In a DG algebra, the Maurer--Cartan equation is `dα = α²` for `α` of degree one. -/
theorem isMaurerCartan_toAInfinityAlgebra_iff (h : IsNonUnitalDGAlgebra 𝒜 d) {α : A} :
    h.toAInfinityAlgebra.IsMaurerCartan α ↔ α ∈ 𝒜 1 ∧ d α = α * α := by
  rw [AInfinityAlgebra.isMaurerCartan_iff (N := 3)
      (fun n hn ↦ by rw [h.toAInfinityAlgebra_m_of_three_le hn, _root_.zero_apply]),
    h.maurerCartanSum_toAInfinityAlgebra α le_rfl, sub_eq_zero, toAInfinityAlgebra_grading,
    InternalGrading.ofDecomposition_piece]

/-- In a DG algebra, `-δ` is a Maurer--Cartan element exactly when `δ` has degree one and
satisfies the twisting equation `dδ + δ² = 0`. -/
theorem isMaurerCartan_toAInfinityAlgebra_neg_iff (h : IsNonUnitalDGAlgebra 𝒜 d) {δ : A} :
    h.toAInfinityAlgebra.IsMaurerCartan (-δ) ↔ δ ∈ 𝒜 1 ∧ d δ + δ * δ = 0 := by
  rw [h.isMaurerCartan_toAInfinityAlgebra_iff, neg_mem_iff, map_neg, neg_mul_neg,
    neg_eq_iff_add_eq_zero]

end IsNonUnitalDGAlgebra

end TauCeti
