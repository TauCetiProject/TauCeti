/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.TFAE
public import TauCeti.RingTheory.TraceFunctional.Expectation

/-!
# Commuting squares

Let `τ` be a tracial linear functional on an algebra `A` over a field, and consider a square of
subalgebras
```
A₀ ⊆ A₁
 ∩     ∩
B₀ ⊆ A
```
in which `A₀`, `A₁` and `B₀` are finite-dimensional with nondegenerate trace pairing
`(x, y) ↦ τ (x * y)`. Write `E_C = C.traceExpectation τ` for the `τ`-preserving conditional
expectation onto such a subalgebra `C`. The square *commutes* when `E_{A₁} ∘ E_{B₀} = E_{A₀}`.

Commuting squares of finite-dimensional algebras are the input of Ocneanu's compactness theorem:
iterating basic constructions on a commuting square yields a subfactor of the hyperfinite II₁
factor whose relative commutants are computed by the square. This file proves the standard
equivalent forms of the commuting condition and their invariance under trace-preserving
isomorphisms.

Only the algebraic structure is used: no positivity, normalization or Markov condition. For a
faithful positive trace on a finite-dimensional C⋆-algebra the nondegeneracy hypotheses hold for
every star-subalgebra, and each `E_C` is then the orthogonal projection of `L²(A, τ)` onto `C`.

## Main definitions

* `Subalgebra.IsCommutingSquare A₀ A₁ B₀ τ`: the square commutes, `E_{A₁} ∘ E_{B₀} = E_{A₀}`.

## Main results

* `Subalgebra.isCommutingSquare_tfae`: for `A₀ ≤ A₁` and `A₀ ≤ B₀`, the following are equivalent:
  the square commutes; `E_{B₀} ∘ E_{A₁} = E_{A₀}`; `E_{B₀}` agrees with `E_{A₀}` on `A₁`; and
  `E_{A₁}` commutes with `E_{B₀}` while `A₁ ⊓ B₀ = A₀`.
* `Subalgebra.isCommutingSquare_comm`: the commuting condition is symmetric in `A₁` and `B₀`.
* `Subalgebra.isCommutingSquare_map_iff`: commuting squares are carried to commuting squares by
  trace-preserving algebra isomorphisms.

## References

* V. F. R. Jones and V. S. Sunder, *Introduction to subfactors*, LMS Lecture Note Series 234,
  Cambridge University Press, 1997, §5.1.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §4.2.
-/

public section

namespace Subalgebra

variable {K A A' : Type*} [Field K] [Ring A] [Algebra K A] [Ring A'] [Algebra K A']

/-- The square of subalgebras `A₀ ⊆ A₁`, `A₀ ⊆ B₀` of `A` *commutes* for the trace `τ` when
expecting onto `B₀` and then onto `A₁` is the expectation onto `A₀`. -/
def IsCommutingSquare (A₀ A₁ B₀ : Subalgebra K A) (τ : A →ₗ[K] K) : Prop :=
  A₁.traceExpectation τ ∘ₗ B₀.traceExpectation τ = A₀.traceExpectation τ

variable {A₀ A₁ B₀ : Subalgebra K A} {τ : A →ₗ[K] K}

/-- Unfolding the commuting condition as an identity of linear maps. -/
theorem isCommutingSquare_def : IsCommutingSquare A₀ A₁ B₀ τ ↔
    A₁.traceExpectation τ ∘ₗ B₀.traceExpectation τ = A₀.traceExpectation τ :=
  Iff.rfl

/-- The commuting condition, tested on each element. -/
theorem isCommutingSquare_iff :
    IsCommutingSquare A₀ A₁ B₀ τ ↔ ∀ a, A₁.traceExpectation τ (B₀.traceExpectation τ a) =
      A₀.traceExpectation τ a :=
  LinearMap.ext_iff

/-- In a commuting square, expecting onto `B₀` and then onto `A₁` is expecting onto `A₀`. -/
theorem IsCommutingSquare.traceExpectation_traceExpectation (h : IsCommutingSquare A₀ A₁ B₀ τ)
    (a : A) :
    A₁.traceExpectation τ (B₀.traceExpectation τ a) = A₀.traceExpectation τ a :=
  isCommutingSquare_iff.mp h a

variable [FiniteDimensional K A₀] [FiniteDimensional K A₁] [FiniteDimensional K B₀]
  (h₀ : ∀ x ∈ A₀, (∀ y ∈ A₀, τ (x * y) = 0) → x = 0)
  (h₁ : ∀ x ∈ A₁, (∀ y ∈ A₁, τ (x * y) = 0) → x = 0)
  (hB : ∀ x ∈ B₀, (∀ y ∈ B₀, τ (x * y) = 0) → x = 0)

omit [FiniteDimensional K A₁] in
include h₀ hB in
/-- A square with `A₀ ≤ B₀` commutes exactly when the expectations onto `A₁` and onto `A₀`
agree on `B₀`. -/
theorem isCommutingSquare_iff_forall_mem (hAB : A₀ ≤ B₀) :
    IsCommutingSquare A₀ A₁ B₀ τ ↔
      ∀ b ∈ B₀, A₁.traceExpectation τ b = A₀.traceExpectation τ b := by
  refine ⟨fun h b hb ↦ ?_, fun h ↦ isCommutingSquare_iff.mpr fun a ↦ ?_⟩
  · simpa [traceExpectation_of_mem hB hb] using h.traceExpectation_traceExpectation b
  · rw [h _ (traceExpectation_mem a), traceExpectation_traceExpectation_of_le h₀ hB hAB]

include h₀ h₁ hB in
/-- For a tracial functional, a commuting square stays commuting when `A₁` and `B₀` are
exchanged. -/
theorem IsCommutingSquare.symm (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hAB : A₀ ≤ B₀)
    (h : IsCommutingSquare A₀ A₁ B₀ τ) : IsCommutingSquare A₀ B₀ A₁ τ := by
  refine isCommutingSquare_iff.mpr fun a ↦ (traceExpectation_eq_iff hB
    (hAB (traceExpectation_mem a))).mpr fun y hy ↦ ?_
  rw [← apply_mul_traceExpectation h₀ hτ, ← h.traceExpectation_traceExpectation,
    traceExpectation_of_mem hB hy, apply_mul_traceExpectation h₁ hτ]

include h₀ h₁ hB in
/-- For a tracial functional, the commuting condition is symmetric in `A₁` and `B₀`. -/
theorem isCommutingSquare_comm (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hA : A₀ ≤ A₁)
    (hAB : A₀ ≤ B₀) : IsCommutingSquare A₀ A₁ B₀ τ ↔ IsCommutingSquare A₀ B₀ A₁ τ :=
  ⟨IsCommutingSquare.symm h₀ h₁ hB hτ hAB, IsCommutingSquare.symm h₀ hB h₁ hτ hA⟩

include h₀ h₁ hB in
/-- A square commutes exactly when the expectations onto its two sides commute and the two sides
intersect in the corner `A₀`. -/
theorem isCommutingSquare_iff_commute_and_inf_eq (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (hA : A₀ ≤ A₁) (hAB : A₀ ≤ B₀) :
    IsCommutingSquare A₀ A₁ B₀ τ ↔
      Commute (A₁.traceExpectation τ) (B₀.traceExpectation τ) ∧ A₁ ⊓ B₀ = A₀ := by
  refine ⟨fun h ↦ ⟨?_, le_antisymm (fun x hx ↦ ?_) (le_inf hA hAB)⟩, fun ⟨hc, hinf⟩ ↦ ?_⟩
  · rw [commute_iff_eq, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      isCommutingSquare_def.mp h, isCommutingSquare_def.mp (h.symm h₀ h₁ hB hτ hAB)]
  · obtain ⟨hx₁, hx₂⟩ := Algebra.mem_inf.mp hx
    rw [← traceExpectation_of_mem h₁ hx₁, ← traceExpectation_of_mem hB hx₂,
      h.traceExpectation_traceExpectation]
    exact traceExpectation_mem x
  · refine isCommutingSquare_iff.mpr fun a ↦ ((traceExpectation_eq_iff h₀ ?_).mpr ?_).symm
    · have hcomm := LinearMap.congr_fun hc.eq a
      simp only [mul_apply_eq_comp] at hcomm
      exact hinf.le (Algebra.mem_inf.mpr ⟨traceExpectation_mem _, hcomm ▸ traceExpectation_mem _⟩)
    · intro y hy
      obtain ⟨hy₁, hy₂⟩ := Algebra.mem_inf.mp (hinf.ge hy)
      rw [apply_traceExpectation_mul h₁ _ hy₁, apply_traceExpectation_mul hB _ hy₂]

include h₀ h₁ hB in
/-- **Commuting squares.** For a tracial functional and a square `A₀ ≤ A₁`, `A₀ ≤ B₀` of
finite-dimensional subalgebras with nondegenerate trace pairings, the following are equivalent:
the square commutes, `E_{A₁} ∘ E_{B₀} = E_{A₀}`; the reversed composite is `E_{A₀}`,
`E_{B₀} ∘ E_{A₁} = E_{A₀}`; `E_{B₀}` agrees with `E_{A₀}` on `A₁`; and `E_{A₁}` commutes with
`E_{B₀}` while `A₁ ⊓ B₀ = A₀`. -/
theorem isCommutingSquare_tfae (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hA : A₀ ≤ A₁)
    (hAB : A₀ ≤ B₀) :
    List.TFAE [IsCommutingSquare A₀ A₁ B₀ τ, IsCommutingSquare A₀ B₀ A₁ τ,
      ∀ a ∈ A₁, B₀.traceExpectation τ a = A₀.traceExpectation τ a,
      Commute (A₁.traceExpectation τ) (B₀.traceExpectation τ) ∧ A₁ ⊓ B₀ = A₀] := by
  tfae_have 1 ↔ 2 := isCommutingSquare_comm h₀ h₁ hB hτ hA hAB
  tfae_have 2 ↔ 3 := isCommutingSquare_iff_forall_mem h₀ h₁ hA
  tfae_have 1 ↔ 4 := isCommutingSquare_iff_commute_and_inf_eq h₀ h₁ hB hτ hA hAB
  tfae_finish

include h₀ h₁ hB in
/-- A trace-preserving algebra isomorphism carries a square to a commuting square exactly when the
original square commutes. -/
theorem isCommutingSquare_map_iff (e : A ≃ₐ[K] A') {τ' : A' →ₗ[K] K} (he : ∀ a, τ' (e a) = τ a) :
    IsCommutingSquare (A₀.map (e : A →ₐ[K] A')) (A₁.map (e : A →ₐ[K] A'))
      (B₀.map (e : A →ₐ[K] A')) τ' ↔ IsCommutingSquare A₀ A₁ B₀ τ := by
  simp only [isCommutingSquare_iff]
  refine ⟨fun h a ↦ e.injective ?_, fun h a' ↦ ?_⟩
  · rw [← traceExpectation_map h₁ e he, ← traceExpectation_map hB e he, h,
      traceExpectation_map h₀ e he]
  · obtain ⟨a, rfl⟩ := e.surjective a'
    rw [traceExpectation_map hB e he, traceExpectation_map h₁ e he, h,
      traceExpectation_map h₀ e he]

end Subalgebra
