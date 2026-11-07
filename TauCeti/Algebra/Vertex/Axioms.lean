/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative

/-!
# The axioms of a vertex algebra

A vertex algebra structure on an `R`-module `V` (`TauCeti.FormalVertexAxioms R V`) consists of

* a linear **state–field correspondence** `Y : V → VertexOperator R V`, written
  `Y(a, z) = ∑ₙ a₍ₙ₎ z^{-n-1}`, whose modes `a₍ₙ₎ = Y(a, z)[[n]]` are
  `TauCeti.FormalVertexAxioms.formalMode`;
* a **vacuum vector** `|0⟩` and a **translation operator** `T`,

subject to the following axioms, all read coefficientwise:

* **vacuum:** `T|0⟩ = 0` and `Y(|0⟩, z) = id`;
* **creation:** `Y(a, z)|0⟩ = e^{zT} a`, that is, `a₍ₙ₎|0⟩ = 0` for `n ≥ 0` and
  `k! a₍₋ₖ₋₁₎|0⟩ = Tᵏ a`;
* **state derivative:** `Y(Ta, z) = ∂_z Y(a, z)`;
* **translation covariance:** `[T, a₍ₙ₎] = -n a₍ₙ₋₁₎`, that is, `[T, Y(a, z)] = ∂_z Y(a, z)`;
* **locality:** for all `a` and `b` there is `N` with `(z - w)ᴺ [Y(a, z), Y(b, w)] = 0`
  (`VertexOperator.IsLocalOfOrder`).

Lower truncation, `a₍ₙ₎ b = 0` for `n ≫ 0`, is built into the carrier: the value `Y(a, z) b` is a
Laurent series (`VertexOperator.exists_forall_ncoeff_apply_eq_zero`). The creation axiom is stated
with factorials on the left, so that it makes sense over every commutative ring; over a
`ℚ`-algebra it says exactly that `Y(a, z)|0⟩ = ∑ₖ (Tᵏ a / k!) zᵏ`.

We derive the first consequences of the axioms.

* `a₍₋₁₎|0⟩ = a` and `a₍₋₂₎|0⟩ = Ta`; in particular `Y` is injective.
* `(Ta)₍ₙ₎ = -n a₍ₙ₋₁₎`, and `T` acts as a derivation of every product:
  `T(a₍ₙ₎ b) = (Ta)₍ₙ₎ b + a₍ₙ₎ (T b)`.
* **Goddard's uniqueness theorem** (`TauCeti.FormalVertexAxioms.eq_Y_of_isLocalOfOrder`): a field
  which is local with every `Y(b, z)` and agrees with `Y(a, z)` on the vacuum is `Y(a, z)`.
* The state–field correspondence determines the whole structure
  (`TauCeti.FormalVertexAxioms.ext`).

## Main definitions

* `TauCeti.FormalVertexAxioms`: a vertex algebra structure on a module.
* `TauCeti.FormalVertexAxioms.formalMode`: the modes `a₍ₙ₎` of the field `Y(a, z)`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §1.3 for the definition and §4.4 for
  Goddard's uniqueness theorem.
* B. Bakalov, V. Kac, *Field algebras*, Definition 2.1, whose (2.14) is the covariance axiom
  and (2.17) the state-derivative identity.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.3 for the
  definition and §3.1 for Goddard's uniqueness theorem.
-/

public section

noncomputable section

open scoped Nat VertexOperator

namespace TauCeti

/-- A **vertex algebra** structure on an `R`-module `V`: a linear state–field correspondence
`Y(a, z) = ∑ₙ a₍ₙ₎ z^{-n-1}` with values in Laurent-series valued fields, a vacuum vector `|0⟩`
and a translation operator `T`, subject to the vacuum, creation, state-derivative, translation
covariance and locality axioms, all read on the coefficients `a₍ₙ₎ = Y(a, z)[[n]]`. Lower
truncation is built into `VertexOperator R V`. -/
structure FormalVertexAxioms (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- The state–field correspondence `a ↦ Y(a, z)`. -/
  Y : V →ₗ[R] VertexOperator R V
  /-- The vacuum vector `|0⟩`. -/
  vacuum : V
  /-- The translation operator `T`. -/
  translation : Module.End R V
  /-- The translation operator kills the vacuum: `T|0⟩ = 0`. -/
  translation_vacuum : translation vacuum = 0
  /-- The field of the vacuum is the identity: `Y(|0⟩, z) = id`. -/
  ncoeff_Y_vacuum (n : ℤ) : (Y vacuum)[[n]] = if n = -1 then 1 else 0
  /-- **Creation**, regular part: `Y(a, z)|0⟩` has no negative powers of `z`. -/
  ncoeff_Y_apply_vacuum_of_nonneg (a : V) {n : ℤ} (hn : 0 ≤ n) : ((Y a)[[n]]) vacuum = 0
  /-- **Creation**, Taylor coefficients: `k! a₍₋ₖ₋₁₎|0⟩ = Tᵏ a`, so that
  `Y(a, z)|0⟩ = e^{zT} a`. -/
  factorial_smul_ncoeff_Y_apply_vacuum (a : V) (k : ℕ) :
    k ! • ((Y a)[[-k - 1]]) vacuum = (translation ^ k) a
  /-- **State derivative**: `Y(Ta, z) = ∂_z Y(a, z)`. -/
  Y_translation (a : V) : Y (translation a) = VertexOperator.derivative (Y a)
  /-- **Translation covariance**: `[T, a₍ₙ₎] = -n a₍ₙ₋₁₎`. -/
  lie_translation_ncoeff_Y (a : V) (n : ℤ) : ⁅translation, (Y a)[[n]]⁆ = (-n) • (Y a)[[n - 1]]
  /-- **Locality**: any two fields `Y(a, z)` and `Y(b, w)` are mutually local. -/
  exists_isLocalOfOrder (a b : V) : ∃ N : ℕ, (Y a).IsLocalOfOrder (Y b) N

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A : FormalVertexAxioms R V)

/-- The **modes** of a vertex algebra: `A.formalMode a n = a₍ₙ₎` is the coefficient of
`z^{-n-1}` in `Y(a, z)`. -/
def formalMode : V →ₗ[R] ℤ → Module.End R V :=
  VertexOperator.ncoeff ∘ₗ A.Y

/-- The normalized coefficients of `Y(a, z)` are the modes `a₍ₙ₎`. -/
@[simp]
theorem ncoeff_Y (a : V) (n : ℤ) : (A.Y a)[[n]] = A.formalMode a n := (rfl)

/-- The modes of the vacuum: `|0⟩₍ₙ₎` is the identity for `n = -1` and zero otherwise. -/
theorem formalMode_vacuum (n : ℤ) : A.formalMode A.vacuum n = if n = -1 then 1 else 0 :=
  A.ncoeff_Y_vacuum n

/-- The mode `|0⟩₍₋₁₎` is the identity. -/
@[simp]
theorem formalMode_vacuum_neg_one : A.formalMode A.vacuum (-1) = 1 := by
  simp [formalMode_vacuum]

/-- The modes `|0⟩₍ₙ₎` with `n ≠ -1` vanish. -/
theorem formalMode_vacuum_of_ne {n : ℤ} (hn : n ≠ -1) : A.formalMode A.vacuum n = 0 := by
  simp [formalMode_vacuum, hn]

/-- **Creation**: the nonnegative modes kill the vacuum. -/
theorem formalMode_apply_vacuum_of_nonneg (a : V) {n : ℤ} (hn : 0 ≤ n) :
    A.formalMode a n A.vacuum = 0 :=
  A.ncoeff_Y_apply_vacuum_of_nonneg a hn

/-- **Creation**: `k! a₍₋ₖ₋₁₎|0⟩ = Tᵏ a`. -/
theorem factorial_smul_formalMode_apply_vacuum (a : V) (k : ℕ) :
    k ! • A.formalMode a (-k - 1) A.vacuum = (A.translation ^ k) a :=
  A.factorial_smul_ncoeff_Y_apply_vacuum a k

/-- **Creation**: `a₍₋₁₎|0⟩ = a`, the value of `Y(a, z)|0⟩` at `z = 0`. -/
@[simp]
theorem formalMode_neg_one_apply_vacuum (a : V) : A.formalMode a (-1) A.vacuum = a := by
  simpa using A.factorial_smul_formalMode_apply_vacuum a 0

/-- The translation operator is read off from the creation axiom: `Ta = a₍₋₂₎|0⟩`. -/
@[simp]
theorem formalMode_neg_two_apply_vacuum (a : V) :
    A.formalMode a (-2) A.vacuum = A.translation a := by
  simpa using A.factorial_smul_formalMode_apply_vacuum a 1

/-- The state–field correspondence is injective, since `a = a₍₋₁₎|0⟩`. -/
theorem Y_injective : Function.Injective A.Y := fun a b h ↦ by
  rw [← A.formalMode_neg_one_apply_vacuum a, ← A.formalMode_neg_one_apply_vacuum b,
    formalMode, LinearMap.comp_apply, h, ← LinearMap.comp_apply]

/-- **State derivative**, on modes: `(Ta)₍ₙ₎ = -n a₍ₙ₋₁₎`. -/
@[simp]
theorem formalMode_translation (a : V) (n : ℤ) :
    A.formalMode (A.translation a) n = (-n) • A.formalMode a (n - 1) := by
  rw [← ncoeff_Y, A.Y_translation, VertexOperator.ncoeff_derivative, ncoeff_Y]

/-- **Translation covariance**: `[T, a₍ₙ₎] = -n a₍ₙ₋₁₎`. -/
theorem lie_translation_formalMode (a : V) (n : ℤ) :
    ⁅A.translation, A.formalMode a n⁆ = (-n) • A.formalMode a (n - 1) :=
  A.lie_translation_ncoeff_Y a n

/-- The translation operator is a derivation of every product:
`T(a₍ₙ₎ b) = (Ta)₍ₙ₎ b + a₍ₙ₎ (Tb)`. -/
theorem translation_formalMode_apply (a b : V) (n : ℤ) :
    A.translation (A.formalMode a n b) =
      A.formalMode (A.translation a) n b + A.formalMode a n (A.translation b) := by
  have h := LinearMap.congr_fun (A.lie_translation_formalMode a n) b
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp] at h
  rw [formalMode_translation, ← h]
  abel

/-- **Goddard's uniqueness theorem.** A field `F(z)` which is local with every field `Y(b, w)`
and agrees with `Y(a, z)` on the vacuum, `F(z)|0⟩ = Y(a, z)|0⟩`, is equal to `Y(a, z)`. -/
theorem eq_Y_of_isLocalOfOrder {F : VertexOperator R V} {a : V}
    (hloc : ∀ b : V, ∃ N : ℕ, F.IsLocalOfOrder (A.Y b) N)
    (hvac : ∀ n : ℤ, (F[[n]]) A.vacuum = A.formalMode a n A.vacuum) : F = A.Y a := by
  refine VertexOperator.ext_ncoeff fun m ↦ LinearMap.ext fun b ↦ ?_
  obtain ⟨N₁, h₁⟩ := hloc b
  obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a b
  -- The difference `F - Y(a, z)` kills the vacuum and is local with `Y(b, w)`.
  have hloc' := (h₁.mono (le_max_left N₁ N₂)).sub_left (h₂.mono (le_max_right N₁ N₂))
  have h := hloc'.ncoeff_apply_ncoeff_neg_one_eq_zero
    (fun k ↦ by simp [hvac]) (fun j hj ↦ A.formalMode_apply_vacuum_of_nonneg b hj) m
  simpa [sub_eq_zero] using h

/-- A vertex algebra structure is determined by its state–field correspondence: the vacuum is
the unique vector whose field is the identity, and `Ta = a₍₋₂₎|0⟩`. -/
@[ext]
theorem ext {A A' : FormalVertexAxioms R V} (h : A.Y = A'.Y) : A = A' := by
  have hvac : A.vacuum = A'.vacuum := by
    have h' := A.formalMode_neg_one_apply_vacuum A'.vacuum
    rwa [formalMode, LinearMap.comp_apply, h, ← LinearMap.comp_apply, ← formalMode,
      formalMode_vacuum_neg_one, one_apply_eq_self] at h'
  have hT : A.translation = A'.translation := LinearMap.ext fun a ↦ by
    rw [← formalMode_neg_two_apply_vacuum, ← formalMode_neg_two_apply_vacuum, formalMode,
      formalMode, LinearMap.comp_apply, LinearMap.comp_apply, h, hvac]
  cases A
  cases A'
  simp only at h hvac hT
  subst h hvac hT
  rfl

end FormalVertexAxioms

end TauCeti
