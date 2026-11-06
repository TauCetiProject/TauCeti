/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Formal vertex algebras

A formal vertex algebra on an `R`-module `V` (`TauCeti.FormalVertexAxioms`) consists of a
linear state–field map `a ↦ Y(a,z) = ∑ₙ a₍ₙ₎ z^{-n-1}` into Mathlib's fields
`VertexOperator R V`, a vacuum vector `|0⟩` and a translation operator `T`, subject to:

* the vacuum axioms `T|0⟩ = 0` and `Y(|0⟩,z) = id`;
* creation: `Y(a,z)|0⟩` has no negative powers of `z`, and its constant term is `a`;
* the state-derivative identity `Y(Ta,z) = ∂_z Y(a,z)`;
* translation covariance `[T, Y(a,z)] = ∂_z Y(a,z)`, that is `[T, a₍ₙ₎] = -n a₍ₙ₋₁₎`;
* locality: `(z - w)ᴺ [Y(a,z), Y(b,w)] = 0` for some `N`, read coefficientwise as
  `VertexOperator.IsLocalOfOrder`.

Lower truncation, `a₍ₙ₎ b = 0` for `n` large, is automatic: a field takes values in Laurent
series (`VertexOperator.exists_forall_ncoeff_apply_eq_zero`).

All axioms are stated without division, over an arbitrary commutative ring. Over a
`ℚ`-algebra they are the usual axioms of a vertex algebra; over other rings the standard notion
uses divided powers of `T` instead, so the definition is meant for `ℚ`-algebras.

## Main definitions

* `TauCeti.FormalVertexAxioms`: a formal vertex algebra structure on `V`.

## Main results

* `TauCeti.FormalVertexAxioms.ext`: a formal vertex algebra is determined by its state–field map.
* `TauCeti.FormalVertexAxioms.translation_apply`: `T a = a₍₋₂₎|0⟩`.
* `TauCeti.FormalVertexAxioms.translation_ncoeff_apply`:
  `T (a₍ₙ₎ b) = (T a)₍ₙ₎ b + a₍ₙ₎ (T b)`.
* `TauCeti.FormalVertexAxioms.factorial_smul_ncoeff_field_apply_vacuum`:
  `k! • a₍₋ₖ₋₁₎|0⟩ = Tᵏ a`, and `TauCeti.FormalVertexAxioms.ncoeff_field_apply_vacuum_neg` its
  form `a₍₋ₖ₋₁₎|0⟩ = Tᵏ a / k!` over `ℚ`, the creation identity `Y(a,z)|0⟩ = e^{zT} a`.
* `TauCeti.FormalVertexAxioms.eq_of_ncoeff_apply_vacuum_eq`: Goddard's uniqueness theorem, a field
  local to every `Y(a,z)` is determined by its values on the vacuum.
* `TauCeti.FormalVertexAxioms.eq_field_of_ncoeff_apply_vacuum_eq`: such a field `B` with
  `B(z)|0⟩ = Y(b,z)|0⟩` is `Y(b,z)`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §1.3 (Definition of a vertex algebra) and
  §4.4 (Theorem 4.4, the uniqueness theorem).
* P. Goddard, *Meromorphic conformal field theory*, in *Infinite-dimensional Lie algebras and
  groups*, Adv. Ser. Math. Phys. 7 (1989), for the uniqueness theorem.
* B. Bakalov, V. Kac, *Field algebras*, Int. Math. Res. Not. 2003, Definition 2.1.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- A formal vertex algebra on the `R`-module `V`: a linear state–field map `a ↦ Y(a,z)` into
fields on `V`, a vacuum vector `|0⟩` and a translation operator `T`, satisfying the vacuum,
creation, state-derivative, translation covariance and locality axioms. The modes are the
normalized coefficients `a₍ₙ₎ = (field a)[[n]]`, the coefficients of `z^{-n-1}`. -/
structure FormalVertexAxioms where
  /-- The state–field map `a ↦ Y(a,z)`. -/
  field : V →ₗ[R] VertexOperator R V
  /-- The vacuum vector `|0⟩`. -/
  vacuum : V
  /-- The translation operator `T`. -/
  translation : Module.End R V
  /-- The translation operator kills the vacuum. -/
  translation_vacuum : translation vacuum = 0
  /-- The field of the vacuum is the identity: `|0⟩₍ₙ₎ = δ_{n,-1}`. -/
  ncoeff_field_vacuum : ∀ n : ℤ, (field vacuum)[[n]] = if n = -1 then 1 else 0
  /-- Creation: `Y(a,z)|0⟩` has no negative powers of `z`. -/
  ncoeff_field_apply_vacuum_of_nonneg : ∀ (a : V) (n : ℤ), 0 ≤ n → ((field a)[[n]]) vacuum = 0
  /-- Creation: the constant term of `Y(a,z)|0⟩` is `a`. -/
  ncoeff_neg_one_field_apply_vacuum : ∀ a : V, ((field a)[[-1]]) vacuum = a
  /-- The state-derivative identity `Y(Ta,z) = ∂_z Y(a,z)`. -/
  field_translation : ∀ a : V, field (translation a) = derivative (field a)
  /-- Translation covariance `[T, Y(a,z)] = ∂_z Y(a,z)`, in modes. -/
  lie_translation_ncoeff : ∀ (a : V) (n : ℤ),
    ⁅translation, (field a)[[n]]⁆ = (derivative (field a))[[n]]
  /-- Locality: any two fields are mutually local of some order. -/
  exists_isLocalOfOrder : ∀ a b : V, ∃ N : ℕ, (field a).IsLocalOfOrder (field b) N

namespace FormalVertexAxioms

variable {R V}
variable (A : FormalVertexAxioms R V)

attribute [simp] translation_vacuum ncoeff_field_apply_vacuum_of_nonneg
  ncoeff_neg_one_field_apply_vacuum

/-! ### The vacuum -/

/-- The mode `|0⟩₍₋₁₎` of the vacuum is the identity. -/
@[simp]
theorem ncoeff_neg_one_field_vacuum : (A.field A.vacuum)[[-1]] = 1 := by
  simp [A.ncoeff_field_vacuum]

/-- The modes `|0⟩₍ₙ₎` of the vacuum vanish for `n ≠ -1`. -/
@[simp]
theorem ncoeff_field_vacuum_of_ne {n : ℤ} (hn : n ≠ -1) : (A.field A.vacuum)[[n]] = 0 := by
  simp [A.ncoeff_field_vacuum, hn]

/-- The state–field map is injective: `a` is recovered as `a₍₋₁₎|0⟩`. -/
theorem field_injective : Function.Injective A.field := by
  intro a b h
  rw [← A.ncoeff_neg_one_field_apply_vacuum a, h, A.ncoeff_neg_one_field_apply_vacuum]

/-! ### Translation -/

/-- The modes of `Y(Ta,z)` are `(Ta)₍ₙ₎ = -n a₍ₙ₋₁₎`. -/
@[simp]
theorem ncoeff_field_translation (a : V) (n : ℤ) :
    (A.field (A.translation a))[[n]] = (-n) • (A.field a)[[n - 1]] := by
  rw [A.field_translation, ncoeff_derivative]

/-- Translation is a derivation of each mode: `T (a₍ₙ₎ b) = (T a)₍ₙ₎ b + a₍ₙ₎ (T b)`. -/
theorem translation_ncoeff_apply (a b : V) (n : ℤ) :
    A.translation (((A.field a)[[n]]) b) =
      ((A.field (A.translation a))[[n]]) b + ((A.field a)[[n]]) (A.translation b) := by
  have h := LinearMap.congr_fun (A.lie_translation_ncoeff a n) b
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    ← A.field_translation, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

/-- The creation recursion `T (a₍ₙ₎|0⟩) = -n a₍ₙ₋₁₎|0⟩`. -/
theorem translation_ncoeff_apply_vacuum (a : V) (n : ℤ) :
    A.translation (((A.field a)[[n]]) A.vacuum) = (-n) • ((A.field a)[[n - 1]]) A.vacuum := by
  simp [A.translation_ncoeff_apply]

/-- The translation operator is determined by the fields and the vacuum: `T a = a₍₋₂₎|0⟩`. -/
theorem translation_apply (a : V) : A.translation a = ((A.field a)[[-2]]) A.vacuum := by
  simpa using A.translation_ncoeff_apply_vacuum a (-1)

/-- The creation identity without division: `k! • a₍₋ₖ₋₁₎|0⟩ = Tᵏ a`. -/
theorem factorial_smul_ncoeff_field_apply_vacuum (a : V) (k : ℕ) :
    k.factorial • ((A.field a)[[-k - 1]]) A.vacuum = (A.translation ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := A.translation_ncoeff_apply_vacuum a (-k - 1)
    rw [show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
      show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- The creation identity `Y(a,z)|0⟩ = e^{zT} a`, in modes: `a₍₋ₖ₋₁₎|0⟩ = Tᵏ a / k!`. -/
theorem ncoeff_field_apply_vacuum_neg [Module ℚ V] (a : V) (k : ℕ) :
    ((A.field a)[[-k - 1]]) A.vacuum = (k.factorial : ℚ)⁻¹ • (A.translation ^ k) a := by
  rw [← A.factorial_smul_ncoeff_field_apply_vacuum, ← Nat.cast_smul_eq_nsmul ℚ,
    inv_smul_smul₀ (by exact_mod_cast k.factorial_ne_zero)]

/-! ### Extensionality -/

/-- A formal vertex algebra is determined by its state–field map: the vacuum is the unique state
whose field is the identity, and `T a = a₍₋₂₎|0⟩`. -/
@[ext]
theorem ext {A B : FormalVertexAxioms R V} (h : A.field = B.field) : A = B := by
  have hvac : A.vacuum = B.vacuum := by
    conv_rhs => rw [← A.ncoeff_neg_one_field_apply_vacuum B.vacuum, h,
      B.ncoeff_neg_one_field_vacuum, one_apply_eq_self]
  have hT : A.translation = B.translation := by
    ext a
    rw [A.translation_apply, B.translation_apply, h, hvac]
  cases A
  cases B
  simp_all

/-! ### Goddard's uniqueness theorem -/

/-- If `B` is local of order `N` with `Y(a,z)`, the modes of `B` on `a` are determined by the
action of `B` on the vacuum. -/
private theorem ncoeff_add_apply_eq_sum {B : VertexOperator R V} {a : V} {N : ℕ}
    (h : B.IsLocalOfOrder (A.field a) N) (m : ℤ) :
    (B[[m + N]]) a = ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      ((A.field a)[[-1 + ij.2]]) ((B[[m + ij.1]]) A.vacuum) := by
  -- Apply locality at `(m, -1)` to the vacuum. Of the terms `B₍ₘ₊ᵢ₎ a₍₋₁₊ⱼ₎|0⟩`, only
  -- `j = 0` survives the creation axiom, and there `a₍₋₁₎|0⟩ = a`.
  have h₀ := LinearMap.congr_fun (isLocalOfOrder_iff.mp h m (-1)) A.vacuum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, LinearMap.zero_apply, smul_sub, sum_sub_distrib] at h₀
  rw [sum_eq_single (N, 0) (fun ij hij hne ↦ ?_) (by simp), sub_eq_zero] at h₀
  · simpa using h₀
  · have hj : ij.2 ≠ 0 := fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
    rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega), map_zero, smul_zero, smul_zero]

/-- **Goddard's uniqueness theorem.** Two fields that are local to every field `Y(a,z)` of a
formal vertex algebra and agree on the vacuum are equal. -/
theorem eq_of_ncoeff_apply_vacuum_eq {B C : VertexOperator R V}
    (hB : ∀ a, ∃ N, B.IsLocalOfOrder (A.field a) N)
    (hC : ∀ a, ∃ N, C.IsLocalOfOrder (A.field a) N)
    (h : ∀ n, (B[[n]]) A.vacuum = (C[[n]]) A.vacuum) : B = C := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun a ↦ ?_
  obtain ⟨N₁, h₁⟩ := hB a
  obtain ⟨N₂, h₂⟩ := hC a
  have e : n = n - (max N₁ N₂ : ℕ) + (max N₁ N₂ : ℕ) := by ring
  rw [e, A.ncoeff_add_apply_eq_sum (h₁.mono (le_max_left N₁ N₂)),
    A.ncoeff_add_apply_eq_sum (h₂.mono (le_max_right N₁ N₂))]
  simp only [h]

/-- **Goddard's uniqueness theorem**, field form: a field `B` local to every `Y(a,z)` with
`B(z)|0⟩ = Y(b,z)|0⟩` is `Y(b,z)`. -/
theorem eq_field_of_ncoeff_apply_vacuum_eq {B : VertexOperator R V} {b : V}
    (hB : ∀ a, ∃ N, B.IsLocalOfOrder (A.field a) N)
    (h : ∀ n, (B[[n]]) A.vacuum = ((A.field b)[[n]]) A.vacuum) : B = A.field b :=
  A.eq_of_ncoeff_apply_vacuum_eq hB (A.exists_isLocalOfOrder b) h

end FormalVertexAxioms

end TauCeti
