/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Idempotents whose corner is a line

Let `k` be a field, `A` a commutative `k`-algebra and `e` a nonzero idempotent of `A` with
`e x ∈ k e` for every `x ∈ A`, so that the corner `e A` is the line `k e`. The scalar `φ(x)` with
`e x = φ(x) e` is then unique, and `x ↦ φ(x)` is a `k`-algebra homomorphism `A → k` with
`φ(e) = 1`. The condition `e x ∈ k e` only needs to be checked on a spanning set.

## Main results

* `IsIdempotentElem.forall_exists_mul_eq_smul_of_span_eq_top`: the condition `e x ∈ k e`
  propagates from a spanning set to all of `A`.
* `IsIdempotentElem.exists_algHom_of_forall_exists_mul_eq_smul`: a nonzero idempotent whose
  corner is a line has a character `φ : A →ₐ[k] k` with `φ(e) = 1` and `e x = φ(x) e`.
-/

public section

namespace IsIdempotentElem

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {e : A}

/-- If `e s ∈ k e` for every `s` in a spanning set of `A`, then `e x ∈ k e` for every `x ∈ A`. -/
theorem forall_exists_mul_eq_smul_of_span_eq_top {s : Set A}
    (hs : Submodule.span k s = ⊤) (h : ∀ x ∈ s, ∃ c : k, e * x = c • e) (x : A) :
    ∃ c : k, e * x = c • e := by
  have hx : x ∈ Submodule.span k s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by rw [mul_zero, zero_smul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [mul_add, ha, hb, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [mul_smul_comm, ha, smul_smul]⟩

/-- **The character of an idempotent whose corner is a line.** If `e` is a nonzero idempotent of
a commutative `k`-algebra `A` and `e x ∈ k e` for every `x`, then `x ↦ φ(x)`, the scalar with
`e x = φ(x) e`, is a `k`-algebra homomorphism `A → k` with `φ(e) = 1`. -/
theorem exists_algHom_of_forall_exists_mul_eq_smul (he : IsIdempotentElem e) (hne : e ≠ 0)
    (h : ∀ x, ∃ c : k, e * x = c • e) :
    ∃ φ : A →ₐ[k] k, φ e = 1 ∧ ∀ x, e * x = φ x • e := by
  choose φ hφ using h
  have uniq {x : A} {c : k} (hc : e * x = c • e) : φ x = c :=
    smul_left_injective k hne ((hφ x).symm.trans hc)
  refine ⟨{ toFun := φ
            map_one' := uniq (by rw [mul_one, one_smul])
            map_mul' := fun x y ↦ uniq (by
              rw [← mul_assoc, hφ x, smul_mul_assoc, hφ y, smul_smul])
            map_zero' := uniq (by rw [mul_zero, zero_smul])
            map_add' := fun x y ↦ uniq (by rw [mul_add, hφ x, hφ y, add_smul])
            commutes' := fun r ↦ uniq (by
              rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, Algebra.algebraMap_self,
                RingHom.id_apply]) },
    uniq (by rw [he.eq, one_smul]), hφ⟩

end IsIdempotentElem
