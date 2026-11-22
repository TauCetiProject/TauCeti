/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Ideal.Maps

/-! # Subsemiring membership and finite patching

For a subsemiring containing the kernel of a ring homomorphism, membership can be
tested in its image, and pulling back that image recovers the original subsemiring.
Finite certificates for one also test membership from denominator-cleared products, in either
multiplication order. No membership assumption is needed on the denominators themselves.
-/

public section

namespace Subsemiring

variable {A B : Type*} [Ring A] [Ring B]

/-- A subsemiring containing the kernel contains every lift of each image point. -/
theorem mem_map_iff_mem_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) {x : A} : f x ∈ P.map f ↔ x ∈ P := by
  rw [mem_map]
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have hk : x - y ∈ P := hker (RingHom.mem_ker.mpr (by rw [map_sub, hxy, sub_self]))
  simpa using P.add_mem hy hk

/-- Pulling back the image recovers a subsemiring containing the kernel. -/
@[simp] theorem comap_map_eq_of_ker_subset {f : A →+* B} {P : Subsemiring A}
    (hker : (RingHom.ker f : Set A) ⊆ P) : (P.map f).comap f = P := by
  ext x
  exact mem_map_iff_mem_of_ker_subset hker

end Subsemiring


namespace SubsemiringClass

variable {R S ι : Type*} [Semiring R] [SetLike S R] [SubsemiringClass S R]

/-- A certificate `∑ aᵢ uᵢ = 1`, with `uᵢ` and `f aᵢ` in `H`, implies `f ∈ H`.
The individual `aᵢ` need not belong to `H`. -/
theorem mem_of_sum_mul_eq_one (H : S) (s : Finset ι) (a u : ι → R) {f : R}
    (h1 : ∑ i ∈ s, a i * u i = 1) (hu : ∀ i ∈ s, u i ∈ H)
    (hf : ∀ i ∈ s, f * a i ∈ H) : f ∈ H := by
  rw [← mul_one f, ← h1, Finset.mul_sum]
  exact sum_mem fun i hi ↦ by
    rw [← mul_assoc]
    exact mul_mem (hf i hi) (hu i hi)

/-- A certificate `∑ uᵢ aᵢ = 1`, with `uᵢ` and `aᵢ f` in `H`, implies `f ∈ H`.
The individual `aᵢ` need not belong to `H`. -/
theorem mem_of_sum_mul_eq_one_left (H : S) (s : Finset ι) (u a : ι → R) {f : R}
    (h1 : ∑ i ∈ s, u i * a i = 1) (hu : ∀ i ∈ s, u i ∈ H)
    (hf : ∀ i ∈ s, a i * f ∈ H) : f ∈ H := by
  have hm (x : R) : x ∈ Subsemiring.ofClass H ↔ x ∈ H := by
    rw [← SetLike.mem_coe, Subsemiring.coe_ofClass, SetLike.mem_coe]
  have h := mem_of_sum_mul_eq_one (Subsemiring.ofClass H).op s
    (fun i ↦ MulOpposite.op (a i)) (fun i ↦ MulOpposite.op (u i))
    (f := MulOpposite.op f)
    (by simpa only [← MulOpposite.op_mul, ← Finset.op_sum, MulOpposite.op_one] using
      congrArg MulOpposite.op h1)
    (by simpa only [Subsemiring.mem_op, MulOpposite.unop_op, hm] using hu)
    (by simpa only [Subsemiring.mem_op, MulOpposite.unop_mul, MulOpposite.unop_op,
      hm] using hf)
  simpa only [Subsemiring.mem_op, MulOpposite.unop_op, hm] using h

end SubsemiringClass
