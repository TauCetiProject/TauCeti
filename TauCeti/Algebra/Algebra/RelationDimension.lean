/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# A dimension count for relations among algebra generators

A family of vectors spanning the relations among algebra generators bounds the dimensions of
quotients by compatible subspaces, provided the relevant quotients are finite-dimensional. This is
the dimension-counting step of the Golod–Shafarevich inequality, used by
`TauCeti.card_sq_lt_four_mul_card_of_relations_le_span`.

## Main results

* `TauCeti.card_mul_finrank_quotient_add_le`: a bound on quotient dimensions from generators
  and vectors spanning their relations.

## References

* P. Roquette, *On class field towers*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic
  Number Theory*, Chapter IX, §4.
-/

public section

namespace TauCeti

open Module Submodule

variable {A : Type*} [Ring A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The dimension count behind the Golod–Shafarevich inequality. Let `W`, `U`, `T`, and `S` be
subspaces of `A` such that right multiplication by the entries of the vectors `y`
maps `W` into `U`, right multiplication by the generators `x` maps `U` into `T`, every `∑ aᵢ xᵢ`
lies in `S`, and every element of `T` is a `U`-combination of the `x`. If every relation among the
`x` is an `A`-combination of the `y`, then the induced linear maps `(A ⧸ W)^κ → (A ⧸ U)^ι → A ⧸ T`
have the kernel of the right-hand map contained in the range of the left-hand map, and the image
of the right-hand map is killed by `A ⧸ T → A ⧸ S` (where `T ≤ S` follows from the assumptions).
So if `A ⧸ W` and `A ⧸ T` are finite-dimensional, then
`#ι · dim (A ⧸ U) + dim (A ⧸ S) ≤ dim (A ⧸ T) + #κ · dim (A ⧸ W)`. -/
theorem card_mul_finrank_quotient_add_le {k : Type*} [Field k] [Algebra k A]
    (x : ι → A) (y : κ → ι → A)
    (hker : ∀ a : ι → A, ∑ i, a i * x i = 0 → a ∈ span A (Set.range y))
    {W U T S : Submodule k A} [FiniteDimensional k (A ⧸ W)] [FiniteDimensional k (A ⧸ T)]
    (hWU : ∀ w ∈ W, ∀ j i, w * y j i ∈ U)
    (hUT : ∀ u ∈ U, ∀ i, u * x i ∈ T) (hxS : ∀ a : ι → A, ∑ i, a i * x i ∈ S)
    (hT : ∀ t ∈ T, ∃ a : ι → A, (∀ i, a i ∈ U) ∧ ∑ i, a i * x i = t) :
    Fintype.card ι * finrank k (A ⧸ U) + finrank k (A ⧸ S) ≤
      finrank k (A ⧸ T) + Fintype.card κ * finrank k (A ⧸ W) := by
  classical
  have hTS : T ≤ S := fun t ht ↦ by
    obtain ⟨a, -, rfl⟩ := hT t ht
    exact hxS a
  -- The maps induced on the quotients by the generators and by the relations.
  let d₁ : (ι → A ⧸ U) →ₗ[k] A ⧸ T := piQuotientLift (fun _ ↦ U) T
    (fun i ↦ LinearMap.mulRight k (x i)) fun i u hu ↦ mem_comap.2 (hUT u hu i)
  let d₂ : (κ → A ⧸ W) →ₗ[k] ι → A ⧸ U := LinearMap.pi fun i ↦ piQuotientLift (fun _ ↦ W) U
    (fun j ↦ LinearMap.mulRight k (y j i)) fun j w hw ↦ mem_comap.2 (hWU w hw j i)
  have hd₁ (a : ι → A) : d₁ (U.mkQ ∘ a) = T.mkQ (∑ i, a i * x i) := by
    simp only [d₁, Function.comp_def, mkQ_apply, piQuotientLift_mk]
    simp
  have hd₂ (b : κ → A) : d₂ (W.mkQ ∘ b) = fun i ↦ U.mkQ (∑ j, b j * y j i) := by
    ext i
    simp only [d₂, LinearMap.pi_apply, Function.comp_def, mkQ_apply, piQuotientLift_mk]
    simp
  -- The image of `d₁` lies in `S ⧸ T`, the kernel of `A ⧸ T → A ⧸ S`.
  have hrange : LinearMap.range d₁ ≤ LinearMap.ker (factor hTS) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := U.mkQ_surjective.comp_left a
    rw [LinearMap.mem_ker, hd₁, factor_mk, mkQ_apply, Quotient.mk_eq_zero]
    exact hxS a
  -- A relation modulo `T` comes from the vectors `y`.
  have hexact : LinearMap.ker d₁ ≤ LinearMap.range d₂ := by
    intro a ha
    obtain ⟨a, rfl⟩ := U.mkQ_surjective.comp_left a
    rw [LinearMap.mem_ker, hd₁, mkQ_apply, Quotient.mk_eq_zero] at ha
    obtain ⟨a', ha'U, ha'⟩ := hT _ ha
    obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun A).1
      (hker (a - a') (by simp [sub_mul, Finset.sum_sub_distrib, ha']))
    refine ⟨W.mkQ ∘ b, ?_⟩
    rw [hd₂]
    ext i
    have hbi : ∑ j, b j * y j i = a i - a' i := by
      simpa using congrFun hb i
    simp [hbi, Quotient.mk_sub, (Quotient.mk_eq_zero U).2 (ha'U i)]
  -- The source of `d₁` is finite-dimensional: its kernel and its range are.
  have : FiniteDimensional k (LinearMap.ker d₁) := finiteDimensional_of_le hexact
  have : FiniteDimensional k ((ι → A ⧸ U) ⧸ LinearMap.ker d₁) :=
    .equiv d₁.quotKerEquivRange.symm
  have : FiniteDimensional k (ι → A ⧸ U) := .of_submodule_quotient (LinearMap.ker d₁)
  have hpi : finrank k (ι → A ⧸ U) = Fintype.card ι * finrank k (A ⧸ U) := by
    cases isEmpty_or_nonempty ι with
    | inl _ => simp [finrank_zero_of_subsingleton]
    | inr h =>
      obtain ⟨i⟩ := h
      have : FiniteDimensional k (A ⧸ U) :=
        .of_surjective (LinearMap.proj (R := k) (φ := fun _ ↦ A ⧸ U) i)
          (LinearMap.proj_surjective i)
      simp [Module.finrank_pi_fintype]
  -- Counting dimensions.
  have h₁ := LinearMap.finrank_range_add_finrank_ker d₁
  have h₂ := LinearMap.finrank_range_add_finrank_ker (factor hTS)
  rw [LinearMap.range_eq_top.2 (factor_surjective hTS), finrank_top] at h₂
  have h₃ := Submodule.finrank_mono hrange
  have h₄ := (Submodule.finrank_mono hexact).trans (LinearMap.finrank_range_le d₂)
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h₄
  omega

end TauCeti
