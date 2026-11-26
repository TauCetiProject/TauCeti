/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Freeness and principality of invertible submodules

A submodule whose underlying module is invertible is free exactly when it is principal.
This identifies trivial invertible-module classes with principal submodules, over any
commutative semiring. An invertible ideal is principal near each prime
(`Ideal.exists_mul_mem_span_singleton`). The isomorphism `I ⊗ J ≃ I * J` of invertible submodules
of an algebra is multiplication (`Submodule.coe_tensorEquivMul_tmul`).
-/

public section

open scoped TensorProduct

namespace Submodule

variable {R P : Type*} [CommSemiring R] [AddCommMonoid P] [Module R P]

/-- An invertible submodule is free exactly when it is principal. -/
theorem free_iff_isPrincipal (I : Submodule R P) [Module.Invertible R I] :
    Module.Free R I ↔ I.IsPrincipal := by
  rw [Module.Invertible.free_iff_linearEquiv]
  constructor
  · rintro ⟨f⟩
    exact ⟨_, Submodule.eq_span_singleton_of_surjective f.symm.surjective⟩
  · rintro ⟨x, hx⟩
    -- Multiplication by the generator maps `R` onto `I`, hence isomorphically.
    let f : R →ₗ[R] I :=
      (LinearMap.toSpanSingleton R P x).codRestrict I fun a ↦ by
        rw [hx]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hx ▸ hy : y ∈ Submodule.span R {x})
      exact ⟨a, rfl⟩
    exact ⟨(LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hf)).symm⟩

/-- The isomorphism `I ⊗ J ≃ I * J` of invertible submodules of an algebra is multiplication. -/
theorem coe_tensorEquivMul_tmul {A : Type*} [Semiring A] [Algebra R A] [FaithfulSMul R A]
    (I J : (Submodule R A)ˣ) (x : (I : Submodule R A)) (y : (J : Submodule R A)) :
    (tensorEquivMul I J (x ⊗ₜ y) : A) = x * y := by
  rw [tensorEquivMul]
  exact (congrArg Subtype.val (LinearEquiv.ofBijective_apply _ _)).trans (val_mulMap'_tmul x y)

end Submodule

namespace Ideal

/-- An invertible ideal is principal near each prime: for `J` invertible and `m` prime there are
`e ∈ J` and `s ∉ m` such that `s x ∈ (e)` for every `x ∈ J`. -/
theorem exists_mul_mem_span_singleton {B : Type*} [CommSemiring B] (J : Ideal B)
    [Module.Invertible B J] (m : Ideal B) [m.IsPrime] :
    ∃ e ∈ J, ∃ s ∉ m, ∀ x ∈ J, s * x ∈ Ideal.span {e} := by
  classical
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := B) (M := J)).2 1
  obtain ⟨S, rfl⟩ := t.exists_finset
  have h1 : (1 : B) = ∑ i ∈ S, i.1 i.2 := by
    rw [← ht]
    simp [map_sum]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
    by_contra! h
    exact ‹m.IsPrime›.ne_top ((Ideal.eq_top_iff_one m).mpr (h1 ▸ m.sum_mem h))
  refine ⟨i.2, i.2.property, i.1 i.2, hi, fun x hx ↦
    Ideal.mem_span_singleton'.mpr ⟨i.1 ⟨x, hx⟩, ?_⟩⟩
  have h2 : x • i.2 = (i.2 : B) • (⟨x, hx⟩ : J) := Subtype.ext (by simp [mul_comm])
  have h3 := i.1.map_smul x i.2
  rw [h2, map_smul, smul_eq_mul, smul_eq_mul] at h3
  rw [mul_comm (i.1 i.2), ← h3, mul_comm]

end Ideal
