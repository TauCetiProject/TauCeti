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
(`Ideal.exists_mul_mem_span_singleton`), and the natural map `B ⊗[A] I → J` from the base
change of an invertible ideal `I` onto an invertible ideal `J = I B` is bijective
(`Ideal.tensorToIdeal_bijective`).
-/

public section

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

end Submodule

namespace Ideal

open TensorProduct

/-- An invertible ideal is principal near each prime: for `J` invertible and `m` prime there are
`e ∈ J` and `s ∉ m` such that `s x` is a multiple of `e` for every `x ∈ J`. -/
theorem exists_mul_mem_span_singleton {B : Type*} [CommSemiring B] (J : Ideal B)
    [Module.Invertible B J] (m : Ideal B) [m.IsPrime] :
    ∃ e ∈ J, ∃ s ∉ m, ∀ x ∈ J, ∃ c, s * x = c * e := by
  classical
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv B J).symm 1).exists_finset
  have h1 : (1 : B) = ∑ i ∈ S, i.1 i.2 := by
    simpa [Module.Invertible.linearEquiv] using (LinearEquiv.symm_apply_eq _).mp hS
  obtain ⟨i, -, hi⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
    by_contra! h
    exact ‹m.IsPrime›.ne_top ((Ideal.eq_top_iff_one m).mpr (h1 ▸ m.sum_mem h))
  refine ⟨i.2, i.2.property, i.1 i.2, hi, fun x hx ↦ ⟨i.1 ⟨x, hx⟩, ?_⟩⟩
  have h2 : x • i.2 = (i.2 : B) • (⟨x, hx⟩ : J) := Subtype.ext (by simp [mul_comm])
  have h3 := i.1.map_smul x i.2
  rw [h2, map_smul, smul_eq_mul, smul_eq_mul] at h3
  rw [mul_comm, ← h3, mul_comm]

variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]

/-- For ideals `I` of `A` and `J` of an `A`-algebra `B` with `I B ⊆ J`, the `B`-linear map
`B ⊗[A] I → J`, `b ⊗ x ↦ b x`. -/
noncomputable def tensorToIdeal (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J) :
    B ⊗[A] I →ₗ[B] J :=
  LinearMap.liftBaseChange B
    { toFun x := ⟨algebraMap A B x, h (Ideal.mem_map_of_mem _ x.property)⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' a x := Subtype.ext (by simp [Algebra.smul_def]) }

@[simp]
theorem tensorToIdeal_tmul {I : Ideal A} {J : Ideal B} (h : I.map (algebraMap A B) ≤ J) (b : B)
    (x : I) : (tensorToIdeal I J h (b ⊗ₜ x) : B) = b * algebraMap A B x := by
  simp [tensorToIdeal]

/-- If an invertible ideal `J` of an `A`-algebra `B` is the extension `I B` of an invertible
ideal `I` of `A`, the natural map `B ⊗[A] I → J` is bijective. -/
theorem tensorToIdeal_bijective {I : Ideal A} {J : Ideal B} [Module.Invertible A I]
    [Module.Invertible B J]
    (h : I.map (algebraMap A B) = J) : Function.Bijective (tensorToIdeal I J h.le) := by
  refine Module.Invertible.bijective_of_surjective (LinearMap.range_eq_top.mp ?_)
  refine eq_top_iff.mpr fun y _ ↦ ?_
  have hle : I.map (algebraMap A B) ≤
      (LinearMap.range (tensorToIdeal I J h.le)).map J.subtype := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ⟨_, ⟨1 ⊗ₜ ⟨x, hx⟩, rfl⟩, ?_⟩
    simp
  have hy : (y : B) ∈ I.map (algebraMap A B) := by
    rw [h]
    exact y.property
  obtain ⟨z, hz, hzy⟩ := hle hy
  rwa [Subtype.ext hzy] at hz

end Ideal
