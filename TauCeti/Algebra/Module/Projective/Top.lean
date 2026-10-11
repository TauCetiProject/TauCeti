/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.Algebra.Module.ProjectiveCover.Simple

/-!
# Tops of indecomposable projective modules

Let `P` be a projective module over a ring `R`, and let `I` be a nilpotent ideal.  Then `P` is
indecomposable exactly when `P / IP` is.

Over a semiprimary ring with Jacobson radical `J`, the **top** of `P` is `P / JP`.  A projective
module is indecomposable exactly when its top is simple.  For an indecomposable projective module
`P`, the submodule `JP` is maximal and is the kernel of every surjection onto a simple module, and
every such surjection is a projective cover.

## Main definitions

* `TauCeti.IsIndecomposableModule.quotientJacobsonEquivOfSurjective`: the equivalence between the
  top of an indecomposable projective module and any simple module it maps onto.

## Main results

* `TauCeti.isIndecomposableModule_quotient_smul_top_iff`: for a nilpotent ideal `I`, a projective
  module `P` is indecomposable exactly when `P / IP` is; the reflecting direction
  `TauCeti.IsIndecomposableModule.of_quotient_smul_top` holds for every module.
* `TauCeti.isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top`: over a
  semiprimary ring, a projective module is indecomposable exactly when its top is simple.
* `TauCeti.IsIndecomposableModule.isCoatom_jacobson_smul_top`: the radical of an
  indecomposable projective module is its unique maximal submodule, so it is the kernel of every
  surjection onto a simple module (`TauCeti.ker_eq_jacobson_smul_top_of_ne_zero`).
* `TauCeti.IsIndecomposableModule.isProjectiveCover_of_surjective`: such a surjection is a
  projective cover.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.4.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Sections 23--24.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u v w

section Projective

variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
  {I : Ideal R}

omit [Module.Projective R P] in
/-- **Indecomposability reflects from the top.**  If `I` is nilpotent and `P / IP` is
indecomposable, then so is `P`.  This holds for every module `P`, projective or not. -/
theorem IsIndecomposableModule.of_quotient_smul_top (hI : IsNilpotent I)
    (h : IsIndecomposableModule R (P ⧸ I • (⊤ : Submodule R P))) : IsIndecomposableModule R P := by
  let q := Ideal.endMapQ I P
  have hker : ∀ f ∈ RingHom.ker q, IsNilpotent f :=
    fun _ hf ↦ Ideal.isNilpotent_of_mem_ker_endMapQ I P hI hf
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem] at h ⊢
  obtain ⟨_, h⟩ := h
  refine ⟨(Submodule.mkQ_surjective (I • (⊤ : Submodule R P))).nontrivial, fun f hf ↦ ?_⟩
  rcases h (q f) (hf.map q) with hq0 | hq1
  · exact Or.inl <| hf.eq_zero_of_isNilpotent <| hker f (by simpa [RingHom.mem_ker] using hq0)
  · refine Or.inr (sub_eq_zero.mp ?_).symm
    exact hf.one_sub.eq_zero_of_isNilpotent <| hker _ <| by
      rw [RingHom.mem_ker, map_sub, map_one, hq1, sub_self]

/-- **Indecomposability of a projective module is read off its top.**  If `I` is nilpotent, a
projective module `P` is indecomposable exactly when `P / IP` is. -/
theorem isIndecomposableModule_quotient_smul_top_iff (hI : IsNilpotent I) :
    IsIndecomposableModule R (P ⧸ I • (⊤ : Submodule R P)) ↔ IsIndecomposableModule R P := by
  refine ⟨IsIndecomposableModule.of_quotient_smul_top hI, fun hP ↦ ?_⟩
  let q := Ideal.endMapQ I P
  have hker : ∀ f ∈ RingHom.ker q, IsNilpotent f :=
    fun _ hf ↦ Ideal.isNilpotent_of_mem_ker_endMapQ I P hI hf
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem] at hP ⊢
  obtain ⟨_, h⟩ := hP
  refine ⟨Submodule.Quotient.nontrivial_iff.mpr
    (isSuperfluous_smul_top_of_isNilpotent hI).ne_top, fun g hg ↦ ?_⟩
  obtain ⟨f, hf, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent q hker g
    (RingHom.mem_range.mpr (Ideal.endMapQ_surjective I P g)) hg
  exact (h f hf).imp (fun hf0 ↦ by simp [hf0]) (fun hf1 ↦ by simp [hf1])

/-- **A projective module is indecomposable exactly when its top is simple.**  Here `R` is
semiprimary with Jacobson radical `J`, and the top of `P` is `P / JP`. -/
theorem isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top
    [IsSemiprimaryRing R] :
    IsIndecomposableModule R P ↔
      IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) := by
  have := isSemisimpleModule_quotient_jacobson_smul_top (R := R) P
  rw [← isIndecomposableModule_quotient_smul_top_iff IsSemiprimaryRing.isNilpotent]
  exact ⟨IsIndecomposableModule.isSimpleModule, fun _ ↦ IsSimpleModule.isIndecomposableModule⟩

/-- The radical of an indecomposable projective module over a semiprimary ring is a maximal
submodule. -/
theorem IsIndecomposableModule.isCoatom_jacobson_smul_top [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) :
    IsCoatom (Ring.jacobson R • (⊤ : Submodule R P)) := by
  rw [← isSimpleModule_iff_isCoatom]
  exact isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top.mp h

/-- **An indecomposable projective module is the projective cover of each of its simple
quotients.**  Over a semiprimary ring, any surjection from an indecomposable projective module onto
a simple module is a projective cover. -/
theorem IsIndecomposableModule.isProjectiveCover_of_surjective [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) : IsProjectiveCover f where
  projective := ‹_›
  surjective := hf
  isSuperfluous_ker :=
    have := IsSimpleModule.nontrivial R M
    have := isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top.mp h
    ker_eq_jacobson_smul_top_of_ne_zero (LinearMap.ne_zero_of_surjective hf) ▸
      isSuperfluous_smul_top_of_isNilpotent IsSemiprimaryRing.isNilpotent

/-- A surjection from an indecomposable projective module `P` onto a simple module induces the
canonical equivalence from the simple top of `P` to that module. -/
noncomputable def IsIndecomposableModule.quotientJacobsonEquivOfSurjective [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) :
    (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) ≃ₗ[R] M :=
  have := IsSimpleModule.nontrivial R M
  have := isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top.mp h
  (Submodule.quotEquivOfEq _ _
    (ker_eq_jacobson_smul_top_of_ne_zero (LinearMap.ne_zero_of_surjective hf)).symm).trans
    (f.quotKerEquivOfSurjective hf)

@[simp]
theorem IsIndecomposableModule.quotientJacobsonEquivOfSurjective_mk [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) (x : P) :
    h.quotientJacobsonEquivOfSurjective M f hf (Submodule.Quotient.mk x) = f x := by
  simp [IsIndecomposableModule.quotientJacobsonEquivOfSurjective]

end Projective

end TauCeti
