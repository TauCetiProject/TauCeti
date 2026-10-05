/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.EndQuotient
public import TauCeti.Algebra.Module.ProjectiveCover.Basic
public import TauCeti.RingTheory.Idempotents.Module
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Jacobson.Semiprimary

/-!
# Simple tops of primitive idempotent ideals

Let `A` be a semiprimary ring, with Jacobson radical `J`.  An idempotent `e` determines the
projective left ideal `Ae`, and its **top** is the semisimple quotient

`Ae / J(Ae)`.

This quotient is simple exactly when `e` is primitive, and its quotient map is the projective cover
of that simple module (`TauCeti.isProjectiveCover_mkQ_smul_top_span_singleton`).  Conversely, every
simple module over a left Artinian ring is isomorphic to the top of `Ae` for some primitive
idempotent `e`: choose a primitive orthogonal decomposition of `1`, map one of its summands onto the
simple module, and compare the two maximal kernels.

Nothing in the argument uses more about `Ae` than that it is projective
(`IsIdempotentElem.projective_span_singleton`), so the file first proves the module-level
statements for a projective module `P`.  The proofs use the endomorphism reduction
`Ideal.endMapQ I P`: it is surjective because `P` is projective, and its kernel consists of
nilpotent endomorphisms when `I` is nilpotent.  Thus idempotents lift between the endomorphism
rings of `P` and of `P / IP`, which transfers indecomposability in both directions.  Over a
semiprimary ring the top `P / JP` is semisimple, so it is indecomposable exactly when it is simple;
primitivity of `e` is indecomposability of `Ae`
(`TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`).

## Main definitions

* `TauCeti.IsIndecomposableModule.quotientJacobsonEquivOfSurjective`: the equivalence between the
  top of an indecomposable projective module and any simple module it maps onto.

## Main results

* `TauCeti.isIndecomposableModule_quotient_smul_top_iff`: for a nilpotent ideal `I`, a projective
  module `P` is indecomposable exactly when `P / IP` is; the reflecting direction
  `TauCeti.IsIndecomposableModule.of_quotient_smul_top` holds for every module.
* `TauCeti.isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top`: over a
  semiprimary ring, a projective module is indecomposable exactly when its top is simple.
* `TauCeti.IsIndecomposableModule.isCoatom_jacobson_smul_top` and
  `TauCeti.IsIndecomposableModule.ker_eq_jacobson_smul_top_of_surjective`: the radical of an
  indecomposable projective module is its unique maximal submodule, and is the kernel of every
  surjection onto a simple module.
* `TauCeti.IsIndecomposableModule.isProjectiveCover_of_surjective`: such a surjection is a
  projective cover; `TauCeti.isProjectiveCover_mkQ_smul_top_span_singleton` covers the top of `Ae`
  by `Ae`.
* `TauCeti.isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top`: `e` is primitive
  exactly when `Ae / J(Ae)` is simple.
* `TauCeti.isSimpleModule_iff_exists_isPrimitiveIdempotent_quotient_jacobson_smul_top`: over a
  left Artinian ring, the simple modules are precisely these tops, up to linear equivalence.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.4.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Sections 23--24.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u v w

/-! ### The top of a projective module -/

section Projective

variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
  {I : Ideal R}

omit [Module.Projective R P] in
/-- **Indecomposability reflects from the top.**  If `I` is nilpotent and `P / IP` is
indecomposable, then so is `P`: an idempotent endomorphism of `P` reducing to `0` or `1` differs
from it by a nilpotent idempotent, hence equals it.  No projectivity is needed. -/
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
projective module `P` is indecomposable exactly when `P / IP` is: idempotent endomorphisms lift
along the surjective reduction `Ideal.endMapQ I P`, whose kernel is nil. -/
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

/-- **A projective module is indecomposable exactly when its top is simple.**  Over a semiprimary
ring the top `P / JP` is semisimple, and a semisimple module is indecomposable exactly when it is
simple. -/
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

/-- Any surjection from an indecomposable projective module `P` onto a simple module has kernel
`JP`.  Thus it identifies the simple module with the canonical top of `P`. -/
theorem IsIndecomposableModule.ker_eq_jacobson_smul_top_of_surjective [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) :
    LinearMap.ker f = Ring.jacobson R • (⊤ : Submodule R P) := by
  have hle : Ring.jacobson R • (⊤ : Submodule R P) ≤ LinearMap.ker f :=
    (Ring.jacobson_smul_top_le R P).trans <| IsSemisimpleModule.jacobson_le_ker R R P M f
  exact (h.isCoatom_jacobson_smul_top.le_iff_eq (LinearMap.isCoatom_ker_of_surjective hf).ne_top).mp
    hle

/-- **An indecomposable projective module is the projective cover of each of its simple
quotients.**  Over a semiprimary ring, any surjection from an indecomposable projective module onto
a simple module has kernel `JP`, which is superfluous since `J` is nilpotent. -/
theorem IsIndecomposableModule.isProjectiveCover_of_surjective [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) : IsProjectiveCover f where
  projective := ‹_›
  surjective := hf
  isSuperfluous_ker := h.ker_eq_jacobson_smul_top_of_surjective M f hf ▸
    isSuperfluous_smul_top_of_isNilpotent IsSemiprimaryRing.isNilpotent

/-- A surjection from an indecomposable projective module `P` onto a simple module induces the
canonical equivalence from the simple top of `P` to that module. -/
noncomputable def IsIndecomposableModule.quotientJacobsonEquivOfSurjective [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) :
    (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ (h.ker_eq_jacobson_smul_top_of_surjective M f hf).symm).trans
    (f.quotKerEquivOfSurjective hf)

@[simp]
theorem IsIndecomposableModule.quotientJacobsonEquivOfSurjective_mk [IsSemiprimaryRing R]
    (h : IsIndecomposableModule R P) (M : Type w) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (f : P →ₗ[R] M) (hf : Function.Surjective f) (x : P) :
    h.quotientJacobsonEquivOfSurjective M f hf (Submodule.Quotient.mk x) = f x := by
  simp [IsIndecomposableModule.quotientJacobsonEquivOfSurjective]

end Projective

/-! ### Primitive idempotents -/

variable {A : Type u} [Ring A] {e : A}

/-- **The top of `Ae` is covered by `Ae`.**  For an idempotent `e` and a nilpotent ideal `I`, the
quotient map `Ae →ₗ[A] Ae / I(Ae)` is a projective cover; for `I = J` in a semiprimary ring this is
the cover of the top. -/
theorem isProjectiveCover_mkQ_smul_top_span_singleton (he : IsIdempotentElem e) {I : Ideal A}
    (hI : IsNilpotent I) :
    IsProjectiveCover (I • (⊤ : Submodule A (Ideal.span {e} : Ideal A))).mkQ :=
  have := he.projective_span_singleton
  isProjectiveCover_mkQ_smul_top_of_isNilpotent hI

/-- **A primitive idempotent is characterized by its simple top.**  In a semiprimary ring, an
idempotent `e` is primitive exactly when the radical quotient `Ae / J(Ae)` is a simple module. -/
theorem isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top
    [IsSemiprimaryRing A] (he : IsIdempotentElem e) :
    IsPrimitiveIdempotent e ↔
      IsSimpleModule A
        ((Ideal.span {e} : Ideal A) ⧸
          Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e} : Ideal A))) :=
  have := he.projective_span_singleton
  (isPrimitiveIdempotent_iff_isIndecomposableModule he).trans
    isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top

/-- **Simple modules over a left Artinian ring are exactly the tops of primitive idempotent
ideals.** -/
theorem isSimpleModule_iff_exists_isPrimitiveIdempotent_quotient_jacobson_smul_top
    [IsArtinianRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    IsSimpleModule A M ↔
      ∃ e : A, IsPrimitiveIdempotent e ∧
        Nonempty (M ≃ₗ[A]
          ((Ideal.span {e} : Ideal A) ⧸
            Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e} : Ideal A)))) := by
  constructor
  · intro hM
    let _ : IsSimpleModule A M := hM
    obtain ⟨n, e, he, hprim⟩ := exists_completeOrthogonalIdempotents_isPrimitiveIdempotent A
    obtain ⟨i, f, hf⟩ := he.exists_surjective_of_isSimpleModule M
    have := (hprim i).isIdempotentElem.projective_span_singleton
    exact ⟨e i, hprim i,
      ⟨(hprim i).isIndecomposableModule.quotientJacobsonEquivOfSurjective M f hf |>.symm⟩⟩
  · rintro ⟨e, he, ⟨φ⟩⟩
    have htop := (isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top
      he.isIdempotentElem).mp he
    exact φ.isSimpleModule_iff.mpr htop

end TauCeti
