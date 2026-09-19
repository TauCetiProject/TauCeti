/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.Algebra.GroupAction.AlgHom

-- Roadmap source: `TauCetiRoadmap/NumberFieldArithmetic/README.md` @ `ce02686a0c05`, Layer 7.1,
-- the subfield dictionary, which these general field-theory facts serve. The credit sits outside
-- the module docstring deliberately: the docstring documents the mathematics.

/-!
# Embeddings into a normal extension, and the action on them

For fields `L` and `M` over a base `F`, the group `M ≃ₐ[F] M` acts on the embeddings
`L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`). This file records
the three facts that make that action a dictionary for the subfields of `L`.

*Transitivity.* When `M / F` is normal, any two embeddings lie in the same orbit, because an
isomorphism between two embedded images extends to `M`. This asserts nothing about existence:
if no embedding `L →ₐ[F] M` exists the statement holds vacuously.

*Faithfulness.* When the embedded images generate `M` — that is, when
`IntermediateField.normalClosure F L M = ⊤` — an automorphism fixing every embedding is the
identity, so the action has trivial kernel.

*Counting.* When `L / F` is finite and separable, `M / F` is normal, and at least one embedding
`L →ₐ[F] M` exists, there are exactly `[L : F]` of them. All three hypotheses are needed: without
separability the count drops, and without normality the minimal polynomials need not split in `M`.

## Main results

* `AlgEquiv.liftNormal_equivFieldRange_apply`: lifting the isomorphism between two embedded
  images carries one embedding to the other. This isolates the field-range bookkeeping.
* `AlgEquiv.isPretransitiveAlgHom`: over a normal `M / F`, any two embeddings lie in one orbit.
* `TauCeti.FieldTheory.apply_of_smul_eq`: an automorphism fixing an embedding fixes its values;
  this isolates the coercion the postcomposition action introduces.
* `TauCeti.FieldTheory.eq_one_of_forall_smul_eq`: if the embedded images generate `M`, an
  automorphism fixing every embedding is the identity.
* `TauCeti.FieldTheory.faithfulSMul_of_normalClosure_eq_top`: equivalently, the action is
  faithful. Injectivity of the permutation representation is then Mathlib's
  `smul_left_injective'`.
* `AlgHom.card_of_normal`: for `L / F` finite separable and `M / F` normal admitting an embedding
  of `L`, there are exactly `[L : F]` embeddings.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §9.
-/

public section

open Polynomial IntermediateField

namespace AlgEquiv

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **Lifting the isomorphism between two embedded images carries one embedding to the other.**

This isolates the field-range and coercion bookkeeping: `φ x` is transported into `φ.fieldRange`,
the isomorphism `φ.fieldRange ≃ ψ.fieldRange` is applied there, and `liftNormal_commutes` brings
the result back to `M`. Keeping it separate lets `isPretransitiveAlgHom` state only the
mathematical step. -/
theorem liftNormal_equivFieldRange_apply [Normal F M] (φ ψ : L →ₐ[F] M) (x : L) :
    ((φ.equivFieldRange.symm.trans ψ.equivFieldRange).liftNormal M) (φ x) = ψ x := by
  have hl : φ x = (algebraMap (↥φ.fieldRange) M) (φ.equivFieldRange x) := by simp
  rw [hl, AlgEquiv.liftNormal_commutes _ M (φ.equivFieldRange x), AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, IntermediateField.algebraMap_apply,
    AlgHom.equivFieldRange_apply_coe]

/-- **Any two embeddings into a normal extension are conjugate**, so they lie in the same orbit.
No embedding is asserted to exist: when `L →ₐ[F] M` is empty this holds vacuously. -/
instance isPretransitiveAlgHom [Normal F M] :
    MulAction.IsPretransitive (M ≃ₐ[F] M) (L →ₐ[F] M) where
  -- Transport `φ`'s field range onto `ψ`'s, then lift that isomorphism to `M` by normality.
  exists_smul_eq φ ψ :=
    ⟨(φ.equivFieldRange.symm.trans ψ.equivFieldRange).liftNormal M, AlgHom.ext fun x => by
      rw [smul_algHom_apply]
      exact liftNormal_equivFieldRange_apply φ ψ x⟩

end AlgEquiv

namespace TauCeti.FieldTheory

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **An automorphism fixing an embedding fixes its values.** The postcomposition action phrases
the image through `f.toRingHom`, so this normalises that coercion once, instead of at each use. -/
theorem apply_of_smul_eq {σ : M ≃ₐ[F] M} {f : L →ₐ[F] M} (h : σ • f = f) (x : L) :
    σ (f x) = f x := by
  simpa only [AlgEquiv.smul_algHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    congrArg (fun ρ : L →ₐ[F] M => ρ x) h

/-- **An automorphism fixing every embedding is the identity**, provided the embedded images of
`L` generate `M`. -/
theorem eq_one_of_forall_smul_eq (hgen : IntermediateField.normalClosure F L M = ⊤)
    {σ : M ≃ₐ[F] M} (h : ∀ φ : L →ₐ[F] M, σ • φ = φ) : σ = 1 := by
  set H := Subgroup.closure ({σ} : Set (M ≃ₐ[F] M)) with hH
  have hfix : ∀ f : L →ₐ[F] M, f.fieldRange ≤ IntermediateField.fixedField H := by
    intro f
    rw [IntermediateField.le_iff_le, hH, Subgroup.closure_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    exact apply_of_smul_eq (h f) x
  have htop : (⊤ : IntermediateField F M) ≤ IntermediateField.fixedField H := by
    -- Unfold the normal closure to the supremum of the field ranges explicitly, rather than
    -- letting `iSup_le` match through the definition.
    rw [← hgen, normalClosure_def]
    exact iSup_le hfix
  rw [IntermediateField.le_iff_le, IntermediateField.fixingSubgroup_top, le_bot_iff] at htop
  have : σ ∈ (⊥ : Subgroup (M ≃ₐ[F] M)) := htop ▸ Subgroup.subset_closure rfl
  simpa using this

/-- **The action on embeddings is faithful** when the embedded images generate `M`.

With this instance in scope, injectivity of the permutation representation is Mathlib's
`smul_left_injective'`; no separate statement is needed. -/
theorem faithfulSMul_of_normalClosure_eq_top
    (hgen : IntermediateField.normalClosure F L M = ⊤) :
    FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M) :=
  faithfulSMul_iff.2 fun _ h => eq_one_of_forall_smul_eq hgen h

end TauCeti.FieldTheory

namespace AlgHom

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **The number of embeddings is the degree.** For `L / F` finite and separable and `M / F`
normal, the existence of one embedding `φ : L →ₐ[F] M` forces there to be exactly `[L : F]` of
them: every minimal polynomial over `F` of an element of `L` splits in `M`. -/
theorem card_of_normal [FiniteDimensional F L] [Algebra.IsSeparable F L] [Normal F M]
    (φ : L →ₐ[F] M) : Fintype.card (L →ₐ[F] M) = Module.finrank F L := by
  refine AlgHom.card_of_splits F L M ?_
  intro x
  -- An embedding preserves minimal polynomials, and `M / F` is normal.
  have h : minpoly F (φ x) = minpoly F x := minpoly.algHom_eq φ φ.injective x
  rw [← h]
  exact Normal.splits inferInstance (φ x)

end AlgHom

end
