/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Decomposition
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting.Equiv
public import TauCeti.FieldTheory.FunctionField.Place.ConstantField
import Mathlib.FieldTheory.Normal.Closure

/-!
# Complete splitting in composita

Complete splitting in an intermediate field of a finite Galois extension means that every
upstairs decomposition group fixes that intermediate field pointwise. Since the fixing subgroup
of a compositum is the intersection of the fixing subgroups, complete splitting passes to
composita. Embedding a finite separable extension into its finite Galois closure removes the
Galois hypothesis on the ambient field. A completely split rational place also certifies exactness
of the constant field of the compositum.

The decomposition-group argument follows the number-field analogue in
`TauCeti/NumberTheory/NumberField/SplitsCompletely/GaloisClosure.lean`, using the place-theoretic
fundamental identity and multiplicativity of ramification and residue degrees instead of ideals.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.9.7.
-/

public section

namespace TauCeti.Place

universe u v w

variable {k : Type u} {F : Type v} {M : Type w}
variable [Field k] [Field F] [Field M] [Algebra k F] [Algebra k M] [Algebra F M]
variable [IsScalarTower k F M] [FiniteDimensional F M]

section Galois

variable [IsGalois F M]

/-- Complete splitting in a compositum is equivalent to complete splitting in both
constituents. The two intermediate fields need not be Galois over the base. -/
private theorem isSplitCompletely_sup_iff_of_isGalois
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    P.IsSplitCompletely (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsSplitCompletely (k' := k) (F' := E₁) ∧
        P.IsSplitCompletely (k' := k) (F' := E₂) := by
  simp only [isSplitCompletely_iff_forall_decompositionSubgroup_le hF,
    IntermediateField.fixingSubgroup_sup, le_inf_iff, ← forall_and]

end Galois

/-- **Complete splitting in a compositum** (Stichtenoth, Corollary 3.9.7).
For intermediate fields of any finite separable extension, a place splits completely in their
compositum if and only if it splits completely in each constituent. No rationality, perfectness,
or exact-constants hypothesis is needed for this equivalence. -/
@[simp]
theorem isSplitCompletely_sup_iff [Algebra.IsSeparable F M]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    P.IsSplitCompletely (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsSplitCompletely (k' := k) (F' := E₁) ∧
        P.IsSplitCompletely (k' := k) (F' := E₂) := by
  -- Embed the whole ambient extension into its finite Galois closure, then transport all three
  -- intermediate fields along the same embedding.
  let A := AlgebraicClosure F
  let N := IntermediateField.normalClosure F M A
  have : Algebra.IsSeparable F N := by
    have (f : M →ₐ[F] A) : Algebra.IsSeparable F f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    apply (le_separableClosure_iff F A N).mp
    dsimp only [N]
    rw [normalClosure_def]
    exact iSup_le fun f ↦ le_separableClosure F A f.fieldRange
  have : IsGalois F N := ⟨⟩
  let g : M →ₐ[F] N := (IsAlgClosed.lift (R := F) (S := M) (M := A)).codRestrict N.toSubalgebra
    fun x ↦ (IsAlgClosed.lift (R := F) (S := M) (M := A)).fieldRange_le_normalClosure ⟨x, rfl⟩
  rw [isSplitCompletely_iff_of_algEquiv P ((E₁ ⊔ E₂).equivMap g),
    isSplitCompletely_iff_of_algEquiv P (E₁.equivMap g),
    isSplitCompletely_iff_of_algEquiv P (E₂.equivMap g), IntermediateField.map_sup]
  exact isSplitCompletely_sup_iff_of_isGalois hF P (E₁.map g) (E₂.map g)

/-- If a rational place splits completely in both constituents, their compositum has
exact constant field `k` (Stichtenoth, Corollary 3.9.7). -/
theorem isIntegrallyClosedIn_sup_of_isSplitCompletely [Algebra.IsSeparable F M]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (hP : P.degree = 1)
    (E₁ E₂ : IntermediateField F M)
    (h₁ : P.IsSplitCompletely (k' := k) (F' := E₁))
    (h₂ : P.IsSplitCompletely (k' := k) (F' := E₂)) :
    IsIntegrallyClosedIn k ↥(E₁ ⊔ E₂) := by
  have hsplit := (isSplitCompletely_sup_iff hF P E₁ E₂).mpr ⟨h₁, h₂⟩
  obtain ⟨Q, hQ⟩ := restrict_surjective_of_finiteDimensional
    hF (hF.finite_extension (E := ↥(E₁ ⊔ E₂))) P
  exact Q.isIntegrallyClosedIn_of_degree_eq_one (hsplit.degree_eq_one hP hQ)

end TauCeti.Place
