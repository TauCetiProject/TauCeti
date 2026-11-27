/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Invariant.Basic
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Fixed fields of automorphism groups of function fields

If a finite group of automorphisms acts on an algebraic function field `F / k`, its fixed field
is again an algebraic function field over `k`. The extension of the fixed field is finite Galois,
and its Galois group is the acting group. This is the field-theoretic input to applying
Riemann--Hurwitz to a quotient by a finite automorphism group.

At the other extreme, if `F / k` has exact constants and infinitely many `k`-automorphisms, they
fix nothing outside `k`: `F` is finite over any subfield containing an element transcendental over
`k`, and has only finitely many automorphisms over it. This feeds Rosenlicht's separability
criterion `TauCeti.exists_isTranscendenceBasis_and_isSeparable_of_fixedField_eq_bot`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.7.
* M. Rosenlicht, *Automorphisms of function fields*, Trans. Amer. Math. Soc. 79 (1955), 1–11,
  §3, p. 5.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The fixed field of a finite group of `k`-automorphisms of a function field is itself a
function field over `k`. `IsGalois.of_fixed_field` makes `F` Galois over
this field, and `FixedPoints.toAlgAutMulEquiv` identifies its Galois group
with `H`. -/
theorem IsFunctionField.fixedField (hF : IsFunctionField k F)
    (H : Subgroup (F ≃ₐ[k] F)) [Finite H] :
    IsFunctionField k (IntermediateField.fixedField H) := by
  -- Every `H`-fixed element lies in `fixedField H`, so `F` is integral over it.
  have : Algebra.IsInvariant (IntermediateField.fixedField H) F H :=
    ⟨fun x hx ↦ ⟨⟨x, (IntermediateField.mem_fixedField_iff H x).2 fun σ hσ ↦ by
      simpa only [Subgroup.mk_smul, AlgEquiv.smul_def] using hx ⟨σ, hσ⟩⟩,
      IntermediateField.algebraMap_apply _ _⟩⟩
  have := Algebra.IsInvariant.isIntegral (IntermediateField.fixedField H) F H
  exact hF.of_isAlgebraic_top (E := IntermediateField.fixedField H)

/-- **A function field with infinitely many automorphisms has fixed field `k`**: if `F / k` has
exact constants and infinitely many `k`-automorphisms, the only elements of `F` fixed by all of them
are those of `k`.

Exactness cannot be dropped: every `ℚ`-automorphism of `ℚ(∛2)(x)` fixes `∛2`, the only cube root of
`2` in this field, while the translations `x ↦ x + n` are infinitely many. -/
theorem IsFunctionField.fixedField_top_eq_bot (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Infinite (F ≃ₐ[k] F)] :
    IntermediateField.fixedField (⊤ : Subgroup (F ≃ₐ[k] F)) = ⊥ := by
  refine eq_bot_iff.2 fun y hy ↦ ?_
  by_cases hyt : Transcendental k y
  · -- Every automorphism fixes `k(y)`, over which `F` is finite and has finitely many
    -- automorphisms.
    have := hF.finiteDimensional_adjoin hyt
    have hle : (⊤ : Subgroup (F ≃ₐ[k] F)) ≤ IntermediateField.fixingSubgroup k⟮y⟯ :=
      (IntermediateField.le_fixedField_iff_le_fixingSubgroup _ _).1
        (IntermediateField.adjoin_simple_le_iff.2 hy)
    have := IntermediateField.finite_fixingSubgroup k⟮y⟯
    have : Finite (⊤ : Subgroup (F ≃ₐ[k] F)) := Finite.Set.subset _ hle
    exact (not_finite_iff_infinite.2 ‹_› (Subgroup.topEquiv.finite_iff.1 this)).elim
  · obtain ⟨x, rfl⟩ := hex.isIntegral_iff.mp (not_not.1 hyt).isIntegral
    exact IntermediateField.algebraMap_mem _ x

end TauCeti
