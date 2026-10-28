/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction

/-!
# Primitive reduced forms

Every positive definite integral binary quadratic form of discriminant `-D` is properly
equivalent to exactly one reduced form
(`TauCeti.BinaryQuadraticForm.orbit_mk_reducedForms_bijective`).
Primitivity is invariant under proper equivalence, so restricting to primitive forms on both sides
keeps the bijection: the primitive reduced forms of discriminant `-D` represent the proper
equivalence classes of primitive positive definite forms, `PosDefProperClass D`, each exactly once.

The finite set `TauCeti.primitiveReducedForms D` is a filter of the decidable set
`TauCeti.reducedForms D`, so the kernel can evaluate it. Its cardinality is the unweighted number of
proper classes of primitive positive definite forms, in contrast with the weighted count of all
classes recorded by `TauCeti.hurwitzClassNumber`.

## Main definitions and results

* `TauCeti.primitiveReducedForms D`: the primitive reduced forms of discriminant `-D`.
* `TauCeti.mem_primitiveReducedForms`: membership is being primitive and reduced of discriminant
  `-D`.
* `TauCeti.BinaryQuadraticForm.posDefProperClass_mk_primitiveReducedForms_bijective`: the primitive
  reduced forms represent the proper classes of primitive positive definite forms, each exactly
  once.
* `TauCeti.BinaryQuadraticForm.nat_card_posDefProperClass`: so there are
  `#(primitiveReducedForms D)` such classes, and finitely many of them.

## Implementation notes

`TauCeti.primitiveReducedForms` filters by the gcd of the coefficients rather than by
`TauCeti.BinaryQuadraticForm.IsPrimitive`, whose definition is not exposed, so that the kernel can
still evaluate the set. `TauCeti.mem_primitiveReducedForms` restates membership with `IsPrimitive`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
* D. A. Cox, *Primes of the Form x² + ny²*, §2, Theorem 2.8.
-/

public section

open Finset MulAction
open scoped MatrixGroups

namespace TauCeti

/-- The primitive reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D`: the reduced
forms whose coefficients have gcd one. For `D ≠ 0`, `mem_primitiveReducedForms` characterises
membership by `BinaryQuadraticForm.IsPrimitive`. -/
@[expose] def primitiveReducedForms (D : ℕ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ reducedForms D | Int.gcd f.a (Int.gcd f.b f.c) = 1}

/-- **The primitive reduced forms of discriminant `-D`**: for `D ≠ 0`, `f` lies in
`primitiveReducedForms D` exactly when `f.discrim = -D`, `f` is reduced, and `f` is primitive. -/
@[simp] theorem mem_primitiveReducedForms {D : ℕ} (hD : D ≠ 0) {f : BinaryQuadraticForm ℤ} :
    f ∈ primitiveReducedForms D ↔ f.discrim = -D ∧ IsReducedForm f ∧ f.IsPrimitive := by
  rw [primitiveReducedForms, mem_filter, mem_reducedForms hD, BinaryQuadraticForm.isPrimitive_iff,
    BinaryQuadraticForm.content_def, and_assoc]

/-- The primitive reduced forms are among the reduced forms. -/
theorem primitiveReducedForms_subset_reducedForms (D : ℕ) :
    primitiveReducedForms D ⊆ reducedForms D :=
  filter_subset _ _

namespace BinaryQuadraticForm

variable {D : ℕ} [NeZero D]

/-- A primitive reduced form of discriminant `-D` is a primitive positive definite form. -/
theorem mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ primitiveReducedForms D) : f ∈ posDef D ⊓ primitiveForms (-D) := by
  have hpos := mem_posDef.1 <|
    mem_posDef_of_mem_reducedForms (primitiveReducedForms_subset_reducedForms D hf)
  exact (mem_posDef_inf_primitiveForms D).2
    ⟨hpos.1, hpos.2, ((mem_primitiveReducedForms (NeZero.ne D)).1 hf).2.2⟩

/-- **The primitive reduced forms of discriminant `-D` represent the proper classes of primitive
positive definite forms**: sending a primitive reduced form to its proper equivalence class is a
bijection from `primitiveReducedForms D` onto `PosDefProperClass D` (Cohen, §5.3). -/
theorem posDefProperClass_mk_primitiveReducedForms_bijective :
    Function.Bijective fun f : primitiveReducedForms D ↦
      (Quotient.mk'' ⟨f, mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2⟩ :
        PosDefProperClass D) := by
  have hr (f : primitiveReducedForms D) : IsReducedForm f.1 :=
    ((mem_primitiveReducedForms (NeZero.ne D)).1 f.2).2.1
  have hpos (f : primitiveReducedForms D) : f.1 ∈ posDef D :=
    mem_posDef_of_mem_reducedForms (primitiveReducedForms_subset_reducedForms D f.2)
  refine ⟨fun f g h ↦ Subtype.ext ?_, Quotient.ind' fun f ↦ ?_⟩
  · -- proper equivalence of the primitive forms is proper equivalence of the positive definite
    -- forms, and the reduced representative of a positive definite class is unique
    obtain ⟨γ, hγ⟩ := Quotient.exact' h
    have hfg : (Quotient.mk'' ⟨f.1, hpos f⟩ : orbitRel.Quotient SL(2, ℤ) (posDef D)) =
        Quotient.mk'' ⟨g.1, hpos g⟩ :=
      Quotient.sound' ⟨γ, Subtype.ext <| by
        simpa only [SubMulAction.val_smul] using congrArg Subtype.val hγ⟩
    exact Subtype.mk.inj (orbit_mk_injOn_isReducedForm (by exact hr f) (by exact hr g) hfg)
  · -- reduce the form as a positive definite form; primitivity survives the change of variables
    have hf := (mem_posDef_inf_primitiveForms D).1 f.2
    obtain ⟨γ, hγ⟩ := exists_smul_isReducedForm (⟨f, mem_posDef.2 ⟨hf.1, hf.2.1⟩⟩ : posDef D)
    have hmem : γ • (f : BinaryQuadraticForm ℤ) ∈ primitiveReducedForms D :=
      (mem_primitiveReducedForms (NeZero.ne D)).2
        ⟨(discrim_smul γ _).trans hf.1, hγ, (isPrimitive_smul_iff _ γ).2 hf.2.2⟩
    exact ⟨⟨_, hmem⟩, Quotient.sound' ⟨γ, rfl⟩⟩

/-- There are finitely many proper classes of primitive positive definite forms of discriminant
`-D`. -/
instance finite_posDefProperClass : Finite (PosDefProperClass D) :=
  .of_surjective _ posDefProperClass_mk_primitiveReducedForms_bijective.2

/-- **The number of proper classes of primitive positive definite forms** of discriminant `-D` is
the number of primitive reduced forms of discriminant `-D`. -/
theorem nat_card_posDefProperClass : Nat.card (PosDefProperClass D) = #(primitiveReducedForms D) :=
  (Nat.card_eq_of_bijective _ posDefProperClass_mk_primitiveReducedForms_bijective).symm.trans
    (Nat.card_eq_finsetCard _)

end BinaryQuadraticForm

end TauCeti
