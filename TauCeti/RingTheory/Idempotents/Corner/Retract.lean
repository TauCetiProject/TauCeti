/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# Endomorphism rings of retracts as corners

If `X` is a retract of a module `M`, with inclusion `i : X → M` and retraction `p : M → X`, then
`i ∘ p` is an idempotent of `End_A M`, and `f ↦ p ∘ f ∘ i` identifies its corner with `End_A X`. The
statements are made in the opposite ring `(End_A M)ᵐᵒᵖ`, the ring in which the regular module `A`
recovers `A` itself: `(End_A A)ᵐᵒᵖ ≃ A`.

When `M = X ⊕ Y`, the idempotent of `X` is full as soon as `Y` is a retract of a finite power of
`X`. This is what relates the module categories of the endomorphism rings of different modules in
Morita theory, in `TauCeti.RingTheory.Morita.Progenerator`.

## Main definitions

* `TauCeti.cornerEndRetractAlgEquiv`: the corner of `(End_A M)ᵐᵒᵖ` at the idempotent of a retract
  `X` is `(End_A X)ᵐᵒᵖ`.

## Main results

* `TauCeti.isIdempotentElem_op_comp`: the idempotent of a retract.
* `TauCeti.span_op_comp_eq_top`: this idempotent is full when `id_Y` is a finite sum of maps
  factoring through `X`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, §18 (corner rings
  and direct summands in Morita theory).
-/

public section

open MulOpposite

namespace TauCeti

variable {A : Type*} [Ring A] {X : Type*} [AddCommGroup X] [Module A X]
  {M : Type*} [AddCommGroup M] [Module A M]

/-- The idempotent of `(End_A M)ᵐᵒᵖ` attached to a retract `X` of `M`, with inclusion `i` and
retraction `p`. -/
theorem isIdempotentElem_op_comp {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id) :
    IsIdempotentElem (op (i ∘ₗ p : Module.End A M)) := by
  have h : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  apply unop_injective
  ext x
  simp [h]

/-- An endomorphism of `M` factoring through its retract `X` lies in the two-sided ideal generated
by the idempotent of `X`. -/
private theorem op_comp_mem_span_op_comp {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id)
    (u : X →ₗ[A] M) (v : M →ₗ[A] X) :
    op (u ∘ₗ v : Module.End A M) ∈ TwoSidedIdeal.span {op (i ∘ₗ p : Module.End A M)} := by
  have h : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  have key : op (u ∘ₗ v : Module.End A M) =
      op (i ∘ₗ v : Module.End A M) * op (i ∘ₗ p : Module.End A M) *
        op (u ∘ₗ p : Module.End A M) := by
    apply unop_injective
    ext x
    simp [h]
  rw [key]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))

variable {Y : Type*} [AddCommGroup Y] [Module A Y]

/-- If `M = X ⊕ Y` and `id_Y` is a finite sum of maps factoring through `X`, that is, `Y` is a
retract of a finite power of `X`, then the idempotent of `X` is full in `(End_A M)ᵐᵒᵖ`. -/
theorem span_op_comp_eq_top {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id)
    {i' : Y →ₗ[A] M} {p' : M →ₗ[A] Y} (hsum : i ∘ₗ p + i' ∘ₗ p' = .id)
    {ι : Type*} (s : Finset ι) (u : ι → X →ₗ[A] Y) (v : ι → Y →ₗ[A] X)
    (huv : ∑ j ∈ s, u j ∘ₗ v j = .id) :
    TwoSidedIdeal.span {op (i ∘ₗ p : Module.End A M)} = ⊤ := by
  refine (TwoSidedIdeal.one_mem_iff _).mp ?_
  have key : (1 : (Module.End A M)ᵐᵒᵖ) = op (i ∘ₗ p : Module.End A M) +
      ∑ j ∈ s, op ((i' ∘ₗ u j) ∘ₗ (v j ∘ₗ p') : Module.End A M) := by
    apply unop_injective
    ext x
    have hx := LinearMap.congr_fun hsum x
    have hy := LinearMap.congr_fun huv (p' x)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at hy
    simpa [LinearMap.sum_apply, ← map_sum, hy] using hx.symm
  rw [key]
  exact add_mem (TwoSidedIdeal.subset_span rfl)
    (sum_mem fun j _ ↦ op_comp_mem_span_op_comp hip _ _)

private theorem comp_unop_corner_val {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_op_comp hip).Corner) (x : M) : i (p (unop c.1 x)) = unop c.1 x :=
  LinearMap.congr_fun (congrArg unop ((isIdempotentElem_op_comp hip).corner_val_mul c)) x

private theorem unop_corner_val_comp {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_op_comp hip).Corner) (x : M) : unop c.1 (i (p x)) = unop c.1 x :=
  LinearMap.congr_fun (congrArg unop ((isIdempotentElem_op_comp hip).mul_corner_val c)) x

variable (R : Type*) [CommSemiring R] [Algebra R A] [Module R X] [IsScalarTower R A X]
  [Module R M] [IsScalarTower R A M]

/-- **The endomorphism ring of a retract is a corner.** If `X` is a retract of `M`, with inclusion
`i` and retraction `p`, the corner of `(End_A M)ᵐᵒᵖ` at the idempotent `i ∘ p` is `(End_A X)ᵐᵒᵖ`,
by `f ↦ p ∘ f ∘ i`. -/
noncomputable def cornerEndRetractAlgEquiv {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id) :
    (isIdempotentElem_op_comp hip).Corner ≃ₐ[R] (Module.End A X)ᵐᵒᵖ where
  toFun c := op (p ∘ₗ (unop c.1 : Module.End A M) ∘ₗ i)
  invFun g := (isIdempotentElem_op_comp hip).compress (op (i ∘ₗ unop g ∘ₗ p))
  left_inv c := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    apply Subtype.ext
    apply unop_injective
    ext x
    simp [hpi, comp_unop_corner_val hip c, unop_corner_val_comp hip c]
  right_inv g := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    apply unop_injective
    ext x
    simp [hpi]
  map_mul' c c' := by
    apply unop_injective
    ext x
    simp [comp_unop_corner_val hip c]
  map_add' c c' := by
    apply unop_injective
    ext x
    simp
  commutes' r := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    apply unop_injective
    ext x
    simp [hpi]

@[simp]
theorem unop_cornerEndRetractAlgEquiv_apply {i : X →ₗ[A] M} {p : M →ₗ[A] X} (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_op_comp hip).Corner) :
    unop (cornerEndRetractAlgEquiv R hip c) = p ∘ₗ (unop c.1 : Module.End A M) ∘ₗ i :=
  (rfl)

@[simp]
theorem val_cornerEndRetractAlgEquiv_symm_apply {i : X →ₗ[A] M} {p : M →ₗ[A] X}
    (hip : p ∘ₗ i = .id) (g : (Module.End A X)ᵐᵒᵖ) :
    ((cornerEndRetractAlgEquiv R hip).symm g).1 = op (i ∘ₗ unop g ∘ₗ p) := by
  have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  refine ((isIdempotentElem_op_comp hip).val_compress _).trans ?_
  apply unop_injective
  ext x
  simp [hpi]

end TauCeti
