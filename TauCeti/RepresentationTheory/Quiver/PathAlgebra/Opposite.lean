/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Opposites of path algebras

For a quiver with finitely many vertices and involutive arrow reversal, reversing every path
identifies its path algebra with its opposite algebra. This file constructs that identification
directly on the path basis and records its action on paths, vertices, and arrows.

This identifies left modules with right modules over the same path algebra and transports
reversal-invariant relations to the opposite algebra.

## Main definitions

* `TauCeti.PathAlgebra.reverseOpAlgEquiv`: the algebra isomorphism from a path algebra to its
  opposite induced by path reversal.
-/

public section

namespace TauCeti

open _root_.Quiver MulOpposite

universe u v w

namespace PathAlgebra

section Reverse

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q]
  [HasInvolutiveReverse Q] [Finite Q]

omit [Finite Q] in
private theorem reverseOp_hcomp {a b c : Q} (p : Path a b) (q : Path c a) :
    op (ofPath (Quiver.TotalPath.reverse ⟨a, b, p⟩) : pathAlgebra k Q) *
        op (ofPath (Quiver.TotalPath.reverse ⟨c, a, q⟩) : pathAlgebra k Q) =
      op (ofPath (Quiver.TotalPath.reverse ⟨c, b, q.comp p⟩) : pathAlgebra k Q) := by
  rw [← op_mul, ofPath_mul_ofPath, ← Quiver.TotalPath.map_reverse_mul?]
  simp

private theorem reverseOp_hzero {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    op (ofPath x.reverse : pathAlgebra k Q) * op (ofPath y.reverse : pathAlgebra k Q) = 0 := by
  rw [← op_mul, ofPath_mul_ofPath, ← Quiver.TotalPath.map_reverse_mul?,
    Quiver.TotalPath.mul?_eq_none h]
  simp

private theorem reverseOp_hone :
    letI := Fintype.ofFinite Q
    ∑ a : Q, op (ofPath (Quiver.TotalPath.reverse ⟨a, a, Path.nil⟩) : pathAlgebra k Q) = 1 := by
  let _ := Fintype.ofFinite Q
  simp only [Quiver.TotalPath.reverse_mk, Path.reverse, ofPath_eq_single,
    ← vertexIdempotent_eq_single]
  rw [← Finset.op_sum Finset.univ]
  exact (congrArg op (one_def (k := k) (Q := Q))).symm

private noncomputable def reverseOpAlgHom :
    pathAlgebra k Q →ₐ[k] (pathAlgebra k Q)ᵐᵒᵖ :=
  liftAlgHom k (fun x ↦ op (ofPath x.reverse)) (reverseOp_hcomp k Q)
    (reverseOp_hzero k Q) (reverseOp_hone k Q)

@[simp]
private theorem reverseOpAlgHom_ofPath (x : Quiver.TotalPath Q) :
    reverseOpAlgHom k Q (ofPath x) = op (ofPath x.reverse) := by
  rw [reverseOpAlgHom, liftAlgHom_ofPath]

/-- For a quiver with finitely many vertices and involutive arrow reversal, reversing paths
identifies its path algebra with its opposite algebra. -/
noncomputable def reverseOpAlgEquiv : pathAlgebra k Q ≃ₐ[k] (pathAlgebra k Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverseOpAlgHom k Q) (AlgHom.opComm (reverseOpAlgHom k Q))
    (by
      apply AlgHom.unop.injective
      apply algHom_ext k
      intro x
      simp)
    (algHom_ext k fun x ↦ by simp)

/-- The path-reversal isomorphism sends a basis path to the opposite of its reverse. -/
@[simp]
theorem reverseOpAlgEquiv_ofPath (x : Quiver.TotalPath Q) :
    reverseOpAlgEquiv k Q (ofPath x) = op (ofPath x.reverse) := by
  rw [reverseOpAlgEquiv, AlgEquiv.ofAlgHom_apply, reverseOpAlgHom_ofPath]

/-- The inverse path-reversal isomorphism sends the opposite of a basis path to its reverse. -/
@[simp]
theorem reverseOpAlgEquiv_symm_op_ofPath (x : Quiver.TotalPath Q) :
    (reverseOpAlgEquiv k Q).symm (op (ofPath x)) = ofPath x.reverse := by
  apply (reverseOpAlgEquiv k Q).injective
  simp

/-- Path reversal fixes vertex idempotents, up to passage to the opposite algebra. -/
@[simp]
theorem reverseOpAlgEquiv_vertexIdempotent (a : Q) :
    reverseOpAlgEquiv k Q (vertexIdempotent k a) = op (vertexIdempotent k a) := by
  simpa only [vertexIdempotent_eq_single, ofPath_eq_single, Quiver.TotalPath.reverse_mk,
    Path.reverse] using reverseOpAlgEquiv_ofPath k Q ⟨a, a, Path.nil⟩

/-- Path reversal sends an arrow to the opposite of its reversed arrow. This is not a `simp`
lemma, since `TauCeti.PathAlgebra.ofArrow_eq_ofPath` rewrites its left-hand side. -/
theorem reverseOpAlgEquiv_ofArrow {a b : Q} (e : a ⟶ b) :
    reverseOpAlgEquiv k Q (ofArrow e) = op (ofArrow (Quiver.reverse e)) := by
  simp

end Reverse

end PathAlgebra

end TauCeti
