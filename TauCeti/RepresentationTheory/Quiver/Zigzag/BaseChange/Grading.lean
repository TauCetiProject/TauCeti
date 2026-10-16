/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.BaseChange.TensorProduct
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Grading

/-!
# Graded scalar extension of skew-zigzag algebras

The scalar-extension equivalence of skew-zigzag relation quotients identifies the extension of
each path-length piece with the corresponding piece over the new coefficient ring. Thus it is
graded for Mathlib's tensor-product grading `fun n ↦ (skewZigzagGrade k G c n).baseChange l`,
in which the coefficient algebra has degree zero.

The comparison works over arbitrary commutative-ring algebras, without flatness or injectivity
of the coefficient map. Both pieces are spanned by the same length-`n` path classes. This also
covers disconnected graphs and isolated vertices in the relation quotient; the exceptional
dual-number factors in the public componentwise ordinary zigzag algebra are a separate object.

## References

* C. Couture, *Skew-Zigzag Algebras*, Section 3, for the parameterized path-graded presentations.
-/

public section

namespace SimpleGraph

open scoped TensorProduct
open TauCeti TauCeti.PathAlgebra TauCeti.DoubledQuiver

universe u w z

variable {k : Type w} {l : Type z} [CommRing k] [CommRing l] [Algebra k l]
  {V : Type u} (G : SimpleGraph V) [Finite V] (c : SkewZigzagParameter k G)

/-- Scalar extension identifies each tensor-product graded piece with the path-length piece
of the quotient with extended parameters. -/
theorem skewZigzagScalarExtensionEquiv_map_baseChange_skewZigzagGrade (n : ℕ) :
    ((skewZigzagGrade k G c n).baseChange l).map
      (skewZigzagScalarExtensionEquiv (l := l) G c).toLinearEquiv.toLinearMap =
        skewZigzagGrade l G (c.map (algebraMap k l : k →* l)) n := by
  rw [skewZigzagGrade_eq_span_range, Submodule.baseChange_span, Submodule.map_span,
    ← Set.range_comp', ← Set.range_comp', skewZigzagGrade_eq_span_range]
  congr 1
  congr 1
  funext p
  simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    TensorProduct.mk_apply, skewZigzagScalarExtensionEquiv_tmul, one_smul,
    skewZigzagBaseChange_skewZigzagMk_ofPath]

/-- The scalar-extension equivalence preserves and reflects path degree for the induced
tensor-product grading. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_mem_skewZigzagGrade_iff {n : ℕ}
    {x : l ⊗[k] skewZigzagQuotient k G c} :
    skewZigzagScalarExtensionEquiv G c x ∈
        skewZigzagGrade l G (c.map (algebraMap k l : k →* l)) n ↔
      x ∈ (skewZigzagGrade k G c n).baseChange l := by
  rw [← skewZigzagScalarExtensionEquiv_map_baseChange_skewZigzagGrade G c n,
    Submodule.mem_map_equiv]
  simp only [AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_apply_apply]

/-- The inverse scalar-extension comparison preserves path degree. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_symm_mem_baseChange_iff {n : ℕ}
    {x : skewZigzagQuotient l G (c.map (algebraMap k l : k →* l))} :
    (skewZigzagScalarExtensionEquiv G c).symm x ∈
        (skewZigzagGrade k G c n).baseChange l ↔
      x ∈ skewZigzagGrade l G (c.map (algebraMap k l : k →* l)) n := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (skewZigzagScalarExtensionEquiv_mem_skewZigzagGrade_iff G c
      (x := (skewZigzagScalarExtensionEquiv G c).symm x)).symm

end SimpleGraph
