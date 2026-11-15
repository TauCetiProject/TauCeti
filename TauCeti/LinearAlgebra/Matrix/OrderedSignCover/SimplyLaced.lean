/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover

/-!
# The ordered sign cover of a simply laced lattice

For a symmetric simply laced Gram matrix `B` (`Matrix.IsSimplyLaced`), such as the Cartan matrix
of a simply laced Dynkin diagram, the off-diagonal entries are `0` or `-1`, the negative of the
number of bonds. The canonical section `a ↦ (a, 1)` of the ordered sign cover `Matrix.SignCover B`
is a homomorphism exactly when every strictly lower entry of `B` is even
(`Matrix.forall_canonicalSection_signFactorSet_mul_iff`), so here exactly when the diagram has no
bonds.

This is kept apart from `TauCeti.LinearAlgebra.Matrix.OrderedSignCover` so that the general cover
does not import the theory of Cartan matrices.

## Main results

* `Matrix.forall_canonicalSection_signFactorSet_mul_iff_of_isSimplyLaced`: for a symmetric simply
  laced `B`, the section `a ↦ (a, 1)` is a homomorphism exactly when `B` is diagonal.
-/

public section

namespace Matrix

open TauCeti

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)

attribute [local instance] trivialMulDistribMulAction

/-- **For a simply laced Gram matrix, the canonical section of the ordered sign cover is a
homomorphism exactly when the diagram has no bonds.** Here `B` is symmetric and simply laced, with
off-diagonal entries `0` or `-1`, the negative of the number of bonds, as for the Cartan matrix of a
simply laced Dynkin diagram. -/
theorem forall_canonicalSection_signFactorSet_mul_iff_of_isSimplyLaced (hB : B.IsSymm)
    (hsl : B.IsSimplyLaced) :
    (∀ a b : Multiplicative (I → ℤ), (signFactorSet B).canonicalSection (a * b) =
        (signFactorSet B).canonicalSection a * (signFactorSet B).canonicalSection b) ↔
      ∀ i j, i ≠ j → B i j = 0 := by
  rw [forall_canonicalSection_signFactorSet_mul_iff]
  refine ⟨fun h i j hij => ?_, fun h i j hji => by simp [h i j hji.ne']⟩
  have key : ∀ i j, j < i → B i j = 0 := fun i j hji =>
    ((isSimplyLaced_iff_of_linearOrder B hB).1 hsl hji).resolve_right fun h' => by
      simpa [h'] using h i j hji
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [← hB.apply]
    exact key j i hlt
  · exact key i j hlt

end Matrix
