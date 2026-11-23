/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.Matrix.TracelessAnticommutator
import TauCeti.Data.Fintype.Fin

/-!
# The traceless symmetric product on the adjoint representation of SLₙ

`Matrix.tracelessAnticommutator` is bilinear on all square matrices. When the size `n` is
nonzero in the field, it maps pairs in `slₙ` into `slₙ`, giving the bilinear map
`symmetricProduct`. In size three, its trace transpose gives the symmetric octet embedding.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lectures 12 and 13.
* Jeromie Beasley, `yang-mills-lean`, `AdjointWitnessSU3.lean`, the commutator
  and anticommutator trace forms.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] TauCeti.neZero_card_fin

/-- The symmetric product as a bilinear map on Mathlib's actual trace-zero Lie algebra. -/
def symmetricProduct [NeZero (n : K)] :
    LieAlgebra.SpecialLinear.sl (Fin n) K →ₗ[K]
      LieAlgebra.SpecialLinear.sl (Fin n) K →ₗ[K]
        LieAlgebra.SpecialLinear.sl (Fin n) K :=
  LinearMap.mk₂ K (fun X Y => ⟨tracelessAnticommutator X.val Y.val,
    trace_tracelessAnticommutator X.val Y.val⟩)
    (fun X Y Z => Subtype.ext (tracelessAnticommutator_add_left X.val Y.val Z.val))
    (fun a X Y => Subtype.ext (tracelessAnticommutator_smul_left a X.val Y.val))
    (fun X Y Z => Subtype.ext (tracelessAnticommutator_add_right X.val Y.val Z.val))
    (fun a X Y => Subtype.ext (tracelessAnticommutator_smul_right a X.val Y.val))

/-- The bilinear map has the advertised matrix formula. -/
@[simp]
theorem coe_symmetricProduct [NeZero (n : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    (symmetricProduct X Y).val = tracelessAnticommutator X.val Y.val := by
  simp only [symmetricProduct, LinearMap.mk₂_apply]

/-- Symmetry holds on the native adjoint carrier. -/
theorem symmetricProduct_comm [NeZero (n : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    symmetricProduct X Y = symmetricProduct Y X :=
  Subtype.ext (tracelessAnticommutator_comm _ _)

end TauCeti.AdjointSquare
