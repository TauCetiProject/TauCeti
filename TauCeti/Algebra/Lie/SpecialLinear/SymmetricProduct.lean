/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.Matrix.TracelessAnticommutator

/-!
# The traceless symmetric product on the special linear Lie algebra

`Matrix.tracelessAnticommutator` is bilinear on all square matrices. When the size `n` is
a unit in the scalar ring, it maps pairs in `slₙ` into `slₙ`, giving the bilinear map
`symmetricProduct`. In size three, its trace transpose gives the symmetric octet embedding.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lectures 12 and 13.
* Jeromie Beasley, `yang-mills-lean`, `AdjointWitnessSU3.lean`, the commutator
  and anticommutator trace forms.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
  [Invertible (Fintype.card ι : K)]

/-- The symmetric product as a bilinear map on the trace-zero Lie algebra. -/
noncomputable def symmetricProduct :
    sl ι K →ₗ[K] sl ι K →ₗ[K] sl ι K :=
  LinearMap.mk₂ K (fun X Y => ⟨tracelessAnticommutator X.val Y.val,
    trace_tracelessAnticommutator X.val Y.val⟩)
    (fun X Y Z => Subtype.ext (tracelessAnticommutator_add_left X.val Y.val Z.val))
    (fun a X Y => Subtype.ext (tracelessAnticommutator_smul_left a X.val Y.val))
    (fun X Y Z => Subtype.ext (tracelessAnticommutator_add_right X.val Y.val Z.val))
    (fun a X Y => Subtype.ext (tracelessAnticommutator_smul_right a X.val Y.val))

/-- The underlying matrix is the trace-corrected anticommutator. -/
@[simp]
theorem coe_symmetricProduct (X Y : sl ι K) :
    (symmetricProduct X Y).val = tracelessAnticommutator X.val Y.val := by
  simp only [symmetricProduct, LinearMap.mk₂_apply]

/-- Exchanging the two traceless inputs preserves their symmetric product. -/
theorem symmetricProduct_comm (X Y : sl ι K) :
    symmetricProduct X Y = symmetricProduct Y X :=
  Subtype.ext (tracelessAnticommutator_comm _ _)

end LieAlgebra.SpecialLinear
