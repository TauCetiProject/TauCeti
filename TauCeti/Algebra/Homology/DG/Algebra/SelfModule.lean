/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Defs

/-!
# A differential graded algebra as a module over itself

The multiplication of a differential graded algebra `(𝒜, d)` is the action of its carrier on
itself, and the graded Leibniz rule of `TauCeti.IsDGAlgebra` is the one of
`TauCeti.IsDGLeftModule` read through `smul_eq_mul`.  So a differential graded algebra is a
differential graded left module over itself, `TauCeti.IsDGAlgebra.isDGLeftModule`, and every
consequence of the module axioms specializes to the algebra.

This file records those specializations: the differential commutes with the homogeneous
projections of the grading up to the shift of degrees by one, the Leibniz rule extends from a
homogeneous left factor to an arbitrary one as soon as the right factor is a cycle, a product of
cycles is a cycle, and a cycle times a boundary is a boundary.  Each is a one-line instance of the
corresponding statement about a differential graded left module, which is why they live here
rather than in `TauCeti.Algebra.Homology.DG.Algebra.Defs`: the module interface is defined in
terms of the algebra axioms, so only a file downstream of it can specialize its consequences.

## Main results

* `TauCeti.IsDGAlgebra.map_proj`: the differential commutes with the homogeneous projections of
  the grading, `d (proj p a) = proj (p + 1) (d a)`; in particular the homogeneous components of a
  cycle are cycles and those of a boundary are boundaries.
* `TauCeti.IsDGAlgebra.leibniz_of_map_right_eq_zero`: the Leibniz rule for an arbitrary left
  factor against a cycle.
* `TauCeti.IsDGAlgebra.mul_map_mem_range_of_map_left_eq_zero`: a cycle times a boundary is a
  boundary; a boundary times a cycle is one by the previous item.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace IsDGAlgebra

/-- The differential commutes with the homogeneous projections of the grading, up to the shift by
one that it applies to degrees. -/
theorem map_proj (h : IsDGAlgebra 𝒜 d) (p : ℤ) (a : A) :
    d (GradedRing.proj 𝒜 p a) = GradedRing.proj 𝒜 (p + 1) (d a) := by
  simpa only [GradedRing.proj_apply] using h.isDGLeftModule.map_decompose p a

/-- Every homogeneous projection of a boundary is again a boundary. -/
theorem proj_mem_range (h : IsDGAlgebra 𝒜 d) {a : A} (ha : a ∈ LinearMap.range d) (p : ℤ) :
    GradedRing.proj 𝒜 p a ∈ LinearMap.range d := by
  simpa only [GradedRing.proj_apply] using h.isDGLeftModule.decompose_mem_range ha p

/-- The homogeneous components of a cycle are cycles. -/
theorem map_proj_eq_zero (h : IsDGAlgebra 𝒜 d) {a : A} (ha : d a = 0) (p : ℤ) :
    d (GradedRing.proj 𝒜 p a) = 0 := by
  simpa only [GradedRing.proj_apply] using h.isDGLeftModule.map_decompose_eq_zero ha p

/-- The Leibniz rule against a cycle on the right: the sign disappears with the term it multiplies,
so the left factor need not be homogeneous. -/
theorem leibniz_of_map_right_eq_zero (h : IsDGAlgebra 𝒜 d) (a : A) {b : A} (hb : d b = 0) :
    d (a * b) = d a * b := by
  simpa only [smul_eq_mul] using h.isDGLeftModule.leibniz_of_map_eq_zero a hb

/-- The product of two cycles is a cycle. -/
theorem map_mul_eq_zero_of_map_eq_zero (h : IsDGAlgebra 𝒜 d) {a b : A}
    (ha : d a = 0) (hb : d b = 0) :
    d (a * b) = 0 := by
  simpa only [smul_eq_mul] using h.isDGLeftModule.map_smul_eq_zero_of_map_eq_zero ha hb

/-- A homogeneous cycle times a boundary is, up to the sign of the cycle's degree, the
differential of the product. -/
theorem mul_map_eq_negOnePow_smul_map_mul (h : IsDGAlgebra 𝒜 d) {p : ℤ} {a : A}
    (ha : a ∈ 𝒜 p) (hda : d a = 0) (b : A) :
    a * d b = p.negOnePow • d (a * b) := by
  simpa only [smul_eq_mul] using h.isDGLeftModule.smul_map_eq_negOnePow_smul_map_smul ha hda b

/-- A cycle times a boundary is a boundary.  Componentwise this is the Leibniz rule read backwards:
`x * d b = (-1) ^ |x| * d (x * b)` when `x` is a homogeneous cycle. -/
theorem mul_map_mem_range_of_map_left_eq_zero (h : IsDGAlgebra 𝒜 d) {a : A}
    (ha : d a = 0) (b : A) :
    a * d b ∈ LinearMap.range d := by
  simpa only [smul_eq_mul] using
    h.isDGLeftModule.smul_mem_range_of_map_eq_zero ha (LinearMap.mem_range_self d b)

end IsDGAlgebra

end TauCeti
