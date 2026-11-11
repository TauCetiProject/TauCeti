/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal change of basis over a star algebra

Mapping an orthonormal change-of-basis matrix into a star algebra preserves both
conjugate-transpose inverse identities, even for bases with different finite index types.
These identities allow orthonormal changes of coordinates for matrices with coefficients
in a possibly noncommutative star algebra.
-/

public section

open scoped Matrix

namespace OrthonormalBasis

variable {𝕜 A M ι κ : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
  [Fintype ι] [Fintype κ]

/-- After mapping into a star algebra, the conjugate transpose of an orthonormal
change-of-basis matrix is still a left inverse. -/
@[simp]
theorem toMatrix_map_conjTranspose_mul_self [DecidableEq κ]
    (b : OrthonormalBasis ι 𝕜 M) (c : OrthonormalBasis κ 𝕜 M) :
    ((b.toBasis.toMatrix c).map (algebraMap 𝕜 A))ᴴ *
      (b.toBasis.toMatrix c).map (algebraMap 𝕜 A) = 1 := by
  classical
  rw [← Matrix.conjTranspose_map _ algebraMap_star_comm, ← Matrix.map_mul,
    b.toMatrix_orthonormalBasis_conjTranspose_mul_self c]
  simp

/-- After mapping into a star algebra, the conjugate transpose of an orthonormal
change-of-basis matrix is still a right inverse. -/
@[simp]
theorem toMatrix_map_self_mul_conjTranspose [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 M) (c : OrthonormalBasis κ 𝕜 M) :
    (b.toBasis.toMatrix c).map (algebraMap 𝕜 A) *
      ((b.toBasis.toMatrix c).map (algebraMap 𝕜 A))ᴴ = 1 := by
  classical
  rw [← Matrix.conjTranspose_map _ algebraMap_star_comm, ← Matrix.map_mul,
    b.toMatrix_orthonormalBasis_self_mul_conjTranspose c]
  simp

end OrthonormalBasis
