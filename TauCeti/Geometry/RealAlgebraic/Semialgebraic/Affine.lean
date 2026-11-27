/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function

/-!
# Semialgebraicity of linear and affine subspaces

Over any linearly ordered field `K`, every linear subspace of a finite-dimensional coordinate space
`σ → K` is the kernel of a linear projection onto a complement, and every affine subspace is either
empty or a translate of its direction. Both are therefore semialgebraic without assuming projection
closure (`TauCeti.HasSemialgebraicProjections K`).

## Main results

* `Submodule.isSemialgebraic`: every linear subspace of `σ → K` (`Finite σ`) is semialgebraic.
* `AffineSubspace.isSemialgebraic`: every affine subspace of `σ → K` (`Finite σ`, possibly empty)
  is semialgebraic.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, §2.1.
-/

public section

open Set

section OrderedField

variable {σ K : Type*} [Field K] [LinearOrder K] [Finite σ]

/-- Every linear subspace `W` of `σ → K` (`Finite σ`) is semialgebraic, being the kernel of a
linear projection onto a complement. -/
theorem Submodule.isSemialgebraic (W : Submodule K (σ → K)) :
    TauCeti.IsSemialgebraic (W : Set (σ → K)) := by
  obtain ⟨Q, hWQ⟩ := W.exists_isCompl
  let π : (σ → K) →ₗ[K] (σ → K) := Q.subtype ∘ₗ Submodule.projectionOnto Q W hWQ.symm
  have hker : (W : Set (σ → K)) = π ⁻¹' {0} := by
    ext x
    simp [π, ← LinearMap.mem_ker]
  rw [hker]
  exact (TauCeti.isSemialgebraic_singleton (0 : σ → K)).preimage_affineMap π.toAffineMap

/-- Every affine subspace `A` of `σ → K` (`Finite σ`, possibly empty) is semialgebraic. -/
theorem AffineSubspace.isSemialgebraic (A : AffineSubspace K (σ → K)) :
    TauCeti.IsSemialgebraic (A : Set (σ → K)) := by
  rcases (A : Set (σ → K)).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · simp [h]
  · have htran : (A : Set (σ → K)) =
        (AffineEquiv.vaddConst K (-x₀)).toAffineMap ⁻¹' (A.direction : Set (σ → K)) := by
      ext x
      simp [← AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ x, vsub_eq_sub, sub_eq_add_neg]
    rw [htran]
    exact A.direction.isSemialgebraic.preimage_affineMap _

end OrderedField
