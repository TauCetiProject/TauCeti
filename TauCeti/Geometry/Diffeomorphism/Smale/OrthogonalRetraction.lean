/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Smale
public import TauCeti.Geometry.Diffeomorphism.Sphere.OrthogonalRetraction

/-!
# The Smale conjecture from the contractibility of a fibre

The orthogonal retraction `TauCeti.diffSphereToOrthogonal p hm : Diff(S³) → O(4)` splits `Diff(S³)`
as `O(4)` times its fibre over `1` (`TauCeti.diffSphereHomeomorphProd`). This file records the
resulting reduction of the pinned Smale conjecture `TauCeti.SmaleConjecture` to the
contractibility of that fibre, the first step of Hatcher's proof.

## Main results

* `TauCeti.smaleConjecture_of_contractibleSpace`: the Smale conjecture follows from the
  contractibility of the fibre over `1` of the orthogonal retraction.

## References

* A. Hatcher, *A proof of the Smale conjecture, Diff(S³) ≃ O(4)*, Ann. of Math. 117 (1983),
  553–607.
-/

public section

open Metric
open scoped Manifold ContDiff EuclideanSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-- **The Smale conjecture follows from the contractibility of the fibre of the orthogonal
retraction.** If, for some base point `p` of `S³`, the smooth diffeomorphisms of `S³` that the
orthogonal retraction sends to `1` form a contractible space, then the inclusion
`O(4) → Diff(S³)` is a homotopy equivalence. -/
theorem smaleConjecture_of_contractibleSpace (p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hp : ContractibleSpace {f : Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ //
      diffSphereToOrthogonal p (by norm_num) f = 1}) :
    SmaleConjecture := by
  have hm : (1 : ℕ∞ω) ≤ ∞ := by norm_num
  let e := orthogonalToDiffSphereHomotopyEquiv p hm
  refine smaleConjecture_iff_exists_homotopyInverse.mpr ⟨e.invFun, ?_, ?_⟩
  · rw [← orthogonalToDiffSphereHomotopyEquiv_toFun p hm]
    exact e.left_inv
  · rw [← orthogonalToDiffSphereHomotopyEquiv_toFun p hm]
    exact e.right_inv

end TauCeti
