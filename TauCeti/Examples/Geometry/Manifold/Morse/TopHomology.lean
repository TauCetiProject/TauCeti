/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Cellular.RealProjective.Cohomology
import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.Geometry.Manifold.Morse.TopHomology

/-!
# Examples: integral cohomology in the degree of the largest Morse index

If every critical point of a Morse function on a compact boundaryless manifold `M` has index at
most `d`, then `H_d(M; ℤ)` is free abelian
(`TauCeti.IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`) and the integral
cohomology of `M` vanishes above degree `d`
(`TauCeti.IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le`). This file
checks on real projective space that `Hᵈ(M; ℤ)` itself need not be torsion-free.

Let `N = n + 1` with `n` odd, so that `N ≥ 2` is even, and let `f` be the moment function
`[x] ↦ (∑ i, i * x i ^ 2) / ∑ i, x i ^ 2` on the `N`-manifold `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`
(`TauCeti.projectiveMomentFunction` with the standard weights). It is a Morse function, and every
critical point has index at most `N`, the dimension. So `H_N(ℝℙᴺ; ℤ)` is free (it is `0`) and the
integral cohomology vanishes above degree `N`. Yet `H^N(ℝℙᴺ; ℤ) ≅ ℤ/2`, which is not torsion-free:
by the universal coefficient theorem it is `Ext¹(H_{N-1}(ℝℙᴺ; ℤ), ℤ) = Ext¹(ℤ/2, ℤ)`
(`TauCeti.RealProjectiveSpace.singularCohomologySuccIntLinearEquivOfOdd`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
-/

open AlgebraicTopology CategoryTheory Limits Module
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {n : ℕ}

-- The moment function on `ℝℙⁿ⁺¹` with the standard weights is a Morse function, and every
-- critical point has index at most the dimension `n + 1`.
example : IsMorse 𝓘(ℝ, Fin (n + 1) → ℝ)
      (projectiveMomentFunction ℝ fun i : Fin (n + 2) ↦ ((i : ℕ) : ℝ)) ∧
    ∀ x ∈ criticalPoints 𝓘(ℝ, Fin (n + 1) → ℝ)
      (projectiveMomentFunction ℝ fun i : Fin (n + 2) ↦ ((i : ℕ) : ℝ)),
      manifoldMorseIndex 𝓘(ℝ, Fin (n + 1) → ℝ)
        (projectiveMomentFunction ℝ fun i : Fin (n + 2) ↦ ((i : ℕ) : ℝ)) x ≤ n + 1 :=
  ⟨isMorse_projectiveMomentFunction_natCast, fun _ _ ↦
    manifoldMorseIndex_le_finrank.trans (Module.finrank_fin_fun ℝ).le⟩

-- So the integral homology of `ℝℙⁿ⁺¹` in degree `n + 1` is free abelian ...
example : Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin (n + 2) → ℝ)))) :=
  IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le
    isMorse_projectiveMomentFunction_natCast
    (fun _ _ ↦ manifoldMorseIndex_le_finrank.trans (Module.finrank_fin_fun ℝ).le) _

-- ... and its integral cohomology vanishes above degree `n + 1`.
example {m : ℕ} (hm : n + 1 < m) :
    IsZero ((TopCat.of (ℙ ℝ (Fin (n + 2) → ℝ))).singularCohomology (ModuleCat.of ℤ ℤ) ℤ
      (ModuleCat.of ℤ ℤ) m) :=
  IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le
    isMorse_projectiveMomentFunction_natCast
    (fun _ _ ↦ manifoldMorseIndex_le_finrank.trans (Module.finrank_fin_fun ℝ).le) _ _ hm

open RealProjectiveSpace

-- For odd `n`, the integral cohomology of `ℝℙⁿ⁺¹` in the top degree `n + 1` is `ℤ/2` ...
example (hn : Odd n) :
    Nonempty ((TopCat.of (ℙ ℝ (Fin (n + 2) → ℝ))).singularCohomology (ModuleCat.of ℤ ℤ) ℤ
      (ModuleCat.of ℤ ℤ) (n + 1) ≃ₗ[ℤ] ZMod 2) :=
  ⟨((homeomorphProjectivization (n + 1)).toHomotopyEquiv.singularCohomologyIso
    (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) (n + 1)).toLinearEquiv ≪≫ₗ
      singularCohomologySuccIntLinearEquivOfOdd hn (lt_add_one n)⟩

-- ... so it is not torsion-free.
example (hn : Odd n) :
    ¬ IsAddTorsionFree ((TopCat.of (ℙ ℝ (Fin (n + 2) → ℝ))).singularCohomology
      (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) (n + 1)) := fun _ ↦ by
  let e := ((homeomorphProjectivization (n + 1)).toHomotopyEquiv.singularCohomologyIso
    (ModuleCat.of ℤ ℤ) ℤ (ModuleCat.of ℤ ℤ) (n + 1)).toLinearEquiv.symm
  exact not_isAddTorsionFree_singularCohomology_succ_int hn (lt_add_one n)
    (e.injective.isAddTorsionFree e.toLinearMap.toAddMonoidHom)

end TauCeti
