/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Equiv.Int
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# The higher homotopy groups of real projective space

The antipodal quotient `mk n : Sⁿ → RPⁿ` is a covering map
(`TauCeti.RealProjectiveSpace.isCoveringMap_mk`), so it induces isomorphisms
`π_k(Sⁿ, e) ≃* π_k(RPⁿ, mk n e)` for every `k ≥ 2` (`IsCoveringMap.homotopyGroupPiMulEquiv`).
Through the connectivity of spheres and `πₙ(Sⁿ) ≅ ℤ` this gives, for `n ≥ 2`:

* `π_k(RPⁿ)` is trivial for `2 ≤ k < n`;
* `πₙ(RPⁿ) ≅ ℤ`.

Hence, by the general facts on groups isomorphic to `ℤ`
(`TauCeti.not_isMulTorsion_of_addEquiv_int` and `TauCeti.not_surjective_pow_of_addEquiv_int`),
`πₙ(RPⁿ)` is not a torsion group, no power map `a ↦ a ^ d` with `d ≠ 1` is surjective on it, and
`RPⁿ` is not aspherical. Squaring not being surjective on `πₙ(RPⁿ)` is the hypothesis of
Theorems 5.15 and C of Barraud, Damian, Humilière and Oancea on closed characteristics in cotangent
bundles, for the non-orientable `RPⁿ` with `n` even. Their hypothesis for Theorem 5.10 and
Theorem A is verified for `RPⁿ` in the module
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.RealProjectiveSpace`.

For `n = 2` the first nontrivial higher group is `π₂(RP²) ≅ ℤ`; for `n = 4` it is `π₄(RP⁴) ≅ ℤ`.

## Main definitions

* `TauCeti.RealProjectiveSpace.homotopyGroupAddEquiv`: `πₙ(RPⁿ, mk n e) ≅ ℤ` for `n ≥ 2`.

## Main results

* `TauCeti.RealProjectiveSpace.subsingleton_homotopyGroup_of_lt`: `π_k(RPⁿ)` is trivial for
  `2 ≤ k < n`.
* `TauCeti.RealProjectiveSpace.nontrivial_homotopyGroup`: `πₙ(RPⁿ)` is nontrivial for `n ≥ 2`.
* `TauCeti.RealProjectiveSpace.not_isMulTorsion_homotopyGroup`: `πₙ(RPⁿ)` is not a torsion group.
* `TauCeti.RealProjectiveSpace.not_surjective_pow_homotopyGroup`: `a ↦ a ^ d` is not surjective on
  `πₙ(RPⁿ)` for `d ≠ 1`.
* `TauCeti.RealProjectiveSpace.not_isAspherical`: `RPⁿ` is not aspherical for `n ≥ 2`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.1 (covering
  spaces and higher homotopy groups) and Corollary 4.25 (`πₙ(Sⁿ) ≅ ℤ`).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorems 5.15 and C.
-/

public section

noncomputable section

open Metric Module
open scoped Topology Topology.Homotopy

namespace TauCeti

namespace RealProjectiveSpace

variable (n : ℕ)

/-- **The homotopy groups of `RPⁿ` vanish strictly between `1` and `n`.** The homotopy group
`π_k(RPⁿ, x)` is trivial for `2 ≤ k < n`, since the antipodal covering identifies it with
`π_k(Sⁿ)`. -/
theorem subsingleton_homotopyGroup_of_lt {k : ℕ} (hk : k + 2 < n) (x : RealProjectiveSpace n) :
    Subsingleton (π_ (k + 2) (RealProjectiveSpace n) x) := by
  obtain ⟨e, rfl⟩ := mk_surjective n x
  have := subsingleton_homotopyGroup_sphere_of_lt
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)) (N := Fin (k + 2))
    (by simpa using hk) e
  exact ((isCoveringMap_mk n).homotopyGroupPiMulEquiv e k).symm.toEquiv.subsingleton

/-- **The `n`-th homotopy group of `RPⁿ` is `ℤ`** for `n ≥ 2`: the antipodal covering identifies
`π_{n+2}(RP^{n+2}, mk e)` with `π_{n+2}(S^{n+2}, e)`, which is `ℤ` through the Hurewicz isomorphism
and the standard orientation of `S^{n+2}` (`TauCeti.homotopyGroupSphereAddEquiv`). -/
def homotopyGroupAddEquiv (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) :
    Additive (π_ (n + 2) (RealProjectiveSpace (n + 2)) (mk (n + 2) e)) ≃+ ℤ :=
  ((isCoveringMap_mk (n + 2)).homotopyGroupPiMulEquiv e n).symm.toAdditive.trans
    (homotopyGroupSphereAddEquiv (EuclideanSpace.basisFun (Fin (n + 2 + 1)) ℝ) e)

/-- `TauCeti.RealProjectiveSpace.homotopyGroupAddEquiv` lifts a class along the antipodal covering
and evaluates the lift by `TauCeti.homotopyGroupSphereAddEquiv`. -/
theorem homotopyGroupAddEquiv_apply (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1)
    (a : Additive (π_ (n + 2) (RealProjectiveSpace (n + 2)) (mk (n + 2) e))) :
    homotopyGroupAddEquiv n e a =
      homotopyGroupSphereAddEquiv (EuclideanSpace.basisFun (Fin (n + 2 + 1)) ℝ) e
        (Additive.ofMul (((isCoveringMap_mk (n + 2)).homotopyGroupPiMulEquiv e n).symm
          a.toMul)) :=
  (rfl)

/-- **`πₙ(RPⁿ)` is not a torsion group** for `n ≥ 2`, since it is `ℤ`. -/
theorem not_isMulTorsion_homotopyGroup (x : RealProjectiveSpace (n + 2)) :
    ¬ IsMulTorsion (π_ (n + 2) (RealProjectiveSpace (n + 2)) x) := by
  obtain ⟨e, rfl⟩ := mk_surjective (n + 2) x
  exact not_isMulTorsion_of_addEquiv_int (homotopyGroupAddEquiv n e)

/-- **`πₙ(RPⁿ)` is nontrivial** for `n ≥ 2`, since it is `ℤ`. -/
theorem nontrivial_homotopyGroup (x : RealProjectiveSpace (n + 2)) :
    Nontrivial (π_ (n + 2) (RealProjectiveSpace (n + 2)) x) := by
  obtain ⟨e, rfl⟩ := mk_surjective (n + 2) x
  exact (Additive.ofMul.trans (homotopyGroupAddEquiv n e).toEquiv).nontrivial

/-- **No power map other than the identity is surjective on `πₙ(RPⁿ)`** for `n ≥ 2`, since
`πₙ(RPⁿ) ≅ ℤ` and `1` is not a multiple of `d ≠ 1`. For `d = 2` this says that `πₙ(RPⁿ) ⊗ ℤ/2` is
nonzero. -/
theorem not_surjective_pow_homotopyGroup (x : RealProjectiveSpace (n + 2)) {d : ℕ} (hd : d ≠ 1) :
    ¬ Function.Surjective fun a : π_ (n + 2) (RealProjectiveSpace (n + 2)) x ↦ a ^ d := by
  obtain ⟨e, rfl⟩ := mk_surjective (n + 2) x
  exact not_surjective_pow_of_addEquiv_int (homotopyGroupAddEquiv n e) hd

/-- **Real projective space `RPⁿ` is not aspherical** for `n ≥ 2`: its `n`-th homotopy group is
`ℤ`. -/
theorem not_isAspherical (x : RealProjectiveSpace (n + 2)) :
    ¬ IsAspherical (RealProjectiveSpace (n + 2)) x := fun h ↦
  have := nontrivial_homotopyGroup n x
  not_subsingleton _ ((isAspherical_iff.1 h).2 n)

end RealProjectiveSpace

end TauCeti
