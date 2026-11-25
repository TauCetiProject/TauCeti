/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Comparison
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator

import TauCeti.Algebra.Ring.Parity

/-!
# The coordinate cube class

The positive ordered triangulation `TauCeti.SingularCube.orderedChain` of the identity cube of
`Iⁿ` is a relative singular cycle of the pair `(Iⁿ, ∂Iⁿ)`. With integer coefficients it is the
`n`-fold iterated shuffle product of the interval chain `t ↦ t` taken in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`), so its class is the coordinate-oriented
fundamental class of the cube. This file computes that class: it is `(-1) ^ (n (n + 1) / 2)` times
the selected generator `TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ(Iⁿ, ∂Iⁿ; k)`, over
every ring `k` (`TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`). In
particular it generates `Hₙ(Iⁿ, ∂Iⁿ; k)` (`TauCeti.bijective_smul_coordinateCubeClass`), and in
dimension one it is the class of `t ↦ t`, whose boundary is `[1] - [0]`
(`TauCeti.coordinateCubeClass_zero`).

The computation compares the triangulation with the acyclic-models comparison
`TauCeti.cubicalToSingular`, whose value on the identity cube is calibrated in
`TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator`: by
`TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube` the coordinate cube class
is `(-1) ^ n` times the image of the cubical class of the identity cube.

## Main definitions

* `TauCeti.coordinateCubeClass k m`: the coordinate cube class in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`.

## Main results

* `TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`: the coordinate of the
  cube class is `(-1) ^ ((m + 1) (m + 2) / 2)`.
* `TauCeti.bijective_smul_coordinateCubeClass`: the coordinate cube class generates.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Proposition 3B.1 and the relative cross product after
  Theorem 3B.6.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-! ### The coordinate cube class -/

/-- The **coordinate cube class** `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`: the class of the
positive ordered triangulation of the identity cube, the signed sum over the coordinate orderings
of the simplices from the origin to the far vertex. With integer coefficients its chain is the
iterated shuffle product of the interval chain `t ↦ t` in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`). -/
def coordinateCubeClass (m : ℕ) :
    (cubeBoundaryPair.{u} (m + 1)).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k)
      (m + 1) :=
  ((cubeBoundaryPair.{u} (m + 1)).singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
    (TopPair.orderedCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)))

theorem coordinateCubeClass_def (m : ℕ) :
    coordinateCubeClass k m =
      ((cubeBoundaryPair.{u} (m + 1)).singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
        (TopPair.orderedCycleOfCube k
          (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
          (mapsTo_upCube_boundary (m + 1))) :=
  (rfl)

/-- The coordinate cube class is `(-1) ^ (m + 1)` times the cubical class of the identity cube. -/
theorem coordinateCubeClass_eq_neg_one_pow_smul (m : ℕ) :
    coordinateCubeClass k m =
      (-1 : k) ^ (m + 1) • (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (m + 1))
        (m + 1)).inv (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) := by
  have hz : cubeBoundaryPairCycle k m = TopPair.cubicalCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)) :=
    HomologicalComplex.moduleCat_iCycles_injective _ (m + 1)
      ((iCycles_cubeBoundaryPairCycle k m).trans (TopPair.iCycles_cubicalCycleOfCube ..).symm)
  have h := congrArg ((-1 : k) ^ (m + 1) • ·)
    (TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube (k := k)
      (P := cubeBoundaryPair.{u} (m + 1)) _ (mapsTo_upCube_boundary (m + 1)))
  rw [hz]
  -- The ambient space of the cube pair is the cube model only up to unfolding `Arrow.mk`, so the
  -- relative formula is combined with equations rather than rewritten.
  exact (h.trans ((smul_smul _ _ _).trans
    ((congrArg (fun a : k ↦ a • coordinateCubeClass k m)
      (neg_one_pow_mul_neg_one_pow (m + 1))).trans (one_smul k _)))).symm

/-- **The coordinate of the cube class**: under `TauCeti.singularHomologyCubeBoundaryPairIso`, the
coordinate cube class of `Iⁿ`, `n = m + 1`, is `(-1) ^ (n (n + 1) / 2)`. -/
theorem singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) := by
  rw [coordinateCubeClass_eq_neg_one_pow_smul, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle, smul_eq_mul, ← pow_add]
  congr 1
  have h : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- The selected generator of `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)` is `(-1) ^ ((m + 1) (m + 2) / 2)` times the
coordinate cube class. -/
theorem singularHomologyCubeBoundaryPairIso_inv_apply_one (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).inv (1 : k) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) • coordinateCubeClass k m := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom).1 inferInstance
  rw [ModuleCat.hom_inv_apply, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, smul_eq_mul,
    neg_one_pow_mul_neg_one_pow]

/-- **The coordinate cube class generates**: `a ↦ a • [Iᵐ⁺¹, ∂Iᵐ⁺¹]` is a bijection from `k` onto
`Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`. -/
theorem bijective_smul_coordinateCubeClass (m : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateCubeClass k m := by
  set e := singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)
  set ε : k := (-1) ^ ((m + 1) * (m + 2) / 2)
  have hε : ε * ε = 1 := neg_one_pow_mul_neg_one_pow _
  have he : ∀ a : k, e.hom (a • coordinateCubeClass k m) = a * ε := fun a ↦ by
    rw [map_smul, singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, smul_eq_mul]
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ⟨e.hom z * ε, ?_⟩⟩
  · have h := congrArg (· * ε) ((he a).symm.trans ((congrArg e.hom hab).trans (he b)))
    simpa only [mul_assoc, hε, mul_one] using h
  · apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    rw [he, mul_assoc, hε, mul_one]

/-- In dimension one the coordinate cube class is the class of the singular simplex `t ↦ t`, whose
boundary is `[1] - [0]` (`TauCeti.cubeRelClass_singularHomologyδ`). -/
theorem coordinateCubeClass_zero :
    coordinateCubeClass k 0 = (cubeRelClass.{u} (ModuleCat.of k k)).hom (1 : k) := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom).1 inferInstance
  have h := congrArg (fun φ ↦ ((singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom)
    (φ.hom (1 : k))) (singularHomologyCubeBoundaryPairIso_one_inv (ModuleCat.of k k))
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg] at h
  rw [singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, ← neg_eq_iff_eq_neg.2 h]
  norm_num

end TauCeti
