/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.FiberHomotopy
public import TauCeti.Topology.PathSpace.Moore.Pullback

/-!
# Relative chains of a pulled-back Moore path fibration

A continuous family of paths from `b` to `f d` trivializes the pullback of the based
Moore path fibration over `D` up to fibre homotopy. On normalized cubical chains this
gives a chain homotopy equivalence

`C_*(D × Ω_b X, S × Ω_b X; R) ≃ C_*(f*P_b X, (f*P_b X)|_S; R)`

for every subset `S` of `D`. The forward map appends the chosen path; the inverse
appends its reversal. The cube formulas below identify the actual relative chain maps.
Applying `FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv` to
`radialFiberHomotopyEquiv` supplies this comparison over a characteristic disk,
relative to its boundary, using radial paths from its centre.

The comparison is of complexes of coefficient modules. The product side retains its
loop coordinates and carries no loop-module structure here.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential
  graded coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open CategoryTheory ContinuousMap

namespace TauCeti.MoorePathPullback

universe u

variable {D X : Type u} [TopologicalSpace D] [TopologicalSpace X]
  {f : C(D, X)} {b : X}
  (τ : C(D, MoorePath X)) (h₀ : ∀ d, (τ d).source = b)
  (h₁ : ∀ d, (τ d).target = f d) (S : Set D) (R : Type u) [Ring R]

/-- Appending a continuous family of paths gives a chain homotopy equivalence relative to
any subset of the parameter space.

The carrier-specialized wrapper supports the cube simp lemmas below: on the generic term,
the hom/inv simp rules fire before the conversion of the pair's ambient-space wrapper. -/
def relativeChainHomotopyEquiv :
    _root_.HomotopyEquiv
      ((TopPair.ofSubset (X := TopCat.of (D × MooreLoopSpace X b))
        ((ContinuousMap.fst : C(D × MooreLoopSpace X b, D)) ⁻¹' S)).cubicalChainComplex R)
      ((TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b))
        ((proj f b) ⁻¹' S)).cubicalChainComplex R) :=
  (fiberHomotopyEquiv τ h₀ h₁).relativeCubicalChainHomotopyEquiv S R

/-- The forward comparison sends a relative cube to the cube obtained by appending `τ`.
This formula includes cubes meeting the relative subspace. -/
@[simp]
theorem relativeChainHomotopyEquiv_hom_f_cubicalChainOfCube {n : ℕ}
    (σ : SingularCube (D × MooreLoopSpace X b) n) :
    (relativeChainHomotopyEquiv τ h₀ h₁ S R).hom.f n
        (TopPair.cubicalChainOfCube R σ) =
      TopPair.cubicalChainOfCube R
        (P := TopPair.ofSubset (X := TopCat.of (MoorePathPullback f b)) ((proj f b) ⁻¹' S))
        ((trivializationMap τ h₀ h₁).comp σ) := by
  rw [relativeChainHomotopyEquiv, FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_hom]
  have h := TopPair.cubicalChainComplexMap_f_cubicalChainOfCube R
    ((fiberHomotopyEquiv τ h₀ h₁).preimagePairMap S) σ
  simp only [FiberHomotopyEquiv.preimagePairMap_fst, fiberHomotopyEquiv_toFun] at h
  -- The cube lemma uses the ambient space of a pair, while `σ` uses the product carrier.
  -- Converting compares the same compact-open map across those wrappers.
  convert h using 1
  congr 1

/-- The inverse comparison sends a relative cube to the cube obtained by appending the
reversed chosen paths, retaining the parameter and the resulting loop. -/
@[simp]
theorem relativeChainHomotopyEquiv_inv_f_cubicalChainOfCube {n : ℕ}
    (σ : SingularCube (MoorePathPullback f b) n) :
    (relativeChainHomotopyEquiv τ h₀ h₁ S R).inv.f n
        (TopPair.cubicalChainOfCube R σ) =
      TopPair.cubicalChainOfCube R
        (P := TopPair.ofSubset (X := TopCat.of (D × MooreLoopSpace X b))
          ((ContinuousMap.fst : C(D × MooreLoopSpace X b, D)) ⁻¹' S))
        ((trivializationInverse τ h₀ h₁).comp σ) := by
  rw [relativeChainHomotopyEquiv, FiberHomotopyEquiv.relativeCubicalChainHomotopyEquiv_inv]
  have h := TopPair.cubicalChainComplexMap_f_cubicalChainOfCube R
    ((fiberHomotopyEquiv τ h₀ h₁).symm.preimagePairMap S) σ
  simp only [FiberHomotopyEquiv.preimagePairMap_fst, FiberHomotopyEquiv.symm_toFun,
    fiberHomotopyEquiv_invFun] at h
  -- As above, only the ambient-space wrapper of the pair differs.
  convert h using 1
  congr 1

end TauCeti.MoorePathPullback
