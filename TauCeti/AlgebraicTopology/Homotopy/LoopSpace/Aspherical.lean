/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology

/-!
# Acyclicity of loop spaces and aspherical spaces

For a pointed space `(X, x)`, the loop-space shift identifies `πₖ(ΩX)` with `πₖ₊₁(X, x)` in every
degree `k ≥ 0`, and therefore identifies `πₖ(Ω²X)` with `πₖ₊₂(X, x)`. Combined with Eilenberg's
based-cube retraction
(`TauCeti.isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup`) and the
higher cubical Hurewicz isomorphism (`HomotopyGroup.cubicalHurewiczAddEquiv` and
`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv`), this yields the homological
characterization of vanishing higher homotopy groups:

* A loop space `ΩX` (or `ΩᴹX`) is path connected with vanishing positive-degree integral homology
  if and only if `πₙ₊₁(X, x)` is trivial for every `n : ℕ`.
* A double loop space `Ω²X` (or `ΩᴹΩᴹX`) is path connected with vanishing positive-degree integral
  homology if and only if `πₙ₊₂(X, x)` is trivial for every `n : ℕ`.
* In particular, when `X` is path connected, `Ω²X` (or `ΩᴹΩᴹX`) has the integral homology of a
  point if and only if `X` is aspherical (`TauCeti.IsAspherical`), i.e., an Eilenberg--Mac Lane
  space `K(π₁(X, x), 1)` (`TauCeti.IsEilenbergMacLaneSpaceOne`). In the forward direction, the
  positive-degree homology of `Ω²X` and `ΩᴹΩᴹX` vanishes with coefficients in any ring.

Both the fixed-interval and Moore loop-space models, as well as simplicial singular chains and
normalized cubical chains, are treated.

The arbitrary-ring vanishing results allow `X : Type u` and `R : Type u`. The integral-homology
characterizations use `X : Type`: the chain functors `singularChains` and
`normalizedCubicalChainComplex` share the universe of the space and coefficient ring, so their
specializations to `ℤ` take small spaces. The Hurewicz equivalences used here have the same scope.

## Main results

* `TauCeti.isZero_homology_normalizedCubicalChainComplex_doubleLoopSpace`,
  `TauCeti.isZero_homology_singularChains_doubleLoopSpace`,
  `TauCeti.MooreLoopSpace.isZero_homology_normalizedCubicalChainComplex_double`,
  `TauCeti.MooreLoopSpace.isZero_homology_singularChains_double`: vanishing of the positive-degree
  homology of `Ω²X` and `ΩᴹΩᴹX` over any coefficient ring when `πₙ₊₂(X, x)` vanishes for all `n`.
* `TauCeti.pathConnectedSpace_doubleLoopSpace_and_forall_isZero_homology_singularChains_iff`,
  `TauCeti.MooreLoopSpace.pathConnectedSpace_double_and_forall_isZero_homology_singularChains_iff`:
  `Ω²X` and `ΩᴹΩᴹX` have the integral homology of a point if and only if `πₙ₊₂(X, x)` vanishes for
  all `n`.
* `TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`,
  `TauCeti.isAspherical_iff_doubleLoopSpace_cubicalHomology`,
  `TauCeti.MooreLoopSpace.isAspherical_iff_double_singularHomology`,
  `TauCeti.MooreLoopSpace.isAspherical_iff_double_cubicalHomology`:
  for path-connected `X`, `Ω²X` and `ΩᴹΩᴹX` have the integral homology of a point if and only if
  `X` is aspherical / a `K(π₁(X, x), 1)` (Barraud--Damian--Humilière--Oancea, Lemma 3.41).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 3.41.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.1 and Theorem 4.32.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy

namespace TauCeti

universe u

section ArbitraryRing

variable {X : Type u} [TopologicalSpace X] (R : Type u) [Ring R]

/-! ### Vanishing of positive-degree homology over an arbitrary coefficient ring -/

/-- If `π_ (n + 1) X x` vanishes for all `n : ℕ`, then the positive-degree normalized cubical
homology of `Ω X x` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_normalizedCubicalChainComplex_loopSpace {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((normalizedCubicalChainComplex R).obj (TopCat.of (Ω X x))).homology m) :=
  isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup
    (x := Path.refl x)
    (fun k _ ↦ (forall_subsingleton_homotopyGroup_loopSpace_iff x).mpr hX k) R hm0
    (Nat.lt_succ_self m)

/-- If `π_ (n + 1) X x` vanishes for all `n : ℕ`, then the positive-degree singular homology of
`Ω X x` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_singularChains_loopSpace {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((singularChains R).obj (TopCat.of (Ω X x))).homology m) :=
  (isZero_homology_normalizedCubicalChainComplex_loopSpace R hX hm0).of_iso
    (singularCubicalHomologyIso R (TopCat.of (Ω X x)) m)

/-- If `π_ (n + 2) X x` vanishes for all `n : ℕ`, then the positive-degree normalized cubical
homology of `Ω (Ω X x) (Path.refl x)` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_normalizedCubicalChainComplex_doubleLoopSpace {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((normalizedCubicalChainComplex R).obj
      (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m) :=
  isZero_homology_normalizedCubicalChainComplex_loopSpace R
    (fun n ↦ (pathLoopSpaceMulEquiv (X := X) (x := x) n).toEquiv.subsingleton_congr.mpr (hX n)) hm0

/-- If `π_ (n + 2) X x` vanishes for all `n : ℕ`, then the positive-degree singular homology of
`Ω (Ω X x) (Path.refl x)` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_singularChains_doubleLoopSpace {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((singularChains R).obj (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m) :=
  (isZero_homology_normalizedCubicalChainComplex_doubleLoopSpace R hX hm0).of_iso
    (singularCubicalHomologyIso R (TopCat.of (Ω (Ω X x) (Path.refl x))) m)

namespace MooreLoopSpace

/-- If `π_ (n + 1) X x` vanishes for all `n : ℕ`, then the positive-degree normalized cubical
homology of `MooreLoopSpace X x` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_normalizedCubicalChainComplex {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))).homology m) :=
  isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup
    (x := (1 : MooreLoopSpace X x))
    (fun k _ ↦ (forall_subsingleton_homotopyGroup_iff x).mpr hX k) R hm0 (Nat.lt_succ_self m)

/-- If `π_ (n + 1) X x` vanishes for all `n : ℕ`, then the positive-degree singular homology of
`MooreLoopSpace X x` vanishes over any coefficient ring `R`. -/
theorem isZero_homology_singularChains {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 1) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((singularChains R).obj (TopCat.of (MooreLoopSpace X x))).homology m) :=
  (isZero_homology_normalizedCubicalChainComplex R hX hm0).of_iso
    (singularCubicalHomologyIso R (TopCat.of (MooreLoopSpace X x)) m)

/-- If `π_ (n + 2) X x` vanishes for all `n : ℕ`, then the positive-degree normalized cubical
homology of the double Moore loop space vanishes over any coefficient ring `R`. -/
theorem isZero_homology_normalizedCubicalChainComplex_double {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((normalizedCubicalChainComplex R).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m) :=
  isZero_homology_normalizedCubicalChainComplex R
    (fun n ↦ (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr.mpr (hX n)) hm0

/-- If `π_ (n + 2) X x` vanishes for all `n : ℕ`, then the positive-degree singular homology of
the double Moore loop space vanishes over any coefficient ring `R`. -/
theorem isZero_homology_singularChains_double {x : X}
    (hX : ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)) {m : ℕ} (hm0 : m ≠ 0) :
    IsZero (((singularChains R).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m) :=
  (isZero_homology_normalizedCubicalChainComplex_double R hX hm0).of_iso
    (singularCubicalHomologyIso R (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) m)

end MooreLoopSpace

end ArbitraryRing

/-! ### Homological characterization via the Hurewicz isomorphism -/

section IntegralHomology

variable {X : Type} [TopologicalSpace X]

/-- The fixed-interval loop space `Ω X x` is path connected with vanishing positive-degree integral
singular homology if and only if `π_ (n + 1) X x` is trivial for every `n : ℕ`. -/
theorem pathConnectedSpace_loopSpace_and_forall_isZero_homology_singularChains_iff (x : X) :
    (PathConnectedSpace (Ω X x) ∧
        ∀ m ≠ 0, IsZero (((singularChains ℤ).obj (TopCat.of (Ω X x))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) := by
  constructor
  · rintro ⟨hpc, hH⟩
    let hHomology : Subsingleton (((singularChains ℤ).obj (TopCat.of (Ω X x))).homology 1) :=
      ModuleCat.subsingleton_of_isZero (hH 1 one_ne_zero)
    let hPiTwo : Subsingleton (π_ 2 X x) :=
      (Additive.ofMul.trans
        (pathLoopSpaceFirstHomologyAddEquiv x).toEquiv).subsingleton_congr.mpr hHomology
    let hLoopPiOne : Subsingleton (π_ 1 (Ω X x) (Path.refl x)) :=
      (pathLoopSpaceMulEquiv (X := X) (x := x) 0).toEquiv.subsingleton_congr.mpr hPiTwo
    exact (forall_subsingleton_homotopyGroup_loopSpace_iff x).mp
      (subsingleton_homotopyGroup_of_isZero_homology_singularChains (Path.refl x)
        fun n ↦ hH (n + 2) (Nat.succ_ne_zero _))
  · intro hX
    exact ⟨(pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).mpr (hX 0),
      fun _ hm0 ↦ isZero_homology_singularChains_loopSpace ℤ hX hm0⟩

/-- The fixed-interval loop space `Ω X x` is path connected with vanishing positive-degree integral
normalized cubical homology if and only if `π_ (n + 1) X x` is trivial for every `n : ℕ`. -/
theorem pathConnectedSpace_loopSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff
    (x : X) :
    (PathConnectedSpace (Ω X x) ∧
        ∀ m ≠ 0,
          IsZero (((normalizedCubicalChainComplex ℤ).obj (TopCat.of (Ω X x))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) := by
  rw [← pathConnectedSpace_loopSpace_and_forall_isZero_homology_singularChains_iff x]
  refine and_congr_right' (forall_congr' fun m ↦ imp_congr_right fun _ ↦ ?_)
  exact (singularCubicalHomologyIso ℤ (TopCat.of (Ω X x)) m).isZero_iff.symm

/-- The fixed-interval double loop space `Ω (Ω X x) (Path.refl x)` is path connected with vanishing
positive-degree integral singular homology if and only if `π_ (n + 2) X x` is trivial for every
`n : ℕ`. -/
theorem pathConnectedSpace_doubleLoopSpace_and_forall_isZero_homology_singularChains_iff (x : X) :
    (PathConnectedSpace (Ω (Ω X x) (Path.refl x)) ∧
        ∀ m ≠ 0,
          IsZero (((singularChains ℤ).obj (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (pathConnectedSpace_loopSpace_and_forall_isZero_homology_singularChains_iff (Path.refl x)).trans
    (forall_congr' fun n ↦
      (pathLoopSpaceMulEquiv (X := X) (x := x) n).toEquiv.subsingleton_congr)

/-- The fixed-interval double loop space `Ω (Ω X x) (Path.refl x)` is path connected with vanishing
positive-degree integral normalized cubical homology if and only if `π_ (n + 2) X x` is trivial for
every `n : ℕ`. -/
theorem
    pathConnectedSpace_doubleLoopSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff
    (x : X) :
    (PathConnectedSpace (Ω (Ω X x) (Path.refl x)) ∧
        ∀ m ≠ 0, IsZero (((normalizedCubicalChainComplex ℤ).obj
          (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (pathConnectedSpace_loopSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff
    (Path.refl x)).trans
    (forall_congr' fun n ↦
      (pathLoopSpaceMulEquiv (X := X) (x := x) n).toEquiv.subsingleton_congr)

/-- **Barraud--Damian--Humilière--Oancea, Lemma 3.41 (fixed-interval singular homology).** A
path-connected space `X` is aspherical if and only if its double loop space
`Ω (Ω X x) (Path.refl x)` is path connected with vanishing positive-degree integral singular
homology. -/
theorem isAspherical_iff_doubleLoopSpace_singularHomology (x : X) [PathConnectedSpace X] :
    IsAspherical X x ↔
      PathConnectedSpace (Ω (Ω X x) (Path.refl x)) ∧
        ∀ m ≠ 0,
          IsZero (((singularChains ℤ).obj (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m) := by
  rw [isAspherical_iff,
    pathConnectedSpace_doubleLoopSpace_and_forall_isZero_homology_singularChains_iff]
  exact and_iff_right inferInstance

/-- **Barraud--Damian--Humilière--Oancea, Lemma 3.41 (fixed-interval cubical homology).** A
path-connected space `X` is aspherical if and only if its double loop space
`Ω (Ω X x) (Path.refl x)` is path connected with vanishing positive-degree integral normalized
cubical homology. -/
theorem isAspherical_iff_doubleLoopSpace_cubicalHomology (x : X) [PathConnectedSpace X] :
    IsAspherical X x ↔
      PathConnectedSpace (Ω (Ω X x) (Path.refl x)) ∧
        ∀ m ≠ 0, IsZero (((normalizedCubicalChainComplex ℤ).obj
          (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology m) := by
  rw [isAspherical_iff,
    pathConnectedSpace_doubleLoopSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff]
  exact and_iff_right inferInstance

namespace MooreLoopSpace

/-- The Moore loop space `MooreLoopSpace X x` is path connected with vanishing positive-degree
integral singular homology if and only if `π_ (n + 1) X x` is trivial for every `n : ℕ`. -/
theorem pathConnectedSpace_and_forall_isZero_homology_singularChains_iff (x : X) :
    (PathConnectedSpace (MooreLoopSpace X x) ∧
        ∀ m ≠ 0, IsZero (((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) := by
  rw [← pathConnectedSpace_loopSpace_and_forall_isZero_homology_singularChains_iff x]
  refine and_congr
    ((pathConnectedSpace_iff_subsingleton_pi1 x).trans
      (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).symm)
    (forall_congr' fun m ↦ imp_congr_right fun _ ↦ ?_)
  exact ((homotopyEquivPath x).singularHomologyIso (ModuleCat.of ℤ ℤ) m).isZero_iff

/-- The Moore loop space `MooreLoopSpace X x` is path connected with vanishing positive-degree
integral normalized cubical homology if and only if `π_ (n + 1) X x` is trivial for every
`n : ℕ`. -/
theorem pathConnectedSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff (x : X) :
    (PathConnectedSpace (MooreLoopSpace X x) ∧
        ∀ m ≠ 0, IsZero (((normalizedCubicalChainComplex ℤ).obj
          (TopCat.of (MooreLoopSpace X x))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 1) X x) := by
  rw [← pathConnectedSpace_and_forall_isZero_homology_singularChains_iff x]
  refine and_congr_right' (forall_congr' fun m ↦ imp_congr_right fun _ ↦ ?_)
  exact (singularCubicalHomologyIso ℤ (TopCat.of (MooreLoopSpace X x)) m).isZero_iff.symm

/-- The double Moore loop space `MooreLoopSpace (MooreLoopSpace X x) 1` is path connected with
vanishing positive-degree integral singular homology if and only if `π_ (n + 2) X x` is trivial for
every `n : ℕ`. -/
theorem pathConnectedSpace_double_and_forall_isZero_homology_singularChains_iff (x : X) :
    (PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) ∧
        ∀ m ≠ 0, IsZero (((singularChains ℤ).obj
          (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (pathConnectedSpace_and_forall_isZero_homology_singularChains_iff
    (1 : MooreLoopSpace X x)).trans
    (forall_congr' fun n ↦ (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr)

/-- The double Moore loop space `MooreLoopSpace (MooreLoopSpace X x) 1` is path connected with
vanishing positive-degree integral normalized cubical homology if and only if `π_ (n + 2) X x` is
trivial for every `n : ℕ`. -/
theorem pathConnectedSpace_double_and_forall_isZero_homology_normalizedCubicalChainComplex_iff
    (x : X) :
    (PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) ∧
        ∀ m ≠ 0, IsZero (((normalizedCubicalChainComplex ℤ).obj
          (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m)) ↔
      ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  (pathConnectedSpace_and_forall_isZero_homology_normalizedCubicalChainComplex_iff
    (1 : MooreLoopSpace X x)).trans
    (forall_congr' fun n ↦ (homotopyGroupMulEquiv x n).toEquiv.subsingleton_congr)

/-- **Barraud--Damian--Humilière--Oancea, Lemma 3.41 (Moore singular homology).** A path-connected
space `X` is aspherical if and only if its double Moore loop space is path connected with vanishing
positive-degree integral singular homology. -/
theorem isAspherical_iff_double_singularHomology (x : X) [PathConnectedSpace X] :
    IsAspherical X x ↔
      PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) ∧
        ∀ m ≠ 0, IsZero (((singularChains ℤ).obj
          (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m) := by
  rw [isAspherical_iff, pathConnectedSpace_double_and_forall_isZero_homology_singularChains_iff]
  exact and_iff_right inferInstance

/-- **Barraud--Damian--Humilière--Oancea, Lemma 3.41 (Moore cubical homology).** A path-connected
space `X` is aspherical if and only if its double Moore loop space is path connected with vanishing
positive-degree integral normalized cubical homology. -/
theorem isAspherical_iff_double_cubicalHomology (x : X) [PathConnectedSpace X] :
    IsAspherical X x ↔
      PathConnectedSpace (MooreLoopSpace (MooreLoopSpace X x) 1) ∧
        ∀ m ≠ 0, IsZero (((normalizedCubicalChainComplex ℤ).obj
          (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology m) := by
  rw [isAspherical_iff,
    pathConnectedSpace_double_and_forall_isZero_homology_normalizedCubicalChainComplex_iff]
  exact and_iff_right inferInstance

end MooreLoopSpace

end IntegralHomology

end TauCeti
