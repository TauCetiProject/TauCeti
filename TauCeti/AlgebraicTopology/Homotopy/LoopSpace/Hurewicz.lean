/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup

/-!
# Hurewicz isomorphisms for loop spaces

Let `(X, x)` be a pointed space whose homotopy groups `π_1, …, π_{n+2}` at `x` vanish. Then the
loop space `ΩX` is `(n + 1)`-connected, since `π_k(ΩX) ≅ π_{k+1}(X)` in every degree `k`,
including `k = 0`. The Hurewicz theorem for `ΩX` and the loop-space shift therefore identify

`H_{n+2}(ΩX; ℤ) ≅ π_{n+3}(X, x)`.

Applying this to the loop space, if `π_2, …, π_{n+3}` vanish at `x` (no condition on `π_1`), then

`H_{n+2}(Ω²X; ℤ) ≅ π_{n+4}(X, x)`,

so the first nonvanishing higher homotopy group `π_k(X, x)`, `k ≥ 4`, is the homology of the
double loop space in degree `k - 2`. The case `k = 3` is degree-one Hurewicz
(`TauCeti.MooreLoopSpace.doubleFirstHomologyAddEquiv`). This is the homological input for
detecting higher homotopy groups through double loop spaces.

Both the fixed-interval loop spaces `Ω X x` and the Moore loop spaces `MooreLoopSpace X x` are
treated; for the latter the double-loop identification is also stated for normalized cubical
chains. The Hurewicz isomorphism used is the cubical one
(`HomotopyGroup.cubicalHurewiczAddEquiv`), transported to simplicial singular homology by the
cubical–simplicial comparison.

## Main definitions

* `TauCeti.pathLoopSpaceHomologyAddEquiv`: `π_{n+3}(X, x) ≅ H_{n+2}(ΩX; ℤ)`.
* `TauCeti.doubleLoopSpaceHomologyAddEquiv`: `π_{n+4}(X, x) ≅ H_{n+2}(Ω²X; ℤ)`.
* `TauCeti.MooreLoopSpace.homologyAddEquiv` and `TauCeti.MooreLoopSpace.doubleHomologyAddEquiv`:
  the same for Moore loops.
* `TauCeti.MooreLoopSpace.doubleCubicalHomologyAddEquiv`: `π_{n+4}(X, x)` is the normalized
  cubical homology `H_{n+2}(ΩᴹΩᴹX; ℤ)`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.32 and §4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Propositions 5.11 and 6.21.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy
open AlgebraicTopology HomotopyGroup

namespace TauCeti

variable {X : Type} [TopologicalSpace X]

/-! ### Fixed-interval loops -/

/-- **Hurewicz for loop spaces.** If `π_{k+1}(X, x)` vanishes for every `k < n + 2`, then the
integral homology of the loop space `Ω X x` in degree `n + 2` is
`H_{n+2}(ΩX; ℤ) ≅ π_{n+3}(X, x)`. -/
def pathLoopSpaceHomologyAddEquiv (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 1) X x)) :
    Additive (π_ (n + 3) X x) ≃+ ((singularChains ℤ).obj (TopCat.of (Ω X x))).homology (n + 2) :=
  (pathLoopSpaceMulEquiv (n + 1)).symm.toAdditive.trans
    (cubicalHurewiczSingularHomologyAddEquiv fun k hk ↦
      (subsingleton_homotopyGroup_loopSpace_iff x k).mpr (hX k hk))

/-- `TauCeti.pathLoopSpaceHomologyAddEquiv` is the inverse loop-space shift followed by the
Hurewicz isomorphism of the loop space. -/
theorem pathLoopSpaceHomologyAddEquiv_apply (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 1) X x)) (a : Additive (π_ (n + 3) X x)) :
    pathLoopSpaceHomologyAddEquiv x n hX a =
      cubicalHurewiczSingularHomologyAddEquiv
        (fun k hk ↦ (subsingleton_homotopyGroup_loopSpace_iff x k).mpr (hX k hk))
        (Additive.ofMul ((pathLoopSpaceMulEquiv (n + 1)).symm a.toMul)) :=
  (rfl)

/-- **Hurewicz for double loop spaces.** If `π_{k+2}(X, x)` vanishes for every `k < n + 2`, then
the integral homology of the double loop space `Ω (Ω X x) (Path.refl x)` in degree `n + 2` is
`H_{n+2}(Ω²X; ℤ) ≅ π_{n+4}(X, x)`. -/
def doubleLoopSpaceHomologyAddEquiv (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) :
    Additive (π_ (n + 4) X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (Ω (Ω X x) (Path.refl x)))).homology (n + 2) :=
  (pathLoopSpaceMulEquiv (n + 2)).symm.toAdditive.trans
    (pathLoopSpaceHomologyAddEquiv (Path.refl x) n fun k hk ↦
      (pathLoopSpaceMulEquiv (X := X) (x := x) k).toEquiv.subsingleton_congr.mpr (hX k hk))

/-- `TauCeti.doubleLoopSpaceHomologyAddEquiv` is the inverse loop-space shift followed by the
Hurewicz identification for the loop space `Ω X x`. -/
theorem doubleLoopSpaceHomologyAddEquiv_apply (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) (a : Additive (π_ (n + 4) X x)) :
    doubleLoopSpaceHomologyAddEquiv x n hX a =
      pathLoopSpaceHomologyAddEquiv (Path.refl x) n
        (fun k hk ↦
          (pathLoopSpaceMulEquiv (X := X) (x := x) k).toEquiv.subsingleton_congr.mpr (hX k hk))
        (Additive.ofMul ((pathLoopSpaceMulEquiv (n + 2)).symm a.toMul)) :=
  (rfl)

/-! ### Moore loops -/

namespace MooreLoopSpace

/-- **Hurewicz for Moore loop spaces.** If `π_{k+1}(X, x)` vanishes for every `k < n + 2`, then
the integral homology of the Moore loop space in degree `n + 2` is
`H_{n+2}(ΩᴹX; ℤ) ≅ π_{n+3}(X, x)`. -/
def homologyAddEquiv (x : X) (n : ℕ) (hX : ∀ k < n + 2, Subsingleton (π_ (k + 1) X x)) :
    Additive (π_ (n + 3) X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace X x))).homology (n + 2) :=
  (homotopyGroupMulEquiv x (n + 1)).symm.toAdditive.trans
    (cubicalHurewiczSingularHomologyAddEquiv fun k hk ↦
      (subsingleton_homotopyGroup_iff x k).mpr (hX k hk))

/-- `TauCeti.MooreLoopSpace.homologyAddEquiv` is the inverse Moore loop-space shift followed by
the Hurewicz isomorphism of the Moore loop space. -/
theorem homologyAddEquiv_apply (x : X) (n : ℕ) (hX : ∀ k < n + 2, Subsingleton (π_ (k + 1) X x))
    (a : Additive (π_ (n + 3) X x)) :
    homologyAddEquiv x n hX a =
      cubicalHurewiczSingularHomologyAddEquiv
        (fun k hk ↦ (subsingleton_homotopyGroup_iff x k).mpr (hX k hk))
        (Additive.ofMul ((homotopyGroupMulEquiv x (n + 1)).symm a.toMul)) :=
  (rfl)

/-- **Hurewicz for double Moore loop spaces.** If `π_{k+2}(X, x)` vanishes for every `k < n + 2`,
then the integral homology of the double Moore loop space in degree `n + 2` is
`H_{n+2}(ΩᴹΩᴹX; ℤ) ≅ π_{n+4}(X, x)`. -/
def doubleHomologyAddEquiv (x : X) (n : ℕ) (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) :
    Additive (π_ (n + 4) X x) ≃+
      ((singularChains ℤ).obj (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology
        (n + 2) :=
  (homotopyGroupMulEquiv x (n + 2)).symm.toAdditive.trans
    (homologyAddEquiv (1 : MooreLoopSpace X x) n fun k hk ↦
      (homotopyGroupMulEquiv x k).toEquiv.subsingleton_congr.mpr (hX k hk))

/-- `TauCeti.MooreLoopSpace.doubleHomologyAddEquiv` is the inverse Moore loop-space shift followed
by the Hurewicz identification for the Moore loop space. -/
theorem doubleHomologyAddEquiv_apply (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) (a : Additive (π_ (n + 4) X x)) :
    doubleHomologyAddEquiv x n hX a =
      homologyAddEquiv (1 : MooreLoopSpace X x) n
        (fun k hk ↦ (homotopyGroupMulEquiv x k).toEquiv.subsingleton_congr.mpr (hX k hk))
        (Additive.ofMul ((homotopyGroupMulEquiv x (n + 2)).symm a.toMul)) :=
  (rfl)

/-- With normalized cubical chains: if `π_{k+2}(X, x)` vanishes for every `k < n + 2`, then
`H_{n+2}(ΩᴹΩᴹX; ℤ) ≅ π_{n+4}(X, x)`, through `TauCeti.singularCubicalHomologyIso`. -/
def doubleCubicalHomologyAddEquiv (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) :
    Additive (π_ (n + 4) X x) ≃+
      ((normalizedCubicalChainComplex ℤ).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1))).homology (n + 2) :=
  let e := singularCubicalHomologyIso ℤ (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)) (n + 2)
  (doubleHomologyAddEquiv x n hX).trans e.toLinearEquiv.toAddEquiv

/-- The cubical identification is the singular one followed by the homology map of the named
singular-to-cubical comparison. -/
theorem doubleCubicalHomologyAddEquiv_apply (x : X) (n : ℕ)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) X x)) (a : Additive (π_ (n + 4) X x)) :
    doubleCubicalHomologyAddEquiv x n hX a =
      (HomologicalComplex.homologyMap
        ((singularToCubical ℤ).app (TopCat.of (MooreLoopSpace (MooreLoopSpace X x) 1)))
          (n + 2)).hom (doubleHomologyAddEquiv x n hX a) := by
  simp only [doubleCubicalHomologyAddEquiv, AddEquiv.trans_apply]
  rw [← singularCubicalHomologyIso_hom]
  rfl

end MooreLoopSpace

end TauCeti
