/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Isomorphism
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

/-!
# The cubical Hurewicz equivalence in singular homology

For an `(n + 1)`-connected pointed space, the cubical Hurewicz homomorphism in degree `n + 2`
is an additive equivalence.  The natural chain-homotopy equivalence between simplicial and
normalized cubical singular chains transports this to an equivalence with ordinary singular
homology (`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv`).

The resulting equivalence is natural in based maps; so is the transported cubical Hurewicz map
itself, with no connectivity hypothesis
(`HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality`).  It supplies the
degree-`n + 2` singular homology isomorphism, while
`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup` supplies the positive
lower-degree vanishing.  The comparison here retains the cubical Hurewicz map as its forward
description.  The independently defined relative-fundamental-class map
`HomotopyGroup.hurewiczHom` agrees with it up to a universal sign
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`), which gives the Hurewicz
theorem for `hurewiczHom` (`HomotopyGroup.hurewiczAddEquiv`).

The inductive Hurewicz criterion
`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_singularChains` shows that a simply
connected space with vanishing integral singular homology in degrees at least two has trivial
homotopy groups in every degree.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407--447.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.32.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace HomotopyGroup

open TauCeti

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} {n : ℕ}

/-- **The cubical Hurewicz equivalence with ordinary singular homology.** If
`πₖ(X, x)` is trivial for every `k < n + 2`, then `πₙ₊₂(X, x)` is additively equivalent to
degree-`n + 2` singular homology with integer coefficients.  Its forward map is the cubical
Hurewicz homomorphism followed by the inverse cubical--simplicial homology comparison. -/
def cubicalHurewiczSingularHomologyAddEquiv
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((singularChains ℤ).obj (TopCat.of X)).homology (n + 2) :=
  (cubicalHurewiczAddEquiv hX).trans
    (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).symm.toLinearEquiv.toAddEquiv

/-- The cubical Hurewicz equivalence with singular homology sends a homotopy class to its
cubical Hurewicz class, transported through the inverse cubical--simplicial comparison. -/
@[simp]
theorem cubicalHurewiczSingularHomologyAddEquiv_apply
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    cubicalHurewiczSingularHomologyAddEquiv hX a =
      (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).inv
        (cubicalHurewiczHom ℤ (n + 1) a) := by
  rw [cubicalHurewiczSingularHomologyAddEquiv, AddEquiv.trans_apply,
    cubicalHurewiczAddEquiv_apply]
  rfl

/-- The cubical Hurewicz class, transported to singular homology through the inverse
cubical--simplicial comparison, is natural in based maps, for coefficients in any ring `k`. No
connectivity hypothesis is needed. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality (k : Type) [Ring k]
    (f : C(X, Y)) (hf : f x = y) (a : Additive (HomotopyGroup (Fin (n + 1)) X x)) :
    HomologicalComplex.homologyMap ((singularChains k).map (TopCat.ofHom f)) (n + 1)
        ((singularCubicalHomologyIso k (TopCat.of X) (n + 1)).inv (cubicalHurewiczHom k n a)) =
      (singularCubicalHomologyIso k (TopCat.of Y) (n + 1)).inv
        (cubicalHurewiczHom k n (Additive.ofMul (HomotopyGroup.map f hf a.toMul))) := by
  have hcomp :
      (singularCubicalHomologyIso k (TopCat.of X) (n + 1)).inv ≫
          HomologicalComplex.homologyMap ((singularChains k).map (TopCat.ofHom f)) (n + 1) =
        HomologicalComplex.homologyMap
            ((normalizedCubicalChainComplex k).map (TopCat.ofHom f)) (n + 1) ≫
          (singularCubicalHomologyIso k (TopCat.of Y) (n + 1)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact singularCubicalHomologyIso_hom_naturality (k := k) (TopCat.ofHom f) (n + 1)
  rw [← ModuleCat.comp_apply, hcomp, ModuleCat.comp_apply,
    cubicalHurewiczHom_apply, cubicalHurewiczHom_apply]
  exact congrArg (singularCubicalHomologyIso k (TopCat.of Y) (n + 1)).inv.hom
    (cubicalHurewicz_map k n f hf a.toMul).symm

/-- The cubical Hurewicz equivalence with singular homology is natural in based maps between
spaces satisfying the connectivity hypothesis. -/
theorem cubicalHurewiczSingularHomologyAddEquiv_naturality
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y y))
    (f : C(X, Y)) (hf : f x = y)
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    HomologicalComplex.homologyMap ((singularChains ℤ).map (TopCat.ofHom f)) (n + 2)
        (cubicalHurewiczSingularHomologyAddEquiv hX a) =
      cubicalHurewiczSingularHomologyAddEquiv hY
        (Additive.ofMul (HomotopyGroup.map f hf a.toMul)) := by
  rw [cubicalHurewiczSingularHomologyAddEquiv_apply,
    cubicalHurewiczSingularHomologyAddEquiv_apply]
  exact singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality ℤ f hf a

end HomotopyGroup

namespace TauCeti

open HomotopyGroup

variable {X : Type} [TopologicalSpace X]

/-- **Inductive Hurewicz vanishing criterion (singular homology).** If `X` is path connected with
trivial `π_ 1 X x` and its integral singular homology vanishes in every degree `n + 2`, then all
homotopy groups `π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_singularChains (x : X)
    [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ, IsZero (((singularChains ℤ).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex x
    (fun n ↦ (hH n).of_iso (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).symm) k

end TauCeti
