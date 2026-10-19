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

The resulting equivalence is natural in based maps.  It supplies the degree-`n + 2` singular
homology isomorphism, while
`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup` supplies the positive
lower-degree vanishing.  The comparison here deliberately retains the cubical Hurewicz map as
its forward description; identifying it with the independently defined
relative-fundamental-class map `HomotopyGroup.hurewiczHom` requires a separate orientation
comparison for the cube generator.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407--447.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

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
  have hcomp :
      (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).inv ≫
          HomologicalComplex.homologyMap ((singularChains ℤ).map (TopCat.ofHom f)) (n + 2) =
        HomologicalComplex.homologyMap
            ((normalizedCubicalChainComplex ℤ).map (TopCat.ofHom f)) (n + 2) ≫
          (singularCubicalHomologyIso ℤ (TopCat.of Y) (n + 2)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact singularCubicalHomologyIso_hom_naturality (k := ℤ) (TopCat.ofHom f) (n + 2)
  rw [← ModuleCat.comp_apply, hcomp, ModuleCat.comp_apply,
    cubicalHurewiczHom_apply, cubicalHurewiczHom_apply]
  exact congrArg (singularCubicalHomologyIso ℤ (TopCat.of Y) (n + 2)).inv.hom
    (cubicalHurewicz_map ℤ (n + 1) f hf a.toMul).symm

end HomotopyGroup
