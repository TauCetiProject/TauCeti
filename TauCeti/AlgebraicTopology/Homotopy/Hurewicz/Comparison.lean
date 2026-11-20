/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Isomorphism
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ULift
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# The cubical Hurewicz equivalence in singular homology

For an `(n + 1)`-connected pointed space, the cubical Hurewicz homomorphism in degree `n + 2`
is an additive equivalence.  The natural chain-homotopy equivalence between simplicial and
normalized cubical singular chains transports this to an equivalence with ordinary singular
homology (`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv` in `Type 0`, and
`HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv` in an arbitrary universe `u` through
`TopCat.singularHomologyUliftAddEquiv`).

The resulting equivalences are natural in based maps; so is the transported cubical Hurewicz map
itself, with no connectivity hypothesis
(`HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality`).  They supply the
degree-`n + 2` singular homology isomorphism, while
`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`,
`TauCeti.isZero_singularHomologyFunctor_ulift_of_subsingleton_homotopyGroup`,
`TauCeti.isZero_reducedSingularHomologyFunctor_of_subsingleton_homotopyGroup`, and
`TauCeti.isZero_reducedSingularHomologyFunctor_ulift_of_subsingleton_homotopyGroup` supply the
lower-degree singular and reduced homology vanishing in every universe.  The comparison here
retains the cubical Hurewicz map as its forward description.  The independently defined
relative-fundamental-class map `HomotopyGroup.hurewiczHom` agrees with it up to a universal sign
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`,
`HomotopyGroup.exists_hurewicz_ulift_eq_units_smul_cubicalHurewicz`), which gives the Hurewicz
theorem for `hurewiczHom` (`HomotopyGroup.hurewiczAddEquiv`,
`HomotopyGroup.hurewiczUliftAddEquiv`).

The inductive Hurewicz criteria
`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_singularChains`,
`TauCeti.subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift_of_le`, and
`TauCeti.subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift` show that a simply
connected space in any universe whose integral singular homology vanishes in degrees at least two
(up to `k`, or in every degree) has trivial homotopy groups in that range.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407--447.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.32.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u v w

namespace HomotopyGroup

open TauCeti

section Small

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

end Small

/-- The cubical Hurewicz class, transported to singular homology through the inverse
cubical--simplicial comparison, is natural in based maps, for coefficients in any ring `k` in the
same universe as the spaces. No connectivity hypothesis is needed. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ} (k : Type u) [Ring k]
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
theorem cubicalHurewiczSingularHomologyAddEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}
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

section Universe

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}

/-- **The cubical Hurewicz equivalence with ordinary singular homology in an arbitrary universe.**
If `πₖ(X, x)` is trivial for every `k < n + 2`, then `πₙ₊₂(X, x)` is additively equivalent to
degree-`n + 2` singular homology with universe-lifted integer coefficients
`ModuleCat.of ℤ (ULift.{u} ℤ)`. Its forward map is the cubical Hurewicz homomorphism over
`ULift.{u} ℤ`, transported through the inverse cubical--simplicial comparison and
`(TopCat.singularHomologyUliftAddEquiv ℤ (n + 2)).symm`. -/
def cubicalHurewiczSingularHomologyUliftAddEquiv
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X) :=
  ((cubicalHurewiczUliftAddEquiv hX).trans
      (singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.of X)
        (n + 2)).symm.toLinearEquiv.toAddEquiv).trans
    ((TopCat.of X).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm

/-- Explicit forward evaluation of `HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv`. -/
@[simp]
theorem cubicalHurewiczSingularHomologyUliftAddEquiv_apply
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    cubicalHurewiczSingularHomologyUliftAddEquiv hX a =
      ((TopCat.of X).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm
        ((singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.of X) (n + 2)).inv
          (cubicalHurewiczHom (ULift.{u} ℤ) (n + 1) a)) := by
  rw [cubicalHurewiczSingularHomologyUliftAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    cubicalHurewiczUliftAddEquiv_apply]
  rfl

/-- `HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv` is natural in based maps between
spaces in universe `u` satisfying the connectivity hypothesis. -/
theorem cubicalHurewiczSingularHomologyUliftAddEquiv_naturality
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y y))
    (f : C(X, Y)) (hf : f x = y)
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).map (TopCat.ofHom f)).hom
      (cubicalHurewiczSingularHomologyUliftAddEquiv hX a) =
      cubicalHurewiczSingularHomologyUliftAddEquiv hY
        (Additive.ofMul (HomotopyGroup.map f hf a.toMul)) := by
  rw [cubicalHurewiczSingularHomologyUliftAddEquiv_apply,
    cubicalHurewiczSingularHomologyUliftAddEquiv_apply,
    ← TopCat.singularHomologyUliftAddEquiv_symm_naturality.{u, 0} ℤ (TopCat.ofHom f) (n + 2),
    singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality (ULift.{u} ℤ) f hf a]

end Universe

end HomotopyGroup

namespace TauCeti

open HomotopyGroup

/-- **The singular homology with lifted ring coefficients of an `(n - 1)`-connected space vanishes
in the positive degrees below `n`.** For any ring `R : Type v` and space `X : TopCat.{max v u}`
with `πₖ(X, x)` trivial for every `k < n`, `Hₘ(X; ULift.{u} R) = 0` for `0 < m < n`. -/
theorem isZero_singularHomologyFunctor_ulift_of_subsingleton_homotopyGroup
    {X : TopCat.{max v u}} {n : ℕ} {x : X}
    (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
    (R : Type v) [Ring R] {m : ℕ} (hm0 : m ≠ 0) (hm : m < n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{max v u} R) m).obj
      (ModuleCat.of R (ULift.{u} R))).obj X) :=
  (X.isZero_singularHomology_ulift_iff R m).mpr
    (isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup hX (ULift.{u} R) hm0 hm)

private lemma isZero_reducedSingularHomologyFunctor_of_isZero_pos {C : Type*}
    [Category* C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C] [HasKernels C]
    {X : TopCat.{w}} {n : ℕ} {x : X}
    (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x)) (A : C)
    (hpos : ∀ m, m ≠ 0 → m < n → IsZero (((singularHomologyFunctor C m).obj A).obj X))
    {m : ℕ} (hm : m < n) :
    IsZero ((reducedSingularHomologyFunctor A m).obj X) := by
  cases m with
  | zero =>
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).mpr (hX 0 hm)
    exact isZero_reducedSingularHomologyFunctor_zero A X
  | succ m =>
    exact (hpos (m + 1) m.succ_ne_zero hm).of_iso ((reducedSingularHomologySuccIso A m).app X)

/-- **The reduced singular homology of an `(n - 1)`-connected space vanishes below `n`.** If
`πₖ(X, x)` is trivial for every `k < n`, then `H~ₘ(X; R) = 0` for every `m < n` and ring
`R : Type u`. -/
theorem isZero_reducedSingularHomologyFunctor_of_subsingleton_homotopyGroup
    {X : TopCat.{u}} {n : ℕ} {x : X}
    (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
    (R : Type u) [Ring R] {m : ℕ} (hm : m < n) :
    IsZero ((reducedSingularHomologyFunctor (ModuleCat.of R R) m).obj X) :=
  isZero_reducedSingularHomologyFunctor_of_isZero_pos hX (ModuleCat.of R R)
    (fun _ ↦ isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup hX R) hm

/-- **The reduced singular homology with lifted ring coefficients of an `(n - 1)`-connected space
vanishes below `n` in every universe.** For any ring `R : Type v` and space
`X : TopCat.{max v u}` with `πₖ(X, x)` trivial for every `k < n`,
`H~ₘ(X; ModuleCat.of R (ULift.{u} R)) = 0` for every `m < n`. When `R = ℤ`, this states that an
`(n - 1)`-connected pointed space in any universe `u` has vanishing reduced integral homology below
`n`. -/
theorem isZero_reducedSingularHomologyFunctor_ulift_of_subsingleton_homotopyGroup
    {X : TopCat.{max v u}} {n : ℕ} {x : X}
    (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
    (R : Type v) [Ring R] {m : ℕ} (hm : m < n) :
    IsZero ((reducedSingularHomologyFunctor (ModuleCat.of R (ULift.{u} R)) m).obj X) :=
  isZero_reducedSingularHomologyFunctor_of_isZero_pos hX (ModuleCat.of R (ULift.{u} R))
    (fun _ ↦ isZero_singularHomologyFunctor_ulift_of_subsingleton_homotopyGroup hX R) hm

/-- **Inductive Hurewicz vanishing criterion (singular homology).** If `X` is path connected with
trivial `π_ 1 X x` and its integral singular homology vanishes in every degree `n + 2`, then all
homotopy groups `π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_singularChains
    {X : Type} [TopologicalSpace X] (x : X)
    [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ, IsZero (((singularChains ℤ).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex x
    (fun n ↦ (hH n).of_iso (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).symm) k

/-- **Inductive Hurewicz vanishing criterion up to `k` (singular chains over `ULift.{u} ℤ`).** If
`X : Type u` is path connected with trivial `π_ 1 X x` and the homology of
`singularChains (ULift.{u} ℤ)` vanishes in every degree `n + 2 ≤ k`, then `π_ k X x` is trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_singularChains_ulift_of_le
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    {k : ℕ}
    (hH : ∀ n, n + 2 ≤ k →
      IsZero (((singularChains (ULift.{u} ℤ)).obj (TopCat.of X)).homology (n + 2))) :
    Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_normalizedCubicalChainComplex_ulift_of_le x
    fun n hn ↦ (hH n hn).of_iso
      (singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.of X) (n + 2)).symm

/-- **Inductive Hurewicz vanishing criterion (singular chains over `ULift.{u} ℤ`).** If
`X : Type u` is path connected with trivial `π_ 1 X x` and the homology of
`singularChains (ULift.{u} ℤ)` vanishes in every degree `n + 2`, then all homotopy groups
`π_ k X x` are trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_homology_singularChains_ulift
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ, IsZero (((singularChains (ULift.{u} ℤ)).obj (TopCat.of X)).homology (n + 2)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_singularChains_ulift_of_le x fun n _ ↦ hH n

/-- **Inductive Hurewicz vanishing criterion up to `k` (integral singular homology, arbitrary
universe).** If `X : Type u` is path connected with trivial `π_ 1 X x` and its integral singular
homology `H_{n+2}(X; ULift.{u} ℤ)` vanishes whenever `n + 2 ≤ k`, then `π_ k X x` is trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift_of_le
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    {k : ℕ}
    (hH : ∀ n, n + 2 ≤ k →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X))) :
    Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_homology_singularChains_ulift_of_le x
    fun n hn ↦ ((TopCat.of X).isZero_singularHomology_ulift_iff.{u, 0} ℤ (n + 2)).mp (hH n hn)

/-- **Inductive Hurewicz vanishing criterion (integral singular homology, arbitrary universe).** If
`X : Type u` is path connected with trivial `π_ 1 X x` and its integral singular homology
`H_{n+2}(X; ULift.{u} ℤ)` vanishes in every degree `n + 2`, then all homotopy groups `π_ k X x` are
trivial. -/
theorem subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift
    {X : Type u} [TopologicalSpace X] (x : X) [PathConnectedSpace X] [Subsingleton (π_ 1 X x)]
    (hH : ∀ n : ℕ,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)))
    (k : ℕ) : Subsingleton (π_ k X x) :=
  subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift_of_le x fun n _ ↦ hH n

end TauCeti
