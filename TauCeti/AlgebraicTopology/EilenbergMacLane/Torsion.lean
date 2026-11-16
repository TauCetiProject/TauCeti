/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.AlgebraicTopology.SerreClass.SubmonoidTorsion
public import TauCeti.AlgebraicTopology.Singular.Coefficients.Flat
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.Singular.Fibration.AcyclicFiber

/-!
# Acyclicity and torsion homology of Eilenberg--Mac Lane spaces `K(A, n)`

If `A` is an abelian group and `R` is a commutative ring in which the additive order of every
element of `A` is a unit, then `H_{k + 1}(K(A, n + 1); R) = 0` for all `n, k : ℕ`. The proof
inducts on `n`: the base case `n = 0` reduces via `K(A, 1)` to group homology
(`TauCeti.subsingleton_groupHomology_of_forall_isUnit_addOrderOf`), and the inductive step uses
`Ω K(A, n + 2) ≃ K(A, n + 1)` and path-fibration acyclicity transfer
(`TauCeti.subsingleton_singularHomology_of_loopSpace`). Combining this with flat base change to a
localization of `ℤ` at a submonoid `S` verifies Serre's `K(A, n + 1)` property for `S`-torsion
(and in particular for torsion abelian groups over `ℚ`).

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`:
  `H_{k + 1}(K(A, n + 1); R) = 0` whenever every element order of `A` is a unit in `R`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`:
  `H_{k + 1}(K(A, n + 1); R) = 0` for an `S`-torsion abelian group `A` and a localization `R` of
  `ℤ` at `S`.
* `TauCeti.IsEilenbergMacLaneSpace.isTorsion'_singularHomology`,
  `TauCeti.IsEilenbergMacLaneSpace.isSubmonoidTorsion_singularHomology`:
  if `A` is `S`-torsion, then `H_{k + 1}(K(A, n + 1); ℤ)` is `S`-torsion.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_rat`,
  `TauCeti.IsEilenbergMacLaneSpace.isAddTorsion_singularHomology`,
  `TauCeti.IsEilenbergMacLaneSpace.isTorsion_singularHomology`:
  if `A` is torsion, then `H_{k + 1}(K(A, n + 1); ℚ) = 0` and `H_{k + 1}(K(A, n + 1); ℤ)` is
  torsion.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I, §3, and Chapter II, Proposition 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2--4.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

namespace IsEilenbergMacLaneSpace

/-- **Acyclicity of `K(A, n + 1)` when element orders of `A` are invertible in `R`.** For every
abelian group `A`, every commutative ring `R` in which `addOrderOf a` is a unit for all `a : A`,
and every Eilenberg--Mac Lane space `(X, x)` of type `K(A, n + 1)`, the positive-degree singular
homology `H_{k + 1}(X; R)` vanishes. -/
theorem subsingleton_singularHomology_of_forall_isUnit_addOrderOf
    {A : Type u} [AddCommGroup A] {n : ℕ} {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    (R : Type u) [CommRing R] (hA : ∀ a : A, IsUnit (addOrderOf a : R)) (k : ℕ) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (k + 1)) := by
  induction n generalizing X x k with
  | zero =>
    have := subsingleton_groupHomology_of_forall_isUnit_addOrderOf R hA k
    exact ((isEilenbergMacLaneSpace_one_iff.1 hX).nonempty_singularHomologyIsoGroupHomology R
      (k + 1)).some.toLinearEquiv.toEquiv.subsingleton
  | succ n ih =>
    have := hX.pathConnectedSpace
    have := hX.loopSpace.pathConnectedSpace
    refine subsingleton_singularHomology_of_loopSpace x R k fun q hq1 _ ↦ ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq1)
    exact ih hX.loopSpace j

/-- **Acyclicity of `K(A, n + 1)` over a localization `R` of `ℤ` at `S` when `A` is
`S`-torsion.** -/
theorem subsingleton_singularHomology_of_isTorsion'
    {A : Type} [AddCommGroup A] {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    {S : Submonoid ℤ} (hA : Module.IsTorsion' A S)
    (R : Type) [CommRing R] [Algebra ℤ R] [IsLocalization S R] (k : ℕ) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (k + 1)) :=
  hX.subsingleton_singularHomology_of_forall_isUnit_addOrderOf R
    (S.isUnit_addOrderOf_of_isTorsion' R hA) k

/-- Multiplicative-group variant of
`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`, for a commutative
group `G` whose additive counterpart `Additive G` is `S`-torsion (such as a higher homotopy group
`π_{m + 2}(Z, z)`). -/
theorem subsingleton_singularHomology_of_isTorsion'_additive
    {G : Type} [CommGroup G] {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace G (n + 1) X x)
    {S : Submonoid ℤ} (hG : Module.IsTorsion' (Additive G) S)
    (R : Type) [CommRing R] [Algebra ℤ R] [IsLocalization S R] (k : ℕ) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (k + 1)) :=
  (hX.of_mulEquiv (MulEquiv.mk (Equiv.mk (fun g ↦ Multiplicative.ofAdd (Additive.ofMul g))
    (fun g ↦ Additive.toMul (Multiplicative.toAdd g)) (fun _ ↦ rfl) (fun _ ↦ rfl))
    (fun _ _ ↦ rfl))).subsingleton_singularHomology_of_isTorsion' hG R k

/-- **Integral positive-degree homology of `K(A, n + 1)` is `S`-torsion when `A` is `S`-torsion.**
This verifies Serre's `K(A, n)` property for every submonoid-torsion class. -/
theorem isTorsion'_singularHomology
    {A : Type} [AddCommGroup A] {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    {S : Submonoid ℤ} (hA : Module.IsTorsion' A S) (k : ℕ) :
    Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of X)).homology (k + 1)) S :=
  ((TopCat.of X).isTorsion'_singularHomology_int_iff_subsingleton S (Localization S)
    (k + 1)).2 (hX.subsingleton_singularHomology_of_isTorsion' hA (Localization S) k)

/-- **Serre's `K(A, n + 1)` property for the `S`-torsion Serre class.** If `A` belongs to
`AddCommGrpCat.isSubmonoidTorsion S`, then so does `H_{k + 1}(K(A, n + 1); ℤ)` for every `k`. -/
theorem isSubmonoidTorsion_singularHomology
    {A : AddCommGrpCat.{0}} {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    {S : Submonoid ℤ} (hA : AddCommGrpCat.isSubmonoidTorsion S A) (k : ℕ) :
    AddCommGrpCat.isSubmonoidTorsion S
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (k + 1))) :=
  (AddCommGrpCat.prop_isSubmonoidTorsion_iff S _).2 <|
    hX.isTorsion'_singularHomology ((AddCommGrpCat.prop_isSubmonoidTorsion_iff S A).1 hA) k

/-- **Rational acyclicity of `K(A, n + 1)` for a torsion abelian group `A`**:
`H_{k + 1}(K(A, n + 1); ℚ) = 0` for all `n, k : ℕ`. -/
theorem subsingleton_singularHomology_rat
    {A : Type} [AddCommGroup A] {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    (hA : IsAddTorsion A) (k : ℕ) :
    Subsingleton (((singularChains ℚ).obj (TopCat.of X)).homology (k + 1)) :=
  hX.subsingleton_singularHomology_of_isTorsion' (S := nonZeroDivisors ℤ)
    (isAddTorsion_iff_isTorsion_int.1 hA) ℚ k

/-- **Integral positive-degree homology of `K(A, n + 1)` is torsion when `A` is torsion.** -/
theorem isAddTorsion_singularHomology
    {A : Type} [AddCommGroup A] {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    (hA : IsAddTorsion A) (k : ℕ) :
    IsAddTorsion (((singularChains ℤ).obj (TopCat.of X)).homology (k + 1)) :=
  (TopCat.isAddTorsion_singularHomology_iff_subsingleton_rat (TopCat.of X) (k + 1)).2
    (hX.subsingleton_singularHomology_rat hA k)

/-- **Serre's `K(A, n + 1)` property for the torsion Serre class.** If `A` belongs to
`AddCommGrpCat.isTorsion`, then so does `H_{k + 1}(K(A, n + 1); ℤ)` for every `k`. -/
theorem isTorsion_singularHomology
    {A : AddCommGrpCat.{0}} {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) (n + 1) X x)
    (hA : AddCommGrpCat.isTorsion A) (k : ℕ) :
    AddCommGrpCat.isTorsion
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (k + 1))) :=
  (AddCommGrpCat.prop_isTorsion_iff _).2 <|
    hX.isAddTorsion_singularHomology ((AddCommGrpCat.prop_isTorsion_iff A).1 hA) k

end IsEilenbergMacLaneSpace

end TauCeti
