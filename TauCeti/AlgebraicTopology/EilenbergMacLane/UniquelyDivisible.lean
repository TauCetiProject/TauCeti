/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo
public import TauCeti.AlgebraicTopology.Singular.Fibration.AcyclicFiber

import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Acyclicity of Eilenberg--Mac Lane spaces of uniquely divisible abelian groups

Let `m` be an integer, `A` an abelian group on which multiplication by `m` is bijective, and `k` a
commutative semisimple ring in which `m = 0`. For every positive integer `n`, every Eilenberg--Mac
Lane space `(X, x)` of type `K(A, n)` — with no CW or separation hypothesis on `X` — has vanishing
`k`-homology in all positive degrees
(`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`).

The proof proceeds by induction on `n`.
* For `n = 1`, `X` receives a weak homotopy equivalence from Milnor's classifying space of `A`,
  whose `k`-homology is the group homology `H_*(A, k) = 0` in positive degrees
  (`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`).
* For `n + 2`, `X` is simply connected and its based loop space `Ω X x` is an Eilenberg--Mac Lane
  space of type `K(A, n + 1)` (`TauCeti.IsEilenbergMacLaneSpace.loopSpace`), hence `k`-acyclic by
  the induction hypothesis; applying the acyclic-fibre theorem to the contractible fixed-end path
  fibration over `X` (`TauCeti.isZero_singularHomology_of_loopSpace`) shows that `X` is `k`-acyclic
  as well.

Specializing to `m = 2` and `k = ZMod 2` gives the mod-two acyclicity of `K(A, n)` spaces for
uniquely two-divisible abelian groups `A`
(`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`), both over
`ModuleCat (ZMod 2)` and over `ModuleCat ℤ` with `ZMod 2` coefficients. Because no CW hypothesis is
imposed on `X`, the theorem applies directly to loop-space fibres `Ω K(πₙ Z, n)` appearing in the
Whitehead tower of a space `Z`.

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`: a `K(A, n)`
  space of a uniquely `m`-divisible abelian group has vanishing positive-degree `k`-homology over
  any commutative semisimple ring `k` in which `m = 0`.
* `TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`:
  mod-two acyclicity of `K(A, n)` spaces for uniquely two-divisible abelian groups `A`.
* `TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_int_zmod_two_of_isUniquelyTwoDivisible`:
  the corresponding vanishing for singular homology over `ℤ` with `ZMod 2` coefficients.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I and Chapter III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2 and Section 5.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology Topology.Homotopy

namespace TauCeti

namespace IsEilenbergMacLaneSpace

section Semisimple

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

/-- Inductive form on `d` (representing degree `d + 1`) of the acyclicity modulo `m` of
Eilenberg--Mac Lane spaces of uniquely `m`-divisible abelian groups. -/
private theorem isZero_singularHomology_succ_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) :
    ∀ (d : ℕ) {X : Type} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpace (Multiplicative A) (d + 1) X x →
      ∀ q : ℕ, IsZero (((singularChains k).obj (TopCat.of X)).homology (q + 1))
  | 0, X, _, x, hX, q => by
    have hsub := IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul
      k hmk hA (isEilenbergMacLaneSpace_one_iff.1 hX) q
    exact ModuleCat.isZero_iff_subsingleton.2 hsub
  | d + 1, X, _, x, hX, q => by
    have : PathConnectedSpace X := hX.pathConnectedSpace
    have hπ₁ : Subsingleton (π_ 1 X x) := hX.subsingleton_homotopyGroup (by omega)
    exact isZero_singularHomology_of_loopSpace x hπ₁ k
      (isZero_singularHomology_succ_of_bijective_zsmul hmk hA d hX.loopSpace) q

/-- **`K(A, n)` spaces of uniquely `m`-divisible abelian groups are acyclic modulo `m`.** If
multiplication by the integer `m` is bijective on an abelian group `A` and `k` is a commutative
semisimple ring in which `m = 0`, then every `K(A, n)` space (for `n ≥ 1`, with no CW or separation
hypothesis) has vanishing `k`-homology in all positive degrees. -/
theorem isZero_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    IsZero (((singularChains k).obj (TopCat.of X)).homology (q + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact isZero_singularHomology_succ_of_bijective_zsmul k hmk hA d hX q

/-- `Subsingleton` form of
`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (q + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1
    (hX.isZero_singularHomology_of_bijective_zsmul k hmk hA q)

end Semisimple

section TwoDivisible

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A` and
every positive integer `n`, every `K(A, n)` space has vanishing mod-two singular homology in all
positive degrees. -/
theorem isZero_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    IsZero (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (q + 1)) :=
  hX.isZero_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) q

/-- `Subsingleton` form of
`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (q + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1
    (hX.isZero_singularHomology_of_isUniquelyTwoDivisible hA q)

/-- Multiplicative-group convenience form of
`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`, for a
commutative group `G` whose additive counterpart `Additive G` is uniquely two-divisible. -/
theorem isZero_singularHomology_of_isUniquelyTwoDivisible_additive {G : Type} [CommGroup G]
    (hG : IsUniquelyTwoDivisible (Additive G)) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpace G n X x) (q : ℕ) :
    IsZero (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (q + 1)) :=
  (hX.of_mulEquiv (MulEquiv.multiplicativeAdditive (H := G)).symm)
    |>.isZero_singularHomology_of_isUniquelyTwoDivisible hG q

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`. -/
theorem isZero_singularHomology_int_zmod_two_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 1)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X)) := by
  let e𝔽₂ := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (q + 1)).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).toModuleIso).app (TopCat.of X))
  let eℤ := (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 1)).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).toModuleIso).app (TopCat.of X))
  have hU : IsZero (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (q + 1)).obj
      (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).obj (TopCat.of X)) :=
    (hX.isZero_singularHomology_of_isUniquelyTwoDivisible hA q).of_iso e𝔽₂
  exact (((TopCat.of X).isZero_singularHomology_modTwo_iff (q + 1)).2 hU).of_iso eℤ.symm

end TwoDivisible

end IsEilenbergMacLaneSpace

end TauCeti
