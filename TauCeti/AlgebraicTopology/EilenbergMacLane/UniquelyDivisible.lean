/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.Algebra.Group.Pow
import TauCeti.AlgebraicTopology.Singular.Coefficients.Divisible
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence
import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction

/-!
# Eilenberg--Mac Lane spaces of uniquely divisible groups

Let `m : ℤ`, let `A` be an abelian group on which multiplication by `m` is bijective, and let
`n ≥ 1` (with `A`, the space, and the coefficient rings/modules in arbitrary universes). Then
every Eilenberg--Mac Lane space `X` of type `K(A, n)` (with no hypothesis of CW type) satisfies:

* multiplication by `m` is bijective on positive-degree integral singular homology `Hᵢ(X; ℤ)`
  (`TauCeti.IsEilenbergMacLaneSpace.bijective_zsmul_singularHomology_int_of_bijective_zsmul`);
* for any ring `R` and any `R`-module `M` annihilated by `m`, the positive-degree singular homology
  `Hᵢ(X; M)` vanishes
  (`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`) and the reduced
  singular homology with coefficients in `M` vanishes in every degree
  (`TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_bijective_zsmul`);
* in particular, for any ring `k` in which `m = 0` (with no commutativity or semisimplicity
  assumption, including `ZMod m` for any `m : ℕ`), `Hᵢ(X; k)` vanishes for all `i > 0`
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`, and the
  multiplicative `[CommGroup G]` form
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zpow`);
* for `m = 2`: every `K(A, n)` space of a uniquely two-divisible group has the mod-two homology of
  a point
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`).

The proof proceeds in three stages. First, for a commutative semisimple ring `k` with `m = 0`, the
base case `n = 1` is the computation of the group homology of `A`
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`), and the
induction on `n` goes through the based path fibration `p : P → X`
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).
Second, applying this at each prime divisor `p ∣ m` together with the prime-factor criterion
(`TopCat.isZero_singularHomology_zmod_iff_forall_prime`) and the mod-`m` coefficient sequence yields
bijectivity of multiplication by `m` on `Hᵢ(X; ℤ)`. Third, for any path-connected space with
uniquely `m`-divisible positive integral homology,
`TauCeti.isZero_singularHomology_of_bijective_zsmul_int` shows that homology with coefficients in
any `ℤ`-module annihilated by `m` vanishes in positive degrees, and restriction of scalars along
`ℤ →+* R` transfers this to arbitrary `R`-modules.

This is the input on Eilenberg--Mac Lane spaces for Serre's mod-`m` and mod-two vanishing theorems.

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.bijective_zsmul_singularHomology_int_of_bijective_zsmul`:
  unique `m`-divisibility of the positive-degree integral singular homology of `K(A, n)`.
* `TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_bijective_zsmul`:
  vanishing of positive-degree and reduced singular homology of `K(A, n)` with coefficients in any
  module annihilated by `m`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zpow`: a `K(A, n)`
  (or multiplicatively `K(G, n)`) space of a uniquely `m`-divisible abelian group is acyclic modulo
  `m` over any ring `k` with `(m : k) = 0`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`: a
  `K(A, n)` space of a uniquely two-divisible abelian group has the mod-two homology of a point.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_odd_natCard`: so does a
  `K(A, n)` space of a finite abelian group of odd order, such as `K(ℤ/3, 1)`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1,
  Proposition 4.21, and Section 4.2, Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace TauCeti

namespace IsEilenbergMacLaneSpace

/-- Mod-`m` acyclicity of `K(A, d)` spaces for arbitrary `m : ℕ`, obtained from prime moduli via
`TopCat.isZero_singularHomology_zmod_iff_forall_prime`. -/
private theorem isZero_singularHomology_zmod_of_bijective_zsmul {m : ℕ} {A : Type u}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ (m : ℤ) • a) {d : ℕ} [NeZero d]
    {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x) (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj (TopCat.of X)) := by
  by_cases hm : m = 0
  · subst hm
    have : Subsingleton A := ⟨fun a b ↦ hA.1 (by simp)⟩
    have hπ (r : ℕ) : Subsingleton (HomotopyGroup (Fin r) X x) := by
      by_cases hr : r = d
      · subst hr
        exact (hX.nonempty_homotopyGroupMulEquiv.some.toEquiv.trans
          Multiplicative.toAdd).subsingleton
      · exact hX.subsingleton_homotopyGroup hr
    exact ((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv 0
      (ULift.ringEquiv : ULift.{u} (ZMod 0) ≃+* ZMod 0) (n + 1)).2 <|
        isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup (fun r _ ↦ hπ r)
          (ULift.{u} (ZMod 0)) (Nat.succ_ne_zero n) (Nat.lt_succ_self (n + 1))
  · have : NeZero m := ⟨hm⟩
    refine ((TopCat.of X).isZero_singularHomology_zmod_iff_forall_prime m (n + 1)).2
      fun p hp hpm ↦ ?_
    have : Fact p.Prime := ⟨hp⟩
    have hAp : Function.Bijective fun a : A ↦ (p : ℤ) • a :=
      TauCeti.bijective_zsmul_of_dvd (Int.natCast_dvd_natCast.2 hpm) hA
    have : IsSemisimpleRing (ULift.{u} (ZMod p)) :=
      (ULift.ringEquiv : ULift.{u} (ZMod p) ≃+* ZMod p).symm.isSemisimpleRing
    exact ((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv p
      (ULift.ringEquiv : ULift.{u} (ZMod p) ≃+* ZMod p) (n + 1)).2 <|
        ModuleCat.isZero_iff_subsingleton.2 <|
          subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne (ULift.{u} (ZMod p))
            (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul
              (ULift.{u} (ZMod p)) (m := p) (ULift.down_injective (by simp)) hAp) hX n

/-- **Unique `m`-divisibility of the integral homology of `K(A, d)`**: if multiplication by `m : ℤ`
is a bijection of `A`, then for every `d ≥ 1` and `n ≥ 0`, multiplication by `m` is a bijection on
the lifted integral singular homology `Hₙ₊₁(K(A, d); ULift.{u} ℤ)`. -/
theorem bijective_zsmul_singularHomology_int_of_bijective_zsmul {m : ℤ} {A : Type u}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x)
    (n : ℕ) :
    Function.Bijective fun y : ((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X) ↦ m • y := by
  rw [TauCeti.bijective_zsmul_iff_natAbs] at hA ⊢
  exact (TopCat.of X).bijective_zsmul_singularHomology_of_isZero_zmod m.natAbs (n + 1)
    (isZero_singularHomology_zmod_of_bijective_zsmul hA hX n)
    (isZero_singularHomology_zmod_of_bijective_zsmul hA hX (n + 1))

/-- **`K(A, d)` spaces of uniquely `m`-divisible groups are acyclic for any module killed by `m`.**
If multiplication by `m : ℤ` is a bijection of `A`, then for every `d ≥ 1`, every ring `R`, and
every `R`-module `M` annihilated by `m`, every `K(A, d)` space has vanishing positive-degree
singular homology `Hₙ₊₁(X; M) = 0`. -/
theorem isZero_singularHomology_of_bijective_zsmul {R : Type v} [Ring R] (M : ModuleCat.{u} R)
    {m : ℤ} (hmM : ∀ a : M, m • a = 0) {A : Type u} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x)
    (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj M).obj
      (TopCat.of X)) := by
  have := hX.pathConnectedSpace
  let F := ModuleCat.restrictScalars.{u} (algebraMap ℤ R)
  have hℤ : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (F.obj M)).obj (TopCat.of X)) :=
    TauCeti.isZero_singularHomology_of_bijective_zsmul_int
      (bijective_zsmul_singularHomology_int_of_bijective_zsmul hA hX) (F.obj M) hmM n
  exact (F.isZero_singularHomologyFunctor_iff M (n + 1) _).1 hℤ

/-- **Reduced acyclicity of `K(A, d)` spaces modulo `m`.** If multiplication by `m : ℤ` is a
bijection of `A`, then for every `d ≥ 1`, every ring `R`, and every `R`-module `M` annihilated by
`m`, the reduced singular homology of every `K(A, d)` space `X` with coefficients in `M` vanishes
in every degree, including degree zero. -/
theorem isZero_reducedSingularHomology_of_bijective_zsmul {R : Type v} [Ring R]
    (M : ModuleCat.{u} R) {m : ℤ} (hmM : ∀ a : M, m • a = 0) {A : Type u} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x)
    (n : ℕ) :
    Limits.IsZero ((reducedSingularHomologyFunctor M n).obj (TopCat.of X)) := by
  cases n with
  | zero =>
    have := hX.pathConnectedSpace
    exact isZero_reducedSingularHomologyFunctor_zero _ _
  | succ n =>
    exact (isZero_singularHomology_of_bijective_zsmul M hmM hA hX n).of_iso
      ((reducedSingularHomologySuccIso M n).app (TopCat.of X))

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, n)`
space, for every `n ≥ 1`, has no homology in positive degrees with coefficients in any ring `k` in
which `m = 0` (including `ZMod m` for any `m : ℕ`). -/
theorem subsingleton_singularHomology_of_bijective_zsmul (k : Type u) [Ring k] {m : ℤ}
    (hmk : (m : k) = 0) {A : Type u} [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a)
    {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1 <|
    isZero_singularHomology_of_bijective_zsmul (ModuleCat.of k k)
      (fun a ↦ by rw [zsmul_eq_mul, hmk, zero_mul]) hA hX i

/-- Multiplicative form of `subsingleton_singularHomology_of_bijective_zsmul`: if raising to the
`m`-th power is a bijection of a commutative group `G`, then every `K(G, n)` space has no positive
degree homology with coefficients in any ring `k` in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zpow (k : Type u) [Ring k] {m : ℤ}
    (hmk : (m : k) = 0) {G : Type u} [CommGroup G] (hG : Function.Bijective fun g : G ↦ g ^ m)
    {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace G n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul k hmk (A := Additive G)
    (Additive.ofMul.bijective.comp (hG.comp Additive.toMul.bijective))
    (hX.of_mulEquiv (AddEquiv.toMultiplicativeRight (.refl (Additive G)))) i

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A`
and every `n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; k) = 0` for
all `i > 0`, with coefficients in any ring `k` in which `2 = 0`, such as `𝔽₂`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible (k : Type u) [Ring k]
    (hk : (2 : k) = 0) {A : Type u} [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) {n : ℕ}
    [NeZero n] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul k (m := 2) (mod_cast hk)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

/-- **Mod-two acyclicity of `K(A, n)` spaces of finite groups of odd order.** For a finite abelian
group `A` of odd order, such as `ℤ/3`, and every `n ≥ 1`, every `K(A, n)` space has the mod-two
homology of a point, with coefficients in any ring `k` in which `2 = 0`: `A` is uniquely
two-divisible (`TauCeti.isUniquelyTwoDivisible_iff_odd_natCard`). -/
theorem subsingleton_singularHomology_of_odd_natCard (k : Type u) [Ring k] (hk : (2 : k) = 0)
    {A : Type u} [AddCommGroup A] [Finite A] (hA : Odd (Nat.card A)) {n : ℕ} [NeZero n]
    {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk
    ((isUniquelyTwoDivisible_iff_odd_natCard A).2 hA) hX i

end IsEilenbergMacLaneSpace

end TauCeti
