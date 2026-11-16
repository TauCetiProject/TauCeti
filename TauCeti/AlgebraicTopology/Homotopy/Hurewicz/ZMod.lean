/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence
import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.ContinuousMap.Sigma
import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange

/-!
# Mod-`m` and mod-two vanishing theorems for higher homotopy groups

Let `Y` be a topological space with a base point `y` such that `π₁(Y, y)` is trivial, and let
`m : ℕ`. If the singular homology `H_q(Y; ℤ/m)` vanishes in the finite range `2 ≤ q ≤ n + 3`,
then multiplication by `m` is a bijection on `π_{n + 2}(Y, y)`
(`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`). No Hausdorff,
path-connectedness, CW, or finite-generation assumption is needed on `Y`, and `m` need not be
prime or nonzero. For `m = 2` this is the **mod-two vanishing theorem**: if `π₁(Y, y)` is trivial
and the reduced mod-two singular homology of `Y` vanishes in every degree, then every higher
homotopy group `π_{n + 2}(Y, y)` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo`), hence
becomes a `ℤ[1/2]`-module and satisfies `π_{n + 2}(Y, y) ⊗ 𝔽₂ = 0`.

The proof combines three ingredients.
1. **CW approximation reduction**: passing to the path-connected, Hausdorff CW approximation of
   the path component of `y` preserves every positive homotopy group and every singular homology
   vanishing hypothesis, since that summand is a retract of `TauCeti.sigmaCWApproximation`.
2. **Base step**: when `π_k(X, x)` vanishes for `1 ≤ k < n + 2`, the Hurewicz isomorphism on the
   CW approximation of the path component of `x` identifies `π_{n + 2}` with `H_{n + 2}(-; ℤ)`,
   and the mod-`m` coefficient exact sequence makes multiplication by `m` bijective from vanishing
   in degrees `n + 2` and `n + 3` (`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_zmod`).
3. **Whitehead-tower induction**: the fibre of the `(j + 2)`-connected cover `W⟨j + 2⟩ → W` of the
   `(j + 1)`-connected Hausdorff CW approximation `W` is a `K(π_{j + 2} W, j + 1)`. Once
   `π_{j + 2} W` is uniquely `m`-divisible, that fibre is acyclic modulo `m`
   (`IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`), so the Serre fibration
   comparison theorem (`TopCat.isIso_singularHomologyMap_of_isZero_fiber`) shows that
   `W⟨j + 2⟩ → W` induces an isomorphism on `H_*(-; ℤ/m)`. Repeating the step climbs up the
   Whitehead tower to degree `n + 2`.

We also record the sharp finite-range integral Hurewicz vanishing theorem
(`TauCeti.subsingleton_homotopyGroup_of_isZero_singularHomology_int`, requiring only
`2 ≤ q ≤ n + 2`).

## Main declarations

* `TauCeti.subsingleton_homotopyGroup_of_isZero_singularHomology_int`: sharp finite-range
  integral Hurewicz vanishing.
* `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_zmod`: unique `m`-divisibility of the first
  possible nonzero homotopy group from vanishing of `H_{n + 2}(-; ℤ/m)` and `H_{n + 3}(-; ℤ/m)`.
* `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod`: sharp
  finite-range and reduced-homology mod-`m` vanishing theorems.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo`: the
  mod-two vanishing theorem.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.2 and 4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti

/-! ### Algebraic and CW-approximation reductions -/

/-- Transport bijectivity of integer multiplication along an additive group isomorphism. -/
private lemma bijective_zsmul_of_addEquiv {A B : Type*} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (m : ℤ) (h : Function.Bijective fun a : A ↦ m • a) :
    Function.Bijective fun b : B ↦ m • b := by
  have hcomp : (fun b : B ↦ m • b) = e ∘ (fun a : A ↦ m • a) ∘ e.symm := by
    funext b
    simp [map_zsmul]
  exact hcomp ▸ e.bijective.comp (h.comp e.symm.bijective)

/-- Transport bijectivity of integer multiplication on `Additive` along a multiplicative group
isomorphism. -/
private lemma bijective_zsmul_additive_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (m : ℤ) (h : Function.Bijective fun a : Additive G ↦ m • a) :
    Function.Bijective fun b : Additive H ↦ m • b :=
  bijective_zsmul_of_addEquiv (MulEquiv.toAdditive e) m h

/-- The CW approximation of the path component of `y` inherits singular homology vanishing from
`Y`, since it is a retract of `TauCeti.sigmaCWApproximation`. -/
private lemma isZero_singularHomology_cwApproximation_of_isZero {Y : Type} [TopologicalSpace Y]
    (y : Y) (R : Type) [Ring R] (q : ℕ)
    (hY : IsZero (((singularChains R).obj (TopCat.of Y)).homology q)) :
    IsZero (((singularChains R).obj
      (cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y)))).homology q) := by
  let c : ZerothHomotopy (TopCat.of Y) := ZerothHomotopy.mk y
  let x₀ : TopCat.of Y := Quotient.out c
  let Z := cwApproximation (TopCat.of Y) x₀
  let H := (singularHomologyFunctor (ModuleCat.{0} R) q).obj (ModuleCat.of R R)
  have : IsIso (H.map (sigmaCWApproximationMap (TopCat.of Y))) :=
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap (TopCat.of Y)).isIso_singularHomologyMap
      (ModuleCat.of R R) q
  let e := asIso (H.map (sigmaCWApproximationMap (TopCat.of Y)))
  have hS : IsZero (H.obj (sigmaCWApproximation (TopCat.of Y))) := hY.of_iso e
  let ι : Z ⟶ sigmaCWApproximation (TopCat.of Y) :=
    TopCat.ofHom (ContinuousMap.sigmaMk
      (X := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c)
  let r : sigmaCWApproximation (TopCat.of Y) ⟶ Z :=
    TopCat.ofHom (ContinuousMap.sigmaRetraction
      (Z := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c (cwApproximationBasepoint (TopCat.of Y) x₀))
  have hcomp : ι ≫ r = 𝟙 Z := by
    ext p
    exact ContinuousMap.sigmaRetraction_sigmaMk
      (Z := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c (cwApproximationBasepoint (TopCat.of Y) x₀) p
  refine (IsZero.iff_id_eq_zero (H.obj Z)).2 ?_
  rw [← H.map_id, ← hcomp, H.map_comp, hS.eq_of_tgt (H.map ι) 0, Limits.zero_comp]

/-- The CW approximation of the path component of `y` has the same positive homotopy groups as `Y`
at `y`. -/
private def cwApproximationHomotopyGroupMulEquiv {Y : Type} [TopologicalSpace Y] (y : Y) (k : ℕ) :
    π_ (k + 1) (cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y)))
      (cwApproximationBasepoint (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))) ≃*
      π_ (k + 1) Y y :=
  let x₀ : TopCat.of Y := Quotient.out (ZerothHomotopy.mk y)
  let z := cwApproximationBasepoint (TopCat.of Y) x₀
  (MulEquiv.ofBijective
    (HomotopyGroup.mapHom (cwApproximationMap (TopCat.of Y) x₀).hom rfl)
    (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) x₀ k z)).trans
    (homotopyGroupMulEquivOfPath
      ((Quotient.mk_out (s := pathSetoid Y) y).somePath.cast
        (cwApproximationMap_cwApproximationBasepoint (TopCat.of Y) x₀) rfl))

/-! ### Sharp finite-range integral Hurewicz vanishing -/

/-- **Sharp finite-range integral Hurewicz vanishing.** If `π₁(Y, y)` is trivial and the integral
singular homology `H_q(Y; ℤ)` vanishes for `2 ≤ q ≤ n + 2`, then `π_{n + 2}(Y, y)` is trivial.
No connectedness, separation, or CW assumption is needed on `Y`. -/
theorem subsingleton_homotopyGroup_of_isZero_singularHomology_int {Y : Type} [TopologicalSpace Y]
    {y : Y} [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 2 →
      IsZero (((singularChains ℤ).obj (TopCat.of Y)).homology q)) :
    Subsingleton (π_ (n + 2) Y y) := by
  let Z := cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
  let z := cwApproximationBasepoint (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
  have hZ1 : Subsingleton (π_ 1 Z z) :=
    (cwApproximationHomotopyGroupMulEquiv y 0).toEquiv.subsingleton
  have hZ : ∀ j ≤ n, Subsingleton (π_ (j + 2) Z z) := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have hconn : ∀ k < j + 2, Subsingleton (π_ k Z z) := by
        intro k hk
        match k with
        | 0 => exact HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
        | 1 => exact hZ1
        | k + 2 => exact ih k (by omega) (by omega)
      have : Subsingleton (((singularChains ℤ).obj (TopCat.of Z)).homology (j + 2)) :=
        ModuleCat.isZero_iff_subsingleton.1 <|
          isZero_singularHomology_cwApproximation_of_isZero y ℤ (j + 2)
            (hY (j + 2) (by omega) (by omega))
      exact (Additive.ofMul.trans
        (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hconn).toEquiv).subsingleton
  have : Subsingleton (π_ (n + 2) Z z) := hZ n le_rfl
  exact (cwApproximationHomotopyGroupMulEquiv y (n + 1)).symm.toEquiv.subsingleton

/-! ### Base step and the mod-`m` and mod-two vanishing theorems -/

/-- **First nonzero homotopy group modulo `m`.** For a pointed space `(X, x)` whose homotopy groups
`π_k(X, x)` vanish for `1 ≤ k < n + 2` and any `m : ℕ`, vanishing of `H_{n + 2}(X; ℤ/m)` and
`H_{n + 3}(X; ℤ/m)` makes multiplication by `m` bijective on `π_{n + 2}(X, x)`. No
path-connectedness, separation, or CW assumption is needed on `X`. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_zmod {X : Type} [TopologicalSpace X] {x : X}
    {n m : ℕ} (hX : ∀ k, 1 ≤ k → k < n + 2 → Subsingleton (π_ k X x))
    (hn : IsZero (((singularChains (ZMod m)).obj (TopCat.of X)).homology (n + 2)))
    (hn' : IsZero (((singularChains (ZMod m)).obj (TopCat.of X)).homology (n + 3))) :
    Function.Bijective fun a : Additive (π_ (n + 2) X x) ↦ (m : ℤ) • a := by
  let Z := cwApproximation (TopCat.of X) (Quotient.out (ZerothHomotopy.mk x))
  let z := cwApproximationBasepoint (TopCat.of X) (Quotient.out (ZerothHomotopy.mk x))
  have hZ : ∀ k < n + 2, Subsingleton (π_ k Z z) := fun k hk ↦ match k with
    | 0 => HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    | k + 1 =>
      have : Subsingleton (π_ (k + 1) X x) := hX (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hk
      (cwApproximationHomotopyGroupMulEquiv x k).toEquiv.subsingleton
  have hbij := (TopCat.of Z).bijective_zsmul_singularHomology_of_isZero_zmod m (n + 2)
    (((TopCat.of Z).isZero_singularHomology_uliftZMod_iff m (n + 2)).2
      (isZero_singularHomology_cwApproximation_of_isZero x (ZMod m) (n + 2) hn))
    (((TopCat.of Z).isZero_singularHomology_uliftZMod_iff m (n + 3)).2
      (isZero_singularHomology_cwApproximation_of_isZero x (ZMod m) (n + 3) hn'))
  let e : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of Z) ≃+
      ((singularChains ℤ).obj (TopCat.of Z)).homology (n + 2) :=
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso).app
        (TopCat.of Z)).toLinearEquiv.toAddEquiv
  exact bijective_zsmul_additive_of_mulEquiv (cwApproximationHomotopyGroupMulEquiv x (n + 1))
    (m : ℤ) (bijective_zsmul_of_addEquiv
      (e.trans (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hZ).symm) (m : ℤ) hbij)

/-- Whitehead-tower induction: `d` steps climb from vanishing of `π_k` for `1 ≤ k < j + 2` to
unique `m`-divisibility of `π_{j + d + 2}`. -/
private theorem bijective_zsmul_homotopyGroup_of_isZero_zmod_aux (m : ℕ) :
    ∀ (d j : ℕ) {Y : Type} [TopologicalSpace Y] {y : Y},
      (∀ k, 1 ≤ k → k < j + 2 → Subsingleton (π_ k Y y)) →
      (∀ q, j + 2 ≤ q → q ≤ j + d + 3 →
        IsZero (((singularChains (ZMod m)).obj (TopCat.of Y)).homology q)) →
      Function.Bijective fun a : Additive (π_ (j + d + 2) Y y) ↦ (m : ℤ) • a
  | 0, j, _, _, _, hY, hH =>
    bijective_zsmul_homotopyGroup_of_isZero_zmod hY
      (hH (j + 2) le_rfl (by omega)) (hH (j + 3) (by omega) le_rfl)
  | d + 1, j, Y, _, y, hY, hH => by
    let W := cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
    let w := cwApproximationBasepoint (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
    have hW : ∀ k, k ≠ 0 → k < j + 2 → Subsingleton (π_ k W w) := fun k hk0 hk ↦ by
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have : Subsingleton (π_ (k' + 1) Y y) := hY (k' + 1) (by omega) hk
      exact (cwApproximationHomotopyGroupMulEquiv y k').toEquiv.subsingleton
    have hπ : Function.Bijective fun a : Additive (π_ (j + 2) W w) ↦ (m : ℤ) • a :=
      bijective_zsmul_additive_of_mulEquiv (cwApproximationHomotopyGroupMulEquiv y (j + 1)).symm
        (m : ℤ) (bijective_zsmul_homotopyGroup_of_isZero_zmod hY
          (hH (j + 2) le_rfl (by omega)) (hH (j + 3) (by omega) (by omega)))
    let E := nConnectedCover (j + 2) (TopCat.of W) w
    let e₀ := nConnectedCoverBasepoint (j + 2) (TopCat.of W) w
    have hE : ∀ k, 1 ≤ k → k < (j + 1) + 2 → Subsingleton (π_ k E e₀) := fun k _ hk ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (j + 2) (TopCat.of W) w e₀
        (by omega)
    have hf := isEilenbergMacLaneSpace_fiber_nConnectedCoverProj (TopCat.of W) w j hW
    have := hf.pathConnectedSpace
    have hHE : ∀ q, (j + 1) + 2 ≤ q → q ≤ (j + 1) + d + 3 →
        IsZero (((singularChains (ZMod m)).obj (TopCat.of E)).homology q) := fun q hq1 hq2 ↦ by
      have := TopCat.isIso_singularHomologyMap_of_isZero_fiber
        (serreFibrations_nConnectedCoverProj (j + 2) (TopCat.of W) w) w (ZMod m) q fun r _ ↦
        IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul
          (ModuleCat.of (ZMod m) (ZMod m))
          (fun a ↦ by rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]) hπ
          (hf.of_mulEquiv (AddEquiv.toMultiplicativeRight (.refl _))) r
      let e := asIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod m)) q).obj
        (ModuleCat.of (ZMod m) (ZMod m))).map (nConnectedCoverProj (j + 2) (TopCat.of W) w))
      exact (isZero_singularHomology_cwApproximation_of_isZero y (ZMod m) q
        (hH q (by omega) (by omega))).of_iso e
    have hstep := bijective_zsmul_homotopyGroup_of_isZero_zmod_aux m d (j + 1) hE hHE
    exact bijective_zsmul_additive_of_mulEquiv
      (((HomotopyGroup.congrMulEquiv (finCongr (by omega : j + 1 + d + 2 = j + (d + 1) + 2))).trans
        (nConnectedCoverHomotopyGroupMulEquiv (j + 2) (TopCat.of W) w
          (j + (d + 1) + 2) (by omega))).trans
        (cwApproximationHomotopyGroupMulEquiv y (j + d + 2)))
      (m : ℤ) hstep

/-- **Sharp finite-range mod-`m` vanishing theorem.** Let `Y` be a space with a base point `y` such
that `π₁(Y, y)` is trivial, and let `m, n : ℕ`. If `H_q(Y; ℤ/m) = 0` for all `2 ≤ q ≤ n + 3`, then
multiplication by `m` is a bijection on `π_{n + 2}(Y, y)`. No Hausdorff, path-connectedness, CW,
or finite-generation assumption is required on `Y`, and `m` need not be prime or nonzero. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularChains (ZMod m)).obj (TopCat.of Y)).homology q)) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a := by
  have h1 : ∀ k, 1 ≤ k → k < 0 + 2 → Subsingleton (π_ k Y y) := fun k hk1 hk2 ↦ by
    obtain rfl : k = 1 := by omega
    infer_instance
  have hstep := bijective_zsmul_homotopyGroup_of_isZero_zmod_aux m n 0 h1 fun q hq1 hq2 ↦
    hY q (by omega) (by omega)
  exact bijective_zsmul_additive_of_mulEquiv
    (HomotopyGroup.congrMulEquiv (finCongr (by omega : 0 + n + 2 = n + 2))) (m : ℤ) hstep

/-- **Reduced-homology mod-`m` vanishing theorem.** If `π₁(Y, y)` is trivial and the reduced
singular homology of `Y` with coefficients in `ZMod m` vanishes in every degree, then
multiplication by `m` is a bijection on every higher homotopy group `π_{n + 2}(Y, y)`. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m : ℕ}
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor
      (ModuleCat.of (ZMod m) (ZMod m)) q).obj (TopCat.of Y))) (n : ℕ) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod fun q hq _ ↦ by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact (hY (q' + 1)).of_iso
      ((reducedSingularHomologySuccIso (ModuleCat.of (ZMod m) (ZMod m)) q').app (TopCat.of Y)).symm

/-- **Sharp finite-range mod-two vanishing theorem.** If `π₁(Y, y)` is trivial and `H_q(Y; 𝔽₂) = 0`
for all `2 ≤ q ≤ n + 3`, then `π_{n + 2}(Y, y)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  (isUniquelyTwoDivisible_iff _).2
    (bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod hY)

/-- **The mod-two vanishing theorem.** If `π₁(Y, y)` is trivial and the reduced mod-two singular
homology of `Y` vanishes in every degree, then every higher homotopy group `π_{n + 2}(Y, y)` is
uniquely two-divisible (hence is a `ℤ[1/2]`-module and satisfies `π_{n + 2}(Y, y) ⊗ 𝔽₂ = 0`). -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor
      (ModuleCat.of (ZMod 2) (ZMod 2)) q).obj (TopCat.of Y))) (n : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  (isUniquelyTwoDivisible_iff _).2
    (bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod hY n)

end TauCeti
