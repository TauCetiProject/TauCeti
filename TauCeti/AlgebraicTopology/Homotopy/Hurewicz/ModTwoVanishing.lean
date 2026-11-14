/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.Singular.Fibration.AcyclicFiber

/-!
# Mod-two vanishing of higher homotopy groups

Let `(Y, y)` be a path-connected topological space with trivial fundamental group `π₁(Y, y)` whose
positive-degree singular homology with `ZMod 2` coefficients vanishes. Then for every `m : ℕ` the
higher homotopy group `π_{m+2}(Y, y)` is uniquely two-divisible — equivalently, a module over
`ℤ[1/2]` (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`) — and
in particular its tensor product with `ZMod 2` vanishes
(`TauCeti.subsingleton_tensorProduct_zmod_two_homotopyGroup`). No CW, separation, or
finite-generation hypothesis is imposed on `Y` or on its homotopy groups.

Note that the class `{G | G ⊗ ℤ/2 = 0}` is not a Serre class of abelian groups (`ℚ` belongs to it
whereas its subgroup `ℤ` does not), whereas the class of uniquely two-divisible abelian groups is
closed under kernels, cokernels, and extensions and makes Eilenberg--Mac Lane spaces `K(A, n)`
acyclic modulo two
(`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_isUniquelyTwoDivisible`).

## Proof outline

1. **One-step connected-cover lemma.** Let `Z` be a Hausdorff, `(m + 1)`-connected space whose
   mod-two homology vanishes in degrees `m + 2` and `m + 3`. By the Hurewicz theorem and the
   Bockstein sequence (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two`), the group
   `π_{m+2}(Z, z)` is uniquely two-divisible. The fibre over `z` of the `(m + 2)`-connected cover
   `Z⟨m + 2⟩ ⟶ Z` is an Eilenberg--Mac Lane space of type `K(π_{m+2}(Z, z), m + 1)`
   (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`), so it is path-connected and has
   vanishing positive mod-two homology. By the acyclic-fibre theorem
   (`TauCeti.TopCat.isIso_singularHomologyMap_of_fiber`), the projection `Z⟨m + 2⟩ ⟶ Z` induces an
   isomorphism on `H_q(-; ZMod 2)` in every degree `q`
   (`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`). In particular, if `Z` has
   vanishing positive mod-two homology, then so does `Z⟨m + 2⟩`
   (`TauCeti.isZero_singularHomology_nConnectedCover_mod_two`).
2. **Whitehead-tower induction and CW approximation.** Replacing `Y` by its Hausdorff CW
   approximation `Z₀ = cwApproximation (TopCat.of Y) y` preserves path-connectedness, all homotopy
   groups, and mod-two singular homology. Iterating `Z ↦ Z⟨m + 2⟩` produces, for each `m : ℕ`, a
   Hausdorff `(m + 1)`-connected mod-two acyclic space `(Z_m, z_m)` with
   `π_k(Z_m, z_m) ≃* π_k(Y, y)` for all `k ≥ m + 2`, from which unique two-divisibility of
   `π_{m+2}(Y, y)` follows.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`,
  `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two`: if `(Z, z)` is Hausdorff,
  `(m + 1)`-connected, and has vanishing mod-two homology in degrees `m + 2` and `m + 3`, then
  `nConnectedCoverProj (m + 2) Z z` induces isomorphisms on mod-two homology in all degrees.
* `TauCeti.isZero_singularHomology_nConnectedCover_mod_two`: under the same connectivity hypothesis,
  mod-two acyclicity passes from `Z` to `nConnectedCover (m + 2) Z z`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace`: every higher homotopy
  group `π_{m+2}(Y, y)` of a simply connected mod-two acyclic space `Y` is uniquely two-divisible.
* `TauCeti.subsingleton_tensorProduct_zmod_two_homotopyGroup`: consequently
  `π_{m+2}(Y, y) ⊗_ℤ (ZMod 2) = 0` for every `m : ℕ`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III, Theorem 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3 (Whitehead towers) and Section 5.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology Topology.Homotopy

namespace TauCeti

section Coefficients

/-- Singular homology over `ℤ` with `ZMod 2` coefficients vanishes if and only if singular homology
over the field `ZMod 2` vanishes. -/
private theorem isZero_singularHomology_int_zmod_two_iff (X : TopCat.{0}) (q : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ (ZMod 2))).obj X) ↔
      IsZero (((singularChains (ZMod 2)).obj X).homology q) := by
  let eℤ := (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).toModuleIso).app X)
  let e𝔽₂ := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).toModuleIso).app X)
  exact (Iso.isZero_iff eℤ).symm.trans
    ((X.isZero_singularHomology_modTwo_iff q).trans (Iso.isZero_iff e𝔽₂))

/-- If a map of spaces in `TopCat.{0}` induces an isomorphism on singular homology over `ZMod 2` in
degree `q`, it also induces an isomorphism on singular homology over `ℤ` with `ZMod 2` coefficients
in degree `q`. -/
private theorem isIso_singularHomologyMap_int_zmod_two {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (hf : IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map f)) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ZMod 2))).map f) := by
  let α₂ := (singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).toModuleIso
  have hU₂ : IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).map f) := by
    have : IsIso ((((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
        (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).map f) ≫ α₂.hom.app Y) := by
      rw [α₂.hom.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (α₂.hom.app Y)
  have hU₁ : IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ULift.{0} (ZMod 2)))).map f) := by
    have : IsIso ((((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
        (ModuleCat.of ℤ (ULift.{0} (ZMod 2)))).map f) ≫
        (Y.singularHomologyModTwoIso q).hom) := by
      rw [TopCat.singularHomologyModTwoIso_hom_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Y.singularHomologyModTwoIso q).hom
  let α₁ := (singularHomologyFunctor (ModuleCat.{0} ℤ) q).mapIso
    (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).toModuleIso
  have : IsIso ((((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ZMod 2))).map f) ≫ α₁.inv.app Y) := by
    rw [α₁.inv.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (α₁.inv.app Y)

end Coefficients

section OneStep

variable {Z : TopCat.{0}} [T2Space Z] [PathConnectedSpace Z] {z : Z} {m : ℕ}

/-- **One-step connected-cover mod-two homology isomorphism.** Let `(Z, z)` be a Hausdorff,
`(m + 1)`-connected space whose mod-two homology vanishes in degrees `m + 2` and `m + 3`. Then the
projection `Z⟨m + 2⟩ ⟶ Z` of the `(m + 2)`-connected cover induces an isomorphism on `ZMod 2`
singular homology in every degree `q`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_mod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hm₂ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 2)))
    (hm₃ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 3))) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map (nConnectedCoverProj (m + 2) Z z)) := by
  have hdiv : IsUniquelyTwoDivisible (Additive (π_ (m + 2) Z z)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two hZ
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 2)).2 hm₂)
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 3)).2 hm₃)
  have hEM := isEilenbergMacLaneSpace_fiber_nConnectedCoverProj Z z m fun k _ hk ↦ hZ k hk
  refine TopCat.isIso_singularHomologyMap_of_fiber (serreFibrations_nConnectedCoverProj (m + 2) Z z)
    z (ZMod 2) hEM.pathConnectedSpace (fun r hr ↦ ?_) q
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
  exact hEM.isZero_singularHomology_of_isUniquelyTwoDivisible_additive hdiv d

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hm₂ : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj Z))
    (hm₃ : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 3)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj Z)) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ZMod 2))).map (nConnectedCoverProj (m + 2) Z z)) :=
  isIso_singularHomologyMap_int_zmod_two _ q
    (isIso_singularHomologyMap_nConnectedCoverProj_mod_two hZ
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 2)).1 hm₂)
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 3)).1 hm₃) q)

/-- **One-step preservation of mod-two acyclicity.** If `(Z, z)` is Hausdorff, `(m + 1)`-connected,
and has vanishing positive-degree mod-two singular homology, then its `(m + 2)`-connected cover
`nConnectedCover (m + 2) Z z` also has vanishing positive-degree mod-two singular homology. -/
theorem isZero_singularHomology_nConnectedCover_mod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hH : ∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj Z).homology (q + 1))) (q : ℕ) :
    IsZero (((singularChains (ZMod 2)).obj (nConnectedCover (m + 2) Z z)).homology (q + 1)) := by
  have hIso :=
    isIso_singularHomologyMap_nConnectedCoverProj_mod_two hZ (hH (m + 1)) (hH (m + 2)) (q + 1)
  exact (hH q).of_iso (@asIso _ _ _ _ _ hIso)

end OneStep

section WhiteheadTower

/-- Inductive Whitehead-tower stages over a Hausdorff simply connected mod-two acyclic space `Z₀`:
for each `m : ℕ` there exists a Hausdorff, path-connected, `(m + 1)`-connected, mod-two acyclic
space `(Z, z)` whose homotopy groups above dimension `m + 1` are isomorphic to those of `(Z₀, z₀)`.
-/
private theorem exists_whitehead_stage_of_t2Space (Z₀ : TopCat.{0}) [T2Space Z₀]
    [PathConnectedSpace Z₀] (z₀ : Z₀) (hπ₁ : Subsingleton (π_ 1 Z₀ z₀))
    (hH₀ : ∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj Z₀).homology (q + 1))) (m : ℕ) :
    ∃ (Z : TopCat.{0}) (_ : T2Space Z) (_ : PathConnectedSpace Z) (z : Z),
      (∀ k < m + 2, Subsingleton (π_ k Z z)) ∧
      (∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj Z).homology (q + 1))) ∧
      ∀ k : ℕ, [NeZero k] → m + 1 < k → Nonempty (π_ k Z z ≃* π_ k Z₀ z₀) := by
  induction m with
  | zero =>
    refine ⟨Z₀, inferInstance, inferInstance, z₀, fun k hk ↦ ?_, hH₀,
      fun k _ _ ↦ ⟨MulEquiv.refl _⟩⟩
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z₀).1 inferInstance
    · exact hπ₁
  | succ m ih =>
    obtain ⟨Z, hT2, hPC, z, hConn, hHZ, hEquiv⟩ := ih
    let Z' := nConnectedCover (m + 2) Z z
    let z' := nConnectedCoverBasepoint (m + 2) Z z
    refine ⟨Z', inferInstance, inferInstance, z',
      fun k hk ↦ subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace
        (m + 2) Z z z' (by omega),
      isZero_singularHomology_nConnectedCover_mod_two hConn hHZ,
      fun k _ hk ↦ ?_⟩
    obtain ⟨e⟩ := hEquiv k (by omega)
    exact ⟨(nConnectedCoverHomotopyGroupMulEquiv (m + 2) Z z k (by omega)).trans e⟩

/-- Promotes bijectivity of `HomotopyGroup.map f rfl` at `x` together with `f x = y` to a
multiplicative isomorphism `π_k(X, x) ≃* π_k(Y, y)` for `k ≥ 1`. -/
private def homotopyGroupMulEquivOfBijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {k : ℕ} [NeZero k] (f : C(X, Y)) (x : X) {y : Y} (hf : f x = y)
    (hbij : Function.Bijective (HomotopyGroup.map (N := Fin k) f (rfl : f x = f x))) :
    π_ k X x ≃* π_ k Y y := by
  subst hf
  exact MulEquiv.ofBijective (HomotopyGroup.mapHom f rfl) hbij

/-- **Mod-two vanishing of higher homotopy groups.** Let `(Y, y)` be a path-connected topological
space with trivial fundamental group `π₁(Y, y)`. If `H_{q+1}(Y; ZMod 2) = 0` for every `q : ℕ`,
then for every `m : ℕ` the homotopy group `π_{m+2}(Y, y)` is uniquely two-divisible (a module over
`ℤ[1/2]`). No CW, separation, or finite-generation hypothesis is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y))
    (hH : ∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 1)))
    (m : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) := by
  -- Replace `Y` by its Hausdorff CW approximation `Z₀`.
  let Z₀ := cwApproximation (TopCat.of Y) y
  let z₀ := cwApproximationBasepoint (TopCat.of Y) y
  let g := cwApproximationMap (TopCat.of Y) y
  have hg₀ : g.hom z₀ = y := cwApproximationMap_cwApproximationBasepoint (TopCat.of Y) y
  have he₁ : π_ 1 Z₀ z₀ ≃* π_ 1 Y y :=
    homotopyGroupMulEquivOfBijective g.hom z₀ hg₀
      (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y 0 z₀)
  have hπ₁Z₀ : Subsingleton (π_ 1 Z₀ z₀) := he₁.toEquiv.subsingleton_congr.2 hπ₁
  have hHZ₀ (q : ℕ) : IsZero (((singularChains (ZMod 2)).obj Z₀).homology (q + 1)) := by
    have hIso :=
      (isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Y) y).isIso_singularHomologyMap
        (ModuleCat.of (ZMod 2) (ZMod 2)) (q + 1)
    exact (hH q).of_iso (@asIso _ _ _ _ _ hIso)
  obtain ⟨Z, _, _, z, hConn, hHZ, hEquiv⟩ :=
    exists_whitehead_stage_of_t2Space Z₀ z₀ hπ₁Z₀ hHZ₀ m
  have hdivZ : IsUniquelyTwoDivisible (Additive (π_ (m + 2) Z z)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two hConn
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 2)).2 (hHZ (m + 1)))
      ((isZero_singularHomology_int_zmod_two_iff Z (m + 3)).2 (hHZ (m + 2)))
  obtain ⟨eZ⟩ := hEquiv (m + 2) (by omega)
  have heY : π_ (m + 2) Z₀ z₀ ≃* π_ (m + 2) Y y :=
    homotopyGroupMulEquivOfBijective g.hom z₀ hg₀
      (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y (m + 1) z₀)
  exact hdivZ.of_addEquiv (eZ.trans heY).toAdditive

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y))
    (hH : ∀ q : ℕ, IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 1)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of Y)))
    (m : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two hπ₁
    (fun q ↦ (isZero_singularHomology_int_zmod_two_iff (TopCat.of Y) (q + 1)).1 (hH q)) m

/-- `SimplyConnectedSpace` form of
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y)
    (hH : ∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 1)))
    (m : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance) hH m

/-- **Vanishing of `π_{m+2}(Y, y) ⊗_ℤ (ZMod 2)` for a mod-two acyclic simply connected space.** -/
theorem subsingleton_tensorProduct_zmod_two_homotopyGroup
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y))
    (hH : ∀ q : ℕ, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 1)))
    (m : ℕ) :
    Subsingleton (TensorProduct ℤ (Additive (π_ (m + 2) Y y)) (ZMod 2)) :=
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two hπ₁ hH m)
    |>.subsingleton_tensorProduct_zmod_two

end WhiteheadTower

end TauCeti
