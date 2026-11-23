/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.PowerTorsion
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
import TauCeti.AlgebraicTopology.Homotopy.WhiteheadTower
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# The Hurewicz theorem modulo the groups annihilated by a power of `d`

**Theorem** (Serre). Let `d` be a natural number, `Y` a simply connected space and `k` a natural
number such that every integral homology group `Hᵢ(Y; ℤ)`, `1 ≤ i ≤ k`, is annihilated by some
power of `d`. Then so is every homotopy group `πᵢ(Y)`, `2 ≤ i ≤ k`
(`TauCeti.isKilledBySomePower_homotopyGroup_of_isKilledBySomePower_singularHomology`). No finite
generation and no CW structure is assumed.

This is the vanishing half of Serre's Hurewicz theorem modulo a class of abelian groups, for the
Serre class `AddCommGrpCat.isKilledBySomePower d` of groups annihilated by *some* power of `d`.
The groups annihilated by one fixed power `dᵐ`, `d ≥ 2`, `m ≥ 1`, do not form a Serre class, and
the class is not the class of groups each of whose elements is annihilated by some power of `d`:
`⨁ₘ ℤ/dᵐ` lies in the second and not in the first. For finitely generated groups the two agree.

The proof climbs the Whitehead tower one homotopy group at a time, as for mod-two vanishing.

* **First homotopy group.** If `Z` is `(n - 1)`-connected, `n ≥ 2`, the Hurewicz isomorphism
  `πₙ(Z) ≅ Hₙ(Z; ℤ)` puts `πₙ(Z)` in the class as soon as `Hₙ(Z; ℤ)` is.
* **One step up the tower.** The projection `Z⟨n⟩ → Z` of the `n`-connected cover is a fibration
  whose fibres are homotopy equivalent to the loop space of a `K(πₙ(Z), n)`, a `K(πₙ(Z), n - 1)`
  (`TauCeti.nConnectedCoverFiberHomotopyEquivLoopSpace`). Its homology in positive degrees is in
  the class (`TauCeti.IsEilenbergMacLaneSpace.isKilledBySomePower_singularHomology`), and in the
  finitely many degrees up to `k` it is annihilated by one common power of `d`. The comparison
  theorem modulo a Serre class (`TauCeti.TopCat.isoModSerre_singularHomologyMap_of_prop_fiber`)
  then makes the projection an isomorphism on `Hᵢ(-; ℤ)` modulo the class for `i ≤ k`, so
  `Hᵢ(Z⟨n⟩; ℤ)` is in the class for `1 ≤ i ≤ k`
  (`TauCeti.isKilledBySomePower_singularHomology_nConnectedCover`).
* **The induction.** The cover `Z⟨n⟩` is `n`-connected and has the homotopy groups of `Z` above
  `n`, so the first step applies to it in degree `n + 1`. This is the shared induction along the
  Whitehead tower, `TauCeti.whiteheadTower_induction`.

## Main results

* `TauCeti.isKilledBySomePower_singularHomology_nConnectedCover`: the `n`-connected cover of an
  `(n - 1)`-connected Hausdorff space whose homology in degrees `1, …, k`, `2 ≤ n ≤ k`, is
  annihilated by powers of `d` has the same property.
* `TauCeti.isKilledBySomePower_homotopyGroup_of_isKilledBySomePower_singularHomology`: the
  homotopy groups `πᵢ(Y)`, `2 ≤ i ≤ k`, of a simply connected space whose homology in degrees
  `1, …, k` is annihilated by powers of `d` are annihilated by powers of `d`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Theorem 1 (the Hurewicz theorem modulo a class).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable {d : ℕ}

/-- The first possible homotopy group: the homotopy group `πₙ₊₂` of an `(n + 1)`-connected space
whose homology `Hₙ₊₂(-; ℤ)` is annihilated by some power of `d` is annihilated by some power of
`d`, by the Hurewicz theorem. -/
private theorem isKilledBySomePower_homotopyGroup_of_connected {Z : Type} [TopologicalSpace Z]
    [PathConnectedSpace Z] {z : Z} {n : ℕ}
    (hZ : ∀ q, q ≠ 0 → q < n + 2 → Subsingleton (π_ q Z z))
    (h : AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of Z)).homology (n + 2)))) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive (π_ (n + 2) Z z))) := by
  refine (AddCommGrpCat.isKilledBySomePower d).prop_of_iso
    (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv fun q hq ↦ ?_).symm.toAddCommGrpIso h
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
  · exact hZ q hq0 hq

/-- **The `n`-connected cover, modulo the groups annihilated by a power of `d`.** Let `X` be a
Hausdorff, path-connected space whose homotopy groups `π_q` vanish for `1 ≤ q < m + 2`, and whose
integral homology `H_q(X; ℤ)` is annihilated by some power of `d` for `1 ≤ q ≤ k`, where
`m + 2 ≤ k`. Then the integral homology of its `(m + 2)`-connected cover `X⟨m + 2⟩` is annihilated
by some power of `d` in the same degrees. -/
theorem isKilledBySomePower_singularHomology_nConnectedCover (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ) {k : ℕ} (hmk : m + 2 ≤ k)
    (hX : ∀ q, q ≠ 0 → q < m + 2 → Subsingleton (π_ q X x))
    (hXd : ∀ q, q ≠ 0 → q ≤ k → AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj X).homology q)))
    {q : ℕ} (hq0 : q ≠ 0) (hq : q ≤ k) :
    AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj (nConnectedCover (m + 2) X x)).homology q)) := by
  -- `πₘ₊₂(X)` is annihilated by a power of `d`, by the Hurewicz theorem.
  have hπ := isKilledBySomePower_homotopyGroup_of_connected (Z := X) (z := x) (n := m) hX
    (hXd (m + 2) (by omega) hmk)
  -- The Postnikov section `K` of `X` is a `K(πₘ₊₂(X), m + 2)`, so its loop space is a
  -- `K(πₘ₊₂(X), m + 1)`, and one power `d ^ M` annihilates the homology of every fibre of the
  -- cover in degrees `1, …, k`.
  have hK := (isEilenbergMacLaneSpace_killHomotopyGroups (m + 2) X x hX).of_mulEquiv
    (MulEquiv.multiplicativeAdditive _).symm
  have := hK.pathConnectedSpace
  obtain ⟨M, hM⟩ := exists_isKilledBy_singularHomology_of_homotopyEquiv
    (Y := fun b ↦ (nConnectedCoverProj (m + 2) X x).fiber b) (k := k)
    (fun b ↦ nConnectedCoverFiberHomotopyEquivLoopSpace (m + 2) X x b
      (PathConnectedSpace.somePath _ _))
    fun q hq0 _ ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      exact IsEilenbergMacLaneSpace.isKilledBySomePower_singularHomology hπ hK.loopSpace q
  -- So the projection is an isomorphism modulo the class on `H_q(-; ℤ)`.
  let P := (AddCommGrpCat.isKilledBySomePower d).inverseImage
    (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)
  have hiso := TauCeti.TopCat.isoModSerre_singularHomologyMap_of_prop_fiber P
    (ObjectProperty.isKilledBy (ModuleCat.{0} ℤ) (d ^ M))
    (AddCommGrpCat.isKilledBy_pow_le_inverseImage_isKilledBySomePower d M)
    (serreFibrations_nConnectedCoverProj (m + 2) X x) q
    (fun b ↦ (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX b).choose_spec
      |>.pathConnectedSpace)
    fun b j hj0 hj ↦ hM b j hj0 (hj.trans hq)
  exact P.prop_of_monoModSerre hiso.1 (hXd q hq0 hq)

/-- **The Hurewicz theorem modulo the groups annihilated by a power of `d`** (Serre). Let `Y` be a
simply connected space whose integral homology `Hᵢ(Y; ℤ)` is annihilated by some power of `d` for
every `1 ≤ i ≤ k`. Then every homotopy group `πᵢ(Y)`, `2 ≤ i ≤ k`, is annihilated by some power of
`d`. No finite generation or CW structure is assumed. -/
theorem isKilledBySomePower_homotopyGroup_of_isKilledBySomePower_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] {k : ℕ}
    (hY : ∀ i, i ≠ 0 → i ≤ k → AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of Y)).homology i)))
    (y : Y) {n : ℕ} (hn : n + 2 ≤ k) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive (π_ (n + 2) Y y))) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (q : ℕ) (hq0 : q ≠ 0) (hq : q < 2) : Subsingleton (π_ q Y y) := by
    obtain rfl : q = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  refine whiteheadTower_induction (N := n)
    (fun X ↦ ∀ q, q ≠ 0 → q ≤ k → AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((singularChains ℤ).obj X).homology q)))
    (fun G _ ↦ AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (Additive G)))
    (fun _ _ f hf hd q hq0 hq ↦ ?_)
    (fun _ _ _ _ e ↦
      (AddCommGrpCat.isKilledBySomePower d).prop_of_iso e.toAdditive.toAddCommGrpIso)
    (fun _ hZ hZd ↦ isKilledBySomePower_homotopyGroup_of_connected hZ (hZd _ (by omega) hn))
    (fun m _ X _ _ x hX hXd _ hq0 hq ↦
      isKilledBySomePower_singularHomology_nConnectedCover X x m (by omega) hX hXd hq0 hq)
    (Nat.zero_le n) y h₁ hY
  -- A weak homotopy equivalence is a homology isomorphism.
  exact ((AddCommGrpCat.isKilledBySomePower d).inverseImage
    (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)).prop_of_iso
    (@asIso _ _ _ _ _ (hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) q)).symm (hd q hq0 hq)

end TauCeti
