/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.SerreClass.Torsion
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.AlgebraicTopology.EilenbergMacLane.SerreClass
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# From homotopy groups to homology modulo a Serre class

**Theorem** (Serre). Let `P` be a Serre class of abelian groups and `Y` a simply connected space
whose homotopy groups `πᵢ(Y)` lie in `P` for `2 ≤ i ≤ k`. Then the integral homology groups
`Hᵢ(Y; ℤ)` lie in `P` for `1 ≤ i ≤ k`
(`TauCeti.prop_singularHomology_of_prop_homotopyGroup`). This is the direction "homotopy in `P`
implies homology in `P`" of Serre's Hurewicz theorem modulo a class (Theorem 5.12 of
Barraud–Damian–Humilière–Oancea). No finite generation and no CW structure is assumed. For the
class of torsion groups: a simply connected space with torsion homotopy groups through degree `k`
has torsion integral homology through degree `k`
(`TauCeti.isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup`).

The class must satisfy Serre's axiom on Eilenberg--Mac Lane spaces: a `K(G, n)` space with
`G ∈ P` has its positive-degree homology in `P`. As in the comparison theorem for Serre fibrations
modulo a class (`TauCeti.TopCat.isoModSerre_singularHomologyMap_of_prop_fiber`), the homology of
the fibres is asked to lie in a property `Q ≤ P` closed under direct sums. Only the degrees
`1, …, k` matter, and `Q` may be chosen separately for each `G` and `n`, so `P` need not be closed
under infinite direct sums. For the groups annihilated by some power of `d`, `Q` can be the groups
annihilated by a single power `dᴺ`: all `K(G, n + 1)` spaces have isomorphic homology, so in the
finitely many degrees `1, …, k` it is annihilated by one power of `d` as soon as each degree lies
in the class. When `P` itself is closed under direct sums, the axiom for `K(G, 1)` spaces implies
it for all `K(G, n)`, through the based path fibrations `K(G, n) → E → K(G, n + 1)` with
contractible total space (`TauCeti.IsEilenbergMacLaneSpace.prop_singularHomology_of_one`).

The proof climbs the Whitehead tower.

* **Top of the tower.** A `k`-connected space has no homology in the positive degrees at most
  `k` (`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`).
* **One step down.** If `Z` is `(n - 1)`-connected, `n ≥ 2`, the `n`-connected cover
  `Z⟨n⟩ → Z` is a fibration with `K(πₙ Z, n - 1)` fibres
  (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). When the homology of these
  fibres lies in `Q ≤ P`, it is an isomorphism on homology modulo `P`, so the homology of `Z` lies
  in `P` wherever that of `Z⟨n⟩` does (`TauCeti.prop_singularHomology_of_nConnectedCover`). The
  induction supplies such a `Q` because `πₙ Z ∈ P`.
* **The induction.** `Z⟨n⟩` is `n`-connected and has the homotopy groups of `Z` above `n`. Each
  stage is replaced by its CW approximation, which is Hausdorff and changes neither homotopy nor
  homology.

The converse direction, from homology to homotopy, and the comparison of `πₖ` with `Hₖ` modulo
`P` are not treated here.

## Main results

* `TauCeti.prop_singularHomology_of_nConnectedCover`: one step down the Whitehead tower.
* `TauCeti.prop_singularHomology_of_prop_homotopyGroup`: Serre's theorem, homotopy groups in `P`
  through degree `k` give homology in `P` through degree `k`.
* `TauCeti.isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup`: torsion homotopy groups
  through degree `k` give torsion homology through degree `k`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Spectral Sequences in Algebraic Topology*, Chapter 1 (Serre classes).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.12.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

/-! ### One step down the tower -/

variable (P Q : ObjectProperty (ModuleCat.{0} ℤ)) [P.IsSerreClass] [Q.IsClosedUnderIsomorphisms]
  [Q.ContainsZero] [∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)]

/-- **One step down the Whitehead tower.** Let `X` be a Hausdorff path-connected space whose
homotopy groups `πⱼ` vanish for `1 ≤ j < m + 2`, and suppose that the homology in degrees
`1, …, i` of every `K(πₘ₊₂(X), m + 1)` space lies in `Q ≤ P`. Then the homology `Hᵢ(X; ℤ)`
lies in `P` whenever the homology of the `(m + 2)`-connected cover `X⟨m + 2⟩` does. -/
theorem prop_singularHomology_of_nConnectedCover (hQP : Q ≤ P) (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m i : ℕ)
    (hX : ∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k X x))
    (hK : ∀ (Z : Type) [TopologicalSpace Z] (z : Z),
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Z z → ∀ q, q ≠ 0 → q ≤ i →
        Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of Z)))
    (hC : P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
      (nConnectedCover (m + 2) X x))) :
    P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj X) := by
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)
  let p := nConnectedCoverProj (m + 2) X x
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space.
  have hfib (b : X) := isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX b
  -- So the projection is an isomorphism on homology modulo `P`.
  have hiso := TopCat.isoModSerre_singularHomologyMap_of_prop_fiber P Q hQP
    (serreFibrations_nConnectedCoverProj (m + 2) X x) i
    (fun b ↦ (hfib b).choose_spec.pathConnectedSpace)
    (fun b q hq0 hqi ↦ hK _ _ (hfib b).choose_spec q hq0 hqi)
  -- `Hᵢ(X⟨m + 2⟩) ⟶ Hᵢ(X) ⟶ coker` is exact, with both ends in `P`.
  exact P.prop_X₂_of_exact (ShortComplex.exact_cokernel (H.map p)) hC hiso.2

/-! ### The induction -/

/-- **Hausdorff models.** A statement about the homology of a path-connected space `Z` holds as
soon as it holds for every Hausdorff path-connected space with the homotopy groups of `Z`: its CW
approximation is such a space, with the homology of `Z`. -/
private theorem prop_singularHomology_of_cwApproximation {Z : Type} [TopologicalSpace Z]
    [PathConnectedSpace Z] (z : Z) (i : ℕ)
    (h : ∀ (X : TopCat.{0}) [T2Space X] [PathConnectedSpace X] (x₀ : X),
      (∀ j [NeZero j], Nonempty (π_ j X x₀ ≃* π_ j Z z)) →
        P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj X)) :
    P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of Z)) := by
  let f := cwApproximationMap (TopCat.of Z) z
  have hf : f.hom.IsWeakHomotopyEquivalence :=
    isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Z) z
  have : PathConnectedSpace (cwApproximation (TopCat.of Z) z) :=
    hf.pathConnectedSpace_iff.2 inferInstance
  -- `f` is a homology isomorphism, and identifies the homotopy groups at the base points.
  have := hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) i
  refine P.prop_of_iso (asIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj
    (ModuleCat.of ℤ ℤ)).map f)) (h _ (cwApproximationBasepoint (TopCat.of Z) z) fun j _ ↦ ?_)
  exact ⟨cwApproximationHomotopyGroupMulEquiv (TopCat.of Z) z j⟩

/-- The induction along the Whitehead tower: for an `(n + 1)`-connected space whose homotopy
groups `π_{j + 2}` lie in `P` for `n ≤ j` and `j + 2 ≤ k`, the homology `Hᵢ` lies in `P` for
`0 < i ≤ k`. The number of homotopy groups still to be killed is `d = k - n`, by induction on
`d`. -/
private theorem prop_singularHomology_of_add (k : ℕ)
    (hK : ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ n : ℕ,
      ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
        Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
        ∀ (Z : Type) [TopologicalSpace Z] (z : Z), IsEilenbergMacLaneSpace G (n + 1) Z z →
          ∀ q, q ≠ 0 → q ≤ k →
            Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
              (TopCat.of Z)))
    (d : ℕ) :
    ∀ (n : ℕ) {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z),
      k ≤ n + 1 + d →
      (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
      (∀ j, n ≤ j → j + 2 ≤ k → P (ModuleCat.of ℤ (Additive (π_ (j + 2) Z z)))) →
        ∀ i, i ≠ 0 → i ≤ k →
          P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
            (TopCat.of Z)) := by
  induction d with
  | zero =>
    -- No homotopy group is left: `Z` is `k`-connected, so its homology vanishes up to `k`.
    intro n Z _ _ z hkn hZ _ i hi0 hik
    refine P.prop_of_isZero (isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup
      (X := TopCat.of Z) (n := n + 2) (x := z) (fun j hj ↦ ?_) ℤ hi0 (by omega))
    rcases eq_or_ne j 0 with rfl | hj0
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
    · exact hZ j hj0 hj
  | succ d ih =>
    intro n Z _ _ z hkn hZ hπ i hi0 hik
    -- Replace `Z` by a Hausdorff model `X` with the same homotopy groups.
    refine prop_singularHomology_of_cwApproximation P z i fun X _ _ x₀ e ↦ ?_
    have hX : ∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j X x₀) := fun j hj0 hj ↦ by
      have : NeZero j := ⟨hj0⟩
      have := hZ j hj0 hj
      exact (e j).some.toEquiv.subsingleton
    have hπX (j : ℕ) (hj : n ≤ j) (hjk : j + 2 ≤ k) :
        P (ModuleCat.of ℤ (Additive (π_ (j + 2) X x₀))) :=
      P.prop_of_iso (LinearEquiv.toModuleIso (e (j + 2)).some.toAdditive.toIntLinearEquiv).symm
        (hπ j hj hjk)
    rcases lt_or_ge k (n + 2) with hkn' | hkn'
    · -- No homotopy group of `X` in the range is left: `X` is `k`-connected.
      exact ih n x₀ (by omega) hX (fun j hj hjk ↦ hπX j hj hjk) i hi0 hik
    -- The `(n + 2)`-connected cover `C` of `X` is `(n + 2)`-connected.
    let C := nConnectedCover (n + 2) X x₀
    let c₀ := nConnectedCoverBasepoint (n + 2) X x₀
    have hC : ∀ j, j ≠ 0 → j < n + 1 + 2 → Subsingleton (π_ j C c₀) := fun j _ hj ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2) X x₀ c₀
        (by omega)
    -- The cover has the homotopy groups of `X` above dimension `n + 2`.
    have hπC (j : ℕ) (hj : n + 1 ≤ j) (hjk : j + 2 ≤ k) :
        P (ModuleCat.of ℤ (Additive (π_ (j + 2) C c₀))) :=
      P.prop_of_iso (LinearEquiv.toModuleIso
        (nConnectedCoverHomotopyGroupMulEquiv (n + 2) X x₀ (j + 2)
          (by omega)).toAdditive.toIntLinearEquiv).symm (hπX j (by omega) hjk)
    -- The fibres are `K(πₙ₊₂(X), n + 1)` spaces, with homology through degree `k` in some `Q`.
    obtain ⟨Q, hQP, _, _, _, hQ⟩ := hK _ (hπX n le_rfl hkn') n
    refine prop_singularHomology_of_nConnectedCover P Q hQP X x₀ n i hX
      (fun Z' _ z' hZ' q hq hqi ↦ hQ Z' z' hZ' q hq (hqi.trans hik)) ?_
    exact ih (n + 1) c₀ (by omega) hC hπC i hi0 hik

/-- **Serre's Hurewicz theorem modulo a class, from homotopy to homology.** Let `P` be a Serre
class of abelian groups such that for every `G ∈ P` and `n ≥ 1` there is a property `Q ≤ P`
closed under isomorphisms and direct sums containing the integral homology in degrees `1, …, k`
of every `K(G, n)` space. Let `Y` be a simply connected space whose homotopy groups `πᵢ(Y)` lie
in `P` for `2 ≤ i ≤ k`. Then `Hᵢ(Y; ℤ)` lies in `P` for `1 ≤ i ≤ k`. -/
theorem prop_singularHomology_of_prop_homotopyGroup (k : ℕ)
    (hK : ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ n : ℕ,
      ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
        Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
        ∀ (Z : Type) [TopologicalSpace Z] (z : Z), IsEilenbergMacLaneSpace G (n + 1) Z z →
          ∀ q, q ≠ 0 → q ≤ k →
            Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
              (TopCat.of Z)))
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y)
    (hY : ∀ j, j + 2 ≤ k → P (ModuleCat.of ℤ (Additive (π_ (j + 2) Y y))))
    {i : ℕ} (hi0 : i ≠ 0) (hik : i ≤ k) :
    P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of Y)) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j Y y) := by
    obtain rfl : j = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  exact prop_singularHomology_of_add P k hK k 0 y (by omega) h₁
    (fun j _ hjk ↦ hY j hjk) i hi0 hik

/-! ### Torsion homotopy groups -/

/-- **Torsion homotopy groups give torsion homology** (Serre). Let `Y` be a simply connected space
whose homotopy groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ k`. Then the integral homology
groups `Hᵢ(Y; ℤ)` are torsion groups for `1 ≤ i ≤ k`. This is the case of the Serre class of
torsion groups, for which Serre's axiom holds because the positive-degree homology of the
classifying space of a torsion abelian group is torsion. -/
theorem isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) (k : ℕ)
    (hY : ∀ j, j + 2 ≤ k → IsMulTorsion (π_ (j + 2) Y y)) {i : ℕ} (hi0 : i ≠ 0) (hik : i ≤ k) :
    IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology i) := by
  -- The torsion `ℤ`-modules, as an object property of `ModuleCat ℤ`.
  have hP (M : ModuleCat.{0} ℤ) :
      (AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)) M ↔
        IsAddTorsion M :=
    (ObjectProperty.prop_inverseImage_iff _ _ _).trans (AddCommGrpCat.prop_isTorsion_iff _)
  rw [← singularHomologyFunctor_obj_obj]
  refine (hP _).1 (prop_singularHomology_of_prop_homotopyGroup _ k ?_ y
    (fun j hj ↦ (hP _).2 fun a : Additive (π_ (j + 2) Y y) ↦
      (isOfFinAddOrder_ofMul_iff (x := a.toMul)).2 (hY j hj _)) hi0 hik)
  -- Torsion groups are closed under direct sums, so they serve as `Q` at every stage.
  intro G _ hG n
  refine ⟨_, le_rfl, inferInstance, inferInstance, inferInstance, fun Z _ z hZ q hq _ ↦ ?_⟩
  refine IsEilenbergMacLaneSpace.prop_singularHomology_of_one _ (fun Z _ z hZ q hq ↦ ?_) n hZ hq
  -- A `K(G, 1)` space receives a weak homotopy equivalence from the classifying space of `G`,
  -- a locally finite group.
  have : Group.IsLocallyFinite G := Group.isLocallyFinite_iff_isMulTorsion.2 fun g ↦
    isOfFinAddOrder_ofMul_iff.1 ((hP _).1 hG (Additive.ofMul g))
  obtain ⟨f, hf⟩ :=
    (isEilenbergMacLaneSpace_one_iff.1 hZ).exists_isWeakHomotopyEquivalence_classifyingSpace
  have := hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) q
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact ObjectProperty.prop_of_iso _ (asIso (((singularHomologyFunctor (ModuleCat.{0} ℤ)
    (q + 1)).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)))
    ((hP _).2 (by
      rw [singularHomologyFunctor_obj_obj]
      exact isAddTorsion_classifyingSpace_singularHomology ℤ q))

end TauCeti
