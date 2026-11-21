/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.SerreClass.Torsion
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.AlgebraicTopology.EilenbergMacLane.SerreClass
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Serre's Hurewicz theorem modulo a class

**Theorem** (Serre). Let `P` be a Serre class of abelian groups and `Y` a simply connected space
whose homotopy groups `πᵢ(Y)` lie in `P` for `2 ≤ i ≤ k`. Then the integral homology groups
`Hᵢ(Y; ℤ)` lie in `P` for `1 ≤ i ≤ k`
(`TauCeti.prop_singularHomology_of_prop_homotopyGroup`), and the Hurewicz map
`πₖ₊₁(Y) → Hₖ₊₁(Y; ℤ)` is an isomorphism modulo `P`: its kernel and cokernel lie in `P`
(`TauCeti.isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup`). This is Serre's Hurewicz
theorem modulo a class: its direction "homotopy in `P` implies homology in `P`" (Theorem 5.12 of
Barraud–Damian–Humilière–Oancea) and its comparison of `πₖ₊₁` with `Hₖ₊₁`. No finite generation
and no CW structure is assumed. For the class of torsion groups: a simply connected space with
torsion homotopy groups through degree `k` has torsion integral homology through degree `k`
(`TauCeti.isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup`), and its Hurewicz map in
degree `k + 1` has torsion kernel and cokernel
(`TauCeti.isoModSerre_hurewiczModuleCatHom_of_isMulTorsion_homotopyGroup`). The Hurewicz map is
read as a morphism of `ModuleCat ℤ` (`HomotopyGroup.hurewiczModuleCatHom`), so that being an
isomorphism modulo `P` is Mathlib's `CategoryTheory.ObjectProperty.isoModSerre`.

The class must satisfy Serre's axiom on Eilenberg--Mac Lane spaces: a `K(G, n)` space with `G ∈ P`
has its positive-degree homology in `P`. As in the comparison theorem for Serre fibrations modulo a
class (`TauCeti.TopCat.isoModSerre_singularHomologyMap_of_prop_fiber`), the homology of the fibres
is asked to lie in a property `Q ≤ P` closed under direct sums
(`CategoryTheory.ObjectProperty.SatisfiesEilenbergMacLaneAxiom`). Only finitely many degrees matter:
`1, …, k` for the homology statement and `1, …, k + 1` for the Hurewicz comparison in degree
`k + 1`. `Q` may be chosen separately for each `G` and `n`, so `P` need not be closed under infinite
direct sums. For the groups annihilated by some power of `d`, `Q` can be the groups annihilated by a
single power `dᴺ`: all `K(G, n + 1)` spaces have isomorphic homology, so in finitely many degrees
(`1, …, k` or `1, …, k + 1`) it is annihilated by one power of `d` as soon as each degree lies in
the class. When `P` itself is closed under direct sums, the axiom for `K(G, 1)` spaces implies it
for all `K(G, n)`, through the based path fibrations `K(G, n) → E → K(G, n + 1)` with contractible
total space (`TauCeti.IsEilenbergMacLaneSpace.prop_singularHomology_of_one`).

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

The comparison climbs the same tower. Each projection `Z⟨n⟩ → Z` with `n ≤ k` is bijective on
`πₖ₊₁` and an isomorphism modulo `P` on `Hₖ₊₁`, and the Hurewicz map is natural, so the Hurewicz
map of `Z` is an isomorphism modulo `P` as soon as that of `Z⟨n⟩` is. At the top of the tower the
stage is `k`-connected and the ordinary Hurewicz theorem
(`HomotopyGroup.hurewiczAddEquiv`) makes the Hurewicz map an isomorphism.

The converse direction, from homology to homotopy, is not treated here.

## Main results

* `CategoryTheory.ObjectProperty.SatisfiesEilenbergMacLaneAxiom`: Serre's axiom on
  Eilenberg--Mac Lane spaces through a given degree, the hypothesis on the class, unfolded by
  `CategoryTheory.ObjectProperty.satisfiesEilenbergMacLaneAxiom_iff`.
* `TauCeti.prop_singularHomology_of_nConnectedCover`: one step down the Whitehead tower.
* `TauCeti.prop_singularHomology_of_prop_homotopyGroup`: Serre's theorem, homotopy groups in `P`
  through degree `k` give homology in `P` through degree `k`.
* `TauCeti.isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup`: Serre's theorem, homotopy
  groups in `P` through degree `k` make the Hurewicz map in degree `k + 1` an isomorphism
  modulo `P`.
* `TauCeti.satisfiesEilenbergMacLaneAxiom_isTorsion`: the torsion groups satisfy the axiom in
  every degree.
* `TauCeti.isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup`: torsion homotopy groups
  through degree `k` give torsion homology through degree `k`.
* `TauCeti.isoModSerre_hurewiczModuleCatHom_of_isMulTorsion_homotopyGroup`: torsion homotopy
  groups through degree `k` make the Hurewicz map in degree `k + 1` an isomorphism modulo torsion.

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

namespace CategoryTheory.ObjectProperty

/-- **Serre's axiom on Eilenberg--Mac Lane spaces through degree `k`**, in the form taken by
Serre's Hurewicz theorem modulo `P`: for every `G ∈ P` and `m ≥ 1` there is a property `Q ≤ P`
of `ℤ`-modules, closed under isomorphisms and direct sums and containing zero, which contains
the integral homology in degrees `1, …, k` of every `K(G, m)` space. -/
def SatisfiesEilenbergMacLaneAxiom (P : ObjectProperty (ModuleCat.{0} ℤ)) (k : ℕ) : Prop :=
  ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ m : ℕ,
    ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
      Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
      ∀ (Z : Type) [TopologicalSpace Z] (z : Z), TauCeti.IsEilenbergMacLaneSpace G (m + 1) Z z →
        ∀ q, q ≠ 0 → q ≤ k →
          Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
            (TopCat.of Z))

/-- Unfolding `ObjectProperty.SatisfiesEilenbergMacLaneAxiom`: the class `P` satisfies Serre's
axiom through degree `k` exactly when every `G ∈ P` and `m` admit a property `Q ≤ P`, closed
under isomorphisms and direct sums and containing zero, which contains the integral homology in
degrees `1, …, k` of every `K(G, m + 1)` space. -/
theorem satisfiesEilenbergMacLaneAxiom_iff (P : ObjectProperty (ModuleCat.{0} ℤ)) (k : ℕ) :
    P.SatisfiesEilenbergMacLaneAxiom k ↔
      ∀ (G : Type) [CommGroup G], P (ModuleCat.of ℤ (Additive G)) → ∀ m : ℕ,
        ∃ Q : ObjectProperty (ModuleCat.{0} ℤ), Q ≤ P ∧ Q.IsClosedUnderIsomorphisms ∧
          Q.ContainsZero ∧ (∀ J : Type, Q.IsClosedUnderColimitsOfShape (Discrete J)) ∧
          ∀ (Z : Type) [TopologicalSpace Z] (z : Z),
            TauCeti.IsEilenbergMacLaneSpace G (m + 1) Z z → ∀ q, q ≠ 0 → q ≤ k →
              Q (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
                (TopCat.of Z)) :=
  Iff.rfl

end CategoryTheory.ObjectProperty

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

/-- **Hausdorff models.** The CW approximation of a path-connected space `Z` is a Hausdorff
path-connected space with the homotopy groups of `Z`
(`TauCeti.cwApproximationHomotopyGroupMulEquiv`), and its map to `Z` is an isomorphism on integral
homology. -/
private theorem cwApproximation_pathConnectedSpace_and_isIso {Z : Type} [TopologicalSpace Z]
    [PathConnectedSpace Z] (z : Z) :
    PathConnectedSpace (cwApproximation (TopCat.of Z) z) ∧ ∀ i,
      IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).map
        (cwApproximationMap (TopCat.of Z) z)) := by
  have hf := isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Z) z
  exact ⟨hf.pathConnectedSpace_iff.2 inferInstance,
    fun i ↦ hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) i⟩

/-- A statement about the homology of a path-connected space `Z` holds as soon as it holds for
every Hausdorff path-connected space with the homotopy groups of `Z`: its CW approximation is such
a space, with the homology of `Z`. -/
private theorem prop_singularHomology_of_cwApproximation {Z : Type} [TopologicalSpace Z]
    [PathConnectedSpace Z] (z : Z) (i : ℕ)
    (h : ∀ (X : TopCat.{0}) [T2Space X] [PathConnectedSpace X] (x₀ : X),
      (∀ j [NeZero j], Nonempty (π_ j X x₀ ≃* π_ j Z z)) →
        P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj X)) :
    P (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of Z)) := by
  obtain ⟨_, hH⟩ := cwApproximation_pathConnectedSpace_and_isIso z
  have := hH i
  exact P.prop_of_iso (asIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj
    (ModuleCat.of ℤ ℤ)).map (cwApproximationMap (TopCat.of Z) z)))
    (h _ (cwApproximationBasepoint (TopCat.of Z) z) fun j _ ↦
      ⟨cwApproximationHomotopyGroupMulEquiv (TopCat.of Z) z j⟩)

/-- **Passing to a model.** If the homotopy groups of `X` in positive degrees are isomorphic to
those of `Z`, then `X` is `(j + 1)`-connected and has its homotopy groups `π_{i + 2}` in `P` for
`j ≤ i` and `i + 2 ≤ k` as soon as `Z` does. -/
private theorem subsingleton_and_prop_homotopyGroup_of_mulEquiv {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] {x : X} {z : Z} (e : ∀ i [NeZero i], Nonempty (π_ i X x ≃* π_ i Z z))
    {j k : ℕ} (hZ : ∀ i, i ≠ 0 → i < j + 2 → Subsingleton (π_ i Z z))
    (hπ : ∀ i, j ≤ i → i + 2 ≤ k → P (ModuleCat.of ℤ (Additive (π_ (i + 2) Z z)))) :
    (∀ i, i ≠ 0 → i < j + 2 → Subsingleton (π_ i X x)) ∧
      ∀ i, j ≤ i → i + 2 ≤ k → P (ModuleCat.of ℤ (Additive (π_ (i + 2) X x))) := by
  refine ⟨fun i hi0 hi ↦ ?_, fun i hji hik ↦ ?_⟩
  · have : NeZero i := ⟨hi0⟩
    have := hZ i hi0 hi
    exact (e i).some.toEquiv.subsingleton
  · exact P.prop_of_iso (LinearEquiv.toModuleIso (e (i + 2)).some.toAdditive.toIntLinearEquiv).symm
      (hπ i hji hik)

/-- **The next stage of the tower.** The `(j + 2)`-connected cover of a Hausdorff path-connected
space `X` is `(j + 2)`-connected, and has its homotopy groups `π_{i + 2}` in `P` for `j < i` and
`i + 2 ≤ k` as soon as `X` has them in `P` for `j ≤ i` and `i + 2 ≤ k`. -/
private theorem subsingleton_and_prop_homotopyGroup_nConnectedCover (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x₀ : X) {j k : ℕ}
    (hπ : ∀ i, j ≤ i → i + 2 ≤ k → P (ModuleCat.of ℤ (Additive (π_ (i + 2) X x₀)))) :
    (∀ i, i ≠ 0 → i < j + 1 + 2 →
      Subsingleton (π_ i (nConnectedCover (j + 2) X x₀) (nConnectedCoverBasepoint (j + 2) X x₀))) ∧
      ∀ i, j + 1 ≤ i → i + 2 ≤ k → P (ModuleCat.of ℤ (Additive
        (π_ (i + 2) (nConnectedCover (j + 2) X x₀) (nConnectedCoverBasepoint (j + 2) X x₀)))) :=
  ⟨fun _ _ hi ↦ subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (j + 2) X x₀ _
      (by omega),
    fun i hji hik ↦ P.prop_of_iso (LinearEquiv.toModuleIso
      (nConnectedCoverHomotopyGroupMulEquiv (j + 2) X x₀ (i + 2)
        (by omega)).toAdditive.toIntLinearEquiv).symm (hπ i (by omega) hik)⟩

/-- The induction along the Whitehead tower: for an `(n + 1)`-connected space whose homotopy
groups `π_{j + 2}` lie in `P` for `n ≤ j` and `j + 2 ≤ k`, the homology `Hᵢ` lies in `P` for
`0 < i ≤ k`. The number of homotopy groups still to be killed is `d = k - n`, by induction on
`d`. -/
private theorem prop_singularHomology_of_add (k : ℕ)
    (hK : P.SatisfiesEilenbergMacLaneAxiom k) (d : ℕ) :
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
    obtain ⟨hX, hπX⟩ := subsingleton_and_prop_homotopyGroup_of_mulEquiv P e hZ hπ
    rcases lt_or_ge k (n + 2) with hkn' | hkn'
    · -- No homotopy group of `X` in the range is left: `X` is `k`-connected.
      exact ih n x₀ (by omega) hX hπX i hi0 hik
    -- The `(n + 2)`-connected cover of `X` is `(n + 2)`-connected, with the homotopy groups of `X`
    -- above dimension `n + 2`.
    obtain ⟨hC, hπC⟩ := subsingleton_and_prop_homotopyGroup_nConnectedCover P X x₀ hπX
    -- The fibres are `K(πₙ₊₂(X), n + 1)` spaces, with homology through degree `k` in some `Q`.
    obtain ⟨Q, hQP, _, _, _, hQ⟩ :=
      (P.satisfiesEilenbergMacLaneAxiom_iff k).1 hK _ (hπX n le_rfl hkn') n
    refine prop_singularHomology_of_nConnectedCover P Q hQP X x₀ n i hX
      (fun Z' _ z' hZ' q hq hqi ↦ hQ Z' z' hZ' q hq (hqi.trans hik)) ?_
    exact ih (n + 1) _ (by omega) hC hπC i hi0 hik

/-- **Serre's Hurewicz theorem modulo a class, from homotopy to homology.** Let `P` be a Serre
class of abelian groups such that for every `G ∈ P` and `n ≥ 1` there is a property `Q ≤ P`
closed under isomorphisms and direct sums containing the integral homology in degrees `1, …, k`
of every `K(G, n)` space. Let `Y` be a simply connected space whose homotopy groups `πᵢ(Y)` lie
in `P` for `2 ≤ i ≤ k`. Then `Hᵢ(Y; ℤ)` lies in `P` for `1 ≤ i ≤ k`. -/
theorem prop_singularHomology_of_prop_homotopyGroup (k : ℕ)
    (hK : P.SatisfiesEilenbergMacLaneAxiom k)
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

/-! ### The Hurewicz map modulo a class -/

variable {P} in
/-- **Naturality of the Hurewicz map modulo `P`.** Along a based map `f : (X, x) → (Z, z)` which is
bijective on `πₙ₊₂` and an isomorphism modulo `P` on `Hₙ₊₂`, the Hurewicz map of `Z` in degree
`n + 2` is an isomorphism modulo `P` as soon as that of `X` is. -/
private theorem isoModSerre_hurewiczModuleCatHom_of_map {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] {x : X} {z : Z} {n : ℕ} (f : C(X, Z)) (hf : f x = z)
    (hπ : Function.Bijective (HomotopyGroup.map (N := Fin (n + 2)) f hf))
    (hH : P.isoModSerre (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)))
    (hX : P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom X x n)) :
    P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom Z z n) := by
  let e : ModuleCat.of ℤ (Additive (π_ (n + 2) X x)) ⟶ ModuleCat.of ℤ (Additive (π_ (n + 2) Z z)) :=
    ModuleCat.ofHom (HomotopyGroup.mapHom f hf).toAdditive.toIntLinearMap
  have : IsIso e := (ConcreteCategory.isIso_iff_bijective e).2
    (Additive.ofMul.bijective.comp (hπ.comp Additive.toMul.bijective))
  rw [← IsIso.inv_hom_id_assoc e (HomotopyGroup.hurewiczModuleCatHom Z z n),
    HomotopyGroup.hurewiczModuleCatHom_naturality]
  exact P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _) (P.isoModSerre.comp_mem _ _ hX hH)

/-- The Hurewicz map of an `(n + 1)`-connected space is an isomorphism, hence an isomorphism
modulo `P`. -/
private theorem isoModSerre_hurewiczModuleCatHom_of_subsingleton {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (hX : ∀ k < n + 2, Subsingleton (π_ k X x)) :
    P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom X x n) := by
  have : IsIso (HomotopyGroup.hurewiczModuleCatHom X x n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 <| by
      convert (HomotopyGroup.hurewiczAddEquiv hX).bijective using 1
      funext a
      exact (HomotopyGroup.hurewiczModuleCatHom_apply X x n a).trans
        (HomotopyGroup.hurewiczAddEquiv_apply_eq_hurewiczIntHom hX a).symm
  exact P.isoModSerre_of_isIso _

/-- The Hurewicz map of a path-connected space `Z` is an isomorphism modulo `P` as soon as it is
for every Hausdorff path-connected space with the homotopy groups of `Z`: the CW approximation of
`Z` is such a space, and its map to `Z` is bijective on homotopy groups and on homology. -/
private theorem isoModSerre_hurewiczModuleCatHom_of_cwApproximation {Z : Type}
    [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ)
    (h : ∀ (X : TopCat.{0}) [T2Space X] [PathConnectedSpace X] (x₀ : X),
      (∀ j [NeZero j], Nonempty (π_ j X x₀ ≃* π_ j Z z)) →
        P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom X x₀ n)) :
    P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom Z z n) := by
  obtain ⟨_, hH⟩ := cwApproximation_pathConnectedSpace_and_isIso z
  have := hH (n + 2)
  refine isoModSerre_hurewiczModuleCatHom_of_map (cwApproximationMap (TopCat.of Z) z).hom
    (cwApproximationMap_cwApproximationBasepoint (TopCat.of Z) z) ?_ (P.isoModSerre_of_isIso _)
    (h _ (cwApproximationBasepoint (TopCat.of Z) z) fun j _ ↦
      ⟨cwApproximationHomotopyGroupMulEquiv (TopCat.of Z) z j⟩)
  convert (cwApproximationHomotopyGroupMulEquiv (TopCat.of Z) z (n + 2)).bijective using 1
  funext a
  exact (cwApproximationHomotopyGroupMulEquiv_apply (TopCat.of Z) z (n + 2) a).symm

/-- The induction along the Whitehead tower: for a `(j + 1)`-connected space whose homotopy groups
`π_{i + 2}` lie in `P` for `j ≤ i < n`, the Hurewicz map `πₙ₊₂ → Hₙ₊₂` is an isomorphism modulo
`P`. The number of homotopy groups still to be killed is at most `d`, by induction on `d`. -/
private theorem isoModSerre_hurewiczModuleCatHom_of_add (n : ℕ)
    (hK : P.SatisfiesEilenbergMacLaneAxiom (n + 2)) (d : ℕ) :
    ∀ (j : ℕ) {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z),
      n ≤ j + d →
      (∀ i, i ≠ 0 → i < j + 2 → Subsingleton (π_ i Z z)) →
      (∀ i, j ≤ i → i + 2 ≤ n + 1 → P (ModuleCat.of ℤ (Additive (π_ (i + 2) Z z)))) →
        P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom Z z n) := by
  induction d with
  | zero =>
    -- No homotopy group is left: `Z` is `(n + 1)`-connected, and Hurewicz is an isomorphism.
    intro j Z _ _ z hnj hZ _
    refine isoModSerre_hurewiczModuleCatHom_of_subsingleton P fun i hi ↦ ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
    · exact hZ i hi0 (by omega)
  | succ d ih =>
    intro j Z _ _ z hnj hZ hπ
    -- Replace `Z` by a Hausdorff model `X` with the same homotopy groups.
    refine isoModSerre_hurewiczModuleCatHom_of_cwApproximation P z n fun X _ _ x₀ e ↦ ?_
    obtain ⟨hX, hπX⟩ := subsingleton_and_prop_homotopyGroup_of_mulEquiv P e hZ hπ
    rcases le_or_gt n j with hnj' | hjn
    · -- No homotopy group of `X` in the range is left: `X` is `(n + 1)`-connected.
      exact ih j x₀ (by omega) hX hπX
    -- The `(j + 2)`-connected cover of `X` is `(j + 2)`-connected, with the homotopy groups of `X`
    -- above dimension `j + 2`.
    obtain ⟨hC, hπC⟩ := subsingleton_and_prop_homotopyGroup_nConnectedCover P X x₀ hπX
    -- The fibres of `X⟨j + 2⟩ → X` are `K(π_{j + 2}(X), j + 1)` spaces, with homology in some
    -- `Q ≤ P` through degree `n + 2`, so the projection is an isomorphism on `Hₙ₊₂` modulo `P`.
    obtain ⟨Q, hQP, _, _, _, hQ⟩ :=
      (P.satisfiesEilenbergMacLaneAxiom_iff (n + 2)).1 hK _ (hπX j le_rfl (by omega)) j
    have hfib (b : X) := isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x₀ j hX b
    refine isoModSerre_hurewiczModuleCatHom_of_map (nConnectedCoverProj (j + 2) X x₀).hom
      (nConnectedCoverProj_nConnectedCoverBasepoint (j + 2) X x₀)
      (bijective_homotopyGroupMap_nConnectedCoverProj (j + 2) X x₀ _ _ (by omega))
      (TopCat.isoModSerre_singularHomologyMap_of_prop_fiber P Q hQP
        (serreFibrations_nConnectedCoverProj (j + 2) X x₀) (n + 2)
        (fun b ↦ (hfib b).choose_spec.pathConnectedSpace)
        (fun b q hq0 hqn ↦ hQ _ _ (hfib b).choose_spec q hq0 hqn))
      (ih (j + 1) _ (by omega) hC hπC)

/-- **Serre's Hurewicz theorem modulo a class.** Let `P` be a Serre class of abelian groups such
that for every `G ∈ P` and `m ≥ 1` there is a property `Q ≤ P` closed under isomorphisms and
direct sums containing the integral homology in degrees `1, …, n + 2` of every `K(G, m)` space.
Let `Y` be a simply connected space whose homotopy groups `πᵢ(Y)` lie in `P` for
`2 ≤ i ≤ n + 1`. Then the Hurewicz map `πₙ₊₂(Y) → Hₙ₊₂(Y; ℤ)` is an isomorphism modulo `P`: its
kernel and cokernel lie in `P`. -/
theorem isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup (n : ℕ)
    (hK : P.SatisfiesEilenbergMacLaneAxiom (n + 2))
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y)
    (hY : ∀ i, i < n → P (ModuleCat.of ℤ (Additive (π_ (i + 2) Y y)))) :
    P.isoModSerre (HomotopyGroup.hurewiczModuleCatHom Y y n) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (i : ℕ) (hi0 : i ≠ 0) (hi : i < 2) : Subsingleton (π_ i Y y) := by
    obtain rfl : i = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  exact isoModSerre_hurewiczModuleCatHom_of_add P n hK n 0 y (by omega) h₁
    (fun i _ hin ↦ hY i (by omega))

/-! ### Torsion homotopy groups -/

/-- **Serre's axiom for the torsion groups**, in every degree: for a torsion abelian group `G`,
the positive-degree homology of every `K(G, m + 1)` space is torsion, and the torsion groups are
closed under direct sums, so they serve as `Q`. The axiom holds because the positive-degree
homology of the classifying space of a torsion abelian group is torsion. -/
theorem satisfiesEilenbergMacLaneAxiom_isTorsion (k : ℕ) :
    (AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{0} ℤ)
      AddCommGrpCat)).SatisfiesEilenbergMacLaneAxiom k := by
  refine (ObjectProperty.satisfiesEilenbergMacLaneAxiom_iff _ k).2 fun G _ hG m ↦ ?_
  refine ⟨_, le_rfl, inferInstance, inferInstance, inferInstance, fun Z _ z hZ q hq _ ↦ ?_⟩
  refine IsEilenbergMacLaneSpace.prop_singularHomology_of_one _ (fun Z _ z hZ q hq ↦ ?_) m hZ hq
  -- A `K(G, 1)` space receives a weak homotopy equivalence from the classifying space of `G`,
  -- a locally finite group.
  have : Group.IsLocallyFinite G := Group.isLocallyFinite_iff_isMulTorsion.2 fun g ↦
    isOfFinAddOrder_ofMul_iff.1
      ((AddCommGrpCat.prop_inverseImage_isTorsion_iff _).1 hG (Additive.ofMul g))
  obtain ⟨f, hf⟩ :=
    (isEilenbergMacLaneSpace_one_iff.1 hZ).exists_isWeakHomotopyEquivalence_classifyingSpace
  have := hf.isIso_singularHomologyMap (ModuleCat.of ℤ ℤ) q
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact ObjectProperty.prop_of_iso _ (asIso (((singularHomologyFunctor (ModuleCat.{0} ℤ)
    (q + 1)).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)))
    ((AddCommGrpCat.prop_inverseImage_isTorsion_iff _).2 (by
      rw [singularHomologyFunctor_obj_obj]
      exact isAddTorsion_classifyingSpace_singularHomology ℤ q))

/-- A torsion homotopy group, read as a `ℤ`-module, lies in the torsion class. -/
private theorem prop_isTorsion_homotopyGroup {Y : Type} [TopologicalSpace Y] {y : Y} {j : ℕ}
    (h : IsMulTorsion (π_ (j + 2) Y y)) :
    AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)
      (ModuleCat.of ℤ (Additive (π_ (j + 2) Y y))) :=
  (AddCommGrpCat.prop_inverseImage_isTorsion_iff _).2 fun a : Additive (π_ (j + 2) Y y) ↦
    (isOfFinAddOrder_ofMul_iff (x := a.toMul)).2 (h _)

/-- **Torsion homotopy groups give torsion homology** (Serre). Let `Y` be a simply connected space
whose homotopy groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ k`. Then the integral homology
groups `Hᵢ(Y; ℤ)` are torsion groups for `1 ≤ i ≤ k`. This is the case of the Serre class of
torsion groups, for which Serre's axiom holds because the positive-degree homology of the
classifying space of a torsion abelian group is torsion. -/
theorem isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) (k : ℕ)
    (hY : ∀ j, j + 2 ≤ k → IsMulTorsion (π_ (j + 2) Y y)) {i : ℕ} (hi0 : i ≠ 0) (hik : i ≤ k) :
    IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology i) := by
  rw [← singularHomologyFunctor_obj_obj]
  exact (AddCommGrpCat.prop_inverseImage_isTorsion_iff _).1
    (prop_singularHomology_of_prop_homotopyGroup _ k (satisfiesEilenbergMacLaneAxiom_isTorsion k) y
      (fun j hj ↦ prop_isTorsion_homotopyGroup (hY j hj)) hi0 hik)

/-- **The Hurewicz map modulo torsion** (Serre). Let `Y` be a simply connected space whose
homotopy groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ n + 1`. Then the Hurewicz map
`πₙ₊₂(Y) → Hₙ₊₂(Y; ℤ)` is an isomorphism modulo torsion: its kernel and cokernel are torsion
groups. -/
theorem isoModSerre_hurewiczModuleCatHom_of_isMulTorsion_homotopyGroup {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) (n : ℕ)
    (hY : ∀ i, i < n → IsMulTorsion (π_ (i + 2) Y y)) :
    (AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)).isoModSerre
      (HomotopyGroup.hurewiczModuleCatHom Y y n) :=
  isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup _ n
    (satisfiesEilenbergMacLaneAxiom_isTorsion (n + 2)) y
    (fun i hi ↦ prop_isTorsion_homotopyGroup (hY i hi))

end TauCeti
