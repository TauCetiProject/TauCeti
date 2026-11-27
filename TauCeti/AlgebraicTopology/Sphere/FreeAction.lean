/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Cellular.CellAttachment
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FiniteCyclic.Prod
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.Homotopy.CellAttachment
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# Free actions of finite groups on spheres

Let a finite group `G` act freely and continuously on the sphere `Sⁿ`, `n ≥ 2`. This file shows
that for every division ring `k`, for instance every field, the homology `Hₙ₊₁(BG; k)` of the
classifying space of `G` has dimension at most one
(`TauCeti.finrank_classifyingSpace_singularHomology_le_one`). Since `H_d(B(ℤ/p × ℤ/p); 𝔽_p)` has
dimension `d + 1`, it follows that no continuous action of `ℤ/p × ℤ/p` on `Sⁿ` is free: some
nonidentity element fixes a point
(`TauCeti.exists_ne_one_smul_eq_self_sphere`, which also covers `S⁰` by counting points). No
linearity, smoothness or cellularity of the action is assumed.

## The argument

Write `S` for the sphere `Sⁿ` and `M = S / G` for the orbit space.

* As `G` is finite and acts freely, the orbit map `S → M` is a covering map, and `M` is a compact
  Hausdorff space carrying the charts of `S` (`MulAction.instChartedSpaceQuotient`). So `M` is a
  compact topological `n`-manifold and `Hₙ₊₁(M; k) = 0`
  (`TauCeti.isZero_singularHomology_of_compactSpace`).
* As `S` is simply connected, `π₁(M) ≅ G`, and the covering induces isomorphisms
  `πⱼ(S) ≅ πⱼ(M)` for `j ≥ 2`. So `πⱼ(M)` vanishes for `2 ≤ j < n`, and `πₙ(M) ≅ ℤ`.
* Attaching one `(n + 1)`-cell `Y = M ∪ eⁿ⁺¹` along a generator of `πₙ(M)` kills `πₙ` and keeps
  the lower homotopy groups. As `Hₙ₊₁(M; k)` vanishes, `Hₙ₊₁(Y; k)` embeds into the relative
  homology of the single cell, so it has dimension at most one
  (`TauCeti.finrank_singularHomology_cellAttachment_le`).
* Killing the homotopy groups of `Y` from degree `n + 1` on, by attaching cells of dimension at
  least `n + 2` (`TauCeti.killHomotopyGroups`), gives a space `K` with `π₁(K) ≅ G` and no higher
  homotopy groups, that is, a `K(G, 1)`. The inclusion `Y → K` is `(n + 1)`-connected, so it is
  onto on `Hₙ₊₁(-; k)` (`ContinuousMap.IsNConnected.epi_singularHomologyMap`).
* The classifying space `BG` maps to the `K(G, 1)` space `K` by a weak homotopy equivalence
  (`TauCeti.IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace`), which
  induces isomorphisms on homology. So `dim Hₙ₊₁(BG; k) ≤ dim Hₙ₊₁(Y; k) ≤ 1`.

For `G = ℤ/p × ℤ/p` and `k = 𝔽_p`, the dimension of `Hₙ₊₁(BG; 𝔽_p)` is `n + 2`
(`TauCeti.finrank_classifyingSpace_prod_singularCohomology_of_natCast_card_eq_zero` together with
the universal coefficient theorem over a field, `TopCat.finrank_singularCohomology`), which is
more than one.

On `S⁰` a free action of a group with `p² ≥ 4` elements would need at least `p²` points. The
circle `S¹` is not covered here: there the statement needs that the finite groups acting freely on
the circle are cyclic.

## Main results

* `TauCeti.finrank_classifyingSpace_singularHomology_le_one`: if a finite group `G` acts freely and
  continuously on `Sⁿ`, `n ≥ 2`, then `dim Hₙ₊₁(BG; k) ≤ 1` for every division ring `k`.
* `TauCeti.exists_ne_one_smul_eq_self_sphere`: for every prime `p` and `n ≠ 1`, every
  continuous action of `ℤ/p × ℤ/p` on `Sⁿ` has a nonidentity element fixing a point.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Exercise 28 (free actions of `ℤ/p × ℤ/p` on spheres), Section 4.1 (attaching cells
  to kill homotopy groups) and Proposition 1B.9 (uniqueness of `K(G, 1)` spaces).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module Set MulAction
open scoped Topology Topology.Homotopy

namespace TauCeti

section OrbitSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  {G : Type} [Group G] [Finite G] [MulAction G (sphere (0 : E) 1)]
  [ContinuousConstSMul G (sphere (0 : E) 1)] [IsCancelSMul G (sphere (0 : E) 1)]

/-- The orbit map of a free action of a finite group on a sphere is a quotient covering map. -/
private lemma isQuotientCoveringMap_orbitMk (hE : finrank ℝ E = n + 3) :
    IsQuotientCoveringMap (Quotient.mk (orbitRel G (sphere (0 : E) 1))) G := by
  have := Module.finite_of_finrank_eq_succ hE
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The orbit space of a free action of a finite group on `Sⁿ⁺²` has no homology in degree
`n + 3`: it is a compact topological manifold of dimension `n + 2`. -/
private lemma isZero_singularHomology_orbitRelQuotient (hE : finrank ℝ E = n + 3)
    (k : Type) [DivisionRing k] :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} k) (n + 3)).obj (ModuleCat.of k k)).obj
      (TopCat.of (orbitRel.Quotient G (sphere (0 : E) 1)))) := by
  have := Module.finite_of_finrank_eq_succ hE
  have : Fact (finrank ℝ E = n + 2 + 1) := ⟨hE⟩
  exact isZero_singularHomology_of_compactSpace (E := EuclideanSpace ℝ (Fin (n + 2)))
    (ModuleCat.of k k) (finrank_euclideanSpace_fin) (by omega)

/-- The homotopy groups `πⱼ` of the orbit space of a free action of a finite group on `Sⁿ⁺²`
vanish for `2 ≤ j < n + 2`: the orbit map is a covering, and `Sⁿ⁺²` is `(n + 1)`-connected. -/
private lemma subsingleton_homotopyGroup_orbitRelQuotient (hE : finrank ℝ E = n + 3)
    (x : sphere (0 : E) 1) {j : ℕ} (h2 : 2 ≤ j) (hj : j < n + 2) :
    Subsingleton (π_ j (orbitRel.Quotient G (sphere (0 : E) 1)) (Quotient.mk _ x)) := by
  have : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.2 h2
  have := subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) hE (N := Fin j)
    (by simpa using hj) x
  exact ((isQuotientCoveringMap_orbitMk (G := G) hE).isCoveringMap.homotopyGroupMulEquiv
    (N := Fin j) x).symm
    |>.toEquiv.subsingleton

/-- The homotopy group `πₙ₊₂` of the orbit space of a free action of a finite group on `Sⁿ⁺²`,
which is isomorphic to `πₙ₊₂(Sⁿ⁺²) ≅ ℤ`, is generated by a single class. -/
private lemma exists_normalClosure_eq_top (hE : finrank ℝ E = n + 3) (x : sphere (0 : E) 1) :
    ∃ p : Ω^ (Fin (n + 2)) (TopCat.of (orbitRel.Quotient G (sphere (0 : E) 1))) (Quotient.mk _ x),
      Subgroup.normalClosure (G := π_ (n + 2) _ (Quotient.mk _ x)) {⟦p⟧} = ⊤ := by
  have : Nontrivial (Fin (n + 2)) := Fin.nontrivial_iff_two_le.2 (by omega)
  let e := ((isQuotientCoveringMap_orbitMk (G := G) hE).isCoveringMap.homotopyGroupMulEquiv
    (N := Fin (n + 2)) x).symm
  let f := homotopyGroupSphereAddEquivOfFinrankEq hE x
  let a : π_ (n + 2) (orbitRel.Quotient G (sphere (0 : E) 1)) (Quotient.mk _ x) :=
    e.symm (Additive.toMul (f.symm 1))
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  refine ⟨p, eq_top_iff.2 fun b _ ↦ ?_⟩
  -- Every class is a power of `a`, through `πₙ₊₂ ≅ ℤ`.
  have hb : b = a ^ f (Additive.ofMul (e b)) := by
    apply e.injective
    rw [map_zpow, MulEquiv.apply_symm_apply]
    apply Additive.ofMul.injective
    apply f.injective
    rw [ofMul_zpow, ofMul_toMul, map_zsmul, AddEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  rw [hb, ← hp]
  exact Subgroup.zpow_mem _ (Subgroup.subset_normalClosure rfl) _

/-! ### Attaching a cell along a generator of `πₙ₊₂` -/

variable {x : sphere (0 : E) 1}
  (p : Ω^ (Fin (n + 2)) (TopCat.of (orbitRel.Quotient G (sphere (0 : E) 1))) (Quotient.mk _ x))

/-- After attaching an `(n + 3)`-cell along a generator of `πₙ₊₂` of the orbit space of a free
action of a finite group on `Sⁿ⁺²`, the homotopy groups `πⱼ` vanish for `2 ≤ j ≤ n + 2`. -/
private lemma subsingleton_homotopyGroup_cellAttachment_orbit (hE : finrank ℝ E = n + 3)
    (hp : Subgroup.normalClosure (G := π_ (n + 2) _ (Quotient.mk _ x)) {⟦p⟧} = ⊤) {j : ℕ}
    (h2 : 2 ≤ j) (hj : j ≤ n + 2) :
    Subsingleton (π_ j (cellAttachment fun _ : PUnit ↦ GenLoop.diskBoundaryMap p)
      (cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x))) := by
  have := Module.finite_of_finrank_eq_succ hE
  rcases hj.lt_or_eq with hj | rfl
  · -- Below the dimension of the cell, the homotopy groups of the orbit space are unchanged.
    have := subsingleton_homotopyGroup_orbitRelQuotient (G := G) hE x h2 hj
    exact (bijective_homotopyGroupMap_cellAttachmentIncl (n := n + 2)
      (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (N := Fin j) (by simpa using hj) _).2.subsingleton
  · -- The cell kills the generator.
    refine subsingleton_homotopyGroup_cellAttachment (fun _ : PUnit ↦ p) ?_
    convert hp using 2
    exact range_const

/-- After attaching an `(n + 3)`-cell to the orbit space of a free action of a finite group `G` on
`Sⁿ⁺²`, the fundamental group is still isomorphic to `G`. -/
private lemma nonempty_fundamentalGroup_cellAttachment_mulEquiv (hE : finrank ℝ E = n + 3) :
    Nonempty (FundamentalGroup (cellAttachment fun _ : PUnit ↦ GenLoop.diskBoundaryMap p)
      (cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x)) ≃* G) := by
  have := Module.finite_of_finrank_eq_succ hE
  have : SimplyConnectedSpace (sphere (0 : E) 1) :=
    simplyConnectedSpace_sphere (by rw [← finrank_eq_rank, hE]; norm_cast; omega) 0 zero_le_one
  -- The orbit space has fundamental group `Gᵐᵒᵖ ≅ G`, and attaching a cell of dimension at least
  -- three does not change it.
  let e₁ := MulEquiv.ofBijective (FundamentalGroup.mapOfEq
    (cellAttachmentIncl fun _ : PUnit ↦ GenLoop.diskBoundaryMap p).hom rfl)
    ((HomotopyGroup.bijective_map_iff_bijective_mapOfEq _ rfl).1
      (bijective_homotopyGroupMap_cellAttachmentIncl (n := n + 2)
        (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (N := Fin 1) (by simp)
        (Quotient.mk _ x : orbitRel.Quotient G (sphere (0 : E) 1))))
  exact ⟨e₁.symm.trans (((isQuotientCoveringMap_orbitMk hE).fundamentalGroupEquiv
    (⟨x, rfl⟩ : Quotient.mk _ ⁻¹' {Quotient.mk _ x})).trans (MulEquiv.inv' G).symm)⟩

omit [IsCancelSMul G (sphere (0 : E) 1)] in
/-- The space obtained by attaching an `(n + 3)`-cell to the orbit space of an action of a finite
group on `Sⁿ⁺²` is path connected. -/
private lemma pathConnectedSpace_cellAttachment_orbit (hE : finrank ℝ E = n + 3) :
    PathConnectedSpace (cellAttachment fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) := by
  have := Module.finite_of_finrank_eq_succ hE
  have : PathConnectedSpace (sphere (0 : E) 1) := by
    have := subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) hE (N := Fin 0) (by simp) x
    exact pathConnectedSpace_iff_zerothHomotopy.2
      ⟨⟨⟦x⟧⟩, (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm.subsingleton⟩
  have : PathConnectedSpace (orbitRel.Quotient G (sphere (0 : E) 1)) :=
    (Quotient.mk_surjective.pathConnectedSpace continuous_quotient_mk')
  have hsurj := (bijective_homotopyGroupMap_cellAttachmentIncl (n := n + 2)
    (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (N := Fin 0) (by simp) (Quotient.mk _ x)).2
  have : Subsingleton (π_ 0 (orbitRel.Quotient G (sphere (0 : E) 1)) (Quotient.mk _ x)) :=
    HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  have := hsurj.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨⟦cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x)⟧⟩,
      (HomotopyGroup.pi0EquivZerothHomotopy (x := cellAttachmentIncl
      (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x))).symm.subsingleton⟩

/-- After attaching an `(n + 3)`-cell along a generator of `πₙ₊₂` of the orbit space of a free
action of a finite group `G` on `Sⁿ⁺²`, killing the homotopy groups from degree `n + 3` on gives
a `K(G, 1)`. -/
private lemma isEilenbergMacLaneSpaceOne_killHomotopyGroups_cellAttachment
    (hE : finrank ℝ E = n + 3)
    (hp : Subgroup.normalClosure (G := π_ (n + 2) _ (Quotient.mk _ x)) {⟦p⟧} = ⊤) :
    IsEilenbergMacLaneSpaceOne G
      (killHomotopyGroups (n + 3) (cellAttachment fun _ : PUnit ↦ GenLoop.diskBoundaryMap p)
        (cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x)))
      (killHomotopyGroupsIncl (n + 3) _ _
        (cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x))) := by
  have := Module.finite_of_finrank_eq_succ hE
  have := pathConnectedSpace_cellAttachment_orbit p hE
  set Y := cellAttachment fun _ : PUnit ↦ GenLoop.diskBoundaryMap p
  set y : Y := cellAttachmentIncl (fun _ : PUnit ↦ GenLoop.diskBoundaryMap p) (Quotient.mk _ x)
  obtain ⟨e⟩ := nonempty_fundamentalGroup_cellAttachment_mulEquiv p hE
  refine IsEilenbergMacLaneSpaceOne.mk (isAspherical_iff.2 ⟨inferInstance, fun j ↦ ?_⟩)
    ⟨(killHomotopyGroupsFundamentalGroupMulEquiv (n + 3) Y y (by omega)).symm.trans e⟩
  rcases lt_or_ge (j + 2) (n + 3) with hj | hj
  · -- Below degree `n + 3` the homotopy groups are those of `Y`, which vanish from degree two on.
    have := subsingleton_homotopyGroup_cellAttachment_orbit p hE hp (j := j + 2) (by omega)
      (by omega)
    exact (bijective_homotopyGroupMap_killHomotopyGroupsIncl (n + 3) Y y (N := Fin (j + 2))
      (by simpa using hj)).2.subsingleton
  · exact subsingleton_homotopyGroup_killHomotopyGroups (n + 3) Y y hj

end OrbitSpace

/-! ### The homology of the classifying space -/

/-- **A finite group acting freely on `Sⁿ⁺²` has at most one-dimensional `Hₙ₊₃(BG; k)`.** Let a
finite group `G` act freely and continuously on the unit sphere `Sⁿ⁺²` of an `(n + 3)`-dimensional
real inner product space. Then for every division ring `k`, the singular homology `Hₙ₊₃(BG; k)`
of the classifying space of `G` has dimension at most one. -/
theorem finrank_classifyingSpace_singularHomology_le_one {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (hE : finrank ℝ E = n + 3) {G : Type} [Group G] [Finite G]
    [MulAction G (sphere (0 : E) 1)] [ContinuousConstSMul G (sphere (0 : E) 1)]
    [IsCancelSMul G (sphere (0 : E) 1)] (k : Type) [DivisionRing k] :
    finrank k (((singularHomologyFunctor (ModuleCat.{0} k) (n + 3)).obj (ModuleCat.of k k)).obj
      (TopCat.of (classifyingSpace G))) ≤ 1 := by
  have := Module.finite_of_finrank_eq_succ hE
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨x⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨p, hp⟩ := exists_normalClosure_eq_top (G := G) hE x
  have := pathConnectedSpace_cellAttachment_orbit p hE
  set φ := fun _ : PUnit ↦ GenLoop.diskBoundaryMap p
  set y := cellAttachmentIncl φ (Quotient.mk _ x)
  set H := (singularHomologyFunctor (ModuleCat.{0} k) (n + 3)).obj (ModuleCat.of k k)
  -- The classifying space is weakly equivalent to the `K(G, 1)` built from the orbit space.
  obtain ⟨f, hf⟩ := (isEilenbergMacLaneSpaceOne_killHomotopyGroups_cellAttachment p hE hp)
    |>.exists_isWeakHomotopyEquivalence_classifyingSpace
  have := hf.isIso_singularHomologyMap (ModuleCat.of k k) (n + 3)
  rw [(asIso (H.map (TopCat.ofHom f))).toLinearEquiv.finrank_eq]
  -- The `K(G, 1)` is obtained from `Y = M ∪ eⁿ⁺³` by attaching cells of dimension at least
  -- `n + 4`, so it receives a surjection from `Hₙ₊₃(Y; k)`, which has dimension at most one.
  have hM := isZero_singularHomology_orbitRelQuotient (G := G) hE k
  have := finite_singularHomology_cellAttachment φ k hM
  have hepi := (isNConnected_killHomotopyGroupsIncl (n + 3) (cellAttachment φ) y)
    |>.epi_singularHomologyMap k le_rfl
  calc _ ≤ finrank k (H.obj (cellAttachment φ)) :=
        LinearMap.finrank_le_finrank_of_surjective
          ((ModuleCat.epi_iff_surjective _).1 hepi)
    _ ≤ Nat.card PUnit := finrank_singularHomology_cellAttachment_le φ k hM
    _ = 1 := Nat.card_unique

/-! ### Free actions of `ℤ/p × ℤ/p` -/

/-- For `n ≥ 2`, every continuous action of `ℤ/p × ℤ/p` on `Sⁿ` has a nonidentity element fixing
a point: otherwise `Hₙ₊₁(B(ℤ/p × ℤ/p); 𝔽_p)`, of dimension `n + 2`, would have dimension at most
one. -/
private lemma exists_ne_one_smul_eq_self_of_two_le {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hE : finrank ℝ E = n + 1)
    [MulAction (Multiplicative (ZMod p × ZMod p)) (sphere (0 : E) 1)]
    (hcont : ∀ g : Multiplicative (ZMod p × ZMod p),
      Continuous fun x : sphere (0 : E) 1 ↦ g • x) :
    ∃ g : Multiplicative (ZMod p × ZMod p), g ≠ 1 ∧ ∃ x : sphere (0 : E) 1, g • x = x := by
  have := Fact.mk hp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  by_contra! hfree
  -- Act by `ℤ/p × ℤ/p` written as a product of two cyclic groups.
  let e := (MulEquiv.prodMultiplicative (G := ZMod p) (H := ZMod p)).symm
  let : MulAction (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (sphere (0 : E) 1) :=
    MulAction.compHom _ e.toMonoidHom
  have : ContinuousConstSMul (Multiplicative (ZMod p) × Multiplicative (ZMod p))
      (sphere (0 : E) 1) := ⟨fun g ↦ hcont (e g)⟩
  have : IsCancelSMul (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (sphere (0 : E) 1) :=
    isCancelSMul_iff_eq_one_of_smul_eq.2 fun g x hx ↦ by
      by_contra hg
      exact hfree (e g) (by simpa using hg) x hx
  have hcard : (Nat.card (Multiplicative (ZMod p)) : ZMod p) = 0 := by simp
  have h := finrank_classifyingSpace_singularHomology_le_one hE
    (G := Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p)
  rw [← TopCat.finrank_singularCohomology,
    finrank_classifyingSpace_prod_singularCohomology_of_natCast_card_eq_zero (ZMod p) hcard
      hcard] at h
  omega

/-- On `S⁰`, every action of `ℤ/p × ℤ/p` has a nonidentity element fixing a point: a free action
of a group with `p² ≥ 4` elements needs at least `p²` points. -/
private lemma exists_ne_one_smul_eq_self_of_finrank_eq_one {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p : ℕ} (hp : p.Prime) (hE : finrank ℝ E = 1)
    [MulAction (Multiplicative (ZMod p × ZMod p)) (sphere (0 : E) 1)] :
    ∃ g : Multiplicative (ZMod p × ZMod p), g ≠ 1 ∧ ∃ x : sphere (0 : E) 1, g • x = x := by
  have := Fact.mk hp
  by_contra! hfree
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨x⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- The orbit map of `x` is injective, as the action is free.
  have hinj : Function.Injective fun g : Multiplicative (ZMod p × ZMod p) ↦ g • x := by
    intro g h hgh
    by_contra hne
    refine hfree (h⁻¹ * g) (by rwa [ne_eq, inv_mul_eq_one, eq_comm]) x ?_
    rw [mul_smul]
    exact inv_smul_eq_iff.2 hgh
  -- The sphere `S⁰` has at most two points.
  have hS : Nat.card (sphere (0 : E) 1) ≤ 2 := by
    rw [sphere_eq_pair_of_finrank_eq_one hE x.property, Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by simp)
  have := finite_sphere_of_finrank_eq_one hE 0 1
  have h := (Nat.card_le_card_of_injective _ hinj).trans hS
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod,
    ZMod.card] at h
  nlinarith [hp.two_le]

/-- **No continuous action of `ℤ/p × ℤ/p` on `Sⁿ`, `n ≠ 1`, is free** (Hatcher, Section 4.2,
Exercise 28). For every prime `p`, every continuous action of `ℤ/p × ℤ/p`, written as the
multiplicative group `Multiplicative (ZMod p × ZMod p)`, on the unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real inner product space with `n ≠ 1` has a nonidentity element fixing a
point. For a finite group, continuity of each translation is continuity of the action for the
discrete topology on the group; no linearity, smoothness or cellularity is assumed. -/
theorem exists_ne_one_smul_eq_self_sphere {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p n : ℕ} (hp : p.Prime) (hn : n ≠ 1) (hE : finrank ℝ E = n + 1)
    [MulAction (Multiplicative (ZMod p × ZMod p)) (sphere (0 : E) 1)]
    (hcont : ∀ g : Multiplicative (ZMod p × ZMod p),
      Continuous fun x : sphere (0 : E) 1 ↦ g • x) :
    ∃ g : Multiplicative (ZMod p × ZMod p), g ≠ 1 ∧ ∃ x : sphere (0 : E) 1, g • x = x := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 0 := by omega
    exact exists_ne_one_smul_eq_self_of_finrank_eq_one hp hE
  · exact exists_ne_one_smul_eq_self_of_two_le hp h hE hcont

end TauCeti
