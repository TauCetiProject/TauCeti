/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Uniqueness and pointed mapping property of `K(G, 1)` spaces of CW type

Two aspherical spaces of CW type with isomorphic fundamental groups are homotopy equivalent, and
the homotopy equivalence can be chosen to realize any prescribed isomorphism
`φ : π₁(X, x) ≃* π₁(Y, y)` (`TauCeti.IsAspherical.exists_homotopyEquiv`). Without well-pointedness,
a homotopy equivalence `e` need not send `x` to `y`, so realizing `φ` means: there is a path `γ`
from `e x` to `y` such that the map induced by `e` on fundamental groups, followed by basepoint
change along `γ`, is `φ`. In particular any two `K(G, 1)` spaces of CW type are homotopy equivalent
(`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`), and every `K(G, 1)` space of CW
type is homotopy equivalent to Milnor's classifying space `TauCeti.classifyingSpace G`, compatibly
with the identifications of both fundamental groups with `G`
(`TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`).

When the base point `x` of `X` has the homotopy extension property (for instance any point of a
Hausdorff CW complex, by `TauCeti.hasHomotopyExtensionProperty_singleton_of_cwComplex`), the
comparison map from a cellular classifying space `cellularClassifyingSpace R` to `X` upgrades to a
*pointed* homotopy equivalence relative to the base points
(`TauCeti.exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv`). Transporting the universal
property of the cellular model along this equivalence yields Hatcher's Proposition 1B.9 for every
well-pointed aspherical space of CW type:

* Every homomorphism `φ : π₁(X, x) →* π₁(Y, y)` into a space with vanishing `π_k(Y, y)` for
  `k ≥ 2` is induced by a pointed map `f : C(X, Y)` (`TauCeti.IsAspherical.exists_mapOfEq`).
* Two pointed maps into a space with vanishing `π_{n+2}(Y, z)` at every point `z : Y` that induce
  the same homomorphism on `π₁` are homotopic relative to `{x}`
  (`TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`).

Specializing to Milnor's classifying space `classifyingSpace G` (which is a Hausdorff CW complex)
gives `TauCeti.exists_mapOfEq_classifyingSpace` and
`TauCeti.homotopicRel_of_mapOfEq_eq_classifyingSpace`.

With well-pointedness on the source `X`, an isomorphism `φ : π₁(X, x) ≃* π₁(Y, y)` between
aspherical spaces of CW type is realized by a homotopy equivalence whose forward map sends `x` to
`y` (`TauCeti.IsAspherical.exists_homotopyEquiv_of_hasHomotopyExtensionProperty`). With
well-pointedness on both `X` and `Y`, both forward and inverse maps preserve base points, induce
`φ` and `φ⁻¹` directly, and have both composites homotopic to the identities relative to the base
points (`TauCeti.IsAspherical.exists_homotopyEquiv_homotopicRel`, specialized to Hausdorff CW
complexes in `TauCeti.IsAspherical.exists_homotopyEquiv_of_cwComplex`, and to `classifyingSpace G`
in `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace_homotopicRel`).

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are both
path connected with trivial homotopy groups, but they are not homotopy equivalent.

Without CW type on the target, `TauCeti.exists_mapOfEq_classifyingSpace` directly produces a
*pointed* weak homotopy equivalence `f : classifyingSpace G → X` realizing any prescribed
identification `π₁(X, x) ≃* G`
(`TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`), which is the case
`n = 1` of Hatcher's Proposition 4.30 without needing CW approximation or a change of base point.

## Main results

* `TauCeti.IsAspherical.exists_homotopyEquiv`: **aspherical spaces of CW type are homotopy
  equivalent by a homotopy equivalence realizing any prescribed isomorphism of fundamental
  groups** (up to a change of base point).
* `TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`: two `K(G, 1)` spaces of CW type are
  homotopy equivalent.
* `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`: an aspherical space of CW type
  with fundamental group identified with `G` is homotopy equivalent to `classifyingSpace G`,
  compatibly with the identifications of fundamental groups.
* `TauCeti.IsAspherical.exists_mapOfEq` and `TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`:
  **Hatcher's Proposition 1B.9** for any well-pointed aspherical space of CW type.
* `TauCeti.exists_mapOfEq_classifyingSpace` and
  `TauCeti.homotopicRel_of_mapOfEq_eq_classifyingSpace`: pointed maps out of Milnor's
  `classifyingSpace G` into a space without higher homotopy groups are classified by `π₁`.
* `TauCeti.IsAspherical.exists_homotopyEquiv_of_hasHomotopyExtensionProperty`: pointed forward
  homotopy equivalence assuming well-pointedness on the source only.
* `TauCeti.IsAspherical.exists_homotopyEquiv_homotopicRel`,
  `TauCeti.IsAspherical.exists_homotopyEquiv_of_cwComplex`, and
  `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace_homotopicRel`: **pointed uniqueness**
  relative to base points in both directions.
* `TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`: every aspherical space
  receives a pointed weak homotopy equivalence from `classifyingSpace G`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19),
  Section 1.B, Theorem 1B.8 and Proposition 1B.9, and Section 4.1, Theorem 4.5 and Proposition 4.30.
* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. 9
  (2009), 1585--1622, for the Warsaw circle.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup Set Topology

universe u v

namespace TauCeti

/-- **Uniqueness of aspherical spaces of CW type.** Two aspherical spaces of CW type are homotopy
equivalent by a homotopy equivalence realizing any prescribed isomorphism `φ` of their fundamental
groups: there is a homotopy equivalence `e` and a path `γ` from `e x` to `y` such that the map
induced by `e` on fundamental groups, followed by basepoint change along `γ`, is `φ`.

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are
aspherical with trivial fundamental groups, but they are not homotopy equivalent. -/
theorem IsAspherical.exists_homotopyEquiv {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y} (hX : IsAspherical X x)
    (hY : IsAspherical Y y) (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (γ : Path (e.toFun x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map e.toFun x a) = φ a := by
  obtain ⟨R, -, -, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨ψ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  have : PathConnectedSpace (cellularClassifyingSpace R) := hC.isAspherical.pathConnectedSpace
  -- Pointed homotopy equivalences from the cellular classifying space realizing `ψ` and `φ ∘ ψ`.
  set f := cellularClassifyingSpaceHomotopyEquiv R hX ψ
  set g := cellularClassifyingSpaceHomotopyEquiv R hY (ψ.trans φ)
  -- `f⁻¹` is a homotopy right inverse of `f`, so `g ∘ f⁻¹` realizes `φ` up to basepoint change.
  refine ⟨f.symm.trans g, f.right_inv.some.exists_path_fundamentalGroupMulEquivOfPath_map_comp
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX ψ)
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY (ψ.trans φ)) φ.toMonoidHom
    (MonoidHom.ext fun a ↦ by simp [f])⟩

/-- **Two `K(G, 1)` spaces of CW type are homotopy equivalent.** See
`TauCeti.IsAspherical.exists_homotopyEquiv` for a homotopy equivalence realizing a prescribed
isomorphism of fundamental groups. -/
theorem IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv {G : Type v} [Group G]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y}
    (hX : IsEilenbergMacLaneSpaceOne G X x) (hY : IsEilenbergMacLaneSpaceOne G Y y) :
    Nonempty (X ≃ₕ Y) := by
  obtain ⟨eX⟩ := hX.nonempty_fundamentalGroupMulEquiv
  obtain ⟨eY⟩ := hY.nonempty_fundamentalGroupMulEquiv
  obtain ⟨e, -⟩ := IsAspherical.exists_homotopyEquiv hX.isAspherical hY.isAspherical
    (eX.trans eY.symm)
  exact ⟨e⟩

/-- **Milnor's classifying space is the unique `K(G, 1)` of CW type.** An aspherical space `X` of
CW type whose fundamental group is identified with `G` by `eX` is homotopy equivalent to
`classifyingSpace G`, by a homotopy equivalence `e` compatible with the identifications: for a
suitable path `γ` from `e x` to the base point, the map induced by `e`, followed by basepoint
change along `γ` and the identification `classifyingSpaceFundamentalGroupMulEquiv G`, is `eX`. -/
theorem IsAspherical.exists_homotopyEquiv_classifyingSpace {G : Type u} [Group G] {X : Type u}
    [TopologicalSpace X] [CWType X] {x : X} (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (e : X ≃ₕ classifyingSpace G) (γ : Path (e.toFun x) (classifyingSpaceBasepoint G)),
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv G
        (fundamentalGroupMulEquivOfPath γ (map e.toFun x a)) = eX a := by
  obtain ⟨e, γ, h⟩ := hX.exists_homotopyEquiv
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  exact ⟨e, γ, fun a ↦ by rw [h, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]⟩

/-- Every well-pointed aspherical space `X` of CW type admits a pointed homotopy equivalence from
a cellular classifying space `cellularClassifyingSpace R`, with both composites homotopic to the
identities relative to the base points. -/
private theorem exists_cellular_pointedHomotopyEquiv {X : Type u} [TopologicalSpace X] [CWType X]
    {x : X} (hX : IsAspherical X x) (hx : HasHomotopyExtensionProperty ({x} : Set X)) :
    ∃ (R : Set (FreeGroup (FundamentalGroup X x)))
      (p : C(cellularClassifyingSpace R, X)) (q : C(X, cellularClassifyingSpace R))
      (hp : p (cellularClassifyingSpaceBasepoint R) = x)
      (hq : q x = cellularClassifyingSpaceBasepoint R),
      (q.comp p).HomotopicRel (ContinuousMap.id _) {cellularClassifyingSpaceBasepoint R} ∧
      (p.comp q).HomotopicRel (ContinuousMap.id X) {x} ∧
      ∃ ψ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
          FundamentalGroup X x,
        FundamentalGroup.mapOfEq p hp = ψ.toMonoidHom ∧
        FundamentalGroup.mapOfEq q hq = ψ.symm.toMonoidHom := by
  obtain ⟨R, -, -, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨ψ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  obtain ⟨q, hq, hqp, hpq, hqψ⟩ :=
    exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv R hX ψ hx
  exact ⟨R, (cellularClassifyingSpaceHomotopyEquiv R hX ψ).toFun, q,
    cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX ψ, hq, hqp, hpq, ψ,
    MonoidHom.ext (mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply R hX ψ), hqψ⟩

/-- **Homomorphisms out of the fundamental group of a well-pointed aspherical space of CW type are
induced by pointed maps** (Hatcher, Proposition 1B.9, existence). If `(X, x)` is a well-pointed
aspherical space of CW type and `π_k(Y, y)` vanishes for `k ≥ 2`, every homomorphism
`φ : π₁(X, x) →* π₁(Y, y)` is induced by a continuous map `f : C(X, Y)` taking `x` to `y`. -/
theorem IsAspherical.exists_mapOfEq {X Y : Type u} [TopologicalSpace X] [CWType X]
    [TopologicalSpace Y] {x : X} {y : Y} (hX : IsAspherical X x)
    (hx : HasHomotopyExtensionProperty ({x} : Set X))
    (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (hf : f x = y), FundamentalGroup.mapOfEq f hf = φ := by
  obtain ⟨R, _, q, _, hq, _, _, ψ, _, hqψ⟩ := exists_cellular_pointedHomotopyEquiv hX hx
  obtain ⟨g, hg, hgφ⟩ := exists_mapOfEq_cellularClassifyingSpace R hY (φ.comp ψ.toMonoidHom)
  have hcomp : (g.comp q) x = y := by rw [ContinuousMap.comp_apply, hq, hg]
  refine ⟨g.comp q, hcomp, MonoidHom.ext fun a ↦ ?_⟩
  rw [← FundamentalGroup.mapOfEq_comp g q hq hg a, DFunLike.congr_fun hqψ a,
    DFunLike.congr_fun hgφ _]
  simp

/-- **Pointed maps out of a well-pointed aspherical space of CW type are determined up to pointed
homotopy by their effect on `π₁`** (Hatcher, Proposition 1B.9, uniqueness). If `(X, x)` is a
well-pointed aspherical space of CW type and `π_{n+2}(Y, z)` vanishes at every `z : Y`, then two
maps `f, g : C(X, Y)` taking `x` to `y` that induce the same homomorphism on fundamental groups
are homotopic relative to `{x}`. -/
theorem IsAspherical.homotopicRel_of_mapOfEq_eq {X : Type u} {Y : Type v} [TopologicalSpace X]
    [CWType X] [TopologicalSpace Y] {x : X} (hX : IsAspherical X x)
    (hx : HasHomotopyExtensionProperty ({x} : Set X))
    (hY : ∀ (z : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y z))
    {f g : C(X, Y)} {y : Y} (hf : f x = y) (hg : g x = y)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x} := by
  obtain ⟨R, p, q, hp, hq, _, hpq, _⟩ := exists_cellular_pointedHomotopyEquiv hX hx
  have hfp : (f.comp p) (cellularClassifyingSpaceBasepoint R) = y := by
    rw [ContinuousMap.comp_apply, hp, hf]
  have hgp : (g.comp p) (cellularClassifyingSpaceBasepoint R) = y := by
    rw [ContinuousMap.comp_apply, hp, hg]
  have hrel : (f.comp p).HomotopicRel (g.comp p) {cellularClassifyingSpaceBasepoint R} :=
    homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hY hfp hgp <| MonoidHom.ext fun a ↦ by
      rw [← FundamentalGroup.mapOfEq_comp f p hp hf a,
        ← FundamentalGroup.mapOfEq_comp g p hp hg a, DFunLike.congr_fun hfg]
  have hmid : ((f.comp p).comp q).HomotopicRel ((g.comp p).comp q) {x} :=
    (hrel.precomp q).mono (by simp [hq])
  have hleft : (f.comp (p.comp q)).HomotopicRel f {x} := by
    simpa only [ContinuousMap.comp_id] using hpq.comp_continuousMap f
  have hright : (g.comp (p.comp q)).HomotopicRel g {x} := by
    simpa only [ContinuousMap.comp_id] using hpq.comp_continuousMap g
  rw [ContinuousMap.comp_assoc] at hmid
  exact hleft.symm.trans (hmid.trans hright)

/-- **Homomorphisms out of the fundamental group of Milnor's classifying space are induced by
pointed maps.** If `π_k(Y, y)` vanishes for `k ≥ 2`, every homomorphism from
`π₁(classifyingSpace G)` to `π₁(Y, y)` is induced by a continuous map sending the base point to
`y`. -/
theorem exists_mapOfEq_classifyingSpace {G : Type u} [Group G] {Y : Type u} [TopologicalSpace Y]
    {y : Y} (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
    (φ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G) →*
      FundamentalGroup Y y) :
    ∃ (f : C(classifyingSpace G, Y)) (hf : f (classifyingSpaceBasepoint G) = y),
      FundamentalGroup.mapOfEq f hf = φ :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.exists_mapOfEq
    (hasHomotopyExtensionProperty_singleton_of_cwComplex _) hY φ

/-- **Pointed maps out of Milnor's classifying space are determined up to pointed homotopy by
their effect on `π₁`.** If `π_{n+2}(Y, z)` vanishes at every `z : Y`, two maps from
`classifyingSpace G` to `Y` taking the base point to `y` that induce the same homomorphism on
fundamental groups are homotopic relative to `{classifyingSpaceBasepoint G}`. -/
theorem homotopicRel_of_mapOfEq_eq_classifyingSpace {G : Type u} [Group G] {Y : Type v}
    [TopologicalSpace Y] (hY : ∀ (z : Y) (n : ℕ), Subsingleton (π_ (n + 2) Y z))
    {f g : C(classifyingSpace G, Y)} {y : Y}
    (hf : f (classifyingSpaceBasepoint G) = y) (hg : g (classifyingSpaceBasepoint G) = y)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {classifyingSpaceBasepoint G} :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.homotopicRel_of_mapOfEq_eq
    (hasHomotopyExtensionProperty_singleton_of_cwComplex _) hY hf hg hfg

/-- **Pointed forward uniqueness of aspherical spaces of CW type** (one-sided well-pointedness).
When `{x}` has the homotopy extension property in `X`, any isomorphism `φ : π₁(X, x) ≃* π₁(Y, y)`
between aspherical spaces of CW type is realized by a homotopy equivalence whose forward map
sends `x` to `y` directly, with no basepoint-change path. -/
theorem IsAspherical.exists_homotopyEquiv_of_hasHomotopyExtensionProperty {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y}
    (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (hx : HasHomotopyExtensionProperty ({x} : Set X))
    (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (he : e.toFun x = y),
      ∀ a, FundamentalGroup.mapOfEq e.toFun he a = φ a := by
  obtain ⟨f, hf, hfφ⟩ := hX.exists_mapOfEq hx
    (fun k hk ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact hY.subsingleton_homotopyGroup n) φ.toMonoidHom
  have hw : f.IsWeakHomotopyEquivalence :=
    (hX.isWeakHomotopyEquivalence_iff hY hf).2 (hfφ ▸ φ.bijective)
  refine ⟨hw.homotopyEquiv, ?_, fun a ↦ ?_⟩
  · rw [hw.homotopyEquiv_toFun]
    exact hf
  · rw [FundamentalGroup.mapOfEq_congr hw.homotopyEquiv_toFun _ hf]
    exact DFunLike.congr_fun hfφ a

/-- **Pointed uniqueness of well-pointed aspherical spaces of CW type.** When both base points
have the homotopy extension property, any isomorphism `φ : π₁(X, x) ≃* π₁(Y, y)` between
aspherical spaces of CW type is realized by a pointed homotopy equivalence whose forward and
inverse maps both preserve base points, induce `φ` and `φ⁻¹` directly, and have both composites
homotopic to the identities relative to the base points. -/
theorem IsAspherical.exists_homotopyEquiv_homotopicRel {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y}
    (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (hx : HasHomotopyExtensionProperty ({x} : Set X))
    (hy : HasHomotopyExtensionProperty ({y} : Set Y))
    (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (he : e.toFun x = y) (he' : e.invFun y = x),
      FundamentalGroup.mapOfEq e.toFun he = φ.toMonoidHom ∧
      FundamentalGroup.mapOfEq e.invFun he' = φ.symm.toMonoidHom ∧
      (e.invFun.comp e.toFun).HomotopicRel (ContinuousMap.id X) {x} ∧
      (e.toFun.comp e.invFun).HomotopicRel (ContinuousMap.id Y) {y} := by
  obtain ⟨e₀, he₀, he₀φ⟩ := hX.exists_homotopyEquiv_of_hasHomotopyExtensionProperty hY hx φ
  obtain ⟨g, hg, hgf, hfg⟩ := hx.exists_basedInverse_homotopicRel hy e₀ he₀
  let e : X ≃ₕ Y := ⟨e₀.toFun, g, hgf.homotopic, hfg.homotopic⟩
  refine ⟨e, he₀, hg, MonoidHom.ext he₀φ, MonoidHom.ext fun a ↦ ?_, hgf, hfg⟩
  apply φ.injective
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hcomp_bp : (e₀.toFun.comp g) y = y := by rw [ContinuousMap.comp_apply, hg, he₀]
  have hmap := DFunLike.congr_fun
    (FundamentalGroup.mapOfEq_eq_of_homotopicRel hcomp_bp (ContinuousMap.id_apply y) rfl hfg) a
  rw [FundamentalGroup.mapOfEq_id] at hmap
  rw [← he₀φ]
  exact (FundamentalGroup.mapOfEq_comp e₀.toFun g hg he₀ a).trans hmap

/-- **Pointed uniqueness of aspherical Hausdorff CW complexes.** Every point of a Hausdorff CW
complex has the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_singleton_of_cwComplex`), so any isomorphism
`φ : π₁(X, x) ≃* π₁(Y, y)` between aspherical Hausdorff CW complexes at arbitrary base points `x`
and `y` is realized by a pointed homotopy equivalence relative to `{x}` and `{y}`. -/
theorem IsAspherical.exists_homotopyEquiv_of_cwComplex {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    [CWComplex (univ : Set X)] [CWComplex (univ : Set Y)] {x : X} {y : Y}
    (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (he : e.toFun x = y) (he' : e.invFun y = x),
      FundamentalGroup.mapOfEq e.toFun he = φ.toMonoidHom ∧
      FundamentalGroup.mapOfEq e.invFun he' = φ.symm.toMonoidHom ∧
      (e.invFun.comp e.toFun).HomotopicRel (ContinuousMap.id X) {x} ∧
      (e.toFun.comp e.invFun).HomotopicRel (ContinuousMap.id Y) {y} :=
  hX.exists_homotopyEquiv_homotopicRel hY
    (hasHomotopyExtensionProperty_singleton_of_cwComplex x)
    (hasHomotopyExtensionProperty_singleton_of_cwComplex y) φ

/-- **Every well-pointed aspherical space of CW type is pointed homotopy equivalent to Milnor's
classifying space**, compatibly with a prescribed identification `eX : π₁(X, x) ≃* G`, with both
composites homotopic to the identities relative to the base points. -/
theorem IsAspherical.exists_homotopyEquiv_classifyingSpace_homotopicRel {G : Type u} [Group G]
    {X : Type u} [TopologicalSpace X] [CWType X] {x : X} (hX : IsAspherical X x)
    (hx : HasHomotopyExtensionProperty ({x} : Set X)) (eX : FundamentalGroup X x ≃* G) :
    ∃ (e : X ≃ₕ classifyingSpace G)
      (he : e.toFun x = classifyingSpaceBasepoint G)
      (he' : e.invFun (classifyingSpaceBasepoint G) = x),
      (∀ a, classifyingSpaceFundamentalGroupMulEquiv G (FundamentalGroup.mapOfEq e.toFun he a) =
        eX a) ∧
      (∀ a, eX (FundamentalGroup.mapOfEq e.invFun he' a) =
        classifyingSpaceFundamentalGroupMulEquiv G a) ∧
      (e.invFun.comp e.toFun).HomotopicRel (ContinuousMap.id X) {x} ∧
      (e.toFun.comp e.invFun).HomotopicRel (ContinuousMap.id (classifyingSpace G))
        {classifyingSpaceBasepoint G} := by
  let φ := eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm
  obtain ⟨e, he, he', hφ, hφ', hleft, hright⟩ := hX.exists_homotopyEquiv_homotopicRel
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hx
    (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G)) φ
  refine ⟨e, he, he', fun a ↦ ?_, fun a ↦ ?_, hleft, hright⟩
  · rw [DFunLike.congr_fun hφ a]
    simp [φ]
  · rw [DFunLike.congr_fun hφ' a]
    simp [φ]

/-- **Every aspherical space receives a pointed weak homotopy equivalence from the classifying
space** (Hatcher, Proposition 4.30 for `n = 1`). For an aspherical space `X`, of any kind, whose
fundamental group is identified with `G` by `eX`, there is a pointed weak homotopy equivalence
`f : classifyingSpace G → X` sending `classifyingSpaceBasepoint G` to `x` and inducing `eX⁻¹` under
`classifyingSpaceFundamentalGroupMulEquiv G`.

Unlike `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`, no hypothesis of CW type is
made on `X`, and a weak homotopy equivalence is the most one can ask for: the Warsaw circle is
aspherical with trivial fundamental group, and it is not homotopy equivalent to a point. -/
theorem IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace {G : Type u} [Group G]
    {X : Type u} [TopologicalSpace X] {x : X} (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (f : C(classifyingSpace G, X)) (hf : f (classifyingSpaceBasepoint G) = x),
      f.IsWeakHomotopyEquivalence ∧
        ∀ a, eX (FundamentalGroup.mapOfEq f hf a) =
          classifyingSpaceFundamentalGroupMulEquiv G a := by
  let hB := (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
  let φ := (classifyingSpaceFundamentalGroupMulEquiv G).trans eX.symm
  obtain ⟨f, hf, hfφ⟩ := exists_mapOfEq_classifyingSpace
    (fun k hk ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact hX.subsingleton_homotopyGroup n) φ.toMonoidHom
  refine ⟨f, hf, (hB.isWeakHomotopyEquivalence_iff hX hf).2 (hfφ ▸ φ.bijective), fun a ↦ ?_⟩
  rw [DFunLike.congr_fun hfφ a]
  simp [φ]

/-- **Every `K(G, 1)` space receives a weak homotopy equivalence from the classifying space.**
See `TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace` for a pointed weak
homotopy equivalence realizing a prescribed identification of the fundamental group with `G`. -/
theorem IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace
    {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne G X x) :
    ∃ f : C(classifyingSpace G, X), f.IsWeakHomotopyEquivalence := by
  obtain ⟨eX⟩ := hX.nonempty_fundamentalGroupMulEquiv
  obtain ⟨f, -, hf, -⟩ := hX.isAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace eX
  exact ⟨f, hf⟩

end TauCeti
