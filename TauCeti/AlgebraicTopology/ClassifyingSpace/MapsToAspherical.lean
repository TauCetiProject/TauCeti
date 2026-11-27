/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Hom.Conj
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.Topology.CWComplex.Comparison
import TauCeti.Topology.Homotopy.Extension.Basepoint
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Maps from a CW space into an aspherical space

Let `X` be a path-connected space of CW type with a base point `x`, and `Y` a space whose higher
homotopy groups at `y` vanish, such as an aspherical space. Every homomorphism
`φ : π₁(X, x) →* π₁(Y, y)` is induced by a continuous map `f : X → Y` up to a change of base point:
there is a path `γ` from `f x` to `y` such that the map induced by `f`, followed by the change of
base point along `γ`, is `φ`
(`exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`).
This is the existence half of Hatcher's Proposition 1B.9 before the base point is moved; `x` is an
arbitrary point, and `X` and `Y` lie in independent universes.

When `{x}` is closed and has the homotopy extension property in `X` — as holds at every point of a
Hausdorff CW complex (`TauCeti.hasHomotopyExtensionProperty_singleton`) — extending a homotopy of
`f` with trace `γ` at `x` produces a basepoint-preserving map `(X, x) → (Y, y)` inducing `φ` on the
nose (`TauCeti.HasHomotopyExtensionProperty.exists_mapOfEq_of_subsingleton_homotopyGroup`,
`TauCeti.exists_mapOfEq`, `TauCeti.exists_mapOfEq_of_cwComplex`). Combined with pointed uniqueness
(`TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex`), this establishes Hatcher's Proposition 1B.9 in
full generality and its unbased consequence via basepoint change
(`TauCeti.homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex`):

* Pointed homotopy classes `[(X, x₀), (Y, y₀)]_*` correspond bijectively to homomorphisms
  `π₁(X, x₀) →* π₁(Y, y₀)` (`TauCeti.pointedHomotopyEquivMonoidHom`,
  `TauCeti.pointedHomotopyEquivMonoidHomOfCWComplex`, and categorically
  `TauCeti.fundamentalGroupFunctor_map_bijective_of_cwComplex`, Hatcher's Proposition 1B.9).
* Deduced from this when `Y` is path connected, free homotopy classes `[X, Y]` correspond
  bijectively to conjugacy classes of homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)`
  (`TauCeti.monoidHomConjSetoid`) via `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex`.

First `X` is replaced by a homotopy equivalent CW complex, which is Hausdorff. The map then
factors through the cellular classifying space `C` of a presentation of `π₁(X, x)`. Killing the
higher homotopy groups of `X` embeds it into an aspherical space `X'` with the same fundamental
group. The cellular model maps into `X'` by a weak homotopy equivalence `e` inducing that
identification, and into `Y` by a map `g` inducing `φ`; both maps exist because the targets have no
higher homotopy (`TauCeti.exists_mapOfEq_cellularClassifyingSpace`). Since `X` has CW type, the
inclusion of `X` into `X'` lifts through `e` up to homotopy to a map `ℓ : X → C`
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`), and `g ∘ ℓ` realizes `φ` up to
the change of base point that corrects the trace of that homotopy
(`ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp_eq_mapOfEq`). The
cellular model, `X'` and `Y` are lifted to a common universe with `ULift`; `X` is not lifted.

## Main definitions

* `TauCeti.pointedHomotopyEquivMonoidHom` and
  `TauCeti.pointedHomotopyEquivMonoidHomOfCWComplex`: the bijection between pointed homotopy
  classes `[(X, x₀), (Y, y₀)]_*` and `π₁(X, x₀) →* π₁(Y, y₀)` (Hatcher, Proposition 1B.9).
* `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex`: the bijection between free
  homotopy classes `[X, Y]` and `Quotient (monoidHomConjSetoid (π₁(X, x₀)) (π₁(Y, y₀)))`, deduced
  from Hatcher's Proposition 1B.9.

## Main results

* `exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`: every
  homomorphism from `π₁(X, x)` to the fundamental group of a space with vanishing higher
  homotopy groups is induced by a map, up to a change of base point in the target.
* `TauCeti.HasHomotopyExtensionProperty.exists_mapOfEq_of_subsingleton_homotopyGroup`,
  `TauCeti.exists_mapOfEq`, `TauCeti.exists_mapOfEq_of_cwComplex`: pointed realization of
  homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)` (Hatcher, Proposition 1B.9, existence).
* `TauCeti.fundamentalGroupFunctor_map_bijective_of_cwComplex`: in `PointedHomotopyCat`,
  `PointedHomotopyCat.fundamentalGroupFunctor.map` is bijective out of any path-connected Hausdorff
  CW complex into a based space with vanishing higher homotopy groups at its base point.
* `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path`: computation of the
  unbased classification bijection on an arbitrary map via a path from `f x₀` to `y₀`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9, and Section 4.1, Proposition 4.22.
-/

public section

noncomputable section

open Set Topology
open scoped Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

/-- The case of
`TauCeti.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`
for a Hausdorff `X` and with `Y` in the universe `max u v`, where the cellular model of `π₁(X, x)`
and the lifted space `X'` live. -/
private theorem exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    {Y : Type (max u v)} [TopologicalSpace Y] {y : Y} (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWType X] [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (γ : Path (f x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map f x a) = φ a := by
  -- The aspherical space `X'` containing `X`, lifted to the universe `max u v`.
  let X' := killHomotopyGroups 2 (TopCat.of X) x
  let incl := killHomotopyGroupsIncl 2 (TopCat.of X) x
  let eX : X' ≃ₜ ULift.{v} X' := Homeomorph.ulift.symm
  let ι : C(X, ULift.{v} X') := (eX : C(X', ULift.{v} X')).comp incl.hom
  have hZ : IsAspherical (ULift.{v} X') (ι x) :=
    (eX.isWeakHomotopyEquivalence.isAspherical_iff (incl x)).1
      (isEilenbergMacLaneSpaceOne_killHomotopyGroups (TopCat.of X) x).isAspherical
  -- The inclusion `ι` induces an isomorphism of fundamental groups.
  let ιπ : FundamentalGroup X x ≃* FundamentalGroup (ULift.{v} X') (ι x) :=
    (killHomotopyGroupsFundamentalGroupMulEquiv 2 (TopCat.of X) x one_lt_two).trans
      (homeomorphMulEquiv eX (incl x))
  have hιπ (a : FundamentalGroup X x) : ιπ a = mapOfEq ι (rfl : ι x = ι x) a := by
    rw [MulEquiv.trans_apply, killHomotopyGroupsFundamentalGroupMulEquiv_apply,
      homeomorphMulEquiv_apply]
    exact mapOfEq_mapOfEq_eq_mapOfEq rfl rfl rfl rfl a
  -- The cellular classifying space `C` of a presentation of `π₁(X, x)`, in the universe `max u v`.
  obtain ⟨R, -, -, hC⟩ := exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace
    (ULift.{v} (FundamentalGroup X x))
  obtain ⟨ψ₀⟩ := hC.nonempty_fundamentalGroupMulEquiv
  let ψ := ψ₀.trans MulEquiv.ulift
  -- The weak homotopy equivalence `e : C → ULift X'` inducing `ιπ ∘ ψ`, and `g : C → Y`
  -- inducing `φ ∘ ψ`.
  obtain ⟨e, he, heπ, heW⟩ :=
    exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hZ (ψ.trans ιπ)
  obtain ⟨g, hg, hgπ⟩ := exists_mapOfEq_cellularClassifyingSpace R hY (φ.comp ψ.toMonoidHom)
  -- The lift `ℓ : X → C` of `ι` through `e`; then `g ∘ ℓ` induces `φ ∘ ιπ⁻¹ ∘ ι_* = φ`.
  obtain ⟨ℓ, ⟨H⟩⟩ := heW.exists_comp_homotopic ι
  obtain ⟨γ, hγ⟩ := H.exists_path_fundamentalGroupMulEquivOfPath_map_comp_eq_mapOfEq he hg rfl
    (φ.comp ιπ.symm.toMonoidHom) (MonoidHom.ext fun a ↦ by simp [heπ, hgπ])
  exact ⟨g.comp ℓ, γ, fun a ↦ (hγ a).trans (congrArg φ (ιπ.symm_apply_eq.2 (hιπ a).symm))⟩

/-- **Homomorphisms into the fundamental group of a space with vanishing higher homotopy groups
are induced by maps, up to a change of base point** (the existence half of Hatcher, Proposition
1B.9, before the base point is moved). Let `X` be a path-connected space of CW type, such as a
path-connected Hausdorff CW complex, with an arbitrary base point `x`, and let the homotopy groups
`π_k(Y, y)` vanish for `k ≥ 2`, as they do when `Y` is aspherical at `y`. For every
homomorphism `φ : π₁(X, x) →* π₁(Y, y)` there are a continuous map `f : X → Y` and a path `γ` from
`f x` to `y` such that the map induced by `f`, followed by the change of base point along `γ`, is
`φ`. The spaces `X` and `Y` lie in independent universes. -/
theorem exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup
    {Y : Type v} [TopologicalSpace Y] {y : Y} (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
    {X : Type u} [TopologicalSpace X] [CWType X] [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (γ : Path (f x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map f x a) = φ a := by
  -- Replace `X` by a homotopy equivalent CW complex `D`, which is Hausdorff.
  obtain ⟨Z, _, _, D, _, ⟨e⟩⟩ := (inferInstance : CWType X).exists_homotopyEquiv
  have he := e.isWeakHomotopyEquivalence
  have : PathConnectedSpace D := he.pathConnectedSpace_iff.1 inferInstance
  let eπ : FundamentalGroup X x ≃* FundamentalGroup D (e.toFun x) :=
    MulEquiv.ofBijective (map e.toFun x) (e.fundamentalGroup_map_bijective x)
  -- Replace `Y` by `ULift Y`, in the universe `max u v`.
  let eY : Y ≃ₜ ULift.{u} Y := Homeomorph.ulift.symm
  let down : C(ULift.{u} Y, Y) := eY.symm
  obtain ⟨f, γ, hγ⟩ := exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    (fun k hk ↦ (HomotopyGroup.homeomorphEquiv eY y).subsingleton_congr.1 (hY k hk)) (e.toFun x)
    ((homeomorphMulEquiv eY y).toMonoidHom.comp (φ.comp eπ.symm.toMonoidHom))
  refine ⟨down.comp (f.comp e.toFun), γ.map down.continuous, fun a ↦ ?_⟩
  have h := map_fundamentalGroupMulEquivOfPath down γ (map f (e.toFun x) (eπ a))
  simp only [hγ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
  rw [← mapOfEq_rfl down] at h
  simp only [map_comp, MonoidHom.comp_apply]
  exact h.symm.trans ((homeomorphMulEquiv_symm_apply eY y _).symm.trans
    ((homeomorphMulEquiv eY y).symm_apply_apply (φ a)))

/-! ### Pointed existence and classification (Hatcher, Proposition 1B.9) -/

/-- **Pointed maps out of a cofibrantly based CW space realize every `π₁`-homomorphism.** If `X`
is path connected of CW type, `{x}` is closed with the homotopy extension property in `X`, and
`πₙ(Y, y) = 0` for `n ≥ 2` (with `X` and `Y` in independent universes and without assuming `Y` is
path connected), then every homomorphism `φ : π₁(X, x) →* π₁(Y, y)` is induced by a pointed map
`(X, x) → (Y, y)`. -/
theorem HasHomotopyExtensionProperty.exists_mapOfEq_of_subsingleton_homotopyGroup
    {X : Type u} [TopologicalSpace X] [CWType X] [PathConnectedSpace X] {x : X}
    (hx : HasHomotopyExtensionProperty ({x} : Set X)) (hxc : IsClosed ({x} : Set X))
    {Y : Type v} [TopologicalSpace Y] {y : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y))
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (hf : f x = y), mapOfEq f hf = φ := by
  obtain ⟨f₀, γ, hγ⟩ :=
    exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY n) x φ
  obtain ⟨f, hf, -, -, hfπ⟩ :=
    hx.exists_mapOfEq_eq_fundamentalGroupMulEquivOfPath_map hxc f₀ γ
  exact ⟨f, hf, MonoidHom.ext fun a ↦ (hfπ a).trans (hγ a)⟩

section CW

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y]

/-- **Pointed maps out of a path-connected Hausdorff CW complex realize every `π₁`-homomorphism
(Hatcher, Proposition 1B.9, existence).** Let `C` be a path-connected CW complex in a Hausdorff
space `X` with base point `x₀`, and let `(Y, y₀)` be a based space (in any universe, without
assuming `Y` is path connected) with `πₙ(Y, y₀) = 0` for all `n ≥ 2`. Every homomorphism
`φ : π₁(C, x₀) →* π₁(Y, y₀)` is induced by a continuous map `(C, x₀) → (Y, y₀)`. -/
theorem exists_mapOfEq {C : Set X} [CWComplex C] [PathConnectedSpace C] {x₀ : C} {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (φ : FundamentalGroup C x₀ →* FundamentalGroup Y y₀) :
    ∃ (f : C(C, Y)) (hf : f x₀ = y₀), mapOfEq f hf = φ :=
  (hasHomotopyExtensionProperty_singleton
    (notMem_empty _)).exists_mapOfEq_of_subsingleton_homotopyGroup isClosed_singleton hY φ

/-- **Pointed maps out of a path-connected Hausdorff space with a CW structure on `univ` realize
every `π₁`-homomorphism (Hatcher, Proposition 1B.9, existence).** -/
theorem exists_mapOfEq_of_cwComplex [CWComplex (univ : Set X)] [PathConnectedSpace X]
    {x₀ : X} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (φ : FundamentalGroup X x₀ →* FundamentalGroup Y y₀) :
    ∃ (f : C(X, Y)) (hf : f x₀ = y₀), mapOfEq f hf = φ :=
  (hasHomotopyExtensionProperty_singleton_of_cwComplex
    x₀).exists_mapOfEq_of_subsingleton_homotopyGroup isClosed_singleton hY φ

/-- **Pointed homotopy classification of maps out of a CW complex on `univ` (Hatcher, Proposition
1B.9, pointed form).** -/
def pointedHomotopyEquivMonoidHomOfCWComplex [CWComplex (univ : Set X)] [PathConnectedSpace X]
    (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (pointedHomotopySetoid x₀ y₀) ≃
      (FundamentalGroup X x₀ →* FundamentalGroup Y y₀) :=
  Equiv.ofBijective
    (Quotient.lift (fun f : {f : C(X, Y) // f x₀ = y₀} ↦ mapOfEq f.val f.property)
      fun f g h ↦ mapOfEq_eq_of_homotopicRel f.property g.property
        (mem_singleton x₀) (pointedHomotopySetoid_iff.1 h))
    ⟨Quotient.ind₂ fun f g hfg ↦ Quotient.sound
        (pointedHomotopySetoid_iff.2
          (homotopicRel_of_mapOfEq_eq_of_cwComplex hY f.property g.property hfg)),
      fun φ ↦ by
        obtain ⟨f, hf, hfφ⟩ := exists_mapOfEq_of_cwComplex hY φ
        exact ⟨⟦⟨f, hf⟩⟧, hfφ⟩⟩

@[simp]
theorem pointedHomotopyEquivMonoidHomOfCWComplex_mk [CWComplex (univ : Set X)]
    [PathConnectedSpace X] (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : {f : C(X, Y) // f x₀ = y₀}) :
    pointedHomotopyEquivMonoidHomOfCWComplex x₀ hY ⟦f⟧ = mapOfEq f.val f.property := by
  unfold pointedHomotopyEquivMonoidHomOfCWComplex
  rfl

/-- **Pointed homotopy classification of maps into an aspherical space (Hatcher, Proposition 1B.9,
pointed form).** For a path-connected Hausdorff CW complex `C` with base point `x₀` and a based
space `(Y, y₀)` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, sending a pointed map `(C, x₀) → (Y, y₀)` to its
induced homomorphism on `π₁` is a bijection from pointed homotopy classes to
`π₁(C, x₀) →* π₁(Y, y₀)`. -/
def pointedHomotopyEquivMonoidHom {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (pointedHomotopySetoid x₀ y₀) ≃
      (FundamentalGroup C x₀ →* FundamentalGroup Y y₀) :=
  letI := cwComplexUniv C
  pointedHomotopyEquivMonoidHomOfCWComplex x₀ hY

@[simp]
theorem pointedHomotopyEquivMonoidHom_mk {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : {f : C(C, Y) // f x₀ = y₀}) :
    pointedHomotopyEquivMonoidHom x₀ hY ⟦f⟧ = mapOfEq f.val f.property := by
  let _ := cwComplexUniv C
  exact pointedHomotopyEquivMonoidHomOfCWComplex_mk x₀ hY f

end CW

open CategoryTheory in
/-- **Pointed maps out of a path-connected Hausdorff CW complex are classified by `π₁` (Hatcher,
Proposition 1B.9).** If the homotopy groups of `Y` at its base point vanish from degree `2` on,
then sending a pointed homotopy class `X ⟶ Y` in `PointedHomotopyCat` to its induced homomorphism
on fundamental groups is bijective. -/
theorem fundamentalGroupFunctor_map_bijective_of_cwComplex
    {X Y : BasedTopologicalSpace.{u}} [T2Space X.carrier]
    [CWComplex (univ : Set X.carrier)] [PathConnectedSpace X.carrier]
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y.carrier Y.basepoint)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj X)
      (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    simp only [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map] at hab
    exact (PointedHomotopyCat.quotient_map_eq_iff f g).2
      (homotopicRel_of_mapOfEq_eq_of_cwComplex hY f.map_basepoint g.map_basepoint
        (by
          have h' := congrArg GrpCat.Hom.hom hab
          rw [BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
            BasedTopologicalSpace.fundamentalGroupFunctor_map_hom] at h'
          exact h'))
  · let φ : FundamentalGroup X.carrier X.basepoint →* FundamentalGroup Y.carrier Y.basepoint :=
      ψ.hom
    obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_of_cwComplex (x₀ := X.basepoint) hY φ
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map _)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

/-! ### Unbased homotopy classification via conjugacy classes of homomorphisms -/

section Unbased

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [PathConnectedSpace Y]

/-- Transporting `FundamentalGroup.map f x₀` back to `y₀` along a chosen path in `Y`; its class
modulo `monoidHomConjSetoid` is independent of the path and depends only on the free homotopy
class of `f`. -/
private def unbasedInducedMonoidHom {Z : Type*} [TopologicalSpace Z] (x₀ : Z) (y₀ : Y)
    (f : C(Z, Y)) : FundamentalGroup Z x₀ →* FundamentalGroup Y y₀ :=
  (fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath y₀ (f x₀))).symm.toMonoidHom.comp (map f x₀)

@[simp]
private lemma unbasedInducedMonoidHom_apply {Z : Type*} [TopologicalSpace Z] (x₀ : Z) (y₀ : Y)
    (f : C(Z, Y)) (a : FundamentalGroup Z x₀) :
    unbasedInducedMonoidHom x₀ y₀ f a =
      (fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath y₀ (f x₀))).symm
        (map f x₀ a) :=
  rfl

/-- Transporting `unbasedInducedMonoidHom x₀ y₀ f` by conjugation with the loop `α · γ` at `y₀`
recovers basepoint change along `γ : Path (f x₀) y₀` composed with `map f x₀`. -/
private lemma monoidHomConjSetoid_unbasedInducedMonoidHom_comp {Z : Type*} [TopologicalSpace Z]
    (x₀ : Z) (y₀ : Y) (f : C(Z, Y)) (γ : Path (f x₀) y₀) :
    monoidHomConjSetoid _ _ (unbasedInducedMonoidHom x₀ y₀ f)
      ((fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)) := by
  let α := PathConnectedSpace.somePath y₀ (f x₀)
  refine monoidHomConjSetoid_iff.2
    ⟨fromPath (Path.Homotopic.Quotient.mk (α.trans γ)), fun a ↦ ?_⟩
  simpa only [fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
    unbasedInducedMonoidHom_apply, MulEquiv.apply_symm_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, α] using
    (fundamentalGroupMulEquivOfPath_loop_apply (α.trans γ)
      (unbasedInducedMonoidHom x₀ y₀ f a)).symm

private lemma monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f g : C(X, Y)) :
    monoidHomConjSetoid _ _ (unbasedInducedMonoidHom x₀ y₀ f) (unbasedInducedMonoidHom x₀ y₀ g) ↔
      f.Homotopic g := by
  have hYg (n : ℕ) : Subsingleton (π_ (n + 2) Y (g x₀)) :=
    (homotopyGroupEquivOfPath (PathConnectedSpace.somePath y₀ (g x₀))).subsingleton_congr.mp (hY n)
  rw [homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex x₀ hYg]
  set αf := PathConnectedSpace.somePath y₀ (f x₀)
  set αg := PathConnectedSpace.somePath y₀ (g x₀)
  constructor
  · -- A conjugating loop `δ` at `y₀` yields the path `αf⁻¹ · (δ · αg)` from `f x₀` to `g x₀`.
    intro h
    obtain ⟨c, hc⟩ := monoidHomConjSetoid_iff.1 h
    obtain ⟨δ, hδ⟩ := Quotient.exists_rep c.asHom
    have hc_eq : c = fromPath (Path.Homotopic.Quotient.mk δ) := by ext; exact hδ.symm
    refine ⟨αf.symm.trans (δ.trans αg), fun a ↦ ?_⟩
    have hconj : fundamentalGroupMulEquivOfPath δ
        (unbasedInducedMonoidHom x₀ y₀ f a) = unbasedInducedMonoidHom x₀ y₀ g a :=
      (fundamentalGroupMulEquivOfPath_loop_apply δ _).trans (hc_eq ▸ hc a)
    simpa only [fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
      fundamentalGroupMulEquivOfPath_symm, unbasedInducedMonoidHom_apply,
      MulEquiv.apply_symm_apply, αf, αg] using
      congrArg (fundamentalGroupMulEquivOfPath αg) hconj
  · -- Conversely, an intertwining path `γ` composes with `αg⁻¹` to a path from `f x₀` to `y₀`.
    rintro ⟨γ, hγ⟩
    have hfg_eq :
        (fundamentalGroupMulEquivOfPath (γ.trans αg.symm)).toMonoidHom.comp (map f x₀) =
          unbasedInducedMonoidHom x₀ y₀ g :=
      MonoidHom.ext fun a ↦ by simp [αg, hγ a]
    exact hfg_eq ▸ monoidHomConjSetoid_unbasedInducedMonoidHom_comp x₀ y₀ f (γ.trans αg.symm)

/-- **Unbased homotopy classification of maps out of a CW complex on `univ` (deduced from Hatcher,
Proposition 1B.9).** For a path-connected Hausdorff CW complex `X` with base point `x₀` and a
path-connected space `Y` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, free homotopy classes `[X, Y]` are in
canonical bijection with conjugacy classes of homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)`
(`TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path`). -/
def homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex [CWComplex (univ : Set X)]
    [PathConnectedSpace X] (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (homotopicSetoid X Y) ≃
      Quotient (monoidHomConjSetoid (FundamentalGroup X x₀) (FundamentalGroup Y y₀)) :=
  Equiv.ofBijective
    (Quotient.lift (s := homotopicSetoid X Y)
      (fun f : C(X, Y) ↦ Quotient.mk (monoidHomConjSetoid _ _) (unbasedInducedMonoidHom x₀ y₀ f))
      fun f g h ↦ Quotient.sound
        ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).2
          (homotopicSetoid_iff.1 h)))
    ⟨Quotient.ind₂ (s₁ := homotopicSetoid X Y) (s₂ := homotopicSetoid X Y) fun f g h ↦
        Quotient.sound (s := homotopicSetoid X Y) (homotopicSetoid_iff.2
          ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).1
            (Quotient.exact h))),
      Quotient.ind fun ψ ↦ by
        obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_of_cwComplex hY ψ
        refine ⟨Quotient.mk (homotopicSetoid X Y) f, Quotient.sound ?_⟩
        rcases hf with rfl
        have hψ :
            (fundamentalGroupMulEquivOfPath (Path.refl (f x₀))).toMonoidHom.comp (map f x₀) = ψ :=
          MonoidHom.ext fun a ↦ by simpa [mapOfEq_rfl] using DFunLike.congr_fun hfψ a
        exact hψ ▸ monoidHomConjSetoid_unbasedInducedMonoidHom_comp x₀ (f x₀) f (Path.refl (f x₀))⟩

/-- On any map `f : C(X, Y)` and any path `γ : Path (f x₀) y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the free homotopy class of `f` to
the conjugacy class of `(fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)`. -/
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f : C(X, Y)) (γ : Path (f x₀) y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk (homotopicSetoid X Y) f) =
      Quotient.mk (monoidHomConjSetoid _ _)
        ((fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)) := by
  rw [homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex.eq_1]
  exact Quotient.sound (monoidHomConjSetoid_unbasedInducedMonoidHom_comp x₀ y₀ f γ)

/-- On any map `f : C(X, Y)` sending `x₀` to `y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the class of `f` to the conjugacy
class of `FundamentalGroup.mapOfEq f hf`. -/
@[simp]
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) {f : C(X, Y)} (hf : f x₀ = y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk (homotopicSetoid X Y) f) =
      Quotient.mk (monoidHomConjSetoid _ _) (mapOfEq f hf) := by
  rcases hf with rfl
  simpa [mapOfEq_rfl] using
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path x₀ hY f (Path.refl (f x₀))

/-- **Unbased homotopy classification of maps out of a path-connected Hausdorff CW complex (deduced
from Hatcher, Proposition 1B.9).** For a path-connected CW complex `C` in a Hausdorff space `X` with
base point `x₀` and a path-connected space `Y` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, free homotopy
classes `Quotient (homotopicSetoid C Y)` correspond bijectively to conjugacy classes
`Quotient (monoidHomConjSetoid (FundamentalGroup C x₀) (FundamentalGroup Y y₀))`, sending `⟦f⟧` via
any path from `f x₀` to `y₀` (`TauCeti.homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path`). -/
def homotopicQuotientEquivMonoidHomConjQuotient {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (homotopicSetoid C Y) ≃
      Quotient (monoidHomConjSetoid (FundamentalGroup C x₀) (FundamentalGroup Y y₀)) :=
  letI := cwComplexUniv C
  homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY

/-- On any map `f : C(C, Y)` and any path `γ : Path (f x₀) y₀`,
`homotopicQuotientEquivMonoidHomConjQuotient` sends the free homotopy class of `f` to the
conjugacy class of `(fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)`. -/
theorem homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : C(C, Y)) (γ : Path (f x₀) y₀) :
    homotopicQuotientEquivMonoidHomConjQuotient x₀ hY
        (Quotient.mk (homotopicSetoid C Y) f) =
      Quotient.mk (monoidHomConjSetoid _ _)
        ((fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)) := by
  let _ := cwComplexUniv C
  exact homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path x₀ hY f γ

/-- On any map `f : C(C, Y)` sending `x₀` to `y₀`,
`homotopicQuotientEquivMonoidHomConjQuotient` sends the class of `f` to the conjugacy class of
`FundamentalGroup.mapOfEq f hf`. -/
@[simp]
theorem homotopicQuotientEquivMonoidHomConjQuotient_mk_of_eq {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f : C(C, Y)} (hf : f x₀ = y₀) :
    homotopicQuotientEquivMonoidHomConjQuotient x₀ hY
        (Quotient.mk (homotopicSetoid C Y) f) =
      Quotient.mk (monoidHomConjSetoid _ _) (mapOfEq f hf) := by
  let _ := cwComplexUniv C
  exact homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq x₀ hY hf

end Unbased

end TauCeti
