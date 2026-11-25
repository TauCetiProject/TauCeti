/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Algebra.Group.Hom.Conj
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.Homotopic.Rel
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
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
`TauCeti.exists_mapOfEq`, `TauCeti.exists_mapOfEq_of_cwComplex`). Combined with pointed and free
homotopy uniqueness (`TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex`,
`TauCeti.homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex`), this yields the
full pointed and unbased classification bijections of Hatcher's Proposition 1B.9:

* Pointed homotopy classes `[(X, x₀), (Y, y₀)]_*` correspond bijectively to homomorphisms
  `π₁(X, x₀) →* π₁(Y, y₀)` (`TauCeti.pointedHomotopyEquivMonoidHom`,
  `TauCeti.pointedHomotopyEquivMonoidHomOfCWComplex`).
* When `Y` is path connected, free homotopy classes `[X, Y]` correspond bijectively to conjugacy
  classes of homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)` (`TauCeti.monoidHomConjSetoid`) via
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient` and
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
  classes `[(X, x₀), (Y, y₀)]_*` and `π₁(X, x₀) →* π₁(Y, y₀)`.
* `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex`: the bijection between free
  homotopy classes `[X, Y]` and `Quotient (monoidHomConjSetoid (π₁(X, x₀)) (π₁(Y, y₀)))`.

## Main results

* `exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`: every
  homomorphism from `π₁(X, x)` to the fundamental group of a space with vanishing higher
  homotopy groups is induced by a map, up to a change of base point in the target.
* `TauCeti.HasHomotopyExtensionProperty.exists_mapOfEq_of_subsingleton_homotopyGroup`,
  `TauCeti.exists_mapOfEq`, `TauCeti.exists_mapOfEq_of_cwComplex`: pointed realization of
  homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)` (Hatcher, Proposition 1B.9, existence).
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

omit [PathConnectedSpace Y] in
/-- Basepoint change along a three-step right-associated composite `p · (q · r)` applies the three
basepoint-change equivalences in turn. -/
private lemma fundamentalGroupMulEquivOfPath_trans_trans_apply {w₀ w₁ w₂ w₃ : Y}
    (p : Path w₀ w₁) (q : Path w₁ w₂) (r : Path w₂ w₃) (z : FundamentalGroup Y w₀) :
    fundamentalGroupMulEquivOfPath (p.trans (q.trans r)) z =
      fundamentalGroupMulEquivOfPath r
        (fundamentalGroupMulEquivOfPath q (fundamentalGroupMulEquivOfPath p z)) := by
  rw [fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
    fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply]

private lemma monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f g : C(X, Y)) :
    monoidHomConjSetoid _ _ (unbasedInducedMonoidHom x₀ y₀ f) (unbasedInducedMonoidHom x₀ y₀ g) ↔
      f.Homotopic g := by
  have hYg (n : ℕ) : Subsingleton (π_ (n + 2) Y (g x₀)) :=
    (homotopyGroupEquivOfPath (PathConnectedSpace.somePath y₀ (g x₀))).subsingleton_congr.mp (hY n)
  rw [homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex x₀ hYg,
    monoidHomConjSetoid_iff]
  set αf := PathConnectedSpace.somePath y₀ (f x₀)
  set αg := PathConnectedSpace.somePath y₀ (g x₀)
  constructor
  · -- A conjugating loop `δ` at `y₀` yields the path `αf⁻¹ · (δ · αg)` from `f x₀` to `g x₀`.
    rintro ⟨c, hc⟩
    obtain ⟨δ, hδ⟩ := Quotient.exists_rep c.asHom
    have hc_eq : c = fromPath (Path.Homotopic.Quotient.mk δ) := by ext; exact hδ.symm
    refine ⟨αf.symm.trans (δ.trans αg), fun a ↦ ?_⟩
    have hconj : fundamentalGroupMulEquivOfPath δ
        (unbasedInducedMonoidHom x₀ y₀ f a) = unbasedInducedMonoidHom x₀ y₀ g a := by
      rw [fundamentalGroupMulEquivOfPath_eq_conj, MulAut.conj_apply, ← hc_eq]
      exact hc a
    rw [fundamentalGroupMulEquivOfPath_trans_trans_apply, fundamentalGroupMulEquivOfPath_symm,
      ← unbasedInducedMonoidHom_apply, hconj, unbasedInducedMonoidHom_apply,
      MulEquiv.apply_symm_apply]
  · -- Conversely, an intertwining path `γ` closes up with `αf` and `αg⁻¹` to a loop at `y₀`.
    rintro ⟨γ, hγ⟩
    let δ : Path y₀ y₀ := αf.trans (γ.trans αg.symm)
    refine ⟨fromPath (Path.Homotopic.Quotient.mk δ), fun a ↦ ?_⟩
    rw [← MulAut.conj_apply, ← fundamentalGroupMulEquivOfPath_eq_conj,
      unbasedInducedMonoidHom_apply, unbasedInducedMonoidHom_apply,
      fundamentalGroupMulEquivOfPath_trans_trans_apply, MulEquiv.apply_symm_apply, hγ a,
      fundamentalGroupMulEquivOfPath_symm]

/-- **Unbased homotopy classification of maps out of a CW complex on `univ` (Hatcher, Proposition
1B.9).** For a path-connected Hausdorff CW complex `X` with base point `x₀` and a path-connected
space `Y` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, free homotopy classes `[X, Y]` are in canonical
bijection with conjugacy classes of homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)`. -/
def homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex [CWComplex (univ : Set X)]
    [PathConnectedSpace X] (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := Y), ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient (monoidHomConjSetoid (FundamentalGroup X x₀) (FundamentalGroup Y y₀)) :=
  let s : Setoid C(X, Y) := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩
  Equiv.ofBijective
    (Quotient.lift (s := s)
      (fun f : C(X, Y) ↦ Quotient.mk (monoidHomConjSetoid _ _) (unbasedInducedMonoidHom x₀ y₀ f))
      fun f g h ↦ Quotient.sound
        ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).2 h))
    ⟨Quotient.ind₂ (s₁ := s) (s₂ := s) fun f g h ↦ Quotient.sound (s := s)
        ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).1
          (Quotient.exact h)),
      Quotient.ind fun ψ ↦ by
        obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_of_cwComplex hY ψ
        refine ⟨Quotient.mk s f, Quotient.sound (monoidHomConjSetoid_iff.2 ?_)⟩
        rcases hf with rfl
        let α := PathConnectedSpace.somePath (f x₀) (f x₀)
        refine ⟨fromPath (Path.Homotopic.Quotient.mk α), fun a ↦ ?_⟩
        rw [← MulAut.conj_apply, ← fundamentalGroupMulEquivOfPath_eq_conj, ← hfψ,
          mapOfEq_rfl, unbasedInducedMonoidHom_apply]
        exact (fundamentalGroupMulEquivOfPath α).apply_symm_apply _⟩

/-- On any map `f : C(X, Y)` and any path `γ : Path (f x₀) y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the free homotopy class of `f` to
the conjugacy class of `(fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)`. -/
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f : C(X, Y)) (γ : Path (f x₀) y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _)
        ((fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)) := by
  unfold homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex
  refine Quotient.sound (monoidHomConjSetoid_iff.2 ?_)
  let α := PathConnectedSpace.somePath y₀ (f x₀)
  refine ⟨fromPath (Path.Homotopic.Quotient.mk (α.trans γ)), fun a ↦ ?_⟩
  rw [← MulAut.conj_apply, ← fundamentalGroupMulEquivOfPath_eq_conj,
    fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply, unbasedInducedMonoidHom_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact congrArg (fundamentalGroupMulEquivOfPath γ)
    ((fundamentalGroupMulEquivOfPath α).apply_symm_apply _)

/-- On any map `f : C(X, Y)` sending `x₀` to `y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the class of `f` to the conjugacy
class of `FundamentalGroup.mapOfEq f hf`. -/
@[simp]
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) {f : C(X, Y)} (hf : f x₀ = y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _) (mapOfEq f hf) := by
  rcases hf with rfl
  simpa [mapOfEq_rfl] using
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path x₀ hY f (Path.refl (f x₀))

/-- **Unbased homotopy classification of maps into a path-connected aspherical space (Hatcher,
Proposition 1B.9).** -/
def homotopicQuotientEquivMonoidHomConjQuotient {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient ⟨ContinuousMap.Homotopic (X := C) (Y := Y), ContinuousMap.Homotopic.equivalence⟩ ≃
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
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
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
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _) (mapOfEq f hf) := by
  let _ := cwComplexUniv C
  exact homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq x₀ hY hf

end Unbased

end TauCeti
