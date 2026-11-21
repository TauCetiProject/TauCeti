/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Affine
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Compactness.Compact
public import TauCeti.Topology.Homotopy.LocallyContractible

/-!
# Locally equiconnected spaces

A space `X` is **locally equiconnected** if nearby points can be joined by short paths depending
continuously on their endpoints: there are an open neighbourhood `W` of the diagonal in `X × X`
and a map `l : X × X → I → X`, continuous on `W × I`, such that for `(x, y) ∈ W` the path
`t ↦ l (x, y) t` runs from `x` to `y`, and `l (x, x)` is the constant path at `x`
(`TauCeti.IsEquiconnecting`, `TauCeti.LocallyEquiconnectedSpace`). This is Fox's notion; it is
the structure behind the local contractibility of absolute neighbourhood retracts.

Unlike local contractibility, local equiconnectedness is a single uniform piece of data, and so
it passes to mapping spaces out of a compact, locally compact space
(`TauCeti.Topology.Homotopy.LocallyEquiconnected.MappingSpace`). In particular the free loop
space of a closed manifold is locally path-connected and semilocally simply connected, which are
the hypotheses of covering space theory.

This file proves:

* a locally equiconnected space is locally contractible in the classical sense
  (`TauCeti.LocallyEquiconnectedSpace.locallyContractibleSpace`), hence locally path-connected
  and semilocally simply connected (instances);
* neighbourhood retracts of locally equiconnected spaces are locally equiconnected
  (`TauCeti.LocallyEquiconnectedSpace.of_retract`): if `e : Y → X` is continuous and
  `r : X → Y` is continuous on an open set `U ⊇ range e` with `r ∘ e = id`, then `Y` is locally
  equiconnected. Consequently so are homeomorphic copies
  (`Homeomorph.locallyEquiconnectedSpace`) and open subsets
  (`IsOpen.locallyEquiconnectedSpace`);
* subsingletons and real topological vector spaces, through straight segments, are locally
  equiconnected.

## Main definitions

* `TauCeti.IsEquiconnecting W l`: `l` is an equiconnecting map on the neighbourhood `W` of the
  diagonal.
* `TauCeti.LocallyEquiconnectedSpace X`: `X` admits an equiconnecting map.

## References

* R. H. Fox, *On fibre spaces. II*, Bull. Amer. Math. Soc. 49 (1943), 733–735.
* J. Dugundji, *Locally equiconnected spaces and absolute neighborhood retracts*, Fund. Math. 57
  (1965), 187–193.
-/

public section

open Set Function Topology unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `l` is an **equiconnecting map** on `W`: `W` is an open neighbourhood of the diagonal of
`X × X`, `l` is continuous on `W × I`, the path `l p` runs from `p.1` to `p.2` for `p ∈ W`, and
`l (x, x)` is the constant path at `x`. Outside `W` the values of `l` are irrelevant. -/
structure IsEquiconnecting (W : Set (X × X)) (l : X × X → I → X) : Prop where
  /-- The domain `W` is open. -/
  isOpen : IsOpen W
  /-- The domain `W` contains the diagonal. -/
  diagonal_subset : diagonal X ⊆ W
  /-- The connecting paths depend continuously on their endpoints and time. -/
  continuousOn : ContinuousOn (uncurry l) (W ×ˢ univ)
  /-- The connecting path of `p ∈ W` starts at `p.1`. -/
  apply_zero : ∀ p ∈ W, l p 0 = p.1
  /-- The connecting path of `p ∈ W` ends at `p.2`. -/
  apply_one : ∀ p ∈ W, l p 1 = p.2
  /-- The connecting path from a point to itself is constant. -/
  apply_self : ∀ x t, l (x, x) t = x

variable (X) in
/-- A space is **locally equiconnected** if it admits an equiconnecting map: nearby points are
joined by paths depending continuously on their endpoints, with constant paths on the diagonal. -/
class LocallyEquiconnectedSpace : Prop where
  /-- There is an equiconnecting map. -/
  exists_isEquiconnecting : ∃ (W : Set (X × X)) (l : X × X → I → X), IsEquiconnecting W l

namespace IsEquiconnecting

variable {W : Set (X × X)} {l : X × X → I → X}

/-- The domain of an equiconnecting map contains every diagonal pair. -/
theorem mk_self_mem (h : IsEquiconnecting W l) (x : X) : (x, x) ∈ W :=
  h.diagonal_subset (mem_diagonal x)

/-- Connecting paths between `W`-close endpoints varying continuously on `s`, at times varying
continuously on `s`, vary continuously on `s`. -/
theorem continuousOn_comp (h : IsEquiconnecting W l) {Z : Type*} [TopologicalSpace Z]
    {f g : Z → X} {τ : Z → I} {s : Set Z} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hτ : ContinuousOn τ s) (hW : ∀ z ∈ s, (f z, g z) ∈ W) :
    ContinuousOn (fun z => l (f z, g z) (τ z)) s :=
  h.continuousOn.comp (f := fun z => ((f z, g z), τ z)) ((hf.prodMk hg).prodMk hτ)
    fun z hz => ⟨hW z hz, trivial⟩

/-- Connecting paths between continuously varying `W`-close endpoints, at a continuously varying
time, vary continuously. -/
theorem continuous_comp (h : IsEquiconnecting W l) {Z : Type*} [TopologicalSpace Z]
    {f g : Z → X} {τ : Z → I} (hf : Continuous f) (hg : Continuous g) (hτ : Continuous τ)
    (hW : ∀ z, (f z, g z) ∈ W) : Continuous fun z => l (f z, g z) (τ z) :=
  continuousOn_univ.mp <| h.continuousOn_comp hf.continuousOn hg.continuousOn hτ.continuousOn
    fun z _ => hW z

/-- The pairs in `W` whose connecting path stays in an open set `U` form an open set. -/
theorem isOpen_inter_setOf_forall_mem (h : IsEquiconnecting W l) {U : Set X} (hU : IsOpen U) :
    IsOpen (W ∩ {p | ∀ t, l p t ∈ U}) := by
  have hO := h.continuousOn.isOpen_inter_preimage (h.isOpen.prod isOpen_univ) hU
  convert h.isOpen.inter (isOpen_forall_prodMk_mem continuous_id hO) using 1
  ext p
  simp +contextual [iff_def]

/-- A locally equiconnected space is locally contractible in the classical sense: the points
joined to `x` by connecting paths inside `U` form a neighbourhood of `x`, and the connecting paths
contract its inclusion into `U` onto `x`. -/
theorem locallyContractibleSpace (h : IsEquiconnecting W l) : LocallyContractibleSpace X := by
  intro x U hU
  obtain ⟨U', hU'U, hU', hxU'⟩ := mem_nhds_iff.mp hU
  let V := {y | (x, y) ∈ W ∧ ∀ t, l (x, y) t ∈ U'}
  have hV : IsOpen V := (h.isOpen_inter_setOf_forall_mem hU').preimage (.prodMk_right x)
  have hxV : x ∈ V := ⟨h.mk_self_mem x, fun t => (h.apply_self x t).symm ▸ hxU'⟩
  have hVU : V ⊆ U := fun y hy => hU'U (by simpa [h.apply_one _ hy.1] using hy.2 1)
  refine ⟨V, hVU, hV.mem_nhds hxV, ⟨x, hU'U hxU'⟩, ⟨?_⟩⟩
  -- Run the connecting path from `x` to `y` backwards, from `y` to `x`.
  have hc : Continuous fun p : I × V => l (x, (p.2 : X)) (σ p.1) :=
    h.continuous_comp continuous_const (by fun_prop) (by fun_prop) fun p => p.2.property.1
  exact
    { toFun := fun p => ⟨l (x, p.2) (σ p.1), hU'U (p.2.property.2 _)⟩
      continuous_toFun := hc.subtype_mk _
      map_zero_left := fun y => Subtype.ext <| by simp [h.apply_one _ y.property.1]
      map_one_left := fun y => Subtype.ext <| by simp [h.apply_zero _ y.property.1] }

/-- Transport of an equiconnecting map to a neighbourhood retract. -/
theorem retract (h : IsEquiconnecting W l) {e : Y → X} (he : Continuous e) {r : X → Y}
    {U : Set X} (hU : IsOpen U) (heU : range e ⊆ U) (hr : ContinuousOn r U)
    (hre : ∀ y, r (e y) = y) :
    IsEquiconnecting {p : Y × Y | (e p.1, e p.2) ∈ W ∧ ∀ t, l (e p.1, e p.2) t ∈ U}
      fun p t => r (l (e p.1, e p.2) t) where
  isOpen := (h.isOpen_inter_setOf_forall_mem hU).preimage (he.prodMap he)
  diagonal_subset := by
    rintro ⟨y, y'⟩ (rfl : y = y')
    exact ⟨h.mk_self_mem _, fun t => (h.apply_self _ t).symm ▸ heU (mem_range_self y)⟩
  continuousOn := hr.comp (h.continuousOn_comp (f := fun q : (Y × Y) × I => e q.1.1)
    (g := fun q => e q.1.2) (τ := Prod.snd) (by fun_prop) (by fun_prop) (by fun_prop)
      fun q hq => hq.1.1) fun q hq => hq.1.2 q.2
  apply_zero p hp := by simp only [h.apply_zero _ hp.1, hre]
  apply_one p hp := by simp only [h.apply_one _ hp.1, hre]
  apply_self y t := by simp only [h.apply_self, hre]

end IsEquiconnecting

namespace LocallyEquiconnectedSpace

/-- A locally equiconnected space is locally contractible in the classical sense. -/
theorem locallyContractibleSpace [LocallyEquiconnectedSpace X] : LocallyContractibleSpace X :=
  let ⟨_, _, h⟩ := exists_isEquiconnecting (X := X)
  h.locallyContractibleSpace

/-- A locally equiconnected space is locally path-connected. -/
instance (priority := 100) [LocallyEquiconnectedSpace X] : LocallyPathConnectedSpace X :=
  locallyContractibleSpace.locallyPathConnectedSpace

/-- A locally equiconnected space is semilocally simply connected. -/
instance (priority := 100) [LocallyEquiconnectedSpace X] : SemilocallySimplyConnectedSpace X :=
  .of_locallyContractibleSpace locallyContractibleSpace

/-- **Neighbourhood retracts.** If `e : Y → X` is continuous, and `r : X → Y` is continuous on an
open neighbourhood `U` of the image of `e` with `r ∘ e = id`, then `Y` is locally equiconnected
whenever `X` is. -/
theorem of_retract [LocallyEquiconnectedSpace X] {e : Y → X} (he : Continuous e) {r : X → Y}
    {U : Set X} (hU : IsOpen U) (heU : range e ⊆ U) (hr : ContinuousOn r U)
    (hre : ∀ y, r (e y) = y) : LocallyEquiconnectedSpace Y :=
  let ⟨_, _, h⟩ := exists_isEquiconnecting (X := X)
  ⟨⟨_, _, h.retract he hU heU hr hre⟩⟩

/-- A subsingleton is locally equiconnected, through constant paths. -/
instance (priority := 100) of_subsingleton [Subsingleton X] : LocallyEquiconnectedSpace X :=
  ⟨⟨univ, fun p _ => p.1,
    { isOpen := isOpen_univ
      diagonal_subset := subset_univ _
      continuousOn := by fun_prop
      apply_zero := fun _ _ => rfl
      apply_one := fun _ _ => Subsingleton.elim _ _
      apply_self := fun _ _ => rfl }⟩⟩

/-- A real topological vector space is locally equiconnected, through straight segments. -/
instance of_module {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] : LocallyEquiconnectedSpace E :=
  ⟨⟨univ, fun p t => AffineMap.lineMap p.1 p.2 (t : ℝ),
    { isOpen := isOpen_univ
      diagonal_subset := subset_univ _
      continuousOn := (Continuous.lineMap (by fun_prop) (by fun_prop) (by fun_prop)).continuousOn
      apply_zero := fun _ _ => by simp
      apply_one := fun _ _ => by simp
      apply_self := fun _ _ => by simp }⟩⟩

end LocallyEquiconnectedSpace

/-- Local equiconnectedness is invariant under homeomorphisms. -/
theorem _root_.Homeomorph.locallyEquiconnectedSpace (e : X ≃ₜ Y) [LocallyEquiconnectedSpace X] :
    LocallyEquiconnectedSpace Y :=
  .of_retract e.symm.continuous isOpen_univ (subset_univ _) e.continuous.continuousOn
    e.apply_symm_apply

/-- An open subset of a locally equiconnected space is locally equiconnected. -/
theorem _root_.IsOpen.locallyEquiconnectedSpace [LocallyEquiconnectedSpace X] {s : Set X}
    (hs : IsOpen s) : LocallyEquiconnectedSpace s := by
  classical
  rcases isEmpty_or_nonempty s with _ | hne
  · infer_instance
  obtain ⟨y₀⟩ := hne
  -- Retract onto `s` by the identity on `s`, with an arbitrary value outside `s`.
  let r : X → s := fun x => if hx : x ∈ s then ⟨x, hx⟩ else y₀
  have hr : ContinuousOn r s := by
    refine continuousOn_iff_continuous_domRestrict.mpr (continuous_id.congr fun x => ?_)
    simp [r, x.property]
  exact .of_retract continuous_subtypeVal hs (by simp) hr fun y => by simp [r, y.property]

end TauCeti
