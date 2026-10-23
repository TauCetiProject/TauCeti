/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.Homotopy.Product
-- Private: `Path.Homotopic.refl_of_forall_mem_of_nullhomotopic` is used only in a proof below,
-- so this import is not re-exported.
import TauCeti.Topology.Homotopy.Path

/-!
# Semilocally simply connected spaces

A topological space `X` is *semilocally simply connected* if every point `x` has a
neighbourhood `U` such that every loop in `U` based at `x` is null-homotopic *in `X`*. This is
the standing point-set hypothesis (alongside path-connectedness and local path-connectedness)
under which the universal cover of a space exists; see the universal-covers roadmap. Mathlib
master has `SimplyConnectedSpace` and the local notions `LocallyContractibleSpace` and
`StronglyLocallyContractibleSpace`, but no semilocal simple connectivity; the predicate follows
Kim Morrison's unmerged mathlib4#38292 (see the References below).

The condition is genuinely *semi*local: the null-homotopy is allowed to leave `U` and use the
whole of `X`. It is therefore weaker than asking each `U` to be simply connected on its own (the
local notion); the constructor
`SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected` records that
implication. The classical local-contractibility hypothesis `LocallyContractibleSpace` is also
enough (`SemilocallySimplyConnectedSpace.of_locallyContractibleSpace`), and through it every
strongly locally contractible space is semilocally simply connected. Discrete spaces are also
instances, witnessed by singleton neighbourhoods.

## Main declarations

* `SemilocallySimplyConnectedAt`: the pointwise predicate.
* `TauCeti.SemilocallySimplyConnectedSpace`: the predicate at every point, as a typeclass.
* `SemilocallySimplyConnectedAt.exists_mem_nhds_subset_loops_nullhomotopic`: the witnessing
  neighbourhood can be taken inside any prescribed neighbourhood.
* `SemilocallySimplyConnectedAt.exists_isOpen_mem_nhds_subset_loops_nullhomotopic`: the
  witnessing neighbourhood can moreover be taken open.
* `TauCeti.SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected`: a space
  in which every point has a simply connected neighbourhood is semilocally simply connected.
* `TauCeti.SemilocallySimplyConnectedSpace.of_locallyContractibleSpace`: a locally contractible
  space is semilocally simply connected.
* Instances deriving the property for simply connected spaces, strongly locally contractible
  spaces, discrete spaces, and binary products.

## References

This file supplies the semilocal-simple-connectivity hypothesis required by the Tau Ceti
universal-covers roadmap (`TauCetiRoadmap/UniversalCovers`); see the standing hypotheses there.
The predicate follows the one Kim Morrison introduces (as `SemilocallySimplyConnectedSpace`, the
classical based notion of Brazas, Definition 2.1, https://arxiv.org/abs/1102.0993) in mathlib4
PRs [#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292), which state the
universal-cover construction over `[SemilocallySimplyConnectedSpace X]`; neither has merged, so
the predicate is not yet in Mathlib. The API here is a streamlined single-field restatement
sufficient for the roadmap's Stage 0.2.
-/

public section

open Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is **semilocally simply connected at `x`** if `x` has a neighbourhood `U` such that
every loop in `U` based at `x` is null-homotopic in the whole space. The null-homotopy is allowed
to leave `U`, which is what makes this weaker than local simple connectivity. This is the based
notion of Brazas, Definition 2.1 (see the References below). -/
def _root_.SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x)

/-- The defining characterization of semilocal simple connectivity at a point. -/
theorem _root_.semilocallySimplyConnectedAt_def {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U ∈ 𝓝 x, ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  Iff.rfl

/-- A space is **semilocally simply connected** if it is semilocally simply connected at every
point: every point `x` has a neighbourhood `U` such that every loop in `U` based at `x` is
null-homotopic in the whole space. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point has a neighbourhood in which every based loop is null-homotopic in `X`. -/
  semilocallySimplyConnectedAt (x : X) : SemilocallySimplyConnectedAt x

/-- The witnessing neighbourhood of a point can be shrunk to lie inside any prescribed
neighbourhood: loops contained in a smaller set are in particular contained in the larger one. -/
theorem _root_.SemilocallySimplyConnectedAt.exists_mem_nhds_subset_loops_nullhomotopic {x : X}
    (h : SemilocallySimplyConnectedAt x) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U ∈ 𝓝 x, U ⊆ V ∧
      ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hloop⟩ := semilocallySimplyConnectedAt_def.mp h
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Set.inter_subset_right, fun γ hγ => ?_⟩
  exact hloop γ (hγ.trans Set.inter_subset_left)

/-- The witnessing neighbourhood can be taken open and inside any prescribed neighbourhood. This
is the form consumed by the universal-cover construction, where the sheets must be open. -/
theorem _root_.SemilocallySimplyConnectedAt.exists_isOpen_mem_nhds_subset_loops_nullhomotopic
    {x : X} (h : SemilocallySimplyConnectedAt x) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hUV, hloop⟩ := h.exists_mem_nhds_subset_loops_nullhomotopic hV
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  exact ⟨W, hWopen, hxW, hWU.trans hUV, fun γ hγ => hloop γ (hγ.trans hWU)⟩

/-- If every point of `X` has a simply connected neighbourhood, then `X` is semilocally simply
connected: a loop inside such a neighbourhood is already null-homotopic there, hence in `X`. -/
theorem SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, IsSimplyConnected U) : SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := by
    obtain ⟨U, hU, hsc⟩ := h x
    refine semilocallySimplyConnectedAt_def.mpr ⟨U, hU, fun γ hγ => ?_⟩
    obtain ⟨F, -⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 x γ
      (Set.range_subset_iff.mp hγ)
    exact ⟨F⟩

/-- A locally contractible space (each neighbourhood of a point contains a smaller neighbourhood
whose inclusion into the larger one is null-homotopic) is semilocally simply connected. A based
loop in the smaller neighbourhood becomes null-homotopic once pushed forward along the
null-homotopic inclusion into `X`. -/
theorem SemilocallySimplyConnectedSpace.of_locallyContractibleSpace
    (h : LocallyContractibleSpace X) : SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := by
    obtain ⟨V, hVU, hV, hnull⟩ := h x Set.univ Filter.univ_mem
    -- The inclusion `↥V → X` (factoring through `↥univ`) is null-homotopic.
    let j : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hnj : j.Nullhomotopic :=
      hnull.comp_right (⟨Subtype.val, continuous_subtype_val⟩ : C((Set.univ : Set X), X))
    refine semilocallySimplyConnectedAt_def.mpr ⟨V, hV, fun γ hγ => ?_⟩
    exact Path.Homotopic.refl_of_forall_mem_of_nullhomotopic hnj γ (Set.range_subset_iff.mp hγ)

/-- A simply connected space is semilocally simply connected: the whole space already witnesses
the condition, since every loop is null-homotopic. -/
instance (priority := 100) [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x :=
    semilocallySimplyConnectedAt_def.mpr
      ⟨Set.univ, Filter.univ_mem,
        fun γ _ => (simply_connected_iff_loops_nullhomotopic.mp ‹_›).2 x γ⟩

/-- A strongly locally contractible space (each point has a basis of contractible neighbourhoods)
is semilocally simply connected, since strong local contractibility implies the classical local
contractibility hypothesis. -/
instance (priority := 100) [StronglyLocallyContractibleSpace X] :
    SemilocallySimplyConnectedSpace X :=
  .of_locallyContractibleSpace StronglyLocallyContractibleSpace.locallyContractible

/-- A discrete space is semilocally simply connected: the singleton neighbourhood of a point
contains only the constant loop. -/
instance (priority := 100) [DiscreteTopology X] : SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := by
    refine semilocallySimplyConnectedAt_def.mpr
      ⟨{x}, (isOpen_discrete _).mem_nhds rfl, fun γ hγ => ?_⟩
    have hγx : γ = Path.refl x := by
      ext t
      simpa using hγ ⟨t, rfl⟩
    rw [hγx]

/-- A product of semilocally simply connected spaces is semilocally simply connected: a loop in a
product of witnessing neighbourhoods projects to loops in each factor, and their null-homotopies
combine into a null-homotopy of the original loop. -/
instance [SemilocallySimplyConnectedSpace X] [SemilocallySimplyConnectedSpace Y] :
    SemilocallySimplyConnectedSpace (X × Y) where
  semilocallySimplyConnectedAt := by
    rintro ⟨x, y⟩
    obtain ⟨U, hU, hUloop⟩ :=
      semilocallySimplyConnectedAt_def.mp
        (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (X := X) x)
    obtain ⟨V, hV, hVloop⟩ :=
      semilocallySimplyConnectedAt_def.mp
        (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (X := Y) y)
    refine semilocallySimplyConnectedAt_def.mpr
      ⟨U ×ˢ V, prod_mem_nhds hU hV, fun γ hγ => ?_⟩
    obtain ⟨F₁⟩ := hUloop (γ.map continuous_fst)
      (Set.range_subset_iff.mpr fun t => (Set.mem_prod.mp (hγ ⟨t, rfl⟩)).1)
    obtain ⟨F₂⟩ := hVloop (γ.map continuous_snd)
      (Set.range_subset_iff.mpr fun t => (Set.mem_prod.mp (hγ ⟨t, rfl⟩)).2)
    have key : ((γ.map continuous_fst).prod (γ.map continuous_snd)).Homotopic
        ((Path.refl x).prod (Path.refl y)) := ⟨Path.Homotopic.prodHomotopy F₁ F₂⟩
    have hleft : (γ.map continuous_fst).prod (γ.map continuous_snd) = γ := by
      ext t <;> simp
    have hright : (Path.refl x).prod (Path.refl y) = Path.refl (x, y) := by
      ext t <;> simp
    rwa [hleft, hright] at key

end TauCeti
