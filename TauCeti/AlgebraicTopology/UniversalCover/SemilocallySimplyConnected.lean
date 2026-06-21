/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.Homotopy.Product

/-!
# Semilocally simply connected spaces

A topological space `X` is *semilocally simply connected* if every point `x` has a
neighbourhood `U` such that every loop in `U` based at `x` is null-homotopic *in `X`*. This is
the standing point-set hypothesis (alongside path-connectedness and local path-connectedness)
under which the universal cover of a space exists; see the universal-covers roadmap. Mathlib has
`SimplyConnectedSpace` and the local notions `LocallyContractibleSpace` and
`StronglyLocallyContractibleSpace`, but no semilocal simple connectivity, so we introduce it
here.

The condition is genuinely *semi*local: the null-homotopy is allowed to leave `U` and use the
whole of `X`. It is therefore weaker than asking each `U` to be simply connected on its own (the
local notion); the constructor `SemilocallySimplyConnectedSpace.of_forall_isSimplyConnected_nhds`
records that implication, and through it every strongly locally contractible space is semilocally
simply connected. Discrete spaces are also instances, witnessed by singleton neighbourhoods.

## Main declarations

* `TauCeti.SemilocallySimplyConnectedSpace`: the predicate, as a typeclass.
* `TauCeti.SemilocallySimplyConnectedSpace.exists_nhds_subset_loops_nullhomotopic`: the
  witnessing neighbourhood can be taken inside any prescribed neighbourhood.
* `TauCeti.SemilocallySimplyConnectedSpace.of_forall_isSimplyConnected_nhds`: a space in which
  every point has a simply connected neighbourhood is semilocally simply connected.
* Instances deriving the property for simply connected spaces, strongly locally contractible
  spaces, discrete spaces, and binary products.

## References

This file supplies the semilocal-simple-connectivity hypothesis required by the Tau Ceti
universal-covers roadmap (`TauCetiRoadmap/UniversalCovers`); see the standing hypotheses there.
-/

open Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is **semilocally simply connected** if every point `x` has a neighbourhood `U` such
that every loop in `U` based at `x` is null-homotopic in the whole space. The null-homotopy is
allowed to leave `U`, which is what makes this weaker than local simple connectivity. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point has a neighbourhood in which every based loop is null-homotopic in `X`. -/
  exists_nhds_loops_nullhomotopic (x : X) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x)

namespace SemilocallySimplyConnectedSpace

variable [SemilocallySimplyConnectedSpace X]

/-- The witnessing neighbourhood of a point can be shrunk to lie inside any prescribed
neighbourhood: loops contained in a smaller set are in particular contained in the larger one. -/
theorem exists_nhds_subset_loops_nullhomotopic (x : X) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U ∈ 𝓝 x, U ⊆ V ∧ ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hloop⟩ := exists_nhds_loops_nullhomotopic (X := X) x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Set.inter_subset_right, fun γ hγ => ?_⟩
  exact hloop γ fun t => (hγ t).1

end SemilocallySimplyConnectedSpace

/-- If every point of `X` has a simply connected neighbourhood, then `X` is semilocally simply
connected: a loop inside such a neighbourhood is already null-homotopic there, hence in `X`. -/
theorem SemilocallySimplyConnectedSpace.of_forall_isSimplyConnected_nhds
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, IsSimplyConnected U) : SemilocallySimplyConnectedSpace X where
  exists_nhds_loops_nullhomotopic x := by
    obtain ⟨U, hU, hsc⟩ := h x
    refine ⟨U, hU, fun γ hγ => ?_⟩
    obtain ⟨F, -⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 x γ hγ
    exact ⟨F⟩

/-- A simply connected space is semilocally simply connected: the whole space already witnesses
the condition, since every loop is null-homotopic. -/
instance (priority := 100) [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X where
  exists_nhds_loops_nullhomotopic x :=
    ⟨Set.univ, Filter.univ_mem,
      fun γ _ => (simply_connected_iff_loops_nullhomotopic.mp ‹_›).2 x γ⟩

/-- A strongly locally contractible space (each point has a basis of contractible neighbourhoods)
is semilocally simply connected, since a contractible subspace is simply connected. -/
instance (priority := 100) [StronglyLocallyContractibleSpace X] :
    SemilocallySimplyConnectedSpace X := by
  apply SemilocallySimplyConnectedSpace.of_forall_isSimplyConnected_nhds
  intro x
  obtain ⟨U, ⟨hU, hcon⟩, -⟩ := (contractible_basis x).mem_iff.mp Filter.univ_mem
  exact ⟨U, hU, (inferInstance : SimplyConnectedSpace U)⟩

/-- A discrete space is semilocally simply connected: the singleton neighbourhood of a point
contains only the constant loop. -/
instance (priority := 100) [DiscreteTopology X] : SemilocallySimplyConnectedSpace X where
  exists_nhds_loops_nullhomotopic x := by
    refine ⟨{x}, (isOpen_discrete _).mem_nhds rfl, fun γ hγ => ?_⟩
    have hγx : γ = Path.refl x := by
      ext t
      simpa using hγ t
    rw [hγx]

/-- A product of semilocally simply connected spaces is semilocally simply connected: a loop in a
product of witnessing neighbourhoods projects to loops in each factor, and their null-homotopies
combine into a null-homotopy of the original loop. -/
instance [SemilocallySimplyConnectedSpace X] [SemilocallySimplyConnectedSpace Y] :
    SemilocallySimplyConnectedSpace (X × Y) where
  exists_nhds_loops_nullhomotopic := by
    rintro ⟨x, y⟩
    obtain ⟨U, hU, hUloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_nhds_loops_nullhomotopic (X := X) x
    obtain ⟨V, hV, hVloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_nhds_loops_nullhomotopic (X := Y) y
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, fun γ hγ => ?_⟩
    obtain ⟨F₁⟩ := hUloop (γ.map continuous_fst) fun t => (Set.mem_prod.mp (hγ t)).1
    obtain ⟨F₂⟩ := hVloop (γ.map continuous_snd) fun t => (Set.mem_prod.mp (hγ t)).2
    have key : ((γ.map continuous_fst).prod (γ.map continuous_snd)).Homotopic
        ((Path.refl x).prod (Path.refl y)) := ⟨Path.Homotopic.prodHomotopy F₁ F₂⟩
    have hleft : (γ.map continuous_fst).prod (γ.map continuous_snd) = γ := by
      ext t <;> simp
    have hright : (Path.refl x).prod (Path.refl y) = Path.refl (x, y) := by
      ext t <;> simp
    rwa [hleft, hright] at key

end TauCeti
