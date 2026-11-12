/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Geometry.Manifold.LocallyContractible
public import TauCeti.Topology.Circle.Punctured
public import TauCeti.Topology.WedgeSum
import TauCeti.Topology.Homotopy.Path

/-!
# Wedge sums of semilocally simply connected spaces

Let `(X i, x i)` be pointed spaces whose base points are closed and have open neighbourhoods
`V i` which deformation retract onto them. If every `X i` is semilocally simply connected, so is
the wedge sum `⋁ᵢ X i` (`TauCeti.WedgeSum.semilocallySimplyConnectedSpace`).

* At the wedge point, the wedge sum of the `V i` is an open neighbourhood, and it is contractible
  (`TauCeti.WedgeSum.contractibleSpace`), so every loop in it is null-homotopic.
* At a point `y ≠ x i` of the `i`-th summand, a witnessing neighbourhood `U` of `y` in `X i` can
  be chosen to avoid `x i`. Its preimage under the retraction `TauCeti.WedgeSum.proj x i` onto the
  `i`-th summand is an open neighbourhood of `y` in the wedge sum on which the retraction is
  inverse to the inclusion of the summand, so a loop in it is the image of a loop in `U`.

In particular a wedge of circles, with any number of circles, is semilocally simply connected
(`TauCeti.WedgeSum.instSemilocallySimplyConnectedSpaceCircle`), so it has a universal cover.

## Main results

* `TauCeti.WedgeSum.semilocallySimplyConnectedSpace`: a wedge sum of semilocally simply connected
  spaces, with closed base points that have contractible neighbourhoods as above, is semilocally
  simply connected.
* `TauCeti.WedgeSum.instSemilocallySimplyConnectedSpaceCircle`: a wedge of circles is semilocally
  simply connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, the discussion of semilocal simple connectivity before Proposition 1.36.
-/

public section

open Set Topology

universe u v

namespace TauCeti

namespace WedgeSum

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)] {x : ∀ i, X i}

/-- The wedge sum is semilocally simply connected at a point `y ≠ x i` of the `i`-th summand at
which `X i` is, provided the base point `x i` is closed: a witnessing neighbourhood of `y` avoiding
`x i` pulls back along the retraction onto `X i` to one in the wedge sum. -/
theorem semilocallySimplyConnectedAt_incl {i : ι} (hx : IsClosed ({x i} : Set (X i)))
    {y : X i} (hy : y ≠ x i) (h : SemilocallySimplyConnectedAt y) :
    SemilocallySimplyConnectedAt (incl x i y) := by
  obtain ⟨U, hUo, hyU, hUx, hU⟩ :=
    h.exists_isOpen_mem_nhds_subset_loops_nullhomotopic (hx.isOpen_compl.mem_nhds hy)
  have hxy : proj x i (incl x i y) = y := proj_incl_self i y
  refine semilocallySimplyConnectedAt_def.2
    ⟨proj x i ⁻¹' U, ((hUo.preimage (proj x i).continuous).mem_nhds (by rwa [mem_preimage, hxy])),
      fun γ hγ ↦ ?_⟩
  -- The loop `γ` is the image under `incl x i` of its retraction `γ'` onto `X i`, a loop in `U`.
  let γ' : Path y y := (γ.map (proj x i).continuous).cast hxy.symm hxy.symm
  have hγ' : γ'.map (incl x i).continuous = γ := by
    ext t
    exact incl_proj_of_proj_ne (hUx (hγ ⟨t, rfl⟩))
  rw [← hγ']
  exact (hU γ' (by rintro _ ⟨t, rfl⟩; exact hγ ⟨t, rfl⟩)).map (incl x i)

/-- **A wedge sum of semilocally simply connected spaces is semilocally simply connected**,
provided every base point `x i` is closed and has an open neighbourhood `V` which deformation
retracts onto `x i`. The wedge sum of these neighbourhoods is a contractible open neighbourhood of
the wedge point. -/
theorem semilocallySimplyConnectedSpace [∀ i, SemilocallySimplyConnectedSpace (X i)]
    (hx : ∀ i, IsClosed ({x i} : Set (X i)))
    (hV : ∀ i, ∃ V : Set (X i), IsOpen V ∧ ∃ hx : x i ∈ V,
      Nonempty ((ContinuousMap.id V).HomotopyRel (.const V ⟨x i, hx⟩) {⟨x i, hx⟩})) :
    SemilocallySimplyConnectedSpace (WedgeSum x) where
  semilocallySimplyConnectedAt w := by
    have hbase : SemilocallySimplyConnectedAt (base x) := by
      choose V hVo hxV hH using hV
      have := contractibleSpace hH
      have he := isOpenEmbedding_subtypeVal hxV hVo
      -- The inclusion of the open set `range (subtypeVal hxV)` factors through the contractible
      -- wedge sum of the `V i`, so it is null-homotopic.
      have hnull : (ContinuousMap.mk (Subtype.val : range (subtypeVal hxV) → WedgeSum x)
          continuous_subtype_val).Nullhomotopic := by
        convert ((id_nullhomotopic _).comp_right (subtypeVal hxV)).comp_left
          ⟨he.isEmbedding.toHomeomorph.symm, he.isEmbedding.toHomeomorph.symm.continuous⟩
        ext w
        exact congrArg Subtype.val (he.isEmbedding.toHomeomorph.apply_symm_apply w).symm
      exact semilocallySimplyConnectedAt_def.2 ⟨_, he.isOpen_range.mem_nhds
        (base_mem_range_subtypeVal hxV), fun γ hγ ↦
          Path.Homotopic.refl_of_forall_mem_of_nullhomotopic hnull γ fun t ↦ hγ ⟨t, rfl⟩⟩
    induction w using ind with
    | base => exact hbase
    | incl i y =>
      by_cases hy : y = x i
      · rwa [hy, incl_apply_self]
      · exact semilocallySimplyConnectedAt_incl (hx i) hy
          (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt y)

/-- **A wedge of circles is semilocally simply connected**, for any number of circles: the circle
is a manifold, and `Circle ∖ {-1}` deformation retracts onto `1` (`TauCeti.circleChordHomotopy`). -/
instance instSemilocallySimplyConnectedSpaceCircle :
    SemilocallySimplyConnectedSpace (WedgeSum fun _ : ι ↦ (1 : Circle)) :=
  semilocallySimplyConnectedSpace (fun _ ↦ isClosed_singleton) fun _ ↦
    ⟨{z : Circle | z ≠ -1}, isOpen_ne, (Circle.neg_ne_self 1).symm, ⟨circleChordHomotopy⟩⟩

end WedgeSum

end TauCeti
