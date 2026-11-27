/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product.ClosedImmersion
import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Empty and rank-one root-product charts

Check the empty parameter scheme and the positive and negative one-root charts on the
simply connected datum of type A₁. These are closed immersions over `ℤ`, so the checks
include arbitrary scalar extension.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Examples.Chevalley

/-- The native simply connected Chevalley datum of type A₁. -/
noncomputable def a1Datum : DynkinType.ChevalleyDatum (.A 1) (by decide) :=
  (DynkinType.A 1).scChevalleyDatum (by decide)

/-- The unique simple-root number in type A₁. -/
def a1Simple : Fin (DynkinType.A 1).rank :=
  ⟨0, by rw [DynkinType.rank_A]; decide⟩

/-- The empty A₁ root product is the closed unit section. -/
theorem isClosedImmersion_a1_rootProduct_nil : IsClosedImmersion (a1Datum.rootProduct []).left :=
  a1Datum.isClosedImmersion_rootProduct List.nodup_nil (fun _ h ↦ (List.not_mem_nil h).elim)

/-- The positive one-root A₁ product is a closed affine-line chart. -/
theorem isClosedImmersion_a1_rootProduct_positive : IsClosedImmersion
    (a1Datum.rootProduct [(DynkinType.A 1).simpleIndex (by decide) a1Simple]).left := by
  apply a1Datum.isClosedImmersion_rootProduct (List.nodup_singleton _)
  intro γ hγ
  simp only [List.mem_singleton] at hγ
  subst γ
  exact DynkinType.simpleIndex_mem_posRoots a1Simple

/-- The negative one-root A₁ product is a closed affine-line chart. -/
theorem isClosedImmersion_a1_rootProduct_negative : IsClosedImmersion
    (a1Datum.rootProduct [((DynkinType.A 1).simplyConnectedRootDatum (by decide)).reflectionPerm
      ((DynkinType.A 1).simpleIndex (by decide) a1Simple)
      ((DynkinType.A 1).simpleIndex (by decide) a1Simple)]).left := by
  apply a1Datum.isClosedImmersion_rootProduct_of_negRoots (List.nodup_singleton _)
  intro γ hγ
  simp only [List.mem_singleton] at hγ
  subst γ
  rw [← DynkinType.reflectionPerm_rationalRootSystem]
  exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr
    (DynkinType.simpleIndex_mem_posRoots a1Simple)

end TauCeti.Examples.Chevalley
