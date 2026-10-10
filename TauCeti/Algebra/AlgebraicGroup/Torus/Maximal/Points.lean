/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Maximal tori from geometric points

A torus is maximal if its points over an algebraically closed extension are self-centralizing
in the ambient point group. Every competing torus is reduced and commutative, so the general
closed-subgroup criterion applies.

## Main declarations

* `TauCeti.HopfIdeal.isMaximalTorus_of_centralizer_quotientPointsSubgroup`: a sufficient
  geometric-point criterion for maximality of a torus.

This packages pointwise centralizer computations for Layer 7, "Borel subgroups, maximal tori",
of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v

/-- A torus with self-centralizing points over an algebraically closed extension is maximal.
The ambient group may be any affine group of finite type. -/
theorem isMaximalTorus_of_centralizer_quotientPointsSubgroup
    {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {I : HopfIdeal k H}
    (hI : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I))
    (hpoints : Subgroup.centralizer
        (CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K) : Set _) =
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K)) :
    IsMaximalTorus k H I := by
  rw [isMaximalTorus_iff]
  refine ⟨hI, fun J hJ hJI ↦ ?_⟩
  let _ : IsReduced (CommHopfAlgCat.quotient H J) := hJ.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient H J) := hJ.isCocomm k _
  exact (eq_of_le_of_centralizer_quotientPointsSubgroup hJI hpoints).ge

end TauCeti.HopfIdeal
