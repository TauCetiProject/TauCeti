/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy

/-!
# Diffeomorphism invariance of smooth singular chain comparisons

A smooth diffeomorphism exhibits each manifold as a smooth homotopy retract of the other, with the
constant homotopy, so the quasi-isomorphism property of the smooth-to-singular chain map is
invariant under smooth diffeomorphisms
(`Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`). This is the special case
of `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy` in which the
homotopy is `Prod.snd`.

## Main results

* `Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`: a smooth diffeomorphism
  preserves and reflects whether the inclusion of smooth singular chains into singular chains is a
  quasi-isomorphism.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

universe u v w

namespace Diffeomorph

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] [CategoryWithHomology C]

/-- A smooth diffeomorphism preserves and reflects whether the inclusion of smooth singular chains
into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff (e : M ≃ₘ⟮I, J⟯ N) (R : C) :
    QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex J N).ι R) :=
  ⟨TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy R
      e.symm.contMDiff e.contMDiff contMDiff_snd (fun _ ↦ rfl)
      (fun y ↦ (e.apply_symm_apply y).symm),
    TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy R
      e.contMDiff e.symm.contMDiff contMDiff_snd (fun _ ↦ rfl)
      (fun x ↦ (e.symm_apply_apply x).symm)⟩

end Diffeomorph
