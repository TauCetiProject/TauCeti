/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.FirstOrder
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The isometry group of a round sphere

The restriction of ambient linear isometries to a positive-dimensional round sphere is onto its
Riemannian isometry group. Together with `LinearIsometryEquiv.unitSphereIsomHom_injective`, this
identifies the round sphere's isometry group with its ambient orthogonal group.
-/

public section

open Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- Every Riemannian isometry of a positive-dimensional round sphere is induced by an ambient
linear isometry. -/
theorem unitSphereIsomHom_surjective (hn : n ≠ 0) :
    Function.Surjective (unitSphereIsomHom (E := E) (n := n)) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    have hfin : finrank ℝ E = n + 1 := (inferInstance : Fact (finrank ℝ E = n + 1)).out
    rw [hfin]
    omega)
  let _ : ConnectedSpace (sphere (0 : E) 1) :=
    isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
      have hfin : finrank ℝ E = n + 1 := (inferInstance : Fact (finrank ℝ E = n + 1)).out
      rw [← Module.finrank_eq_rank, hfin]
      have hn' : 1 < n + 1 := by omega
      exact_mod_cast hn') 0 zero_le_one
  intro Φ
  let _ : Nonempty (sphere (0 : E) 1) :=
    ((NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1)).mpr zero_le_one).to_subtype
  let x : sphere (0 : E) 1 := Classical.choice inferInstance
  obtain ⟨e, he, hde⟩ :=
    TauCeti.RiemannianIsometry.exists_linearIsometryEquiv_apply_eq_and_mfderiv_eq Φ x
  refine ⟨e, TauCeti.RiemannianIsometry.ext_of_mfderiv_eq (p := x) (unitSphereIsomHom e) Φ ?_ ?_⟩
  · simpa only [unitSphereIsomHom_apply, coe_unitSphereRiemannianIsometry] using he
  · rw [unitSphereIsomHom_apply]
    rw [show ⇑(unitSphereRiemannianIsometry e) = unitSphereEquiv e from
      coe_unitSphereRiemannianIsometry e]
    exact hde

/-- The restriction homomorphism from ambient linear isometries to a positive-dimensional round
sphere is bijective. -/
theorem unitSphereIsomHom_bijective (hn : n ≠ 0) :
    Function.Bijective (unitSphereIsomHom (E := E) (n := n)) :=
  ⟨unitSphereIsomHom_injective, unitSphereIsomHom_surjective hn⟩

end LinearIsometryEquiv
