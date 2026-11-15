/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Alternating.Conormal
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Conormal forms on transverse simplices

The edge frame of a nondegenerate simplex evaluates nontrivially under a nonzero
conormal form when its direction complements the tangent subspace. In dimension
two this allows a transverse triangular boundary to be ordered positively for a
prescribed conormal orientation.

The proof uses Mathlib's basis of a linearly independent span and
`Submodule.quotientEquivOfIsCompl`, together with
`Submodule.conormalFormsEquiv` to descend the form to the normal quotient.

Adapted from `Mei/Geometry/Affine/Simplex/Conormal.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Set Module

namespace Affine.Simplex

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddTorsor V P] {n : ℕ}

/-- A nonzero conormal form evaluates nontrivially on the edge frame of a
simplex whose direction complements the tangent subspace. -/
theorem conormal_apply_ne_zero (s : Simplex R P n) {W : Submodule R V}
    (hW : IsCompl W (vectorSpan R (range s.points)))
    {α : V [⋀^Fin n]→ₗ[R] R} (hα : α ∈ W.conormalForms (Fin n)) (hα0 : α ≠ 0) :
    α (fun j : Fin n => s.points j.succ -ᵥ s.points 0) ≠ 0 := by
  classical
  let v : Fin n → V := fun j => s.points j.succ -ᵥ s.points 0
  have hi : LinearIndependent R v := by
    simpa only [v, Function.comp_def, finSuccAboveEquiv_apply,
      Fin.succAbove_zero] using
      ((affineIndependent_iff_linearIndependent_vsub R s.points 0).mp s.independent).comp
        (finSuccAboveEquiv 0) (finSuccAboveEquiv 0).injective
  have hspan : Submodule.span R (range v) = vectorSpan R (range s.points) := by
    rw [vectorSpan_range_eq_span_range_vsub_right_ne R s.points 0]
    congr 1
    simpa only [v, Function.comp_def, finSuccAboveEquiv_apply,
      Fin.succAbove_zero] using
      (finSuccAboveEquiv 0).surjective.range_comp
        (fun j : {j : Fin (n + 1) // j ≠ 0} => s.points j -ᵥ s.points 0)
  let T := Submodule.span R (range v)
  have hWT : IsCompl W T := by simpa only [T, hspan] using hW
  let e := W.quotientEquivOfIsCompl T hWT
  let b := (Basis.span hi).map e.symm
  let β := W.conormalFormsEquiv.symm ⟨α, hα⟩
  have hβ : β ≠ 0 := by
    intro hz
    have hz' : W.conormalFormsEquiv.symm ⟨α, hα⟩ = 0 := hz
    exact hα0 (congrArg Subtype.val (W.conormalFormsEquiv.symm.map_eq_zero_iff.mp hz'))
  have hb := (β.map_basis_ne_zero_iff b).mpr hβ
  have he (j : Fin n) : b j = W.mkQ (v j) := by
    simp only [b, Basis.map_apply, Basis.span_apply, e,
      ← LinearEquiv.coe_coe,
      Submodule.toLinearMap_symm_quotientEquivOfIsCompl,
      LinearMap.comp_apply, Submodule.subtype_apply]
  have hefun : (b : Fin n → V ⧸ W) = fun j => Submodule.Quotient.mk (v j) := by
    funext j
    exact he j
  rw [hefun] at hb
  simpa only [β, Submodule.conormalFormsEquiv_symm_apply_mk] using hb

end Affine.Simplex
