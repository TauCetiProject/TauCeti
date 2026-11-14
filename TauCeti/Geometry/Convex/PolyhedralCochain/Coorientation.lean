/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Direction

/-!
# Integral coorientations of oriented wall cells

An oriented rational-normal cell of codimension one admits a nonzero integral
normal with the prescribed positive side. The sign of its real extension on
every vector agrees with the conormal orientation on the corresponding
one-vector frame. Thus the normal records the orientation, rather than only
the tangent hyperplane.

Adapted from `Mei/Geometry/Convex/PolyhedralCochain/Coorientation.lean` at
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).

The integral equation comes from
`IsRationalNormalPolyhedron.exists_direction_eq_ker`. The sign is selected
using `Module.Ray.IsConormal.eq_or_eq_neg` and the cell's normal-quotient
dimension: its prescribed orientation is the ray of the integral one-form or
the reversed ray. No primitive normal, rational offset, boundedness or absence
of lineality is required.
-/

public section

noncomputable section

open Set Module

namespace TauCeti.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A codimension-one oriented cell has a nonzero integral normal cutting out
its direction and inducing precisely its prescribed conormal orientation. -/
theorem exists_ker_realCharacter_eq_direction_and_sign_eq_evalSign (σ : OrientedCell h 1) :
    ∃ m : N →+ ℤ, m ≠ 0 ∧
      (h.realCharacter m).ker = (affineSpan ℝ σ.carrier).direction ∧
      ∀ v : V, SignType.sign (h.realCharacter m v) =
        σ.orientation.evalSign (fun _ : Fin 1 => v) := by
  have := h.finiteDimensional
  obtain ⟨m, hm, hms⟩ := σ.rational.exists_direction_eq_ker
    σ.nonempty σ.finrank_direction_add
  let α := AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (h.realCharacter m)
  have hα : α ≠ 0 := by
    intro he
    have hzero : AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1) (0 : V →ₗ[ℝ] ℝ) = 0 := by
      ext w
      simp
    have hz : h.realCharacter m = 0 :=
      (AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1)).injective (he.trans hzero.symm)
    exact hm (h.realCharacter_injective (by simpa using hz))
  have hcon : (rayOfNeZero ℝ α hα).IsConormal (affineSpan ℝ σ.carrier).direction := by
    rw [Module.Ray.isConormal_rayOfNeZero_iff, Submodule.mem_conormalForms]
    intro w j hw
    rw [hms, LinearMap.mem_ker] at hw
    simpa [α, Fin.eq_zero j] using hw
  rcases σ.isConormal.eq_or_eq_neg hcon
    (by simpa using σ.finrank_quotient_direction) with ho | ho
  · refine ⟨m, hm, hms.symm, fun v => ?_⟩
    rw [ho, Module.Ray.evalSign_rayOfNeZero]
    simp [α]
  · refine ⟨-m, neg_ne_zero.mpr hm, ?_, fun v => ?_⟩
    · simpa only [map_neg, LinearMap.ker_neg] using hms.symm
    · rw [ho, Module.Ray.evalSign_neg, Module.Ray.evalSign_rayOfNeZero]
      simp [α, Left.sign_neg]

end TauCeti.OrientedCell
