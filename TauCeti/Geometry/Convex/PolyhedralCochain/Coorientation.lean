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
using the cell's conormal form and Mathlib's
`mem_span_of_iInf_ker_le_ker`: scalar-valued linear maps with the same kernel
are proportional. No primitive normal, rational offset, boundedness or absence
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
theorem exists_integral_coorientation (σ : OrientedCell h 1) :
    ∃ m : N →+ ℤ, m ≠ 0 ∧
      (h.realCharacter m).ker = (affineSpan ℝ σ.carrier).direction ∧
      ∀ v : V, SignType.sign (h.realCharacter m v) =
        σ.orientation.evalSign (fun _ : Fin 1 => v) := by
  have := h.finiteDimensional
  -- Read the conormal one-form as a covector, whose kernel is the cell direction.
  let f : V →ₗ[ℝ] ℝ :=
    (AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1)).symm σ.orientation.someVector
  have hfapply (v : V) : f v = σ.orientation.someVector (fun _ : Fin 1 => v) := rfl
  have hf : f ≠ 0 := by
    intro hf
    apply σ.orientation.someVector_ne_zero
    ext v
    have he := congrArg (fun g : V →ₗ[ℝ] ℝ => g (v 0)) hf
    rw [hfapply] at he
    have hv : (fun _ : Fin 1 => v 0) = v := funext fun j => congrArg v (Fin.eq_zero j).symm
    simpa only [hv, LinearMap.zero_apply, zero_apply] using he
  have hle : (affineSpan ℝ σ.carrier).direction ≤ f.ker := by
    intro v hv
    exact (Submodule.mem_conormalForms.mp
      (Module.Ray.isConormal_iff.mp σ.isConormal)) (fun _ => v) 0 hv
  have hdir : (affineSpan ℝ σ.carrier).direction = f.ker :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have hdim := σ.finrank_direction_add
      have hfker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      omega)
  -- Rational-normality supplies an integral equation of the same hyperplane.
  obtain ⟨m, hm, hms⟩ := σ.rational.exists_direction_eq_ker
    σ.nonempty σ.finrank_direction_add
  have hmker := hms.symm
  have hspan : h.realCharacter m ∈ Submodule.span ℝ ({f} : Set (V →ₗ[ℝ] ℝ)) := by
    simpa using (mem_span_of_iInf_ker_le_ker
      (L := fun _ : Unit => f) (K := h.realCharacter m)
      (by simpa only [iInf_const] using (hdir.symm.trans hmker.symm).le))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hc0 : c ≠ 0 := by
    intro hc0
    have hz : h.realCharacter m = 0 := by simpa only [hc0, zero_smul] using hc.symm
    exact hm (h.realCharacter_injective (by simpa using hz))
  have hsign (v : V) : SignType.sign (f v) =
        σ.orientation.evalSign (fun _ : Fin 1 => v) := by
    simpa only [Module.Ray.someVector_ray, ← hfapply] using
      (Module.Ray.evalSign_rayOfNeZero σ.orientation.someVector_ne_zero
        (fun _ : Fin 1 => v)).symm
  -- Reverse the integral equation precisely when its scalar factor is negative.
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · refine ⟨-m, neg_ne_zero.mpr hm, ?_, fun v => ?_⟩
    · simpa only [map_neg, LinearMap.ker_neg] using hmker
    · have he : h.realCharacter (-m) v = (-c) * f v := by
        rw [map_neg, LinearMap.neg_apply, ← hc, LinearMap.smul_apply, smul_eq_mul, neg_mul]
      rw [he, sign_mul, sign_pos (neg_pos.mpr hcneg), one_mul, hsign]
  · refine ⟨m, hm, hmker, fun v => ?_⟩
    rw [← hc, LinearMap.smul_apply, smul_eq_mul, sign_mul, sign_pos hcpos, one_mul, hsign]

end TauCeti.OrientedCell
