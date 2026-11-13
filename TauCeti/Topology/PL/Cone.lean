/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Cone
public import TauCeti.Topology.PL.Compact
import TauCeti.Analysis.Convex.Polyhedron.Homogenization

/-!
# Coning piecewise-affine maps

The geometric cone on `s ⊆ E` is the apex together with the rays `(t • x, t)`,
where `x ∈ s` and `t > 0`. A map of bases extends by preserving the height and
scaling its value by that height. A finite piecewise-affine decomposition on any
subset of a real topological vector space extends to a finite piecewise-linear
one on the entire cone, including the apex. In particular, a PL map on a compact
base extends to a PL map on its cone.

This supplies the PL regularity needed when extending maps of links to maps of
vertex stars. The PL extension assumes a compact base in a real coordinate product.
The affine map `coneToJoin b` reads a cone point as a point of the join of the base with a
point `b`, placing the apex at `b`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapter 1, “Joins and Cones”, pp. 1–2,
  Example 1.5(4), p. 5, and Chapter 2, “Pseudo-Radial Projection”, pp. 20–21.
-/

public section

noncomputable section

open Set

namespace TauCeti

section PiecewiseAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {s : Set E} {f : E → F}

-- Use Mathlib's continuous-affine decomposition and continuous-linear product combinators.
/-- The homogeneous affine piece associated to a base piece. It includes the height coordinate
so that it has the same codomain as `coneMap`. -/
private def coneAffinePiece (A : E →ᴬ[ℝ] F) :
    (E × ℝ) →ᴬ[ℝ] (F × ℝ) :=
  (A.homogenize.prod (ContinuousLinearMap.snd ℝ E ℝ)).toContinuousAffineMap

/-- A finite piecewise-affine map extends piecewise affinely over the whole geometric cone,
including the apex. No boundedness, closedness or polyhedral assumption on the base is needed. -/
theorem IsPiecewiseAffineOn.coneMap (hf : IsPiecewiseAffineOn f s) :
    IsPiecewiseAffineOn (coneMap ℝ f) (s.cone ℝ) := by
  classical
  obtain ⟨n, C, A, hC, hcover, heq⟩ := isPiecewiseAffineOn_iff.mp hf
  -- Height-zero recession directions lie outside the cone, so cells need no coordinate bounds.
  choose m a ha using fun i => isConvexPolyhedron_iff.mp (hC i)
  -- Keep an apex cell even when the base decomposition has no pieces.
  let cells : Option (Fin n) → Set (E × ℝ) :=
    fun i => match i with
      | none =>
        (homogeneousInequalityCone (fun _ : Fin 1 => ContinuousAffineMap.const ℝ E 1) : Set (E × ℝ))
      | some i => (homogeneousInequalityCone (a i) : Set (E × ℝ))
  let pieces : Option (Fin n) → (E × ℝ) →ᴬ[ℝ] (F × ℝ) :=
    fun i => match i with
      | none => ContinuousAffineMap.const ℝ _ 0
      | some i => coneAffinePiece (A i)
  refine isPiecewiseAffineOn_of_finite (C := cells) (A := pieces) ?_ ?_ ?_
  · rintro (_ | i) <;> exact isConvexPolyhedron_homogeneousInequalityCone _
  · intro p hp
    rcases mem_cone.mp hp with rfl | ⟨ht, hx⟩
    · exact mem_iUnion.mpr ⟨none, (homogeneousInequalityCone _).zero_mem⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      have hbase : (p.2⁻¹ • p.1, (1 : ℝ)) ∈ homogeneousInequalityCone (a i) := by
        simpa [ha i] using hi
      have hcell := (homogeneousInequalityCone (a i)).smul_mem ht.le hbase
      simp only [Prod.smul_mk, smul_inv_smul₀ ht.ne', smul_eq_mul, mul_one] at hcell
      exact mem_iUnion.mpr ⟨some i, hcell⟩
  · rintro (_ | i) p ⟨hp, hc⟩
    · have hc' := mem_homogeneousInequalityCone.mp hc
      have ht : p.2 = 0 := le_antisymm
        (by simpa [ContinuousAffineMap.homogenize_apply, smul_eq_mul] using hc'.2 0) hc'.1
      have hp0 : p = 0 := (mem_cone.mp hp).resolve_right (by simp [ht])
      rw [hp0, coneMap_zero]
      rfl
    · rcases mem_cone.mp hp with rfl | ⟨ht, hx⟩
      · simp [pieces, coneAffinePiece]
      · have hbase : p.2⁻¹ • p.1 ∈ C i := by
          rw [ha i]
          intro j
          have hrow := (mem_homogeneousInequalityCone.mp hc).2 j
          rw [(a i j).homogenize_apply_of_ne_zero p.1 ht.ne'] at hrow
          exact nonpos_of_mul_nonpos_right (by simpa using hrow) ht
        ext
        · simp only [coneMap_fst, pieces, coneAffinePiece,
            ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.prod_apply,
            heq i ⟨hx, hbase⟩]
          exact ((A i).homogenize_apply_of_ne_zero p.1 ht.ne').symm
        · simp [pieces, coneAffinePiece]

end PiecewiseAffine

variable {ι : Type*}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

/-- The affine map `(p, t) ↦ p - t • b + b` from cone coordinates to the join with `b`. It sends
the apex to `b` and the ray point `(t • x, t)` to `t • x + (1 - t) • b`, so the cone point at
height `t` over `x` goes to the point at parameter `1 - t` on the segment from `x` to `b`. -/
def coneToJoin (b : F) : (F × ℝ) →ᴬ[ℝ] F :=
  (ContinuousLinearMap.fst ℝ F ℝ -
      (ContinuousLinearMap.snd ℝ F ℝ).smulRight b).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (F × ℝ) b

@[simp]
theorem coneToJoin_apply (b : F) (p : F × ℝ) : coneToJoin b p = p.1 - p.2 • b + b := (rfl)

/-- A PL map on a compact base extends to a PL map of geometric cones, including at the apex.
The target may be any real topological vector space. -/
theorem IsPLOn.coneMap (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPLOn (coneMap ℝ f) (s.cone ℝ) := by
  exact (hf.isPiecewiseAffineOn_of_isCompact hs).coneMap.isPLOn

end TauCeti
