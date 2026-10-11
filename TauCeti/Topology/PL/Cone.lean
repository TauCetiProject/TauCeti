/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Cone
public import TauCeti.Topology.PL.Compact
import Mathlib.Basic.Finite.Sum

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
  ((A.contLinear.comp (ContinuousLinearMap.fst ℝ _ _) +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (A 0)).prod
    (ContinuousLinearMap.snd ℝ E ℝ)).toContinuousAffineMap

private theorem coneAffinePiece_apply (A : E →ᴬ[ℝ] F) (p : E × ℝ) :
    coneAffinePiece A p = (A.contLinear p.1 + p.2 • A 0, p.2) := (rfl)

private theorem coneAffinePiece_ray (A : E →ᴬ[ℝ] F) (x : E) (t : ℝ) :
    coneAffinePiece A (t • x, t) = (t • A x, t) := by
  rw [coneAffinePiece_apply, map_smul, ← smul_add]
  congr 2
  exact (congrFun A.decomp x).symm

/-- A cell defined by homogenized base inequalities and nonnegative height. -/
private def coneCell {n : ℕ} (a : Fin n → E →ᴬ[ℝ] ℝ) :
    Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ ∀ j, (a j).contLinear p.1 + p.2 * a j 0 ≤ 0}

private theorem isConvexPolyhedron_coneCell {n : ℕ}
    (a : Fin n → E →ᴬ[ℝ] ℝ) : IsConvexPolyhedron (coneCell a) := by
  let height := (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  let inequalities : Unit ⊕ Fin n → (E × ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun _ => -height)
      (fun j => ((a j).contLinear.comp (ContinuousLinearMap.fst ℝ _ _) +
        (ContinuousLinearMap.snd ℝ E ℝ).smulRight (a j 0)).toContinuousAffineMap)
  convert isConvexPolyhedron_setOf_forall inequalities using 1
  ext p
  simp [coneCell, inequalities, height, Sum.forall]

private theorem coneCell_zero {n : ℕ} (a : Fin n → E →ᴬ[ℝ] ℝ) :
    (0 : E × ℝ) ∈ coneCell a := by simp [coneCell]

private theorem coneCell_ray {n : ℕ} {a : Fin n → E →ᴬ[ℝ] ℝ}
    {x : E} {t : ℝ} (ht : 0 ≤ t) (hx : ∀ j, a j x ≤ 0) :
    (t • x, t) ∈ coneCell a := by
  refine ⟨ht, fun j => ?_⟩
  have heq := congrArg Prod.fst (coneAffinePiece_ray (a j) x t)
  simp only [coneAffinePiece_apply, smul_eq_mul] at heq
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hx j)

private theorem coneCell_normalize {n : ℕ} {a : Fin n → E →ᴬ[ℝ] ℝ}
    {p : E × ℝ} (hp : p ∈ coneCell a) (ht : 0 < p.2) :
    ∀ j, a j (p.2⁻¹ • p.1) ≤ 0 := by
  intro j
  have heq := congrArg Prod.fst (coneAffinePiece_ray (a j) (p.2⁻¹ • p.1) p.2)
  simp only [smul_inv_smul₀ ht.ne'] at heq
  simp only [coneAffinePiece_apply, smul_eq_mul] at heq
  have hmul : p.2 * a j (p.2⁻¹ • p.1) ≤ 0 := heq ▸ hp.2 j
  nlinarith

/-- A finite piecewise-affine map extends piecewise affinely over the whole geometric cone,
including the apex. No boundedness, closedness or polyhedral assumption on the base is needed. -/
theorem IsPiecewiseAffineOn.coneMap (hf : IsPiecewiseAffineOn f s) :
    IsPiecewiseAffineOn (coneMap f) s.cone := by
  classical
  obtain ⟨n, C, A, hC, hcover, heq⟩ := isPiecewiseAffineOn_iff.mp hf
  -- Height-zero recession directions lie outside the cone, so cells need no coordinate bounds.
  choose m a ha using fun i => isConvexPolyhedron_iff.mp (hC i)
  -- Keep an apex cell even when the base decomposition has no pieces.
  let cells : Option (Fin n) → Set (E × ℝ) :=
    fun i => match i with
      | none => coneCell (fun _ : Fin 1 => ContinuousAffineMap.const ℝ E 1)
      | some i => coneCell (a i)
  let pieces : Option (Fin n) → (E × ℝ) →ᴬ[ℝ] (F × ℝ) :=
    fun i => match i with
      | none => ContinuousAffineMap.const ℝ _ 0
      | some i => coneAffinePiece (A i)
  refine isPiecewiseAffineOn_of_finite (C := cells) (A := pieces) ?_ ?_ ?_
  · rintro (_ | i) <;> exact isConvexPolyhedron_coneCell _
  · intro p hp
    rcases mem_cone.mp hp with rfl | ⟨ht, hx⟩
    · exact mem_iUnion.mpr ⟨none, coneCell_zero _⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      have hcell := coneCell_ray ht.le (by rwa [ha i] at hi)
      simp only [smul_inv_smul₀ ht.ne'] at hcell
      exact mem_iUnion.mpr ⟨some i, hcell⟩
  · rintro (_ | i) p ⟨hp, hc⟩
    · have ht : p.2 = 0 := le_antisymm
        (by simpa [cells] using hc.2 0) hc.1
      have hp0 : p = 0 := (mem_cone.mp hp).resolve_right (by simp [ht])
      rw [hp0, coneMap_zero]
      rfl
    · rcases mem_cone.mp hp with rfl | ⟨ht, hx⟩
      · simp [pieces, coneAffinePiece_apply]
        rfl
      · have hbase : p.2⁻¹ • p.1 ∈ C i := by
          rw [ha i]
          exact coneCell_normalize hc ht
        have hvalue := heq i ⟨hx, hbase⟩
        have hpiece := coneAffinePiece_ray (A i) (p.2⁻¹ • p.1) p.2
        simpa [smul_inv_smul₀ ht.ne', Prod.ext_iff, pieces, hvalue] using hpiece.symm

end PiecewiseAffine

variable {ι : Type*}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

/-- A PL map on a compact base extends to a PL map of geometric cones, including at the apex.
The target may be any real topological vector space. -/
theorem IsPLOn.coneMap (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPLOn (coneMap f) s.cone := by
  exact (hf.isPiecewiseAffineOn_of_isCompact hs).coneMap.isPLOn

end TauCeti
