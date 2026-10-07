/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Cone
public import TauCeti.Topology.PL.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Basic.Finite.Sum

/-!
# Coning piecewise-affine maps

The geometric cone on `s ⊆ E` is the apex together with the rays `(t • x, t)`,
where `x ∈ s` and `t > 0`. A map of bases extends by preserving the height and
scaling its value by that height. On bounded subsets of finite coordinate spaces,
a finite piecewise-affine decomposition extends to a finite piecewise-linear
one on the entire cone, including the apex. In particular, a PL map on a compact
base extends to a PL map on its cone.

This supplies the PL regularity needed when extending maps of links to maps of
vertex stars. The finite-decomposition extension assumes a bounded base; the
PL extension assumes a compact base.

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

variable {ι : Type*}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

-- Use Mathlib's continuous-affine decomposition and continuous-linear product combinators.
/-- The homogeneous affine piece associated to a base piece. It includes the height coordinate
so that it has the same codomain as `coneMap`. -/
private def coneAffinePiece (A : (ι → ℝ) →ᴬ[ℝ] F) :
    ((ι → ℝ) × ℝ) →ᴬ[ℝ] (F × ℝ) :=
  ((A.contLinear.comp (ContinuousLinearMap.fst ℝ _ _) +
      (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).smulRight (A 0)).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ)).toContinuousAffineMap

private theorem coneAffinePiece_apply (A : (ι → ℝ) →ᴬ[ℝ] F) (p : (ι → ℝ) × ℝ) :
    coneAffinePiece A p = (A.contLinear p.1 + p.2 • A 0, p.2) := (rfl)

private theorem coneAffinePiece_ray (A : (ι → ℝ) →ᴬ[ℝ] F) (x : ι → ℝ) (t : ℝ) :
    coneAffinePiece A (t • x, t) = (t • A x, t) := by
  rw [coneAffinePiece_apply, map_smul, ← smul_add]
  congr 2
  exact (congrFun A.decomp x).symm

/-- A homogenized cell, cut off in every coordinate to remove height-zero recession directions. -/
private def coneCell {n : ℕ} (a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ) (R : ℝ) :
    Set ((ι → ℝ) × ℝ) :=
  {p | 0 ≤ p.2 ∧ (∀ i, |p.1 i| ≤ R * p.2) ∧
    ∀ j, (a j).contLinear p.1 + p.2 * a j 0 ≤ 0}

variable [Finite ι]

private theorem isConvexPolyhedron_coneCell {n : ℕ}
    (a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ) (R : ℝ) : IsConvexPolyhedron (coneCell a R) := by
  let height := (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).toContinuousAffineMap
  let coord (i : ι) := ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)).toContinuousAffineMap
  let inequalities : Unit ⊕ (ι ⊕ ι) ⊕ Fin n → ((ι → ℝ) × ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun _ => -height) (Sum.elim
      (Sum.elim (fun i => coord i - R • height) (fun i => -coord i - R • height))
      (fun j => ((a j).contLinear.comp (ContinuousLinearMap.fst ℝ _ _) +
        (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).smulRight (a j 0)).toContinuousAffineMap))
  convert isConvexPolyhedron_setOf_forall inequalities using 1
  ext p
  simp [coneCell, inequalities, height, coord, Sum.forall, abs_le, forall_and, neg_le, and_comm]

omit [Finite ι] in
private theorem coneCell_zero {n : ℕ} (a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ) (R : ℝ) :
    (0 : (ι → ℝ) × ℝ) ∈ coneCell a R := by simp [coneCell]

omit [Finite ι] in
private theorem coneCell_eq_zero_of_height_zero {n : ℕ}
    {a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ} {R : ℝ} {p : (ι → ℝ) × ℝ}
    (hp : p ∈ coneCell a R) (ht : p.2 = 0) : p = 0 := by
  apply Prod.ext
  · ext i
    have hi := hp.2.1 i
    simpa [ht] using hi
  · exact ht

omit [Finite ι] in
private theorem coneCell_ray {n : ℕ} {a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ}
    {R : ℝ} {x : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ i, |x i| ≤ R) (hx : ∀ j, a j x ≤ 0) :
    (t • x, t) ∈ coneCell a R := by
  refine ⟨ht, fun i => ?_, fun j => ?_⟩
  · simpa [abs_mul, abs_of_nonneg ht, mul_comm] using mul_le_mul_of_nonneg_left (hbound i) ht
  · have heq := congrArg Prod.fst (coneAffinePiece_ray (a j) x t)
    simp only [coneAffinePiece_apply, smul_eq_mul] at heq
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos ht (hx j)

omit [Finite ι] in
private theorem coneCell_normalize {n : ℕ} {a : Fin n → (ι → ℝ) →ᴬ[ℝ] ℝ}
    {R : ℝ} {p : (ι → ℝ) × ℝ} (hp : p ∈ coneCell a R) (ht : 0 < p.2) :
    ∀ j, a j (p.2⁻¹ • p.1) ≤ 0 := by
  intro j
  have heq := congrArg Prod.fst (coneAffinePiece_ray (a j) (p.2⁻¹ • p.1) p.2)
  simp only [smul_inv_smul₀ ht.ne'] at heq
  simp only [coneAffinePiece_apply, smul_eq_mul] at heq
  have hmul : p.2 * a j (p.2⁻¹ • p.1) ≤ 0 := heq ▸ hp.2.2 j
  nlinarith

/-- A finite piecewise-affine map on a bounded base extends piecewise affinely over the whole
geometric cone, including the apex. No closedness or polyhedral assumption on the base is needed. -/
theorem IsPiecewiseAffineOn.coneMap (hf : IsPiecewiseAffineOn f s)
    (hs : Bornology.IsBounded s) : IsPiecewiseAffineOn (coneMap f) (coneSet s) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨n, C, A, hC, hcover, heq⟩ := isPiecewiseAffineOn_iff.mp hf
  choose radius hpos hbound using fun i => (hs.image_eval i).exists_pos_norm_le (E := ℝ)
  let R := ∑ i, radius i
  have hR (x : ι → ℝ) (hx : x ∈ s) (i : ι) : |x i| ≤ R := by
    exact (hbound i _ ⟨x, hx, rfl⟩).trans
      (Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i))
  -- Bound the base cells in a coordinate box before homogenizing their inequalities,
  -- so the height-zero slices contain only the apex rather than recession directions.
  choose m a ha using fun i => isConvexPolyhedron_iff.mp (hC i)
  -- Keep an apex cell even when the base decomposition has no pieces.
  let cells : Option (Fin n) → Set ((ι → ℝ) × ℝ) :=
    fun i => match i with
      | none => coneCell (fun _ : Fin 1 => ContinuousAffineMap.const ℝ (ι → ℝ) 1) 0
      | some i => coneCell (a i) R
  let pieces : Option (Fin n) → ((ι → ℝ) × ℝ) →ᴬ[ℝ] (F × ℝ) :=
    fun i => match i with
      | none => ContinuousAffineMap.const ℝ _ 0
      | some i => coneAffinePiece (A i)
  refine isPiecewiseAffineOn_of_finite (C := cells) (A := pieces) ?_ ?_ ?_
  · rintro (_ | i) <;> exact isConvexPolyhedron_coneCell _ _
  · intro p hp
    rcases mem_coneSet.mp hp with rfl | ⟨ht, hx⟩
    · exact mem_iUnion.mpr ⟨none, coneCell_zero _ _⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      have hnorm : ∀ j, |(p.2⁻¹ • p.1) j| ≤ R := hR _ hx
      have hcell := coneCell_ray ht.le hnorm (by rwa [ha i] at hi)
      simp only [smul_inv_smul₀ ht.ne'] at hcell
      exact mem_iUnion.mpr ⟨some i, hcell⟩
  · rintro (_ | i) p ⟨hp, hc⟩
    · have ht : p.2 = 0 := le_antisymm
        (by simpa [cells] using hc.2.2 0) hc.1
      rw [coneCell_eq_zero_of_height_zero hc ht, coneMap_zero]
      rfl
    · rcases mem_coneSet.mp hp with rfl | ⟨ht, hx⟩
      · simp [pieces, coneAffinePiece_apply]
        rfl
      · have hbase : p.2⁻¹ • p.1 ∈ C i := by
          rw [ha i]
          exact coneCell_normalize hc ht
        have hvalue := heq i ⟨hx, hbase⟩
        have hpiece := coneAffinePiece_ray (A i) (p.2⁻¹ • p.1) p.2
        simpa [smul_inv_smul₀ ht.ne', Prod.ext_iff, pieces, hvalue] using hpiece.symm

/-- A PL map on a compact base extends to a PL map of geometric cones, including at the apex.
The target may be any real topological vector space. -/
theorem IsPLOn.coneMap (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPLOn (coneMap f) (coneSet s) := by
  have hbound : Bornology.IsBounded s :=
    Bornology.forall_isBounded_image_eval_iff.mp fun i =>
      (hs.image (continuous_apply i)).isBounded
  exact ((hf.isPiecewiseAffineOn_of_isCompact hs).coneMap hbound).isPLOn

end PiecewiseAffine

end TauCeti
