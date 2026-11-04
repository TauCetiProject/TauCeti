/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DoublePoint
public import TauCeti.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Stability of transverse polygon crossings

A transverse crossing of two projected edges is determined by a nonsingular three-by-three
linear system. Its solution records the two edge parameters and the signed separation in the
viewing direction. We construct these coordinates and prove that they vary continuously with
the vertices and the viewing direction wherever the system is nonsingular.

Consequently, an interior crossing with distinct spatial preimages persists under small
perturbations. Both the over/under choice and the sign of the ordered triple of edge directions
are unchanged. This is the local control of ordinary crossings needed when comparing diagrams
along a deformation; it does not address the singular events giving Reidemeister moves.

We work in an affine three-space with a chosen basis `b` of its vector space. The equation is
`edgePath i s = a • d +ᵥ edgePath j t`, so `a > 0` means that the first strand is over when
viewed from the side into which `d` points. The preserved orientation sign is computed by
`b.det`, as in the polygon Gauss-code API. Coordinate three-space is recovered by taking
`b = Pi.basisFun ℝ (Fin 3)`. For continuity, the vector space is a Hausdorff topological real
vector space and subtraction of affine points is continuous.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Chapter I (regular projections).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (crossings of projections).
-/

public section

open Set Filter Topology Matrix Module

namespace Polygon

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A] {n : ℕ}

/-- The crossing system for edges `i`, `j` in the basis `b`: its columns are the first edge
direction, minus the second edge direction, and minus the viewing direction. -/
noncomputable def crossingMatrix (poly : Polygon A n) (b : Basis (Fin 3) ℝ V) (d : V)
    (i j : Fin n) : Matrix (Fin 3) (Fin 3) ℝ :=
  b.toMatrix ![poly (finRotate n i) -ᵥ poly i, -(poly (finRotate n j) -ᵥ poly j), -d]

/-- The crossing coordinates `(s, t, a)`, satisfying
`edgePath i s = a • d +ᵥ edgePath j t` when the crossing system is nonsingular.
Outside that locus these are the values of Mathlib's totalized matrix inverse. -/
noncomputable def crossingCoordinates (poly : Polygon A n) (b : Basis (Fin 3) ℝ V) (d : V)
    (i j : Fin n) : Fin 3 → ℝ :=
  (poly.crossingMatrix b d i j)⁻¹ *ᵥ b.equivFun (poly j -ᵥ poly i)

/-- The determinant of the crossing system is the oriented volume in the basis `b` of the
ordered triple of the two edge directions and the viewing direction. The two minus signs cancel. -/
@[simp]
theorem det_crossingMatrix (poly : Polygon A n) (b : Basis (Fin 3) ℝ V) (d : V)
    (i j : Fin n) :
    (poly.crossingMatrix b d i j).det =
      b.det ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d] := by
  simp [crossingMatrix, Basis.det_apply, Basis.toMatrix_apply, Matrix.det_fin_three,
    -neg_vsub_eq_vsub_rev]

/-- A transverse ordered triple of edge directions and viewing direction gives a nonsingular
crossing system. -/
theorem det_crossingMatrix_ne_zero {poly : Polygon A n} (b : Basis (Fin 3) ℝ V) {d : V}
    {i j : Fin n}
    (h : LinearIndependent ℝ
      ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d]) :
    (poly.crossingMatrix b d i j).det ≠ 0 := by
  rw [det_crossingMatrix, Basis.det_apply, ← Matrix.det_transpose]
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_row_iff_isUnit.mp
  exact h.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)

private theorem crossingMatrix_mulVec (poly : Polygon A n) (b : Basis (Fin 3) ℝ V)
    (d : V) (i j : Fin n) (c : Fin 3 → ℝ) :
    (poly.crossingMatrix b d i j) *ᵥ c =
      b.equivFun (c 0 • (poly (finRotate n i) -ᵥ poly i) -
        c 1 • (poly (finRotate n j) -ᵥ poly j) - c 2 • d) := by
  ext k
  simp [crossingMatrix, Basis.toMatrix_apply, Basis.equivFun_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, -neg_vsub_eq_vsub_rev]
  ring

/-- The linear system is exactly the equality of the two edge points up to displacement in
the viewing direction. This characterization also holds for singular systems. -/
theorem crossingMatrix_mulVec_eq_iff (poly : Polygon A n) (b : Basis (Fin 3) ℝ V)
    (d : V) (i j : Fin n) (c : Fin 3 → ℝ) :
    (poly.crossingMatrix b d i j) *ᵥ c = b.equivFun (poly j -ᵥ poly i) ↔
      poly.edgePath ℝ i (c 0) = c 2 • d +ᵥ poly.edgePath ℝ j (c 1) := by
  rw [crossingMatrix_mulVec, b.equivFun.injective.eq_iff]
  rw [← (vsub_left_injective (poly i)).eq_iff]
  simp only [edgePath, AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero]
  constructor <;> intro h <;> linear_combination (norm := module) h

/-- At a transverse pair of edges the crossing coordinates are the unique solution, including
solutions outside the edges themselves. -/
theorem crossingCoordinates_eq_iff {poly : Polygon A n} {b : Basis (Fin 3) ℝ V} {d : V}
    {i j : Fin n} (h : (poly.crossingMatrix b d i j).det ≠ 0) (c : Fin 3 → ℝ) :
    poly.crossingCoordinates b d i j = c ↔
      poly.edgePath ℝ i (c 0) = c 2 • d +ᵥ poly.edgePath ℝ j (c 1) := by
  rw [← crossingMatrix_mulVec_eq_iff]
  constructor
  · intro hc
    rw [← hc, crossingCoordinates, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]
  · intro hc
    rw [crossingCoordinates, ← hc, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]

/-- The points specified by the crossing coordinates have the same projection. -/
theorem crossingCoordinates_projAlong_eq {poly : Polygon A n} {b : Basis (Fin 3) ℝ V} {d : V}
    {i j : Fin n} (h : (poly.crossingMatrix b d i j).det ≠ 0) (p₀ : A) :
    projAlong ℝ p₀ d (poly.edgePath ℝ i (poly.crossingCoordinates b d i j 0)) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j (poly.crossingCoordinates b d i j 1)) := by
  have hc := (crossingCoordinates_eq_iff h (poly.crossingCoordinates b d i j)).mp rfl
  exact projAlong_eq_projAlong_iff.mpr ⟨poly.crossingCoordinates b d i j 2, by
    rw [hc, vadd_vsub]⟩

section Families

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [TopologicalSpace A] [IsTopologicalAddTorsor A]
  (b : Basis (Fin 3) ℝ V)
  {X : Type*} [TopologicalSpace X] {x : X}
  {P : X → Polygon A n} {d : X → V} {i j : Fin n}

/-- The crossing matrix depends continuously on its four endpoints and the viewing direction.
No simplicity or regularity assumption on the other edges is required. -/
theorem continuousAt_crossingMatrix
    (hi : ContinuousAt (fun y ↦ P y i) x)
    (hi' : ContinuousAt (fun y ↦ P y (finRotate n i)) x)
    (hj : ContinuousAt (fun y ↦ P y j) x)
    (hj' : ContinuousAt (fun y ↦ P y (finRotate n j)) x)
    (hd : ContinuousAt d x) :
    ContinuousAt (fun y ↦ (P y).crossingMatrix b (d y) i j) x := by
  apply continuousAt_pi.mpr
  intro k
  apply continuousAt_pi.mpr
  intro l
  have hb := (continuous_apply k).comp (continuous_equivFun_basis b)
  fin_cases l <;> simp only [crossingMatrix, Basis.toMatrix_apply]
  · exact hb.continuousAt.comp (hi'.vsub hi)
  · exact hb.continuousAt.comp ((hj'.vsub hj).neg)
  · exact hb.continuousAt.comp hd.neg

/-- The crossing parameters and signed separation depend continuously on moving endpoints and
viewing direction at every transverse pair. -/
theorem continuousAt_crossingCoordinates
    (hi : ContinuousAt (fun y ↦ P y i) x)
    (hi' : ContinuousAt (fun y ↦ P y (finRotate n i)) x)
    (hj : ContinuousAt (fun y ↦ P y j) x)
    (hj' : ContinuousAt (fun y ↦ P y (finRotate n j)) x)
    (hd : ContinuousAt d x)
    (h : ((P x).crossingMatrix b (d x) i j).det ≠ 0) :
    ContinuousAt (fun y ↦ (P y).crossingCoordinates b (d y) i j) x := by
  have hm := continuousAt_crossingMatrix b hi hi' hj hj' hd
  have hinv := hm.matrix_inv h
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
    (hinv.prodMk ((continuous_equivFun_basis b).continuousAt.comp (hj.vsub hi)))

/-- An interior transverse crossing with nonzero separation persists under small perturbations.
The canonical crossing parameters remain interior, the system remains nonsingular, and both
its oriented determinant sign in the basis `b` and its over/under choice are unchanged. -/
theorem eventually_crossingCoordinates_mem_and_sign_eq
    (hi : ContinuousAt (fun y ↦ P y i) x)
    (hi' : ContinuousAt (fun y ↦ P y (finRotate n i)) x)
    (hj : ContinuousAt (fun y ↦ P y j) x)
    (hj' : ContinuousAt (fun y ↦ P y (finRotate n j)) x)
    (hd : ContinuousAt d x)
    (h : ((P x).crossingMatrix b (d x) i j).det ≠ 0)
    (hs : (P x).crossingCoordinates b (d x) i j 0 ∈ Ioo (0 : ℝ) 1)
    (ht : (P x).crossingCoordinates b (d x) i j 1 ∈ Ioo (0 : ℝ) 1)
    (ha : (P x).crossingCoordinates b (d x) i j 2 ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      ((P y).crossingMatrix b (d y) i j).det ≠ 0 ∧
      (P y).crossingCoordinates b (d y) i j 0 ∈ Ioo (0 : ℝ) 1 ∧
      (P y).crossingCoordinates b (d y) i j 1 ∈ Ioo (0 : ℝ) 1 ∧
      SignType.sign ((P y).crossingCoordinates b (d y) i j 2) =
        SignType.sign ((P x).crossingCoordinates b (d x) i j 2) ∧
      SignType.sign (b.det ![(P y) (finRotate n i) -ᵥ (P y) i,
        (P y) (finRotate n j) -ᵥ (P y) j, d y]) =
        SignType.sign (b.det ![(P x) (finRotate n i) -ᵥ (P x) i,
          (P x) (finRotate n j) -ᵥ (P x) j, d x]) := by
  have hm : ContinuousAt (fun y ↦ ((P y).crossingMatrix b (d y) i j).det) x :=
    continuous_id.matrix_det.continuousAt.comp
      (continuousAt_crossingMatrix b hi hi' hj hj' hd)
  have hc (k : Fin 3) : ContinuousAt (fun y ↦ (P y).crossingCoordinates b (d y) i j k) x :=
    (continuous_apply k).continuousAt.comp (continuousAt_crossingCoordinates b hi hi' hj hj' hd h)
  have hs' := (hc 0).eventually (isOpen_Ioo.mem_nhds hs)
  have ht' := (hc 1).eventually (isOpen_Ioo.mem_nhds ht)
  have hsa : ContinuousAt (fun y ↦ SignType.sign ((P y).crossingCoordinates b (d y) i j 2)) x :=
    (continuousAt_sign_of_ne_zero ha).comp
      (f := fun y ↦ (P y).crossingCoordinates b (d y) i j 2) (hc 2)
  have hsm : ContinuousAt (fun y ↦ SignType.sign (((P y).crossingMatrix b (d y) i j).det)) x :=
    (continuousAt_sign_of_ne_zero h).comp
      (f := fun y ↦ ((P y).crossingMatrix b (d y) i j).det) hm
  have ha' := hsa.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
  have hm' := hsm.eventually ((isOpen_discrete _).mem_nhds (Set.mem_singleton _))
  filter_upwards [hm.eventually_ne h, hs', ht', ha', hm'] with y hy hs ht ha hm
  exact ⟨hy, hs, ht, ha, by simpa only [det_crossingMatrix] using hm⟩

/-- An ordinary crossing of a regular projection persists when its four endpoints and the
viewing direction vary continuously. Near the original parameter there is a unique crossing of
the same two edges, with interior parameters, the same sign of separation, and the same determinant
sign in the basis `b`. No continuity or regularity of the rest of the perturbed diagram is
required. -/
theorem IsRegularProjection.eventually_exists_crossing
    {p₀ : A} (hπ : (P x).IsRegularProjection ℝ (projAlong ℝ p₀ (d x)))
    (b : Basis (Fin 3) ℝ V)
    (hi : ContinuousAt (fun y ↦ P y i) x)
    (hi' : ContinuousAt (fun y ↦ P y (finRotate n i)) x)
    (hj : ContinuousAt (fun y ↦ P y j) x)
    (hj' : ContinuousAt (fun y ↦ P y (finRotate n j)) x)
    (hd : ContinuousAt d x)
    (hsimple : (P x).IsSimple ℝ) {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hne : (P x).edgePath ℝ i s ≠ (P x).edgePath ℝ j t)
    (hproj : projAlong ℝ p₀ (d x) ((P x).edgePath ℝ i s) =
      projAlong ℝ p₀ (d x) ((P x).edgePath ℝ j t)) :
    ∃ a : ℝ, a ≠ 0 ∧
      (P x).edgePath ℝ i s = a • d x +ᵥ (P x).edgePath ℝ j t ∧
      ∀ᶠ y in 𝓝 x, ∃! c : Fin 3 → ℝ,
        (P y).edgePath ℝ i (c 0) = c 2 • d y +ᵥ (P y).edgePath ℝ j (c 1) ∧
        c 0 ∈ Ioo (0 : ℝ) 1 ∧ c 1 ∈ Ioo (0 : ℝ) 1 ∧
        SignType.sign (c 2) = SignType.sign a ∧
        SignType.sign (b.det ![(P y) (finRotate n i) -ᵥ (P y) i,
          (P y) (finRotate n j) -ᵥ (P y) j, d y]) =
          SignType.sign (b.det ![(P x) (finRotate n i) -ᵥ (P x) i,
            (P x) (finRotate n j) -ᵥ (P x) j, d x]) := by
  obtain ⟨a, ha⟩ := projAlong_eq_projAlong_iff.mp hproj
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (vsub_eq_zero_iff_eq.mp (by simpa using ha.symm))
  have heq : (P x).edgePath ℝ i s = a • d x +ᵥ (P x).edgePath ℝ j t := by
    rw [ha, vsub_vadd]
  have hm := det_crossingMatrix_ne_zero b
    (hπ.linearIndependent_of_projAlong_eq hsimple hs ht hne hproj)
  have hc : (P x).crossingCoordinates b (d x) i j = ![s, t, a] :=
    (crossingCoordinates_eq_iff hm _).mpr heq
  refine ⟨a, ha0, heq, ?_⟩
  have hev := eventually_crossingCoordinates_mem_and_sign_eq b hi hi' hj hj' hd hm
    (by simpa [hc] using hs)
    (by simpa [hc] using ht)
    (by simpa [hc] using ha0)
  filter_upwards [hev] with y hy
  refine ⟨(P y).crossingCoordinates b (d y) i j, ?_, ?_⟩
  · exact ⟨(crossingCoordinates_eq_iff hy.1 _).mp rfl, hy.2.1, hy.2.2.1,
      by simpa [hc] using hy.2.2.2.1, hy.2.2.2.2⟩
  · intro c hcross
    exact ((crossingCoordinates_eq_iff hy.1 c).mpr hcross.1).symm

end Families

end Polygon
