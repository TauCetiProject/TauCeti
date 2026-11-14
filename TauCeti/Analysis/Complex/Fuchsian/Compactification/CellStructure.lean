/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.VertexCycle
public import TauCeti.Analysis.Complex.Fuchsian.Polygon.Area
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.PermutationTriple
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Side.Presentation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.ParabolicClosure
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Identification
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Side.EdgeArc
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.MetricSpace.Pseudo.Pi
import TauCeti.Topology.Separation.InvFunOn

/-!
# The CW structure and Euler characteristic of a cuspidal fundamental polygon

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, with vertices in `ℍ ∪ ∂ℍ`, and let a
discrete subgroup `Γ ≤ PSL(2, ℝ)` contain the side-pairing maps, with locally finite translates of
`P` whose interiors are pairwise disjoint. Adjoining the cusp orbits of `Γ` to the coarse quotient
`Γ \ ℍ` gives the compactified quotient `X(Γ) = Γ.CompactifiedQuotient`. This file constructs an
explicit finite CW complex structure on `X(Γ)` directly from `(P, σ)`:

* `0`-cells: the `V` finite vertex cycles in `Γ \ ℍ`, the `c` adjoined cusp orbits (the ideal
  vertex cycles of `(P, σ)`), and the `k` orbits of the fixed points of self-paired sides;
* `1`-cells: one open edge for each of the `E = (n + k) / 2` side pairs (`σ.SideRepresentative`),
  parametrized via `σ.edgeArc`, carrying the whole side when `σ.pair i ≠ i` and the half-side up to
  `σ.selfPairedSideFixedPoint` when `σ.pair i = i`, with ideal endpoints converging to their cusp
  `0`-cells along horodiscs;
* `2`-cell: one face, obtained from the parabolic disk compactification of `P`
  (`ConvexPolygon.exists_equiv_closedBall`), whose interior maps bijectively onto the image of
  `interior P.carrier` and whose ideal-vertex boundary points map to the corresponding cusps.

Consequently `X(Γ)` has finite CW type, its Euler characteristic is
`χ(X(Γ)) = V + c + k - E + 1 = σ.toPermutationTriple.eulerChar`, and the connected combinatorial
surface `σ.toPermutationTriple` supplies `χ(X(Γ)) ≤ 2` and `Even χ(X(Γ))`, proving the genus bridge
`χ(X(Γ)) = 2 - 2 · genus X(Γ)` and `genus X(Γ) = σ.toPermutationTriple.genus`. Substituting this
into the polygon Gauss–Bonnet formula `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul` yields the
orbifold area formula with cusps (`covolume_eq_two_pi_mul_signature`).

## Main results

* `ConvexPolygon.SidePairing.finiteCWType_compactifiedQuotient`: `Γ.CompactifiedQuotient` has
  finite CW type.
* `ConvexPolygon.SidePairing.eulerChar_compactifiedQuotient`:
  `χ(X(Γ)) = V + c + k - E + 1`.
* `ConvexPolygon.SidePairing.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus`:
  `χ(X(Γ)) = 2 - 2 · genus X(Γ)`.
* `ConvexPolygon.SidePairing.genus_compactifiedQuotient_eq`:
  `genus X(Γ) = σ.toPermutationTriple.genus`.
* `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps` and
  `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_signature`: the orbifold area formula in Euler
  characteristic and signature (`2g - 2 + ∑ₑ (1 - 1 / mₑ) + c`) form.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §§9.3 and 10.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago Press,
  1992, §§4.2–4.3.
-/

public section

noncomputable section

open MeasureTheory Metric MulAction Set Topology Topology.RelCWComplex UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

/-! ### Orbit identifications on `P` -/

section Orbits

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}
  (hmap : ∀ i, σ.map i ∈ Γ)
  (hdisj : ∀ γ : Γ, γ ≠ 1 → Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

include hmap hdisj in
private theorem eq_or_eq_map_smul_of_mk_eq {i : Fin n} {u : ℝ} (hu : u ∈ Ioo (-1) 1) {w : ℍ}
    (hw : w ∈ P.carrier) (h : π w = π (σ.edgeArc i u)) :
    w = σ.edgeArc i u ∨ w = σ.map i • σ.edgeArc i u := by
  have hside := σ.edgeArc_mem_side i hu
  have hne := σ.vertex_ne_inl_edgeArc i hu
  rw [Quotient.eq'', orbitRel_apply] at h
  rcases (σ.mem_orbit_iff_of_mem_carrier hmap hdisj (P.side_subset_carrier i hside) hw).1 h with
    h | ⟨j, hj, rfl⟩ | ⟨j, -, hj, -, -⟩
  · exact Or.inl h
  · obtain rfl := P.eq_of_mem_side_of_mem_side hside (hne i) (hne (i + 1)) hj
    exact Or.inr rfl
  · exact (hne j hj).elim

include hmap hdisj in
private theorem edgeArc_eq_or_of_mk_eq {i j : Fin n} {u v : ℝ}
    (hu : u ∈ Ioo (-1) 1) (hv : v ∈ Ioo (-1) 1)
    (h : π (σ.edgeArc j v) = π (σ.edgeArc i u)) :
    (j = i ∧ v = u) ∨ (j = σ.pair i ∧ σ.edgeArc j v = σ.map i • σ.edgeArc i u) := by
  have hsi := σ.edgeArc_mem_side i hu
  have hsj := σ.edgeArc_mem_side j hv
  have hnej := σ.vertex_ne_inl_edgeArc j hv
  rcases σ.eq_or_eq_map_smul_of_mk_eq hmap hdisj hu (P.side_subset_carrier j hsj) h with heq | heq
  · obtain rfl := P.eq_of_mem_side_of_mem_side hsj (hnej j) (hnej (j + 1)) (heq ▸ hsi)
    exact Or.inl ⟨rfl, σ.injOn_edgeArc j hv hu heq⟩
  · refine Or.inr ⟨P.eq_of_mem_side_of_mem_side hsj (hnej j) (hnej (j + 1)) ?_, heq⟩
    exact heq ▸ σ.map_smul_mem_side hsi

include hmap hdisj in
private theorem exists_vertex_eq_of_mk_eq {j : Fin n} {v w : ℍ}
    (hv : P.vertex j = .inl v) (hw : w ∈ P.carrier) (h : π w = π v) :
    ∃ k, P.vertex k = .inl w := by
  rw [Quotient.eq'', orbitRel_apply] at h
  rcases (σ.mem_orbit_iff_of_mem_carrier hmap hdisj
      (P.side_subset_carrier j (P.mem_side_of_vertex_eq_inl hv)) hw).1 h with
    rfl | ⟨k, hk, rfl⟩ | ⟨-, k, -, hk, -⟩
  · exact ⟨j, hv⟩
  · rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hv hk with rfl | rfl
    · exact ⟨σ.pair j + 1, by simpa [hv] using (σ.map_smul_vertex j).symm⟩
    · exact ⟨σ.pair k, by simpa [hv] using (σ.map_smul_vertex_add_one k).symm⟩
  · exact ⟨k, hk⟩

omit σ hmap in
include hdisj in
private theorem eq_of_mk_eq_of_mem_interior {z w : ℍ}
    (hz : z ∈ interior P.carrier) (hw : w ∈ P.carrier) (h : π w = π z) : w = z := by
  rw [Quotient.eq'', orbitRel_apply, mem_orbit_iff] at h
  obtain ⟨γ, rfl⟩ := h
  by_contra hne
  have hγ : γ ≠ 1 := fun h1 ↦ hne (by simp [h1])
  have hopen : IsOpen ((γ : PSL(2, ℝ)) • interior P.carrier) :=
    (Homeomorph.smul (γ : PSL(2, ℝ))).isOpenMap _ isOpen_interior
  have hd := (hdisj γ hγ).closure_right hopen
  rw [P.closure_interior_carrier] at hd
  exact disjoint_left.1 hd (smul_mem_smul_set hz) hw

omit σ hmap in
include hdisj in
private theorem mk_notMem_image_interior {j : Fin n} {z : ℍ} (hz : z ∈ P.side j) :
    π z ∉ π '' interior P.carrier := by
  rintro ⟨w, hw, h⟩
  obtain rfl := eq_of_mk_eq_of_mem_interior hdisj hw (P.side_subset_carrier j hz) h.symm
  exact disjoint_left.1 disjoint_interior_frontier hw (P.side_subset_frontier_carrier j hz)

end Orbits

/-! ### The `0`-cells -/

section ZeroCells

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

variable (P Γ) in
private def finiteVertexOrbits : Set Γ.CompactifiedQuotient :=
  range fun j : {i : Fin n // (P.vertex i).isLeft} ↦ ofQuotient (π ((P.vertex j).getLeft j.2))

variable (Γ) in
private def midpointOrbits : Set Γ.CompactifiedQuotient :=
  range fun i : {i : Fin n // σ.pair i = i} ↦ ofQuotient (π (σ.selfPairedSideFixedPoint i))

variable (Γ) in
/-- The `0`-cells of `Γ.CompactifiedQuotient`: finite vertex cycles, self-paired midpoints, and
cusp orbits. -/
private def zeroCells : Set Γ.CompactifiedQuotient :=
  (finiteVertexOrbits P Γ ∪ σ.midpointOrbits Γ) ∪ range (ofCusp (Γ := Γ))

private theorem finite_zeroCells (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    (σ.zeroCells Γ).Finite := by
  have := σ.finite_cuspOrbit hmap hlf
  exact ((finite_range _).union (finite_range _)).union (finite_range _)

private theorem disjoint_finiteVertexOrbits_midpointOrbits (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Disjoint (finiteVertexOrbits P Γ) (σ.midpointOrbits Γ) := by
  rw [disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
  exact σ.quotientMk_vertex_ne_selfPairedSideFixedPoint hmap hdisj
    (Sum.inl_getLeft _ j.2).symm i (ofQuotient_injective hi.symm)

private theorem disjoint_interiorZeroCells_cusps :
    Disjoint (finiteVertexOrbits P Γ ∪ σ.midpointOrbits Γ) (range (ofCusp (Γ := Γ))) := by
  rw [disjoint_left]
  rintro _ (⟨j, rfl⟩ | ⟨i, rfl⟩) ⟨C, hC⟩ <;> cases hC

private theorem natCard_zeroCells (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Nat.card (σ.zeroCells Γ) =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} := by
  have := σ.finite_cuspOrbit hmap hlf
  have hfin₁ : (finiteVertexOrbits P Γ).Finite := finite_range _
  have hfin₂ : (σ.midpointOrbits Γ).Finite := finite_range _
  have hfin₃ : (range (ofCusp (Γ := Γ))).Finite := finite_range _
  rw [zeroCells, Nat.card_coe_set_eq,
    ncard_union_eq σ.disjoint_interiorZeroCells_cusps (hfin₁.union hfin₂) hfin₃,
    ncard_union_eq (σ.disjoint_finiteVertexOrbits_midpointOrbits hmap hdisj) hfin₁ hfin₂,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  have hV : Nat.card (finiteVertexOrbits P Γ) = Nat.card σ.FiniteVertexCycle := by
    have heq : finiteVertexOrbits P Γ = ofQuotient '' range
        (fun j : {i : Fin n // (P.vertex i).isLeft} ↦ π ((P.vertex j).getLeft j.2)) := by
      ext x
      simp [finiteVertexOrbits]
    rw [heq, Nat.card_image_of_injective ofQuotient_injective,
      Nat.card_congr (σ.finiteVertexCycleEquiv hmap hdisj)]
  have hM : Nat.card (σ.midpointOrbits Γ) = Nat.card {i : Fin n // σ.pair i = i} :=
    Nat.card_range_of_injective
      (ofQuotient_injective.comp (σ.injective_quotientMk_selfPairedSideFixedPoint hmap hdisj))
  have hC : Nat.card (range (ofCusp (Γ := Γ))) = Nat.card σ.IdealVertexCycle := by
    rw [Nat.card_range_of_injective fun _ _ h ↦ ofCusp.inj h, σ.natCard_cuspOrbit hmap hlf hdisj]
  rw [hV, hM, hC]
  omega

private theorem ofQuotient_mk_edgeArc_notMem_zeroCells (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {i : Fin n} {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    ofQuotient (π (σ.edgeArc i u)) ∉ σ.zeroCells Γ := by
  rintro ((⟨j, hj⟩ | ⟨j, hj⟩) | ⟨C, hC⟩)
  · obtain ⟨k, hk⟩ := σ.exists_vertex_eq_of_mk_eq hmap hdisj (Sum.inl_getLeft _ j.2).symm
      (P.side_subset_carrier i (σ.edgeArc_mem_side i hu)) (ofQuotient_injective hj.symm)
    exact σ.vertex_ne_inl_edgeArc i hu k hk
  · rcases σ.eq_or_eq_map_smul_of_mk_eq hmap hdisj hu
        (P.side_subset_carrier j.1 (σ.selfPairedSideFixedPoint_spec j).1)
        (ofQuotient_injective hj) with heq | heq
    · exact σ.edgeArc_ne_selfPairedSideFixedPoint i hu j heq.symm
    · exact σ.map_smul_edgeArc_ne_selfPairedSideFixedPoint i hu j heq.symm
  · cases hC

/-- The `0`-cell attached to vertex `i` of `P` (a finite vertex orbit or a cusp orbit). -/
private def vertexZeroCell (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    Γ.CompactifiedQuotient :=
  if hl : (P.vertex i).isLeft then
    ofQuotient (π ((P.vertex i).getLeft hl))
  else
    ofCusp (Γ.cuspOrbitMk ⟨(P.vertex i).getRight (Sum.not_isLeft.1 hl),
      Subgroup.mem_cuspPoints.2 (σ.isCuspPoint_of_vertex_eq_inr
        (Sum.inr_getRight _ (Sum.not_isLeft.1 hl)).symm (σ.cycleMap_mem hmap _) hlf)⟩)

private theorem vertexZeroCell_of_eq_inl (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) {i : Fin n} {v : ℍ}
    (hv : P.vertex i = .inl v) :
    σ.vertexZeroCell hmap hlf i = ofQuotient (π v) := by
  simp [vertexZeroCell, hv]

private theorem vertexZeroCell_of_eq_inr (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) {i : Fin n} {ξ : OnePoint ℝ}
    (hξ : P.vertex i = .inr ξ) (hc : Γ.IsCuspPoint ξ) :
    σ.vertexZeroCell hmap hlf i = ofCusp (Γ.cuspOrbitMk ⟨ξ, Subgroup.mem_cuspPoints.2 hc⟩) := by
  have hl : ¬ (P.vertex i).isLeft := by simp [hξ]
  rw [vertexZeroCell, dite_eq_right hl]
  congr 2
  ext
  simp [hξ]

private theorem vertexZeroCell_mem_zeroCells (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    σ.vertexZeroCell hmap hlf i ∈ σ.zeroCells Γ := by
  unfold vertexZeroCell
  split_ifs with hl
  · exact Or.inl (Or.inl ⟨⟨i, hl⟩, rfl⟩)
  · exact Or.inr ⟨_, rfl⟩

end ZeroCells

/-! ### The `1`-cells -/

section OneCells

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

private def edgeEndCell (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    Γ.CompactifiedQuotient :=
  if hi : σ.pair i = i then
    ofQuotient (π (σ.selfPairedSideFixedPoint ⟨i, hi⟩))
  else
    σ.vertexZeroCell hmap hlf (i + 1)

private theorem edgeEndCell_mem_zeroCells (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    σ.edgeEndCell hmap hlf i ∈ σ.zeroCells Γ := by
  unfold edgeEndCell
  split_ifs with hi
  · exact Or.inl (Or.inr ⟨⟨i, hi⟩, rfl⟩)
  · exact σ.vertexZeroCell_mem_zeroCells hmap hlf (i + 1)

/-- Characteristic map of the `1`-cell carried by side `i`. -/
private def edgeMap (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (i : Fin n) (x : Fin 1 → ℝ) : Γ.CompactifiedQuotient :=
  if x 0 ∈ Ioo (-1 : ℝ) 1 then
    ofQuotient (π (σ.edgeArc i (x 0)))
  else if x 0 ≤ 0 then
    σ.vertexZeroCell hmap hlf i
  else
    σ.edgeEndCell hmap hlf i

private theorem mem_ball_fin_one_iff {x : Fin 1 → ℝ} :
    x ∈ ball (0 : Fin 1 → ℝ) 1 ↔ x 0 ∈ Ioo (-1 : ℝ) 1 := by
  rw [Pi.ball_unique, mem_preimage, Function.eval, Fin.default_eq_zero, Real.ball_eq_Ioo]
  norm_num

private theorem mem_closedBall_fin_one_iff {x : Fin 1 → ℝ} :
    x ∈ closedBall (0 : Fin 1 → ℝ) 1 ↔ x 0 ∈ Icc (-1 : ℝ) 1 := by
  rw [Pi.closedBall_unique, mem_preimage, Function.eval, Fin.default_eq_zero,
    Real.closedBall_eq_Icc]
  norm_num

private theorem mem_sphere_fin_one_iff {x : Fin 1 → ℝ} :
    x ∈ sphere (0 : Fin 1 → ℝ) 1 ↔ x = (fun _ ↦ -1) ∨ x = (fun _ ↦ 1) := by
  rw [Pi.mem_sphere_unique]
  simp only [Fin.default_eq_zero, Pi.zero_apply, mem_sphere_zero_iff_norm, Real.norm_eq_abs,
    abs_eq zero_le_one]
  refine ⟨fun h ↦ h.symm.imp (fun h1 ↦ ?_) (fun h1 ↦ ?_),
    fun h ↦ h.symm.imp (fun h1 ↦ by simp [h1]) (fun h1 ↦ by simp [h1])⟩
  · ext k; rw [Subsingleton.elim k 0, h1]
  · ext k; rw [Subsingleton.elim k 0, h1]

private theorem edgeMap_of_mem_ball (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ ball 0 1) :
    σ.edgeMap hmap hlf i x = ofQuotient (π (σ.edgeArc i (x 0))) := by
  rw [edgeMap, ite_eq_left (mem_ball_fin_one_iff.1 hx)]

private theorem image_edgeMap_ball (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    σ.edgeMap hmap hlf i '' ball 0 1 =
      (fun u ↦ ofQuotient (π (σ.edgeArc i u))) '' Ioo (-1) 1 := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [σ.edgeMap_of_mem_ball hmap hlf i hx]
    exact ⟨x 0, mem_ball_fin_one_iff.1 hx, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hx : (fun _ : Fin 1 ↦ u) ∈ ball (0 : Fin 1 → ℝ) 1 := mem_ball_fin_one_iff.2 hu
    exact ⟨fun _ ↦ u, hx, σ.edgeMap_of_mem_ball hmap hlf i hx⟩

private theorem edgeMap_mem_zeroCells (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    σ.edgeMap hmap hlf i x ∈ σ.zeroCells Γ := by
  rcases mem_sphere_fin_one_iff.1 hx with rfl | rfl
  · have hnot : (-1 : ℝ) ∉ Ioo (-1 : ℝ) 1 := by simp
    rw [edgeMap, ite_eq_right hnot, ite_eq_left (by norm_num : (-1 : ℝ) ≤ 0)]
    exact σ.vertexZeroCell_mem_zeroCells hmap hlf i
  · have hnot : (1 : ℝ) ∉ Ioo (-1 : ℝ) 1 := by simp
    rw [edgeMap, ite_eq_right hnot, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 0)]
    exact σ.edgeEndCell_mem_zeroCells hmap hlf i

private theorem injOn_edgeMap (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : Fin n) : InjOn (σ.edgeMap hmap hlf i) (ball 0 1) := by
  intro x hx y hy h
  rw [σ.edgeMap_of_mem_ball hmap hlf i hx, σ.edgeMap_of_mem_ball hmap hlf i hy] at h
  have hxu := mem_ball_fin_one_iff.1 hx
  have hyu := mem_ball_fin_one_iff.1 hy
  rcases σ.edgeArc_eq_or_of_mk_eq hmap hdisj hxu hyu (ofQuotient_injective h).symm with
    ⟨-, heq⟩ | ⟨hi, heq⟩
  · ext k
    rw [Subsingleton.elim k 0, heq]
  · exact (σ.map_smul_edgeArc_ne_edgeArc_of_pair_eq hi.symm hxu hyu heq.symm).elim

private theorem disjoint_image_edgeMap_ball (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {i j : σ.SideRepresentative} (hij : i ≠ j) :
    Disjoint (σ.edgeMap hmap hlf i '' ball 0 1) (σ.edgeMap hmap hlf j '' ball 0 1) := by
  rw [σ.image_edgeMap_ball, σ.image_edgeMap_ball, disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, h⟩
  rcases σ.edgeArc_eq_or_of_mk_eq hmap hdisj hu hv (ofQuotient_injective h) with
    ⟨heq, -⟩ | ⟨heq, -⟩
  · exact hij (Subtype.ext heq.symm)
  · have hj := j.2
    rw [heq, σ.pair_pair] at hj
    exact hij (Subtype.ext (heq.trans (le_antisymm hj i.2)).symm)

/-- Reduction of `ContinuousWithinAt` on `closedBall (0 : Fin 1 → ℝ) 1` at `fun _ ↦ c` (`c = ±1`)
to `Tendsto` along `Ioo (-1) 1`. -/
private theorem continuousWithinAt_closedBall_fin_one_of_tendsto [DiscreteTopology Γ]
    {f : (Fin 1 → ℝ) → Γ.CompactifiedQuotient} {c : ℝ} (hc : c = -1 ∨ c = 1)
    (ht : Filter.Tendsto (fun u : ℝ ↦ f (fun _ ↦ u)) (𝓝[Ioo (-1) 1] c) (𝓝 (f (fun _ ↦ c)))) :
    ContinuousWithinAt f (closedBall 0 1) (fun _ ↦ c) := by
  set x₀ : Fin 1 → ℝ := fun _ ↦ c
  set x₁ : Fin 1 → ℝ := fun _ ↦ -c
  have hne : x₀ ≠ x₁ := by
    intro h
    have h0 := congrFun h 0
    rcases hc with rfl | rfl <;> norm_num [x₀, x₁] at h0
  have heval : Filter.Tendsto (fun y : Fin 1 → ℝ ↦ y 0) (𝓝[ball 0 1] x₀) (𝓝[Ioo (-1) 1] c) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_apply 0).tendsto x₀).mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset self_mem_nhdsWithin fun y hy ↦ mem_ball_fin_one_iff.1 hy)
  have hball : ContinuousWithinAt f (ball 0 1) x₀ := by
    refine (ht.comp heval).congr' (Filter.Eventually.of_forall fun y ↦ ?_)
    dsimp only [Function.comp_apply]
    congr 1
    ext k
    rw [Subsingleton.elim k 0]
  have hinsert : ContinuousWithinAt f (insert x₀ (ball 0 1)) x₀ :=
    continuousWithinAt_insert_self.2 hball
  have hnhds : 𝓝[closedBall 0 1] x₀ = 𝓝[insert x₀ (ball 0 1)] x₀ := by
    refine nhdsWithin_eq_iff_eventuallyEqSet.2 ?_
    filter_upwards [eventually_ne_nhds hne] with y hy
    simp only [mem_insert_iff]
    constructor
    · intro hycl
      rcases eq_or_ne y x₀ with rfl | hy0
      · exact Or.inl rfl
      · right
        rw [mem_ball_fin_one_iff]
        obtain ⟨h1, h2⟩ := mem_closedBall_fin_one_iff.1 hycl
        rcases hc with rfl | rfl
        · exact ⟨h1.lt_of_ne fun h ↦ hy0 (by ext k; rw [Subsingleton.elim k 0]; exact h.symm),
            h2.lt_of_ne fun h ↦ hy (by ext k; rw [Subsingleton.elim k 0]; simpa [x₁] using h)⟩
        · exact ⟨h1.lt_of_ne fun h ↦
              hy (by ext k; rw [Subsingleton.elim k 0]; simpa [x₁] using h.symm),
            h2.lt_of_ne fun h ↦ hy0 (by ext k; rw [Subsingleton.elim k 0]; exact h)⟩
    · rintro (rfl | hyb)
      · rw [mem_closedBall_fin_one_iff]
        rcases hc with rfl | rfl <;> norm_num [x₀]
      · exact ball_subset_closedBall hyb
  rwa [ContinuousWithinAt, hnhds]

private theorem tendsto_edgeMap_neg_one [DiscreteTopology Γ] (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    Filter.Tendsto (fun u : ℝ ↦ σ.edgeMap hmap hlf i (fun _ ↦ u)) (𝓝[Ioo (-1) 1] (-1))
      (𝓝 (σ.edgeMap hmap hlf i (fun _ ↦ -1))) := by
  have hnot : (-1 : ℝ) ∉ Ioo (-1 : ℝ) 1 := by simp
  have hval : σ.edgeMap hmap hlf i (fun _ ↦ -1) = σ.vertexZeroCell hmap hlf i := by
    rw [edgeMap, ite_eq_right hnot, ite_eq_left (by norm_num : (-1 : ℝ) ≤ 0)]
  rw [hval]
  have heq : (fun u : ℝ ↦ σ.edgeMap hmap hlf i (fun _ ↦ u)) =ᶠ[𝓝[Ioo (-1) 1] (-1)]
      fun u ↦ ofQuotient (π (σ.edgeArc i u)) :=
    Filter.mem_of_superset self_mem_nhdsWithin fun u hu ↦
      σ.edgeMap_of_mem_ball hmap hlf i (mem_ball_fin_one_iff.2 hu)
  refine Filter.Tendsto.congr' heq.symm ?_
  rcases hp : P.vertex i with v | ξ
  · rw [σ.vertexZeroCell_of_eq_inl hmap hlf hp]
    exact ((continuous_ofQuotient.comp continuous_quotient_mk').tendsto v).comp
      (σ.tendsto_edgeArc_neg_one_of_eq_inl hp)
  · have hcusp := σ.isCuspPoint_of_vertex_eq_inr hp (σ.cycleMap_mem hmap _) hlf
    obtain ⟨D, hD⟩ := hcusp.exists_cuspDatum_cusp_eq
    have hcell : σ.vertexZeroCell hmap hlf i = ofCusp D.cuspOrbit := by
      rw [σ.vertexZeroCell_of_eq_inr hmap hlf hp hcusp]
      exact congrArg ofCusp (Subtype.ext (by simp [hD]))
    rw [hcell]
    have hgξ : D.scaling • ξ = ∞ := by rw [← hD, D.scaling_smul_cusp]
    exact (tendsto_ofQuotient_quotientMk_nhds_ofCusp D).comp
      (σ.tendsto_edgeArc_neg_one_atImInfty_of_eq_inr hp hgξ)

private theorem tendsto_edgeMap_one [DiscreteTopology Γ] (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    Filter.Tendsto (fun u : ℝ ↦ σ.edgeMap hmap hlf i (fun _ ↦ u)) (𝓝[Ioo (-1) 1] 1)
      (𝓝 (σ.edgeMap hmap hlf i (fun _ ↦ 1))) := by
  have hnot : (1 : ℝ) ∉ Ioo (-1 : ℝ) 1 := by simp
  have hval : σ.edgeMap hmap hlf i (fun _ ↦ 1) = σ.edgeEndCell hmap hlf i := by
    rw [edgeMap, ite_eq_right hnot, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 0)]
  rw [hval]
  have heq : (fun u : ℝ ↦ σ.edgeMap hmap hlf i (fun _ ↦ u)) =ᶠ[𝓝[Ioo (-1) 1] 1]
      fun u ↦ ofQuotient (π (σ.edgeArc i u)) :=
    Filter.mem_of_superset self_mem_nhdsWithin fun u hu ↦
      σ.edgeMap_of_mem_ball hmap hlf i (mem_ball_fin_one_iff.2 hu)
  refine Filter.Tendsto.congr' heq.symm ?_
  by_cases hi : σ.pair i = i
  · rw [edgeEndCell, dite_eq_left hi]
    exact ((continuous_ofQuotient.comp continuous_quotient_mk').tendsto _).comp
      (σ.tendsto_edgeArc_one_of_pair_eq hi)
  · rw [edgeEndCell, dite_eq_right hi]
    rcases hq : P.vertex (i + 1) with w | η
    · rw [σ.vertexZeroCell_of_eq_inl hmap hlf hq]
      exact ((continuous_ofQuotient.comp continuous_quotient_mk').tendsto w).comp
        (σ.tendsto_edgeArc_one_of_eq_inl hi hq)
    · have hcusp := σ.isCuspPoint_of_vertex_eq_inr hq (σ.cycleMap_mem hmap _) hlf
      obtain ⟨D, hD⟩ := hcusp.exists_cuspDatum_cusp_eq
      have hcell : σ.vertexZeroCell hmap hlf (i + 1) = ofCusp D.cuspOrbit := by
        rw [σ.vertexZeroCell_of_eq_inr hmap hlf hq hcusp]
        exact congrArg ofCusp (Subtype.ext (by simp [hD]))
      rw [hcell]
      have hgη : D.scaling • η = ∞ := by rw [← hD, D.scaling_smul_cusp]
      exact (tendsto_ofQuotient_quotientMk_nhds_ofCusp D).comp
        (σ.tendsto_edgeArc_one_atImInfty_of_eq_inr hi hq hgη)

private theorem continuousOn_edgeMap [DiscreteTopology Γ] (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) (i : Fin n) :
    ContinuousOn (σ.edgeMap hmap hlf i) (closedBall 0 1) := by
  intro x hx
  by_cases hxb : x ∈ ball (0 : Fin 1 → ℝ) 1
  · have hcont : ContinuousOn
        (fun y : Fin 1 → ℝ ↦ ofQuotient (π (σ.edgeArc i (y 0)))) (ball 0 1) :=
      (continuous_ofQuotient.comp continuous_quotient_mk').comp_continuousOn
        ((σ.continuousOn_edgeArc i).comp (continuous_apply 0).continuousOn
          fun y hy ↦ mem_ball_fin_one_iff.1 hy)
    have hball := (hcont x hxb).congr (fun y hy ↦ σ.edgeMap_of_mem_ball hmap hlf i hy)
      (σ.edgeMap_of_mem_ball hmap hlf i hxb)
    exact (hball.continuousAt (isOpen_ball.mem_nhds hxb)).continuousWithinAt
  · have hxs : x ∈ sphere (0 : Fin 1 → ℝ) 1 := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hx, hxb⟩
    rcases mem_sphere_fin_one_iff.1 hxs with rfl | rfl
    · exact continuousWithinAt_closedBall_fin_one_of_tendsto (Or.inl rfl)
        (σ.tendsto_edgeMap_neg_one hmap hlf i)
    · exact continuousWithinAt_closedBall_fin_one_of_tendsto (Or.inr rfl)
        (σ.tendsto_edgeMap_one hmap hlf i)

/-- Every point of a side of `P` maps to a `0`-cell or into the open `1`-cell of a side
representative. -/
private theorem mem_zeroCells_or_exists_edgeMap_of_mem_side (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    {j : Fin n} {z : ℍ} (hz : z ∈ P.side j) :
    ofQuotient (π z) ∈ σ.zeroCells Γ ∨
      ∃ i : σ.SideRepresentative, ofQuotient (π z) ∈ σ.edgeMap hmap hlf i '' ball 0 1 := by
  have hmk (w : ℍ) (k : Fin n) : π (σ.map k • w) = π w :=
    Quotient.sound (mem_orbit w (⟨σ.map k, hmap k⟩ : Γ))
  by_cases hzp : P.vertex j = .inl z
  · exact Or.inl (σ.vertexZeroCell_of_eq_inl hmap hlf hzp ▸
      σ.vertexZeroCell_mem_zeroCells hmap hlf j)
  by_cases hzq : P.vertex (j + 1) = .inl z
  · exact Or.inl (σ.vertexZeroCell_of_eq_inl hmap hlf hzq ▸
      σ.vertexZeroCell_mem_zeroCells hmap hlf (j + 1))
  by_cases hj : j ≤ σ.pair j
  · rcases σ.mem_image_edgeArc_or_selfPaired_of_mem_side hz hzp hzq with
      ⟨u, hu, rfl⟩ | ⟨hjj, rfl | ⟨u, hu, huz⟩⟩
    · refine Or.inr ⟨⟨j, hj⟩, ?_⟩
      rw [σ.image_edgeMap_ball hmap hlf]
      exact ⟨u, hu, rfl⟩
    · exact Or.inl (Or.inl (Or.inr ⟨⟨j, hjj⟩, rfl⟩))
    · refine Or.inr ⟨⟨j, hj⟩, ?_⟩
      rw [σ.image_edgeMap_ball hmap hlf]
      exact ⟨u, hu, by dsimp only; rw [huz, hmk]⟩
  · set k := σ.pair j
    have hkle : k ≤ σ.pair k := by
      rw [σ.pair_pair]
      exact (lt_of_not_ge hj).le
    have hzk : σ.map j • z ∈ P.side k := σ.map_smul_mem_side hz
    have hkp : P.vertex k ≠ .inl (σ.map j • z) := fun h ↦ hzq <|
      MulAction.injective (σ.map j)
        ((σ.map_smul_vertex_add_one j).trans (h.trans (Sum.smul_inl _ _).symm))
    have hkq : P.vertex (k + 1) ≠ .inl (σ.map j • z) := fun h ↦ hzp <|
      MulAction.injective (σ.map j)
        ((σ.map_smul_vertex j).trans (h.trans (Sum.smul_inl _ _).symm))
    have hkne : σ.pair k ≠ k := fun h ↦ hj (by rw [σ.pair_pair] at h; exact h ▸ le_rfl)
    rcases σ.mem_image_edgeArc_or_selfPaired_of_mem_side hzk hkp hkq with
      ⟨u, hu, huz⟩ | ⟨hkk, -⟩
    · refine Or.inr ⟨⟨k, hkle⟩, ?_⟩
      rw [σ.image_edgeMap_ball hmap hlf]
      exact ⟨u, hu, by dsimp only; rw [huz, hmk]⟩
    · exact (hkne hkk).elim

end OneCells

/-! ### The `2`-cell -/

section TwoCell

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

private abbrev diskHomeo : closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  closedBallHomeomorphOfFinrankEq (E := Fin 2 → ℝ) (F := ℂ) (by simp)

variable (P) in
private def diskEquiv :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃ closedBall (0 : ℂ) 1 :=
  P.exists_equiv_closedBall.choose

variable (P) in
private def faceEquiv :
    closedBall (0 : Fin 2 → ℝ) 1 ≃ P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} :=
  diskHomeo.toEquiv.trans (diskEquiv P).symm

private def facePoint (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} → Γ.CompactifiedQuotient
  | .inl z => ofQuotient (π z)
  | .inr i => σ.vertexZeroCell hmap hlf i.1

open scoped Classical in
/-- Characteristic map of the single `2`-cell. -/
private def faceMap (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (x : Fin 2 → ℝ) : Γ.CompactifiedQuotient :=
  if hx : x ∈ closedBall 0 1 then
    σ.facePoint hmap hlf (faceEquiv P ⟨x, hx⟩)
  else
    ofQuotient (π UpperHalfPlane.I)

private theorem faceMap_of_mem (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (x : closedBall (0 : Fin 2 → ℝ) 1) :
    σ.faceMap hmap hlf x = σ.facePoint hmap hlf (faceEquiv P x) := by
  rw [faceMap, dite_eq_left x.2]

private theorem diskHomeo_mem_ball_iff (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (diskHomeo x : ℂ) ∈ ball (0 : ℂ) 1 ↔ (x : Fin 2 → ℝ) ∈ ball 0 1 := by
  rw [diskHomeo, coe_closedBallHomeomorphOfFinrankEq_apply, mem_ball_zero_iff,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, ← mem_ball_zero_iff]

private theorem diskHomeo_mem_sphere_iff (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (diskHomeo x : ℂ) ∈ sphere (0 : ℂ) 1 ↔ (x : Fin 2 → ℝ) ∈ sphere 0 1 := by
  rw [diskHomeo, coe_closedBallHomeomorphOfFinrankEq_apply, mem_sphere_zero_iff_norm,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff, ← mem_sphere_zero_iff_norm]

private theorem image_faceMap_ball (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    σ.faceMap hmap hlf '' ball 0 1 = ofQuotient '' (π '' interior P.carrier) := by
  obtain ⟨-, hball, -, hsphere_inr, -⟩ := P.exists_equiv_closedBall.choose_spec
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    let xc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨x, ball_subset_closedBall hx⟩
    rw [σ.faceMap_of_mem hmap hlf xc]
    have hcb : (diskHomeo xc : ℂ) ∈ ball (0 : ℂ) 1 := (diskHomeo_mem_ball_iff xc).2 hx
    rcases he : faceEquiv P xc with z | i
    · have hez : diskEquiv P (.inl z) = diskHomeo xc := by
        simpa [faceEquiv] using congrArg (diskEquiv P) he.symm
      have hb : (diskEquiv P (.inl z) : ℂ) ∈ ball (0 : ℂ) 1 := hez.symm ▸ hcb
      exact ⟨π z, ⟨z, (hball z).1 hb, rfl⟩, rfl⟩
    · have hei : diskEquiv P (.inr i) = diskHomeo xc := by
        simpa [faceEquiv] using congrArg (diskEquiv P) he.symm
      have hs : (diskEquiv P (.inr i) : ℂ) ∈ sphere (0 : ℂ) 1 := hsphere_inr i
      rw [hei, mem_sphere_zero_iff_norm] at hs
      rw [mem_ball_zero_iff, hs] at hcb
      exact (lt_irrefl _ hcb).elim
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    let zp : P.carrier := ⟨z, interior_subset hz⟩
    let u := diskHomeo.symm (diskEquiv P (.inl zp))
    have hub : (u : Fin 2 → ℝ) ∈ ball 0 1 := by
      rw [← diskHomeo_mem_ball_iff u, Homeomorph.apply_symm_apply]
      exact (hball zp).2 hz
    refine ⟨u, hub, ?_⟩
    rw [σ.faceMap_of_mem hmap hlf u]
    have hfe : faceEquiv P u = .inl zp := by simp [faceEquiv, u]
    rw [hfe, facePoint]

private theorem image_faceMap_closedBall_superset (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    ofQuotient '' (π '' P.carrier) ⊆ σ.faceMap hmap hlf '' closedBall 0 1 := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  let zp : P.carrier := ⟨z, hz⟩
  let u := diskHomeo.symm (diskEquiv P (.inl zp))
  refine ⟨u, u.2, ?_⟩
  rw [σ.faceMap_of_mem hmap hlf u]
  have hfe : faceEquiv P u = .inl zp := by simp [faceEquiv, u]
  rw [hfe, facePoint]

private theorem injOn_faceMap (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    InjOn (σ.faceMap hmap hlf) (ball 0 1) := by
  obtain ⟨-, hball, -, hsphere_inr, -⟩ := P.exists_equiv_closedBall.choose_spec
  intro x hx y hy h
  let xc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨x, ball_subset_closedBall hx⟩
  let yc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨y, ball_subset_closedBall hy⟩
  rw [σ.faceMap_of_mem hmap hlf xc, σ.faceMap_of_mem hmap hlf yc] at h
  have hxc_b := (diskHomeo_mem_ball_iff xc).2 hx
  have hyc_b := (diskHomeo_mem_ball_iff yc).2 hy
  have hnot_inr (w : closedBall (0 : Fin 2 → ℝ) 1)
      (hwb : (diskHomeo w : ℂ) ∈ ball (0 : ℂ) 1)
      (i : {k : Fin n // (P.vertex k).isRight}) (hw : faceEquiv P w = .inr i) : False := by
    have hei : diskEquiv P (.inr i) = diskHomeo w := by
      simpa [faceEquiv] using congrArg (diskEquiv P) hw.symm
    have hs : (diskEquiv P (.inr i) : ℂ) ∈ sphere (0 : ℂ) 1 := hsphere_inr i
    rw [hei, mem_sphere_zero_iff_norm] at hs
    rw [mem_ball_zero_iff, hs] at hwb
    exact lt_irrefl _ hwb
  rcases hex : faceEquiv P xc with zx | ix
  · rcases hey : faceEquiv P yc with zy | iy
    · rw [hex, hey, facePoint, facePoint] at h
      have hzx_eq : diskEquiv P (.inl zx) = diskHomeo xc := by
        simpa [faceEquiv] using congrArg (diskEquiv P) hex.symm
      have hb : (diskEquiv P (.inl zx) : ℂ) ∈ ball (0 : ℂ) 1 := hzx_eq.symm ▸ hxc_b
      have hzx_int : (zx : ℍ) ∈ interior P.carrier := (hball zx).1 hb
      have hz_eq := eq_of_mk_eq_of_mem_interior hdisj hzx_int zy.2
        (ofQuotient_injective h).symm
      have hfe_eq : faceEquiv P xc = faceEquiv P yc := by
        rw [hex, hey, Subtype.ext hz_eq.symm]
      exact congrArg Subtype.val ((faceEquiv P).injective hfe_eq)
    · exact (hnot_inr yc hyc_b iy hey).elim
  · exact (hnot_inr xc hxc_b ix hex).elim

private theorem faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    {x : Fin 2 → ℝ} (hx : x ∈ sphere 0 1) :
    σ.faceMap hmap hlf x ∈ σ.zeroCells Γ ∨
      ∃ i : σ.SideRepresentative, σ.faceMap hmap hlf x ∈ σ.edgeMap hmap hlf i '' ball 0 1 := by
  obtain ⟨-, -, hsphere_inl, -, -⟩ := P.exists_equiv_closedBall.choose_spec
  let xc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨x, sphere_subset_closedBall hx⟩
  rw [σ.faceMap_of_mem hmap hlf xc]
  rcases he : faceEquiv P xc with z | i
  · have hcs : (diskHomeo xc : ℂ) ∈ sphere (0 : ℂ) 1 := (diskHomeo_mem_sphere_iff xc).2 hx
    have hez : diskEquiv P (.inl z) = diskHomeo xc := by
      simpa [faceEquiv] using congrArg (diskEquiv P) he.symm
    have hs : (diskEquiv P (.inl z) : ℂ) ∈ sphere (0 : ℂ) 1 := hez.symm ▸ hcs
    obtain ⟨j, hj⟩ := (hsphere_inl z).1 hs
    exact σ.mem_zeroCells_or_exists_edgeMap_of_mem_side hmap hlf hj
  · exact Or.inl (σ.vertexZeroCell_mem_zeroCells hmap hlf i.1)

private theorem continuousAt_facePoint_faceEquiv_of_eq_inl [DiscreteTopology Γ]
    (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    {x₀ : closedBall (0 : Fin 2 → ℝ) 1} {z₀ : P.carrier} (hx₀ : faceEquiv P x₀ = .inl z₀) :
    ContinuousAt (fun x ↦ σ.facePoint hmap hlf (faceEquiv P x)) x₀ := by
  obtain ⟨hopen, -, -, -, -⟩ := P.exists_equiv_closedBall.choose_spec
  let emb : P.carrier → closedBall (0 : Fin 2 → ℝ) 1 :=
    fun z ↦ diskHomeo.symm (diskEquiv P (.inl z))
  have hemb : IsOpenEmbedding emb := diskHomeo.symm.isOpenEmbedding.comp hopen
  have hx₀_emb : emb z₀ = x₀ := by
    apply diskHomeo.injective
    have h1 : diskEquiv P (.inl z₀) = diskHomeo x₀ := by
      simpa [faceEquiv] using congrArg (diskEquiv P) hx₀.symm
    simp [emb, h1]
  rw [ContinuousAt, ← hx₀_emb, ← hemb.isOpenMap.map_nhds_eq hemb.continuous.continuousAt,
    Filter.tendsto_map'_iff]
  have hcomp : (fun x ↦ σ.facePoint hmap hlf (faceEquiv P x)) ∘ emb =
      fun z : P.carrier ↦ ofQuotient (π (z : ℍ)) := by
    ext z
    have hfe : faceEquiv P (emb z) = .inl z := by simp [faceEquiv, emb]
    simp [Function.comp_apply, hfe, facePoint]
  have hval : σ.facePoint hmap hlf (faceEquiv P (emb z₀)) = ofQuotient (π (z₀ : ℍ)) :=
    congrFun hcomp z₀
  rw [hcomp, hval]
  exact (continuous_ofQuotient.comp
    (continuous_quotient_mk'.comp continuous_subtype_val)).tendsto z₀

private theorem continuousAt_facePoint_faceEquiv_of_eq_inr [DiscreteTopology Γ]
    (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    {x₀ : closedBall (0 : Fin 2 → ℝ) 1} {i : {k : Fin n // (P.vertex k).isRight}}
    (hx₀ : faceEquiv P x₀ = .inr i) :
    ContinuousAt (fun x ↦ σ.facePoint hmap hlf (faceEquiv P x)) x₀ := by
  obtain ⟨-, -, -, -, hhoro⟩ := P.exists_equiv_closedBall.choose_spec
  obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 i.2
  have hcusp := σ.isCuspPoint_of_vertex_eq_inr hξ (σ.cycleMap_mem hmap _) hlf
  obtain ⟨D, hD⟩ := hcusp.exists_cuspDatum_cusp_eq
  have hcell : σ.vertexZeroCell hmap hlf i.1 = ofCusp D.cuspOrbit := by
    rw [σ.vertexZeroCell_of_eq_inr hmap hlf hξ hcusp]
    exact congrArg ofCusp (Subtype.ext (by simp [hD]))
  rw [ContinuousAt, hx₀, facePoint, hcell]
  refine (nhds_basis_cuspNhd D 0).tendsto_right_iff.2 fun A _ ↦ ?_
  have hgξ : D.scaling • ξ = ∞ := by rw [← hD, D.scaling_smul_cusp]
  have hx₀_eq : diskHomeo x₀ = diskEquiv P (.inr i) := by
    simpa [faceEquiv] using congrArg (diskEquiv P) hx₀
  have hpull : Filter.Tendsto diskHomeo (𝓝 x₀) (𝓝 (diskEquiv P (.inr i))) :=
    hx₀_eq ▸ diskHomeo.continuous.tendsto x₀
  filter_upwards [hpull.eventually (hhoro i hξ hgξ A)] with x hx
  rcases hx with heq | ⟨z, hz, hAz⟩
  · have hfe : faceEquiv P x = .inr i := by simp [faceEquiv, diskEquiv, heq]
    rw [hfe, facePoint, hcell]
    exact ofCusp_mem_cuspNhd D A
  · have hfe : faceEquiv P x = .inl z := by simp [faceEquiv, diskEquiv, ← hz]
    rw [hfe, facePoint]
    exact (ofQuotient_mem_cuspNhd_iff D A).mpr ⟨z, (mem_horodisc D).2 hAz, rfl⟩

private theorem continuousOn_faceMap [DiscreteTopology Γ] (hmap : ∀ k, σ.map k ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    ContinuousOn (σ.faceMap hmap hlf) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hrestr : (closedBall (0 : Fin 2 → ℝ) 1).domRestrict (σ.faceMap hmap hlf) =
      fun x : closedBall (0 : Fin 2 → ℝ) 1 ↦ σ.facePoint hmap hlf (faceEquiv P x) := by
    ext x
    exact σ.faceMap_of_mem hmap hlf x
  rw [hrestr, continuous_iff_continuousAt]
  intro x₀
  rcases hx₀ : faceEquiv P x₀ with z₀ | i
  · exact σ.continuousAt_facePoint_faceEquiv_of_eq_inl hmap hlf hx₀
  · exact σ.continuousAt_facePoint_faceEquiv_of_eq_inr hmap hlf hx₀

end TwoCell

/-! ### Assembling the finite CW structure -/

section CWStructure

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}
  (hmap : ∀ i, σ.map i ∈ Γ)
  (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
  (hdisj : ∀ γ : Γ, γ ≠ 1 → Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

variable (Γ) in
private abbrev Cell : ℕ → Type
  | 0 => σ.zeroCells Γ
  | 1 => σ.SideRepresentative
  | 2 => PUnit
  | _ + 3 => PEmpty

private def cellMap : (m : ℕ) → σ.Cell Γ m → PartialEquiv (Fin m → ℝ) Γ.CompactifiedQuotient
  | 0, q => .single 0 q.1
  | 1, i => InjOn.toPartialEquiv _ _ (σ.injOn_edgeMap hmap hlf hdisj i)
  | 2, _ => InjOn.toPartialEquiv _ _ (σ.injOn_faceMap hmap hlf hdisj)
  | _ + 3, i => PEmpty.elim i

private theorem image_cellMap_zero (q : σ.Cell Γ 0) {s : Set (Fin 0 → ℝ)} (hs : s.Nonempty) :
    σ.cellMap hmap hlf hdisj 0 q '' s = {q.1} :=
  hs.image_const _

private theorem coe_cellMap_one (i : σ.Cell Γ 1) :
    ⇑(σ.cellMap hmap hlf hdisj 1 i) = σ.edgeMap hmap hlf i := rfl

private theorem coe_cellMap_two (i : σ.Cell Γ 2) :
    ⇑(σ.cellMap hmap hlf hdisj 2 i) = σ.faceMap hmap hlf := rfl

include hdisj in
private theorem zeroCell_notMem_image_faceMap_ball {q : Γ.CompactifiedQuotient}
    (hq : q ∈ σ.zeroCells Γ) : q ∉ σ.faceMap hmap hlf '' ball 0 1 := by
  rw [σ.image_faceMap_ball hmap hlf]
  rcases hq with (⟨j, rfl⟩ | ⟨i, rfl⟩) | ⟨C, rfl⟩
  · rintro ⟨_, hmem, heq⟩
    exact mk_notMem_image_interior hdisj
      (P.mem_side_of_vertex_eq_inl (Sum.inl_getLeft _ j.2).symm)
      (ofQuotient_injective heq ▸ hmem)
  · rintro ⟨_, hmem, heq⟩
    exact mk_notMem_image_interior hdisj (σ.selfPairedSideFixedPoint_spec i).1
      (ofQuotient_injective heq ▸ hmem)
  · rintro ⟨_, -, heq⟩
    cases heq

private theorem pairwiseDisjoint_cellMap :
    (univ : Set (Σ m, σ.Cell Γ m)).PairwiseDisjoint
      fun c ↦ σ.cellMap hmap hlf hdisj c.1 c.2 '' ball 0 1 := by
  have hb (m : ℕ) : (ball (0 : Fin m → ℝ) 1).Nonempty := ⟨0, mem_ball_self one_pos⟩
  have h01 (q : σ.Cell Γ 0) (i : σ.Cell Γ 1) :
      Disjoint (σ.cellMap hmap hlf hdisj 0 q '' ball 0 1)
        (σ.cellMap hmap hlf hdisj 1 i '' ball 0 1) := by
    rw [image_cellMap_zero _ _ _ _ _ (hb 0), coe_cellMap_one, σ.image_edgeMap_ball,
      disjoint_singleton_left]
    rintro ⟨u, hu, h⟩
    dsimp only at h
    exact σ.ofQuotient_mk_edgeArc_notMem_zeroCells hmap hdisj hu (h ▸ q.2)
  have h02 (q : σ.Cell Γ 0) (i : σ.Cell Γ 2) :
      Disjoint (σ.cellMap hmap hlf hdisj 0 q '' ball 0 1)
        (σ.cellMap hmap hlf hdisj 2 i '' ball 0 1) := by
    rw [image_cellMap_zero _ _ _ _ _ (hb 0), coe_cellMap_two, disjoint_singleton_left]
    exact σ.zeroCell_notMem_image_faceMap_ball hmap hlf hdisj q.2
  have h12 (i : σ.Cell Γ 1) (k : σ.Cell Γ 2) :
      Disjoint (σ.cellMap hmap hlf hdisj 1 i '' ball 0 1)
        (σ.cellMap hmap hlf hdisj 2 k '' ball 0 1) := by
    rw [coe_cellMap_one, coe_cellMap_two, σ.image_edgeMap_ball, σ.image_faceMap_ball,
      disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨_, hmem, heq⟩
    exact mk_notMem_image_interior hdisj (σ.edgeArc_mem_side i.1 hu)
      (ofQuotient_injective heq ▸ hmem)
  rintro ⟨m, c⟩ - ⟨m', c'⟩ - hne
  match m, c, m', c' with
  | 0, q, 0, q' =>
    rw [Function.onFun, image_cellMap_zero _ _ _ _ _ (hb 0),
      image_cellMap_zero _ _ _ _ _ (hb 0), disjoint_singleton]
    exact fun h ↦ hne (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  | 0, q, 1, i => exact h01 q i
  | 1, i, 0, q => exact (h01 q i).symm
  | 0, q, 2, i => exact h02 q i
  | 2, i, 0, q => exact (h02 q i).symm
  | 1, i, 2, k => exact h12 i k
  | 2, k, 1, i => exact (h12 i k).symm
  | 1, i, 1, j =>
    rw [Function.onFun, coe_cellMap_one, coe_cellMap_one]
    exact σ.disjoint_image_edgeMap_ball hmap hlf hdisj fun h ↦ hne (Sigma.ext rfl (heq_of_eq h))
  | 2, ⟨⟩, 2, ⟨⟩ => exact absurd rfl hne
  | _ + 3, i, _, _ | _, _, _ + 3, i => exact PEmpty.elim i

private theorem mapsTo_cellMap :
    ∀ (m : ℕ) (c : σ.Cell Γ m), MapsTo (σ.cellMap hmap hlf hdisj m c) (sphere 0 1)
      (⋃ (k < m) (c' : σ.Cell Γ k), σ.cellMap hmap hlf hdisj k c' '' closedBall 0 1)
  | 0, _ => fun _ hx ↦ ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim
  | 1, i => fun x hx ↦ by
    refine mem_iUnion₂.2 ⟨0, zero_lt_one,
      mem_iUnion.2 ⟨⟨_, σ.edgeMap_mem_zeroCells hmap hlf i hx⟩, ?_⟩⟩
    rw [image_cellMap_zero _ _ _ _ _ ⟨0, mem_closedBall_self zero_le_one⟩]
    rfl
  | 2, _ => fun x hx ↦ by
    rcases σ.faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere hmap hlf hx with hz0 | ⟨i, hi⟩
    · refine mem_iUnion₂.2 ⟨0, zero_lt_two, mem_iUnion.2 ⟨⟨_, hz0⟩, ?_⟩⟩
      rw [image_cellMap_zero _ _ _ _ _ ⟨0, mem_closedBall_self zero_le_one⟩]
      rfl
    · refine mem_iUnion₂.2 ⟨1, one_lt_two, mem_iUnion.2 ⟨i, ?_⟩⟩
      rw [coe_cellMap_one]
      exact image_mono ball_subset_closedBall hi
  | _ + 3, i => PEmpty.elim i

private theorem iUnion_image_cellMap :
    ⋃ (m : ℕ) (c : σ.Cell Γ m), σ.cellMap hmap hlf hdisj m c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  cases p with
  | ofCusp C =>
    have hC : ofCusp C ∈ σ.zeroCells Γ := Or.inr ⟨C, rfl⟩
    refine mem_iUnion₂.2 ⟨0, ⟨ofCusp C, hC⟩, ?_⟩
    rw [image_cellMap_zero _ _ _ _ _ ⟨0, mem_closedBall_self zero_le_one⟩]
    rfl
  | ofQuotient q =>
    obtain ⟨w, rfl⟩ := Quotient.mk''_surjective q
    obtain ⟨γ, z, hz, rfl⟩ :=
      mem_iUnion.1 ((σ.iUnion_smul_carrier_eq_univ hmap hlf).symm ▸ mem_univ w)
    refine mem_iUnion₂.2 ⟨2, ⟨⟩, ?_⟩
    rw [coe_cellMap_two]
    exact σ.image_faceMap_closedBall_superset hmap hlf
      ⟨π z, ⟨z, hz, rfl⟩, congrArg ofQuotient (Quotient.sound (mem_orbit z γ)).symm⟩

section Discrete

variable [DiscreteTopology Γ]

private theorem continuousOn_cellMap_symm :
    ∀ (m : ℕ) (c : σ.Cell Γ m),
      ContinuousOn (σ.cellMap hmap hlf hdisj m c).symm (σ.cellMap hmap hlf hdisj m c).target
  | 0, _ => continuousOn_const
  | 1, i => by
    refine (σ.continuousOn_edgeMap hmap hlf i).continuousOn_invFunOn_image_of_isCompact
      (isCompact_closedBall 0 1) ball_subset_closedBall (σ.injOn_edgeMap hmap hlf hdisj i) ?_
    rw [closedBall_sdiff_ball, σ.image_edgeMap_ball, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨u, hu, h⟩
    dsimp only at h
    exact σ.ofQuotient_mk_edgeArc_notMem_zeroCells hmap hdisj hu
      (h ▸ σ.edgeMap_mem_zeroCells hmap hlf i hx)
  | 2, _ => by
    refine (σ.continuousOn_faceMap hmap hlf).continuousOn_invFunOn_image_of_isCompact
      (isCompact_closedBall 0 1) ball_subset_closedBall (σ.injOn_faceMap hmap hlf hdisj) ?_
    rw [closedBall_sdiff_ball, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hmem
    rcases σ.faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere hmap hlf hx with hz0 | ⟨i, hi⟩
    · exact σ.zeroCell_notMem_image_faceMap_ball hmap hlf hdisj hz0 hmem
    · rw [σ.image_edgeMap_ball] at hi
      obtain ⟨u, hu, hu_eq⟩ := hi
      dsimp only at hu_eq
      rw [← hu_eq, σ.image_faceMap_ball] at hmem
      obtain ⟨_, hint, heq⟩ := hmem
      exact mk_notMem_image_interior hdisj (σ.edgeArc_mem_side i.1 hu)
        (ofQuotient_injective heq ▸ hint)
  | _ + 3, i => PEmpty.elim i

@[instance_reducible]
private def cwComplex : CWComplex (univ : Set Γ.CompactifiedQuotient) :=
  CWComplex.mkFinite univ (σ.Cell Γ) (σ.cellMap hmap hlf hdisj)
    (Filter.eventually_atTop.2 ⟨3, fun m hm ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
      exact inferInstanceAs (IsEmpty PEmpty)⟩)
    (fun
      | 0 => (σ.finite_zeroCells hmap hlf).to_subtype
      | 1 => inferInstanceAs (Finite σ.SideRepresentative)
      | 2 => inferInstanceAs (Finite PUnit)
      | _ + 3 => inferInstanceAs (Finite PEmpty))
    (fun
      | 0, _ => by ext x; simp [cellMap, Subsingleton.elim x 0]
      | 1, _ => rfl
      | 2, _ => rfl
      | _ + 3, i => PEmpty.elim i)
    (fun
      | 0, _ => continuousOn_const
      | 1, i => σ.continuousOn_edgeMap hmap hlf i
      | 2, _ => σ.continuousOn_faceMap hmap hlf
      | _ + 3, i => PEmpty.elim i)
    (σ.continuousOn_cellMap_symm hmap hlf hdisj)
    (σ.pairwiseDisjoint_cellMap hmap hlf hdisj)
    (σ.mapsTo_cellMap hmap hlf hdisj)
    (σ.iUnion_image_cellMap hmap hlf hdisj)

private theorem finite_cwComplex :
    letI := σ.cwComplex hmap hlf hdisj
    RelCWComplex.Finite (univ : Set Γ.CompactifiedQuotient) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

private theorem cwEulerChar_cwComplex :
    letI := σ.cwComplex hmap hlf hdisj
    cwEulerChar (univ : Set Γ.CompactifiedQuotient) =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1 := by
  let := σ.cwComplex hmap hlf hdisj
  have hcell (m : ℕ) : cell (univ : Set Γ.CompactifiedQuotient) m = σ.Cell Γ m := rfl
  rw [cwEulerChar_eq_sum_range (C := (univ : Set Γ.CompactifiedQuotient)) (N := 3) fun m hm ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [hcell]
    exact inferInstanceAs (IsEmpty PEmpty)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hcell, Cell, Nat.card_unique,
    σ.natCard_zeroCells hmap hlf hdisj]
  push_cast
  ring

/-! ### Finite CW type, Euler characteristic, genus, and signature area formula -/

include hmap hlf hdisj in
/-- **The compactified quotient by a fundamental polygon has finite CW type.** Let `σ` pair the
sides of a convex hyperbolic `n`-gon `P`, and let a discrete group `Γ ≤ PSL(2, ℝ)` contain the
side-pairing maps, with locally finite translates of `P` whose interiors are pairwise disjoint.
Then `Γ.CompactifiedQuotient` is homeomorphic to a finite CW complex with `0`-cells at the finite
vertex cycles, cusp orbits, and self-paired side fixed points, one `1`-cell for each pair of sides,
and one `2`-cell. -/
theorem finiteCWType_compactifiedQuotient : FiniteCWType Γ.CompactifiedQuotient := by
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  exact (Homeomorph.Set.univ _).symm.finiteCWType

/-- **The Euler characteristic of the compactified quotient by a fundamental polygon.** Under the
hypotheses of `finiteCWType_compactifiedQuotient`, `χ(X(Γ)) = V + c + k - E + 1`, where `V` is the
number of finite vertex cycles, `c` the number of ideal vertex cycles (cusp orbits), `k` the number
of self-paired sides, and `E = (n + k) / 2` the number of side pairs. -/
theorem eulerChar_compactifiedQuotient :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1 := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ _).symm.toHomotopyEquiv,
    σ.cwEulerChar_cwComplex hmap hlf hdisj]

/-- The finite-CW Euler characteristic of `Γ.CompactifiedQuotient` equals the combinatorial Euler
characteristic of `σ.toPermutationTriple`. -/
theorem eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient = σ.toPermutationTriple.eulerChar := by
  rw [σ.eulerChar_compactifiedQuotient hmap hlf hdisj, σ.eulerChar_toPermutationTriple]

/-- **The genus bridge for a cuspidal fundamental polygon.** The Euler characteristic of
`Γ.CompactifiedQuotient` satisfies `χ(X(Γ)) = 2 - 2 · genus X(Γ)` without truncation: it equals
the Euler characteristic of the connected combinatorial surface `σ.toPermutationTriple`, which is
even and at most `2`. -/
theorem eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient = 2 - 2 * RiemannSurface.genus Γ.CompactifiedQuotient := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  rw [RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff,
    σ.eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple hmap hlf hdisj]
  exact ⟨σ.isConnected_toPermutationTriple.eulerChar_le_two, σ.toPermutationTriple.even_eulerChar⟩

/-- **The topological genus of `Γ.CompactifiedQuotient` read off a fundamental polygon.** It equals
the genus of the ribbon surface `σ.toPermutationTriple`. -/
theorem genus_compactifiedQuotient_eq :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    RiemannSurface.genus Γ.CompactifiedQuotient = σ.toPermutationTriple.genus := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  apply RiemannSurface.genus_eq_of_eulerChar_eq
  rw [σ.eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple hmap hlf hdisj,
    ← σ.isConnected_toPermutationTriple.two_sub_two_mul_genus]

/-- **The orbifold area formula through the Euler characteristic.** Under the hypotheses of
`finiteCWType_compactifiedQuotient`, the covolume of `Γ` is
`2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ) + c)`, where `e` runs over the elliptic orbits of `Γ` with
stabilizer orders `mₑ` and `c` is the number of cusp orbits. -/
theorem covolume_eq_two_pi_mul_neg_eulerChar_add_cusps :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi * (-(eulerChar Γ.CompactifiedQuotient : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
        Nat.card Γ.CuspOrbit)) := by
  rw [σ.covolume_eq_two_pi_mul hmap hlf hdisj, σ.eulerChar_compactifiedQuotient hmap hlf hdisj,
    σ.natCard_cuspOrbit hmap hlf hdisj]
  have hE : (2 * Nat.card σ.SideRepresentative : ℝ) = n + Nat.card {i : Fin n // σ.pair i = i} := by
    exact_mod_cast σ.two_mul_natCard_sideRepresentative
  congr 2
  push_cast
  linarith

/-- **The signature area formula for a fundamental polygon.** Under the hypotheses of
`finiteCWType_compactifiedQuotient`, the covolume of `Γ` is
`2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + c)`, where `g = genus X(Γ)` is the topological genus of the
compactified quotient, `e` runs over the elliptic orbits of `Γ` with stabilizer orders `mₑ`, and
`c` is the number of cusp orbits. -/
theorem covolume_eq_two_pi_mul_signature :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi *
      (2 * (RiemannSurface.genus Γ.CompactifiedQuotient : ℝ) - 2 +
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
          Nat.card Γ.CuspOrbit)) := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  rw [σ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps hmap hlf hdisj,
    σ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus hmap hlf hdisj]
  congr 2
  push_cast
  ring

end Discrete

end CWStructure

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

end
