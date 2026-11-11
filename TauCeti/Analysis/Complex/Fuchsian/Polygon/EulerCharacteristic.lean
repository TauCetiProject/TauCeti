/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Analysis.Complex.Fuchsian.Polygon.Area
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Disk
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Identification
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Side.Presentation
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.MetricSpace.Pseudo.Pi
import TauCeti.Topology.Separation.InvFunOn

/-!
# The Euler characteristic of the quotient by a compact fundamental polygon

Let `σ` pair the sides of a compact convex hyperbolic `n`-gon `P`, and let `Γ ≤ PSL(2, ℝ)`
contain the side-pairing maps, with locally finite translates of `P` whose interiors are pairwise
disjoint. The coarse quotient `Γ \ ℍ` is then a finite CW complex whose cells are read off the
polygon:

* one `0`-cell for each vertex cycle, and one for the fixed point of each self-paired side;
* one `1`-cell for each pair of sides: the image of the side for a side paired with another one,
  and the image of the half of the side from its first vertex to its fixed point for a
  self-paired side, which is folded onto itself by its pairing map;
* one `2`-cell, the image of `P`, whose interior maps injectively to `Γ \ ℍ`.

The characteristic maps are the orbit projection composed with unit-speed parametrizations of the
sides and with a homeomorphism from the closed unit disk onto `P`
(`TauCeti.UpperHalfPlane.CompactConvexPolygon.exists_homeomorph_closedBall`). That the open cells
are disjoint, and that the characteristic maps are injective on them, is the description of
the `Γ`-equivalent points of `P`
(`TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.mem_orbit_iff_of_mem_carrier`).

Consequently `Γ \ ℍ` has finite CW type, and with `V` vertex cycles, `k` self-paired sides and
`(n + k) / 2` side pairs its Euler characteristic is `χ(Γ \ ℍ) = V + k - (n + k) / 2 + 1`.
Combined with the orbifold area formula for a fundamental polygon, this identifies the polygon
count there with the Euler characteristic: the covolume of `Γ` is
`2π (-χ(Γ \ ℍ) + ∑ₑ (1 - 1 / mₑ))`, the sum running over the elliptic orbits with stabilizer
orders `mₑ`. Writing `χ = 2 - 2g` for the topological genus `g` of the compact surface `Γ \ ℍ`,
this is the signature form `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ))` of the area of a cocompact Fuchsian
group.

## Main results

* `ConvexPolygon.SidePairing.finiteCWType_orbitRel_quotient`: `Γ \ ℍ` has finite CW type.
* `ConvexPolygon.SidePairing.eulerChar_orbitRel_quotient`: `χ(Γ \ ℍ)` is the number of vertex
  cycles plus the number of self-paired sides, minus the number of side pairs, plus one.
* `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_neg_eulerChar_add`: the area formula
  `covolume Γ = 2π (-χ(Γ \ ℍ) + ∑ₑ (1 - 1 / mₑ))`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §§9.2–9.3 and 10.4 (the quotient of a fundamental polygon and its genus).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.3 (the cell decomposition of the quotient by a fundamental region and the
  signature of a cocompact group).
-/

public section

noncomputable section

open MeasureTheory Metric MulAction Set Topology Topology.RelCWComplex UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : CompactConvexPolygon n}

/-! ### Unit-speed parametrizations of the sides -/

/-- The unit-speed parametrization of side `i`, starting at `vertex i` at time `0`. -/
private def sideLine (P : CompactConvexPolygon n) (i : Fin n) : ℝ → ℍ :=
  geodesicLine (geodesicBetween (P.vertex i) (P.vertex (i + 1)))

/-- The length of side `i`. -/
private def sideLength (P : CompactConvexPolygon n) (i : Fin n) : ℝ :=
  dist (P.vertex i) (P.vertex (i + 1))

private theorem sideLine_zero (i : Fin n) : sideLine P i 0 = P.vertex i :=
  geodesicLine_geodesicBetween_zero _ _

private theorem sideLine_sideLength (i : Fin n) :
    sideLine P i (sideLength P i) = P.vertex (i + 1) :=
  geodesicLine_geodesicBetween_dist _ _

private theorem sideLine_injective (i : Fin n) : Function.Injective (sideLine P i) :=
  geodesicLine_injective _

private theorem continuous_sideLine (i : Fin n) : Continuous (sideLine P i) :=
  (isometry_geodesicLine _).continuous

private theorem sideLength_pos (i : Fin n) : 0 < sideLength P i :=
  dist_pos.2 (P.vertex_ne_vertex_add_one i)

private theorem side_eq_image_sideLine (i : Fin n) :
    P.toConvexPolygon.side i = sideLine P i '' Icc 0 (sideLength P i) := by
  rw [P.side_toConvexPolygon, CompactConvexPolygon.side_def, geodesicSegment_def]
  rfl

private theorem sideLine_mem_side {i : Fin n} {t : ℝ} (ht : t ∈ Icc 0 (sideLength P i)) :
    sideLine P i t ∈ P.toConvexPolygon.side i := by
  rw [side_eq_image_sideLine]
  exact mem_image_of_mem _ ht

private theorem sideLine_mem_carrier {i : Fin n} {t : ℝ} (ht : t ∈ Icc 0 (sideLength P i)) :
    sideLine P i t ∈ P.toConvexPolygon.carrier :=
  P.toConvexPolygon.side_subset_carrier i (sideLine_mem_side ht)

/-- A point strictly inside a side is not a vertex. -/
private theorem vertex_ne_sideLine {i : Fin n} {t : ℝ} (ht : t ∈ Ioo 0 (sideLength P i))
    (j : Fin n) : P.toConvexPolygon.vertex j ≠ .inl (sideLine P i t) := by
  intro h
  rcases P.toConvexPolygon.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side h
      (sideLine_mem_side (Ioo_subset_Icc_self ht)) with rfl | rfl
  · rw [P.vertex_toConvexPolygon, Sum.inl.injEq, ← sideLine_zero] at h
    exact ht.1.ne (sideLine_injective j h)
  · rw [P.vertex_toConvexPolygon, Sum.inl.injEq, ← sideLine_sideLength] at h
    exact ht.2.ne' (sideLine_injective _ h)

/-- The map pairing a side with itself reverses it. -/
private theorem map_smul_sideLine_of_pair_eq (σ : P.toConvexPolygon.SidePairing) {i : Fin n}
    (hi : σ.pair i = i) (t : ℝ) :
    σ.map i • sideLine P i t = sideLine P i (sideLength P i - t) := by
  have h₁ : σ.map i • P.vertex i = P.vertex (i + 1) := by
    simpa [hi] using σ.map_smul_vertex i
  have h₂ : σ.map i • P.vertex (i + 1) = P.vertex i := by
    simpa [hi] using σ.map_smul_vertex_add_one i
  have hne := P.vertex_ne_vertex_add_one i
  simp only [sideLine, sideLength]
  rw [smul_geodesicLine, ← geodesicBetween_smul _ hne, h₁, h₂, geodesicBetween_swap hne,
    geodesicLine_mul_pslS, geodesicLine_mul_dilation, sub_eq_add_neg]

/-! ### Equivalent points of the polygon -/

variable (σ : P.toConvexPolygon.SidePairing) {Γ : Subgroup PSL(2, ℝ)}
  (hmap : ∀ i, σ.map i ∈ Γ)
  (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.toConvexPolygon.carrier)
  (hdisj : ∀ γ : Γ, γ ≠ 1 →
    Disjoint ((γ : PSL(2, ℝ)) • interior P.toConvexPolygon.carrier)
      (interior P.toConvexPolygon.carrier))

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

/-- The length of the edge carried by side `i` in the cell structure of the quotient: the whole
side, or its half up to the fixed point of the pairing map for a self-paired side. -/
private def edgeLength (i : Fin n) : ℝ :=
  if σ.pair i = i then sideLength P i / 2 else sideLength P i

private theorem edgeLength_of_pair_eq {i : Fin n} (hi : σ.pair i = i) :
    σ.edgeLength i = sideLength P i / 2 := by
  simp [edgeLength, hi]

private theorem edgeLength_pos (i : Fin n) : 0 < σ.edgeLength i := by
  have := sideLength_pos (P := P) i
  unfold edgeLength
  split_ifs <;> linarith

private theorem edgeLength_le (i : Fin n) : σ.edgeLength i ≤ sideLength P i := by
  have := sideLength_pos (P := P) i
  unfold edgeLength
  split_ifs <;> linarith

private theorem Ioo_edgeLength_subset (i : Fin n) :
    Ioo 0 (σ.edgeLength i) ⊆ Ioo 0 (sideLength P i) :=
  Ioo_subset_Ioo_right (σ.edgeLength_le i)

private theorem Icc_edgeLength_subset (i : Fin n) :
    Icc 0 (σ.edgeLength i) ⊆ Icc 0 (sideLength P i) :=
  Icc_subset_Icc_right (σ.edgeLength_le i)

include hmap hdisj in
/-- A point of `P` equivalent to a point strictly inside side `i` is that point or its image
under the pairing map of side `i`. -/
private theorem eq_or_eq_map_smul_of_mk_eq
    {i : Fin n} {t : ℝ} (ht : t ∈ Ioo 0 (sideLength P i)) {w : ℍ}
    (hw : w ∈ P.toConvexPolygon.carrier) (h : π w = π (sideLine P i t)) :
    w = sideLine P i t ∨ w = σ.map i • sideLine P i t := by
  rw [Quotient.eq'', orbitRel_apply] at h
  rcases (σ.mem_orbit_iff_of_mem_carrier hmap hdisj
      (sideLine_mem_carrier (Ioo_subset_Icc_self ht)) hw).1 h with
    h | ⟨j, hj, rfl⟩ | ⟨j, -, hj, -, -⟩
  · exact Or.inl h
  · obtain rfl := P.toConvexPolygon.eq_of_mem_side_of_mem_side
      (sideLine_mem_side (Ioo_subset_Icc_self ht)) (vertex_ne_sideLine ht i)
      (vertex_ne_sideLine ht (i + 1)) hj
    exact Or.inr rfl
  · exact absurd hj (vertex_ne_sideLine ht j)

include hmap hdisj in
/-- Two equivalent points strictly inside sides are equal, or are exchanged by a side pairing. -/
private theorem sideLine_eq_or_of_mk_eq
    {i j : Fin n} {s t : ℝ} (hs : s ∈ Ioo 0 (sideLength P i)) (ht : t ∈ Ioo 0 (sideLength P j))
    (h : π (sideLine P j t) = π (sideLine P i s)) :
    (j = i ∧ t = s) ∨ (j = σ.pair i ∧ sideLine P j t = σ.map i • sideLine P i s) := by
  have hjt := sideLine_mem_side (Ioo_subset_Icc_self ht)
  rcases σ.eq_or_eq_map_smul_of_mk_eq hmap hdisj hs
      (sideLine_mem_carrier (Ioo_subset_Icc_self ht)) h with h | h
  · obtain rfl := P.toConvexPolygon.eq_of_mem_side_of_mem_side hjt (vertex_ne_sideLine ht j)
      (vertex_ne_sideLine ht (j + 1)) (h ▸ sideLine_mem_side (Ioo_subset_Icc_self hs))
    exact Or.inl ⟨rfl, sideLine_injective j h⟩
  · refine Or.inr ⟨P.toConvexPolygon.eq_of_mem_side_of_mem_side hjt (vertex_ne_sideLine ht j)
      (vertex_ne_sideLine ht (j + 1)) ?_, h⟩
    exact h ▸ σ.map_smul_mem_side (sideLine_mem_side (Ioo_subset_Icc_self hs))

include hmap hdisj in
/-- A point of `P` equivalent to a vertex is a vertex. -/
private theorem exists_vertex_eq_of_mk_eq
    {j : Fin n} {w : ℍ} (hw : w ∈ P.toConvexPolygon.carrier) (h : π w = π (P.vertex j)) :
    ∃ k, w = P.vertex k := by
  rw [Quotient.eq'', orbitRel_apply] at h
  have hj : P.toConvexPolygon.vertex j = .inl (P.vertex j) := P.vertex_toConvexPolygon j
  rcases (σ.mem_orbit_iff_of_mem_carrier hmap hdisj
      (P.carrier_toConvexPolygon ▸ P.vertex_mem_carrier j) hw).1 h with
    h | ⟨k, hk, rfl⟩ | ⟨-, k, -, hk, -⟩
  · exact ⟨j, h⟩
  · rcases P.toConvexPolygon.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hj hk with rfl | rfl
    · exact ⟨σ.pair j + 1, by simpa using σ.map_smul_vertex j⟩
    · exact ⟨σ.pair k, by simpa using σ.map_smul_vertex_add_one k⟩
  · exact ⟨k, by simpa using hk.symm⟩

include hmap hdisj in
/-- A point of `P` equivalent to an interior point of `P` is that point. -/
private theorem eq_of_mk_eq_of_mem_interior
    {z w : ℍ} (hz : z ∈ interior P.toConvexPolygon.carrier) (hw : w ∈ P.toConvexPolygon.carrier)
    (h : π w = π z) : w = z := by
  rw [Quotient.eq'', orbitRel_apply] at h
  have hside {j : Fin n} (hj : z ∈ P.toConvexPolygon.side j) : False :=
    disjoint_left.1 disjoint_interior_frontier hz
      (P.toConvexPolygon.side_subset_frontier_carrier j hj)
  rcases (σ.mem_orbit_iff_of_mem_carrier hmap hdisj (interior_subset hz) hw).1 h with
    h | ⟨j, hj, -⟩ | ⟨j, -, hj, -, -⟩
  · exact h
  · exact (hside hj).elim
  · exact (hside (P.toConvexPolygon.mem_side_of_vertex_eq_inl hj)).elim

include hmap in
/-- Every point of a side is equivalent to a point of the edge of a side representative: the
whole side for a side paired with another one, and the half from its first vertex to its fixed
point for a self-paired side. -/
private theorem exists_mk_eq_of_mem_side {j : Fin n} {z : ℍ}
    (hz : z ∈ P.toConvexPolygon.side j) :
    ∃ i : σ.SideRepresentative, ∃ t ∈ Icc 0 (σ.edgeLength i), π (sideLine P i t) = π z := by
  have hmk (x : ℍ) (k : Fin n) : π (σ.map k • x) = π x :=
    Quotient.sound (mem_orbit x (⟨σ.map k, hmap k⟩ : Γ))
  by_cases hj : j ≤ σ.pair j
  · rw [side_eq_image_sideLine] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    by_cases hp : σ.pair j = j
    · rcases le_total u (sideLength P j / 2) with hle | hle
      · exact ⟨⟨j, hj⟩, u, by simpa [edgeLength, hp] using ⟨hu.1, hle⟩, rfl⟩
      · refine ⟨⟨j, hj⟩, sideLength P j - u, ?_, ?_⟩
        · simp only [edgeLength, hp, ↓reduceIte, mem_Icc]
          constructor <;> linarith [hu.2]
        · rw [← map_smul_sideLine_of_pair_eq σ hp, hmk]
    · exact ⟨⟨j, hj⟩, u, by simpa [edgeLength, hp] using hu, rfl⟩
  · have hle : σ.pair j ≤ σ.pair (σ.pair j) := by
      rw [σ.pair_pair]
      exact (lt_of_not_ge hj).le
    have hp : ¬ j = σ.pair j := fun h ↦ hj (h ▸ le_rfl)
    have hz' := σ.map_smul_mem_side hz
    rw [side_eq_image_sideLine] at hz'
    obtain ⟨u, hu, hu'⟩ := hz'
    exact ⟨⟨σ.pair j, hle⟩, u, by simpa [edgeLength, hp] using hu, by rw [hu', hmk]⟩

/-! ### The `0`-cells -/

variable (P Γ) in
/-- The orbits of the vertices of `P`. -/
private def vertexOrbits : Set (orbitRel.Quotient Γ ℍ) :=
  range fun j : Fin n ↦ π (P.vertex j)

variable (Γ) in
/-- The orbits of the fixed points of the self-paired sides. -/
private def midpointOrbits : Set (orbitRel.Quotient Γ ℍ) :=
  range fun i : {i : Fin n // σ.pair i = i} ↦ π (σ.selfPairedSideFixedPoint i)

variable (Γ) in
/-- The `0`-cells: the orbits of the vertices and of the fixed points of self-paired sides. -/
private def zeroCells : Set (orbitRel.Quotient Γ ℍ) :=
  vertexOrbits P Γ ∪ σ.midpointOrbits Γ

private theorem half_mem_Ioo (i : Fin n) : sideLength P i / 2 ∈ Ioo 0 (sideLength P i) := by
  have := sideLength_pos (P := P) i
  constructor <;> linarith

/-- The fixed point of a self-paired side is its midpoint. -/
private theorem selfPairedSideFixedPoint_eq_sideLine (i : {i : Fin n // σ.pair i = i}) :
    σ.selfPairedSideFixedPoint i = sideLine P i (sideLength P i / 2) :=
  σ.selfPairedSideFixedPoint_eq i (by rw [map_smul_sideLine_of_pair_eq σ i.2, sub_half])

include hmap hdisj in
/-- No point strictly inside an edge is a `0`-cell. -/
private theorem mk_sideLine_notMem_zeroCells {i : Fin n} {t : ℝ} (ht : t ∈ Ioo 0 (σ.edgeLength i)) :
    π (sideLine P i t) ∉ σ.zeroCells Γ := by
  have ht' := σ.Ioo_edgeLength_subset i ht
  rintro (⟨j, hj⟩ | ⟨⟨j, hjj⟩, hj⟩)
  · obtain ⟨k, hk⟩ := σ.exists_vertex_eq_of_mk_eq hmap hdisj
      (sideLine_mem_carrier (Ioo_subset_Icc_self ht')) hj.symm
    exact vertex_ne_sideLine ht' k (by rw [P.vertex_toConvexPolygon, hk])
  · dsimp only at hj
    rw [selfPairedSideFixedPoint_eq_sideLine] at hj
    rcases σ.sideLine_eq_or_of_mk_eq hmap hdisj ht' (half_mem_Ioo j) hj with
      ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rw [σ.edgeLength_of_pair_eq hjj] at ht
      exact ht.2.ne h.symm
    · have hi : σ.pair i = i := by rwa [σ.pair_pair, eq_comm] at hjj
      rw [hi, map_smul_sideLine_of_pair_eq σ hi] at h
      rw [σ.edgeLength_of_pair_eq hi] at ht
      linarith [sideLine_injective _ h, ht.2]

include hmap hdisj in
/-- No fixed point of a self-paired side is equivalent to a vertex. -/
private theorem disjoint_vertexOrbits_midpointOrbits :
    Disjoint (vertexOrbits P Γ) (σ.midpointOrbits Γ) := by
  rw [disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
  exact σ.quotientMk_vertex_ne_selfPairedSideFixedPoint hmap hdisj
    (P.vertex_toConvexPolygon j) i hi.symm

private theorem finite_zeroCells : (σ.zeroCells Γ).Finite :=
  (finite_range _).union (finite_range _)

include hmap hdisj in
/-- There is one `0`-cell for each vertex cycle and one for each self-paired side. -/
private theorem natCard_zeroCells :
    Nat.card (σ.zeroCells Γ) =
      Nat.card σ.FiniteVertexCycle + Nat.card {i : Fin n // σ.pair i = i} := by
  have hV : vertexOrbits P Γ = range fun j : {i : Fin n // (P.toConvexPolygon.vertex i).isLeft} ↦
      (Quotient.mk'' ((P.toConvexPolygon.vertex j).getLeft j.2) : orbitRel.Quotient Γ ℍ) := by
    ext q
    simp [vertexOrbits]
  rw [zeroCells, Nat.card_coe_set_eq, ncard_union_eq (σ.disjoint_vertexOrbits_midpointOrbits
      hmap hdisj) (finite_range _) (finite_range _), ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq, midpointOrbits, Nat.card_range_of_injective
      (σ.injective_quotientMk_selfPairedSideFixedPoint hmap hdisj), hV,
    Nat.card_congr (σ.finiteVertexCycleEquiv hmap hdisj)]

/-! ### The `1`-cells -/

/-- The affine parametrization of the edge interval `[0, edgeLength i]` by `[-1, 1]`. -/
private def edgeParam (i : Fin n) (x : Fin 1 → ℝ) : ℝ :=
  σ.edgeLength i * (x 0 + 1) / 2

private theorem continuous_edgeParam (i : Fin n) : Continuous (σ.edgeParam i) := by
  unfold edgeParam
  fun_prop

/-- `edgeParam` is evaluation at the only coordinate, followed by the affine map
`s ↦ edgeLength i / 2 * (s + 1)`. -/
private theorem edgeParam_eq_comp (i : Fin n) :
    σ.edgeParam i = (σ.edgeLength i / 2 * ·) ∘ (· + 1) ∘ Function.eval default := by
  ext x
  simp only [edgeParam, Function.comp_apply, Function.eval, Fin.default_eq_zero]
  ring

private theorem image_edgeParam_ball (i : Fin n) :
    σ.edgeParam i '' ball 0 1 = Ioo 0 (σ.edgeLength i) := by
  rw [σ.edgeParam_eq_comp i, image_comp, image_comp, Pi.ball_unique,
    image_preimage_eq _ (Function.surjective_eval _), Real.ball_eq_Ioo, image_add_const_Ioo,
    image_mul_left_Ioo (half_pos (σ.edgeLength_pos i))]
  norm_num

private theorem image_edgeParam_closedBall (i : Fin n) :
    σ.edgeParam i '' closedBall 0 1 = Icc 0 (σ.edgeLength i) := by
  rw [σ.edgeParam_eq_comp i, image_comp, image_comp, Pi.closedBall_unique,
    image_preimage_eq _ (Function.surjective_eval _), Real.closedBall_eq_Icc, image_add_const_Icc,
    image_mul_left_Icc' (half_pos (σ.edgeLength_pos i))]
  norm_num

private theorem edgeParam_of_mem_sphere (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    σ.edgeParam i x = 0 ∨ σ.edgeParam i x = σ.edgeLength i := by
  rw [Pi.mem_sphere_unique] at hx
  simp only [Fin.default_eq_zero, Pi.zero_apply, mem_sphere_zero_iff_norm, Real.norm_eq_abs] at hx
  rcases (abs_eq zero_le_one).1 hx with h | h
  · right
    rw [edgeParam, h]
    ring
  · left
    rw [edgeParam, h]
    ring

private theorem injective_edgeParam (i : Fin n) : Function.Injective (σ.edgeParam i) := by
  intro x y h
  have hℓ := (σ.edgeLength_pos i).ne'
  simp only [edgeParam] at h
  funext k
  rw [Subsingleton.elim k 0]
  have := mul_left_cancel₀ hℓ
    (by linarith : σ.edgeLength i * (x 0 + 1) = σ.edgeLength i * (y 0 + 1))
  linarith

variable (Γ) in
/-- The characteristic map of the edge carried by side `i`. -/
private def edgeMap (i : Fin n) (x : Fin 1 → ℝ) : orbitRel.Quotient Γ ℍ :=
  π (sideLine P i (σ.edgeParam i x))

private theorem continuous_edgeMap (i : Fin n) : Continuous (σ.edgeMap Γ i) :=
  continuous_quotient_mk'.comp ((continuous_sideLine i).comp (σ.continuous_edgeParam i))

private theorem image_edgeMap_ball (i : Fin n) :
    σ.edgeMap Γ i '' ball 0 1 = (fun t ↦ π (sideLine P i t)) '' Ioo 0 (σ.edgeLength i) := by
  rw [← σ.image_edgeParam_ball i, image_image]
  rfl

private theorem image_edgeMap_closedBall (i : Fin n) :
    σ.edgeMap Γ i '' closedBall 0 1 =
      (fun t ↦ π (sideLine P i t)) '' Icc 0 (σ.edgeLength i) := by
  rw [← σ.image_edgeParam_closedBall i, image_image]
  rfl

/-- The endpoints of an edge are `0`-cells. -/
private theorem edgeMap_mem_zeroCells (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    σ.edgeMap Γ i x ∈ σ.zeroCells Γ := by
  rcases σ.edgeParam_of_mem_sphere i hx with h | h <;> rw [edgeMap, h]
  · exact Or.inl ⟨i, by rw [sideLine_zero]⟩
  · by_cases hi : σ.pair i = i
    · rw [σ.edgeLength_of_pair_eq hi]
      exact Or.inr ⟨⟨i, hi⟩, by dsimp only; rw [selfPairedSideFixedPoint_eq_sideLine]⟩
    · simp only [edgeLength, hi, ↓reduceIte, sideLine_sideLength]
      exact Or.inl ⟨i + 1, rfl⟩

include hmap hdisj in
private theorem injOn_edgeMap (i : Fin n) :
    InjOn (σ.edgeMap Γ i) (ball 0 1) := by
  intro x hx y hy h
  have hs := (σ.image_edgeParam_ball i).subset (mem_image_of_mem _ hx)
  have ht := (σ.image_edgeParam_ball i).subset (mem_image_of_mem _ hy)
  rcases σ.sideLine_eq_or_of_mk_eq hmap hdisj (σ.Ioo_edgeLength_subset i hs)
      (σ.Ioo_edgeLength_subset i ht) h.symm with ⟨-, h⟩ | ⟨hi, h⟩
  · exact σ.injective_edgeParam i h.symm
  · have hi : σ.pair i = i := hi.symm
    rw [map_smul_sideLine_of_pair_eq σ hi] at h
    rw [σ.edgeLength_of_pair_eq hi] at hs ht
    have := sideLine_injective _ h
    linarith [hs.2, ht.2]

include hmap hdisj in
/-- Distinct side representatives carry disjoint open edges. -/
private theorem disjoint_image_edgeMap_ball {i j : σ.SideRepresentative} (hij : i ≠ j) :
    Disjoint (σ.edgeMap Γ i '' ball 0 1) (σ.edgeMap Γ j '' ball 0 1) := by
  rw [σ.image_edgeMap_ball, σ.image_edgeMap_ball, disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, h⟩
  rcases σ.sideLine_eq_or_of_mk_eq hmap hdisj (σ.Ioo_edgeLength_subset i hs)
      (σ.Ioo_edgeLength_subset j ht) h with ⟨h, -⟩ | ⟨h, -⟩
  · exact hij (Subtype.ext h.symm)
  · have hj := j.2
    rw [h, σ.pair_pair] at hj
    exact hij (Subtype.ext (h.trans (le_antisymm hj i.2)).symm)

/-! ### The `2`-cell -/

variable (P) in
/-- A homeomorphism from the closed unit ball of the sup norm on `Fin 2 → ℝ` onto `P`, carrying
the open ball onto the interior and the sphere onto the sides. -/
private def faceHomeomorph : closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ P.carrier :=
  (closedBallHomeomorphOfFinrankEq (by simp)).trans P.exists_homeomorph_closedBall.choose.symm

private theorem faceHomeomorph_mem_interior_iff (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (faceHomeomorph P x : ℍ) ∈ interior P.toConvexPolygon.carrier ↔ (x : Fin 2 → ℝ) ∈ ball 0 1 := by
  have h := P.exists_homeomorph_closedBall.choose_spec.1
    (P.exists_homeomorph_closedBall.choose.symm (closedBallHomeomorphOfFinrankEq (by simp) x))
  rw [Homeomorph.apply_symm_apply, coe_closedBallHomeomorphOfFinrankEq_apply, mem_ball_zero_iff,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, ← mem_ball_zero_iff] at h
  rw [P.carrier_toConvexPolygon]
  exact h.symm

private theorem exists_faceHomeomorph_mem_side (x : closedBall (0 : Fin 2 → ℝ) 1)
    (hx : (x : Fin 2 → ℝ) ∈ sphere 0 1) :
    ∃ i, (faceHomeomorph P x : ℍ) ∈ P.toConvexPolygon.side i := by
  have h := P.exists_homeomorph_closedBall.choose_spec.2
    (P.exists_homeomorph_closedBall.choose.symm (closedBallHomeomorphOfFinrankEq (by simp) x))
  rw [Homeomorph.apply_symm_apply, coe_closedBallHomeomorphOfFinrankEq_apply,
    mem_sphere_zero_iff_norm, ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff,
    ← mem_sphere_zero_iff_norm] at h
  simp only [CompactConvexPolygon.side_toConvexPolygon]
  exact h.1 hx

variable (Γ) in
open scoped Classical in
/-- The characteristic map of the face: the orbit projection of `P`, read on the closed unit
ball through `faceHomeomorph`. -/
private def faceMap (x : Fin 2 → ℝ) : orbitRel.Quotient Γ ℍ :=
  if hx : x ∈ closedBall 0 1 then π (faceHomeomorph P ⟨x, hx⟩)
  else π (faceHomeomorph P ⟨0, mem_closedBall_self zero_le_one⟩)

private theorem faceMap_of_mem (x : closedBall (0 : Fin 2 → ℝ) 1) :
    faceMap (P := P) Γ x = π (faceHomeomorph P x) := by
  simp [faceMap, x.2]

private theorem continuousOn_faceMap : ContinuousOn (faceMap (P := P) Γ) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_quotient_mk'.comp (continuous_subtype_val.comp
    (faceHomeomorph P).continuous)).congr fun x ↦ (faceMap_of_mem x).symm

private theorem image_faceMap_ball :
    faceMap (P := P) Γ '' ball 0 1 = π '' interior P.toConvexPolygon.carrier := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ closedBall 0 1 := ball_subset_closedBall hx
    exact ⟨_, (faceHomeomorph_mem_interior_iff ⟨x, hx'⟩).2 hx, (faceMap_of_mem ⟨x, hx'⟩).symm⟩
  · rintro ⟨z, hz, rfl⟩
    have hzP : z ∈ P.carrier := by
      rw [← P.carrier_toConvexPolygon]
      exact interior_subset hz
    set x := (faceHomeomorph P).symm ⟨z, hzP⟩
    have hxz : (faceHomeomorph P x : ℍ) = z := by simp [x]
    refine ⟨x, (faceHomeomorph_mem_interior_iff x).1 (by rwa [hxz]), ?_⟩
    rw [faceMap_of_mem, hxz]

private theorem image_faceMap_closedBall :
    faceMap (P := P) Γ '' closedBall 0 1 = π '' P.toConvexPolygon.carrier := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨_, ?_, (faceMap_of_mem ⟨x, hx⟩).symm⟩
    rw [P.carrier_toConvexPolygon]
    exact (faceHomeomorph P ⟨x, hx⟩).2
  · rintro ⟨z, hz, rfl⟩
    rw [P.carrier_toConvexPolygon] at hz
    set x := (faceHomeomorph P).symm ⟨z, hz⟩
    refine ⟨x, x.2, ?_⟩
    rw [faceMap_of_mem]
    simp [x]

include hmap hdisj in
private theorem injOn_faceMap : InjOn (faceMap (P := P) Γ) (ball 0 1) := by
  intro x hx y hy h
  have hx' : x ∈ closedBall 0 1 := ball_subset_closedBall hx
  have hy' : y ∈ closedBall 0 1 := ball_subset_closedBall hy
  rw [faceMap_of_mem ⟨x, hx'⟩, faceMap_of_mem ⟨y, hy'⟩] at h
  have := σ.eq_of_mk_eq_of_mem_interior hmap hdisj
    ((faceHomeomorph_mem_interior_iff ⟨x, hx'⟩).2 hx)
    (by rw [P.carrier_toConvexPolygon]; exact (faceHomeomorph P ⟨y, hy'⟩).2) h.symm
  exact (congrArg Subtype.val ((faceHomeomorph P).injective (Subtype.ext this))).symm

/-! ### Disjointness of the open cells -/

include hmap hdisj in
/-- A point of a side is equivalent to no interior point of `P`. -/
private theorem mk_notMem_image_interior {j : Fin n} {z : ℍ} (hz : z ∈ P.toConvexPolygon.side j) :
    π z ∉ π '' interior P.toConvexPolygon.carrier := by
  rintro ⟨w, hw, h⟩
  obtain rfl := σ.eq_of_mk_eq_of_mem_interior hmap hdisj hw
    (P.toConvexPolygon.side_subset_carrier j hz) h.symm
  exact disjoint_left.1 disjoint_interior_frontier hw
    (P.toConvexPolygon.side_subset_frontier_carrier j hz)

/-- Every `0`-cell is the orbit of a point on a side. -/
private theorem exists_mem_side_of_mem_zeroCells {q : orbitRel.Quotient Γ ℍ}
    (hq : q ∈ σ.zeroCells Γ) : ∃ j, ∃ z ∈ P.toConvexPolygon.side j, π z = q := by
  rcases hq with ⟨j, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨j, P.vertex j, P.toConvexPolygon.mem_side_of_vertex_eq_inl (P.vertex_toConvexPolygon j),
      rfl⟩
  · exact ⟨i, _, (σ.selfPairedSideFixedPoint_spec i).1, rfl⟩

/-! ### The CW structure -/

variable (Γ) in
/-- The cells of the quotient: the `0`-cells, one `1`-cell for each pair of sides, and one
`2`-cell. -/
private abbrev Cell : ℕ → Type
  | 0 => σ.zeroCells Γ
  | 1 => σ.SideRepresentative
  | 2 => PUnit
  | _ + 3 => PEmpty

/-- The characteristic maps of the cells of the quotient. -/
private def cellMap : (m : ℕ) → σ.Cell Γ m → PartialEquiv (Fin m → ℝ) (orbitRel.Quotient Γ ℍ)
  | 0, q => .single 0 q.1
  | 1, i => InjOn.toPartialEquiv _ _ (σ.injOn_edgeMap hmap hdisj i)
  | 2, _ => InjOn.toPartialEquiv _ _ (σ.injOn_faceMap hmap hdisj)
  | _ + 3, i => PEmpty.elim i

section CellMap

private theorem image_cellMap_zero (q : σ.Cell Γ 0) {s : Set (Fin 0 → ℝ)} (hs : s.Nonempty) :
    σ.cellMap hmap hdisj 0 q '' s = {q.1} :=
  hs.image_const _

private theorem coe_cellMap_one (i : σ.Cell Γ 1) :
    ⇑(σ.cellMap hmap hdisj 1 i) = σ.edgeMap Γ i :=
  (rfl)

private theorem coe_cellMap_two (i : σ.Cell Γ 2) :
    ⇑(σ.cellMap hmap hdisj 2 i) = faceMap (P := P) Γ :=
  (rfl)

private theorem pairwiseDisjoint_cellMap :
    (univ : Set (Σ m, σ.Cell Γ m)).PairwiseDisjoint
      fun c ↦ σ.cellMap hmap hdisj c.1 c.2 '' ball 0 1 := by
  have hb (m : ℕ) : (ball (0 : Fin m → ℝ) 1).Nonempty := ⟨0, mem_ball_self one_pos⟩
  -- an open edge misses the `0`-cells
  have h01 (q : σ.Cell Γ 0) (i : σ.Cell Γ 1) :
      Disjoint (σ.cellMap hmap hdisj 0 q '' ball 0 1) (σ.cellMap hmap hdisj 1 i '' ball 0 1) := by
    rw [image_cellMap_zero _ _ _ _ (hb 0), coe_cellMap_one, image_edgeMap_ball,
      disjoint_singleton_left]
    rintro ⟨t, ht, h⟩
    dsimp only at h
    exact σ.mk_sideLine_notMem_zeroCells hmap hdisj ht (h ▸ q.2)
  -- the open face misses the `0`-cells
  have h02 (q : σ.Cell Γ 0) (i : σ.Cell Γ 2) :
      Disjoint (σ.cellMap hmap hdisj 0 q '' ball 0 1) (σ.cellMap hmap hdisj 2 i '' ball 0 1) := by
    rw [image_cellMap_zero _ _ _ _ (hb 0), coe_cellMap_two, image_faceMap_ball,
      disjoint_singleton_left]
    obtain ⟨j, z, hz, hq⟩ := σ.exists_mem_side_of_mem_zeroCells q.2
    exact hq ▸ σ.mk_notMem_image_interior hmap hdisj hz
  -- the open face misses the open edges
  have h12 (i : σ.Cell Γ 1) (k : σ.Cell Γ 2) :
      Disjoint (σ.cellMap hmap hdisj 1 i '' ball 0 1) (σ.cellMap hmap hdisj 2 k '' ball 0 1) := by
    rw [coe_cellMap_one, coe_cellMap_two, image_edgeMap_ball, image_faceMap_ball, disjoint_left]
    rintro _ ⟨t, ht, rfl⟩
    exact σ.mk_notMem_image_interior hmap hdisj
      (sideLine_mem_side (σ.Icc_edgeLength_subset i (Ioo_subset_Icc_self ht)))
  rintro ⟨m, c⟩ - ⟨m', c'⟩ - hne
  match m, c, m', c' with
  | 0, q, 0, q' =>
    rw [Function.onFun, image_cellMap_zero _ _ _ _ (hb 0), image_cellMap_zero _ _ _ _ (hb 0),
      disjoint_singleton]
    exact fun h ↦ hne (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  | 0, q, 1, i => exact h01 q i
  | 1, i, 0, q => exact (h01 q i).symm
  | 0, q, 2, i => exact h02 q i
  | 2, i, 0, q => exact (h02 q i).symm
  | 1, i, 2, k => exact h12 i k
  | 2, k, 1, i => exact (h12 i k).symm
  | 1, i, 1, j =>
    rw [Function.onFun, coe_cellMap_one, coe_cellMap_one]
    exact σ.disjoint_image_edgeMap_ball hmap hdisj fun h ↦ hne (Sigma.ext rfl (heq_of_eq h))
  | 2, ⟨⟩, 2, ⟨⟩ => exact absurd rfl hne
  | _ + 3, i, _, _ | _, _, _ + 3, i => exact PEmpty.elim i

private theorem continuousOn_cellMap_symm [T2Space (orbitRel.Quotient Γ ℍ)] :
    ∀ (m : ℕ) (c : σ.Cell Γ m),
      ContinuousOn (σ.cellMap hmap hdisj m c).symm (σ.cellMap hmap hdisj m c).target
  | 0, _ => continuousOn_const
  | 1, i => by
    refine (σ.continuous_edgeMap i).continuousOn.continuousOn_invFunOn_image_of_isCompact
      (isCompact_closedBall 0 1) ball_subset_closedBall (σ.injOn_edgeMap hmap hdisj i) ?_
    rw [closedBall_sdiff_ball, σ.image_edgeMap_ball, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨t, ht, h⟩
    dsimp only at h
    exact σ.mk_sideLine_notMem_zeroCells hmap hdisj ht (h ▸ σ.edgeMap_mem_zeroCells i hx)
  | 2, _ => by
    refine (continuousOn_faceMap (P := P)).continuousOn_invFunOn_image_of_isCompact
      (isCompact_closedBall 0 1) ball_subset_closedBall (σ.injOn_faceMap hmap hdisj) ?_
    rw [closedBall_sdiff_ball, image_faceMap_ball, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := exists_faceHomeomorph_mem_side (P := P) ⟨x, sphere_subset_closedBall hx⟩ hx
    rw [faceMap_of_mem ⟨x, sphere_subset_closedBall hx⟩]
    exact σ.mk_notMem_image_interior hmap hdisj hj
  | _ + 3, i => PEmpty.elim i

private theorem mapsTo_cellMap :
    ∀ (m : ℕ) (c : σ.Cell Γ m), MapsTo (σ.cellMap hmap hdisj m c) (sphere 0 1)
      (⋃ (k < m) (c' : σ.Cell Γ k), σ.cellMap hmap hdisj k c' '' closedBall 0 1)
  | 0, _ => fun x hx ↦ ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim
  | 1, i => fun x hx ↦ by
    refine mem_iUnion₂.2 ⟨0, zero_lt_one, mem_iUnion.2 ⟨⟨_, σ.edgeMap_mem_zeroCells i hx⟩, ?_⟩⟩
    rw [image_cellMap_zero _ _ _ _ ⟨(0 : Fin 0 → ℝ), mem_closedBall_self zero_le_one⟩]
    rfl
  | 2, _ => fun x hx ↦ by
    obtain ⟨j, hj⟩ := exists_faceHomeomorph_mem_side (P := P) ⟨x, sphere_subset_closedBall hx⟩ hx
    obtain ⟨i, t, ht, h⟩ := σ.exists_mk_eq_of_mem_side hmap hj
    refine mem_iUnion₂.2 ⟨1, one_lt_two, mem_iUnion.2 ⟨i, ?_⟩⟩
    rw [coe_cellMap_one, image_edgeMap_closedBall, coe_cellMap_two,
      faceMap_of_mem ⟨x, sphere_subset_closedBall hx⟩]
    exact ⟨t, ht, h⟩
  | _ + 3, i => PEmpty.elim i

include hlf in
private theorem iUnion_image_cellMap :
    ⋃ (m : ℕ) (c : σ.Cell Γ m), σ.cellMap hmap hdisj m c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun q ↦ mem_iUnion₂.2 ⟨2, ⟨⟩, ?_⟩
  obtain ⟨w, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨γ, hγ⟩ := mem_iUnion.1 ((σ.iUnion_smul_carrier_eq_univ hmap hlf).symm ▸ mem_univ w)
  obtain ⟨z, hz, rfl⟩ := hγ
  rw [coe_cellMap_two, image_faceMap_closedBall]
  exact ⟨z, hz, (Quotient.sound (mem_orbit z γ)).symm⟩

end CellMap

include hlf in
/-- A group with locally finite translates of `P` is discrete, so `Γ \ ℍ` is Hausdorff. -/
private theorem discreteTopology_of_locallyFinite_carrier : DiscreteTopology Γ :=
  discreteTopology_of_locallyFinite_smul
    (P.toConvexPolygon.nonempty_interior_carrier.mono interior_subset) hlf

/-- The CW structure on the quotient by a compact fundamental polygon. -/
@[instance_reducible]
private def cwComplex : CWComplex (univ : Set (orbitRel.Quotient Γ ℍ)) :=
  haveI := discreteTopology_of_locallyFinite_carrier hlf
  CWComplex.mkFinite univ (σ.Cell Γ) (σ.cellMap hmap hdisj)
    (Filter.eventually_atTop.2 ⟨3, fun m hm ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
      exact inferInstanceAs (IsEmpty PEmpty)⟩)
    (fun
      | 0 => (σ.finite_zeroCells).to_subtype
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
      | 1, i => (σ.continuous_edgeMap i).continuousOn
      | 2, _ => continuousOn_faceMap
      | _ + 3, i => PEmpty.elim i)
    (σ.continuousOn_cellMap_symm hmap hdisj) (σ.pairwiseDisjoint_cellMap hmap hdisj)
    (σ.mapsTo_cellMap hmap hdisj) (σ.iUnion_image_cellMap hmap hlf hdisj)

private theorem finite_cwComplex :
    letI := σ.cwComplex hmap hlf hdisj
    RelCWComplex.Finite (univ : Set (orbitRel.Quotient Γ ℍ)) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-- The alternating cell count of the CW structure on the quotient. -/
private theorem cwEulerChar_cwComplex :
    letI := σ.cwComplex hmap hlf hdisj
    cwEulerChar (univ : Set (orbitRel.Quotient Γ ℍ)) =
      Nat.card σ.FiniteVertexCycle + Nat.card {i : Fin n // σ.pair i = i} -
        Nat.card σ.SideRepresentative + 1 := by
  let := σ.cwComplex hmap hlf hdisj
  -- The cells of `cwComplex` are, by construction, the family `Cell`.
  have hcell (m : ℕ) : cell (univ : Set (orbitRel.Quotient Γ ℍ)) m = σ.Cell Γ m := rfl
  rw [cwEulerChar_eq_sum_range (C := (univ : Set (orbitRel.Quotient Γ ℍ))) (N := 3) fun m hm ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [hcell]
    exact inferInstanceAs (IsEmpty PEmpty)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hcell, Cell, Nat.card_unique,
    σ.natCard_zeroCells hmap hdisj]
  push_cast
  ring

/-! ### The Euler characteristic -/

include hmap hlf hdisj in
/-- **The quotient by a compact fundamental polygon has finite CW type.** Let `σ` pair the sides
of a compact convex polygon `P`, and let the translates of `P` by a group `Γ` containing the
side-pairing maps be locally finite, with disjoint interiors. Then `Γ \ ℍ` is homeomorphic to a
finite CW complex, with the vertex cycles and the fixed points of self-paired sides as `0`-cells,
one `1`-cell for each pair of sides and one `2`-cell. -/
theorem finiteCWType_orbitRel_quotient : FiniteCWType (orbitRel.Quotient Γ ℍ) := by
  have := discreteTopology_of_locallyFinite_carrier hlf
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  exact (Homeomorph.Set.univ _).symm.finiteCWType

/-- **The Euler characteristic of the quotient by a compact fundamental polygon.** Under the
hypotheses of `finiteCWType_orbitRel_quotient`, `χ(Γ \ ℍ) = V + k - E + 1`, where `V` is the
number of vertex cycles, `k` the number of self-paired sides and `E` the number of pairs of
sides, which is `(n + k) / 2` (`two_mul_natCard_sideRepresentative`). -/
theorem eulerChar_orbitRel_quotient :
    haveI := σ.finiteCWType_orbitRel_quotient hmap hlf hdisj
    eulerChar (orbitRel.Quotient Γ ℍ) =
      Nat.card σ.FiniteVertexCycle + Nat.card {i : Fin n // σ.pair i = i} -
        Nat.card σ.SideRepresentative + 1 := by
  have := discreteTopology_of_locallyFinite_carrier hlf
  have := σ.finiteCWType_orbitRel_quotient hmap hlf hdisj
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ _).symm.toHomotopyEquiv,
    σ.cwEulerChar_cwComplex hmap hlf hdisj]

/-- **The area of a cocompact Fuchsian group through the Euler characteristic.** Under the
hypotheses of `finiteCWType_orbitRel_quotient`, the covolume of `Γ` is
`2π (-χ(Γ \ ℍ) + ∑ₑ (1 - 1 / mₑ))`, the sum running over the elliptic orbits `e` of `Γ` with
stabilizer orders `mₑ`. With `χ = 2 - 2g` this is `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ))`. -/
theorem covolume_eq_two_pi_mul_neg_eulerChar_add :
    haveI := σ.finiteCWType_orbitRel_quotient hmap hlf hdisj
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi * (-(eulerChar (orbitRel.Quotient Γ ℍ) : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹))) := by
  rw [σ.covolume_eq_two_pi_mul hmap hlf hdisj, σ.eulerChar_orbitRel_quotient hmap hlf hdisj]
  have h : (2 * Nat.card σ.SideRepresentative : ℝ) = n + Nat.card {i : Fin n // σ.pair i = i} := by
    exact_mod_cast σ.two_mul_natCard_sideRepresentative
  congr 2
  push_cast
  linarith

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
