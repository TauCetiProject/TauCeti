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
import TauCeti.Topology.Path.Extend.Ioo
import TauCeti.Topology.Separation.InvFunOn

/-!
# The CW structure and Euler characteristic of a cuspidal fundamental polygon

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, with vertices in `ℍ ∪ ∂ℍ`, and let a
discrete subgroup `Γ ≤ PSL(2, ℝ)` contain the side-pairing maps, with locally finite translates of
`P` whose interiors are pairwise disjoint. This file equips `X(Γ) = Γ.CompactifiedQuotient` with a
finite CW complex structure: `0`-cells at the `V` finite vertex cycles, `c` cusp orbits, and `k`
self-paired side fixed points; `E = (n + k) / 2` `1`-cells via `σ.edgeArc`; and one `2`-cell via
`ConvexPolygon.exists_equiv_closedBall`. This yields `χ(X(Γ)) = V + c + k - E + 1 = 2 - 2 · genus`,
`genus X(Γ) = σ.toPermutationTriple.genus`, and the orbifold signature area formula.

## Main results

* `ConvexPolygon.SidePairing.finiteCWType_compactifiedQuotient`: `X(Γ)` has finite CW type.
* `ConvexPolygon.SidePairing.eulerChar_compactifiedQuotient`: `χ(X(Γ)) = V + c + k - E + 1`.
* `ConvexPolygon.SidePairing.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus`:
  `χ(X(Γ)) = 2 - 2 · genus X(Γ)`.
* `ConvexPolygon.SidePairing.genus_compactifiedQuotient_eq`:
  `genus X(Γ) = σ.toPermutationTriple.genus`.
* `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps` and
  `ConvexPolygon.SidePairing.covolume_eq_two_pi_mul_signature`: the orbifold area formula.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, GTM 91, Springer, 1983, §§9.3 and 10.4.
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §§4.2–4.3.
-/

public section

noncomputable section

open MeasureTheory Metric MulAction Set Topology Topology.RelCWComplex UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}
  (hmap : ∀ i, σ.map i ∈ Γ)
  (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
  (hdisj : ∀ γ : Γ, γ ≠ 1 → Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))

local notation "π" => (Quotient.mk'' : ℍ → orbitRel.Quotient Γ ℍ)

/-! ### The `0`-cells -/

variable (P Γ) in
private def finiteVertexOrbits : Set Γ.CompactifiedQuotient :=
  range fun j : {i : Fin n // (P.vertex i).isLeft} ↦
    ofQuotient (π ((P.vertex j).getLeft j.property))

variable (Γ) in
private def midpointOrbits : Set Γ.CompactifiedQuotient :=
  range fun i : {i : Fin n // σ.pair i = i} ↦ ofQuotient (π (σ.selfPairedSideFixedPoint i))

variable (Γ) in
private def zeroCells : Set Γ.CompactifiedQuotient :=
  (finiteVertexOrbits P Γ ∪ σ.midpointOrbits Γ) ∪ range (ofCusp (Γ := Γ))

include hmap hlf in
private theorem finite_zeroCells : (σ.zeroCells Γ).Finite := by
  have := σ.finite_cuspOrbit hmap hlf
  exact ((finite_range _).union (finite_range _)).union (finite_range _)

include hmap hlf hdisj in
private theorem natCard_zeroCells :
    Nat.card (σ.zeroCells Γ) =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} := by
  have := σ.finite_cuspOrbit hmap hlf
  have hd₁ : Disjoint (finiteVertexOrbits P Γ) (σ.midpointOrbits Γ) := by
    rw [disjoint_left]; rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
    exact σ.quotientMk_vertex_ne_selfPairedSideFixedPoint hmap hdisj
      (Sum.inl_getLeft _ j.property).symm i (ofQuotient_injective hi.symm)
  have hd₂ : Disjoint (finiteVertexOrbits P Γ ∪ σ.midpointOrbits Γ) (range (ofCusp (Γ := Γ))) := by
    rw [disjoint_left]; rintro _ (⟨j, rfl⟩ | ⟨i, rfl⟩) ⟨C, hC⟩ <;> cases hC
  rw [zeroCells, Nat.card_coe_set_eq,
    ncard_union_eq hd₂ ((finite_range _).union (finite_range _)) (finite_range _),
    ncard_union_eq hd₁ (finite_range _) (finite_range _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  have hV : Nat.card (finiteVertexOrbits P Γ) = Nat.card σ.FiniteVertexCycle := by
    have hfv : finiteVertexOrbits P Γ = ofQuotient '' range
        (fun j : {i : Fin n // (P.vertex i).isLeft} ↦ π ((P.vertex j).getLeft j.property)) := by
      ext; simp [finiteVertexOrbits]
    rw [hfv, Nat.card_image_of_injective ofQuotient_injective,
      Nat.card_congr (σ.finiteVertexCycleEquiv hmap hdisj)]
  have hM : Nat.card (σ.midpointOrbits Γ) = Nat.card {i : Fin n // σ.pair i = i} :=
    Nat.card_range_of_injective
      (ofQuotient_injective.comp (σ.injective_quotientMk_selfPairedSideFixedPoint hmap hdisj))
  have hC : Nat.card (range (ofCusp (Γ := Γ))) = Nat.card σ.IdealVertexCycle := by
    rw [Nat.card_range_of_injective fun _ _ h ↦ ofCusp.inj h, σ.natCard_cuspOrbit hmap hlf hdisj]
  omega

include hmap hdisj in
private theorem ofQuotient_mk_edgeArc_notMem_zeroCells {i : Fin n} {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    ofQuotient (π (σ.edgeArc i u)) ∉ σ.zeroCells Γ := by
  rintro ((⟨j, hj⟩ | ⟨j, hj⟩) | ⟨C, hC⟩)
  · obtain ⟨k, hk⟩ := σ.exists_vertex_eq_inl_of_quotientMk_eq hmap hdisj
      (Sum.inl_getLeft _ j.property).symm (P.side_subset_carrier i (σ.edgeArc_mem_side i hu))
      (ofQuotient_injective hj.symm)
    exact σ.vertex_ne_inl_edgeArc i hu k hk
  · rcases σ.eq_or_eq_map_smul_of_quotientMk_eq (hmap i) hdisj (σ.edgeArc_mem_side i hu)
        (σ.vertex_ne_inl_edgeArc i hu i) (σ.vertex_ne_inl_edgeArc i hu (i + 1))
        (P.side_subset_carrier j.val (σ.selfPairedSideFixedPoint_spec j).1)
        (ofQuotient_injective hj) with heq | heq
    exacts [σ.edgeArc_ne_selfPairedSideFixedPoint i hu j heq.symm,
      σ.map_smul_edgeArc_ne_selfPairedSideFixedPoint i hu j heq.symm]
  · cases hC

private def vertexZeroCell (i : Fin n) : Γ.CompactifiedQuotient :=
  if hl : (P.vertex i).isLeft then ofQuotient (π ((P.vertex i).getLeft hl))
  else ofCusp (Γ.cuspOrbitMk ⟨(P.vertex i).getRight (Sum.not_isLeft.1 hl),
    Subgroup.mem_cuspPoints.2 (σ.isCuspPoint_of_vertex_eq_inr
      (Sum.inr_getRight _ (Sum.not_isLeft.1 hl)).symm (σ.cycleMap_mem hmap _) hlf)⟩)

private theorem vertexZeroCell_of_eq_inl {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    σ.vertexZeroCell hmap hlf i = ofQuotient (π v) := by
  simp [vertexZeroCell, hv]

private theorem exists_cuspDatum_vertexZeroCell [DiscreteTopology Γ] {i : Fin n} {ξ : OnePoint ℝ}
    (hξ : P.vertex i = .inr ξ) :
    ∃ D : Γ.CuspDatum, σ.vertexZeroCell hmap hlf i = ofCusp D.cuspOrbit ∧ D.scaling • ξ = ∞ := by
  obtain ⟨D, hD⟩ := (σ.isCuspPoint_of_vertex_eq_inr hξ (σ.cycleMap_mem hmap _)
    hlf).exists_cuspDatum_cusp_eq
  refine ⟨D, ?_, by rw [← hD, D.scaling_smul_cusp]⟩
  rw [vertexZeroCell, dite_eq_right (by simp [hξ])]
  exact congrArg ofCusp (Subtype.ext (by simp [hξ, hD]))

private theorem vertexZeroCell_mem_zeroCells (i : Fin n) :
    σ.vertexZeroCell hmap hlf i ∈ σ.zeroCells Γ := by
  unfold vertexZeroCell; split_ifs with hl
  exacts [Or.inl (Or.inl ⟨⟨i, hl⟩, rfl⟩), Or.inr ⟨_, rfl⟩]

/-! ### The `1`-cells -/

private def edgeMap1D (i : Fin n) : ℝ → Γ.CompactifiedQuotient :=
  extendIoo (-1 : ℝ) 1 (σ.vertexZeroCell hmap hlf i)
    (if hi : σ.pair i = i then ofQuotient (π (σ.selfPairedSideFixedPoint ⟨i, hi⟩))
      else σ.vertexZeroCell hmap hlf (i + 1))
    (fun u ↦ ofQuotient (π (σ.edgeArc i u)))

private def edgeMap (i : Fin n) (x : Fin 1 → ℝ) : Γ.CompactifiedQuotient :=
  σ.edgeMap1D hmap hlf i (x 0)

private theorem edgeMap_of_mem_ball (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ ball 0 1) :
    σ.edgeMap hmap hlf i x = ofQuotient (π (σ.edgeArc i (x 0))) := by
  rw [Pi.mem_ball_unique, Fin.default_eq_zero, Pi.zero_apply, Real.ball_eq_Ioo, zero_sub, zero_add]
    at hx
  rw [edgeMap, edgeMap1D, extendIoo_apply_of_mem_Ioo hx]

private theorem image_edgeMap_ball (i : Fin n) :
    σ.edgeMap hmap hlf i '' ball 0 1 =
      (fun u ↦ ofQuotient (π (σ.edgeArc i u))) '' Ioo (-1) 1 := by
  have h : σ.edgeMap hmap hlf i = σ.edgeMap1D hmap hlf i ∘ Function.eval 0 := rfl
  rw [h, image_comp, Pi.ball_unique, Fin.default_eq_zero,
    image_preimage_eq _ (Function.surjective_eval _), Pi.zero_apply, Real.ball_eq_Ioo, zero_sub,
    zero_add]
  exact EqOn.image_eq fun _ hu ↦ extendIoo_apply_of_mem_Ioo hu

private theorem edgeMap_mem_zeroCells (i : Fin n) {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    σ.edgeMap hmap hlf i x ∈ σ.zeroCells Γ := by
  rw [Pi.mem_sphere_unique] at hx
  simp only [Fin.default_eq_zero, Pi.zero_apply, mem_sphere_zero_iff_norm, Real.norm_eq_abs,
    abs_eq zero_le_one] at hx
  rcases hx with h1 | h1
  · rw [edgeMap, h1, edgeMap1D, extendIoo_apply_of_left_lt_of_right_le (by norm_num) le_rfl]
    split_ifs with hi
    exacts [Or.inl (Or.inr ⟨⟨i, hi⟩, rfl⟩), σ.vertexZeroCell_mem_zeroCells hmap hlf (i + 1)]
  · rw [edgeMap, h1, edgeMap1D, extendIoo_apply_of_le_left le_rfl]
    exact σ.vertexZeroCell_mem_zeroCells hmap hlf i

include hdisj in
private theorem injOn_edgeMap (i : Fin n) : InjOn (σ.edgeMap hmap hlf i) (ball 0 1) := by
  intro x hx y hy h
  rw [σ.edgeMap_of_mem_ball hmap hlf i hx, σ.edgeMap_of_mem_ball hmap hlf i hy] at h
  rw [Pi.mem_ball_unique, Fin.default_eq_zero, Pi.zero_apply, Real.ball_eq_Ioo, zero_sub, zero_add]
    at hx hy
  rcases σ.eq_and_eq_or_eq_pair_and_eq_map_smul_of_quotientMk_eq (hmap i) hdisj
      (σ.edgeArc_mem_side i hx) (σ.vertex_ne_inl_edgeArc i hx i)
      (σ.vertex_ne_inl_edgeArc i hx (i + 1)) (σ.edgeArc_mem_side i hy)
      (σ.vertex_ne_inl_edgeArc i hy i) (σ.vertex_ne_inl_edgeArc i hy (i + 1))
      (ofQuotient_injective h).symm with ⟨-, heq⟩ | ⟨-, heq⟩
  · ext k; rw [Subsingleton.elim k 0, σ.injOn_edgeArc i hy hx heq]
  · exact (σ.map_smul_edgeArc_ne_edgeArc i hx hy heq.symm).elim

include hdisj in
private theorem disjoint_image_edgeMap_ball {i j : σ.SideRepresentative} (hij : i ≠ j) :
    Disjoint (σ.edgeMap hmap hlf i '' ball 0 1) (σ.edgeMap hmap hlf j '' ball 0 1) := by
  rw [σ.image_edgeMap_ball, σ.image_edgeMap_ball, disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, h⟩
  rcases σ.eq_and_eq_or_eq_pair_and_eq_map_smul_of_quotientMk_eq (hmap i) hdisj
      (σ.edgeArc_mem_side i hu) (σ.vertex_ne_inl_edgeArc i hu i)
      (σ.vertex_ne_inl_edgeArc i hu (i + 1)) (σ.edgeArc_mem_side j hv)
      (σ.vertex_ne_inl_edgeArc j hv j) (σ.vertex_ne_inl_edgeArc j hv (j + 1))
      (ofQuotient_injective h) with ⟨heq, -⟩ | ⟨heq, -⟩
  · exact hij (Subtype.ext heq.symm)
  · have hj := j.property; rw [heq, σ.pair_pair] at hj
    exact hij (Subtype.ext (heq.trans (le_antisymm hj i.property)).symm)

private theorem continuousOn_edgeMap [DiscreteTopology Γ] (i : Fin n) :
    ContinuousOn (σ.edgeMap hmap hlf i) (closedBall 0 1) := by
  have hlt : (-1 : ℝ) < 1 := by norm_num
  have hq : Continuous (fun z : ℍ ↦ ofQuotient (π z)) :=
    continuous_ofQuotient.comp continuous_quotient_mk'
  have hl : Filter.Tendsto (fun u ↦ ofQuotient (π (σ.edgeArc i u))) (𝓝[>] (-1))
      (𝓝 (σ.vertexZeroCell hmap hlf i)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hlt]
    rcases hp : P.vertex i with v | ξ
    · rw [σ.vertexZeroCell_of_eq_inl hmap hlf hp]
      exact (hq.tendsto v).comp (σ.tendsto_edgeArc_neg_one_of_eq_inl hp)
    · obtain ⟨D, hcell, hgξ⟩ := σ.exists_cuspDatum_vertexZeroCell hmap hlf hp
      rw [hcell]; exact (tendsto_ofQuotient_quotientMk_nhds_ofCusp D).comp
        (σ.tendsto_edgeArc_neg_one_atImInfty_of_eq_inr hp hgξ)
  have hr : Filter.Tendsto (fun u ↦ ofQuotient (π (σ.edgeArc i u))) (𝓝[<] 1)
      (𝓝 (if hi : σ.pair i = i then ofQuotient (π (σ.selfPairedSideFixedPoint ⟨i, hi⟩))
        else σ.vertexZeroCell hmap hlf (i + 1))) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
    split_ifs with hi
    · exact (hq.tendsto _).comp (σ.tendsto_edgeArc_one_of_pair_eq hi)
    · rcases hq' : P.vertex (i + 1) with w | η
      · rw [σ.vertexZeroCell_of_eq_inl hmap hlf hq']
        exact (hq.tendsto w).comp (σ.tendsto_edgeArc_one_of_eq_inl hi hq')
      · obtain ⟨D, hcell, hgη⟩ := σ.exists_cuspDatum_vertexZeroCell hmap hlf hq'
        rw [hcell]; exact (tendsto_ofQuotient_quotientMk_nhds_ofCusp D).comp
          (σ.tendsto_edgeArc_one_atImInfty_of_eq_inr hi hq' hgη)
  refine (continuousOn_Icc_extendIoo (hq.comp_continuousOn (σ.continuousOn_edgeArc i))
    hl hr).comp (continuous_apply 0).continuousOn fun _ hx ↦ ?_
  rw [Pi.mem_closedBall_unique, Fin.default_eq_zero, Pi.zero_apply, Real.closedBall_eq_Icc,
    zero_sub, zero_add] at hx
  exact hx

private theorem mem_zeroCells_or_exists_edgeMap_of_mem_side {j : Fin n} {z : ℍ}
    (hz : z ∈ P.side j) :
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
    · exact Or.inr ⟨⟨j, hj⟩, (σ.image_edgeMap_ball hmap hlf j).symm ▸ ⟨u, hu, rfl⟩⟩
    · exact Or.inl (Or.inl (Or.inr ⟨⟨j, hjj⟩, rfl⟩))
    · exact Or.inr ⟨⟨j, hj⟩,
        (σ.image_edgeMap_ball hmap hlf j).symm ▸ ⟨u, hu, by dsimp only; rw [huz, hmk]⟩⟩
  · set k := σ.pair j
    have hkle : k ≤ σ.pair k := by rw [σ.pair_pair]; exact (lt_of_not_ge hj).le
    have hkp : P.vertex k ≠ .inl (σ.map j • z) := fun h ↦ hzq <| MulAction.injective (σ.map j)
      ((σ.map_smul_vertex_add_one j).trans (h.trans (Sum.smul_inl _ _).symm))
    have hkq : P.vertex (k + 1) ≠ .inl (σ.map j • z) := fun h ↦ hzp <| MulAction.injective (σ.map j)
      ((σ.map_smul_vertex j).trans (h.trans (Sum.smul_inl _ _).symm))
    rcases σ.mem_image_edgeArc_or_selfPaired_of_mem_side (σ.map_smul_mem_side hz) hkp hkq with
      ⟨u, hu, huz⟩ | ⟨hkk, -⟩
    · exact Or.inr ⟨⟨k, hkle⟩,
        (σ.image_edgeMap_ball hmap hlf k).symm ▸ ⟨u, hu, by dsimp only; rw [huz, hmk]⟩⟩
    · exact (hj (by rw [σ.pair_pair] at hkk; exact hkk ▸ le_rfl)).elim

/-! ### The `2`-cell -/

private abbrev diskHomeo : closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  closedBallHomeomorphOfFinrankEq (E := Fin 2 → ℝ) (F := ℂ) (by simp)

variable (P) in
private abbrev diskEquiv :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃ closedBall (0 : ℂ) 1 :=
  P.exists_equiv_closedBall.choose

variable (P) in
private def faceEquiv :
    closedBall (0 : Fin 2 → ℝ) 1 ≃ P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} :=
  diskHomeo.toEquiv.trans (diskEquiv P).symm

private def facePoint :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} → Γ.CompactifiedQuotient
  | .inl z => ofQuotient (π z)
  | .inr i => σ.vertexZeroCell hmap hlf i.val

open scoped Classical in
private def faceMap (x : Fin 2 → ℝ) : Γ.CompactifiedQuotient :=
  if hx : x ∈ closedBall 0 1 then σ.facePoint hmap hlf (faceEquiv P ⟨x, hx⟩)
  else ofQuotient (π UpperHalfPlane.I)

private theorem faceMap_of_mem (x : closedBall (0 : Fin 2 → ℝ) 1) :
    σ.faceMap hmap hlf x = σ.facePoint hmap hlf (faceEquiv P x) := by
  rw [faceMap, dite_eq_left x.property]

private theorem diskEquiv_faceEquiv (x : closedBall (0 : Fin 2 → ℝ) 1) :
    diskEquiv P (faceEquiv P x) = diskHomeo x := by simp [faceEquiv]

private theorem diskHomeo_mem_ball_iff (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (diskHomeo x : ℂ) ∈ ball (0 : ℂ) 1 ↔ (x : Fin 2 → ℝ) ∈ ball 0 1 := by
  rw [diskHomeo, coe_closedBallHomeomorphOfFinrankEq_apply, mem_ball_zero_iff,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, ← mem_ball_zero_iff]

private theorem diskHomeo_mem_sphere_iff (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (diskHomeo x : ℂ) ∈ sphere (0 : ℂ) 1 ↔ (x : Fin 2 → ℝ) ∈ sphere 0 1 := by
  rw [diskHomeo, coe_closedBallHomeomorphOfFinrankEq_apply, mem_sphere_zero_iff_norm,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff, ← mem_sphere_zero_iff_norm]

private theorem exists_faceEquiv_eq_inl_of_mem_ball {x : Fin 2 → ℝ} (hx : x ∈ ball 0 1) :
    ∃ z : P.carrier, faceEquiv P ⟨x, ball_subset_closedBall hx⟩ = .inl z ∧
      (z : ℍ) ∈ interior P.carrier := by
  obtain ⟨-, hball, -, hsphere_inr, -⟩ := P.exists_equiv_closedBall.choose_spec
  let xc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨x, ball_subset_closedBall hx⟩
  have hcb : (diskHomeo xc : ℂ) ∈ ball (0 : ℂ) 1 := (diskHomeo_mem_ball_iff xc).2 hx
  rcases he : faceEquiv P xc with z | i
  · exact ⟨z, rfl, (hball z).1 (by rw [← he, diskEquiv_faceEquiv]; exact hcb)⟩
  · have hs := hsphere_inr i
    rw [← he, diskEquiv_faceEquiv, mem_sphere_zero_iff_norm] at hs
    rw [mem_ball_zero_iff, hs] at hcb; exact (lt_irrefl _ hcb).elim

private theorem image_faceMap_ball :
    σ.faceMap hmap hlf '' ball 0 1 = ofQuotient '' (π '' interior P.carrier) := by
  obtain ⟨-, hball, -, -, -⟩ := P.exists_equiv_closedBall.choose_spec
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hint⟩ := exists_faceEquiv_eq_inl_of_mem_ball (P := P) hx
    rw [σ.faceMap_of_mem hmap hlf ⟨x, ball_subset_closedBall hx⟩, hz, facePoint]
    exact ⟨π z, ⟨z, hint, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    let zp : P.carrier := ⟨z, interior_subset hz⟩
    let u := diskHomeo.symm (diskEquiv P (.inl zp))
    refine ⟨u, (diskHomeo_mem_ball_iff u).1 (by simpa [u, diskEquiv] using (hball zp).2 hz), ?_⟩
    rw [σ.faceMap_of_mem hmap hlf u]; simp [faceEquiv, facePoint, u, zp]

include hdisj in
private theorem injOn_faceMap : InjOn (σ.faceMap hmap hlf) (ball 0 1) := by
  intro x hx y hy h
  obtain ⟨zx, hzx, hzx_int⟩ := exists_faceEquiv_eq_inl_of_mem_ball (P := P) hx
  obtain ⟨zy, hzy, -⟩ := exists_faceEquiv_eq_inl_of_mem_ball (P := P) hy
  rw [σ.faceMap_of_mem hmap hlf ⟨x, ball_subset_closedBall hx⟩,
    σ.faceMap_of_mem hmap hlf ⟨y, ball_subset_closedBall hy⟩, hzx, hzy, facePoint, facePoint] at h
  have hz_eq := P.eq_of_quotientMk_eq_of_mem_interior hdisj hzx_int zy.property
    (ofQuotient_injective h).symm
  have hfe : faceEquiv P ⟨x, ball_subset_closedBall hx⟩ =
      faceEquiv P ⟨y, ball_subset_closedBall hy⟩ := by rw [hzx, hzy, Subtype.ext hz_eq.symm]
  exact congrArg Subtype.val ((faceEquiv P).injective hfe)

private theorem faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere {x : Fin 2 → ℝ}
    (hx : x ∈ sphere 0 1) :
    σ.faceMap hmap hlf x ∈ σ.zeroCells Γ ∨
      ∃ i : σ.SideRepresentative, σ.faceMap hmap hlf x ∈ σ.edgeMap hmap hlf i '' ball 0 1 := by
  obtain ⟨-, -, hsphere_inl, -, -⟩ := P.exists_equiv_closedBall.choose_spec
  let xc : closedBall (0 : Fin 2 → ℝ) 1 := ⟨x, sphere_subset_closedBall hx⟩
  rw [σ.faceMap_of_mem hmap hlf xc]
  rcases he : faceEquiv P xc with z | i
  · have hs : (diskEquiv P (.inl z) : ℂ) ∈ sphere (0 : ℂ) 1 := by
      rw [← he, diskEquiv_faceEquiv]; exact (diskHomeo_mem_sphere_iff xc).2 hx
    obtain ⟨j, hj⟩ := (hsphere_inl z).1 hs
    exact σ.mem_zeroCells_or_exists_edgeMap_of_mem_side hmap hlf hj
  · exact Or.inl (σ.vertexZeroCell_mem_zeroCells hmap hlf i.val)

private theorem continuousOn_faceMap [DiscreteTopology Γ] :
    ContinuousOn (σ.faceMap hmap hlf) (closedBall 0 1) := by
  obtain ⟨hopen, -, -, -, hhoro⟩ := P.exists_equiv_closedBall.choose_spec
  have hdom : (closedBall (0 : Fin 2 → ℝ) 1).domRestrict (σ.faceMap hmap hlf) =
      fun x : closedBall (0 : Fin 2 → ℝ) 1 ↦ σ.facePoint hmap hlf (faceEquiv P x) :=
    funext fun x ↦ σ.faceMap_of_mem hmap hlf x
  rw [continuousOn_iff_continuous_domRestrict, hdom, continuous_iff_continuousAt]
  intro x₀
  rcases hx₀ : faceEquiv P x₀ with z₀ | i
  · let emb : P.carrier → closedBall (0 : Fin 2 → ℝ) 1 :=
      fun z ↦ diskHomeo.symm (diskEquiv P (.inl z))
    have hemb : IsOpenEmbedding emb := diskHomeo.symm.isOpenEmbedding.comp hopen
    have hx₀_emb : emb z₀ = x₀ :=
      diskHomeo.injective (by simp [emb, ← hx₀, diskEquiv_faceEquiv])
    rw [ContinuousAt, ← hx₀_emb, ← hemb.isOpenMap.map_nhds_eq hemb.continuous.continuousAt,
      Filter.tendsto_map'_iff]
    have hcomp : (fun x ↦ σ.facePoint hmap hlf (faceEquiv P x)) ∘ emb =
        fun z : P.carrier ↦ ofQuotient (π (z : ℍ)) := funext fun z ↦ by
      simp [Function.comp_apply, emb, faceEquiv, facePoint]
    have hval : σ.facePoint hmap hlf (faceEquiv P (emb z₀)) = ofQuotient (π (z₀ : ℍ)) :=
      congrFun hcomp z₀
    rw [hcomp, hval]
    exact (continuous_ofQuotient.comp
      (continuous_quotient_mk'.comp continuous_subtypeVal)).tendsto z₀
  · obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 i.property
    obtain ⟨D, hcell, hgξ⟩ := σ.exists_cuspDatum_vertexZeroCell hmap hlf hξ
    rw [ContinuousAt, hx₀, facePoint, hcell]
    refine (nhds_basis_cuspNhd D 0).tendsto_right_iff.2 fun A _ ↦ ?_
    have hx₀_eq : diskHomeo x₀ = diskEquiv P (.inr i) := by rw [← hx₀, diskEquiv_faceEquiv]
    have hpull : Filter.Tendsto diskHomeo (𝓝 x₀) (𝓝 (diskEquiv P (.inr i))) :=
      hx₀_eq ▸ diskHomeo.continuous.tendsto x₀
    filter_upwards [hpull.eventually (hhoro i hξ hgξ A)] with x hx
    rcases hx with heq | ⟨z, hz, hAz⟩
    · have hfe : faceEquiv P x = .inr i := by simp [faceEquiv, diskEquiv, heq]
      rw [hfe, facePoint, hcell]; exact ofCusp_mem_cuspNhd D A
    · have hfe : faceEquiv P x = .inl z := by simp [faceEquiv, diskEquiv, ← hz]
      rw [hfe, facePoint]
      exact (ofQuotient_mem_cuspNhd_iff D A).mpr ⟨z, (mem_horodisc D).2 hAz, rfl⟩

/-! ### Assembling the finite CW structure -/

variable (Γ) in
private abbrev Cell : ℕ → Type
  | 0 => σ.zeroCells Γ
  | 1 => σ.SideRepresentative
  | 2 => PUnit
  | _ + 3 => PEmpty

private def cellMap : (m : ℕ) → σ.Cell Γ m → PartialEquiv (Fin m → ℝ) Γ.CompactifiedQuotient
  | 0, q => .single 0 q.val
  | 1, i => InjOn.toPartialEquiv _ _ (σ.injOn_edgeMap hmap hlf hdisj i)
  | 2, _ => InjOn.toPartialEquiv _ _ (σ.injOn_faceMap hmap hlf hdisj)
  | _ + 3, i => PEmpty.elim i

private theorem image_cellMap_zero (q : σ.Cell Γ 0) {s : Set (Fin 0 → ℝ)} (hs : s.Nonempty) :
    σ.cellMap hmap hlf hdisj 0 q '' s = {q.val} := hs.image_const _

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
    exact P.quotientMk_notMem_image_interior_of_mem_frontier hdisj
      (P.side_subset_frontier_carrier j
        (P.mem_side_of_vertex_eq_inl (Sum.inl_getLeft _ j.property).symm))
      (ofQuotient_injective heq ▸ hmem)
  · rintro ⟨_, hmem, heq⟩
    exact P.quotientMk_notMem_image_interior_of_mem_frontier hdisj
      (P.side_subset_frontier_carrier i (σ.selfPairedSideFixedPoint_spec i).1)
      (ofQuotient_injective heq ▸ hmem)
  · rintro ⟨_, -, heq⟩; cases heq

private theorem pairwiseDisjoint_cellMap :
    (univ : Set (Σ m, σ.Cell Γ m)).PairwiseDisjoint
      fun c ↦ σ.cellMap hmap hlf hdisj c.1 c.2 '' ball 0 1 := by
  have hb0 : (ball (0 : Fin 0 → ℝ) 1).Nonempty := ⟨0, mem_ball_self one_pos⟩
  have h01 (q : σ.Cell Γ 0) (i : σ.Cell Γ 1) : Disjoint
      (σ.cellMap hmap hlf hdisj 0 q '' ball 0 1) (σ.cellMap hmap hlf hdisj 1 i '' ball 0 1) := by
    rw [σ.image_cellMap_zero hmap hlf hdisj q hb0, coe_cellMap_one, σ.image_edgeMap_ball,
      disjoint_singleton_left]
    rintro ⟨u, hu, h⟩; exact σ.ofQuotient_mk_edgeArc_notMem_zeroCells hmap hdisj hu (h ▸ q.property)
  have h02 (q : σ.Cell Γ 0) (i : σ.Cell Γ 2) : Disjoint
      (σ.cellMap hmap hlf hdisj 0 q '' ball 0 1) (σ.cellMap hmap hlf hdisj 2 i '' ball 0 1) := by
    rw [σ.image_cellMap_zero hmap hlf hdisj q hb0, coe_cellMap_two, disjoint_singleton_left]
    exact σ.zeroCell_notMem_image_faceMap_ball hmap hlf hdisj q.property
  have h12 (i : σ.Cell Γ 1) (k : σ.Cell Γ 2) : Disjoint
      (σ.cellMap hmap hlf hdisj 1 i '' ball 0 1) (σ.cellMap hmap hlf hdisj 2 k '' ball 0 1) := by
    rw [coe_cellMap_one, coe_cellMap_two, σ.image_edgeMap_ball, σ.image_faceMap_ball, disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨_, hmem, heq⟩
    exact P.quotientMk_notMem_image_interior_of_mem_frontier hdisj
      (P.side_subset_frontier_carrier i.val (σ.edgeArc_mem_side i.val hu))
      (ofQuotient_injective heq ▸ hmem)
  rintro ⟨m, c⟩ - ⟨m', c'⟩ - hne
  match m, c, m', c' with
  | 0, q, 0, q' =>
    rw [Function.onFun, σ.image_cellMap_zero hmap hlf hdisj q hb0,
      σ.image_cellMap_zero hmap hlf hdisj q' hb0, disjoint_singleton]
    exact fun h ↦ hne (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  | 0, q, 1, i => exact h01 q i
  | 1, i, 0, q => exact (h01 q i).symm
  | 0, q, 2, i => exact h02 q i
  | 2, i, 0, q => exact (h02 q i).symm
  | 1, i, 2, k => exact h12 i k
  | 2, k, 1, i => exact (h12 i k).symm
  | 1, i, 1, j =>
    exact σ.disjoint_image_edgeMap_ball hmap hlf hdisj fun h ↦ hne (Sigma.ext rfl (heq_of_eq h))
  | 2, ⟨⟩, 2, ⟨⟩ => exact absurd rfl hne
  | _ + 3, i, _, _ | _, _, _ + 3, i => exact PEmpty.elim i

private theorem mapsTo_cellMap :
    ∀ (m : ℕ) (c : σ.Cell Γ m), MapsTo (σ.cellMap hmap hlf hdisj m c) (sphere 0 1)
      (⋃ (k < m) (c' : σ.Cell Γ k), σ.cellMap hmap hlf hdisj k c' '' closedBall 0 1)
  | 0, _ => fun _ hx ↦ ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim
  | 1, i => fun x hx ↦ mem_iUnion₂.2 ⟨0, zero_lt_one, mem_iUnion.2
      ⟨⟨_, σ.edgeMap_mem_zeroCells hmap hlf i hx⟩,
        (σ.image_cellMap_zero hmap hlf hdisj _ ⟨0, mem_closedBall_self zero_le_one⟩).symm ▸ rfl⟩⟩
  | 2, _ => fun x hx ↦ by
    rcases σ.faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere hmap hlf hx with hz0 | ⟨i, hi⟩
    · exact mem_iUnion₂.2 ⟨0, zero_lt_two, mem_iUnion.2
        ⟨⟨_, hz0⟩,
          (σ.image_cellMap_zero hmap hlf hdisj _ ⟨0, mem_closedBall_self zero_le_one⟩).symm ▸ rfl⟩⟩
    · exact mem_iUnion₂.2 ⟨1, one_lt_two, mem_iUnion.2 ⟨i, image_mono ball_subset_closedBall hi⟩⟩
  | _ + 3, i => PEmpty.elim i

private theorem iUnion_image_cellMap :
    ⋃ (m : ℕ) (c : σ.Cell Γ m), σ.cellMap hmap hlf hdisj m c '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  cases p with
  | ofCusp C =>
    exact mem_iUnion₂.2 ⟨0, ⟨ofCusp C, Or.inr ⟨C, rfl⟩⟩,
      (σ.image_cellMap_zero hmap hlf hdisj _ ⟨0, mem_closedBall_self zero_le_one⟩).symm ▸ rfl⟩
  | ofQuotient q =>
    obtain ⟨w, rfl⟩ := Quotient.mk''_surjective q
    obtain ⟨γ, z, hz, rfl⟩ :=
      mem_iUnion.1 ((σ.iUnion_smul_carrier_eq_univ hmap hlf).symm ▸ mem_univ w)
    let u := (faceEquiv P).symm (.inl ⟨z, hz⟩)
    refine mem_iUnion₂.2 ⟨2, ⟨⟩, u, u.property, ?_⟩
    rw [coe_cellMap_two, σ.faceMap_of_mem hmap hlf u, Equiv.apply_symm_apply]
    exact congrArg ofQuotient (Quotient.sound (mem_orbit z γ)).symm

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
    exact σ.ofQuotient_mk_edgeArc_notMem_zeroCells hmap hdisj hu
      (h ▸ σ.edgeMap_mem_zeroCells hmap hlf i hx)
  | 2, _ => by
    refine (σ.continuousOn_faceMap hmap hlf).continuousOn_invFunOn_image_of_isCompact
      (isCompact_closedBall 0 1) ball_subset_closedBall (σ.injOn_faceMap hmap hlf hdisj) ?_
    rw [closedBall_sdiff_ball, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hmem
    rcases σ.faceMap_mem_zeroCells_or_edgeMap_of_mem_sphere hmap hlf hx with hz0 | ⟨i, hi⟩
    · exact σ.zeroCell_notMem_image_faceMap_ball hmap hlf hdisj hz0 hmem
    · rw [σ.image_edgeMap_ball] at hi; obtain ⟨u, hu, hu_eq⟩ := hi
      rw [← hu_eq, σ.image_faceMap_ball] at hmem; obtain ⟨_, hint, heq⟩ := hmem
      exact P.quotientMk_notMem_image_interior_of_mem_frontier hdisj
        (P.side_subset_frontier_carrier i.val (σ.edgeArc_mem_side i.val hu))
        (ofQuotient_injective heq ▸ hint)
  | _ + 3, i => PEmpty.elim i

@[instance_reducible]
private def cwComplex : CWComplex (univ : Set Γ.CompactifiedQuotient) :=
  CWComplex.mkFinite univ (σ.Cell Γ) (σ.cellMap hmap hlf hdisj)
    (Filter.eventually_atTop.2 ⟨3, fun m hm ↦ by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm; exact inferInstanceAs (IsEmpty PEmpty)⟩)
    (fun
      | 0 => (σ.finite_zeroCells hmap hlf).to_subtype
      | 1 => inferInstanceAs (Finite σ.SideRepresentative)
      | 2 => inferInstanceAs (Finite PUnit)
      | _ + 3 => inferInstanceAs (Finite PEmpty))
    (fun
      | 0, _ => by ext x; simp [cellMap, Subsingleton.elim x 0]
      | 1, _ | 2, _ => rfl
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

-- `CWComplex.mkFinite` stores `σ.Cell Γ` as its `cell` family definitionally.
private theorem cell_cwComplex (m : ℕ) :
    letI := σ.cwComplex hmap hlf hdisj
    cell (univ : Set Γ.CompactifiedQuotient) m = σ.Cell Γ m :=
  (rfl)

private theorem finite_cwComplex :
    letI := σ.cwComplex hmap hlf hdisj
    RelCWComplex.Finite (univ : Set Γ.CompactifiedQuotient) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-! ### Finite CW type, Euler characteristic, genus, and signature area formula -/

include hmap hlf hdisj in
/-- **The compactified quotient by a fundamental polygon has finite CW type.** -/
theorem finiteCWType_compactifiedQuotient : FiniteCWType Γ.CompactifiedQuotient := by
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  exact (Homeomorph.Set.univ _).symm.finiteCWType

/-- **The Euler characteristic of the compactified quotient by a fundamental polygon** is
`χ(X(Γ)) = V + c + k - E + 1`. -/
theorem eulerChar_compactifiedQuotient :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1 := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  let := σ.cwComplex hmap hlf hdisj
  have := σ.finite_cwComplex hmap hlf hdisj
  have hcell (m : ℕ) := σ.cell_cwComplex hmap hlf hdisj m
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ _).symm.toHomotopyEquiv,
    cwEulerChar_eq_sum_range (C := (univ : Set Γ.CompactifiedQuotient)) (N := 3) fun m hm ↦ by
      rw [hcell m]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm; exact inferInstanceAs (IsEmpty PEmpty)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hcell,
    Cell, Nat.card_unique, σ.natCard_zeroCells hmap hlf hdisj]
  push_cast; ring

/-- `χ(Γ.CompactifiedQuotient) = σ.toPermutationTriple.eulerChar`. -/
theorem eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient = σ.toPermutationTriple.eulerChar := by
  rw [σ.eulerChar_compactifiedQuotient hmap hlf hdisj, σ.eulerChar_toPermutationTriple]

/-- **The genus bridge for a cuspidal fundamental polygon:** `χ(X(Γ)) = 2 - 2 · genus X(Γ)`. -/
theorem eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    eulerChar Γ.CompactifiedQuotient = 2 - 2 * RiemannSurface.genus Γ.CompactifiedQuotient := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  rw [RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff,
    σ.eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple hmap hlf hdisj]
  exact ⟨σ.isConnected_toPermutationTriple.eulerChar_le_two, σ.toPermutationTriple.even_eulerChar⟩

/-- **The topological genus of `Γ.CompactifiedQuotient`** equals `σ.toPermutationTriple.genus`. -/
theorem genus_compactifiedQuotient_eq :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    RiemannSurface.genus Γ.CompactifiedQuotient = σ.toPermutationTriple.genus := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  apply RiemannSurface.genus_eq_of_eulerChar_eq
  rw [σ.eulerChar_compactifiedQuotient_eq_eulerChar_toPermutationTriple hmap hlf hdisj,
    ← σ.isConnected_toPermutationTriple.two_sub_two_mul_genus]

/-- **The orbifold area formula through the Euler characteristic:**
`covolume Γ ℍ = 2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ) + c)`. -/
theorem covolume_eq_two_pi_mul_neg_eulerChar_add_cusps :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi * (-(eulerChar Γ.CompactifiedQuotient : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
        Nat.card Γ.CuspOrbit)) := by
  rw [σ.covolume_eq_two_pi_mul hmap hlf hdisj, σ.eulerChar_compactifiedQuotient hmap hlf hdisj,
    σ.natCard_cuspOrbit hmap hlf hdisj]
  have hE : (2 * Nat.card σ.SideRepresentative : ℝ) = n + Nat.card {i : Fin n // σ.pair i = i} := by
    exact_mod_cast σ.two_mul_natCard_sideRepresentative
  congr 2; push_cast; linarith

/-- **The signature area formula for a fundamental polygon:**
`covolume Γ ℍ = 2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + c)`. -/
theorem covolume_eq_two_pi_mul_signature :
    haveI := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi *
      (2 * (RiemannSurface.genus Γ.CompactifiedQuotient : ℝ) - 2 +
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
          Nat.card Γ.CuspOrbit)) := by
  have := σ.finiteCWType_compactifiedQuotient hmap hlf hdisj
  rw [σ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps hmap hlf hdisj,
    σ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus hmap hlf hdisj]
  congr 2; push_cast; ring

end Discrete

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

end
