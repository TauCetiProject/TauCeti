/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Elliptic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Orbit
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Elliptic orbits extracted from a fundamental polygon

For a side-paired convex polygon whose translates cover the upper half-plane and have disjoint
interiors, the elliptic orbits are exactly the nontrivial finite vertex cycles together with
one orbit for each self-paired side. The latter orbits have order two and are distinct from all
vertex orbits. Finite vertex cycles of order one are excluded.

The classification is an equivalence with the actual elliptic-orbit subtype of the coarse
quotient. Its characteristic equations recover the orbit representatives and their stabilizer
orders, so it supplies both the number and the orders of the elliptic points in an orbifold
signature. Discreteness and compactness are not additional hypotheses.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapters 3–4.
-/

public section

open MulAction Set Topology UpperHalfPlane TauCeti
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

private theorem finiteVertexOrbit_mem_ellipticOrbits_iff
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft}) :
    (Quotient.mk'' ((P.vertex j).getLeft j.2) : orbitRel.Quotient Γ ℍ) ∈
      Γ.ellipticOrbits ↔ σ.cycleMap j ≠ 1 := by
  rw [Γ.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
  exact (σ.stabilizer_eq_bot_iff_cycleMap_eq_one
    (Sum.inl_getLeft (P.vertex j) j.2).symm hmap hdisj).not

private noncomputable def ellipticVertexCycleEquivRange
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.EllipticVertexCycle ≃
      Set.range (fun j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1} ↦
        (Quotient.mk'' ((P.vertex j).getLeft j.2.1) : orbitRel.Quotient Γ ℍ)) := by
  let s : Setoid {i : Fin n // (P.vertex i).isLeft} :=
    Setoid.comap Subtype.val (Equiv.Perm.SameCycle.setoid σ.next)
  let e := σ.finiteVertexCycleEquiv hmap hdisj
  let p : Quotient s → Prop := fun c ↦ (e c).val ∈ Γ.ellipticOrbits
  have hp (j : {i : Fin n // (P.vertex i).isLeft}) : σ.cycleMap j ≠ 1 ↔ p ⟦j⟧ := by
    dsimp only [p, e]
    rw [σ.finiteVertexCycleEquiv_apply]
    exact (σ.finiteVertexOrbit_mem_ellipticOrbits_iff hmap hdisj j).symm
  let flatten := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun i ↦ (P.vertex i).isLeft) (fun i ↦ σ.cycleMap i ≠ 1)
  let unflatten : σ.EllipticVertexCycle ≃
      Quotient (s.comap (Subtype.val : {j : {i : Fin n // (P.vertex i).isLeft} //
        σ.cycleMap j ≠ 1} → _)) :=
    Quotient.congr flatten.symm (fun _ _ ↦ Iff.rfl)
  have hr (q : orbitRel.Quotient Γ ℍ) :
      (q ∈ Set.range (fun j : {i : Fin n // (P.vertex i).isLeft} ↦
        (Quotient.mk'' ((P.vertex j).getLeft j.2) : orbitRel.Quotient Γ ℍ)) ∧
        q ∈ Γ.ellipticOrbits) ↔
      q ∈ Set.range (fun j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1} ↦
        (Quotient.mk'' ((P.vertex j).getLeft j.2.1) : orbitRel.Quotient Γ ℍ)) := by
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨⟨j, j.2, (σ.finiteVertexOrbit_mem_ellipticOrbits_iff hmap hdisj j).mp hj⟩,
        rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨⟨j, j.2.1⟩, rfl⟩,
        (σ.finiteVertexOrbit_mem_ellipticOrbits_iff hmap hdisj ⟨j, j.2.1⟩).mpr j.2.2⟩
  exact unflatten.trans
    (((Equiv.subtypeQuotientEquivQuotientSubtype
      (fun j : {i : Fin n // (P.vertex i).isLeft} ↦ σ.cycleMap j ≠ 1)
      p hp (fun _ _ ↦ Iff.rfl)).symm.trans
      (e.subtypeEquiv (fun _ ↦ Iff.rfl))).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans (Equiv.subtypeEquivRight hr)))

private theorem ellipticVertexCycleEquivRange_apply
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1}) :
    (σ.ellipticVertexCycleEquivRange hmap hdisj (Quotient.mk'' j)).val =
      Quotient.mk'' ((P.vertex j).getLeft j.2.1) := by
  dsimp only [ellipticVertexCycleEquivRange]
  simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, Equiv.subtypeEquiv_apply]
  erw [Quotient.congr_mk, Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk]
  rw [σ.finiteVertexCycleEquiv_apply]
  simp only [Equiv.subtypeSubtypeEquivSubtypeInter_symm_apply_coe_coe]

private theorem ellipticVertexOrbit_mem
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1}) :
    (Quotient.mk'' ((P.vertex j).getLeft j.2.1) : orbitRel.Quotient Γ ℍ) ∈
      Γ.ellipticOrbits := by
  exact (σ.finiteVertexOrbit_mem_ellipticOrbits_iff hmap hdisj ⟨j, j.2.1⟩).mpr j.2.2

private theorem selfPairedSideOrbit_mem
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : {i : Fin n // σ.pair i = i}) :
    (Quotient.mk'' (σ.selfPairedSideFixedPoint i) : orbitRel.Quotient Γ ℍ) ∈
      Γ.ellipticOrbits := by
  obtain ⟨hi, hip, hiq, hfix⟩ := σ.selfPairedSideFixedPoint_spec i
  rw [Γ.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
  intro hbot
  exact ((σ.stabilizer_eq_bot_iff_of_mem_side (hmap i) hdisj hi hip hiq).mp hbot) hfix

private noncomputable def ellipticOrbitMap
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.EllipticVertexCycle ⊕ {i : Fin n // σ.pair i = i} → Γ.ellipticOrbits
  | .inl c => ⟨(σ.ellipticVertexCycleEquivRange hmap hdisj c).val, by
      obtain ⟨j, hj⟩ := (σ.ellipticVertexCycleEquivRange hmap hdisj c).property
      rw [← hj]
      exact σ.ellipticVertexOrbit_mem hmap hdisj j⟩
  | .inr i => ⟨Quotient.mk'' (σ.selfPairedSideFixedPoint i),
      σ.selfPairedSideOrbit_mem hmap hdisj i⟩

private theorem ellipticOrbitMap_apply_inl_mk
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1}) :
    (σ.ellipticOrbitMap hmap hdisj (.inl (Quotient.mk'' j))).val =
      Quotient.mk'' ((P.vertex j).getLeft j.2.1) := by
  exact σ.ellipticVertexCycleEquivRange_apply hmap hdisj j

private theorem ellipticOrbitMap_apply_inr
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : {i : Fin n // σ.pair i = i}) :
    (σ.ellipticOrbitMap hmap hdisj (.inr i)).val =
      Quotient.mk'' (σ.selfPairedSideFixedPoint i) := rfl

private theorem quotientMk_vertex_ne_selfPairedSideFixedPoint
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z)
    (i : {i : Fin n // σ.pair i = i}) :
    (Quotient.mk'' z : orbitRel.Quotient Γ ℍ) ≠
      Quotient.mk'' (σ.selfPairedSideFixedPoint i) := by
  intro heq
  obtain ⟨hi, hip, hiq, hfix⟩ := σ.selfPairedSideFixedPoint_spec i
  have hzi : z = σ.selfPairedSideFixedPoint i :=
    (σ.mem_orbit_iff_eq_of_mem_side_map_smul_eq_self (hmap i) hdisj
      (P.vertex_mem_carrier hz) hi hip hiq hfix).mp
      (orbitRel_apply.mp (Quotient.eq''.mp heq.symm))
  have hside : σ.selfPairedSideFixedPoint i ∈ P.side j :=
    hzi ▸ P.mem_side_of_vertex_eq_inl hz
  by_cases hji : j = i
  · exact hip (hji ▸ hz.trans (congrArg Sum.inl hzi))
  · exact disjoint_left.mp (disjoint_leftHalfPlane_range_geodesicLine _)
      (P.mem_leftHalfPlane_of_mem_side hi hip hiq hji)
      (P.side_subset_range_sideGeodesic _ hside)

private theorem selfPairedSideOrbit_injective
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Injective (fun i : {i : Fin n // σ.pair i = i} ↦
      (Quotient.mk'' (σ.selfPairedSideFixedPoint i) : orbitRel.Quotient Γ ℍ)) := by
  intro i j heq
  obtain ⟨hi, hip, hiq, -⟩ := σ.selfPairedSideFixedPoint_spec i
  obtain ⟨hj, hjp, hjq, hjfix⟩ := σ.selfPairedSideFixedPoint_spec j
  have hij : σ.selfPairedSideFixedPoint i = σ.selfPairedSideFixedPoint j :=
    (σ.mem_orbit_iff_eq_of_mem_side_map_smul_eq_self (hmap j) hdisj
      (P.side_subset_carrier i hi) hj hjp hjq hjfix).mp
      (orbitRel_apply.mp (Quotient.eq''.mp heq.symm))
  apply Subtype.ext
  by_contra hne
  exact disjoint_left.mp (disjoint_leftHalfPlane_range_geodesicLine _)
    (P.mem_leftHalfPlane_of_mem_side hj hjp hjq hne)
    (P.side_subset_range_sideGeodesic _ (hij ▸ hi))

private theorem ellipticOrbitMap_injective
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Injective (σ.ellipticOrbitMap hmap hdisj) := by
  rintro (c | i) (d | j) heq
  · exact congrArg Sum.inl ((σ.ellipticVertexCycleEquivRange hmap hdisj).injective
      (Subtype.ext (congrArg (fun q : Γ.ellipticOrbits ↦ q.val) heq)))
  · obtain ⟨k, hk⟩ := (σ.ellipticVertexCycleEquivRange hmap hdisj c).property
    exact False.elim ((σ.quotientMk_vertex_ne_selfPairedSideFixedPoint hmap hdisj
      (Sum.inl_getLeft (P.vertex k) k.2.1).symm j)
      (hk.trans (congrArg Subtype.val heq)))
  · obtain ⟨k, hk⟩ := (σ.ellipticVertexCycleEquivRange hmap hdisj d).property
    exact False.elim ((σ.quotientMk_vertex_ne_selfPairedSideFixedPoint hmap hdisj
      (Sum.inl_getLeft (P.vertex k) k.2.1).symm i)
      (hk.trans (congrArg Subtype.val heq.symm)))
  · exact congrArg Sum.inr (σ.selfPairedSideOrbit_injective hmap hdisj
      (congrArg Subtype.val heq))

private theorem ellipticOrbitMap_surjective
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Function.Surjective (σ.ellipticOrbitMap hmap hdisj) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn' with | _ z =>
  have hz := (Γ.quotientMk_mem_ellipticOrbits_iff z).mp hq
  have hzbot : stabilizer Γ z ≠ ⊥ := (mem_freeLocus Γ ℍ).not.mp hz
  obtain ⟨w, hworb, hv | ⟨i, -, -, -, hpair, hfix, -⟩⟩ :=
    σ.exists_vertex_or_self_paired_side_of_stabilizer_ne_bot hmap hcover hdisj hzbot
  · obtain ⟨i, hi⟩ := hv
    have hwq : (Quotient.mk'' w : orbitRel.Quotient Γ ℍ) = Quotient.mk'' z :=
      Quotient.sound (orbitRel_apply.mpr hworb)
    have hwbot : stabilizer Γ w ≠ ⊥ := by
      exact (mem_freeLocus Γ ℍ).not.mp
        ((mem_freeLocus_iff_of_quotientMk_eq Γ ℍ hwq).not.mpr hz)
    have hiell : σ.cycleMap i ≠ 1 :=
      (σ.stabilizer_eq_bot_iff_cycleMap_eq_one hi hmap hdisj).not.mp hwbot
    let j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1} :=
      ⟨i, by simp [hi], hiell⟩
    refine ⟨.inl (Quotient.mk'' j), Subtype.ext ?_⟩
    dsimp only [ellipticOrbitMap]
    rw [σ.ellipticVertexCycleEquivRange_apply]
    simpa only [j, hi, Sum.getLeft_inl] using hwq
  · let j : {i : Fin n // σ.pair i = i} := ⟨i, hpair⟩
    refine ⟨.inr j, Subtype.ext ?_⟩
    dsimp only [ellipticOrbitMap]
    rw [σ.selfPairedSideFixedPoint_eq j hfix]
    exact Quotient.sound (orbitRel_apply.mpr hworb)

/-- The elliptic orbits of a fundamental polygon are precisely its nontrivial finite vertex
cycles and its self-paired sides. A self-paired side contributes its unique interior fixed point. -/
noncomputable def ellipticOrbitEquiv
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.EllipticVertexCycle ⊕ {i : Fin n // σ.pair i = i} ≃ Γ.ellipticOrbits :=
  Equiv.ofBijective (σ.ellipticOrbitMap hmap hdisj)
    ⟨σ.ellipticOrbitMap_injective hmap hdisj, σ.ellipticOrbitMap_surjective hmap hcover hdisj⟩

/-- The vertex summand is sent to the actual orbit of the finite vertex. -/
@[simp]
theorem ellipticOrbitEquiv_apply_inl_mk
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1}) :
    (σ.ellipticOrbitEquiv hmap hcover hdisj (.inl (Quotient.mk'' j))).val =
      Quotient.mk'' ((P.vertex j).getLeft j.2.1) := by
  exact (congrArg (fun f ↦ (f (.inl (Quotient.mk'' j))).val)
    (Equiv.coe_ofBijective (σ.ellipticOrbitMap hmap hdisj)
      ⟨σ.ellipticOrbitMap_injective hmap hdisj,
        σ.ellipticOrbitMap_surjective hmap hcover hdisj⟩)).trans
    (σ.ellipticOrbitMap_apply_inl_mk hmap hdisj j)

/-- The side summand is sent to the actual orbit of its unique fixed point. -/
@[simp]
theorem ellipticOrbitEquiv_apply_inr
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : {i : Fin n // σ.pair i = i}) :
    (σ.ellipticOrbitEquiv hmap hcover hdisj (.inr i)).val =
      Quotient.mk'' (σ.selfPairedSideFixedPoint i) := by
  exact (congrArg (fun f ↦ (f (.inr i)).val)
    (Equiv.coe_ofBijective (σ.ellipticOrbitMap hmap hdisj)
      ⟨σ.ellipticOrbitMap_injective hmap hdisj,
        σ.ellipticOrbitMap_surjective hmap hcover hdisj⟩)).trans
    (σ.ellipticOrbitMap_apply_inr hmap hdisj i)

/-- The stabilizer order on the vertex summand is the order of its cycle transformation. -/
@[simp↓]
theorem cardStabilizerOnOrbit_ellipticOrbitEquiv_inl_mk
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (j : {i : Fin n // (P.vertex i).isLeft ∧ σ.cycleMap i ≠ 1}) :
    cardStabilizerOnOrbit (σ.ellipticOrbitEquiv hmap hcover hdisj
      (.inl (Quotient.mk'' j))).val = orderOf (σ.cycleMap j) := by
  rw [σ.ellipticOrbitEquiv_apply_inl_mk, cardStabilizerOnOrbit_mk]
  exact σ.natCard_stabilizer_eq_orderOf_cycleMap
    (Sum.inl_getLeft (P.vertex j) j.2.1).symm hmap hdisj

/-- Every side summand has elliptic stabilizer order two. -/
@[simp↓]
theorem cardStabilizerOnOrbit_ellipticOrbitEquiv_inr
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : {i : Fin n // σ.pair i = i}) :
    cardStabilizerOnOrbit (σ.ellipticOrbitEquiv hmap hcover hdisj (.inr i)).val = 2 := by
  obtain ⟨hi, hip, hiq, hfix⟩ := σ.selfPairedSideFixedPoint_spec i
  rw [σ.ellipticOrbitEquiv_apply_inr, cardStabilizerOnOrbit_mk]
  exact σ.natCard_stabilizer_eq_two_of_mem_side (hmap i) hdisj hi hip hiq hfix

/-- The number of elliptic orbits is the number of nontrivial finite vertex cycles plus
the number of self-paired sides. Neither cusp compactness nor discreteness is needed. -/
theorem natCard_ellipticOrbits
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Nat.card Γ.ellipticOrbits =
      Nat.card σ.EllipticVertexCycle + Nat.card {i : Fin n // σ.pair i = i} := by
  rw [← Nat.card_congr (σ.ellipticOrbitEquiv hmap hcover hdisj), Nat.card_sum]

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
