/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay.Roots
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Two

/-!
# The Leech lattice from the Golay lattice

Keep the Golay lattice vectors pairing evenly with `(-3, 1, …, 1)`, then adjoin the
half-vector `(-3/2, 1/2, …, 1/2)`. The ambient form remains the halved dot product, so the
half-vector has norm four. The module gives explicit membership, rank twenty-four,
positivity, evenness, unimodularity, rootlessness, and a minimum-four witness.

## References

* G. Nebe,
  [*Extremal lattices*](https://www.math.rwth-aachen.de/homes/Gabriele.Nebe/talks/OW12.pdf),
  slide 11, using a sign change at the distinguished coordinate of the Golay two-neighbor.
* R. E. Borcherds, *The Leech lattice and other lattices*, §0.2, for the neighbor and its glue.
-/

public section

namespace TauCeti.Leech

open Matrix

private theorem golay_carrier : BinaryGolay.constructionALattice.carrier =
    ConstructionA.lattice 2 BinaryGolay.code.toAddSubgroup :=
  (congrArg IntegralLattice.carrier BinaryGolay.constructionALattice_eq_integralLattice).trans
    (ConstructionA.integralLattice_carrier 2 BinaryGolay.code.toAddSubgroup
      (TwoPowCode.isTypeII_one_iff.mpr BinaryGolay.isTypeII_code).le_euclideanDual)

private theorem golay_form : BinaryGolay.constructionALattice.form = ConstructionA.form 2 :=
  (congrArg IntegralLattice.form BinaryGolay.constructionALattice_eq_integralLattice).trans
    (ConstructionA.integralLattice_form 2 BinaryGolay.code.toAddSubgroup
      (TwoPowCode.isTypeII_one_iff.mpr BinaryGolay.isTypeII_code).le_euclideanDual)

private def neighborIntVector (i : Fin 24) : ℤ := if i = 0 then -3 else 1

private theorem neighborIntVector_reduction :
    (fun i ↦ (neighborIntVector i : ZMod 2)) = 1 := by
  funext i
  change (neighborIntVector i : ZMod 2) = 1
  rw [neighborIntVector]
  split_ifs <;> decide

/-- The explicit norm-sixteen Golay lattice vector used to form the Leech two-neighbor. -/
def neighborVector : BinaryGolay.constructionALattice :=
  ⟨fun i ↦ (neighborIntVector i : ℚ), by
    rw [golay_carrier]
    apply (ConstructionA.intCast_mem_lattice 2 (C := BinaryGolay.code.toAddSubgroup)
      neighborIntVector).mpr
    change (fun i ↦ (neighborIntVector i : ZMod 2)) ∈ BinaryGolay.code
    rw [neighborIntVector_reduction]
    exact BinaryCode.one_mem_of_isSelfDual BinaryGolay.isSelfDual_code⟩

/-- The neighbor vector has one coordinate `-3` and twenty-three coordinates `1`. -/
@[simp]
theorem neighborVector_apply (i : Fin 24) :
    (neighborVector : Fin 24 → ℚ) i = if i = 0 then -3 else 1 := by
  change ((if i = 0 then -3 else 1 : ℤ) : ℚ) = _
  split_ifs <;> norm_num

/-- The chosen Golay vector has norm sixteen in the halved-dot-product normalization. -/
theorem norm_neighborVector : BinaryGolay.constructionALattice.norm neighborVector = 16 := by
  rw [IntegralLattice.norm_apply, golay_form, ConstructionA.form_apply]
  norm_num [dotProduct, neighborVector_apply, Fin.sum_univ_succ]

/-- The neighbor vector has integral norm sixteen. -/
theorem integralNorm_neighborVector :
    BinaryGolay.constructionALattice.integralNorm neighborVector = 16 := by
  exact_mod_cast (BinaryGolay.constructionALattice.integralNorm_cast neighborVector).trans
    norm_neighborVector

/-- Pairing the neighbor vector with a positive Golay coordinate root gives an odd integer. -/
theorem form_neighborVector_coordinateRoot (i : Fin 24) :
    BinaryGolay.constructionALattice.form neighborVector (BinaryGolay.coordinateRoot i) =
      if i = 0 then -3 else 1 := by
  rw [BinaryGolay.coe_coordinateRoot, golay_form, ConstructionA.form_apply]
  by_cases hi : i = 0 <;> norm_num [dotProduct_single, neighborVector_apply, hi]

/-- The integral pairing with each coordinate root is odd. -/
theorem integralForm_neighborVector_coordinateRoot (i : Fin 24) :
    BinaryGolay.constructionALattice.integralForm neighborVector (BinaryGolay.coordinateRoot i) =
      if i = 0 then -3 else 1 := by
  have h := (BinaryGolay.constructionALattice.integralForm_cast neighborVector
    (BinaryGolay.coordinateRoot i)).trans (form_neighborVector_coordinateRoot i)
  split_ifs at h ⊢ <;> exact_mod_cast h

private theorem eight_dvd_integralNorm_neighborVector :
    (8 : ℤ) ∣ BinaryGolay.constructionALattice.integralNorm neighborVector := by
  rw [integralNorm_neighborVector]
  norm_num

private theorem exists_odd_pairing_neighborVector :
    ∃ w : BinaryGolay.constructionALattice,
      Odd (BinaryGolay.constructionALattice.integralForm neighborVector w) := by
  exact ⟨BinaryGolay.coordinateRoot 0, by rw [integralForm_neighborVector_coordinateRoot]; decide⟩

/-- **The Leech lattice**, with explicit Golay glue and the halved dot product on `ℚ²⁴`. -/
noncomputable def lattice : IntegralLattice (Fin 24 → ℚ) :=
  BinaryGolay.constructionALattice.twoNeighbor BinaryGolay.isEven_constructionALattice
    neighborVector eight_dvd_integralNorm_neighborVector

/-- The Leech lattice carries the same rational coordinate form as the Golay lattice. -/
@[simp]
theorem lattice_form : lattice.form = ConstructionA.form 2 := by
  rw [lattice, IntegralLattice.twoNeighbor_form]
  exact golay_form

/-- The Leech norm is the sum of coordinate squares divided by two. -/
theorem lattice_norm (x : Fin 24 → ℚ) : lattice.norm x = (x ⬝ᵥ x) / 2 := by
  rw [IntegralLattice.norm_apply, lattice_form, ConstructionA.form_apply]
  rfl

/-- Pairing an integer vector with the neighbor vector is half its coordinate sum,
minus twice its distinguished coordinate. -/
theorem form_neighborVector_intCast (z : Fin 24 → ℤ) :
    BinaryGolay.constructionALattice.form neighborVector (fun i ↦ (z i : ℚ)) =
      ((∑ i, z i : ℤ) : ℚ) / 2 - 2 * (z 0 : ℚ) := by
  have hv : (neighborVector : Fin 24 → ℚ) = (fun _ ↦ 1) - Pi.single 0 4 := by
    funext i
    by_cases hi : i = 0 <;> norm_num [neighborVector_apply, hi]
  rw [golay_form, ConstructionA.form_apply, hv, sub_dotProduct, single_dotProduct]
  simp only [dotProduct, one_mul]
  push_cast
  ring

private theorem intCast_mem_neighborKernel_iff (z : Fin 24 → ℤ) :
    (fun i ↦ (z i : ℚ)) ∈ BinaryGolay.constructionALattice.twoNeighborKernel neighborVector ↔
      (fun i ↦ (z i : ZMod 2)) ∈ BinaryGolay.code ∧ (4 : ℤ) ∣ ∑ i, z i := by
  constructor
  · intro hx
    have hxL := BinaryGolay.constructionALattice.twoNeighborKernel_le neighborVector hx
    have hcode := (ConstructionA.intCast_mem_lattice 2 (C := BinaryGolay.code.toAddSubgroup)
      z).mp (golay_carrier ▸ hxL)
    change (fun i ↦ (z i : ZMod 2)) ∈ BinaryGolay.code at hcode
    let y : BinaryGolay.constructionALattice := ⟨fun i ↦ (z i : ℚ), hxL⟩
    have he := (BinaryGolay.constructionALattice.coe_mem_twoNeighborKernel_iff
      neighborVector y).mp hx
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp he
    have hform := BinaryGolay.constructionALattice.integralForm_cast neighborVector y
    change (BinaryGolay.constructionALattice.integralForm neighborVector y : ℚ) =
      BinaryGolay.constructionALattice.form neighborVector (fun i ↦ (z i : ℚ)) at hform
    rw [form_neighborVector_intCast, hk] at hform
    have hsum : ((∑ i, z i : ℤ) : ℚ) = 4 * ((k + z 0 : ℤ) : ℚ) := by
      push_cast at hform ⊢
      linarith
    exact ⟨hcode, ⟨k + z 0, by exact_mod_cast hsum⟩⟩
  · rintro ⟨hcode, k, hk⟩
    have hxL : (fun i ↦ (z i : ℚ)) ∈ BinaryGolay.constructionALattice.carrier := by
      rw [golay_carrier]
      exact (ConstructionA.intCast_mem_lattice 2 (C := BinaryGolay.code.toAddSubgroup) z).mpr hcode
    let y : BinaryGolay.constructionALattice := ⟨fun i ↦ (z i : ℚ), hxL⟩
    apply (BinaryGolay.constructionALattice.coe_mem_twoNeighborKernel_iff neighborVector y).mpr
    have hform := BinaryGolay.constructionALattice.integralForm_cast neighborVector y
    change (BinaryGolay.constructionALattice.integralForm neighborVector y : ℚ) =
      BinaryGolay.constructionALattice.form neighborVector (fun i ↦ (z i : ℚ)) at hform
    rw [form_neighborVector_intCast, hk] at hform
    have hint : BinaryGolay.constructionALattice.integralForm neighborVector y =
        2 * (k - z 0) := by
      have hq : (BinaryGolay.constructionALattice.integralForm neighborVector y : ℚ) =
          ((2 * (k - z 0) : ℤ) : ℚ) := by
        push_cast at hform ⊢
        linarith
      exact_mod_cast hq
    exact even_iff_two_dvd.mpr ⟨k - z 0, hint⟩

private theorem mem_neighborKernel_iff (x : Fin 24 → ℚ) :
    x ∈ BinaryGolay.constructionALattice.twoNeighborKernel neighborVector ↔
      ∃ z : Fin 24 → ℤ, (fun i ↦ (z i : ZMod 2)) ∈ BinaryGolay.code ∧
        (4 : ℤ) ∣ ∑ i, z i ∧ (fun i ↦ (z i : ℚ)) = x := by
  constructor
  · intro hx
    have hxL := BinaryGolay.constructionALattice.twoNeighborKernel_le neighborVector hx
    obtain ⟨z, _, rfl⟩ := (ConstructionA.mem_lattice 2).mp (golay_carrier ▸ hxL)
    obtain ⟨hz, hsum⟩ := (intCast_mem_neighborKernel_iff z).mp hx
    exact ⟨z, hz, hsum, rfl⟩
  · rintro ⟨z, hz, hsum, rfl⟩
    exact (intCast_mem_neighborKernel_iff z).mpr ⟨hz, hsum⟩

/-- **Explicit Leech membership**: an integer lift of a Golay codeword whose coordinate
sum is divisible by four, or its translate by `(-3/2, 1/2, …, 1/2)`. -/
theorem mem_lattice_iff (x : Fin 24 → ℚ) : x ∈ lattice.carrier ↔
    ∃ z : Fin 24 → ℤ, (fun i ↦ (z i : ZMod 2)) ∈ BinaryGolay.code ∧
      (4 : ℤ) ∣ ∑ i, z i ∧
        (x = (fun i ↦ (z i : ℚ)) ∨
          x = (fun i ↦ (z i : ℚ)) + (1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ)) := by
  rw [lattice, IntegralLattice.mem_twoNeighbor_carrier_iff_mem_or_sub_half_mem]
  constructor
  · rintro (hx | hx)
    · obtain ⟨z, hz, hs, heq⟩ := (mem_neighborKernel_iff x).mp hx
      exact ⟨z, hz, hs, Or.inl heq.symm⟩
    · obtain ⟨z, hz, hs, heq⟩ := (mem_neighborKernel_iff _).mp hx
      refine ⟨z, hz, hs, Or.inr ?_⟩
      rw [heq, sub_add_cancel]
  · rintro ⟨z, hz, hs, rfl | rfl⟩
    · exact Or.inl ((intCast_mem_neighborKernel_iff z).mpr ⟨hz, hs⟩)
    · exact Or.inr (by
        rw [add_sub_cancel_right]
        exact (intCast_mem_neighborKernel_iff z).mpr ⟨hz, hs⟩)

/-- The Leech lattice is nondegenerate. -/
instance instIsNondegenerateLattice : lattice.IsNondegenerate := by
  rw [lattice]
  infer_instance

/-- The Leech lattice has rank twenty-four. -/
theorem finrank_lattice : Module.finrank ℤ lattice = 24 := by
  rw [lattice, IntegralLattice.finrank_twoNeighbor, BinaryGolay.finrank_constructionALattice]

/-- The Leech lattice is positive definite. -/
theorem isPosDef_lattice : lattice.IsPosDef := by
  rw [lattice]
  exact (BinaryGolay.constructionALattice.isPosDef_twoNeighbor_iff _ _ _).mpr
    BinaryGolay.isPosDef_constructionALattice

/-- The Leech lattice is even. -/
theorem isEven_lattice : lattice.IsEven := by
  rw [lattice]
  exact IntegralLattice.isEven_twoNeighbor _ _ _ _

/-- The Leech lattice is unimodular. -/
theorem isUnimodular_lattice : lattice.IsUnimodular := by
  rw [lattice]
  exact IntegralLattice.isUnimodular_twoNeighbor _ _ BinaryGolay.isUnimodular_constructionALattice
    _ _ exists_odd_pairing_neighborVector

/-- The explicit half-vector `(-3/2, 1/2, …, 1/2)` in the Leech lattice. -/
noncomputable def minimumVector : lattice :=
  ⟨(1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ),
    BinaryGolay.constructionALattice.half_mem_twoNeighbor_carrier
      BinaryGolay.isEven_constructionALattice neighborVector eight_dvd_integralNorm_neighborVector⟩

/-- The coordinates of the explicit minimum-four witness. -/
@[simp]
theorem coe_minimumVector :
    (minimumVector : Fin 24 → ℚ) = (1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ) := by
  rw [minimumVector]

/-- The glued half-vector has norm four. -/
theorem norm_minimumVector : lattice.norm minimumVector = 4 := by
  rw [coe_minimumVector, lattice, IntegralLattice.twoNeighbor_norm,
    IntegralLattice.norm_smul, norm_neighborVector]
  norm_num

/-- The glued half-vector has integral norm four. -/
theorem integralNorm_minimumVector : lattice.integralNorm minimumVector = 4 := by
  exact_mod_cast (lattice.integralNorm_cast minimumVector).trans norm_minimumVector

private theorem quarter_le_sq_add_half (z : ℤ) : (1 / 4 : ℚ) ≤ ((z : ℚ) + 1 / 2) ^ 2 := by
  have hz : z ≤ -1 ∨ 0 ≤ z := by omega
  rcases hz with hz | hz
  · have hq : (z : ℚ) ≤ -1 := by exact_mod_cast hz
    nlinarith
  · have hq : (0 : ℚ) ≤ z := by exact_mod_cast hz
    nlinarith

private theorem three_le_norm_intCast_add_half (z : Fin 24 → ℤ) :
    3 ≤ lattice.norm ((fun i ↦ (z i : ℚ)) +
      (1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ)) := by
  let x := (fun i ↦ (z i : ℚ)) + (1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ)
  have hcoord (i : Fin 24) :
      x i = ((z i + if i = 0 then -2 else 0 : ℤ) : ℚ) + 1 / 2 := by
    by_cases hi : i = 0
    · simp [x, neighborVector_apply, hi]
      ring
    · simp [x, neighborVector_apply, hi]
  have hsum : (6 : ℚ) ≤ ∑ i, x i ^ 2 := by
    calc
      6 = ∑ _ : Fin 24, (1 / 4 : ℚ) := by norm_num
      _ ≤ ∑ i, x i ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [hcoord]
        exact quarter_le_sq_add_half _
  rw [lattice_norm]
  change 3 ≤ (∑ i, x i * x i) / 2
  simp only [← pow_two] at *
  linarith

/-- **The Leech lattice has no roots:** none of its vectors has norm two. -/
theorem norm_ne_two {x : Fin 24 → ℚ} (hx : x ∈ lattice.carrier) : lattice.norm x ≠ 2 := by
  intro hnorm
  have hg : BinaryGolay.constructionALattice.norm x = 2 := by
    simpa only [lattice, IntegralLattice.twoNeighbor_norm] using hnorm
  rcases (BinaryGolay.constructionALattice.mem_twoNeighbor_carrier_iff_mem_or_sub_half_mem
    BinaryGolay.isEven_constructionALattice neighborVector
    eight_dvd_integralNorm_neighborVector x).mp hx with hx | hx
  · have hxL := BinaryGolay.constructionALattice.twoNeighborKernel_le neighborVector hx
    obtain ⟨i, rfl | rfl⟩ := (BinaryGolay.norm_eq_two_iff hxL).mp hg
    · have he := (BinaryGolay.constructionALattice.coe_mem_twoNeighborKernel_iff neighborVector
        (BinaryGolay.coordinateRoot i)).mp (by
          simpa only [BinaryGolay.coe_coordinateRoot] using hx)
      rw [integralForm_neighborVector_coordinateRoot] at he
      split_ifs at he <;> simp only [even_iff_two_dvd] at he <;> omega
    · have he := (BinaryGolay.constructionALattice.coe_mem_twoNeighborKernel_iff neighborVector
        (-BinaryGolay.coordinateRoot i)).mp (by
          simpa only [Submodule.coe_neg, BinaryGolay.coe_coordinateRoot] using hx)
      rw [map_neg, integralForm_neighborVector_coordinateRoot] at he
      split_ifs at he <;> simp only [even_iff_two_dvd] at he <;> omega
  · have hxL := BinaryGolay.constructionALattice.twoNeighborKernel_le neighborVector hx
    have hxC : x - (1 / 2 : ℚ) • (neighborVector : Fin 24 → ℚ) ∈
        ConstructionA.lattice 2 BinaryGolay.code.toAddSubgroup := by
      simpa only [golay_carrier] using hxL
    obtain ⟨z, _, hz⟩ := (ConstructionA.mem_lattice 2).mp hxC
    have hge := three_le_norm_intCast_add_half z
    rw [hz, sub_add_cancel, hnorm] at hge
    norm_num at hge

/-- The norm-two shell of the actual Leech lattice is empty. -/
theorem vectorsOfNorm_two_eq_empty : lattice.vectorsOfNorm 2 = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  exact norm_ne_two x.2 (IntegralLattice.mem_vectorsOfNorm.mp hx)

/-- The Leech lattice represents two zero times. -/
theorem representationNumber_lattice_two : lattice.representationNumber 2 = 0 := by
  rw [IntegralLattice.representationNumber_def, vectorsOfNorm_two_eq_empty, Set.ncard_empty]

/-- The minimum of the actual Leech lattice is four. -/
theorem minimum_lattice : lattice.minimum = 4 := by
  have hv : minimumVector ≠ 0 := by
    intro h
    have hn := integralNorm_minimumVector
    rw [h, IntegralLattice.integralNorm_zero] at hn
    norm_num at hn
  let : Nontrivial lattice := nontrivial_of_ne minimumVector 0 hv
  have hle := isPosDef_lattice.isPosSemidef.minimum_le_integralNorm hv
  rw [integralNorm_minimumVector] at hle
  have hge := isPosDef_lattice.two_le_minimum isEven_lattice
  obtain ⟨x, _, hx⟩ := isPosDef_lattice.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  have he := (lattice.even_integralNorm_iff x).mpr (isEven_lattice.exists_norm_eq_two_mul x)
  have hne : lattice.minimum ≠ 2 := by
    intro h
    have hn : lattice.norm x = 2 := by
      rw [← lattice.integralNorm_cast, hx, h]
      norm_num
    exact norm_ne_two x.2 hn
  rw [hx, even_iff_two_dvd] at he
  omega

/-- The Golay `A₁²⁴` row and the rootless Leech row are not isometric, since their
norm-two shells have different cardinalities. -/
theorem not_nonempty_isometry_golay :
    ¬Nonempty (IntegralLattice.Isometry BinaryGolay.constructionALattice lattice) := by
  rintro ⟨e⟩
  have h := e.representationNumber_eq 2
  rw [BinaryGolay.representationNumber_constructionALattice_two,
    representationNumber_lattice_two] at h
  norm_num at h

end TauCeti.Leech
