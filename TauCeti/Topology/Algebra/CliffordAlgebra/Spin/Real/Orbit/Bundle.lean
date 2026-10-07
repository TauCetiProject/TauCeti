/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SphereSection
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Orbit.Homeomorph
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection

/-!
# The compact Spin sphere bundle

The orbit of the last coordinate unit vector packages the classical locally trivial bundle

`Spin(n) → Spin(n + 1) → Sⁿ`.

Near the last unit vector, the explicit reflection-pair section gives a quotient chart. The
stabilizer of that vector is topologically isomorphic to `Spin(n)`, so the chart has the expected
fiber. Transitivity moves this chart over every point of the unit level.

## Main declarations

* `CliffordAlgebra.realCliffordSpinLastUnit` is the last coordinate unit vector in the compact
  unit level.
* `CliffordAlgebra.isFiberBundle_realCliffordSpinOrbitMap` gives a local trivialization of the
  compact Spin orbit map around every base point.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 6.
-/

open Set Topology

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The last coordinate unit vector as a point of the compact real Clifford unit level. -/
def realCliffordSpinLastUnit (n : ℕ) : realCliffordUnitLevel (n + 1) :=
  ⟨Pi.single (Fin.last n) 1, by
    rw [mem_realCliffordUnitLevel]
    exact realCliffordForm_zero_single_one (n + 1) (Fin.last n)⟩

/-- The compact Spin last unit has the expected coordinate vector. -/
@[simp]
theorem coe_realCliffordSpinLastUnit (n : ℕ) :
    (realCliffordSpinLastUnit n : Fin (n + 1) → ℝ) = Pi.single (Fin.last n) 1 :=
  (rfl)

private theorem stabilizer_realCliffordSpinLastUnit (n : ℕ) :
    MulAction.stabilizer (realCliffordSpinGroupZero (n + 1))
        (realCliffordSpinLastUnit n) =
      realCliffordSpinLastStabilizer n := by
  ext s
  rw [MulAction.mem_stabilizer_iff, mem_realCliffordSpinLastStabilizer_iff]
  constructor
  · intro hs
    simpa only [coe_realCliffordSpinLastUnit, SubMulAction.val_smul,
      spinGroup_smul_apply] using congrArg Subtype.val hs
  · intro hs
    apply Subtype.ext
    simpa only [coe_realCliffordSpinLastUnit, SubMulAction.val_smul,
      spinGroup_smul_apply] using hs

private theorem realCliffordSpinLastUnit_mem_neighborhood (n : ℕ) :
    realCliffordUnitLevelHomeomorphSubtype (n + 1) (realCliffordSpinLastUnit n) ∈
      realCliffordSpinLastUnitNeighborhood n := by
  rw [mem_realCliffordSpinLastUnitNeighborhood]
  intro h
  have hlast := congrFun h (Fin.last n)
  simp only [coe_realCliffordUnitLevelHomeomorphSubtype_apply,
    coe_realCliffordSpinLastUnit, Pi.single_eq_same, Pi.neg_apply] at hlast
  norm_num at hlast

private noncomputable def realCliffordSpinBaseTrivializationData (n : ℕ) [NeZero n] :
    {e : Bundle.Trivialization (realCliffordSpinGroupZero n)
        (realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n)) //
      realCliffordSpinLastUnit n ∈ e.baseSet} := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hn : 2 ≤ n + 1 := by omega
  let H := MulAction.stabilizer (realCliffordSpinGroupZero (n + 1))
    (realCliffordSpinLastUnit n)
  let hOrbit := realCliffordSpinOrbitHomeomorph (n + 1) hn
    (realCliffordSpinLastUnit n)
  let hCarrier := realCliffordUnitLevelHomeomorphSubtype (n + 1)
  let U : Set (realCliffordSpinGroupZero (n + 1) ⧸ H) :=
    (hCarrier ∘ hOrbit) ⁻¹' realCliffordSpinLastUnitNeighborhood n
  let localSection : realCliffordSpinGroupZero (n + 1) ⧸ H →
      realCliffordSpinGroupZero (n + 1) := fun q =>
    realCliffordSpinLastLocalSection n (hCarrier (hOrbit q))
  have hU : IsOpen U :=
    (isOpen_realCliffordSpinLastUnitNeighborhood n).preimage
      (hCarrier.continuous.comp hOrbit.continuous)
  have hsection : ContinuousOn localSection U :=
    (continuousOn_realCliffordSpinLastLocalSection n).comp
      (hCarrier.continuous.comp hOrbit.continuous).continuousOn (fun _ hq => hq)
  have hsection_mk : ∀ q ∈ U,
      (localSection q : realCliffordSpinGroupZero (n + 1) ⧸ H) = q := by
    intro q hq
    apply hOrbit.injective
    rw [realCliffordSpinOrbitHomeomorph_mk]
    apply Subtype.ext
    simpa only [SubMulAction.val_smul, spinGroup_smul_apply,
      coe_realCliffordSpinLastUnit, localSection, hCarrier,
      coe_realCliffordUnitLevelHomeomorphSubtype_apply] using
      realCliffordSpinLastLocalSection_action (hCarrier (hOrbit q)) hq
  let e := Subgroup.localSectionTrivialization H U hU localSection hsection hsection_mk
  have hH : H = realCliffordSpinLastStabilizer n :=
    stabilizer_realCliffordSpinLastUnit n
  let stabilizerHomeomorph : H ≃ₜ realCliffordSpinLastStabilizer n :=
    Homeomorph.ofEqSubtypes (by
      funext s
      apply propext
      rw [hH])
  let fiberHomeomorph : H ≃ₜ realCliffordSpinGroupZero n :=
    stabilizerHomeomorph.trans
      (realCliffordSpinContinuousMulEquivLastStabilizer n).symm.toHomeomorph
  let e' := (e.homeomorphComp hOrbit).transFiberHomeomorph fiberHomeomorph
  have he_baseSet : e.baseSet = U := by
    dsimp only [e]
    exact Subgroup.localSectionTrivialization_baseSet H U hU localSection hsection hsection_mk
  have he'_baseSet : e'.baseSet = hOrbit.symm ⁻¹' U := by
    dsimp only [e', Bundle.Trivialization.transFiberHomeomorph,
      Bundle.Trivialization.homeomorphComp]
    rw [he_baseSet]
  have hproj : hOrbit ∘ (QuotientGroup.mk : realCliffordSpinGroupZero (n + 1) → _) =
      realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n) := by
    funext s
    simpa only [Function.comp_apply, hOrbit, realCliffordSpinOrbitMap_apply] using
      realCliffordSpinOrbitHomeomorph_mk (n + 1) hn
        (realCliffordSpinLastUnit n) s
  rw [← hproj]
  refine ⟨e', ?_⟩
  rw [he'_baseSet]
  dsimp only [U]
  simpa only [hCarrier, Set.mem_preimage, Function.comp_apply,
    Homeomorph.apply_symm_apply] using
    realCliffordSpinLastUnit_mem_neighborhood n

/-- For positive `n`, the orbit map `Spin(n + 1) → Sⁿ` through the last coordinate unit vector is
locally trivial with fiber `Spin(n)`. Here the sphere is represented by the unit level of the
positive-definite real Clifford form. -/
theorem isFiberBundle_realCliffordSpinOrbitMap (n : ℕ) [NeZero n] :
    ∀ y : realCliffordUnitLevel (n + 1),
      ∃ e : Bundle.Trivialization (realCliffordSpinGroupZero n)
        (realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n)),
        y ∈ e.baseSet := by
  intro y
  have hn0 : n ≠ 0 := NeZero.ne n
  have hn : 2 ≤ n + 1 := by omega
  let _ : MulAction.IsPretransitive (realCliffordSpinGroupZero (n + 1))
      (realCliffordUnitLevel (n + 1)) :=
    isPretransitive_realCliffordUnitLevel (n + 1) hn
  obtain ⟨g, rfl⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := realCliffordSpinGroupZero (n + 1)) (realCliffordSpinLastUnit n) y
  let e₀ := (realCliffordSpinBaseTrivializationData n).1
  let _ : ContinuousSMul (realCliffordSpinGroupZero (n + 1)) (Fin (n + 1) → ℝ) :=
    ⟨by simpa only [spinGroup_smul_apply] using
      continuous_spinVectorAction (realCliffordForm (n + 1) 0)⟩
  let hBase := (Homeomorph.smul g : realCliffordUnitLevel (n + 1) ≃ₜ _)
  let e₁ := (e₀.compHomeomorph (Homeomorph.mulLeft g⁻¹)).homeomorphComp hBase
  have hproj :
      hBase ∘ (realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n) ∘
        (Homeomorph.mulLeft g⁻¹ : realCliffordSpinGroupZero (n + 1) ≃ₜ _)) =
      realCliffordSpinOrbitMap (n + 1) (realCliffordSpinLastUnit n) := by
    funext s
    simp only [Function.comp_apply, Homeomorph.coe_mulLeft,
      realCliffordSpinOrbitMap_apply, hBase,
      Homeomorph.smul_apply, smul_smul]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hproj]
  refine ⟨e₁, ?_⟩
  dsimp only [e₁, Bundle.Trivialization.homeomorphComp,
    Bundle.Trivialization.compHomeomorph]
  rw [← Homeomorph.smul_apply g (realCliffordSpinLastUnit n)]
  simpa only [hBase, e₀, Set.mem_preimage, Homeomorph.symm_apply_apply] using
    (realCliffordSpinBaseTrivializationData n).2

end

end CliffordAlgebra
