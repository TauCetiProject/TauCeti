/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic

/-!
# The lower-rank subgroup of a compact real Spin group

Splitting the last positive coordinate identifies the quadratic space of `Spin(n + 1)` with the
orthogonal sum of the space of `Spin(n)` and a positive line. Functoriality of the Spin group gives
an injective homomorphism `Spin(n) → Spin(n + 1)`. Its image fixes the last coordinate vector, so it
canonically factors through that vector's stabilizer.

This is the algebraic half of the familiar stabilizer description
`Spin(n + 1) / Spin(n) ≃ Sⁿ`. The converse identification of the full stabilizer, and the topology
of the resulting homogeneous space, are separate results.

The split-coordinate action equation below compares the lower-rank inclusion with the Spin
projection. When `n > 0`, the projection has kernel `{1, -1}`; since the inclusion preserves the
canonical `-1` whenever its source form is nonzero, every element sharing a projection with an
included element is itself included. This is the residual kernel calculation needed by the
converse stabilizer identification.

## Main results

* `CliffordAlgebra.realCliffordSpinInclusion` is the lower-rank Spin homomorphism.
* `CliffordAlgebra.realCliffordSpinLastStabilizer` is the stabilizer of the last unit vector.
* `CliffordAlgebra.realCliffordSpinStabilizerInclusion` is the injective homomorphism into that
  stabilizer.
* `CliffordAlgebra.realCliffordSpinInclusion_spinVectorAction_split` computes the full vector
  action of the inclusion in split coordinates.
* `eq_or_eq_realCliffordSpinInclusion_negOne_mul_of_spinToSpecialOrthogonal_eq`
  identifies the two possible lifts of the `spinToSpecialOrthogonal` image of an included element.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section


open QuadraticMap

namespace CliffordAlgebra

open TauCeti

noncomputable section


private def realCliffordSpinInclusionIsometry (n : ℕ) :
    realCliffordForm n 0 →qᵢ realCliffordForm (n + 1) 0 :=
  (realCliffordPositiveSplitIsometry n 0).symm.toIsometry.comp
    (QuadraticMap.Isometry.inl (realCliffordForm n 0)
      (QuadraticMap.sq (R := ℝ) (A := ℝ)))

private def realCliffordSpinLastIsometry (n : ℕ) :
    QuadraticMap.sq (R := ℝ) (A := ℝ) →qᵢ realCliffordForm (n + 1) 0 :=
  (realCliffordPositiveSplitIsometry n 0).symm.toIsometry.comp
    (QuadraticMap.Isometry.inr (realCliffordForm n 0)
      (QuadraticMap.sq (R := ℝ) (A := ℝ)))

/-- The homomorphism `Spin(n) → Spin(n + 1)` induced by including the first summand after splitting
off the last positive coordinate. -/
def realCliffordSpinInclusion (n : ℕ) :
    realCliffordSpinGroupZero n →* realCliffordSpinGroupZero (n + 1) :=
  (realCliffordSpinInclusionIsometry n).spinGroupMap

/-- The lower-rank Spin inclusion is induced by the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_realCliffordSpinInclusion_apply (n : ℕ) (x : realCliffordSpinGroupZero n) :
    (realCliffordSpinInclusion n x : CliffordAlgebra (realCliffordForm (n + 1) 0)) =
      CliffordAlgebra.map
        ((realCliffordPositiveSplitIsometry n 0).symm.toIsometry.comp
          (QuadraticMap.Isometry.inl (realCliffordForm n 0)
            (QuadraticMap.sq (R := ℝ) (A := ℝ))))
        (x : CliffordAlgebra (realCliffordForm n 0)) :=
  QuadraticMap.Isometry.coe_spinGroupMap_apply _ _

private theorem realCliffordSpinLastIsometry_one (n : ℕ) :
    realCliffordSpinLastIsometry n 1 = Pi.single (Fin.last n) 1 := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Pi.single_eq_same]
    have h := realCliffordPositiveSplitIsometry_snd n 0
      (realCliffordSpinLastIsometry n 1)
    simpa [realCliffordSpinLastIsometry] using h.symm
  · rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
    have h := realCliffordPositiveSplitIsometry_fst_pos n 0
      (realCliffordSpinLastIsometry n 1) i
    simpa [realCliffordSpinLastIsometry] using h.symm

/-- The image of the lower-rank Spin inclusion fixes the last coordinate vector. -/
@[simp]
theorem realCliffordSpinInclusion_fixed_last (n : ℕ) (x : realCliffordSpinGroupZero n) :
    spinVectorAction (realCliffordForm (n + 1) 0) (realCliffordSpinInclusion n x)
        (Pi.single (Fin.last n) 1) = Pi.single (Fin.last n) 1 := by
  rw [← realCliffordSpinLastIsometry_one]
  exact (realCliffordPositiveSplitIsometry n 0).spinGroupMap_fixed_of_prod x 1

/-- In positive-split coordinates, the lower-rank Spin inclusion acts on the first summand by
the original Spin element and fixes the complementary line. -/
@[simp]
theorem realCliffordSpinInclusion_spinVectorAction_split (n : ℕ)
    (x : realCliffordSpinGroupZero n) (m : Fin n → ℝ) (r : ℝ) :
    spinVectorAction (realCliffordForm (n + 1) 0) (realCliffordSpinInclusion n x)
        ((realCliffordPositiveSplitIsometry n 0).symm (m, r)) =
      (realCliffordPositiveSplitIsometry n 0).symm
        (spinVectorAction (realCliffordForm n 0) x m, r) := by
  exact (realCliffordPositiveSplitIsometry n 0).spinGroupMap_spinVectorAction_prod x m r

/-- The lower-rank homomorphism `Spin(n) → Spin(n + 1)` is injective. -/
theorem realCliffordSpinInclusion_injective (n : ℕ) :
    Function.Injective (realCliffordSpinInclusion n) := by
  apply QuadraticMap.Isometry.spinGroupMap_injective
  rw [realCliffordSpinInclusionIsometry, ← CliffordAlgebra.map_comp_map]
  exact (CliffordAlgebra.leftInverse_map_of_leftInverse
      (realCliffordPositiveSplitIsometry n 0).symm.toIsometry
      (realCliffordPositiveSplitIsometry n 0).toIsometry
      (realCliffordPositiveSplitIsometry n 0).apply_symm_apply).injective.comp
    (CliffordAlgebra.map_inl_injective (realCliffordForm n 0)
      (QuadraticMap.sq (R := ℝ) (A := ℝ)))

/-- The subgroup of `Spin(n + 1)` fixing the last coordinate vector under the vector action. -/
def realCliffordSpinLastStabilizer (n : ℕ) :
    Subgroup (realCliffordSpinGroupZero (n + 1)) :=
  Subgroup.comap (spinToOrthogonal (realCliffordForm (n + 1) 0))
    (MulAction.stabilizer (QuadraticMap.orthogonalGroup (realCliffordForm (n + 1) 0))
      (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ))

/-- Membership in the last-vector stabilizer means that the Spin vector action fixes that vector. -/
@[simp]
theorem mem_realCliffordSpinLastStabilizer_iff
    {n : ℕ} {x : realCliffordSpinGroupZero (n + 1)} :
    x ∈ realCliffordSpinLastStabilizer n ↔
      spinVectorAction (realCliffordForm (n + 1) 0) x
        (Pi.single (Fin.last n) 1) = Pi.single (Fin.last n) 1 := by
  rw [realCliffordSpinLastStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  -- Expand the orthogonal-group action to the underlying linear equivalence.
  change (((spinToOrthogonal (realCliffordForm (n + 1) 0) x :
        QuadraticMap.orthogonalGroup (realCliffordForm (n + 1) 0)) :
        (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
          (Pi.single (Fin.last n) 1) = Pi.single (Fin.last n) 1) ↔
      spinVectorAction (realCliffordForm (n + 1) 0) x
        (Pi.single (Fin.last n) 1) = Pi.single (Fin.last n) 1
  rw [coe_spinToOrthogonal_apply]

private theorem realCliffordSpinInclusion_mem_lastStabilizer (n : ℕ)
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinInclusion n x ∈ realCliffordSpinLastStabilizer n :=
  mem_realCliffordSpinLastStabilizer_iff.mpr
    (realCliffordSpinInclusion_fixed_last n x)

/-- The injective homomorphism from `Spin(n)` to the last-vector stabilizer in `Spin(n + 1)`. -/
def realCliffordSpinStabilizerInclusion (n : ℕ) :
    realCliffordSpinGroupZero n →* realCliffordSpinLastStabilizer n :=
  (realCliffordSpinInclusion n).codRestrict _
    (realCliffordSpinInclusion_mem_lastStabilizer n)

/-- The stabilizer inclusion agrees with the lower-rank Spin inclusion after forgetting the
stabilizer membership proof. -/
@[simp]
theorem coe_realCliffordSpinStabilizerInclusion_apply
    (n : ℕ) (x : realCliffordSpinGroupZero n) :
    (realCliffordSpinStabilizerInclusion n x : realCliffordSpinGroupZero (n + 1)) =
      realCliffordSpinInclusion n x :=
  by simp only [realCliffordSpinStabilizerInclusion, MonoidHom.codRestrict_apply]

/-- The homomorphism from `Spin(n)` to the last-vector stabilizer is injective. -/
theorem realCliffordSpinStabilizerInclusion_injective (n : ℕ) :
    Function.Injective (realCliffordSpinStabilizerInclusion n) :=
  (MonoidHom.injective_codRestrict _ _ _).mpr (realCliffordSpinInclusion_injective n)

/-- The lower-rank compact Spin inclusion sends the canonical nontrivial kernel element to the
corresponding kernel element in the higher-rank Spin group. -/
@[simp]
theorem realCliffordSpinInclusion_negOne (n : ℕ) [NeZero n] :
    realCliffordSpinInclusion n
        (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) =
      spinGroup.negOne (realCliffordForm (n + 1) 0)
        (nondegenerate_realCliffordForm (n + 1) 0).ne_zero :=
  (realCliffordSpinInclusionIsometry n).spinGroupMap_negOne
    (nondegenerate_realCliffordForm n 0).ne_zero

/-- An element of `Spin(n + 1)` over the projection of an included element of `Spin(n)` is that
element or its translate by the canonical nontrivial kernel element. -/
theorem eq_or_eq_realCliffordSpinInclusion_negOne_mul_of_spinToSpecialOrthogonal_eq
    (n : ℕ) [NeZero n] (x : realCliffordSpinGroupZero (n + 1))
    (y : realCliffordSpinGroupZero n)
    (h : spinToSpecialOrthogonal (realCliffordForm (n + 1) 0) x =
      spinToSpecialOrthogonal (realCliffordForm (n + 1) 0)
        (realCliffordSpinInclusion n y)) :
    x = realCliffordSpinInclusion n y ∨
      x = realCliffordSpinInclusion n
        (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero * y) := by
  rcases eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq
      (realCliffordForm (n + 1) 0)
      (nondegenerate_realCliffordForm (n + 1) 0) x (realCliffordSpinInclusion n y) h with
    hOne | hNeg
  · exact Or.inl hOne
  · exact Or.inr (hNeg.trans (by rw [map_mul, realCliffordSpinInclusion_negOne]))

end


end CliffordAlgebra
