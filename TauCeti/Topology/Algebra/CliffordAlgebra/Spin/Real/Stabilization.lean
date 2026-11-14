/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Prod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

/-!
# Topology of compact real Spin stabilization and block sums

This module equips the first-coordinate stabilization maps and block-sum homomorphisms of
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization` with their topological properties
and transports them to the closed unit-group carriers of
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection`.

On `Spin(n)` and `Spin(p) × Spin(q)`, continuity follows directly from continuity of quadratic
isometry maps on Spin groups and `CliffordAlgebra.continuous_spinGroupProd`. Because the Spin
projection `Spin(m) → SO(m)` is a continuous surjection from a compact group to a Hausdorff group
in every dimension `m`, it is a quotient map; continuity of the corresponding `SO` stabilization and
block-sum homomorphisms descends immediately through the Spin-to-`SO` commutative squares. Since
compact real `Spin` and `SO` groups are compact and Hausdorff, the injective stabilization maps and
the `SO` block sum are closed topological embeddings.

Finally, conjugating by `realCliffordSpinContinuousMulEquivUnitsRange` and
`realCliffordSpecialOrthogonalContinuousMulEquivRange` yields the corresponding continuous
homomorphisms on the closed unit-range carriers in `(CliffordAlgebra (realCliffordForm n 0))ˣ` and
`GL(n, ℝ)`, together with their compatibility squares with
`realCliffordSpinToSpecialOrthogonalRange`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinFirstInclusionContinuousMonoidHom` and
  `CliffordAlgebra.realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom`: first-coordinate
  stabilization bundled as `ContinuousMonoidHom`s.
* `CliffordAlgebra.realCliffordSpinBlockSumContinuousMonoidHom` and
  `CliffordAlgebra.realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom`: compact Spin and `SO`
  block sums bundled as `ContinuousMonoidHom`s.
* `TauCeti.CliffordAlgebra.realCliffordSpinUnitsRangeFirstInclusion`,
  `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalRangeFirstInclusion`,
  `TauCeti.CliffordAlgebra.realCliffordSpinUnitsRangeBlockSum`, and
  `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalRangeBlockSum`: the corresponding continuous
  homomorphisms on the closed unit-range carriers.

## Main results

* `CliffordAlgebra.continuous_realCliffordSpinFirstInclusion`,
  `CliffordAlgebra.isClosedEmbedding_realCliffordSpinFirstInclusion`, and
  `CliffordAlgebra.isEmbedding_realCliffordSpinFirstInclusion`: continuity and closed-embedding
  properties of `Spin(n) → Spin(n + 1)`.
* `CliffordAlgebra.continuous_realCliffordSpecialOrthogonalFirstInclusion`,
  `CliffordAlgebra.isClosedEmbedding_realCliffordSpecialOrthogonalFirstInclusion`, and
  `CliffordAlgebra.isEmbedding_realCliffordSpecialOrthogonalFirstInclusion`: continuity and
  closed-embedding properties of `SO(n) → SO(n + 1)`.
* `CliffordAlgebra.continuous_realCliffordSpinBlockSum`: continuity of
  `Spin(p) × Spin(q) → Spin(p + q)`.
* `CliffordAlgebra.continuous_realCliffordSpecialOrthogonalBlockSum`,
  `CliffordAlgebra.isClosedEmbedding_realCliffordSpecialOrthogonalBlockSum`, and
  `CliffordAlgebra.isEmbedding_realCliffordSpecialOrthogonalBlockSum`: continuity and
  closed-embedding properties of `SO(p) × SO(q) → SO(p + q)`.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_comp_firstInclusion` and
  `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_comp_blockSum`: compatibility
  of the unit-range stabilization and block-sum homomorphisms with the native Spin-to-`SO` carrier
  projection.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and Chapter II, §1.
-/

public section

namespace CliffordAlgebra

open TauCeti TauCeti.QuadraticMap

noncomputable section

/-! ### Continuity and closed embeddings of stabilization and block sum -/

/-- **First-coordinate Spin stabilization `Spin(n) → Spin(n + 1)` is continuous.** -/
@[fun_prop]
theorem continuous_realCliffordSpinFirstInclusion (n : ℕ) :
    Continuous (realCliffordSpinFirstInclusion n) := by
  rw [realCliffordSpinFirstInclusion_eq_spinGroupMap]
  exact (realCliffordSpinFirstInclusionIsometry n).continuous_spinGroupMap

/-- **First-coordinate Spin stabilization `Spin(n) → Spin(n + 1)` is a closed embedding.** -/
theorem isClosedEmbedding_realCliffordSpinFirstInclusion (n : ℕ) :
    Topology.IsClosedEmbedding (realCliffordSpinFirstInclusion n) :=
  (continuous_realCliffordSpinFirstInclusion n).isClosedEmbedding
    (realCliffordSpinFirstInclusion_injective n)

/-- **First-coordinate Spin stabilization `Spin(n) → Spin(n + 1)` is a topological embedding.** -/
theorem isEmbedding_realCliffordSpinFirstInclusion (n : ℕ) :
    Topology.IsEmbedding (realCliffordSpinFirstInclusion n) :=
  (isClosedEmbedding_realCliffordSpinFirstInclusion n).isEmbedding

/-- **First-coordinate Spin stabilization, bundled as a continuous homomorphism.** -/
def realCliffordSpinFirstInclusionContinuousMonoidHom (n : ℕ) :
    realCliffordSpinGroupZero n →ₜ* realCliffordSpinGroupZero (n + 1) :=
  ⟨realCliffordSpinFirstInclusion n, continuous_realCliffordSpinFirstInclusion n⟩

/-- The underlying monoid homomorphism of `realCliffordSpinFirstInclusionContinuousMonoidHom`. -/
@[simp]
theorem coeMonoidHom_realCliffordSpinFirstInclusionContinuousMonoidHom (n : ℕ) :
    (realCliffordSpinFirstInclusionContinuousMonoidHom n :
        realCliffordSpinGroupZero n →* realCliffordSpinGroupZero (n + 1)) =
      realCliffordSpinFirstInclusion n :=
  (rfl)

/-- Evaluating `realCliffordSpinFirstInclusionContinuousMonoidHom` applies
`realCliffordSpinFirstInclusion`. -/
@[simp]
theorem realCliffordSpinFirstInclusionContinuousMonoidHom_apply (n : ℕ)
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinFirstInclusionContinuousMonoidHom n x =
      realCliffordSpinFirstInclusion n x :=
  (rfl)

/-- **First-coordinate special-orthogonal stabilization `SO(n) → SO(n + 1)` is continuous.** -/
@[fun_prop]
theorem continuous_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    Continuous (realCliffordSpecialOrthogonalFirstInclusion n) := by
  have hquot : Topology.IsQuotientMap (spinToSpecialOrthogonal (realCliffordForm n 0)) :=
    Topology.IsQuotientMap.of_surjective_continuous
      (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero n))
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))
  refine hquot.continuous_iff.mpr ?_
  exact ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm (n + 1) 0)).comp
    (continuous_realCliffordSpinFirstInclusion n)).congr fun x ↦
      spinToSpecialOrthogonal_realCliffordSpinFirstInclusion n x

/-- **First-coordinate special-orthogonal stabilization `SO(n) → SO(n + 1)` is a closed
embedding.** -/
theorem isClosedEmbedding_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    Topology.IsClosedEmbedding (realCliffordSpecialOrthogonalFirstInclusion n) :=
  (continuous_realCliffordSpecialOrthogonalFirstInclusion n).isClosedEmbedding
    (realCliffordSpecialOrthogonalFirstInclusion_injective n)

/-- **First-coordinate special-orthogonal stabilization `SO(n) → SO(n + 1)` is a topological
embedding.** -/
theorem isEmbedding_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    Topology.IsEmbedding (realCliffordSpecialOrthogonalFirstInclusion n) :=
  (isClosedEmbedding_realCliffordSpecialOrthogonalFirstInclusion n).isEmbedding

/-- **First-coordinate special-orthogonal stabilization, bundled as a continuous homomorphism.** -/
def realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom (n : ℕ) :
    specialOrthogonalGroup (realCliffordForm n 0) →ₜ*
      specialOrthogonalGroup (realCliffordForm (n + 1) 0) :=
  ⟨realCliffordSpecialOrthogonalFirstInclusion n,
    continuous_realCliffordSpecialOrthogonalFirstInclusion n⟩

/-- The underlying monoid homomorphism of
`realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom`. -/
@[simp]
theorem coeMonoidHom_realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom (n : ℕ) :
    (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom n :
        specialOrthogonalGroup (realCliffordForm n 0) →*
          specialOrthogonalGroup (realCliffordForm (n + 1) 0)) =
      realCliffordSpecialOrthogonalFirstInclusion n :=
  (rfl)

/-- Evaluating `realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom` applies
`realCliffordSpecialOrthogonalFirstInclusion`. -/
@[simp]
theorem realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom_apply (n : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm n 0)) :
    realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom n g =
      realCliffordSpecialOrthogonalFirstInclusion n g :=
  (rfl)

/-- **The compact Spin block-sum homomorphism `Spin(p) × Spin(q) → Spin(p + q)` is continuous.** -/
@[fun_prop]
theorem continuous_realCliffordSpinBlockSum (p q : ℕ) :
    Continuous (realCliffordSpinBlockSum p q) :=
  ((realCliffordSplitIsometry p q 0 0).symm.continuous_spinGroupEquiv.comp
    (continuous_spinGroupProd (realCliffordForm p 0) (realCliffordForm q 0))).congr
      fun x ↦ (realCliffordSpinBlockSum_apply p q x).symm

/-- **The compact Spin block-sum homomorphism, bundled as a continuous homomorphism.** -/
def realCliffordSpinBlockSumContinuousMonoidHom (p q : ℕ) :
    realCliffordSpinGroupZero p × realCliffordSpinGroupZero q →ₜ*
      realCliffordSpinGroupZero (p + q) :=
  ⟨realCliffordSpinBlockSum p q, continuous_realCliffordSpinBlockSum p q⟩

/-- The underlying monoid homomorphism of `realCliffordSpinBlockSumContinuousMonoidHom`. -/
@[simp]
theorem coeMonoidHom_realCliffordSpinBlockSumContinuousMonoidHom (p q : ℕ) :
    (realCliffordSpinBlockSumContinuousMonoidHom p q :
        realCliffordSpinGroupZero p × realCliffordSpinGroupZero q →*
          realCliffordSpinGroupZero (p + q)) =
      realCliffordSpinBlockSum p q :=
  (rfl)

/-- Evaluating `realCliffordSpinBlockSumContinuousMonoidHom` applies
`realCliffordSpinBlockSum`. -/
@[simp]
theorem realCliffordSpinBlockSumContinuousMonoidHom_apply (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    realCliffordSpinBlockSumContinuousMonoidHom p q x =
      realCliffordSpinBlockSum p q x :=
  (rfl)

/-- **The compact special-orthogonal block-sum homomorphism `SO(p) × SO(q) → SO(p + q)` is
continuous.** -/
@[fun_prop]
theorem continuous_realCliffordSpecialOrthogonalBlockSum (p q : ℕ) :
    Continuous (realCliffordSpecialOrthogonalBlockSum p q) := by
  have hquot : Topology.IsQuotientMap
      (Prod.map (spinToSpecialOrthogonal (realCliffordForm p 0))
        (spinToSpecialOrthogonal (realCliffordForm q 0))) :=
    Topology.IsQuotientMap.of_surjective_continuous
      ((spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero p)).prodMap
        (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero q)))
      ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm p 0)).prodMap
        (continuous_spinToSpecialOrthogonal_pi (realCliffordForm q 0)))
  refine hquot.continuous_iff.mpr ?_
  exact ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm (p + q) 0)).comp
    (continuous_realCliffordSpinBlockSum p q)).congr fun x ↦
      spinToSpecialOrthogonal_realCliffordSpinBlockSum p q x

/-- **The compact special-orthogonal block-sum homomorphism `SO(p) × SO(q) → SO(p + q)` is a closed
embedding.** -/
theorem isClosedEmbedding_realCliffordSpecialOrthogonalBlockSum (p q : ℕ) :
    Topology.IsClosedEmbedding (realCliffordSpecialOrthogonalBlockSum p q) :=
  (continuous_realCliffordSpecialOrthogonalBlockSum p q).isClosedEmbedding
    (realCliffordSpecialOrthogonalBlockSum_injective p q)

/-- **The compact special-orthogonal block-sum homomorphism `SO(p) × SO(q) → SO(p + q)` is a
topological embedding.** -/
theorem isEmbedding_realCliffordSpecialOrthogonalBlockSum (p q : ℕ) :
    Topology.IsEmbedding (realCliffordSpecialOrthogonalBlockSum p q) :=
  (isClosedEmbedding_realCliffordSpecialOrthogonalBlockSum p q).isEmbedding

/-- **The compact special-orthogonal block-sum homomorphism, bundled as a continuous
homomorphism.** -/
def realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom (p q : ℕ) :
    specialOrthogonalGroup (realCliffordForm p 0) ×
        specialOrthogonalGroup (realCliffordForm q 0) →ₜ*
      specialOrthogonalGroup (realCliffordForm (p + q) 0) :=
  ⟨realCliffordSpecialOrthogonalBlockSum p q,
    continuous_realCliffordSpecialOrthogonalBlockSum p q⟩

/-- The underlying monoid homomorphism of
`realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom`. -/
@[simp]
theorem coeMonoidHom_realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom (p q : ℕ) :
    (realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom p q :
        specialOrthogonalGroup (realCliffordForm p 0) ×
            specialOrthogonalGroup (realCliffordForm q 0) →*
          specialOrthogonalGroup (realCliffordForm (p + q) 0)) =
      realCliffordSpecialOrthogonalBlockSum p q :=
  (rfl)

/-- Evaluating `realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom` applies
`realCliffordSpecialOrthogonalBlockSum`. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom_apply (p q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0) ×
      specialOrthogonalGroup (realCliffordForm q 0)) :
    realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom p q g =
      realCliffordSpecialOrthogonalBlockSum p q g :=
  (rfl)

end

end CliffordAlgebra

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

/-! ### Compatibility with the closed unit-range carriers -/

/-- **First-coordinate Spin stabilization on the closed Clifford-unit range carriers.** -/
def realCliffordSpinUnitsRangeFirstInclusion (n : ℕ) :
    MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) →ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm (n + 1) 0)) :=
  (realCliffordSpinContinuousMulEquivUnitsRange (n + 1) :
      realCliffordSpinGroupZero (n + 1) →ₜ*
        MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm (n + 1) 0))).comp
    ((realCliffordSpinFirstInclusionContinuousMonoidHom n).comp
      ((realCliffordSpinContinuousMulEquivUnitsRange n).symm :
        MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) →ₜ*
          realCliffordSpinGroupZero n))

/-- Evaluating `realCliffordSpinUnitsRangeFirstInclusion` on a canonical unit-range representative
applies `realCliffordSpinFirstInclusion`. -/
theorem realCliffordSpinUnitsRangeFirstInclusion_apply_equiv (n : ℕ)
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinUnitsRangeFirstInclusion n
        (realCliffordSpinContinuousMulEquivUnitsRange n x) =
      realCliffordSpinContinuousMulEquivUnitsRange (n + 1)
        (realCliffordSpinFirstInclusion n x) := by
  simp [realCliffordSpinUnitsRangeFirstInclusion]

/-- **First-coordinate special-orthogonal stabilization on the closed `GL(n, ℝ)` range
carriers.** -/
def realCliffordSpecialOrthogonalRangeFirstInclusion (n : ℕ) :
    -- `realCliffordForm n 0` lives on `Fin (n + 0) → ℝ`, which is `Fin n → ℝ` by definition;
    -- stating the carrier over `Fin n → ℝ` matches `realCliffordSpinToSpecialOrthogonalRange`.
    MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) →ₜ*
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin (n + 1) → ℝ) from realCliffordForm (n + 1) 0)) :=
  (realCliffordSpecialOrthogonalContinuousMulEquivRange (n + 1) :
      QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 1) 0) →ₜ* _).comp
    ((realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom n).comp
      ((realCliffordSpecialOrthogonalContinuousMulEquivRange n).symm :
        _ →ₜ* QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))

/-- Evaluating `realCliffordSpecialOrthogonalRangeFirstInclusion` on a canonical matrix-range
representative applies `realCliffordSpecialOrthogonalFirstInclusion`. -/
theorem realCliffordSpecialOrthogonalRangeFirstInclusion_apply_equiv (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :
    realCliffordSpecialOrthogonalRangeFirstInclusion n
        (realCliffordSpecialOrthogonalContinuousMulEquivRange n g) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange (n + 1)
        (realCliffordSpecialOrthogonalFirstInclusion n g) := by
  simp [realCliffordSpecialOrthogonalRangeFirstInclusion]

/-- **First-coordinate stabilization commutes with `realCliffordSpinToSpecialOrthogonalRange`.** -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_comp_firstInclusion (n : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRange (n + 1)).comp
        (realCliffordSpinUnitsRangeFirstInclusion n) =
      (realCliffordSpecialOrthogonalRangeFirstInclusion n).comp
        (realCliffordSpinToSpecialOrthogonalRange n) :=
  ContinuousMonoidHom.ext fun u ↦ by
    obtain ⟨x, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange n).surjective u
    have hproj (m : ℕ) (y : realCliffordSpinGroupZero m) :
        realCliffordSpinToSpecialOrthogonalRange m
            (realCliffordSpinContinuousMulEquivUnitsRange m y) =
          realCliffordSpecialOrthogonalContinuousMulEquivRange m
            (spinToSpecialOrthogonal (realCliffordForm m 0) y) := by
      simp
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply,
      realCliffordSpinUnitsRangeFirstInclusion_apply_equiv, hproj,
      realCliffordSpecialOrthogonalRangeFirstInclusion_apply_equiv,
      spinToSpecialOrthogonal_realCliffordSpinFirstInclusion]

/-- **Compact Spin block sum on the closed Clifford-unit range carriers.** -/
def realCliffordSpinUnitsRangeBlockSum (p q : ℕ) :
    MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm p 0)) ×
        MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm q 0)) →ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm (p + q) 0)) :=
  (realCliffordSpinContinuousMulEquivUnitsRange (p + q) :
      realCliffordSpinGroupZero (p + q) →ₜ* _).comp
    ((realCliffordSpinBlockSumContinuousMonoidHom p q).comp
      (((realCliffordSpinContinuousMulEquivUnitsRange p).symm :
          _ →ₜ* realCliffordSpinGroupZero p).prodMap
        ((realCliffordSpinContinuousMulEquivUnitsRange q).symm :
          _ →ₜ* realCliffordSpinGroupZero q)))

/-- Evaluating `realCliffordSpinUnitsRangeBlockSum` on canonical unit-range representatives applies
`realCliffordSpinBlockSum`. -/
theorem realCliffordSpinUnitsRangeBlockSum_apply_equiv (p q : ℕ)
    (x : realCliffordSpinGroupZero p) (y : realCliffordSpinGroupZero q) :
    realCliffordSpinUnitsRangeBlockSum p q
        (realCliffordSpinContinuousMulEquivUnitsRange p x,
          realCliffordSpinContinuousMulEquivUnitsRange q y) =
      realCliffordSpinContinuousMulEquivUnitsRange (p + q)
        (realCliffordSpinBlockSum p q (x, y)) := by
  simp [realCliffordSpinUnitsRangeBlockSum]

/-- **Compact special-orthogonal block sum on the closed `GL` range carriers.** -/
def realCliffordSpecialOrthogonalRangeBlockSum (p q : ℕ) :
    -- `realCliffordForm m 0` lives on `Fin (m + 0) → ℝ`, which is `Fin m → ℝ` by definition;
    -- stating the carriers over `Fin m → ℝ` matches `realCliffordSpinToSpecialOrthogonalRange`.
    MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin p → ℝ) from realCliffordForm p 0)) ×
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin q → ℝ) from realCliffordForm q 0)) →ₜ*
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin (p + q) → ℝ) from realCliffordForm (p + q) 0)) :=
  (realCliffordSpecialOrthogonalContinuousMulEquivRange (p + q) :
      QuadraticMap.specialOrthogonalGroup (realCliffordForm (p + q) 0) →ₜ* _).comp
    ((realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom p q).comp
      (((realCliffordSpecialOrthogonalContinuousMulEquivRange p).symm :
          _ →ₜ* QuadraticMap.specialOrthogonalGroup (realCliffordForm p 0)).prodMap
        ((realCliffordSpecialOrthogonalContinuousMulEquivRange q).symm :
          _ →ₜ* QuadraticMap.specialOrthogonalGroup (realCliffordForm q 0))))

/-- Evaluating `realCliffordSpecialOrthogonalRangeBlockSum` on canonical matrix-range
representatives applies `realCliffordSpecialOrthogonalBlockSum`. -/
theorem realCliffordSpecialOrthogonalRangeBlockSum_apply_equiv (p q : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm p 0))
    (h : QuadraticMap.specialOrthogonalGroup (realCliffordForm q 0)) :
    realCliffordSpecialOrthogonalRangeBlockSum p q
        (realCliffordSpecialOrthogonalContinuousMulEquivRange p g,
          realCliffordSpecialOrthogonalContinuousMulEquivRange q h) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange (p + q)
        (realCliffordSpecialOrthogonalBlockSum p q (g, h)) := by
  simp [realCliffordSpecialOrthogonalRangeBlockSum]

/-- **Block sum commutes with `realCliffordSpinToSpecialOrthogonalRange`.** -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_comp_blockSum (p q : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRange (p + q)).comp
        (realCliffordSpinUnitsRangeBlockSum p q) =
      (realCliffordSpecialOrthogonalRangeBlockSum p q).comp
        ((realCliffordSpinToSpecialOrthogonalRange p).prodMap
          (realCliffordSpinToSpecialOrthogonalRange q)) :=
  ContinuousMonoidHom.ext fun ⟨u, v⟩ ↦ by
    obtain ⟨x, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange p).surjective u
    obtain ⟨y, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange q).surjective v
    have hproj (m : ℕ) (z : realCliffordSpinGroupZero m) :
        realCliffordSpinToSpecialOrthogonalRange m
            (realCliffordSpinContinuousMulEquivUnitsRange m z) =
          realCliffordSpecialOrthogonalContinuousMulEquivRange m
            (spinToSpecialOrthogonal (realCliffordForm m 0) z) := by
      simp
    have hprod : ((realCliffordSpinToSpecialOrthogonalRange p).prodMap
          (realCliffordSpinToSpecialOrthogonalRange q))
          (realCliffordSpinContinuousMulEquivUnitsRange p x,
            realCliffordSpinContinuousMulEquivUnitsRange q y) =
        (realCliffordSpinToSpecialOrthogonalRange p
            (realCliffordSpinContinuousMulEquivUnitsRange p x),
          realCliffordSpinToSpecialOrthogonalRange q
            (realCliffordSpinContinuousMulEquivUnitsRange q y)) :=
      rfl
    simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, hprod,
      realCliffordSpinUnitsRangeBlockSum_apply_equiv, hproj,
      realCliffordSpecialOrthogonalRangeBlockSum_apply_equiv,
      spinToSpecialOrthogonal_realCliffordSpinBlockSum]

end

end TauCeti.CliffordAlgebra

end
