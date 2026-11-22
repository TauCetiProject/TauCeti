/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Prod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering

/-!
# Topology of compact real Spin stabilization and block sums

This module equips the first-coordinate stabilization maps and block-sum homomorphisms of
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilization` with their topological properties
and transports them to the closed unit-group carriers of
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection`.

On `Spin(n)` and `Spin(p) × Spin(q)`, continuity follows directly from continuity of quadratic
isometry maps on Spin groups and `TauCeti.continuous_spinGroupProd`. Because the
Spin projection `Spin(m) → SO(m)` is a continuous surjection from a compact group to a Hausdorff
group in every dimension `m`, it is a quotient map; continuity of the corresponding `SO`
stabilization and block-sum homomorphisms descends immediately through the Spin-to-`SO` commutative
squares. Since compact real `Spin` and `SO` groups are compact and Hausdorff, the injective
stabilization maps and the `SO` block sum are closed topological embeddings.

Finally, conjugating by `realCliffordSpinContinuousMulEquivUnitsRange` and
`realCliffordSpecialOrthogonalContinuousMulEquivRange` yields the corresponding continuous
homomorphisms on the closed unit-range carriers in `(CliffordAlgebra (realCliffordForm n 0))ˣ` and
`GL(n, ℝ)`, together with their compatibility squares with
`realCliffordSpinToSpecialOrthogonalRange`. In rank `n + 2 ≥ 2`, neither the one-block embeddings
nor first-coordinate stabilization admits a continuous lift to `Spin`, and a full `2π`
coordinate-plane rotation loop lifts along the one-block embedding to an open path from `1` to
`-1`.

## Main definitions

* `TauCeti.realCliffordSpinFirstInclusionContinuousMonoidHom` and
  `TauCeti.realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom`:
  first-coordinate stabilization bundled as `ContinuousMonoidHom`s.
* `TauCeti.realCliffordSpinBlockSumContinuousMonoidHom` and
  `TauCeti.realCliffordSpecialOrthogonalBlockSumContinuousMonoidHom`: compact Spin
  and `SO` block sums bundled as `ContinuousMonoidHom`s.
* `TauCeti.realCliffordSpinUnitsRangeFirstInclusion`,
  `TauCeti.realCliffordSpecialOrthogonalRangeFirstInclusion`,
  `TauCeti.realCliffordSpinUnitsRangeBlockSum`, and
  `TauCeti.realCliffordSpecialOrthogonalRangeBlockSum`: the corresponding continuous
  homomorphisms on the closed unit-range carriers.
* `TauCeti.realCliffordSpinBlockSumRotationPath`: explicit open path lift from `1` to `-1` of a
  full `2π` coordinate-plane rotation under the one-block embedding `g ↦ diag(g, I_m)`.

## Main results

* `TauCeti.continuous_realCliffordSpinFirstInclusion`,
  `TauCeti.isClosedEmbedding_realCliffordSpinFirstInclusion`, and
  `TauCeti.isEmbedding_realCliffordSpinFirstInclusion`: continuity and
  closed-embedding properties of `Spin(n) → Spin(n + 1)`.
* `TauCeti.continuous_realCliffordSpecialOrthogonalFirstInclusion`,
  `TauCeti.isClosedEmbedding_realCliffordSpecialOrthogonalFirstInclusion`, and
  `TauCeti.isEmbedding_realCliffordSpecialOrthogonalFirstInclusion`: continuity and
  closed-embedding properties of `SO(n) → SO(n + 1)`.
* `TauCeti.continuous_realCliffordSpinBlockSum`: continuity of
  `Spin(p) × Spin(q) → Spin(p + q)`.
* `TauCeti.continuous_realCliffordSpecialOrthogonalBlockSum`,
  `TauCeti.isClosedEmbedding_realCliffordSpecialOrthogonalBlockSum`, and
  `TauCeti.isEmbedding_realCliffordSpecialOrthogonalBlockSum`: continuity and
  closed-embedding properties of `SO(p) × SO(q) → SO(p + q)`.
* `TauCeti.realCliffordSpinToSpecialOrthogonalRange_comp_firstInclusion` and
  `TauCeti.realCliffordSpinToSpecialOrthogonalRange_comp_blockSum`: compatibility
  of the unit-range stabilization and block-sum homomorphisms with the native Spin-to-`SO` carrier
  projection.
* `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one`,
  `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk`, and
  `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion`: non-existence
  of continuous Spin lifts for the one-block embeddings and first-coordinate stabilization in rank
  `≥ 2`.
* `TauCeti.realCliffordSpinBlockSumRotationPath_apply` and
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinBlockSumRotationPath`: evaluation and
  projection of the open one-block rotation path lift.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and Chapter II, §1.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.CliffordAlgebra TauCeti.QuadraticMap

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

/-- Evaluating `realCliffordSpinUnitsRangeFirstInclusion` transports
`realCliffordSpinFirstInclusion` across `realCliffordSpinContinuousMulEquivUnitsRange`. -/
@[simp]
theorem realCliffordSpinUnitsRangeFirstInclusion_apply (n : ℕ)
    (u : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :
    realCliffordSpinUnitsRangeFirstInclusion n u =
      realCliffordSpinContinuousMulEquivUnitsRange (n + 1)
        (realCliffordSpinFirstInclusion n
          ((realCliffordSpinContinuousMulEquivUnitsRange n).symm u)) :=
  (rfl)

-- Not `@[simp]`: `realCliffordSpinContinuousMulEquivUnitsRange_apply` simplifies the inner
-- argument, and `realCliffordSpinUnitsRangeFirstInclusion_apply` already handles general inputs.
/-- Evaluating `realCliffordSpinUnitsRangeFirstInclusion` on a canonical unit-range representative
applies `realCliffordSpinFirstInclusion`. -/
theorem realCliffordSpinUnitsRangeFirstInclusion_apply_equiv (n : ℕ)
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinUnitsRangeFirstInclusion n
        (realCliffordSpinContinuousMulEquivUnitsRange n x) =
      realCliffordSpinContinuousMulEquivUnitsRange (n + 1)
        (realCliffordSpinFirstInclusion n x) := by
  simp

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

/-- Evaluating `realCliffordSpecialOrthogonalRangeFirstInclusion` transports
`realCliffordSpecialOrthogonalFirstInclusion` across
`realCliffordSpecialOrthogonalContinuousMulEquivRange`. -/
@[simp]
theorem realCliffordSpecialOrthogonalRangeFirstInclusion_apply (n : ℕ)
    (u : MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0))) :
    realCliffordSpecialOrthogonalRangeFirstInclusion n u =
      realCliffordSpecialOrthogonalContinuousMulEquivRange (n + 1)
        (realCliffordSpecialOrthogonalFirstInclusion n
          ((realCliffordSpecialOrthogonalContinuousMulEquivRange n).symm u)) :=
  (rfl)

-- Not `@[simp]`: `realCliffordSpecialOrthogonalContinuousMulEquivRange_apply` simplifies the inner
-- argument, and `realCliffordSpecialOrthogonalRangeFirstInclusion_apply` handles general inputs.
/-- Evaluating `realCliffordSpecialOrthogonalRangeFirstInclusion` on a canonical matrix-range
representative applies `realCliffordSpecialOrthogonalFirstInclusion`. -/
theorem realCliffordSpecialOrthogonalRangeFirstInclusion_apply_equiv (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :
    realCliffordSpecialOrthogonalRangeFirstInclusion n
        (realCliffordSpecialOrthogonalContinuousMulEquivRange n g) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange (n + 1)
        (realCliffordSpecialOrthogonalFirstInclusion n g) := by
  simp

/-- **First-coordinate stabilization commutes with `realCliffordSpinToSpecialOrthogonalRange`.** -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_comp_firstInclusion (n : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRange (n + 1)).comp
        (realCliffordSpinUnitsRangeFirstInclusion n) =
      (realCliffordSpecialOrthogonalRangeFirstInclusion n).comp
        (realCliffordSpinToSpecialOrthogonalRange n) :=
  ContinuousMonoidHom.ext fun _ ↦ by simp

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

/-- Evaluating `realCliffordSpinUnitsRangeBlockSum` transports `realCliffordSpinBlockSum` across
`realCliffordSpinContinuousMulEquivUnitsRange`. -/
@[simp]
theorem realCliffordSpinUnitsRangeBlockSum_apply (p q : ℕ)
    (u : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm p 0)) ×
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm q 0))) :
    realCliffordSpinUnitsRangeBlockSum p q u =
      realCliffordSpinContinuousMulEquivUnitsRange (p + q)
        (realCliffordSpinBlockSum p q
          ((realCliffordSpinContinuousMulEquivUnitsRange p).symm u.1,
            (realCliffordSpinContinuousMulEquivUnitsRange q).symm u.2)) :=
  (rfl)

-- Not `@[simp]`: `realCliffordSpinContinuousMulEquivUnitsRange_apply` simplifies the inner
-- arguments, and `realCliffordSpinUnitsRangeBlockSum_apply` handles general inputs.
/-- Evaluating `realCliffordSpinUnitsRangeBlockSum` on canonical unit-range representatives applies
`realCliffordSpinBlockSum`. -/
theorem realCliffordSpinUnitsRangeBlockSum_apply_equiv (p q : ℕ)
    (x : realCliffordSpinGroupZero p) (y : realCliffordSpinGroupZero q) :
    realCliffordSpinUnitsRangeBlockSum p q
        (realCliffordSpinContinuousMulEquivUnitsRange p x,
          realCliffordSpinContinuousMulEquivUnitsRange q y) =
      realCliffordSpinContinuousMulEquivUnitsRange (p + q)
        (realCliffordSpinBlockSum p q (x, y)) := by
  simp

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

/-- Evaluating `realCliffordSpecialOrthogonalRangeBlockSum` transports
`realCliffordSpecialOrthogonalBlockSum` across
`realCliffordSpecialOrthogonalContinuousMulEquivRange`. -/
@[simp]
theorem realCliffordSpecialOrthogonalRangeBlockSum_apply (p q : ℕ)
    (u : MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin p → ℝ) from realCliffordForm p 0)) ×
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin q → ℝ) from realCliffordForm q 0))) :
    realCliffordSpecialOrthogonalRangeBlockSum p q u =
      realCliffordSpecialOrthogonalContinuousMulEquivRange (p + q)
        (realCliffordSpecialOrthogonalBlockSum p q
          ((realCliffordSpecialOrthogonalContinuousMulEquivRange p).symm u.1,
            (realCliffordSpecialOrthogonalContinuousMulEquivRange q).symm u.2)) :=
  (rfl)

-- Not `@[simp]`: `realCliffordSpecialOrthogonalContinuousMulEquivRange_apply` simplifies the inner
-- arguments, and `realCliffordSpecialOrthogonalRangeBlockSum_apply` handles general inputs.
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
  simp

/-- **Block sum commutes with `realCliffordSpinToSpecialOrthogonalRange`.** -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_comp_blockSum (p q : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRange (p + q)).comp
        (realCliffordSpinUnitsRangeBlockSum p q) =
      (realCliffordSpecialOrthogonalRangeBlockSum p q).comp
        ((realCliffordSpinToSpecialOrthogonalRange p).prodMap
          (realCliffordSpinToSpecialOrthogonalRange q)) :=
  ContinuousMonoidHom.ext fun _ ↦ by simp

/-! ### Obstructions to continuous lifts and open one-block rotation path -/

/-- **No continuous lift of the left one-block embedding `g ↦ diag(g, I_m)`** for rank `n + 2`:
the corresponding Spin block inclusion `x ↦ realCliffordSpinBlockSum (n + 2) m (x, 1)` sends `-1`
to `-1`, whereas the doubled Spin map `x ↦ realCliffordSpinBlockSum (n + 2) (n + 2) (x, x)` sends
`-1` to `1`. -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one (n m : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + m),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + m) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum (n + 2) m (g, 1) := by
  have : NeZero ((n + 2) + m) := ⟨by omega⟩
  exact not_exists_continuous_lift_of_spinLift_monoidHom
    ((realCliffordSpinBlockSum (n + 2) m).comp (MonoidHom.inl _ _))
    ((continuous_realCliffordSpinBlockSum (n + 2) m).comp (continuous_id.prodMk continuous_const))
    (fun x ↦ by simp)
    (by
      dsimp [MonoidHom.inl]
      rw [realCliffordSpinBlockSum_mk_one,
        (realCliffordSpinBlockInlIsometry (n + 2) m).spinGroupMap_negOne])

/-- **No continuous lift of the right one-block embedding `g ↦ diag(I_m, g)`** for rank `n + 2`:
the corresponding Spin block inclusion `x ↦ realCliffordSpinBlockSum m (n + 2) (1, x)` sends `-1`
to `-1`. -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk (m n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero (m + (n + 2)),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm (m + (n + 2)) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum m (n + 2) (1, g) := by
  have : NeZero (m + (n + 2)) := ⟨by omega⟩
  exact not_exists_continuous_lift_of_spinLift_monoidHom
    ((realCliffordSpinBlockSum m (n + 2)).comp (MonoidHom.inr _ _))
    ((continuous_realCliffordSpinBlockSum m (n + 2)).comp (continuous_const.prodMk continuous_id))
    (fun x ↦ by simp)
    (by
      dsimp [MonoidHom.inr]
      rw [realCliffordSpinBlockSum_one_mk,
        (realCliffordSpinBlockInrIsometry m (n + 2)).spinGroupMap_negOne])

/-- **No continuous lift of first-coordinate stabilization `SO(n + 2) → SO(n + 3)` to
`Spin(n + 3)`.** -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + 1),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + 1) 0) (f g) =
          realCliffordSpecialOrthogonalFirstInclusion (n + 2) g :=
  not_exists_continuous_lift_of_spinLift_monoidHom
    (realCliffordSpinFirstInclusion (n + 2))
    (continuous_realCliffordSpinFirstInclusion (n + 2))
    (spinToSpecialOrthogonal_realCliffordSpinFirstInclusion (n + 2))
    (realCliffordSpinFirstInclusion_negOne (n + 2))

/-- **Open path lift of a full `2π` coordinate-plane rotation under the one-block embedding
`g ↦ diag(g, I_m)`**: starting at `1`, the lifted path in `Spin(k + m)` ends at `-1 ≠ 1`. -/
def realCliffordSpinBlockSumRotationPath {k : ℕ} (m : ℕ) {i j : Fin k} (hij : i ≠ j) :
    Path (1 : realCliffordSpinGroupZero (k + m))
      (spinGroup.negOne (realCliffordForm (k + m) 0) (by
        have : NeZero (k + m) := ⟨Nat.add_pos_left (Fin.pos i) m |>.ne'⟩
        exact (nondegenerate_realCliffordForm (k + m) 0).ne_zero)) :=
  ((spinRotationPath (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)).map
    (f := fun x ↦ realCliffordSpinBlockSum k m (x, 1))
    ((continuous_realCliffordSpinBlockSum k m).comp
      (continuous_id.prodMk continuous_const))).cast
    (map_one (realCliffordSpinBlockSum k m)).symm (by
      rw [realCliffordSpinBlockSum_mk_one]
      exact ((realCliffordSpinBlockInlIsometry k m).spinGroupMap_negOne _).symm)

/-- Evaluating `realCliffordSpinBlockSumRotationPath` at `t` embeds the coordinate-plane rotation
at Spin angle `π t` into the left block of `Spin(k + m)`. -/
@[simp]
theorem realCliffordSpinBlockSumRotationPath_apply {k : ℕ} (m : ℕ) {i j : Fin k} (hij : i ≠ j)
    (t : unitInterval) :
    realCliffordSpinBlockSumRotationPath m hij t =
      realCliffordSpinBlockSum k m
        (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
          (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
          (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)), 1) := by
  simp [realCliffordSpinBlockSumRotationPath]

/-- The open path `realCliffordSpinBlockSumRotationPath` projects to the one-block embedding
`t ↦ diag(R(−2π t), I_m)` of the full-turn rotation loop in the ordered `(e_i, e_j)` coordinate
plane (where `Q(e_i) = Q(e_j) = 1`, so `spinRotation` at Spin angle `π t` projects to
`R(−2π t)`). -/
theorem spinToSpecialOrthogonal_realCliffordSpinBlockSumRotationPath {k : ℕ} (m : ℕ)
    {i j : Fin k} (hij : i ≠ j) (t : unitInterval) :
    spinToSpecialOrthogonal (realCliffordForm (k + m) 0)
        (realCliffordSpinBlockSumRotationPath m hij t) =
      realCliffordSpecialOrthogonalBlockSum k m
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ))),
          1) := by
  rw [realCliffordSpinBlockSumRotationPath_apply, spinToSpecialOrthogonal_realCliffordSpinBlockSum,
    map_one]

end

end TauCeti

end
