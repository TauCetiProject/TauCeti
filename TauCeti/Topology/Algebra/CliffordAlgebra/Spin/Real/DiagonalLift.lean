/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.DiagonalLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering

/-!
# Topology, uniqueness, and full-turn loop for the compact real diagonal Spin lift

This module develops the topological properties of the compact real diagonal Spin lift
`TauCeti.realCliffordSpinDiagonalLift k : SO(k) →* Spin(k + k)`:

* **Continuity and closed embedding**: `realCliffordSpinDiagonalLift k` is continuous and a closed
  topological embedding `SO(k) → Spin(k + k)`, and is bundled as the continuous homomorphism
  `TauCeti.realCliffordSpinDiagonalLiftContinuousMonoidHom k : SO(k) →ₜ* Spin(k + k)`. Composing
  this bundled lift with continuous `SO(k)`-valued transition functions lifts doubled transition
  functions continuously to `Spin(k + k)`.
* **Carrier and matrix models**: transporting across the closed unit-group carrier equivalences of
  `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection` gives the continuous carrier lift
  `TauCeti.realCliffordSpecialOrthogonalRangeDiagonalLift k` out of the closed image of `SO(k)` in
  `GL(k, ℝ)`, and precomposing with
  `TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm k` gives the
  matrix-group lift
  `TauCeti.matrixSpecialOrthogonalSpinDiagonalLift k : SO(Fin k, ℝ) →ₜ* Spin(k + k)`.
* **Uniqueness of continuous lifts**: any continuous map `SO(k) → Spin(k + k)` lifting
  `g ↦ diag(g, g)` and sending `1` to `1` (in particular, any continuous homomorphism lifting
  `g ↦ diag(g, g)`) equals `realCliffordSpinDiagonalLift k`. In positive rank, any continuous lift
  without basepoint normalization equals either `realCliffordSpinDiagonalLift k` or its left
  translate by `-1`; in rank zero, `Spin(0)` is trivial and the continuous lift is unique.
* **Closed full-turn rotation loop**: a full `2π` coordinate-plane rotation loop lifts under
  `realCliffordSpinDiagonalLift k` to a closed loop (`1` to `1`) in `Spin(k + k)`, contrasting with
  the open path (`1` to `-1`) under a one-block embedding in
  `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLiftContinuousMonoidHom`: the bundled continuous homomorphism
  `SO(k) →ₜ* Spin(k + k)`.
* `TauCeti.realCliffordSpecialOrthogonalRangeDiagonalLift`: the continuous diagonal lift from the
  closed image of `SO(k)` in `GL(k, ℝ)` to the closed Clifford-unit range carrier of
  `Spin(k + k)`.
* `TauCeti.matrixSpecialOrthogonalSpinDiagonalLift`: the continuous diagonal lift from the matrix
  group `Matrix.specialOrthogonalGroup (Fin k) ℝ` to `Spin(k + k)`.
* `TauCeti.realCliffordSpinDiagonalLiftRotationLoop`: explicit closed loop lift (`1` to `1`) of a
  full `2π` coordinate-plane rotation under the diagonal lift.

## Main results

* `TauCeti.continuous_realCliffordSpinDiagonalLift`,
  `TauCeti.isClosedEmbedding_realCliffordSpinDiagonalLift`, and
  `TauCeti.isEmbedding_realCliffordSpinDiagonalLift`: continuity and closed-embedding properties.
* `TauCeti.realCliffordSpinToSpecialOrthogonalRange_comp_diagonalLift`: compatibility of the
  closed unit-range diagonal lift with `realCliffordSpinToSpecialOrthogonalRange`.
* `TauCeti.eq_realCliffordSpinDiagonalLift_of_continuous_lift`,
  `TauCeti.eq_or_eq_negOne_mul_realCliffordSpinDiagonalLift_of_continuous_lift`, and
  `TauCeti.eq_realCliffordSpinDiagonalLift_of_continuous_monoidHom_lift`: uniqueness of continuous
  and homomorphic diagonal lifts.
* `TauCeti.realCliffordSpinDiagonalLiftRotationLoop_apply` and
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinDiagonalLiftRotationLoop`: evaluation and
  projection of the closed diagonal rotation loop.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§2 and 6.
* A. Hatcher, *Algebraic Topology* (2002), Proposition 1.34 (uniqueness of lifts).
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-! ### Continuity and closed embedding -/

/-- **The compact real diagonal Spin lift `SO(k) → Spin(k + k)` is continuous.** -/
@[fun_prop]
theorem continuous_realCliffordSpinDiagonalLift (k : ℕ) :
    Continuous (realCliffordSpinDiagonalLift k) := by
  have hquot : Topology.IsQuotientMap (spinToSpecialOrthogonal (realCliffordForm k 0)) :=
    Topology.IsQuotientMap.of_surjective_continuous
      (spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero k))
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm k 0))
  refine hquot.continuous_iff.mpr ?_
  have hdiag : Continuous fun x : realCliffordSpinGroupZero k ↦
      realCliffordSpinBlockSum k k (x, x) :=
    (continuous_realCliffordSpinBlockSum k k).comp (continuous_id.prodMk continuous_id)
  exact hdiag.congr fun x ↦ (realCliffordSpinDiagonalLift_spinToSpecialOrthogonal k x).symm

/-- **The compact real diagonal Spin lift `SO(k) → Spin(k + k)` is a closed embedding.** -/
theorem isClosedEmbedding_realCliffordSpinDiagonalLift (k : ℕ) :
    Topology.IsClosedEmbedding (realCliffordSpinDiagonalLift k) :=
  (continuous_realCliffordSpinDiagonalLift k).isClosedEmbedding
    (realCliffordSpinDiagonalLift_injective k)

/-- **The compact real diagonal Spin lift `SO(k) → Spin(k + k)` is a topological embedding.** -/
theorem isEmbedding_realCliffordSpinDiagonalLift (k : ℕ) :
    Topology.IsEmbedding (realCliffordSpinDiagonalLift k) :=
  (isClosedEmbedding_realCliffordSpinDiagonalLift k).isEmbedding

/-- **The compact real diagonal Spin lift, bundled as a continuous homomorphism.** -/
def realCliffordSpinDiagonalLiftContinuousMonoidHom (k : ℕ) :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0) →ₜ*
      realCliffordSpinGroupZero (k + k) :=
  ⟨realCliffordSpinDiagonalLift k, continuous_realCliffordSpinDiagonalLift k⟩

/-- The underlying monoid homomorphism of `realCliffordSpinDiagonalLiftContinuousMonoidHom`. -/
@[simp]
theorem coeMonoidHom_realCliffordSpinDiagonalLiftContinuousMonoidHom (k : ℕ) :
    (realCliffordSpinDiagonalLiftContinuousMonoidHom k :
        QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0) →*
          realCliffordSpinGroupZero (k + k)) =
      realCliffordSpinDiagonalLift k :=
  (rfl)

/-- Evaluating `realCliffordSpinDiagonalLiftContinuousMonoidHom` applies
`realCliffordSpinDiagonalLift`. -/
@[simp]
theorem realCliffordSpinDiagonalLiftContinuousMonoidHom_apply (k : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0)) :
    realCliffordSpinDiagonalLiftContinuousMonoidHom k g = realCliffordSpinDiagonalLift k g :=
  (rfl)

/-! ### Compatibility with closed unit-range carriers and matrix `SO(Fin k, ℝ)` -/

/-- **The compact diagonal Spin lift on the closed unit-range carriers**, mapping the closed image
of `SO(k)` in `GL(k, ℝ)` into the closed `Spin(k + k)` carrier in Clifford units. -/
def realCliffordSpecialOrthogonalRangeDiagonalLift (k : ℕ) :
    -- `realCliffordForm k 0` lives on `Fin (k + 0) → ℝ`, which is `Fin k → ℝ` by definition;
    -- stating the carrier over `Fin k → ℝ` matches `realCliffordSpinToSpecialOrthogonalRange`.
    MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin k → ℝ) from realCliffordForm k 0)) →ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm (k + k) 0)) :=
  (realCliffordSpinContinuousMulEquivUnitsRange (k + k) :
      realCliffordSpinGroupZero (k + k) →ₜ* _).comp
    ((realCliffordSpinDiagonalLiftContinuousMonoidHom k).comp
      ((realCliffordSpecialOrthogonalContinuousMulEquivRange k).symm :
        _ →ₜ* QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0)))

/-- Evaluating `realCliffordSpecialOrthogonalRangeDiagonalLift` transports
`realCliffordSpinDiagonalLift` across the closed range equivalences. -/
@[simp]
theorem realCliffordSpecialOrthogonalRangeDiagonalLift_apply (k : ℕ)
    (u : MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin k → ℝ) from realCliffordForm k 0))) :
    realCliffordSpecialOrthogonalRangeDiagonalLift k u =
      realCliffordSpinContinuousMulEquivUnitsRange (k + k)
        (realCliffordSpinDiagonalLift k
          ((realCliffordSpecialOrthogonalContinuousMulEquivRange k).symm u)) :=
  (rfl)

-- Not `@[simp]`: `realCliffordSpecialOrthogonalContinuousMulEquivRange_apply` simplifies the inner
-- argument, and `realCliffordSpecialOrthogonalRangeDiagonalLift_apply` handles general inputs.
/-- Evaluating `realCliffordSpecialOrthogonalRangeDiagonalLift` on a canonical representative in
the closed image of `SO(k)` in `GL(k, ℝ)` applies `realCliffordSpinDiagonalLift`. -/
theorem realCliffordSpecialOrthogonalRangeDiagonalLift_apply_equiv (k : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0)) :
    realCliffordSpecialOrthogonalRangeDiagonalLift k
        (realCliffordSpecialOrthogonalContinuousMulEquivRange k g) =
      realCliffordSpinContinuousMulEquivUnitsRange (k + k) (realCliffordSpinDiagonalLift k g) := by
  simp

/-- **The closed unit-range diagonal lift commutes with
`realCliffordSpinToSpecialOrthogonalRange`.** -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_comp_diagonalLift (k : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRange (k + k)).comp
        (realCliffordSpecialOrthogonalRangeDiagonalLift k) =
      (realCliffordSpecialOrthogonalRangeBlockSum k k).comp
        ((ContinuousMonoidHom.id _).prod (ContinuousMonoidHom.id _)) :=
  ContinuousMonoidHom.ext fun _ ↦ by simp

/-- **The compact diagonal Spin lift on the matrix group `SO(Fin k, ℝ) →ₜ* Spin(k + k)`.** -/
def matrixSpecialOrthogonalSpinDiagonalLift (k : ℕ) :
    _root_.Matrix.specialOrthogonalGroup (Fin k) ℝ →ₜ* realCliffordSpinGroupZero (k + k) :=
  (realCliffordSpinDiagonalLiftContinuousMonoidHom k).comp
    (matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm k :
      _root_.Matrix.specialOrthogonalGroup (Fin k) ℝ →ₜ*
        QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0))

/-- Evaluating `matrixSpecialOrthogonalSpinDiagonalLift` converts the matrix to an isometry of
`realCliffordForm k 0` and applies `realCliffordSpinDiagonalLift`. -/
@[simp]
theorem matrixSpecialOrthogonalSpinDiagonalLift_apply (k : ℕ)
    (A : _root_.Matrix.specialOrthogonalGroup (Fin k) ℝ) :
    matrixSpecialOrthogonalSpinDiagonalLift k A =
      realCliffordSpinDiagonalLift k
        (matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm k A) :=
  (rfl)

/-- **The matrix-group diagonal Spin lift `SO(Fin k, ℝ) → Spin(k + k)` is a closed embedding.** -/
theorem isClosedEmbedding_matrixSpecialOrthogonalSpinDiagonalLift (k : ℕ) :
    Topology.IsClosedEmbedding (matrixSpecialOrthogonalSpinDiagonalLift k) :=
  (isClosedEmbedding_realCliffordSpinDiagonalLift k).comp
    (matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm
      k).toHomeomorph.isClosedEmbedding

-- Not `@[simp]`: `matrixSpecialOrthogonalSpinDiagonalLift_apply` simplifies the inner argument.
/-- **`matrixSpecialOrthogonalSpinDiagonalLift` acts diagonally by matrix-vector multiplication on
`Fin.append u v`.** -/
theorem spinVectorAction_matrixSpecialOrthogonalSpinDiagonalLift_append (k : ℕ)
    (A : _root_.Matrix.specialOrthogonalGroup (Fin k) ℝ) (u v : Fin k → ℝ) :
    spinVectorAction (realCliffordForm (k + k) 0) (matrixSpecialOrthogonalSpinDiagonalLift k A)
        (Fin.append u v : Fin (k + k) → ℝ) =
      Fin.append (_root_.Matrix.toLin' (A : _root_.Matrix (Fin k) (Fin k) ℝ) u)
        (_root_.Matrix.toLin' (A : _root_.Matrix (Fin k) (Fin k) ℝ) v) := by
  rw [matrixSpecialOrthogonalSpinDiagonalLift_apply,
    spinVectorAction_realCliffordSpinDiagonalLift_append,
    matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply,
    matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply]

/-! ### Uniqueness of continuous lifts -/

/-- **Uniqueness of continuous normalized diagonal lifts**: any continuous map
`SO(k) → Spin(k + k)` lifting `g ↦ diag(g, g)` and sending `1` to `1` equals
`realCliffordSpinDiagonalLift k`. -/
theorem eq_realCliffordSpinDiagonalLift_of_continuous_lift (k : ℕ)
    {f : QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0) →
      realCliffordSpinGroupZero (k + k)}
    (hf : Continuous f)
    (hlift : ∀ g, spinToSpecialOrthogonal (realCliffordForm (k + k) 0) (f g) =
      realCliffordSpecialOrthogonalBlockSum k k (g, g))
    (h1 : f 1 = 1) :
    f = realCliffordSpinDiagonalLift k := by
  obtain rfl | hk := k.eq_zero_or_pos
  · -- In rank zero `Spin(0)` is trivial (`Fin 0 → ℝ` is subsingleton).
    have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    exact funext fun _ ↦ Subsingleton.elim _ _
  have : NeZero (k + k) := ⟨by omega⟩
  refine (isCoveringMap_spinToSpecialOrthogonal_realCliffordForm (k + k)).eq_of_comp_eq
    hf (continuous_realCliffordSpinDiagonalLift k) ?_ 1 (by rw [h1, map_one])
  funext g
  exact (hlift g).trans (spinToSpecialOrthogonal_realCliffordSpinDiagonalLift k g).symm

/-- **Classification of all continuous diagonal lifts in positive rank**: any continuous map
`SO(k) → Spin(k + k)` lifting `g ↦ diag(g, g)` equals either `realCliffordSpinDiagonalLift k` or
its translate by the central element `-1`. -/
theorem eq_or_eq_negOne_mul_realCliffordSpinDiagonalLift_of_continuous_lift (k : ℕ) [NeZero k]
    {f : QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0) →
      realCliffordSpinGroupZero (k + k)}
    (hf : Continuous f)
    (hlift : ∀ g, spinToSpecialOrthogonal (realCliffordForm (k + k) 0) (f g) =
      realCliffordSpecialOrthogonalBlockSum k k (g, g)) :
    f = realCliffordSpinDiagonalLift k ∨
      ∀ g, f g = spinGroup.negOne (realCliffordForm (k + k) 0)
        (nondegenerate_realCliffordForm (k + k) 0).ne_zero * realCliffordSpinDiagonalLift k g := by
  have hk : 0 < k + k := by have := NeZero.pos k; omega
  have : NeZero (k + k) := ⟨hk.ne'⟩
  -- `realCliffordForm (k + k) 0` lives on `Fin ((k + k) + 0) → ℝ`, which is `Fin (k + k) → ℝ`.
  have : Nontrivial (Fin ((k + k) + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin (k + k) → ℝ))
  have hker : f 1 ∈ (spinToSpecialOrthogonal (realCliffordForm (k + k) 0)).ker := by
    rw [MonoidHom.mem_ker, hlift 1]
    exact map_one (realCliffordSpecialOrthogonalBlockSum k k)
  rcases (mem_ker_spinToSpecialOrthogonal_iff _ (nondegenerate_realCliffordForm (k + k) 0)
      (f 1)).mp hker with h1 | h1
  · exact Or.inl (eq_realCliffordSpinDiagonalLift_of_continuous_lift k hf hlift h1)
  · right
    set z := spinGroup.negOne (realCliffordForm (k + k) 0)
      (nondegenerate_realCliffordForm (k + k) 0).ne_zero
    have hzsq : z * z = 1 := Subtype.ext (by simp [z])
    have heq : (fun g ↦ z * f g) = realCliffordSpinDiagonalLift k :=
      eq_realCliffordSpinDiagonalLift_of_continuous_lift k (continuous_const.mul hf)
        (fun g ↦ by rw [map_mul, spinGroup.spinToSpecialOrthogonal_negOne, one_mul, hlift g])
        (by rw [h1, hzsq])
    intro g
    have hg := congrFun heq g
    calc
      f g = (z * z) * f g := by rw [hzsq, one_mul]
      _ = z * (z * f g) := mul_assoc z z (f g)
      _ = z * realCliffordSpinDiagonalLift k g := by rw [hg]

/-- **Uniqueness of continuous homomorphic diagonal lifts**: `realCliffordSpinDiagonalLift` is the
unique continuous group homomorphism `SO(k) →ₜ* Spin(k + k)` lifting `g ↦ diag(g, g)`. -/
theorem eq_realCliffordSpinDiagonalLift_of_continuous_monoidHom_lift (k : ℕ)
    (f : QuadraticMap.specialOrthogonalGroup (realCliffordForm k 0) →ₜ*
      realCliffordSpinGroupZero (k + k))
    (hlift : ∀ g, spinToSpecialOrthogonal (realCliffordForm (k + k) 0) (f g) =
      realCliffordSpecialOrthogonalBlockSum k k (g, g)) :
    f = realCliffordSpinDiagonalLiftContinuousMonoidHom k :=
  ContinuousMonoidHom.ext <| congrFun <|
    eq_realCliffordSpinDiagonalLift_of_continuous_lift k f.continuous hlift (map_one f)

/-! ### Closed full-turn rotation loop -/

/-- **Closed loop lift of a full `2π` coordinate-plane rotation under the diagonal Spin lift**:
in the ordered `(e_i, e_j)` coordinate plane (where `Q(e_i) = Q(e_j) = 1`, so `spinRotation` at
Spin angle `π t` projects to `R(−2π t)`), the path in `Spin(k + k)` lifting
`t ↦ diag(R(−2π t), R(−2π t))` starts and ends at `1`. -/
def realCliffordSpinDiagonalLiftRotationLoop {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    Path (1 : realCliffordSpinGroupZero (k + k)) 1 :=
  ((spinRotationPath (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)).map
    ((continuous_realCliffordSpinDiagonalLift k).comp
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm k 0)))).cast
    (by simp) (by simp)

/-- Evaluating `realCliffordSpinDiagonalLiftRotationLoop` at `t` gives the diagonal lift of the
coordinate-plane rotation at Spin angle `π t`. -/
@[simp]
theorem realCliffordSpinDiagonalLiftRotationLoop_apply {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (t : unitInterval) :
    realCliffordSpinDiagonalLiftRotationLoop hij t =
      realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)))) := by
  simp [realCliffordSpinDiagonalLiftRotationLoop]

/-- The closed loop `realCliffordSpinDiagonalLiftRotationLoop` projects to the diagonal block sum
of the coordinate-plane rotation loop. -/
theorem spinToSpecialOrthogonal_realCliffordSpinDiagonalLiftRotationLoop {k : ℕ} {i j : Fin k}
    (hij : i ≠ j) (t : unitInterval) :
    spinToSpecialOrthogonal (realCliffordForm (k + k) 0)
        (realCliffordSpinDiagonalLiftRotationLoop hij t) =
      realCliffordSpecialOrthogonalBlockSum k k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ))),
          spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)))) := by
  rw [realCliffordSpinDiagonalLiftRotationLoop_apply,
    spinToSpecialOrthogonal_realCliffordSpinDiagonalLift]

end

end TauCeti
