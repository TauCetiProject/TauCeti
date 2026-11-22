/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.DiagonalLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# Topology, uniqueness, and obstruction for the compact real diagonal Spin lift

This module develops the topological properties of the compact real diagonal Spin lift
`TauCeti.realCliffordSpinDiagonalLift k : SO(k) →* Spin(k + k)`:

* **Continuity and closed embedding**: because the compact Spin projection `Spin(k) → SO(k)` is a
  continuous surjection from a compact space to a Hausdorff space, it is a quotient map; continuity
  of `realCliffordSpinDiagonalLift k` descends immediately from
  `continuous_realCliffordSpinBlockSum` along the projection square. Compactness of `SO(k)` and
  injectivity yield a closed topological embedding.
* **Carrier and matrix models**: transporting across the closed unit-group carrier equivalences of
  `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection` gives the continuous carrier lift
  `TauCeti.realCliffordSpecialOrthogonalRangeDiagonalLift k`, and precomposing with
  `TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm k` gives the
  matrix-group lift
  `TauCeti.matrixSpecialOrthogonalSpinDiagonalLift k : SO(Fin k, ℝ) →ₜ* Spin(k + k)`.
* **Uniqueness of continuous lifts**: because `SO(k)` is connected and `Spin(k + k) → SO(k + k)`
  is a covering map in positive rank, any continuous map `SO(k) → Spin(k + k)` lifting
  `g ↦ diag(g, g)` and sending `1` to `1` (in particular, any continuous homomorphism lifting
  `g ↦ diag(g, g)`) must equal `realCliffordSpinDiagonalLift k`, and any continuous lift without
  basepoint normalization equals either `realCliffordSpinDiagonalLift k` or its translate by the
  central element `-1`.
* **Obstruction to one-block lifts**: for `k = n + 2 ≥ 2`, no continuous map lifts the identity
  `SO(n + 2) → SO(n + 2)`, either one-block embedding `g ↦ diag(g, I_m)` or `g ↦ diag(I_m, g)`, or
  the first-coordinate stabilization `SO(n + 2) → SO(n + 3)` to the corresponding Spin group. This
  follows from covering-space lift uniqueness applied to a path from `1` to `-1` in `Spin(n + 2)`;
  in particular, a full `2π` coordinate-plane rotation loop lifts under
  `realCliffordSpinDiagonalLift` to a closed loop (`1` to `1`), whereas under the one-block
  embedding `g ↦ diag(g, I_m)` it lifts from `1` to `-1 ≠ 1`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLiftContinuousMonoidHom`: the bundled continuous homomorphism
  `SO(k) →ₜ* Spin(k + k)`.
* `TauCeti.realCliffordSpecialOrthogonalRangeDiagonalLift`: the continuous diagonal lift between
  the closed `GL(k, ℝ)` and Clifford-unit range carriers.
* `TauCeti.matrixSpecialOrthogonalSpinDiagonalLift`: the continuous diagonal lift from the matrix
  group `Matrix.specialOrthogonalGroup (Fin k) ℝ` to `Spin(k + k)`.
* `TauCeti.realCliffordSpinDiagonalLiftRotationLoop` and
  `TauCeti.realCliffordSpinBlockSumRotationPath`: explicit path lifts of a full `2π`
  coordinate-plane rotation under the diagonal lift (closed, `1` to `1`) versus a one-block
  embedding (open, `1` to `-1`).

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
* `TauCeti.not_exists_continuous_lift_of_spinLift_ne`,
  `TauCeti.not_exists_continuous_section_realCliffordSpin`,
  `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one`,
  `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk`, and
  `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion`: non-existence
  of continuous lifts for the identity, one-block embeddings, and stabilization in rank `≥ 2`.

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

/-- **The compact diagonal Spin lift on the closed unit-range carriers**, mapping the closed
`SO(k)` carrier in `GL(k, ℝ)` into the closed `Spin(k + k)` carrier in Clifford units. -/
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
/-- Evaluating `realCliffordSpecialOrthogonalRangeDiagonalLift` on a canonical matrix-range
representative applies `realCliffordSpinDiagonalLift`. -/
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
  refine (isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom (k + k)).eq_of_comp_eq
    hf (continuous_realCliffordSpinDiagonalLift k) ?_ 1 (by rw [h1, map_one])
  funext g
  simpa using (hlift g).trans (spinToSpecialOrthogonal_realCliffordSpinDiagonalLift k g).symm

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

/-! ### Obstruction to lifting one-block inclusions and full-turn loop comparison -/

/-- **General Spin-lift obstruction in rank `≥ 2`**: if a map `φ : SO(n + 2) → SO(N)` is covered by
a continuous map `ψ : Spin(n + 2) → Spin(N)` satisfying `ψ (-1) ≠ ψ 1`, then `φ` admits no
continuous lift `SO(n + 2) → Spin(N)`. -/
theorem not_exists_continuous_lift_of_spinLift_ne {n N : ℕ}
    {φ : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
      QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0)}
    {ψ : realCliffordSpinGroupZero (n + 2) → realCliffordSpinGroupZero N}
    (hψ_cont : Continuous ψ)
    (hψ_lift : ∀ x, spinToSpecialOrthogonal (realCliffordForm N 0) (ψ x) =
      φ (spinToSpecialOrthogonal (realCliffordForm (n + 2) 0) x))
    (hψ_ne : ψ (spinGroup.negOne (realCliffordForm (n + 2) 0)
        (nondegenerate_realCliffordForm (n + 2) 0).ne_zero) ≠ ψ 1) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero N,
      Continuous f ∧ ∀ g, spinToSpecialOrthogonal (realCliffordForm N 0) (f g) = φ g := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    exact absurd (Subsingleton.elim _ _) hψ_ne
  have : NeZero N := ⟨hN.ne'⟩
  rintro ⟨f, hf_cont, hf_lift⟩
  -- Normalize `f` so that it sends `1` to `ψ 1` while lifting the same map `φ`.
  have hφ1 : spinToSpecialOrthogonal (realCliffordForm N 0) (ψ 1) = φ 1 := by
    simpa using hψ_lift 1
  let f' : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
      realCliffordSpinGroupZero N := fun g ↦ ψ 1 * (f 1)⁻¹ * f g
  have hf'_lift : ∀ g, spinToSpecialOrthogonal (realCliffordForm N 0) (f' g) = φ g := fun g ↦ by
    simp [f', hf_lift, hφ1]
  -- Pull both lifts back along a path from `1` to `-1` in `Spin(n + 2)`.
  obtain ⟨γ⟩ := joined_one_negOne_realCliffordSpinGroupZero_add_two n
  have heq : (fun t : unitInterval ↦ f' (spinToSpecialOrthogonal (realCliffordForm (n + 2) 0)
      (γ t))) = fun t ↦ ψ (γ t) := by
    refine (isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom N).eq_of_comp_eq
      ((continuous_const.mul hf_cont).comp
        ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm (n + 2) 0)).comp γ.continuous))
      (hψ_cont.comp γ.continuous) ?_ 0 ?_
    · funext t
      simpa using (hf'_lift _).trans (hψ_lift (γ t)).symm
    · simp [f', γ.source]
  have h1 := congrFun heq 1
  simp only [γ.target, spinGroup.spinToSpecialOrthogonal_negOne, f', mul_assoc,
    inv_mul_cancel, mul_one] at h1
  exact hψ_ne h1.symm

/-- **The Spin double cover `Spin(n + 2) → SO(n + 2)` has no continuous section.** -/
theorem not_exists_continuous_section_realCliffordSpin (n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero (n + 2),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm (n + 2) 0) (f g) = g :=
  not_exists_continuous_lift_of_spinLift_ne (ψ := id) continuous_id (fun _ ↦ rfl)
    (spinGroup.negOne_ne_one _ _)

/-- **No continuous lift of the left one-block embedding `g ↦ diag(g, I_m)`** for rank `n + 2`:
unlike the doubled map `g ↦ diag(g, g)`, the one-block embedding sends the double-cover kernel
`-1` to `-1` rather than `1`. -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one (n m : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + m),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + m) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum (n + 2) m (g, 1) := by
  have : NeZero ((n + 2) + m) := ⟨by omega⟩
  refine not_exists_continuous_lift_of_spinLift_ne
    (ψ := fun x ↦ realCliffordSpinBlockSum (n + 2) m (x, 1))
    ((continuous_realCliffordSpinBlockSum (n + 2) m).comp (continuous_id.prodMk continuous_const))
    (fun x ↦ by simp) ?_
  rw [realCliffordSpinBlockSum_mk_one, realCliffordSpinBlockSum_mk_one, map_one,
    (realCliffordSpinBlockInlIsometry (n + 2) m).spinGroupMap_negOne
      (nondegenerate_realCliffordForm (n + 2) 0).ne_zero]
  exact spinGroup.negOne_ne_one _ _

/-- **No continuous lift of the right one-block embedding `g ↦ diag(I_m, g)`** for rank `n + 2`. -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk (m n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero (m + (n + 2)),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm (m + (n + 2)) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum m (n + 2) (1, g) := by
  have : NeZero (m + (n + 2)) := ⟨by omega⟩
  refine not_exists_continuous_lift_of_spinLift_ne
    (ψ := fun x ↦ realCliffordSpinBlockSum m (n + 2) (1, x))
    ((continuous_realCliffordSpinBlockSum m (n + 2)).comp (continuous_const.prodMk continuous_id))
    (fun x ↦ by simp) ?_
  rw [realCliffordSpinBlockSum_one_mk, realCliffordSpinBlockSum_one_mk, map_one,
    (realCliffordSpinBlockInrIsometry m (n + 2)).spinGroupMap_negOne
      (nondegenerate_realCliffordForm (n + 2) 0).ne_zero]
  exact spinGroup.negOne_ne_one _ _

/-- **No continuous lift of first-coordinate stabilization `SO(n + 2) → SO(n + 3)` to
`Spin(n + 3)`.** -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + 1),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + 1) 0) (f g) =
          realCliffordSpecialOrthogonalFirstInclusion (n + 2) g := by
  refine not_exists_continuous_lift_of_spinLift_ne
    (ψ := realCliffordSpinFirstInclusion (n + 2))
    (continuous_realCliffordSpinFirstInclusion (n + 2))
    (fun x ↦ spinToSpecialOrthogonal_realCliffordSpinFirstInclusion (n + 2) x) ?_
  rw [map_one, realCliffordSpinFirstInclusion_negOne]
  exact spinGroup.negOne_ne_one _ _

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
