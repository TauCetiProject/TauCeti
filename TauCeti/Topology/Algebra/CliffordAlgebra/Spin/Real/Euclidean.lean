/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Analysis.Matrix.SpecialOrthogonal
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

/-!
# The real Spin projection onto the Euclidean special orthogonal operator group

The orthonormal frame bundle of a Riemannian vector bundle of rank `n`, modelled on
`EuclideanSpace ℝ (Fin n)`, has structure group `unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] _)`, and
its positively oriented frames have structure group
`TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))` in the operator-norm topology. By
contrast, the compact real Spin group `CliffordAlgebra.realCliffordSpinGroupZero n` is defined on
the coordinate quadratic form `CliffordAlgebra.realCliffordForm n 0`, whose special orthogonal
group consists of form-preserving linear equivalences of `Fin n → ℝ`.

This file bridges the two models of `SO(n)`. Composing
`TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm` with
`TauCeti.matrixSpecialOrthogonalContinuousMulEquivEuclidean` identifies the quadratic-form group
`QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` with the Euclidean special orthogonal
operator group `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))`, and composing with the
Spin action produces the continuous surjective homomorphism
`TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal` from `Spin(n)` onto the
Euclidean special orthogonal group.

In every dimension this homomorphism is a covering map, an open map, and a quotient map. In
positive dimension its kernel is `{1, -1}` and it is a quotient covering map by that kernel.

## Main definitions

* `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalContinuousMulEquivEuclidean`: topological
  group isomorphism between `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` and
  `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))`.
* `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal`: the compact real Spin
  projection onto `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))`.

## Main results

* `TauCeti.CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply` and
  `TauCeti.CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply`: the
  quadratic-form group acts on coordinates by Euclidean isometries, continuously in the group
  element.
* `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal_apply_apply`: the Euclidean
  Spin projection acts on coordinates by `CliffordAlgebra.spinVectorAction`.
* `TauCeti.CliffordAlgebra.coe_symm_realCliffordSpinProjectionZero_apply`: column `j` of the
  matrix of the compact Spin projection of `g` is the action of `g` on the basis vector `eⱼ`.
* `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal_surjective`: the Euclidean
  Spin projection is surjective in every dimension.
* `TauCeti.CliffordAlgebra.mem_ker_realCliffordSpinToEuclideanSpecialOrthogonal_iff` and
  `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal_eq_iff`: in positive
  dimension, the kernel is `{1, -1}` and fibres are cosets of `{1, -1}`.
* `TauCeti.CliffordAlgebra.isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal` and
  `TauCeti.CliffordAlgebra.isQuotientCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal`: the
  Euclidean Spin projection is a covering map (and a quotient covering map in positive dimension).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter I, §2.
-/

public section

noncomputable section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

/-- The special orthogonal group of the positive-definite form `realCliffordForm n 0` on
`Fin n → ℝ` is isomorphic as a topological group to the special orthogonal operator group of
`EuclideanSpace ℝ (Fin n)`. -/
def realCliffordSpecialOrthogonalContinuousMulEquivEuclidean (n : ℕ) :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) ≃ₜ*
      specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) :=
  (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n).symm.trans
    (matrixSpecialOrthogonalContinuousMulEquivEuclidean (Fin n))

/-- An element of `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` acts on
`EuclideanSpace ℝ (Fin n)` by applying its underlying linear equivalence to coordinates. -/
@[simp]
theorem realCliffordSpecialOrthogonalContinuousMulEquivEuclidean_apply_apply (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0))
    (v : EuclideanSpace ℝ (Fin n)) :
    (((realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n g :
        specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) :
      unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) v =
      WithLp.toLp 2 ((g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v.ofLp) := by
  simp [realCliffordSpecialOrthogonalContinuousMulEquivEuclidean, Matrix.toLpLin_apply]

/-- An element of `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` preserves the
Euclidean norm of coordinate vectors. -/
theorem norm_toLp_specialOrthogonalGroup_realCliffordForm_apply (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v)‖ = ‖WithLp.toLp 2 v‖ := by
  have h := Unitary.norm_map (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n g :
    unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (WithLp.toLp 2 v)
  rwa [realCliffordSpecialOrthogonalContinuousMulEquivEuclidean_apply_apply,
    WithLp.ofLp_toLp] at h

/-- Applying an element of `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` to a
fixed coordinate vector is continuous in the group element. -/
@[fun_prop]
theorem continuous_specialOrthogonalGroup_realCliffordForm_apply (n : ℕ) (v : Fin n → ℝ) :
    Continuous fun g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) ↦
      (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v := by
  have h : Continuous fun g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) ↦
      ((((realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n g :
          specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) :
        unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)).ofLp :=
    (PiLp.continuous_ofLp 2 _).comp <| (continuous_subtypeVal.comp <| continuous_subtypeVal.comp
      (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).continuous).clm_apply
        continuous_const
  simpa using h

/-- The compact real Spin projection onto the special orthogonal operator group of
`EuclideanSpace ℝ (Fin n)`, bundled as a continuous group homomorphism. -/
def realCliffordSpinToEuclideanSpecialOrthogonal (n : ℕ) :
    realCliffordSpinGroupZero n →ₜ* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) where
  toMonoidHom :=
    (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).toMonoidHom.comp
      (spinToSpecialOrthogonal (realCliffordForm n 0))
  continuous_toFun :=
    (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).continuous.comp
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))

theorem realCliffordSpinToEuclideanSpecialOrthogonal_apply (n : ℕ)
    (g : realCliffordSpinGroupZero n) :
    realCliffordSpinToEuclideanSpecialOrthogonal n g =
      realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n
        (spinToSpecialOrthogonal (realCliffordForm n 0) g) :=
  (rfl)

/-- In positive dimension, the Euclidean Spin projection factors as `realCliffordSpinProjectionZero`
followed by `realCliffordSpecialOrthogonalContinuousMulEquivEuclidean`. -/
theorem realCliffordSpinToEuclideanSpecialOrthogonal_eq_comp (n : ℕ) [NeZero n] :
    ⇑(realCliffordSpinToEuclideanSpecialOrthogonal n) =
      realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n ∘
        realCliffordSpinProjectionZero n := by
  funext g
  simp [realCliffordSpinToEuclideanSpecialOrthogonal_apply, realCliffordSpinProjectionZero_apply]

/-- The entries of the special orthogonal matrix underlying the compact Spin projection of `g`:
column `j` is the image of the standard basis vector `eⱼ` under the action of `g`. -/
theorem coe_symm_realCliffordSpinProjectionZero_apply (n : ℕ) [NeZero n]
    (g : realCliffordSpinGroupZero n) (i j : Fin n) :
    ((QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm n).symm
        (realCliffordSpinProjectionZero n g) : Matrix (Fin n) (Fin n) ℝ) i j =
      spinVectorAction (realCliffordForm n 0) g (Pi.single j 1) i := by
  simp [QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_symm_coe,
    LinearMap.toMatrix'_apply, realCliffordSpinProjectionZero_apply,
    realCliffordSpinDoubleCoverZero_rightHom]

/-- The Euclidean Spin projection acts on `EuclideanSpace ℝ (Fin n)` by
`CliffordAlgebra.spinVectorAction` on coordinates. -/
@[simp]
theorem realCliffordSpinToEuclideanSpecialOrthogonal_apply_apply (n : ℕ)
    (g : realCliffordSpinGroupZero n) (v : EuclideanSpace ℝ (Fin n)) :
    (((realCliffordSpinToEuclideanSpecialOrthogonal n g :
        specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) :
      unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) v =
      WithLp.toLp 2 (spinVectorAction (realCliffordForm n 0) g v.ofLp) := by
  rw [realCliffordSpinToEuclideanSpecialOrthogonal_apply,
    realCliffordSpecialOrthogonalContinuousMulEquivEuclidean_apply_apply,
    coe_spinToSpecialOrthogonal_apply]

/-- The kernel of the Euclidean Spin projection equals the kernel of `spinToSpecialOrthogonal`. -/
theorem ker_realCliffordSpinToEuclideanSpecialOrthogonal (n : ℕ) :
    MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) =
      MonoidHom.ker (spinToSpecialOrthogonal (realCliffordForm n 0)) := by
  ext g
  simp only [MonoidHom.mem_ker]
  exact map_eq_one_iff (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n)
    (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).injective

/-- The compact real Spin projection onto the Euclidean special orthogonal group is surjective in
every dimension. -/
theorem realCliffordSpinToEuclideanSpecialOrthogonal_surjective (n : ℕ) :
    Function.Surjective (realCliffordSpinToEuclideanSpecialOrthogonal n) :=
  (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).surjective.comp
    (spinToSpecialOrthogonal_surjective_of_posDef (realCliffordForm n 0)
      (posDef_realCliffordForm_zero n))

/-- The Euclidean Spin projection is a covering map in every dimension. -/
theorem isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal (n : ℕ) :
    IsCoveringMap (realCliffordSpinToEuclideanSpecialOrthogonal n) := by
  obtain rfl | hn := n.eq_zero_or_pos
  · have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    have : Subsingleton (realCliffordSpinGroupZero 0) := inferInstance
    have : Subsingleton (specialOrthogonalGroup (EuclideanSpace ℝ (Fin 0))) :=
      (realCliffordSpinToEuclideanSpecialOrthogonal_surjective 0).subsingleton
    exact .of_discreteTopology _
  · have : NeZero n := ⟨hn.ne'⟩
    rw [realCliffordSpinToEuclideanSpecialOrthogonal_eq_comp n]
    exact (isCoveringMap_realCliffordSpinProjectionZero n).homeomorph_comp
      (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).toHomeomorph

/-- The Euclidean Spin projection is an open map in every dimension. -/
theorem isOpenMap_realCliffordSpinToEuclideanSpecialOrthogonal (n : ℕ) :
    IsOpenMap (realCliffordSpinToEuclideanSpecialOrthogonal n) :=
  (isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal n).isOpenMap

/-- The Euclidean Spin projection is a quotient map in every dimension. -/
theorem isQuotientMap_realCliffordSpinToEuclideanSpecialOrthogonal (n : ℕ) :
    Topology.IsQuotientMap (realCliffordSpinToEuclideanSpecialOrthogonal n) :=
  (isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal n).isQuotientMap
    (realCliffordSpinToEuclideanSpecialOrthogonal_surjective n)

section PositiveRank

variable (n : ℕ) [NeZero n]

/-- The central element `-1` of `Spin(n)` maps to `1` in the Euclidean special orthogonal group. -/
@[simp]
theorem realCliffordSpinToEuclideanSpecialOrthogonal_negOne :
    realCliffordSpinToEuclideanSpecialOrthogonal n
        (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero) =
      1 := by
  simp [realCliffordSpinToEuclideanSpecialOrthogonal_apply]

/-- In positive dimension, an element of `Spin(n)` lies in the kernel of the Euclidean Spin
projection if and only if it is `1` or `-1`. -/
theorem mem_ker_realCliffordSpinToEuclideanSpecialOrthogonal_iff
    {g : realCliffordSpinGroupZero n} :
    g ∈ MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) ↔
      g = 1 ∨
        g = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero := by
  have : Nontrivial (Fin (n + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin n → ℝ))
  rw [ker_realCliffordSpinToEuclideanSpecialOrthogonal,
    mem_ker_spinToSpecialOrthogonal_iff (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0)]

/-- An element of `Spin(n)` maps to `1` in the Euclidean special orthogonal group if and only if it
is `1` or `-1`. -/
theorem realCliffordSpinToEuclideanSpecialOrthogonal_eq_one_iff
    {g : realCliffordSpinGroupZero n} :
    realCliffordSpinToEuclideanSpecialOrthogonal n g = 1 ↔
      g = 1 ∨
        g = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero :=
  mem_ker_realCliffordSpinToEuclideanSpecialOrthogonal_iff n

/-- Two elements of `Spin(n)` have the same image in the Euclidean special orthogonal group if and
only if they are equal or differ by `-1`. -/
theorem realCliffordSpinToEuclideanSpecialOrthogonal_eq_iff
    {g h : realCliffordSpinGroupZero n} :
    realCliffordSpinToEuclideanSpecialOrthogonal n g =
        realCliffordSpinToEuclideanSpecialOrthogonal n h ↔
      g = h ∨
        g = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero * h := by
  rw [← div_eq_one, ← map_div, realCliffordSpinToEuclideanSpecialOrthogonal_eq_one_iff]
  exact or_congr div_eq_one div_eq_iff_eq_mul

/-- In positive dimension, the Euclidean Spin projection is a quotient covering map by its
kernel. -/
theorem isQuotientCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal :
    IsQuotientCoveringMap (realCliffordSpinToEuclideanSpecialOrthogonal n)
      (MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)))) := by
  have hker :
      MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
          realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) =
        (realCliffordSpinDoubleCoverZero n).rightHom.ker := by
    rw [ker_realCliffordSpinToEuclideanSpecialOrthogonal, realCliffordSpinDoubleCoverZero_rightHom]
  rw [hker, realCliffordSpinToEuclideanSpecialOrthogonal_eq_comp n,
    coe_realCliffordSpinProjectionZero]
  exact (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).homeomorph_comp
    (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).toHomeomorph

end PositiveRank

end CliffordAlgebra

end TauCeti
