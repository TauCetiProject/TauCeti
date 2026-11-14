/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Analysis.Matrix.EuclideanLin
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

This file bridges the two models of `SO(n)`. Over any `RCLike` field `𝕜` and finite index type
`ι`, the star-algebra isomorphism `Matrix.toEuclideanCLM` restricts to a topological group
isomorphism between `Matrix.unitaryGroup ι 𝕜` and the unitary operator group of
`EuclideanSpace 𝕜 ι`; over `ℝ` it further restricts to determinant-one subgroups, identifying
`Matrix.specialOrthogonalGroup ι ℝ` with `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ ι)`.
Composing with `TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm`
identifies the quadratic-form group `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)`
with the Euclidean special orthogonal operator group, and composing with the Spin action produces
the continuous surjective homomorphism
`TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal` from `Spin(n)` onto the
Euclidean special orthogonal group.

In every dimension this homomorphism is a covering map, an open map, and a quotient map. In
positive dimension its kernel is `{1, -1}` and it is a quotient covering map by that kernel.

## Main definitions

* `TauCeti.instFactCardEqFinrankEuclideanSpace`: `Fact` instance recording
  `Fintype.card ι = Module.finrank 𝕜 (EuclideanSpace 𝕜 ι)`.
* `TauCeti.matrixUnitaryContinuousMulEquivEuclidean`: topological group isomorphism between unitary
  matrices and unitary operators on `EuclideanSpace 𝕜 ι`.
* `TauCeti.matrixSpecialOrthogonalContinuousMulEquivEuclidean`: topological group isomorphism
  between real special orthogonal matrices and
  `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ ι)`.
* `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalContinuousMulEquivEuclidean`: topological
  group isomorphism between `QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)` and
  `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))`.
* `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal`: the compact real Spin
  projection onto `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))`.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal_apply_apply`: the Euclidean
  Spin projection acts on coordinates by `CliffordAlgebra.spinVectorAction`.
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

/-- The cardinality of `ι` equals the dimension of `EuclideanSpace 𝕜 ι`, recorded as a `Fact` for
rank-indexed APIs such as `TauCeti.OrthonormalFrameBundle.orientedFrames`. -/
instance instFactCardEqFinrankEuclideanSpace (𝕜 ι : Type*) [RCLike 𝕜] [Fintype ι] :
    Fact (Fintype.card ι = Module.finrank 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨(finrank_euclideanSpace (𝕜 := 𝕜) (ι := ι)).symm⟩

section MatrixUnitary

variable (ι 𝕜 : Type*) [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Unitary `ι × ι` matrices over `𝕜` and unitary operators on `EuclideanSpace 𝕜 ι` are isomorphic
as topological groups via `Matrix.toEuclideanCLM`. -/
def matrixUnitaryContinuousMulEquivEuclidean :
    Matrix.unitaryGroup ι 𝕜 ≃ₜ*
      unitary (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) where
  toFun A := ⟨Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A.1,
    Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)) A.2⟩
  invFun u := ⟨(Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm u.1,
    Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm u.2⟩
  left_inv A := Subtype.ext <| StarAlgEquiv.symm_apply_apply _ A.1
  right_inv u := Subtype.ext <| StarAlgEquiv.apply_symm_apply _ u.1
  map_mul' A B := Subtype.ext <| map_mul (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)) A.1 B.1
  continuous_toFun :=
    (Matrix.continuous_toEuclideanCLM.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (Matrix.continuous_toEuclideanCLM_symm.comp continuous_subtype_val).subtype_mk _

variable {ι 𝕜}

@[simp]
theorem coe_matrixUnitaryContinuousMulEquivEuclidean (A : Matrix.unitaryGroup ι 𝕜) :
    (matrixUnitaryContinuousMulEquivEuclidean ι 𝕜 A :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) (A : Matrix ι ι 𝕜) :=
  (rfl)

@[simp]
theorem coe_matrixUnitaryContinuousMulEquivEuclidean_symm
    (u : unitary (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι)) :
    ((matrixUnitaryContinuousMulEquivEuclidean ι 𝕜).symm u : Matrix ι ι 𝕜) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm
        (u : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
  (rfl)

theorem matrixUnitaryContinuousMulEquivEuclidean_apply_apply (A : Matrix.unitaryGroup ι 𝕜)
    (v : EuclideanSpace 𝕜 ι) :
    (matrixUnitaryContinuousMulEquivEuclidean ι 𝕜 A :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) v =
      Matrix.toEuclideanLin (A : Matrix ι ι 𝕜) v :=
  Matrix.toEuclideanCLM_apply (A : Matrix ι ι 𝕜) v

end MatrixUnitary

section MatrixSpecialOrthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mem_unitaryGroup_real_iff_mem_orthogonalGroup {A : Matrix ι ι ℝ} :
    A ∈ Matrix.unitaryGroup ι ℝ ↔ A ∈ Matrix.orthogonalGroup ι ℝ := by
  simp [Matrix.mem_unitaryGroup_iff]

variable (ι) in
/-- Real special orthogonal `ι × ι` matrices and the special orthogonal operator group of
`EuclideanSpace ℝ ι` are isomorphic as topological groups via `Matrix.toEuclideanCLM`. -/
def matrixSpecialOrthogonalContinuousMulEquivEuclidean :
    Matrix.specialOrthogonalGroup ι ℝ ≃ₜ* specialOrthogonalGroup (EuclideanSpace ℝ ι) where
  toFun A :=
    ⟨matrixUnitaryContinuousMulEquivEuclidean ι ℝ
        ⟨A.1, mem_unitaryGroup_real_iff_mem_orthogonalGroup.2 A.2.1⟩,
      mem_specialOrthogonalGroup_iff.2 <| by
        rw [coe_matrixUnitaryContinuousMulEquivEuclidean, Matrix.det_toEuclideanCLM]
        exact A.2.2⟩
  invFun g :=
    ⟨((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).symm g.1).1,
      mem_unitaryGroup_real_iff_mem_orthogonalGroup.1
        ((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).symm g.1).2,
      MonoidHom.mem_mker.2 <| by
        have hg : (g.1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι).det = 1 :=
          mem_specialOrthogonalGroup_iff.1 g.2
        simpa [coe_matrixUnitaryContinuousMulEquivEuclidean_symm,
          ← Matrix.det_toEuclideanCLM (ι := ι) (𝕜 := ℝ)] using hg⟩
  left_inv A := Subtype.ext <| by
    simpa only [coe_matrixUnitaryContinuousMulEquivEuclidean,
      coe_matrixUnitaryContinuousMulEquivEuclidean_symm] using
      StarAlgEquiv.symm_apply_apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A.1
  right_inv g := Subtype.ext <| Subtype.ext <| by
    simpa only [coe_matrixUnitaryContinuousMulEquivEuclidean,
      coe_matrixUnitaryContinuousMulEquivEuclidean_symm] using
      StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) g.1.1
  map_mul' A B := Subtype.ext <| Subtype.ext <| by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul,
      coe_matrixUnitaryContinuousMulEquivEuclidean]
    exact map_mul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A.1 B.1
  continuous_toFun :=
    (((Matrix.continuous_toEuclideanCLM.comp continuous_subtype_val).subtype_mk _).subtype_mk _)
  continuous_invFun :=
    ((Matrix.continuous_toEuclideanCLM_symm.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)

@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    ((matrixSpecialOrthogonalContinuousMulEquivEuclidean ι A :
        unitary (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (A : Matrix ι ι ℝ) :=
  (rfl)

@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean_symm
    (g : specialOrthogonalGroup (EuclideanSpace ℝ ι)) :
    (((matrixSpecialOrthogonalContinuousMulEquivEuclidean ι).symm g :
        Matrix.specialOrthogonalGroup ι ℝ) : Matrix ι ι ℝ) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
        ((g : unitary (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) :
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  (rfl)

end MatrixSpecialOrthogonal

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
  rw [realCliffordSpecialOrthogonalContinuousMulEquivEuclidean, ContinuousMulEquiv.trans_apply,
    coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean, Matrix.toEuclideanCLM_apply,
    QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_symm_coe]
  have hlin : Matrix.toEuclideanLin (LinearMap.toMatrix'
      (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap) v =
      WithLp.toLp 2 (Matrix.toLin' (LinearMap.toMatrix'
        (g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap) v.ofLp) := rfl
  rw [hlin, Matrix.toLin'_toMatrix', LinearEquiv.coe_coe]

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
  have hfn :
      ⇑(realCliffordSpinToEuclideanSpecialOrthogonal n) =
        ⇑(realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).toHomeomorph ∘
          ⇑(realCliffordSpinDoubleCoverZero n).rightHom := by
    rw [realCliffordSpinToEuclideanSpecialOrthogonal_eq_comp n, coe_realCliffordSpinProjectionZero]
    rfl
  rw [hfn, hker]
  exact (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).homeomorph_comp
    (realCliffordSpecialOrthogonalContinuousMulEquivEuclidean n).toHomeomorph

end PositiveRank

end CliffordAlgebra

end TauCeti
