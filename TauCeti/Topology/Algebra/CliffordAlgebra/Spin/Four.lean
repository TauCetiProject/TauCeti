/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.QuaternionProduct
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Even

/-!
# Topological Spin groups in dimension at most four

Over a complete nontrivially normed field `K` of characteristic not two, finite-dimensionality of
`even Q` for `0 < finrank K V ≤ 4` upgrades
`CliffordAlgebra.spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour` without compactness to
`spinGroup Q ≃ₜ* unitary A`, and `CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd` to
`spinGroup Q ≃ₜ* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]`.

## Main definitions and results

* `CliffordAlgebra.spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour` and
  `CliffordAlgebra.continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour`.
* `CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd` and
  `CliffordAlgebra.continuous_spinGroupEquivQuaternionUnitaryProd`.
-/

public section

open Module
open scoped Quaternion

namespace CliffordAlgebra

universe u v w

variable {K : Type u} {V : Type v} [NontriviallyNormedField K] [CompleteSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V]

section Unitary

variable {A : Type w} [Ring A] [Algebra K A] [StarMul A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul K A]
  (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
  (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A) (he : ∀ x, e (reverseEven Q x) = star (e x))

/-- Continuity of `spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour`. -/
@[fun_prop]
theorem continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour :
    Continuous (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  let _ : IsTopologicalAddGroup (even Q) := (even Q).toSubmodule.isTopologicalAddGroup
  refine continuous_induced_rng.mpr <|
    (e.toLinearMap.continuous_of_finiteDimensional.comp (continuous_spinGroupToEven Q)).congr
      fun s ↦ ?_
  rw [Function.comp_apply, Function.comp_apply,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply,
    evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, AlgEquiv.toLinearMap_apply]

variable [T2Space A]

/-- **Topological-group low-rank Spin unitary equivalence** `spinGroup Q ≃ₜ* unitary A`. -/
noncomputable def spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour :
    spinGroup Q ≃ₜ* unitary A where
  toMulEquiv := spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he
  continuous_toFun := continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he
  continuous_invFun := by
    let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
    let _ : IsTopologicalAddGroup (even Q) := (even Q).toSubmodule.isTopologicalAddGroup
    let eL : even Q ≃L[K] A := e.toLinearEquiv.toContinuousLinearEquiv
    exact continuous_induced_rng.mpr <|
      (continuous_subtypeVal.comp (eL.symm.continuous.comp continuous_subtypeVal)).congr
        fun q ↦ by simp [eL]

/-- Forward evaluation of `spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour`. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour_apply (s : spinGroup Q) :
    spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he s =
      spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he s := (rfl)

/-- Inverse of `spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour`. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour_symm_apply (q : unitary A) :
    (spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q =
      (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q := (rfl)

end Unitary

section QuaternionProduct

variable (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
  {a b : K} [TopologicalSpace ℍ[K,a,0,b]] [IsTopologicalAddGroup ℍ[K,a,0,b]]
  [ContinuousSMul K ℍ[K,a,0,b]] [T2Space ℍ[K,a,0,b]]
  (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b]) (he : ∀ x, e (reverseEven Q x) = star (e x))

/-- **Topological-group quaternary quaternion-product Spin equivalence**. -/
noncomputable def spinGroupContinuousMulEquivQuaternionUnitaryProd :
    spinGroup Q ≃ₜ* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b] :=
  (spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ (by omega) (by omega) e
    he).trans (Unitary.prodContinuousMulEquiv ℍ[K,a,0,b] ℍ[K,a,0,b])

/-- Forward evaluation of `spinGroupContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp]
theorem spinGroupContinuousMulEquivQuaternionUnitaryProd_apply (s : spinGroup Q) :
    spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s =
      spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s := by
  have h1 : (((spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s).1 : ℍ[K,a,0,b]),
      ((spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s).2 : ℍ[K,a,0,b])) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
    simp [spinGroupContinuousMulEquivQuaternionUnitaryProd]
  have h := h1.trans (coe_spinGroupEquivQuaternionUnitaryProd_apply Q hQ hV e he s).symm
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- Inverse of `spinGroupContinuousMulEquivQuaternionUnitaryProd`. -/
@[simp]
theorem spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]) :
    (spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he).symm q =
      (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he).symm q :=
  (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he).injective <| by
    rw [MulEquiv.apply_symm_apply, ← spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
      ContinuousMulEquiv.apply_symm_apply]

/-- Continuity of `spinGroupEquivQuaternionUnitaryProd`. -/
@[fun_prop]
theorem continuous_spinGroupEquivQuaternionUnitaryProd :
    Continuous (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he) :=
  (map_continuous (spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he)).congr
    (spinGroupContinuousMulEquivQuaternionUnitaryProd_apply Q hQ hV e he)

end QuaternionProduct

end CliffordAlgebra

end
