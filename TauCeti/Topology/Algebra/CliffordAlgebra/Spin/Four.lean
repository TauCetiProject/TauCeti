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

/-!
# Topological Spin groups in dimension at most four

Over a complete nontrivially normed field `K` of characteristic not two, a nondegenerate quadratic
form `Q` on a vector space of positive dimension at most four has a finite-dimensional Hausdorff
even Clifford algebra `even Q`. Any reversal-preserving `K`-algebra equivalence `e : even Q ≃ₐ[K] A`
into a Hausdorff topological `K`-algebra `A` is a continuous linear equivalence in both directions
by finite-dimensionality (`LinearEquiv.toContinuousLinearEquiv`), so the low-rank Spin equivalence
`CliffordAlgebra.spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour` upgrades without any compactness
hypothesis to a topological group isomorphism `spinGroup Q ≃ₜ* unitary A`.

Composing with `Unitary.prodContinuousMulEquiv` upgrades the quaternary quaternion-product Spin
equivalence `CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd` to
`spinGroup Q ≃ₜ* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]`.

## Main definitions and results

* `CliffordAlgebra.continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour` and
  `CliffordAlgebra.spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour`: topological-group
  upgrade of `spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour`.
* `CliffordAlgebra.continuous_spinGroupEquivQuaternionUnitaryProd` and
  `CliffordAlgebra.spinGroupContinuousMulEquivQuaternionUnitaryProd`: topological-group upgrade of
  `spinGroupEquivQuaternionUnitaryProd`.
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

/-- Over a complete nontrivially normed field, `spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour` is
continuous into a topological `K`-algebra. -/
@[fun_prop]
theorem continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    Continuous (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  let _ : IsTopologicalAddGroup (even Q) := (even Q).toSubmodule.isTopologicalAddGroup
  apply continuous_induced_rng.mpr
  refine (e.toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_spinGroupToEven Q)).congr fun s ↦ ?_
  rw [Function.comp_apply, Function.comp_apply,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply,
    evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, AlgEquiv.toLinearMap_apply]

variable [T2Space A]

/-- **Topological-group low-rank Spin unitary equivalence**: over a complete nontrivially normed
field of characteristic not two, a reversal-preserving algebra equivalence `e : even Q ≃ₐ[K] A` into
a Hausdorff topological `K`-algebra upgrades `spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour` to a
topological group isomorphism `spinGroup Q ≃ₜ* unitary A` without requiring compactness. -/
noncomputable def spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    spinGroup Q ≃ₜ* unitary A where
  toMulEquiv := spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he
  continuous_toFun :=
    continuous_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he
  continuous_invFun := by
    let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
    let _ : IsTopologicalAddGroup (even Q) := (even Q).toSubmodule.isTopologicalAddGroup
    let eL : even Q ≃L[K] A := e.toLinearEquiv.toContinuousLinearEquiv
    apply continuous_induced_rng.mpr
    refine (continuous_subtype_val.comp (eL.symm.continuous.comp continuous_subtype_val)).congr
      fun q ↦ ?_
    simp [eL]

/-- `spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour` evaluates as
`spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour`. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he s =
      spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he s :=
  (rfl)

/-- The inverse of `spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour` evaluates as
`(spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour ...).symm`. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (q : unitary A) :
    (spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q =
      (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q :=
  (rfl)

end Unitary

section QuaternionProduct

/-- **Topological-group quaternary quaternion-product Spin equivalence**: upgrades
`CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd` to a topological group isomorphism
`spinGroup Q ≃ₜ* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]`. -/
noncomputable def spinGroupContinuousMulEquivQuaternionUnitaryProd
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    {a b : K} [TopologicalSpace ℍ[K,a,0,b]] [IsTopologicalAddGroup ℍ[K,a,0,b]]
    [ContinuousSMul K ℍ[K,a,0,b]] [T2Space ℍ[K,a,0,b]]
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    spinGroup Q ≃ₜ* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b] :=
  (spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ (by omega) (by omega) e
    he).trans (Unitary.prodContinuousMulEquiv ℍ[K,a,0,b] ℍ[K,a,0,b])

/-- `spinGroupContinuousMulEquivQuaternionUnitaryProd` evaluates as
`spinGroupEquivQuaternionUnitaryProd`. -/
@[simp]
theorem spinGroupContinuousMulEquivQuaternionUnitaryProd_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    {a b : K} [TopologicalSpace ℍ[K,a,0,b]] [IsTopologicalAddGroup ℍ[K,a,0,b]]
    [ContinuousSMul K ℍ[K,a,0,b]] [T2Space ℍ[K,a,0,b]]
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s =
      spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s := by
  have h1 :
      (((spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s).1 : ℍ[K,a,0,b]),
        ((spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he s).2 : ℍ[K,a,0,b])) =
        e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
    rw [spinGroupContinuousMulEquivQuaternionUnitaryProd, ContinuousMulEquiv.trans_apply,
      Unitary.prodContinuousMulEquiv_apply,
      spinGroupContinuousMulEquivUnitaryOfAlgEquivOfFinrankLeFour_apply,
      Unitary.coe_prodEquiv_apply, coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply]
  have h2 := coe_spinGroupEquivQuaternionUnitaryProd_apply Q hQ hV e he s
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst (h1.trans h2.symm)
  · exact congrArg Prod.snd (h1.trans h2.symm)

/-- The inverse of `spinGroupContinuousMulEquivQuaternionUnitaryProd` evaluates as
`(spinGroupEquivQuaternionUnitaryProd ...).symm`. -/
@[simp]
theorem spinGroupContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    {a b : K} [TopologicalSpace ℍ[K,a,0,b]] [IsTopologicalAddGroup ℍ[K,a,0,b]]
    [ContinuousSMul K ℍ[K,a,0,b]] [T2Space ℍ[K,a,0,b]]
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x))
    (q : unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]) :
    (spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he).symm q =
      (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he).symm q := by
  apply (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he).injective
  rw [MulEquiv.apply_symm_apply, ← spinGroupContinuousMulEquivQuaternionUnitaryProd_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- Over a complete nontrivially normed field, `spinGroupEquivQuaternionUnitaryProd` is
continuous. -/
@[fun_prop]
theorem continuous_spinGroupEquivQuaternionUnitaryProd
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    {a b : K} [TopologicalSpace ℍ[K,a,0,b]] [IsTopologicalAddGroup ℍ[K,a,0,b]]
    [ContinuousSMul K ℍ[K,a,0,b]] [T2Space ℍ[K,a,0,b]]
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    Continuous (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he) :=
  (map_continuous (spinGroupContinuousMulEquivQuaternionUnitaryProd Q hQ hV e he)).congr
    (spinGroupContinuousMulEquivQuaternionUnitaryProd_apply Q hQ hV e he)

end QuaternionProduct

end CliffordAlgebra

end
