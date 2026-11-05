/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.InnerProductSpace.HilbertSum
public import TauCeti.Analysis.Normed.Lp.Basic
public import TauCeti.Analysis.Normed.Lp.Map

/-!
# Hilbert direct sums of covariant representations

Covariant representations of a fixed C⋆-action can be summed over an arbitrary index type.
The Hilbert space is `lp H 2`, and both representations act coordinatewise. The coefficient
operators are uniformly bounded by the coefficient norm, and the group operators by one.
Strong continuity follows from uniform approximation by finite coordinate sums.

The vector-integrated form acts coordinatewise as well: evaluation in a summand commutes
with the integral. In particular, integration commutes with infinite Hilbert direct sums,
not just algebraic sums of finite-support vectors.

The conventions and direct-sum construction follow Dana Williams, *Crossed Products of
C*-Algebras*, Chapter 2. We use Mathlib's `lp.mapCLM` and the existing vector-integrated form
`CovariantRepresentation.integratedOperator`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace CompactlySupported

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A ι : Type*} {H : ι → Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
  {α : CStarAction G A} (P : ∀ i, CovariantRepresentation α (H i))

/-- The Hilbert direct sum of a family of covariant representations. The coefficient and group
representations act coordinatewise on `lp H 2`. -/
def hilbertSum : CovariantRepresentation α (lp H 2) where
  coefficient :=
    { toFun a := lp.mapCLM 2 (fun i => (P i).coefficient a) (norm_nonneg a)
        (fun i => NonUnitalStarAlgHom.norm_apply_le _ a)
      map_zero' := by ext x i; simp
      map_add' a b := by ext x i; simp
      map_smul' c a := by ext x i; simp
      map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
      map_star' a := by
        rw [ContinuousLinearMap.star_eq_adjoint, lp.adjoint_mapCLM _ _ _ (norm_nonneg a)
          (fun i => by simpa using NonUnitalStarAlgHom.norm_apply_le (P i).coefficient a)]
        ext x i
        simp [← ContinuousLinearMap.star_eq_adjoint, map_star] }
  group := .ofMonoidHom
    { toFun g := lp.mapCLM 2 (fun i => (P i).group g) zero_le_one
        (fun i => (P i).isUnitary.norm_le_one g)
      map_one' := by ext x i; simp
      map_mul' g h := by ext x i; simp [mul_apply_eq_comp] }
  isUnitary := (ContRepresentation.isUnitary_iff_norm_map _).mpr fun g x => by
    apply le_antisymm
    · apply lp.norm_mono (by norm_num)
      intro i
      exact ((P i).isUnitary.norm_map g (x i)).le
    · apply lp.norm_mono (by norm_num)
      intro i
      exact ((P i).isUnitary.norm_map g (x i)).ge
  continuous_orbit := lp.continuous_mapCLM_apply (by simp)
    (fun g i => (P i).group g) zero_le_one
    (fun g i => (P i).isUnitary.norm_le_one g) (fun i => (P i).continuous_orbit)
  covariance g a x := by
    ext i
    exact (P i).covariance g a (x i)

/-- Coefficients in the Hilbert direct sum act coordinatewise. -/
@[simp]
theorem hilbertSum_coefficient_apply (a : A) (x : lp H 2) (i : ι) :
    (hilbertSum P).coefficient a x i = (P i).coefficient a (x i) :=
  (rfl)

/-- Group operators in the Hilbert direct sum act coordinatewise. -/
@[simp]
theorem hilbertSum_group_apply (g : G) (x : lp H 2) (i : ι) :
    (hilbertSum P).group g x i = (P i).group g (x i) :=
  (rfl)

section Integrated

variable [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- Integration commutes with evaluation in every summand of a Hilbert direct sum. -/
@[simp]
theorem integratedOperator_hilbertSum_apply (f : C_c(G, A)) (x : lp H 2) (i : ι) :
    (hilbertSum P).integratedOperator μ f x i = (P i).integratedOperator μ f (x i) := by
  let ev := lp.evalCLM ℂ H 2 i
  calc
    _ = ev ((hilbertSum P).integratedOperator μ f x) :=
      (lp.evalCLM_apply i _).symm
    _ = ev (∫ g, (hilbertSum P).coefficient (f g) ((hilbertSum P).group g x) ∂μ) :=
      congrArg ev ((hilbertSum P).integratedOperator_apply μ f x)
    _ = ∫ g, ev ((hilbertSum P).coefficient (f g) ((hilbertSum P).group g x)) ∂μ :=
      (ev.integral_comp_comm ((hilbertSum P).integrable_integrand μ f x)).symm
    _ = ∫ g, (P i).coefficient (f g) ((P i).group g (x i)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp [ev]
    _ = _ := ((P i).integratedOperator_apply μ f (x i)).symm

/-- The integrated operator of a Hilbert direct sum is the Hilbert direct sum of the integrated
operators, uniformly bounded by the common L¹ estimate. -/
theorem integratedOperator_hilbertSum (f : C_c(G, A)) :
    (hilbertSum P).integratedOperator μ f =
      lp.mapCLM 2 (fun i => (P i).integratedOperator μ f)
        (integral_nonneg fun _ => norm_nonneg _)
        (fun i => (P i).norm_integratedOperator_le μ f) := by
  ext x i
  simp

end Integrated

end TauCeti.CStarAction.CovariantRepresentation
