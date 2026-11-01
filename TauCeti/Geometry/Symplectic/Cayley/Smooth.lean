/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Smooth compatible Cayley interpolation

The algebraic Cayley chart identifies tame complex structures with a convex ball of antilinear
endomorphisms, and compatible structures with its self-adjoint part. Here the inverse charts
are shown to preserve smooth parameter families, using the operator-norm topology on continuous
linear maps. This is needed when
extending prescribed almost complex structures across collars: convex interpolation must be
smooth as well as pointwise compatible.

`SymplecticForm.Compatible.cayleyPath` joins a compatible structure to any other compatible
structure, is constant for parameters at most zero and at least one, and is smooth on the
whole real line. Thus its endpoint jets of every positive order vanish. Smoothness is also
proved jointly with external parameters for families expressed in Cayley coordinates. These
are linear, fixed-form statements; no extension theorem for sections of a tangent bundle is
asserted here.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart on compatible complex structures).
-/

public noncomputable section

open Set Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ J₁ : AlmostComplexStructure V}

/-- The inverse-chart denominator is invertible also in the continuous-endomorphism ring. -/
lemma isUnit_one_sub_of_toLinearMap_mem_cayleyBall {C : V →L[ℝ] V}
    (hC : C.toLinearMap ∈ ω.cayleyBall J₀) : IsUnit (1 - C) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  exact isUnit_one_sub_of_mem_cayleyBall hC

/-- In operator-norm coordinates, the inverse tame Cayley chart is the same rational
formula as its algebraic version. -/
theorem Compatible.cayleyEquiv_symm_apply_toContinuousLinearMap
    (h₀ : ω.Compatible J₀) (C : V →L[ℝ] V)
    (hC : C.toLinearMap ∈ ω.cayleyBall J₀) :
    LinearMap.toContinuousLinearMap
        (h₀.cayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, Compatible.cayleyEquiv_symm_apply_toLinearMap]
  have hinv := (isUnit_one_sub_of_toLinearMap_mem_cayleyBall hC).map_ringInverse
    (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ))
  simpa only [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_one, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.toLinearMapRingHom_apply, map_sub, map_one] using
    congrArg (fun A => J₀.toLinearMap * (1 + C.toLinearMap) * A) hinv.symm

/-- In operator-norm coordinates, the inverse compatible Cayley chart is the same rational
formula as its algebraic version. -/
theorem Compatible.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap
    (h₀ : ω.Compatible J₀) (C : V →L[ℝ] V)
    (hC : C.toLinearMap ∈ ω.compatibleCayleyBall J₀) :
    LinearMap.toContinuousLinearMap
        (h₀.compatibleCayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  simpa only [Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap,
    Compatible.cayleyEquiv_symm_apply_toLinearMap] using
    h₀.cayleyEquiv_symm_apply_toContinuousLinearMap C (compatibleCayleyBall_subset_cayleyBall hC)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A smooth family in the tame Cayley ball gives a smooth family of tame structures.
Smoothness is in the continuous-endomorphism carrier, including all external parameters. -/
theorem Compatible.contDiffAt_cayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.cayleyBall J₀)
    {n : WithTop ℕ∞} {p : P} (hCs : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (fun q => LinearMap.toContinuousLinearMap
      (h₀.cayleyEquiv.symm ⟨(C q).toLinearMap, hC q⟩).val.toLinearMap) p := by
  simp_rw [h₀.cayleyEquiv_symm_apply_toContinuousLinearMap]
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_toLinearMap_mem_cayleyBall (hC p)
  have hi : ContDiffAt ℝ n (fun q => Ring.inverse (1 - C q)) p := by
    have hi := contDiffAt_ringInverse (n := n) ℝ u
    rw [hu] at hi
    exact hi.comp p (contDiffAt_const.sub hCs)
  exact (contDiffAt_const.mul (contDiffAt_const.add hCs)).mul hi

/-- The inverse tame Cayley chart preserves globally smooth parameter families. -/
theorem Compatible.contDiff_cayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.cayleyBall J₀)
    {n : WithTop ℕ∞} (hCs : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => LinearMap.toContinuousLinearMap
      (h₀.cayleyEquiv.symm ⟨(C p).toLinearMap, hC p⟩).val.toLinearMap) :=
  contDiff_iff_contDiffAt.2 fun _ => h₀.contDiffAt_cayleyEquiv_symm hC hCs.contDiffAt

/-- A smooth family in the compatible Cayley ball gives a smooth family of compatible
structures. Smoothness is in the continuous-endomorphism carrier, so it includes all external
parameters of the family. -/
theorem Compatible.contDiffAt_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} {p : P} (hCs : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (fun q => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C q).toLinearMap, hC q⟩).val.toLinearMap) p := by
  simpa only [Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap,
    Compatible.cayleyEquiv_symm_apply_toLinearMap] using
    h₀.contDiffAt_cayleyEquiv_symm (fun q => compatibleCayleyBall_subset_cayleyBall (hC q)) hCs

/-- The inverse compatible Cayley chart preserves globally smooth parameter families. -/
theorem Compatible.contDiff_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} (hCs : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C p).toLinearMap, hC p⟩).val.toLinearMap) :=
  contDiff_iff_contDiffAt.2 fun _ => h₀.contDiffAt_compatibleCayleyEquiv_symm hC hCs.contDiffAt

/-- A smooth, collar-constant path from `J₀` to `J₁` through compatible structures, obtained by
multiplying the Cayley coordinate of `J₁` by `smoothTransition t`. -/
def Compatible.cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    AlmostComplexStructure V :=
  (h₀.compatibleCayleyEquiv.symm
    ⟨smoothTransition t • J₀.cayley J₁,
      h₀.smul_cayley_mem_compatibleCayleyBall h₁
        ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩⟩).val

/-- The path is the inverse compatible Cayley chart at the cutoff-scaled endpoint coordinate. -/
theorem Compatible.cayleyPath_eq_compatibleCayleyEquiv_symm
    (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    h₀.cayleyPath h₁ t =
      (h₀.compatibleCayleyEquiv.symm
        ⟨smoothTransition t • J₀.cayley J₁,
          h₀.smul_cayley_mem_compatibleCayleyBall h₁
            ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩⟩).val := by
  rfl

/-- The interpolated structure is compatible at every parameter, not only at its endpoints. -/
theorem Compatible.compatible_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    ω.Compatible (h₀.cayleyPath h₁ t) :=
  (h₀.compatibleCayleyEquiv.symm _).property

/-- The Cayley coordinate of the path is the cutoff-scaled coordinate of its endpoint. -/
@[simp]
theorem Compatible.cayley_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    J₀.cayley (h₀.cayleyPath h₁ t) = smoothTransition t • J₀.cayley J₁ := by
  rw [h₀.cayleyPath_eq_compatibleCayleyEquiv_symm h₁ t]
  simpa only [Compatible.compatibleCayleyEquiv_apply_coe] using
    congrArg Subtype.val (h₀.compatibleCayleyEquiv.apply_symm_apply _)

/-- Interpolating a structure with itself leaves it fixed at every parameter. -/
@[simp]
theorem Compatible.cayleyPath_self (h₀ : ω.Compatible J₀) (t : ℝ) :
    h₀.cayleyPath h₀ t = J₀ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₀ t).tames h₀.tames (by simp)

/-- The path agrees with its initial structure on the entire incoming collar. -/
@[simp]
theorem Compatible.cayleyPath_of_nonpos (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h₁ t = J₀ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₁ t).tames h₀.tames
    (by simp [smoothTransition.zero_of_nonpos ht])

/-- The path agrees with its final structure on the entire outgoing collar. -/
@[simp]
theorem Compatible.cayleyPath_of_one_le (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h₁ t = J₁ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₁ t).tames h₁.tames
    (by simp [smoothTransition.one_of_one_le ht])

/-- The path is smooth on the whole real line, including both transition endpoints. -/
theorem Compatible.contDiff_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    (n : ℕ∞) :
    ContDiff ℝ n (fun t => LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap) := by
  let C : ℝ → V →L[ℝ] V := fun t =>
    smoothTransition t • LinearMap.toContinuousLinearMap (J₀.cayley J₁)
  have hC (t : ℝ) : (C t).toLinearMap ∈ ω.compatibleCayleyBall J₀ := by
    simpa only [C, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.coe_toContinuousLinearMap] using
      h₀.smul_cayley_mem_compatibleCayleyBall h₁
        ⟨smoothTransition.nonneg t, smoothTransition.le_one t⟩
  convert h₀.contDiff_compatibleCayleyEquiv_symm (n := n) hC
    (smoothTransition.contDiff.smul contDiff_const) using 1
  funext t
  rw [h₀.cayleyPath_eq_compatibleCayleyEquiv_symm h₁ t]
  simp only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]

end TauCeti.SymplecticForm
