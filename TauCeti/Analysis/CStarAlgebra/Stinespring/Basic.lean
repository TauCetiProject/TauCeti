/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Stinespring's dilation theorem

Every completely positive map `φ : A →CP (H →L[ℂ] H)` from a (possibly nonunital) C⋆-algebra `A`
into `H →L[ℂ] H` dilates to a nondegenerate `⋆`-representation `π` on a Hilbert space `K`
compressed by `V : H →L[ℂ] K`: `φ a = V† ∘L π a ∘L V`, with `‖V‖ ^ 2 = ‖φ‖` and minimal spanning
subspace `closure (span {π a (V ξ)}) = ⊤`.

Here `φ.PreStinespring` is `A ⊗[ℂ] H` with semi-inner product
`⟪a ⊗ ξ, b ⊗ η⟫ = ⟪ξ, φ (star a * b) η⟫_ℂ`, completed to `φ.Stinespring`; `φ.stinespringOp` is the
strong limit of `e ↦ [e ⊗ ·]` along `CStarAlgebra.approximateUnit A`. As a corollary, `φ` satisfies
the Kadison–Schwarz inequality `star (φ a) * φ a ≤ ‖φ‖ • φ (star a * a)`.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955), Thm. 1.
* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*, II.6.9.7.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 4.1.
-/

public section

universe u v

open Filter Topology TensorProduct
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace CompletelyPositiveMap

section PreStinespring

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : A →CP (H →L[ℂ] H))

private noncomputable def rightLift (a : A) (ξ : H) : (A ⊗[ℂ] H) →ₗ[ℂ] ℂ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun b η => ⟪ξ, φ (star a * b) η⟫_ℂ)
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_smul_comm])
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

private theorem rightLift_add_left (a₁ a₂ : A) (ξ : H) :
    rightLift φ (a₁ + a₂) ξ = rightLift φ a₁ ξ + rightLift φ a₂ ξ :=
  TensorProduct.ext' fun _ _ => by simp [rightLift, add_mul]

private theorem rightLift_smul_left (c : ℂ) (a : A) (ξ : H) :
    rightLift φ (c • a) ξ = star c • rightLift φ a ξ :=
  TensorProduct.ext' fun _ _ => by simp [rightLift, smul_mul_assoc]

private theorem rightLift_add_right (a : A) (ξ₁ ξ₂ : H) :
    rightLift φ a (ξ₁ + ξ₂) = rightLift φ a ξ₁ + rightLift φ a ξ₂ :=
  TensorProduct.ext' fun _ _ => by simp [rightLift]

private theorem rightLift_smul_right (c : ℂ) (a : A) (ξ : H) :
    rightLift φ a (c • ξ) = star c • rightLift φ a ξ :=
  TensorProduct.ext' fun _ _ => by simp [rightLift, mul_comm]

private noncomputable def leftLift (y : A ⊗[ℂ] H) : (A ⊗[ℂ] H) →ₗ[ℂ] ℂ :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun a ξ => star (rightLift φ a ξ y))
    (fun a₁ a₂ ξ => by simp [rightLift_add_left]) (fun c a ξ => by simp [rightLift_smul_left])
    (fun a ξ₁ ξ₂ => by simp [rightLift_add_right]) (fun c a ξ => by simp [rightLift_smul_right])

private theorem leftLift_tmul_tmul (a b : A) (ξ η : H) :
    leftLift φ (b ⊗ₜ[ℂ] η) (a ⊗ₜ[ℂ] ξ) = star ⟪ξ, φ (star a * b) η⟫_ℂ := (rfl)

private theorem leftLift_add (y₁ y₂ : A ⊗[ℂ] H) :
    leftLift φ (y₁ + y₂) = leftLift φ y₁ + leftLift φ y₂ :=
  TensorProduct.ext' fun _ _ => by simp [leftLift]

private theorem leftLift_symm (x y : A ⊗[ℂ] H) : leftLift φ x y = star (leftLift φ y x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b η =>
    induction y using TensorProduct.inductionOn with
    | tmul a ξ =>
      have hstar : φ (star b * a) = (φ (star a * b)).adjoint := by
        simpa only [coe_toPositiveLinearMap, star_mul, star_star,
          ContinuousLinearMap.star_eq_adjoint] using map_star φ.toPositiveLinearMap (star a * b)
      rw [leftLift_tmul_tmul, leftLift_tmul_tmul, star_star, Complex.star_def, inner_conj_symm,
        hstar, ContinuousLinearMap.adjoint_inner_right]
    | add y₁ y₂ hy₁ hy₂ => simp [leftLift_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp [leftLift_add, hx₁, hx₂]

/-- The algebraic tensor product `A ⊗[ℂ] H` equipped with the Stinespring semi-inner product. -/
def PreStinespring (_φ : A →CP (H →L[ℂ] H)) : Type (max u v) := A ⊗[ℂ] H

instance : AddCommGroup φ.PreStinespring := inferInstanceAs (AddCommGroup (A ⊗[ℂ] H))

instance : Module ℂ φ.PreStinespring := inferInstanceAs (Module ℂ (A ⊗[ℂ] H))

/-- The linear equivalence from `A ⊗[ℂ] H` to `φ.PreStinespring`. -/
def toPreStinespring : (A ⊗[ℂ] H) ≃ₗ[ℂ] φ.PreStinespring := LinearEquiv.refl ℂ _

/-- The linear equivalence from `φ.PreStinespring` back to `A ⊗[ℂ] H`. -/
def ofPreStinespring : φ.PreStinespring ≃ₗ[ℂ] (A ⊗[ℂ] H) := φ.toPreStinespring.symm

@[simp] theorem toPreStinespring_ofPreStinespring (x : φ.PreStinespring) :
    φ.toPreStinespring (φ.ofPreStinespring x) = x := (rfl)

@[simp] theorem ofPreStinespring_toPreStinespring (t : A ⊗[ℂ] H) :
    φ.ofPreStinespring (φ.toPreStinespring t) = t := (rfl)

/-- The semi-inner product structure on `φ.PreStinespring` sending `(a ⊗ ξ, b ⊗ η)` to
`⟪ξ, φ (star a * b) η⟫_ℂ`. -/
@[instance_reducible]
noncomputable def preStinespringCore : PreInnerProductSpace.Core ℂ φ.PreStinespring where
  inner x y := star (leftLift φ (φ.ofPreStinespring y) (φ.ofPreStinespring x))
  conj_inner_symm x y := by
    simpa only [← Complex.star_def, star_star] using
      leftLift_symm φ (φ.ofPreStinespring x) (φ.ofPreStinespring y)
  re_inner_nonneg x := by
    obtain ⟨n, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq (φ.ofPreStinespring x)
    have hinner : star (leftLift φ (φ.ofPreStinespring x) (φ.ofPreStinespring x)) =
        ∑ i, ∑ j, ⟪ξ i, φ (star (a i) * a j) (ξ j)⟫_ℂ := by
      rw [hx, map_sum]
      simp_rw [leftLift, TensorProduct.lift.tmul, LinearMap.mk₂_apply, rightLift, map_sum,
        TensorProduct.lift.tmul, LinearMap.mk₂_apply, star_sum, star_star]
    let M : CStarMatrix (Fin n) (Fin n) A :=
      CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)
    have hM : 0 ≤ M := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun y => by
      convert star_mul_self_nonneg (∑ i, a i * y i) using 1
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; simp [M, mul_assoc]
    rw [hinner]
    exact (RCLike.nonneg_iff.mp
      ((CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mp (φ.map_cstarMatrix_nonneg M hM)) ξ)).1
  add_left _ _ _ := by simp
  smul_left _ _ _ := by simp

noncomputable instance : SeminormedAddCommGroup φ.PreStinespring :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preStinespringCore)

noncomputable instance : InnerProductSpace ℂ φ.PreStinespring :=
  InnerProductSpace.ofCore φ.preStinespringCore

@[simp] theorem inner_toPreStinespring_tmul (a b : A) (ξ η : H) :
    ⟪φ.toPreStinespring (a ⊗ₜ[ℂ] ξ), φ.toPreStinespring (b ⊗ₜ[ℂ] η)⟫_ℂ =
      ⟪ξ, φ (star a * b) η⟫_ℂ :=
  star_star _

theorem inner_toPreStinespring_sum {n : Type*} [Fintype n] {m : Type*} [Fintype m]
    (a : n → A) (ξ : n → H) (b : m → A) (η : m → H) :
    ⟪φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i), φ.toPreStinespring (∑ j, b j ⊗ₜ[ℂ] η j)⟫_ℂ =
      ∑ i, ∑ j, ⟪ξ i, φ (star (a i) * b j) (η j)⟫_ℂ := by
  simp_rw [map_sum, sum_inner, inner_sum, inner_toPreStinespring_tmul]

theorem norm_toPreStinespring_sum_sq {n : Type*} [Fintype n] (a : n → A) (ξ : n → H) :
    (‖φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 : ℂ) =
      ∑ i, ∑ j, ⟪ξ i, φ (star (a i) * a j) (ξ j)⟫_ℂ := by
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _).symm.trans (φ.inner_toPreStinespring_sum a ξ a ξ)

theorem norm_toPreStinespring_tmul_sq (a : A) (ξ : H) :
    (‖φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)‖ ^ 2 : ℂ) = ⟪ξ, φ (star a * a) ξ⟫_ℂ := by
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _).symm.trans (φ.inner_toPreStinespring_tmul a a ξ ξ)

theorem norm_toPreStinespring_tmul_le (a : A) (ξ : H) :
    ‖φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖ * ‖ξ‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  have hre : ‖φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)‖ ^ 2 = (⟪ξ, φ (star a * a) ξ⟫_ℂ).re := by
    simpa [← Complex.ofReal_pow] using congrArg Complex.re (φ.norm_toPreStinespring_tmul_sq a ξ)
  rw [hre, mul_pow, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  calc (⟪ξ, φ (star a * a) ξ⟫_ℂ).re
      ≤ ‖ξ‖ * ‖φ (star a * a) ξ‖ := (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ ‖ξ‖ * (‖φ (star a * a)‖ * ‖ξ‖) := by gcongr; exact (φ (star a * a)).le_opNorm ξ
    _ ≤ ‖ξ‖ * ((‖φ.toContinuousLinearMap‖ * ‖star a * a‖) * ‖ξ‖) := by
        gcongr; simpa only [toContinuousLinearMap_apply] using
          φ.toContinuousLinearMap.le_opNorm (star a * a)
    _ = ‖φ.toContinuousLinearMap‖ * ‖a‖ ^ 2 * ‖ξ‖ ^ 2 := by
        rw [CStarRing.norm_star_mul_self, ← sq]; ring

end PreStinespring

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : A →CP (H →L[ℂ] H))

/-- The canonical minimal Stinespring Hilbert space of `φ`: the separated completion of
`φ.PreStinespring`. -/
abbrev Stinespring : Type (max u v) := UniformSpace.Completion φ.PreStinespring

/-- The linear map from `A ⊗[ℂ] H` into `φ.Stinespring`. -/
noncomputable def toStinespringLinearMap : (A ⊗[ℂ] H) →ₗ[ℂ] φ.Stinespring :=
  UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp φ.toPreStinespring.toLinearMap

@[simp] theorem toStinespringLinearMap_apply (t : A ⊗[ℂ] H) :
    φ.toStinespringLinearMap t = (φ.toPreStinespring t : φ.Stinespring) := (rfl)

theorem denseRange_toStinespringLinearMap : DenseRange φ.toStinespringLinearMap :=
  UniformSpace.Completion.denseRange_coe.comp φ.toPreStinespring.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- The bounded linear class map `ξ ↦ [a ⊗ ξ]` into `φ.Stinespring` for fixed `a : A`. -/
noncomputable def toStinespring (a : A) : H →L[ℂ] φ.Stinespring :=
  (φ.toStinespringLinearMap.comp (TensorProduct.mk ℂ A H a)).mkContinuous
    (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖) fun ξ => by
      simpa using φ.norm_toPreStinespring_tmul_le a ξ

@[simp] theorem toStinespring_apply (a : A) (ξ : H) :
    φ.toStinespring a ξ = (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ) : φ.Stinespring) := (rfl)

theorem inner_toStinespring (a b : A) (ξ η : H) :
    ⟪φ.toStinespring a ξ, φ.toStinespring b η⟫_ℂ = ⟪ξ, φ (star a * b) η⟫_ℂ := by
  simp [toStinespring_apply]

theorem norm_toStinespring_le (a : A) :
    ‖φ.toStinespring a‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖ :=
  (φ.toStinespring a).opNorm_le_bound (by positivity) fun ξ => by
    simpa using φ.norm_toPreStinespring_tmul_le a ξ

theorem continuous_toStinespring_left (ξ : H) : Continuous fun a : A => φ.toStinespring a ξ := by
  let L : A →ₗ[ℂ] φ.Stinespring :=
    { toFun a := φ.toStinespring a ξ
      map_add' a b := by simp [toStinespring_apply, add_tmul, UniformSpace.Completion.coe_add]
      map_smul' c a := by
        rw [toStinespring_apply, toStinespring_apply, ← smul_tmul', map_smul,
          UniformSpace.Completion.coe_smul, RingHom.id_apply] }
  exact (L.mkContinuous (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖ξ‖) fun a => by
    simpa [L, mul_right_comm] using φ.norm_toPreStinespring_tmul_le a ξ).continuous

private theorem norm_leftMulPreStinespring_sum_le {n : ℕ} (c : A) (a : Fin n → A)
    (ξ : Fin n → H) :
    ‖φ.toPreStinespring (∑ i, (c * a i) ⊗ₜ[ℂ] ξ i)‖ ≤
      ‖c‖ * ‖φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow]
  let M₁ : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => star (c * a i) * (c * a j))
  let M₂ : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => (‖c‖ ^ 2 : ℝ) • (star (a i) * a j))
  have hle : 0 ≤ M₂ - M₁ := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun y => by
    let z : A := ∑ j, a j * y j
    have hdiff : (∑ i, ∑ j, star (y i) * (M₂ - M₁) i j * y j) =
        (‖c‖ ^ 2 : ℝ) • (star z * z) - star z * (star c * c) * z := by
      simp only [z, star_sum, Finset.sum_mul, Finset.smul_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [M₁, M₂, Finset.mul_sum, Finset.smul_sum, Finset.sum_sub_distrib, mul_sub, sub_mul,
        mul_assoc, mul_smul_comm, smul_mul_assoc]
    rw [hdiff, sub_nonneg, sq, ← CStarRing.norm_star_mul_self (x := c)]
    exact CStarAlgebra.star_left_conjugate_le_norm_smul z (star c * c)
  have hre : 0 ≤ (∑ i, ∑ j, ⟪ξ i, (M₂ - M₁).map φ i j (ξ j)⟫_ℂ).re :=
    (RCLike.nonneg_iff.mp
      ((CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mp
        (φ.map_cstarMatrix_nonneg (M₂ - M₁) hle)) ξ)).1
  have h₁ : ‖φ.toPreStinespring (∑ i, (c * a i) ⊗ₜ[ℂ] ξ i)‖ ^ 2 =
      (∑ i, ∑ j, ⟪ξ i, φ (M₁ i j) (ξ j)⟫_ℂ).re := by
    simpa [M₁, ← Complex.ofReal_pow] using
      congrArg Complex.re (φ.norm_toPreStinespring_sum_sq (fun i => c * a i) ξ)
  have h₂ : ‖c‖ ^ 2 * ‖φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 =
      (∑ i, ∑ j, ⟪ξ i, φ (M₂ i j) (ξ j)⟫_ℂ).re := by
    have hx : ‖φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 =
        (∑ i, ∑ j, ⟪ξ i, φ (star (a i) * a j) (ξ j)⟫_ℂ).re := by
      simpa [← Complex.ofReal_pow] using congrArg Complex.re (φ.norm_toPreStinespring_sum_sq a ξ)
    rw [hx]
    simp [M₂, ← Complex.coe_smul, -Complex.ofReal_pow, Finset.mul_sum]
  have hsub : (∑ i, ∑ j, ⟪ξ i, (M₂ - M₁).map φ i j (ξ j)⟫_ℂ).re =
      (∑ i, ∑ j, ⟪ξ i, φ (M₂ i j) (ξ j)⟫_ℂ).re - (∑ i, ∑ j, ⟪ξ i, φ (M₁ i j) (ξ j)⟫_ℂ).re := by
    simp [Finset.sum_sub_distrib]
  linarith

/-- Left multiplication by `c : A` on `φ.PreStinespring`, bounded in operator norm by `‖c‖`. -/
noncomputable def leftMulPreStinespring (c : A) : φ.PreStinespring →L[ℂ] φ.PreStinespring :=
  (φ.toPreStinespring.toLinearMap.comp
    (TensorProduct.map (LinearMap.mulLeft ℂ c) LinearMap.id |>.comp
      φ.ofPreStinespring.toLinearMap)).mkContinuous ‖c‖ fun x => by
    obtain ⟨n, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq (φ.ofPreStinespring x)
    have hx' : x = φ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i) := by
      rw [← hx, toPreStinespring_ofPreStinespring]
    simpa [hx, ← hx', map_sum] using norm_leftMulPreStinespring_sum_le φ c a ξ

@[simp] theorem leftMulPreStinespring_tmul (c a : A) (ξ : H) :
    φ.leftMulPreStinespring c (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)) =
      φ.toPreStinespring ((c * a) ⊗ₜ[ℂ] ξ) := (rfl)

@[simp] theorem leftMulPreStinespring_mul (a b : A) :
    φ.leftMulPreStinespring (a * b) = φ.leftMulPreStinespring a ∘L φ.leftMulPreStinespring b := by
  ext x
  obtain ⟨t, rfl⟩ := φ.toPreStinespring.surjective x
  induction t using TensorProduct.inductionOn with
  | tmul c ξ => simp [mul_assoc]
  | add s₁ s₂ hs₁ hs₂ => simp [map_add, hs₁, hs₂]

private theorem completion_ext {S T : φ.Stinespring →L[ℂ] φ.Stinespring}
    (h : ∀ a ξ, S (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)) = T (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ))) :
    S = T := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih x =>
    obtain ⟨t, rfl⟩ := φ.toPreStinespring.surjective x
    induction t using TensorProduct.inductionOn with
    | tmul a ξ => exact h a ξ
    | add s₁ s₂ hs₁ hs₂ => simp [map_add, UniformSpace.Completion.coe_add, hs₁, hs₂]

/-- The canonical Stinespring `⋆`-representation of `A` on `φ.Stinespring`. -/
noncomputable def stinespringHom : A →⋆ₙₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  toFun a := (φ.leftMulPreStinespring a).completion
  map_smul' m a := completion_ext φ fun b ξ => by
    rw [ContinuousLinearMap.completion_apply_coe, leftMulPreStinespring_tmul, smul_mul_assoc,
      ← smul_tmul', map_smul, UniformSpace.Completion.coe_smul, MonoidHom.id_apply, smul_apply,
      ContinuousLinearMap.completion_apply_coe, leftMulPreStinespring_tmul]
  map_zero' := completion_ext φ fun b ξ => by
    simp [ContinuousLinearMap.completion_apply_coe, zero_tmul]
  map_add' a b := completion_ext φ fun c ξ => by
    simp [ContinuousLinearMap.completion_apply_coe, add_mul, add_tmul,
      UniformSpace.Completion.coe_add]
  map_mul' a b := completion_ext φ fun c ξ => by
    simp [ContinuousLinearMap.completion_apply_coe]
  map_star' a := (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y =>
      obtain ⟨n, b, ξ, hb⟩ := TensorProduct.exists_sum_tmul_eq (φ.ofPreStinespring x)
      obtain ⟨m, c, η, hc⟩ := TensorProduct.exists_sum_tmul_eq (φ.ofPreStinespring y)
      rw [← φ.toPreStinespring_ofPreStinespring x, ← φ.toPreStinespring_ofPreStinespring y, hb, hc]
      simp [ContinuousLinearMap.completion_apply_coe, map_sum, sum_inner, inner_sum, mul_assoc]

theorem stinespringHom_apply (a : A) :
    φ.stinespringHom a = (φ.leftMulPreStinespring a).completion := (rfl)

theorem stinespringHom_toStinespring (a b : A) (ξ : H) :
    φ.stinespringHom a (φ.toStinespring b ξ) = φ.toStinespring (a * b) ξ := by
  rw [stinespringHom_apply, toStinespring_apply, toStinespring_apply,
    ContinuousLinearMap.completion_apply_coe, leftMulPreStinespring_tmul]

private noncomputable def diagFunctional (ξ : H) : A →P[ℂ] ℂ where
  toLinearMap := { toFun a := ⟪ξ, φ a ξ⟫_ℂ, map_add' _ _ := by simp, map_smul' _ _ := by simp }
  cont := by
    have hc : Continuous fun a : A => φ.toContinuousLinearMap a ξ := by fun_prop
    simpa only [toContinuousLinearMap_apply] using continuous_const.inner hc
  monotone' a b hab := by
    have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp (map_nonneg φ (sub_nonneg.mpr hab))
    exact sub_nonneg.mp (by simpa [inner_sub_right] using hpos.inner_nonneg_right ξ)

@[simp] private theorem diagFunctional_apply (ξ : H) (a : A) :
    diagFunctional φ ξ a = ⟪ξ, φ a ξ⟫_ℂ := (rfl)

private theorem norm_toStinespring_sub_sq_le (ξ : H) {e₀ e : A}
    (he₀ : 0 ≤ e₀) (hle : e₀ ≤ e) (he : ‖e‖ ≤ 1) :
    ‖φ.toStinespring e ξ - φ.toStinespring e₀ ξ‖ ^ 2 ≤ (diagFunctional φ ξ (e - e₀)).re := by
  have hd₀ : 0 ≤ e - e₀ := sub_nonneg.mpr hle
  have hd₁ : ‖e - e₀‖ ≤ 1 :=
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self e he₀) hd₀).trans he
  have hd_sq : star (e - e₀) * (e - e₀) ≤ e - e₀ := by
    rw [(IsSelfAdjoint.of_nonneg hd₀).star_eq]
    exact CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hd₀ hd₁
  have hsub : φ.toStinespring e ξ - φ.toStinespring e₀ ξ = φ.toStinespring (e - e₀) ξ := by
    simp [toStinespring_apply, sub_tmul, UniformSpace.Completion.coe_sub]
  have hre : ‖φ.toStinespring (e - e₀) ξ‖ ^ 2 =
      (diagFunctional φ ξ (star (e - e₀) * (e - e₀))).re := by
    simpa [← Complex.ofReal_pow] using
      congrArg Complex.re (φ.norm_toPreStinespring_tmul_sq (e - e₀) ξ)
  rw [hsub, hre]
  exact (RCLike.le_iff_re_im.mp ((diagFunctional φ ξ).mono hd_sq)).1

private theorem cauchy_map_toStinespring (ξ : H) :
    Cauchy (Filter.map (fun e => φ.toStinespring e ξ) (CStarAlgebra.approximateUnit A)) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩
  let c : ℂ := ‖((diagFunctional φ ξ : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖
  obtain ⟨e₀, he₀, hball⟩ := (CStarAlgebra.hasBasis_approximateUnit A).tendsto_left_iff.mp
    ((diagFunctional φ ξ).tendsto_nhds_opNorm hl)
    (Metric.ball c (ε ^ 2 / 8)) (Metric.ball_mem_nhds _ (by positivity))
  refine ⟨(fun e => φ.toStinespring e ξ) '' ({x : A | e₀ ≤ x} ∩ Metric.closedBall 0 1),
    Filter.image_mem_map ((CStarAlgebra.hasBasis_approximateUnit A).mem_of_mem he₀), ?_⟩
  have he₀_mem : e₀ ∈ {x : A | e₀ ≤ x} ∩ Metric.closedBall 0 1 := ⟨le_rfl, by simpa using he₀.2.le⟩
  have hdist₀ : ∀ e ∈ {x : A | e₀ ≤ x} ∩ Metric.closedBall 0 1,
      dist (φ.toStinespring e ξ) (φ.toStinespring e₀ ξ) < ε / 2 := by
    rintro e ⟨hle, he_ball⟩
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    have h₁ := norm_toStinespring_sub_sq_le φ ξ he₀.1 hle (by simpa using he_ball)
    have h₂ : (diagFunctional φ ξ (e - e₀)).re ≤ dist (diagFunctional φ ξ e) c +
        dist (diagFunctional φ ξ e₀) c := by
      rw [map_sub]
      refine (Complex.re_le_norm _).trans ?_
      rw [← dist_eq_norm]
      exact dist_triangle_right (diagFunctional φ ξ e) (diagFunctional φ ξ e₀) c
    have h₃ := Metric.mem_ball.mp (hball ⟨hle, he_ball⟩)
    have h₄ := Metric.mem_ball.mp (hball he₀_mem)
    rw [dist_eq_norm]
    linarith [show ε ^ 2 / 8 + ε ^ 2 / 8 = (ε / 2) ^ 2 by ring]
  rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
  linarith [dist_triangle_right (φ.toStinespring e₁ ξ) (φ.toStinespring e₂ ξ)
    (φ.toStinespring e₀ ξ), hdist₀ e₁ he₁, hdist₀ e₂ he₂]

private theorem exists_stinespringOp :
    ∃ V : H →L[ℂ] φ.Stinespring, ‖V‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ ∧
      ∀ ξ, Tendsto (fun e => φ.toStinespring e ξ) (CStarAlgebra.approximateUnit A) (𝓝 (V ξ)) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  set f : H → φ.Stinespring :=
    fun ξ => limUnder (CStarAlgebra.approximateUnit A) fun e => φ.toStinespring e ξ
  have hf (ξ : H) :
      Tendsto (fun e => φ.toStinespring e ξ) (CStarAlgebra.approximateUnit A) (𝓝 (f ξ)) :=
    tendsto_nhds_limUnder (cauchy_map_iff_exists_tendsto.mp (cauchy_map_toStinespring φ ξ))
  have hbdd : ∀ᶠ e in CStarAlgebra.approximateUnit A,
      ‖φ.toStinespring e‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ :=
    hl.eventually_norm.mono fun e he => (φ.norm_toStinespring_le e).trans
      (mul_le_of_le_one_right (Real.sqrt_nonneg _) he)
  let B := Metric.closedBall (0 : H →L[ℂ] φ.Stinespring) (Real.sqrt ‖φ.toContinuousLinearMap‖)
  have hmem : f ∈ closure (((↑) : (H →L[ℂ] φ.Stinespring) → H → φ.Stinespring) '' B) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.mpr hf) <| hbdd.mono fun e he =>
      ⟨φ.toStinespring e, (mem_closedBall_zero_iff (a := φ.toStinespring e)).mpr he, rfl⟩
  let V := ContinuousLinearMap.ofMemClosureImageCoeBounded f Metric.isBounded_closedBall hmem
  have hV : ⇑V = f := ContinuousLinearMap.ofMemClosureImageCoeBounded_apply _ _ _
  refine ⟨V, V.opNorm_le_bound (Real.sqrt_nonneg _) fun ξ => hV ▸ le_of_tendsto ((hf ξ).norm) ?_,
    fun ξ => hV ▸ hf ξ⟩
  exact hbdd.mono fun e he =>
    ((φ.toStinespring e).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right he (norm_nonneg ξ))

/-- The canonical Stinespring operator `V : H →L[ℂ] φ.Stinespring`: the strong limit of
`e ↦ [e ⊗ ·]` along `CStarAlgebra.approximateUnit A`. -/
noncomputable def stinespringOp : H →L[ℂ] φ.Stinespring := (exists_stinespringOp φ).choose

theorem norm_stinespringOp_le : ‖φ.stinespringOp‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ :=
  (exists_stinespringOp φ).choose_spec.1

theorem tendsto_toStinespring_approximateUnit (ξ : H) :
    Tendsto (fun e => φ.toStinespring e ξ) (CStarAlgebra.approximateUnit A)
      (𝓝 (φ.stinespringOp ξ)) :=
  (exists_stinespringOp φ).choose_spec.2 ξ

@[simp] theorem stinespringHom_apply_stinespringOp (a : A) (ξ : H) :
    φ.stinespringHom a (φ.stinespringOp ξ) = φ.toStinespring a ξ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h₁ : Tendsto (fun e => φ.stinespringHom a (φ.toStinespring e ξ))
      (CStarAlgebra.approximateUnit A) (𝓝 (φ.stinespringHom a (φ.stinespringOp ξ))) :=
    ((φ.stinespringHom a).continuous.tendsto _).comp (φ.tendsto_toStinespring_approximateUnit ξ)
  have h₂ : Tendsto (fun e => φ.toStinespring (a * e) ξ)
      (CStarAlgebra.approximateUnit A) (𝓝 (φ.toStinespring a ξ)) :=
    ((φ.continuous_toStinespring_left ξ).tendsto a).comp (hl.tendsto_mul_left a)
  exact tendsto_nhds_unique h₁ (by simpa only [stinespringHom_toStinespring] using h₂)

/-- The Stinespring dilation identity: `φ a = V† ∘L π a ∘L V`. -/
@[simp] theorem stinespring_eq (a : A) :
    φ.stinespringOp.adjoint.comp ((φ.stinespringHom a).comp φ.stinespringOp) = φ a := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  ext η
  refine ext_inner_left ℂ fun ξ => ?_
  have hc : Continuous fun b : A => ⟪ξ, φ b η⟫_ℂ := by
    have h : Continuous fun b : A => φ.toContinuousLinearMap b η := by fun_prop
    simpa only [toContinuousLinearMap_apply] using continuous_const.inner h
  have h₂ : Tendsto (fun e => ⟪ξ, φ (e * a) η⟫_ℂ)
      (CStarAlgebra.approximateUnit A) (𝓝 ⟪ξ, φ a η⟫_ℂ) :=
    (hc.tendsto a).comp (hl.tendsto_mul_right a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    stinespringHom_apply_stinespringOp]
  refine tendsto_nhds_unique (Filter.Tendsto.inner (φ.tendsto_toStinespring_approximateUnit ξ)
    tendsto_const_nhds) (h₂.congr' ?_)
  filter_upwards [hl.eventually_star_eq] with e he
  rw [φ.inner_toStinespring, he]

/-- The canonical Stinespring dilation is minimal: `{π a (V ξ)}` spans a dense subspace. -/
theorem topologicalClosure_span_stinespring :
    (Submodule.span ℂ
      {x : φ.Stinespring | ∃ (a : A) (ξ : H),
        x = φ.stinespringHom a (φ.stinespringOp ξ)}).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  refine φ.denseRange_toStinespringLinearMap.mono ?_
  rintro _ ⟨t, rfl⟩
  have hrange : LinearMap.range φ.toStinespringLinearMap ≤
      Submodule.span ℂ {x : φ.Stinespring | ∃ (a : A) (ξ : H),
        x = φ.stinespringHom a (φ.stinespringOp ξ)} := by
    rw [← Submodule.map_top, ← TensorProduct.span_tmul_eq_top, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨a, ξ, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a, ξ, (φ.stinespringHom_apply_stinespringOp a ξ).symm⟩
  exact hrange (LinearMap.mem_range_self _ t)

/-- The canonical Stinespring representation is nondegenerate. -/
theorem isNondegenerate_stinespringHom : φ.stinespringHom.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    eq_top_iff, ← φ.topologicalClosure_span_stinespring]
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨a, ξ, rfl⟩
  exact Set.mem_iUnion.mpr ⟨a, φ.stinespringOp ξ, rfl⟩

/-- The squared operator norm of the Stinespring operator equals the operator norm of `φ`. -/
@[simp] theorem norm_stinespringOp_sq : ‖φ.stinespringOp‖ ^ 2 = ‖φ.toContinuousLinearMap‖ := by
  refine le_antisymm ?_ (φ.toContinuousLinearMap.opNorm_le_bound (sq_nonneg _) fun a => ?_)
  · calc ‖φ.stinespringOp‖ ^ 2 ≤ (Real.sqrt ‖φ.toContinuousLinearMap‖) ^ 2 := by
          gcongr; exact φ.norm_stinespringOp_le
      _ = ‖φ.toContinuousLinearMap‖ := Real.sq_sqrt (norm_nonneg _)
  · rw [toContinuousLinearMap_apply, ← φ.stinespring_eq a]
    calc ‖φ.stinespringOp.adjoint.comp ((φ.stinespringHom a).comp φ.stinespringOp)‖
        ≤ ‖φ.stinespringOp‖ * (‖φ.stinespringHom a‖ * ‖φ.stinespringOp‖) := by
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          rw [ContinuousLinearMap.adjoint.norm_map]
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖φ.stinespringOp‖ * (‖a‖ * ‖φ.stinespringOp‖) := by
          gcongr; exact NonUnitalStarAlgHom.norm_apply_le φ.stinespringHom a
      _ = ‖φ.stinespringOp‖ ^ 2 * ‖a‖ := by ring

/-- The **Kadison–Schwarz inequality** for a completely positive map into `H →L[ℂ] H`:
`star (φ a) * φ a ≤ ‖φ‖ • φ (star a * a)`. -/
theorem star_map_mul_map_le_opNorm_smul (a : A) :
    star (φ a) * φ a ≤ ‖φ.toContinuousLinearMap‖ • φ (star a * a) := by
  let V := φ.stinespringOp
  let π := φ.stinespringHom
  refine ContinuousLinearMap.le_def.mpr
    ((ContinuousLinearMap.isPositive_iff_complex _).mpr fun ξ => ?_)
  have h₁ : ⟪(star (φ a) * φ a) ξ, ξ⟫_ℂ = (‖φ a ξ‖ : ℂ) ^ 2 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    simp
  have h₂ : ⟪φ (star a * a) ξ, ξ⟫_ℂ = (‖π a (V ξ)‖ : ℂ) ^ 2 := by
    rw [← φ.stinespring_eq (star a * a), map_mul, map_star, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (π a (V ξ))
  have hle : ‖φ a ξ‖ ^ 2 ≤ ‖φ.toContinuousLinearMap‖ * ‖π a (V ξ)‖ ^ 2 := by
    have hnorm : ‖φ a ξ‖ ≤ ‖V‖ * ‖π a (V ξ)‖ := by
      have hφa : φ a ξ = V.adjoint (π a (V ξ)) := congrFun (congrArg DFunLike.coe
        (φ.stinespring_eq a).symm) ξ
      rw [hφa, ← ContinuousLinearMap.adjoint.norm_map V]
      exact V.adjoint.le_opNorm (π a (V ξ))
    calc ‖φ a ξ‖ ^ 2 ≤ (‖V‖ * ‖π a (V ξ)‖) ^ 2 := by gcongr
      _ = ‖φ.toContinuousLinearMap‖ * ‖π a (V ξ)‖ ^ 2 := by
          rw [mul_pow, φ.norm_stinespringOp_sq]
  have hinner : ⟪(‖φ.toContinuousLinearMap‖ • φ (star a * a) - star (φ a) * φ a) ξ, ξ⟫_ℂ =
      Complex.ofReal (‖φ.toContinuousLinearMap‖ * ‖π a (V ξ)‖ ^ 2 - ‖φ a ξ‖ ^ 2) := by
    rw [sub_apply, smul_apply, ← Complex.coe_smul, inner_sub_left, inner_smul_left,
      Complex.conj_ofReal, h₁, h₂]
    push_cast; rfl
  rw [hinner]
  exact ⟨by simp [-Complex.ofReal_pow],
    by simpa [RCLike.ofReal_re, -Complex.ofReal_pow] using sub_nonneg.mpr hle⟩

/-- **Stinespring's dilation theorem (nonunital domain)**. -/
theorem stinespring_nonUnital :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      π.IsNondegenerate ∧ (∀ a, φ a = V.adjoint.comp ((π a).comp V)) ∧
      ‖V‖ ^ 2 = ‖φ.toContinuousLinearMap‖ ∧
      (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringHom, φ.stinespringOp,
    φ.isNondegenerate_stinespringHom, fun a => (φ.stinespring_eq a).symm, φ.norm_stinespringOp_sq,
    φ.topologicalClosure_span_stinespring⟩

end NonUnital

section Monotone

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Domination `ψ ≤ φ` in the completely positive order dominates the Stinespring seminorm on
`A ⊗[ℂ] H`. -/
theorem norm_toStinespringLinearMap_le_of_le {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ)
    (t : A ⊗[ℂ] H) : ‖ψ.toStinespringLinearMap t‖ ≤ ‖φ.toStinespringLinearMap t‖ := by
  obtain ⟨θ, rfl⟩ := h
  obtain ⟨n, a, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  rw [toStinespringLinearMap_apply, toStinespringLinearMap_apply,
    UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hsum : (‖(ψ + θ).toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 : ℂ) =
      (‖ψ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 : ℂ) +
        (‖θ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖ ^ 2 : ℂ) := by
    simp_rw [norm_toPreStinespring_sum_sq, ← Finset.sum_add_distrib, add_apply, inner_add_right]
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  linarith [sq_nonneg ‖θ.toPreStinespring (∑ i, a i ⊗ₜ[ℂ] ξ i)‖]

end Monotone

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : D →CP (H →L[ℂ] H))

@[simp] theorem stinespringHom_one : φ.stinespringHom 1 = 1 :=
  completion_ext φ fun a ξ => by
    simp [stinespringHom_apply, ContinuousLinearMap.completion_apply_coe]

/-- The unital Stinespring `⋆`-representation of a unital C⋆-algebra `D` on `φ.Stinespring`. -/
noncomputable def stinespringStarAlgHom : D →⋆ₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  __ := φ.stinespringHom
  map_one' := φ.stinespringHom_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, φ.stinespringHom_one]

@[simp] theorem coe_stinespringStarAlgHom : ⇑φ.stinespringStarAlgHom = ⇑φ.stinespringHom := (rfl)

@[simp] theorem toNonUnitalStarAlgHom_stinespringStarAlgHom :
    φ.stinespringStarAlgHom.toNonUnitalStarAlgHom = φ.stinespringHom := (rfl)

/-- When the domain is unital, `φ.stinespringOp` is simply `ξ ↦ [1 ⊗ ξ]`. -/
theorem stinespringOp_eq_toStinespring_one : φ.stinespringOp = φ.toStinespring 1 := by
  ext ξ
  simpa [stinespringHom_one] using φ.stinespringHom_apply_stinespringOp 1 ξ

@[simp] theorem stinespringOp_adjoint_comp_self :
    φ.stinespringOp.adjoint.comp φ.stinespringOp = φ 1 := by
  simpa [stinespringHom_one, ContinuousLinearMap.one_def] using φ.stinespring_eq 1

theorem norm_stinespringOp_sq_eq_norm_map_one : ‖φ.stinespringOp‖ ^ 2 = ‖φ 1‖ := by
  rw [← φ.stinespringOp_adjoint_comp_self, ContinuousLinearMap.norm_adjoint_comp_self, sq]

/-- A completely positive map from a unital C⋆-algebra into `H →L[ℂ] H` attains its operator norm
at `1`: `‖φ‖ = ‖φ 1‖`. -/
@[simp] theorem opNorm_toContinuousLinearMap_eq_norm_map_one :
    ‖φ.toContinuousLinearMap‖ = ‖φ 1‖ := by
  rw [← φ.norm_stinespringOp_sq, φ.norm_stinespringOp_sq_eq_norm_map_one]

/-- The Stinespring operator is an isometry if and only if `φ` is unital (`φ 1 = 1`). -/
theorem isometry_stinespringOp_iff : Isometry φ.stinespringOp ↔ φ 1 = 1 := by
  rw [ContinuousLinearMap.isometry_iff_adjoint_comp_self, φ.stinespringOp_adjoint_comp_self]

/-- The **subunital Kadison–Schwarz inequality** for a completely positive map from a unital
C⋆-algebra into `H →L[ℂ] H`: `star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a)`. -/
theorem star_map_mul_map_le_norm_map_one_smul (a : D) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) :=
  φ.opNorm_toContinuousLinearMap_eq_norm_map_one ▸ φ.star_map_mul_map_le_opNorm_smul a

/-- The **Kadison–Schwarz inequality** for a unital completely positive map into `H →L[ℂ] H`. -/
theorem star_map_mul_map_le_of_map_one (h1 : φ 1 = 1) (a : D) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  by_cases hH : Subsingleton H
  · exact le_of_eq (Subsingleton.elim _ _)
  · rw [not_subsingleton_iff_nontrivial] at hH
    simpa [h1] using φ.star_map_mul_map_le_norm_map_one_smul a

/-- **Stinespring's dilation theorem** (Stinespring 1955, Theorem 1; Blackadar II.6.9.7). -/
theorem stinespring :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      (∀ a, φ a = V.adjoint.comp ((π a).comp V)) ∧ ‖V‖ ^ 2 = ‖φ 1‖ ∧
      (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringStarAlgHom,
    φ.stinespringOp, fun a => (φ.stinespring_eq a).symm, φ.norm_stinespringOp_sq_eq_norm_map_one,
    φ.topologicalClosure_span_stinespring⟩

end Unital

end CompletelyPositiveMap
