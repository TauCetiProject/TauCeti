/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Stinespring's dilation theorem and unitary uniqueness of minimal dilations

For a completely positive map `φ : A →CP (H →L[ℂ] H)` from a (possibly nonunital) C⋆-algebra `A`
into the bounded operators on a complex Hilbert space `H`, the algebraic tensor product `A ⊗[ℂ] H`
carries the sesquilinear form

`⟪a ⊗ₜ ξ, b ⊗ₜ η⟫ = ⟪ξ, φ (star a * b) η⟫_ℂ`.

Complete positivity of `φ` makes this form positive semidefinite: on any finite sum
`∑ i, a i ⊗ₜ ξ i` it is the vector quadratic form of `(CStarMatrix.gram A a).map φ`. Following
Mathlib's `PositiveLinearMap.PreGNS` / `PositiveLinearMap.GNS` pattern, we wrap `A ⊗[ℂ] H` in a
structure `φ.PreStinespring` and take its Hausdorff completion `φ.Stinespring`
(`UniformSpace.Completion φ.PreStinespring`), which automatically separates and completes the
semi-inner product space into a Hilbert space.

Left multiplication `a ⊗ₜ ξ ↦ (c * a) ⊗ₜ ξ` is bounded by `‖c‖` on `φ.PreStinespring` and extends
to a nondegenerate ⋆-representation
`φ.stinespringNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring)`. Along the
canonical increasing approximate unit of `A`, the vectors `[e ⊗ₜ ξ]` form a Cauchy net whose limit
defines the connecting bounded operator `φ.stinespringOp : H →L[ℂ] φ.Stinespring` satisfying:

* `φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOp ξ) = φ.stinespringTmul a ξ`;
* `φ a = φ.stinespringOp.adjoint ∘L φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOp`;
* `‖φ.stinespringOp‖ ^ 2 = ‖φ.toContinuousLinearMap‖`;
* `(Submodule.span ℂ {x | ∃ a ξ, x = π a (V ξ)}).topologicalClosure = ⊤` (minimality).

When `A` is unital, `φ.stinespringStarAlgHom` is a unital ⋆-representation,
`φ.stinespringOp ξ = [1 ⊗ₜ ξ]`, `‖φ.stinespringOp‖ ^ 2 = ‖φ 1‖`, and `φ.stinespringOp` is an
isometry whenever `φ 1 = 1`. Finally, any minimal Stinespring dilation `(K, π, V)` of `φ` is
unitarily equivalent to `(φ.Stinespring, φ.stinespringNonUnitalStarAlgHom, φ.stinespringOp)` by a
unique unitary intertwiner `φ.stinespringEquiv`.

## Main declarations

* `CompletelyPositiveMap.PreStinespring`, `CompletelyPositiveMap.Stinespring`: the pre-Hilbert
  wrapper around `A ⊗[ℂ] H` and its Hilbert-space completion.
* `CompletelyPositiveMap.stinespringTmul`: the pure-tensor class map `(a, ξ) ↦ [a ⊗ₜ ξ]`.
* `CompletelyPositiveMap.stinespringNonUnitalStarAlgHom`,
  `CompletelyPositiveMap.stinespringStarAlgHom`: the canonical nonunital and unital Stinespring
  representations.
* `CompletelyPositiveMap.stinespringOp`: the connecting bounded linear map `H →L[ℂ] φ.Stinespring`,
  with dilation identity `stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp`, norm
  identity `norm_stinespringOp_sq`, minimality `topologicalClosure_span_stinespring_eq_top`, and
  nondegeneracy `isNondegenerate_stinespringNonUnitalStarAlgHom`.
* `CompletelyPositiveMap.exists_stinespring_nonUnital`,
  `CompletelyPositiveMap.exists_stinespring`: existential minimal Stinespring dilation theorems.
* `CompletelyPositiveMap.stinespringEquiv`, `CompletelyPositiveMap.existsUnique_stinespringEquiv`,
  `CompletelyPositiveMap.existsUnique_stinespringEquiv_unital`: canonical unitary equivalence and
  uniqueness of minimal Stinespring dilations.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216, Theorem 1.
* W. B. Arveson, *Subalgebras of C*-algebras*, Acta Math. 123 (1969), 141–224, §1.2.
* B. Blackadar, *Operator Algebras*, §II.6.9.7.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 4.1 and Proposition 4.2.
* The `PreStinespring` / `UniformSpace.Completion` construction parallels Mathlib's GNS
  construction in `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`.
-/

public section

noncomputable section

open Filter Topology ContinuousLinearMap UniformSpace
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal TensorProduct

namespace CompletelyPositiveMap

universe u v w

section PreStinespring

variable {A : Type u} {H : Type v}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pre-Hilbert space underlying the Stinespring dilation of `φ : A →CP (H →L[ℂ] H)`: a
single-field wrapper around `A ⊗[ℂ] H` equipped with the semi-inner product
`⟪a ⊗ₜ ξ, b ⊗ₜ η⟫ = ⟪ξ, φ (star a * b) η⟫_ℂ`. Its Hausdorff completion is
`CompletelyPositiveMap.Stinespring`. -/
@[ext]
structure PreStinespring (φ : A →CP (H →L[ℂ] H)) : Type (max u v) where
  /-- The underlying tensor in `A ⊗[ℂ] H`. -/
  ofPreStinespring : A ⊗[ℂ] H

section Algebraic

variable (φ : A →CP (H →L[ℂ] H))

instance : AddCommGroup φ.PreStinespring where
  add x y := ⟨x.1 + y.1⟩
  add_assoc _ _ _ := PreStinespring.ext (add_assoc _ _ _)
  zero := ⟨0⟩
  zero_add _ := PreStinespring.ext (zero_add _)
  add_zero _ := PreStinespring.ext (add_zero _)
  nsmul n x := ⟨n • x.1⟩
  nsmul_zero _ := PreStinespring.ext (zero_smul ℕ _)
  nsmul_succ _ _ := PreStinespring.ext (succ_nsmul _ _)
  neg x := ⟨-x.1⟩
  sub x y := ⟨x.1 - y.1⟩
  sub_eq_add_neg _ _ := PreStinespring.ext (sub_eq_add_neg _ _)
  zsmul n x := ⟨n • x.1⟩
  zsmul_zero' _ := PreStinespring.ext (zero_smul ℤ _)
  zsmul_succ' _ _ := PreStinespring.ext (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := PreStinespring.ext (SubNegMonoid.zsmul_neg' _ _)
  neg_add_cancel _ := PreStinespring.ext (neg_add_cancel _)
  add_comm _ _ := PreStinespring.ext (add_comm _ _)

instance : Module ℂ φ.PreStinespring where
  smul c x := ⟨c • x.1⟩
  one_smul _ := PreStinespring.ext (one_smul ℂ _)
  mul_smul _ _ _ := PreStinespring.ext (mul_smul _ _ _)
  smul_zero _ := PreStinespring.ext (smul_zero _)
  smul_add _ _ _ := PreStinespring.ext (smul_add _ _ _)
  add_smul _ _ _ := PreStinespring.ext (add_smul _ _ _)
  zero_smul _ := PreStinespring.ext (zero_smul ℂ _)

@[simp] theorem ofPreStinespring_zero : (0 : φ.PreStinespring).ofPreStinespring = 0 := (rfl)
@[simp] theorem ofPreStinespring_add (x y : φ.PreStinespring) :
    (x + y).ofPreStinespring = x.ofPreStinespring + y.ofPreStinespring := (rfl)
@[simp] theorem ofPreStinespring_neg (x : φ.PreStinespring) :
    (-x).ofPreStinespring = -x.ofPreStinespring := (rfl)
@[simp] theorem ofPreStinespring_sub (x y : φ.PreStinespring) :
    (x - y).ofPreStinespring = x.ofPreStinespring - y.ofPreStinespring := (rfl)
@[simp] theorem ofPreStinespring_smul (c : ℂ) (x : φ.PreStinespring) :
    (c • x).ofPreStinespring = c • x.ofPreStinespring := (rfl)

/-- The canonical linear equivalence from `A ⊗[ℂ] H` to `φ.PreStinespring`. -/
def toPreStinespring : (A ⊗[ℂ] H) ≃ₗ[ℂ] φ.PreStinespring where
  toFun x := ⟨x⟩
  invFun := PreStinespring.ofPreStinespring
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem ofPreStinespring_toPreStinespring (x : A ⊗[ℂ] H) :
    (φ.toPreStinespring x).ofPreStinespring = x := (rfl)

@[simp]
theorem toPreStinespring_ofPreStinespring (x : φ.PreStinespring) :
    φ.toPreStinespring x.ofPreStinespring = x := (rfl)

@[simp]
theorem toPreStinespring_symm_apply (x : φ.PreStinespring) :
    φ.toPreStinespring.symm x = x.ofPreStinespring := (rfl)

@[simp]
theorem ofPreStinespring_sum {ι : Type*} (s : Finset ι) (f : ι → φ.PreStinespring) :
    (∑ i ∈ s, f i).ofPreStinespring = ∑ i ∈ s, (f i).ofPreStinespring :=
  map_sum φ.toPreStinespring.symm f s

/-- Right half of the Stinespring sesquilinear form on `A ⊗[ℂ] H`, sending `b ⊗ₜ η` to
`⟪ξ, φ (star a * b) η⟫_ℂ` for fixed `a : A` and `ξ : H`. -/
private def stinespringSesqRight (a : A) (ξ : H) : (A ⊗[ℂ] H) →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun b :=
        { toFun η := ⟪ξ, φ (star a * b) η⟫_ℂ
          map_add' η₁ η₂ := by simp
          map_smul' c η := by simp }
      map_add' b₁ b₂ := by
        ext η
        simp [mul_add]
      map_smul' c b := by
        ext η
        simp [mul_smul_comm] }

private theorem stinespringSesqRight_tmul (a b : A) (ξ η : H) :
    stinespringSesqRight φ a ξ (b ⊗ₜ[ℂ] η) = ⟪ξ, φ (star a * b) η⟫_ℂ :=
  rfl

/-- The Stinespring sesquilinear form on `A ⊗[ℂ] H`, conjugate-linear in the first tensor and
complex-linear in the second, given on pure tensors by
`stinespringSesqForm φ (a ⊗ₜ ξ) (b ⊗ₜ η) = ⟪ξ, φ (star a * b) η⟫_ℂ`. -/
private def stinespringSesqForm : (A ⊗[ℂ] H) →ₗ⋆[ℂ] (A ⊗[ℂ] H) →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun a :=
        { toFun ξ := stinespringSesqRight φ a ξ
          map_add' ξ₁ ξ₂ := TensorProduct.ext' fun b η => by
            simp [stinespringSesqRight_tmul]
          map_smul' c ξ := TensorProduct.ext' fun b η => by
            simp [stinespringSesqRight_tmul]
            ring }
      map_add' a₁ a₂ := LinearMap.ext fun ξ => TensorProduct.ext' fun b η => by
        simp [stinespringSesqRight_tmul, add_mul]
      map_smul' c a := LinearMap.ext fun ξ => TensorProduct.ext' fun b η => by
        simp [stinespringSesqRight_tmul, star_smul, smul_mul_assoc] }

private theorem stinespringSesqForm_tmul (a b : A) (ξ η : H) :
    stinespringSesqForm φ (a ⊗ₜ[ℂ] ξ) (b ⊗ₜ[ℂ] η) = ⟪ξ, φ (star a * b) η⟫_ℂ :=
  rfl

private theorem stinespringSesqForm_conj_symm (x y : A ⊗[ℂ] H) :
    (starRingEnd ℂ) (stinespringSesqForm φ y x) = stinespringSesqForm φ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a ξ =>
    induction y using TensorProduct.inductionOn with
    | tmul b η =>
      simp only [stinespringSesqForm_tmul, inner_conj_symm]
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, star_mul, star_star]
    | add y₁ y₂ hy₁ hy₂ => simp [map_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp [map_add, hx₁, hx₂]

private theorem stinespringSesqForm_self_nonneg (x : A ⊗[ℂ] H) :
    0 ≤ stinespringSesqForm φ x x := by
  obtain ⟨k, a, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  have hsum :
      stinespringSesqForm φ (∑ i, a i ⊗ₜ[ℂ] ξ i) (∑ j, a j ⊗ₜ[ℂ] ξ j) =
        ∑ i, ∑ j, ⟪ξ i, ((CStarMatrix.gram A a).map φ) i j (ξ j)⟫_ℂ := by
    simp only [map_sum, LinearMap.sum_apply, stinespringSesqForm_tmul, CStarMatrix.map_apply,
      CStarMatrix.gram_apply]
    exact Finset.sum_comm
  rw [hsum]
  exact CStarMatrix.sum_inner_nonneg (φ.map_cstarMatrix_nonneg _ (CStarMatrix.gram_nonneg a)) ξ

/-- The pre-inner product core on `φ.PreStinespring`. -/
@[instance_reducible]
def preStinespringCore : PreInnerProductSpace.Core ℂ φ.PreStinespring where
  inner x y := stinespringSesqForm φ x.ofPreStinespring y.ofPreStinespring
  conj_inner_symm x y := stinespringSesqForm_conj_symm φ x.ofPreStinespring y.ofPreStinespring
  re_inner_nonneg x := (Complex.nonneg_iff.mp (stinespringSesqForm_self_nonneg φ x.1)).1
  add_left x y z := by simp [map_add]
  smul_left x y c := by simp [map_smulₛₗ]

instance : SeminormedAddCommGroup φ.PreStinespring :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preStinespringCore)

instance : InnerProductSpace ℂ φ.PreStinespring :=
  InnerProductSpace.ofCore φ.preStinespringCore

@[simp]
theorem preStinespring_inner_tmul (a b : A) (ξ η : H) :
    ⟪φ.toPreStinespring (a ⊗ₜ[ℂ] ξ), φ.toPreStinespring (b ⊗ₜ[ℂ] η)⟫_ℂ =
      ⟪ξ, φ (star a * b) η⟫_ℂ :=
  (rfl)

/-- Squared seminorm on `φ.PreStinespring` as a complex inner product. -/
theorem preStinespring_norm_sq (x : φ.PreStinespring) :
    (‖x‖ ^ 2 : ℂ) = ⟪x, x⟫_ℂ :=
  (inner_self_eq_norm_sq_to_K x).symm

/-- Squared seminorm on `φ.PreStinespring` as the real part of the inner product. -/
theorem preStinespring_norm_sq_re (x : φ.PreStinespring) :
    ‖x‖ ^ 2 = (⟪x, x⟫_ℂ).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex]

end Algebraic

end PreStinespring

section Stinespring

variable {A : Type u} {H : Type v}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Hilbert space of the canonical Stinespring dilation of `φ : A →CP (H →L[ℂ] H)`, obtained as
the uniform Hausdorff completion of `φ.PreStinespring`. -/
abbrev Stinespring (φ : A →CP (H →L[ℂ] H)) : Type (max u v) :=
  UniformSpace.Completion φ.PreStinespring

section NonUnital

variable (φ : A →CP (H →L[ℂ] H))

/-- The class `[a ⊗ₜ ξ]` in the Stinespring Hilbert space `φ.Stinespring`. -/
def stinespringTmul (a : A) (ξ : H) : φ.Stinespring :=
  (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ) : φ.Stinespring)

theorem stinespringTmul_def (a : A) (ξ : H) :
    φ.stinespringTmul a ξ = (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ) : φ.Stinespring) :=
  (rfl)

@[simp]
theorem stinespringTmul_add_left (a b : A) (ξ : H) :
    φ.stinespringTmul (a + b) ξ = φ.stinespringTmul a ξ + φ.stinespringTmul b ξ := by
  rw [stinespringTmul_def, stinespringTmul_def, stinespringTmul_def,
    TensorProduct.add_tmul, map_add, Completion.coe_add]

@[simp]
theorem stinespringTmul_add_right (a : A) (ξ η : H) :
    φ.stinespringTmul a (ξ + η) = φ.stinespringTmul a ξ + φ.stinespringTmul a η := by
  rw [stinespringTmul_def, stinespringTmul_def, stinespringTmul_def,
    TensorProduct.tmul_add, map_add, Completion.coe_add]

@[simp]
theorem stinespringTmul_smul_left (c : ℂ) (a : A) (ξ : H) :
    φ.stinespringTmul (c • a) ξ = c • φ.stinespringTmul a ξ := by
  rw [stinespringTmul_def, stinespringTmul_def, ← TensorProduct.smul_tmul',
    map_smul, Completion.coe_smul]

@[simp]
theorem stinespringTmul_smul_right (c : ℂ) (a : A) (ξ : H) :
    φ.stinespringTmul a (c • ξ) = c • φ.stinespringTmul a ξ := by
  rw [stinespringTmul_def, stinespringTmul_def, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul', map_smul, Completion.coe_smul]

@[simp]
theorem stinespringTmul_zero_left (ξ : H) : φ.stinespringTmul 0 ξ = 0 := by
  simpa using φ.stinespringTmul_smul_left 0 0 ξ

@[simp]
theorem stinespringTmul_zero_right (a : A) : φ.stinespringTmul a 0 = 0 := by
  simpa using φ.stinespringTmul_smul_right 0 a 0

@[simp]
theorem inner_stinespringTmul (a b : A) (ξ η : H) :
    ⟪φ.stinespringTmul a ξ, φ.stinespringTmul b η⟫_ℂ = ⟪ξ, φ (star a * b) η⟫_ℂ := by
  simp [stinespringTmul_def]

/-- Squared norm of a pure-tensor class `[a ⊗ₜ ξ]` in `φ.Stinespring`. -/
theorem norm_stinespringTmul_sq (a : A) (ξ : H) :
    ‖φ.stinespringTmul a ξ‖ ^ 2 = (⟪ξ, φ (star a * a) ξ⟫_ℂ).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_stinespringTmul, RCLike.re_to_complex]

/-- Norm bound `‖[a ⊗ₜ ξ]‖ ≤ √‖φ‖ * ‖a‖ * ‖ξ‖` in `φ.Stinespring`. -/
theorem norm_stinespringTmul_le (a : A) (ξ : H) :
    ‖φ.stinespringTmul a ξ‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖ * ‖ξ‖ := by
  have hsq : ‖φ.stinespringTmul a ξ‖ ^ 2 ≤
      (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖ * ‖ξ‖) ^ 2 := by
    calc
      ‖φ.stinespringTmul a ξ‖ ^ 2 = (⟪ξ, φ (star a * a) ξ⟫_ℂ).re := φ.norm_stinespringTmul_sq a ξ
      _ ≤ ‖⟪ξ, φ (star a * a) ξ⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖ξ‖ * ‖φ (star a * a) ξ‖ := norm_inner_le_norm ξ _
      _ ≤ ‖ξ‖ * (‖φ (star a * a)‖ * ‖ξ‖) := by gcongr; exact (φ (star a * a)).le_opNorm ξ
      _ ≤ ‖ξ‖ * (‖φ.toContinuousLinearMap‖ * ‖star a * a‖ * ‖ξ‖) := by
        gcongr
        simpa using φ.toContinuousLinearMap.le_opNorm (star a * a)
      _ = (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖a‖ * ‖ξ‖) ^ 2 := by
        rw [CStarRing.norm_star_mul_self, mul_pow, mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- For fixed `ξ : H`, the pure-tensor class map `a ↦ [a ⊗ₜ ξ]` is norm-continuous. -/
@[fun_prop]
theorem continuous_stinespringTmul_left (ξ : H) :
    Continuous (fun a : A => φ.stinespringTmul a ξ) :=
  let f : A →ₗ[ℂ] φ.Stinespring :=
    { toFun a := φ.stinespringTmul a ξ
      map_add' a b := φ.stinespringTmul_add_left a b ξ
      map_smul' c a := φ.stinespringTmul_smul_left c a ξ }
  (f.mkContinuous (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖ξ‖) fun a => by
    simpa [f, mul_right_comm] using φ.norm_stinespringTmul_le a ξ).continuous

private theorem norm_leftMul_preStinespring_le (c : A) (x : φ.PreStinespring) :
    ‖φ.toPreStinespring ((LinearMap.rTensor H (LinearMap.mulLeft ℂ c)) x.ofPreStinespring)‖ ≤
      ‖c‖ * ‖x‖ := by
  obtain ⟨k, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq x.ofPreStinespring
  let N : CStarMatrix (Fin k) (Fin k) A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j =>
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j) - star (c * a i) * (c * a j))
  have hpos := (Complex.nonneg_iff.mp
    (CStarMatrix.sum_inner_nonneg
      (φ.map_cstarMatrix_nonneg N (CStarMatrix.norm_sq_smul_sub_mulLeft_nonneg c a)) ξ)).1
  have hx' : x = ∑ i, φ.toPreStinespring (a i ⊗ₜ[ℂ] ξ i) := PreStinespring.ext (by simpa using hx)
  have hdiff :
      (∑ i, ∑ j, ⟪ξ i, (N.map φ) i j (ξ j)⟫_ℂ).re =
        ‖c‖ ^ 2 * ‖x‖ ^ 2 -
          ‖φ.toPreStinespring
            ((LinearMap.rTensor H (LinearMap.mulLeft ℂ c)) x.ofPreStinespring)‖ ^ 2 := by
    have hNij (i j : Fin k) :
        (N.map φ) i j (ξ j) =
          ((‖c‖ ^ 2 : ℝ) : ℂ) • (φ (star (a i) * a j) (ξ j)) -
            φ (star (c * a i) * (c * a j)) (ξ j) := by
      simp [N, CStarMatrix.map_apply, map_sub]
    simp_rw [hNij, inner_sub_right, inner_smul_right, Finset.sum_sub_distrib]
    rw [φ.preStinespring_norm_sq_re x, φ.preStinespring_norm_sq_re, hx, hx']
    simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
      sum_inner, inner_sum, preStinespring_inner_tmul,
      Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_comm
  rw [hdiff, sub_nonneg, ← mul_pow] at hpos
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hpos

/-- Left multiplication by `c : A` on `φ.PreStinespring`, sending `a ⊗ₜ ξ` to `(c * a) ⊗ₜ ξ`, is
bounded with operator norm at most `‖c‖`. -/
private def leftMulMapPreStinespring (c : A) : φ.PreStinespring →L[ℂ] φ.PreStinespring :=
  (φ.toPreStinespring.toLinearMap.comp
    ((LinearMap.rTensor H (LinearMap.mulLeft ℂ c)).comp φ.toPreStinespring.symm.toLinearMap))
    |>.mkContinuous ‖c‖ (φ.norm_leftMul_preStinespring_le c)

@[simp]
private theorem leftMulMapPreStinespring_tmul (c a : A) (ξ : H) :
    φ.leftMulMapPreStinespring c (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)) =
      φ.toPreStinespring ((c * a) ⊗ₜ[ℂ] ξ) :=
  (rfl)

@[simp]
private theorem leftMulMapPreStinespring_add (c d : A) :
    φ.leftMulMapPreStinespring (c + d) =
      φ.leftMulMapPreStinespring c + φ.leftMulMapPreStinespring d := by
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a ξ => simp [add_mul, TensorProduct.add_tmul]
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂]

@[simp]
private theorem leftMulMapPreStinespring_smul (m : ℂ) (c : A) :
    φ.leftMulMapPreStinespring (m • c) = m • φ.leftMulMapPreStinespring c := by
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a ξ => simp [smul_mul_assoc, ← TensorProduct.smul_tmul']
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂]

@[simp]
private theorem leftMulMapPreStinespring_mul (c d : A) :
    φ.leftMulMapPreStinespring (c * d) =
      φ.leftMulMapPreStinespring c ∘L φ.leftMulMapPreStinespring d := by
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a ξ => simp [mul_assoc]
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, map_add, ht₁, ht₂]

private theorem inner_leftMulMapPreStinespring (c : A) (x y : φ.PreStinespring) :
    ⟪φ.leftMulMapPreStinespring (star c) x, y⟫_ℂ =
      ⟪x, φ.leftMulMapPreStinespring c y⟫_ℂ := by
  obtain ⟨tx, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  obtain ⟨ty, rfl⟩ : ∃ t, φ.toPreStinespring t = y := ⟨y.1, rfl⟩
  induction tx using TensorProduct.inductionOn with
  | tmul a ξ =>
    induction ty using TensorProduct.inductionOn with
    | tmul b η => simp [mul_assoc]
    | add y₁ y₂ hy₁ hy₂ => rw [map_add, map_add, inner_add_right, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => rw [map_add, map_add, inner_add_left, inner_add_left, hx₁, hx₂]

private theorem completion_leftMulMapPreStinespring_smul (m : ℂ) (c : A) :
    (φ.leftMulMapPreStinespring (m • c)).completion =
      m • (φ.leftMulMapPreStinespring c).completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (φ.leftMulMapPreStinespring (m • c)).completion.continuous
      (m • (φ.leftMulMapPreStinespring c).completion).continuous
  | ih x => simp

/-- The canonical nonunital ⋆-representation `A →⋆ₙₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring)`
associated to `φ : A →CP (H →L[ℂ] H)`. -/
def stinespringNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  toFun c := (φ.leftMulMapPreStinespring c).completion
  map_smul' m c := φ.completion_leftMulMapPreStinespring_smul m c
  map_zero' := by simpa using φ.completion_leftMulMapPreStinespring_smul 0 0
  map_add' c d := by
    ext x
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (φ.leftMulMapPreStinespring (c + d)).completion.continuous
        ((φ.leftMulMapPreStinespring c).completion +
          (φ.leftMulMapPreStinespring d).completion).continuous
    | ih x => simp [UniformSpace.Completion.coe_add]
  map_mul' c d := by
    ext x
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (φ.leftMulMapPreStinespring (c * d)).completion.continuous
        ((φ.leftMulMapPreStinespring c).completion ∘L
          (φ.leftMulMapPreStinespring d).completion).continuous
    | ih x => simp
  map_star' c := by
    refine (ContinuousLinearMap.eq_adjoint_iff
      (φ.leftMulMapPreStinespring (star c)).completion
      (φ.leftMulMapPreStinespring c).completion).mpr fun x y => ?_
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp [inner_leftMulMapPreStinespring]

@[simp]
theorem stinespringNonUnitalStarAlgHom_apply_stinespringTmul (c a : A) (ξ : H) :
    φ.stinespringNonUnitalStarAlgHom c (φ.stinespringTmul a ξ) = φ.stinespringTmul (c * a) ξ := by
  simp [stinespringNonUnitalStarAlgHom, stinespringTmul_def]

/-- Positive continuous linear functional `a ↦ ⟪ξ, φ a ξ⟫_ℂ` associated to `ξ : H`. -/
private def stinespringFunctional (ξ : H) : A →P[ℂ] ℂ where
  toLinearMap :=
    { toFun a := ⟪ξ, φ a ξ⟫_ℂ
      map_add' a b := by simp
      map_smul' c a := by simp }
  monotone' a b hab := by
    rw [← sub_nonneg] at hab ⊢
    have hpos : 0 ≤ φ (b - a) := _root_.map_nonneg φ hab
    simpa [map_sub, inner_sub_right] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).inner_nonneg_right ξ
  cont := by
    let L : A →L[ℂ] ℂ :=
      (innerSL ℂ ξ).comp
        ((ContinuousLinearMap.apply ℂ H ξ).comp φ.toContinuousLinearMap)
    have hL : (fun a : A => ⟪ξ, φ a ξ⟫_ℂ) = L := by ext a; simp [L]
    exact hL ▸ L.continuous

@[simp]
private theorem stinespringFunctional_apply (ξ : H) (a : A) :
    φ.stinespringFunctional ξ a = ⟪ξ, φ a ξ⟫_ℂ := (rfl)

private theorem norm_stinespringFunctional_le (ξ : H) :
    ‖(φ.stinespringFunctional ξ : A →L[ℂ] ℂ)‖ ≤ ‖φ.toContinuousLinearMap‖ * ‖ξ‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  calc
    ‖(φ.stinespringFunctional ξ : A →L[ℂ] ℂ) a‖ = ‖⟪ξ, φ a ξ⟫_ℂ‖ := rfl
    _ ≤ ‖ξ‖ * ‖φ a ξ‖ := norm_inner_le_norm ξ (φ a ξ)
    _ ≤ ‖ξ‖ * (‖φ a‖ * ‖ξ‖) := by gcongr; exact (φ a).le_opNorm ξ
    _ ≤ ‖ξ‖ * (‖φ.toContinuousLinearMap‖ * ‖a‖ * ‖ξ‖) := by
      gcongr
      simpa using φ.toContinuousLinearMap.le_opNorm a
    _ = ‖φ.toContinuousLinearMap‖ * ‖ξ‖ ^ 2 * ‖a‖ := by ring

private theorem dist_stinespringTmul_sq_le (ξ : H) {x e : A}
    (hx0 : 0 ≤ x) (hxe : x ≤ e) (he1 : ‖e‖ ≤ 1) :
    dist (φ.stinespringTmul e ξ) (φ.stinespringTmul x ξ) ^ 2 ≤
      (⟪ξ, φ e ξ⟫_ℂ).re - (⟪ξ, φ x ξ⟫_ℂ).re := by
  let d : A := e - x
  have hd0 : 0 ≤ d := sub_nonneg.mpr hxe
  have hde : d ≤ e := sub_le_self e hx0
  have hd1 : ‖d‖ ≤ 1 := (CStarAlgebra.norm_le_norm_of_le_of_nonneg hde hd0).trans he1
  have hdd : star d * d ≤ d :=
    (IsSelfAdjoint.of_nonneg hd0).star_eq.symm ▸
      CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hd0 hd1
  have hle : ⟪ξ, φ (star d * d) ξ⟫_ℂ ≤ ⟪ξ, φ d ξ⟫_ℂ := (φ.stinespringFunctional ξ).monotone' hdd
  have hsub : φ.stinespringTmul e ξ - φ.stinespringTmul x ξ = φ.stinespringTmul d ξ := by
    rw [sub_eq_iff_eq_add, ← stinespringTmul_add_left, sub_add_cancel]
  rw [dist_eq_norm, hsub, φ.norm_stinespringTmul_sq d ξ]
  simpa [d, map_sub, inner_sub_right] using (Complex.le_def.mp hle).1

private theorem exists_tendsto_stinespringTmul_approximateUnit (ξ : H) :
    ∃ w : φ.Stinespring,
      Tendsto (fun e : A => φ.stinespringTmul e ξ) (CStarAlgebra.approximateUnit A) (𝓝 w) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  let f := φ.stinespringFunctional ξ
  have hre : Tendsto (fun e : A => (⟪ξ, φ e ξ⟫_ℂ).re)
      (CStarAlgebra.approximateUnit A) (𝓝 ‖(f : A →L[ℂ] ℂ)‖) :=
    Complex.continuous_re.continuousAt.tendsto.comp (f.tendsto_nhds_opNorm hl)
  refine cauchy_map_iff_exists_tendsto.mp (Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩)
  have hmem :
      {e : A | |(⟪ξ, φ e ξ⟫_ℂ).re - ‖(f : A →L[ℂ] ℂ)‖| < (ε / 2) ^ 2 / 2} ∈
        CStarAlgebra.approximateUnit A :=
    hre.eventually (Metric.ball_mem_nhds ‖(f : A →L[ℂ] ℂ)‖ (by positivity))
  obtain ⟨x, ⟨hx0, hx1⟩, hxS⟩ := (CStarAlgebra.hasBasis_approximateUnit A).mem_iff.mp hmem
  let S : Set A := {e : A | x ≤ e} ∩ Metric.closedBall 0 1
  refine ⟨(fun e : A => φ.stinespringTmul e ξ) '' S,
    Filter.image_mem_map ((CStarAlgebra.hasBasis_approximateUnit A).mem_of_mem ⟨hx0, hx1⟩), ?_⟩
  rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
  have hx_lt : |(⟪ξ, φ x ξ⟫_ℂ).re - ‖(f : A →L[ℂ] ℂ)‖| < (ε / 2) ^ 2 / 2 :=
    hxS ⟨le_rfl, by simpa using hx1.le⟩
  have hdist {e : A} (he : e ∈ S) :
      dist (φ.stinespringTmul e ξ) (φ.stinespringTmul x ξ) < ε / 2 := by
    have he_lt : |(⟪ξ, φ e ξ⟫_ℂ).re - ‖(f : A →L[ℂ] ℂ)‖| < (ε / 2) ^ 2 / 2 := hxS he
    have hsq : dist (φ.stinespringTmul e ξ) (φ.stinespringTmul x ξ) ^ 2 < (ε / 2) ^ 2 := by
      have h1 := φ.dist_stinespringTmul_sq_le ξ hx0 he.1 (by simpa using he.2)
      linarith [abs_lt.mp hx_lt, abs_lt.mp he_lt]
    nlinarith [dist_nonneg (x := φ.stinespringTmul e ξ) (y := φ.stinespringTmul x ξ)]
  calc
    dist (φ.stinespringTmul e₁ ξ) (φ.stinespringTmul e₂ ξ)
      ≤ dist (φ.stinespringTmul e₁ ξ) (φ.stinespringTmul x ξ) +
          dist (φ.stinespringTmul x ξ) (φ.stinespringTmul e₂ ξ) := dist_triangle _ _ _
    _ = dist (φ.stinespringTmul e₁ ξ) (φ.stinespringTmul x ξ) +
          dist (φ.stinespringTmul e₂ ξ) (φ.stinespringTmul x ξ) := by
          rw [dist_comm _ (φ.stinespringTmul e₂ ξ)]
    _ < ε / 2 + ε / 2 := add_lt_add (hdist he₁) (hdist he₂)
    _ = ε := add_halves ε

private theorem norm_choose_stinespringOp_le (ξ : H) :
    ‖(φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose‖ ≤
      Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖ξ‖ := by
  set v := (φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose
  have hlim := (φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose_spec
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hnorm_tendsto :
      Tendsto (fun e : A => ‖φ.stinespringTmul e ξ‖ ^ 2)
        (CStarAlgebra.approximateUnit A) (𝓝 (‖v‖ ^ 2)) :=
    (continuous_pow 2).continuousAt.tendsto.comp hlim.norm
  have hre_tendsto :
      Tendsto (fun e : A => (⟪ξ, φ e ξ⟫_ℂ).re)
        (CStarAlgebra.approximateUnit A) (𝓝 ‖(φ.stinespringFunctional ξ : A →L[ℂ] ℂ)‖) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      ((φ.stinespringFunctional ξ).tendsto_nhds_opNorm hl)
  have hcongr :
      (fun e : A => ‖φ.stinespringTmul e ξ‖ ^ 2) =ᶠ[CStarAlgebra.approximateUnit A]
        fun e : A => (⟪ξ, φ (star e * e) ξ⟫_ℂ).re :=
    Filter.Eventually.of_forall fun e => φ.norm_stinespringTmul_sq e ξ
  have hle_ev :
      ∀ᶠ e : A in CStarAlgebra.approximateUnit A,
        (⟪ξ, φ (star e * e) ξ⟫_ℂ).re ≤ (⟪ξ, φ e ξ⟫_ℂ).re := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he0 he1
    have hee : star e * e ≤ e :=
      (IsSelfAdjoint.of_nonneg he0).star_eq.symm ▸
        CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he0 he1
    exact (Complex.le_def.mp ((φ.stinespringFunctional ξ).monotone' hee)).1
  have hv_sq : ‖v‖ ^ 2 ≤ (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖ξ‖) ^ 2 := by
    calc
      ‖v‖ ^ 2 ≤ ‖(φ.stinespringFunctional ξ : A →L[ℂ] ℂ)‖ :=
        le_of_tendsto_of_tendsto (hnorm_tendsto.congr' hcongr) hre_tendsto hle_ev
      _ ≤ ‖φ.toContinuousLinearMap‖ * ‖ξ‖ ^ 2 := φ.norm_stinespringFunctional_le ξ
      _ = (Real.sqrt ‖φ.toContinuousLinearMap‖ * ‖ξ‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hv_sq

/-- The connecting bounded linear map `V : H →L[ℂ] φ.Stinespring` of the canonical Stinespring
dilation, defined as the strong limit of `ξ ↦ [e ⊗ₜ ξ]` along `CStarAlgebra.approximateUnit A`. -/
def stinespringOp : H →L[ℂ] φ.Stinespring :=
  let hlim := fun ξ => (φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose_spec
  let _ := (CStarAlgebra.increasingApproximateUnit A).neBot
  LinearMap.mkContinuous
    { toFun ξ := (φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose
      map_add' ξ η := by
        refine tendsto_nhds_unique (hlim (ξ + η)) ?_
        simpa [stinespringTmul_add_right] using (hlim ξ).add (hlim η)
      map_smul' c ξ := by
        refine tendsto_nhds_unique (hlim (c • ξ)) ?_
        simpa [stinespringTmul_smul_right] using (hlim ξ).const_smul c }
    (Real.sqrt ‖φ.toContinuousLinearMap‖) φ.norm_choose_stinespringOp_le

/-- Along the canonical increasing approximate unit of `A`, `[e ⊗ₜ ξ]` converges to
`φ.stinespringOp ξ`. -/
theorem tendsto_stinespringTmul_approximateUnit (ξ : H) :
    Tendsto (fun e : A => φ.stinespringTmul e ξ)
      (CStarAlgebra.approximateUnit A) (𝓝 (φ.stinespringOp ξ)) :=
  (φ.exists_tendsto_stinespringTmul_approximateUnit ξ).choose_spec

/-- Acting by `a : A` on `φ.stinespringOp ξ` recovers the pure-tensor class `[a ⊗ₜ ξ]`. -/
@[simp]
theorem stinespringNonUnitalStarAlgHom_apply_stinespringOp (a : A) (ξ : H) :
    φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOp ξ) = φ.stinespringTmul a ξ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h₁ :
      Tendsto (fun e : A => φ.stinespringNonUnitalStarAlgHom a (φ.stinespringTmul e ξ))
        (CStarAlgebra.approximateUnit A)
        (𝓝 (φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOp ξ))) :=
    (φ.stinespringNonUnitalStarAlgHom a).continuous.continuousAt.tendsto.comp
      (φ.tendsto_stinespringTmul_approximateUnit ξ)
  have h₂ :
      Tendsto (fun e : A => φ.stinespringTmul (a * e) ξ)
        (CStarAlgebra.approximateUnit A) (𝓝 (φ.stinespringTmul a ξ)) :=
    ((φ.continuous_stinespringTmul_left ξ).tendsto a).comp (hl.tendsto_mul_left a)
  exact tendsto_nhds_unique h₁ (by simpa using h₂)

/-- `φ.stinespringOp.adjoint` sends `[a ⊗ₜ η]` to `φ a η`. -/
@[simp]
theorem stinespringOp_adjoint_stinespringTmul (a : A) (η : H) :
    φ.stinespringOp.adjoint (φ.stinespringTmul a η) = φ a η := by
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h₁ :
      Tendsto (fun e : A => ⟪φ.stinespringTmul e ξ, φ.stinespringTmul a η⟫_ℂ)
        (CStarAlgebra.approximateUnit A)
        (𝓝 ⟪φ.stinespringOp ξ, φ.stinespringTmul a η⟫_ℂ) :=
    Filter.Tendsto.inner (φ.tendsto_stinespringTmul_approximateUnit ξ) tendsto_const_nhds
  have hcont : Continuous (fun x : A => ⟪ξ, φ x η⟫_ℂ) := by
    let L : A →L[ℂ] ℂ :=
      (innerSL ℂ ξ).comp
        ((ContinuousLinearMap.apply ℂ H η).comp φ.toContinuousLinearMap)
    have hL : (fun x : A => ⟪ξ, φ x η⟫_ℂ) = L := by ext x; simp [L]
    exact hL ▸ L.continuous
  have h₂ :
      Tendsto (fun e : A => ⟪ξ, φ (e * a) η⟫_ℂ)
        (CStarAlgebra.approximateUnit A) (𝓝 ⟪ξ, φ a η⟫_ℂ) :=
    (hcont.tendsto a).comp (hl.tendsto_mul_right a)
  have hcongr :
      (fun e : A => ⟪φ.stinespringTmul e ξ, φ.stinespringTmul a η⟫_ℂ)
        =ᶠ[CStarAlgebra.approximateUnit A] fun e : A => ⟪ξ, φ (e * a) η⟫_ℂ := by
    filter_upwards [hl.eventually_star_eq] with e he
    simp [he]
  exact tendsto_nhds_unique h₁ (h₂.congr' hcongr.symm)

/-- **Stinespring dilation identity** (nonunital form): `φ a = V† ∘L π a ∘L V` for every `a : A`. -/
theorem stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp (a : A) :
    φ.stinespringOp.adjoint ∘L φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOp = φ a := by
  ext η
  simp

/-- In terms of `CompletelyPositiveMap.conjCLM`, `φ` factors through its Stinespring
representation. -/
@[simp]
theorem conjCLM_stinespringOp_comp :
    (conjCLM φ.stinespringOp).comp
      (φ.stinespringNonUnitalStarAlgHom : A →CP (φ.Stinespring →L[ℂ] φ.Stinespring)) = φ := by
  ext a η
  simp

/-- The squared operator norm of `φ.stinespringOp` equals the operator norm of `φ`. -/
theorem norm_stinespringOp_sq :
    ‖φ.stinespringOp‖ ^ 2 = ‖φ.toContinuousLinearMap‖ := by
  refine le_antisymm ?_ ?_
  · have hle : ‖φ.stinespringOp‖ ≤ Real.sqrt ‖φ.toContinuousLinearMap‖ :=
      LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) φ.norm_choose_stinespringOp_le
    calc
      ‖φ.stinespringOp‖ ^ 2 ≤ (Real.sqrt ‖φ.toContinuousLinearMap‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg φ.stinespringOp) hle 2
      _ = ‖φ.toContinuousLinearMap‖ := Real.sq_sqrt (norm_nonneg _)
  · refine φ.toContinuousLinearMap.opNorm_le_bound (sq_nonneg _) fun a => ?_
    calc
      ‖φ.toContinuousLinearMap a‖
        = ‖φ.stinespringOp.adjoint ∘L φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOp‖ := by
          rw [toContinuousLinearMap_apply,
            ← φ.stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a]
      _ ≤ ‖φ.stinespringOp.adjoint‖ *
          ‖φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOp‖ := opNorm_comp_le _ _
      _ ≤ ‖φ.stinespringOp.adjoint‖ *
          (‖φ.stinespringNonUnitalStarAlgHom a‖ * ‖φ.stinespringOp‖) := by
          gcongr
          exact opNorm_comp_le _ _
      _ ≤ ‖φ.stinespringOp‖ * (‖a‖ * ‖φ.stinespringOp‖) := by
          rw [ContinuousLinearMap.adjoint.norm_map]
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le φ.stinespringNonUnitalStarAlgHom a
      _ = ‖φ.stinespringOp‖ ^ 2 * ‖a‖ := by ring

/-- **Minimality** of the canonical Stinespring dilation: the linear span of the vectors
`π a (V ξ)` is dense in `φ.Stinespring`. -/
theorem topologicalClosure_span_stinespring_eq_top :
    (Submodule.span ℂ
      {x : φ.Stinespring |
        ∃ (a : A) (ξ : H), x = φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOp ξ)}
    ).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  refine Completion.denseRange_coe.mono ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a ξ =>
    exact Submodule.subset_span
      ⟨a, ξ, (φ.stinespringNonUnitalStarAlgHom_apply_stinespringOp a ξ).symm⟩
  | add t₁ t₂ ht₁ ht₂ =>
    rw [map_add, UniformSpace.Completion.coe_add]
    exact Submodule.add_mem _ ht₁ ht₂

/-- The canonical Stinespring representation is nondegenerate. -/
theorem isNondegenerate_stinespringNonUnitalStarAlgHom :
    φ.stinespringNonUnitalStarAlgHom.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    eq_top_iff, ← φ.topologicalClosure_span_stinespring_eq_top]
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨a, ξ, rfl⟩
  exact Set.mem_iUnion.mpr ⟨a, φ.stinespringOp ξ, rfl⟩

/-- **Stinespring's dilation theorem** (nonunital form): every completely positive map
`φ : A →CP (H →L[ℂ] H)` admits a minimal nondegenerate dilation `(K, π, V)` with
`‖V‖ ^ 2 = ‖φ.toContinuousLinearMap‖`. -/
theorem exists_stinespring_nonUnital :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      (∀ a, φ a = V.adjoint.comp ((π a).comp V)) ∧
      ‖V‖ ^ 2 = ‖φ.toContinuousLinearMap‖ ∧
      π.IsNondegenerate ∧
      (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringNonUnitalStarAlgHom,
    φ.stinespringOp,
    fun a => (φ.stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a).symm,
    φ.norm_stinespringOp_sq, φ.isNondegenerate_stinespringNonUnitalStarAlgHom,
    φ.topologicalClosure_span_stinespring_eq_top⟩

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (φ : D →CP (H →L[ℂ] H))

@[simp]
private theorem leftMulMapPreStinespring_one :
    φ.leftMulMapPreStinespring 1 = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a ξ => simp
  | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, ht₁, ht₂]; rfl

@[simp]
theorem stinespringNonUnitalStarAlgHom_one :
    φ.stinespringNonUnitalStarAlgHom 1 = 1 := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (φ.stinespringNonUnitalStarAlgHom 1).continuous continuous_id
  | ih x => simp [stinespringNonUnitalStarAlgHom]

/-- The canonical unital ⋆-representation `D →⋆ₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring)`
associated to a completely positive map `φ` on a unital C⋆-algebra `D`. -/
def stinespringStarAlgHom : D →⋆ₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  __ := φ.stinespringNonUnitalStarAlgHom
  map_one' := φ.stinespringNonUnitalStarAlgHom_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem stinespringStarAlgHom_apply (a : D) :
    φ.stinespringStarAlgHom a = φ.stinespringNonUnitalStarAlgHom a :=
  (rfl)

/-- When `D` is unital, `φ.stinespringOp ξ` is simply the pure-tensor class `[1 ⊗ₜ ξ]`. -/
theorem stinespringOp_eq_stinespringTmul_one (ξ : H) :
    φ.stinespringOp ξ = φ.stinespringTmul 1 ξ := by
  simpa using φ.stinespringNonUnitalStarAlgHom_apply_stinespringOp 1 ξ

/-- **Stinespring dilation identity** (unital form): `φ a = V† ∘L π a ∘L V` for every `a : D`. -/
theorem stinespringOp_adjoint_comp_stinespringStarAlgHom_comp (a : D) :
    φ.stinespringOp.adjoint ∘L φ.stinespringStarAlgHom a ∘L φ.stinespringOp = φ a :=
  φ.stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a

/-- For unital `D`, `‖φ.stinespringOp‖ ^ 2 = ‖φ 1‖`. -/
theorem norm_stinespringOp_sq_eq_norm_one :
    ‖φ.stinespringOp‖ ^ 2 = ‖φ 1‖ := by
  rw [φ.norm_stinespringOp_sq, φ.norm_toContinuousLinearMap]

/-- If `φ : D →CP (H →L[ℂ] H)` is unital (`φ 1 = 1`), then `φ.stinespringOp` is an isometry. -/
theorem isometry_stinespringOp (hφ : φ 1 = 1) : Isometry φ.stinespringOp := by
  refine AddMonoidHomClass.isometry_of_norm φ.stinespringOp fun ξ => ?_
  have hsq : ‖φ.stinespringOp ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [φ.stinespringOp_eq_stinespringTmul_one, φ.norm_stinespringTmul_sq]
    simp [hφ, ← Complex.ofReal_pow]
  nlinarith [norm_nonneg (φ.stinespringOp ξ), norm_nonneg ξ]

/-- **Stinespring's dilation theorem** (unital form): every completely positive map
`φ : D →CP (H →L[ℂ] H)` on a unital C⋆-algebra `D` factors as `a ↦ V† ∘L π a ∘L V` for a unital
⋆-representation `π : D →⋆ₐ[ℂ] (K →L[ℂ] K)` and a bounded linear map `V : H →L[ℂ] K` with
`‖V‖ ^ 2 = ‖φ 1‖` and minimal cyclic span. -/
theorem exists_stinespring :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      (∀ a, φ a = V.adjoint.comp ((π a).comp V)) ∧ ‖V‖ ^ 2 = ‖φ 1‖ ∧
      (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringStarAlgHom,
    φ.stinespringOp,
    fun a => (φ.stinespringOp_adjoint_comp_stinespringStarAlgHom_comp a).symm,
    φ.norm_stinespringOp_sq_eq_norm_one,
    φ.topologicalClosure_span_stinespring_eq_top⟩

end Unital

section Uniqueness

variable {A : Type u} {H : Type v} {K : Type w}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

section NonUnital

variable (φ : A →CP (H →L[ℂ] H)) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- Linear map `φ.PreStinespring →ₗ[ℂ] K` sending `[a ⊗ₜ ξ]` to `π a (V ξ)` for any pair
`(π, V)`. -/
private def stinespringLiftPre : φ.PreStinespring →ₗ[ℂ] K :=
  (TensorProduct.lift
    { toFun a := ((π a).comp V).toLinearMap
      map_add' a b := by ext ξ; simp
      map_smul' c a := by ext ξ; simp }).comp φ.toPreStinespring.symm.toLinearMap

private theorem stinespringLiftPre_tmul (a : A) (ξ : H) :
    φ.stinespringLiftPre π V (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ)) = π a (V ξ) :=
  rfl

private theorem norm_stinespringLiftPre_eq
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V)) (x : φ.PreStinespring) :
    ‖φ.stinespringLiftPre π V x‖ = ‖(x : φ.Stinespring)‖ := by
  obtain ⟨k, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq x.ofPreStinespring
  have hx' : x = ∑ i, φ.toPreStinespring (a i ⊗ₜ[ℂ] ξ i) := PreStinespring.ext (by simpa using hx)
  have hsq : ‖φ.stinespringLiftPre π V x‖ ^ 2 = ‖(x : φ.Stinespring)‖ ^ 2 := by
    rw [Completion.norm_coe, φ.preStinespring_norm_sq_re,
      ← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, hx']
    simp only [map_sum, stinespringLiftPre_tmul, inner_sum, sum_inner, preStinespring_inner_tmul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hφ (star (a j) * a i), map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
    simp [ContinuousLinearMap.adjoint_inner_right]
  nlinarith [norm_nonneg (φ.stinespringLiftPre π V x), norm_nonneg (x : φ.Stinespring)]

private theorem denseRange_stinespringLiftPre
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    DenseRange (φ.stinespringLiftPre π V) := by
  have hrange :
      Set.range (φ.stinespringLiftPre π V) =
        (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)} : Set K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq x.ofPreStinespring
      have hx' : x = ∑ i, φ.toPreStinespring (a i ⊗ₜ[ℂ] ξ i) :=
        PreStinespring.ext (by simpa using hx)
      rw [hx', map_sum (φ.stinespringLiftPre π V)]
      exact Submodule.sum_mem _ fun i _ => by
        rw [stinespringLiftPre_tmul]
        exact Submodule.subset_span ⟨a i, ξ i, rfl⟩
    · intro hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, ξ, rfl⟩
        exact ⟨φ.toPreStinespring (a ⊗ₜ[ℂ] ξ), rfl⟩
      · exact ⟨0, map_zero _⟩
      · rintro _ _ _ _ ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
        exact ⟨x₁ + x₂, map_add _ x₁ x₂⟩
      · rintro c _ _ ⟨x, rfl⟩
        exact ⟨c • x, map_smul _ c x⟩
  rw [DenseRange, hrange]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hmin

/-- The canonical unitary equivalence `φ.Stinespring ≃ₗᵢ[ℂ] K` between the canonical Stinespring
space and any minimal Stinespring dilation `(K, π, V)` of `φ`. -/
def stinespringEquiv
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    φ.Stinespring ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ φ.PreStinespring).extendOfIsometry
    Completion.toComplL.toLinearMap
    (φ.stinespringLiftPre π V)
    Completion.denseRange_coe
    (φ.denseRange_stinespringLiftPre π V hmin)
    (φ.norm_stinespringLiftPre_eq π V hφ)

@[simp]
theorem stinespringEquiv_stinespringTmul
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (ξ : H) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringTmul a ξ) = π a (V ξ) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ))

@[simp]
theorem stinespringEquiv_intertwines
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (w : φ.Stinespring) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringNonUnitalStarAlgHom a w) =
      π a (φ.stinespringEquiv π V hφ hmin w) := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((φ.stinespringEquiv π V hφ hmin).continuous.comp
        (φ.stinespringNonUnitalStarAlgHom a).continuous)
      ((π a).continuous.comp (φ.stinespringEquiv π V hφ hmin).continuous)
  | ih x =>
    obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul b ξ =>
      rw [← stinespringTmul_def, stinespringNonUnitalStarAlgHom_apply_stinespringTmul]
      simp
    | add t₁ t₂ ht₁ ht₂ =>
      simp [map_add, UniformSpace.Completion.coe_add, ht₁, ht₂]

@[simp]
theorem stinespringEquiv_stinespringOp
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (ξ : H) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringOp ξ) = V ξ := by
  set U := φ.stinespringEquiv π V hφ hmin
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hπ : π.IsNondegenerate := by
    rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense,
      Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← hmin]
    refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
    rintro _ ⟨a, η, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, V η, rfl⟩
  have h₁ :
      Tendsto (fun e : A => U (φ.stinespringTmul e ξ))
        (CStarAlgebra.approximateUnit A) (𝓝 (U (φ.stinespringOp ξ))) :=
    U.continuous.continuousAt.tendsto.comp (φ.tendsto_stinespringTmul_approximateUnit ξ)
  have h₂ :
      Tendsto (fun e : A => π e (V ξ)) (CStarAlgebra.approximateUnit A) (𝓝 (V ξ)) :=
    (NonUnitalStarAlgHom.isNondegenerate_iff_tendsto hl).mp hπ (V ξ)
  exact tendsto_nhds_unique (by simpa [U] using h₁) h₂

/-- The inverse Stinespring unitary intertwines the given representation with the canonical one. -/
@[simp]
theorem stinespringEquiv_symm_intertwines
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (y : K) :
    (φ.stinespringEquiv π V hφ hmin).symm (π a y) =
      φ.stinespringNonUnitalStarAlgHom a ((φ.stinespringEquiv π V hφ hmin).symm y) := by
  apply (φ.stinespringEquiv π V hφ hmin).injective
  simp

/-- The inverse Stinespring unitary carries `V` back to `φ.stinespringOp`. -/
@[simp]
theorem stinespringEquiv_symm_stinespringOp
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (ξ : H) :
    (φ.stinespringEquiv π V hφ hmin).symm (V ξ) = φ.stinespringOp ξ := by
  apply (φ.stinespringEquiv π V hφ hmin).injective
  simp

/-- **Unitary uniqueness of minimal Stinespring dilations** (nonunital form): there is a unique
unitary `U : φ.Stinespring ≃ₗᵢ[ℂ] K` carrying `φ.stinespringOp` to `V` and intertwining
`φ.stinespringNonUnitalStarAlgHom` with `π`. -/
theorem existsUnique_stinespringEquiv
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K,
      (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : A) (w : φ.Stinespring), U (φ.stinespringNonUnitalStarAlgHom a w) = π a (U w) := by
  refine ⟨φ.stinespringEquiv π V hφ hmin,
    ⟨φ.stinespringEquiv_stinespringOp π V hφ hmin,
      φ.stinespringEquiv_intertwines π V hφ hmin⟩, ?_⟩
  rintro U ⟨hUop, hUinter⟩
  ext w
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq U.continuous (φ.stinespringEquiv π V hφ hmin).continuous
  | ih x =>
    obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x := ⟨x.1, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a ξ =>
      have htmul : (φ.toPreStinespring (a ⊗ₜ[ℂ] ξ) : φ.Stinespring) =
          φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOp ξ) :=
        (φ.stinespringNonUnitalStarAlgHom_apply_stinespringOp a ξ).symm
      rw [htmul, hUinter, hUop, φ.stinespringEquiv_intertwines, φ.stinespringEquiv_stinespringOp]
    | add t₁ t₂ ht₁ ht₂ =>
      simp [map_add, UniformSpace.Completion.coe_add, ht₁, ht₂]

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (φ : D →CP (H →L[ℂ] H)) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- **Unitary uniqueness of minimal Stinespring dilations** (unital form). -/
theorem existsUnique_stinespringEquiv_unital
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K,
      (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : D) (w : φ.Stinespring), U (φ.stinespringStarAlgHom a w) = π a (U w) :=
  φ.existsUnique_stinespringEquiv π.toNonUnitalStarAlgHom V hφ hmin

end Unital

end Uniqueness

end Stinespring

end CompletelyPositiveMap
