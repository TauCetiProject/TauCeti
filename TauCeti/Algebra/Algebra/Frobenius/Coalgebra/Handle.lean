/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra.Basic

/-!
# Converse perfectness, dual-basis expansions, and the handle element

This file completes the correspondence between perfect trace pairings and Frobenius coalgebras from
`TauCeti.Algebra.Algebra.Frobenius.Coalgebra.Basic`, and develops dual-basis and handle identities.

For a unital `R`-algebra `A` with `Coalgebra.IsFrobenius R A`, the pairing `(a, b) ↦ ε (a * b)` is
perfect (`Coalgebra.IsFrobenius.isPerfPair_mul_compr₂_counit`), without associativity or
commutativity of `A`. When `A` is commutative, every Frobenius coalgebra is cocommutative
(`Coalgebra.IsFrobenius.instIsCocomm`), and when `A` is also finite and projective over `R`,
`TauCeti.perfPairTraceEquivFrobeniusCoalgebra` packages reconstruction and counit extraction as a
bijection between perfect traces and Frobenius coalgebra structures on `A`.

The **handle operator** `Coalgebra.handleOp R A = mul' ∘ comul` and **handle element**
`Coalgebra.handleElem R A = mul' (comul 1)` represent attaching a handle in 2D TQFT and foam
evaluation. On an associative Frobenius algebra, `handleOp R A` acts by multiplication on either
side by the central element `handleElem R A`; on a commutative Frobenius algebra with a finite basis
of size `n`, `handleElem R A` is the sum of dual-basis products and its counit is `n`.

## Main definitions

* `TauCeti.perfPairTraceEquivFrobeniusCoalgebra`: bijection between perfect trace functionals and
  Frobenius coalgebra structures on a finite projective commutative `R`-algebra.
* `Coalgebra.handleOp`, `Coalgebra.handleElem`: `mul' ∘ comul` and `mul' (comul 1)`.

## Main results

* `Coalgebra.IsFrobenius.isPerfPair_mul_compr₂_counit`, `Coalgebra.IsFrobenius.instIsCocomm`.
* `Coalgebra.IsFrobenius.comul_eq_sum_traceDualBasis`,
  `Coalgebra.IsFrobenius.comul_one_eq_sum_traceDualBasis`.
* `Coalgebra.handleOp_apply_eq_mul_handleElem`, `Coalgebra.commute_handleElem`,
  `Coalgebra.iterate_handleOp_apply`, `Coalgebra.handleElem_eq_sum_mul_traceDualBasis`,
  `Coalgebra.counit_handleElem`.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, §§2.3, 3.3.
* F. Goertz, L. Marino, P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  `arXiv:2602.11120v1`, §§2–3.
-/

public section

noncomputable section

open TensorProduct

/-! ### Coproduct-multiplication identities and converse perfectness -/

namespace Coalgebra.IsFrobenius

section CoalgebraStruct

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]

/-- Evaluating `Coalgebra.IsFrobenius.left` on `a ⊗ₜ b` multiplies the second leg of `comul a` on
the right by `b`. -/
@[simp] theorem left_tmul (a b : A) :
    left R A (a ⊗ₜ[R] b) = (LinearMap.mulRight R b).lTensor A (Coalgebra.comul (R := R) a) := by
  simp only [left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn <;> simp_all [add_tmul]

/-- Evaluating `Coalgebra.IsFrobenius.right` on `a ⊗ₜ b` multiplies the first leg of `comul b` on
the left by `a`. -/
@[simp] theorem right_tmul (a b : A) :
    right R A (a ⊗ₜ[R] b) = (LinearMap.mulLeft R a).rTensor A (Coalgebra.comul (R := R) b) := by
  simp only [right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul]
  induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn <;> simp_all [tmul_add]

end CoalgebraStruct

section NonUnitalNonAssocSemiring

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- Multiplying the first leg of the coproduct on the left multiplies its input on the left. -/
theorem comul_mul_left (a b : A) :
    Coalgebra.comul (R := R) (a * b) = (LinearMap.mulLeft R a).rTensor A (Coalgebra.comul b) := by
  simpa using (LinearMap.congr_fun (right_eq_comul_comp_mul' (R := R) (A := A)) (a ⊗ₜ[R] b)).symm

/-- Multiplying the second leg of the coproduct on the right multiplies its input on the right. -/
theorem comul_mul_right (a b : A) :
    Coalgebra.comul (R := R) (a * b) = (LinearMap.mulRight R b).lTensor A (Coalgebra.comul a) := by
  simpa using (LinearMap.congr_fun (left_eq_comul_comp_mul' (R := R) (A := A)) (a ⊗ₜ[R] b)).symm

end NonUnitalNonAssocSemiring

section NonAssocSemiringStruct

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A] [Coalgebra.IsFrobenius R A]

/-- In a unital Frobenius algebra-coalgebra, `comul a` is obtained from `comul 1` by multiplying
the first tensor factor on the left by `a`. -/
theorem comul_eq_rTensor_mulLeft_comul_one (a : A) :
    Coalgebra.comul (R := R) a = (LinearMap.mulLeft R a).rTensor A (Coalgebra.comul (1 : A)) := by
  simpa using LinearMap.congr_fun (left_eq_right (R := R) (A := A)) (a ⊗ₜ[R] 1)

/-- In a unital Frobenius algebra-coalgebra, `comul a` is obtained from `comul 1` by multiplying
the second tensor factor on the right by `a`. -/
theorem comul_eq_lTensor_mulRight_comul_one (a : A) :
    Coalgebra.comul (R := R) a = (LinearMap.mulRight R a).lTensor A (Coalgebra.comul (1 : A)) := by
  simpa using (LinearMap.congr_fun (left_eq_right (R := R) (A := A)) (1 ⊗ₜ[R] a)).symm

end NonAssocSemiringStruct

section NonAssocSemiring

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- **The trace pairing of a unital Frobenius coalgebra is perfect.** No associativity or
commutativity assumption on `A` is needed. -/
instance isPerfPair_mul_compr₂_counit :
    ((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).IsPerfPair :=
  .of_bijective _ compr₂_mul_counit_bijective

/-- Right-hand counterpart of `Coalgebra.IsFrobenius.compr₂_mul_counit_bijective`: the flipped
multiplication-counit pairing `b ↦ (a ↦ ε (a * b))` of a unital Frobenius coalgebra is bijective. -/
theorem flip_compr₂_mul_counit_bijective :
    Function.Bijective (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).flip) :=
  LinearMap.IsPerfPair.bijective_right _

/-- Contracting the first leg of `comul a` against `x ↦ counit (b * x)` produces `b * a`. -/
theorem lid_rTensor_counit_mulLeft_comul (b a : A) :
    (_root_.TensorProduct.lid R A)
      (((Coalgebra.counit (R := R) ∘ₗ LinearMap.mulLeft R b).rTensor A)
        (Coalgebra.comul (R := R) a)) = b * a := by
  simpa [LinearMap.rTensor_comp] using congrArg ((_root_.TensorProduct.lid R A).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R)).rTensor A) (comul_mul_left (R := R) b a).symm

/-- Two elements of `A ⊗[R] A` in a unital Frobenius coalgebra are equal as soon as they agree
after contracting their first tensor factor against `x ↦ counit (b * x)` for every `b : A`. -/
theorem tensor_eq_of_forall_lid_rTensor_counit_mulLeft {z₁ z₂ : A ⊗[R] A}
    (hz : ∀ b : A, (_root_.TensorProduct.lid R A)
        (((Coalgebra.counit (R := R) ∘ₗ LinearMap.mulLeft R b).rTensor A) z₁) =
      (_root_.TensorProduct.lid R A)
        (((Coalgebra.counit (R := R) ∘ₗ LinearMap.mulLeft R b).rTensor A) z₂)) :
    z₁ = z₂ := by
  let ε : Module.Dual R A := Coalgebra.counit
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (Coalgebra.comul (R := R) (1 : A))
  have hid : (LinearMap.id : A →ₗ[R] A) =
      ∑ x ∈ S, LinearMap.smulRight (ε ∘ₗ LinearMap.mulLeft R x.2) x.1 := LinearMap.ext fun u => by
    simpa [ε, hS, sum_tmul] using congrArg ((_root_.TensorProduct.rid R A).toLinearMap ∘ₗ
      ε.lTensor A) (comul_eq_lTensor_mulRight_comul_one (R := R) u)
  have hrsum (g : A × A → A →ₗ[R] A) : (∑ x ∈ S, g x).rTensor A = ∑ x ∈ S, (g x).rTensor A :=
    TensorProduct.ext' fun _ _ => by simp [LinearMap.sum_apply, sum_tmul]
  have hsmul (φ : A →ₗ[R] R) (w : A) : (LinearMap.smulRight φ w).rTensor A =
      TensorProduct.mk R A A w ∘ₗ (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ φ.rTensor A :=
    TensorProduct.ext' fun _ _ => by simp [smul_tmul]
  have hexpand (z : A ⊗[R] A) : z = ∑ x ∈ S, x.1 ⊗ₜ[R]
      (_root_.TensorProduct.lid R A) (((ε ∘ₗ LinearMap.mulLeft R x.2).rTensor A) z) := by
    have hz0 : z = (LinearMap.id : A →ₗ[R] A).rTensor A z := by simp
    conv_lhs => rw [hz0, hid, hrsum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by rw [hsmul]; rfl
  rw [hexpand z₁, hexpand z₂]
  exact Finset.sum_congr rfl fun x _ => by rw [hz x.2]

end NonAssocSemiring

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- **A commutative Frobenius coalgebra is cocommutative.** -/
instance instIsCocomm : Coalgebra.IsCocomm R A where
  comm_comp_comul := by
    ext a; let ε : A →ₗ[R] R := Coalgebra.counit
    refine ε.traceTensorEquiv.injective (TensorProduct.ext' fun x y => ?_)
    have hcomm (t : A ⊗[R] A) :
        ε.traceTensorEquiv (TensorProduct.comm R A A t) (x ⊗ₜ[R] y) =
          ε.traceTensorEquiv t (y ⊗ₜ[R] x) := by
      induction t using TensorProduct.inductionOn <;> simp_all [mul_comm]
    have htrace := ε.traceTensorEquiv_comul_of_isFrobenius ‹_› rfl ‹_› a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcomm, htrace, mul_comm y x]

end CommSemiring

end Coalgebra.IsFrobenius

/-! ### Equivalence between perfect traces and Frobenius coalgebras -/

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The Frobenius coalgebra reconstructed from a perfect trace on a finite projective commutative
algebra is cocommutative. -/
theorem frobeniusCoalgebra_isCocomm [Module.Finite R A] [Module.Projective R A]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] :
    letI := ε.frobeniusCoalgebra; Coalgebra.IsCocomm R A := by
  let := ε.frobeniusCoalgebra; have := ε.frobeniusCoalgebra_isFrobenius; infer_instance

variable (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- Taking the trace-dual basis twice on a commutative algebra recovers the original basis. -/
@[simp] theorem traceDualBasis_traceDualBasis {ι : Type*} [Finite ι] (b : Module.Basis ι R A) :
    traceDualBasis ε (traceDualBasis ε b) = b := by
  ext i : 1; apply (traceDualBasis ε b).repr.injective; ext j
  rw [traceDualBasis_repr, traceDualBasis_mul, traceDualBasis_repr, mul_comm, traceDualBasis_repr]

/-- Expansion of an algebra element in the trace-dual basis, with coefficients given by trace
pairings against the primal basis. -/
theorem sum_apply_mul_smul_traceDualBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (a : A) : ∑ i, ε (a * b i) • traceDualBasis ε b i = a := by
  simpa only [traceDualBasis_repr] using (traceDualBasis ε b).sum_repr a

/-- Expansion of an algebra element in the primal basis, with coefficients given by trace pairings
against the trace-dual basis. -/
theorem sum_traceDualBasis_mul_smul {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (a : A) : ∑ i, ε (traceDualBasis ε b i * a) • b i = a := by
  simpa only [traceDualBasis_mul] using b.sum_repr a

end LinearMap

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- **Perfect traces correspond bijectively to Frobenius coalgebras.** On a finite projective
commutative `R`-algebra `A`, reconstructing `ε.frobeniusCoalgebra` from a perfect trace `ε` and
taking the counit of a Frobenius coalgebra are mutually inverse bijections. -/
def perfPairTraceEquivFrobeniusCoalgebra :
    {ε : A →ₗ[R] R // ((LinearMap.mul R A).compr₂ ε).IsPerfPair} ≃
      {c : Coalgebra R A // letI := c; Coalgebra.IsFrobenius R A} where
  toFun ε := letI := ε.2; ⟨ε.1.frobeniusCoalgebra, ε.1.frobeniusCoalgebra_isFrobenius⟩
  invFun c := letI := c.1; letI := c.2; ⟨c.1.counit, inferInstance⟩
  left_inv ε := Subtype.ext <| by let := ε.2; exact ε.1.frobeniusCoalgebra_counit
  right_inv c := Subtype.ext <| by
    let := c.1; let := c.2; exact c.1.counit.frobeniusCoalgebra_eq c.1 rfl c.2

@[simp] theorem perfPairTraceEquivFrobeniusCoalgebra_apply_coe
    (ε : {ε : A →ₗ[R] R // ((LinearMap.mul R A).compr₂ ε).IsPerfPair}) :
    (perfPairTraceEquivFrobeniusCoalgebra R A ε : Coalgebra R A) =
      (letI := ε.2; ε.1.frobeniusCoalgebra) := (rfl)

@[simp] theorem perfPairTraceEquivFrobeniusCoalgebra_symm_apply_coe
    (c : {c : Coalgebra R A // letI := c; Coalgebra.IsFrobenius R A}) :
    ((perfPairTraceEquivFrobeniusCoalgebra R A).symm c : A →ₗ[R] R) = c.1.counit := (rfl)

end TauCeti

namespace Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- Dual-basis formula for the coproduct of any commutative Frobenius coalgebra, with the input
multiplying the second leg. -/
theorem comul_eq_sum_traceDualBasis {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) (a : A) :
    Coalgebra.comul (R := R) a =
      ∑ i, b i ⊗ₜ[R] (LinearMap.traceDualBasis Coalgebra.counit b i * a) := by
  have hc := congrArg (fun c : Coalgebra R A => c.comul)
    ((Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra_eq ‹_› rfl ‹_›)
  exact hc ▸ (Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra_comul_eq_sum b a

/-- Dual-basis formula for `comul 1` in any commutative Frobenius coalgebra: the Casimir /
diagonal tensor `∑ i, b i ⊗ b^* i` is independent of the choice of finite basis `b`. -/
theorem comul_one_eq_sum_traceDualBasis {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    Coalgebra.comul (R := R) (1 : A) =
      ∑ i, b i ⊗ₜ[R] LinearMap.traceDualBasis Coalgebra.counit b i := by
  simpa using comul_eq_sum_traceDualBasis b (1 : A)

/-- Dual-basis formula for the coproduct of any commutative Frobenius coalgebra, with the input
multiplying the first leg. -/
theorem comul_eq_sum_mul_traceDualBasis_left {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (a : A) :
    Coalgebra.comul (R := R) a =
      ∑ i, (a * b i) ⊗ₜ[R] LinearMap.traceDualBasis Coalgebra.counit b i := by
  rw [comul_eq_rTensor_mulLeft_comul_one (R := R) a, comul_one_eq_sum_traceDualBasis b, map_sum]
  simp

end Coalgebra.IsFrobenius

/-! ### The handle operator and handle element -/

namespace Coalgebra

section NonUnital

variable (R A : Type*) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]

/-- The **handle operator** (or window operator) `mul' ∘ comul` of an algebra-coalgebra, sending
`a` to the product of the legs of `comul a`. In 2D TQFT and foam evaluation it represents inserting
a handle (genus-one tube) on a sheet. -/
def handleOp : A →ₗ[R] A := LinearMap.mul' R A ∘ₗ Coalgebra.comul

theorem handleOp_def : handleOp R A = LinearMap.mul' R A ∘ₗ Coalgebra.comul := (rfl)

theorem handleOp_apply (a : A) :
    handleOp R A a = LinearMap.mul' R A (Coalgebra.comul (R := R) a) := (rfl)

end NonUnital

section Unital

variable (R A : Type*) [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]

/-- The **handle element** (or Euler / characteristic element) `m (Δ 1)` of a unital
algebra-coalgebra, obtained by evaluating `Coalgebra.handleOp` at `1`. -/
def handleElem : A := handleOp R A 1

theorem handleElem_def : handleElem R A = LinearMap.mul' R A (Coalgebra.comul (R := R) 1) := (rfl)

@[simp] theorem handleOp_one : handleOp R A 1 = handleElem R A := (rfl)

end Unital

/-- On the base commutative semiring `R` with its canonical coalgebra structure, the handle
operator is the identity. -/
@[simp] theorem handleOp_self (R : Type*) [CommSemiring R] : handleOp R R = LinearMap.id := by
  ext; simp [handleOp]

/-- On the base commutative semiring `R` with its canonical coalgebra structure, the handle element
is `1`. -/
@[simp] theorem handleElem_self (R : Type*) [CommSemiring R] : handleElem R R = 1 := by
  simp [handleElem]

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A] [Coalgebra.IsFrobenius R A]

/-- In an associative Frobenius algebra-coalgebra, the handle operator acts by right multiplication
by the handle element. -/
theorem handleOp_apply_eq_mul_handleElem (a : A) : handleOp R A a = a * handleElem R A := by
  rw [handleElem, handleOp_apply, handleOp_apply,
    IsFrobenius.comul_eq_rTensor_mulLeft_comul_one (R := R) a]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn <;>
    simp_all [mul_assoc, mul_add]

/-- In an associative Frobenius algebra-coalgebra, the handle operator acts by left multiplication
by the handle element. -/
theorem handleOp_apply_eq_handleElem_mul (a : A) : handleOp R A a = handleElem R A * a := by
  rw [handleElem, handleOp_apply, handleOp_apply,
    IsFrobenius.comul_eq_lTensor_mulRight_comul_one (R := R) a]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn <;>
    simp_all [mul_assoc, add_mul]

/-- **The handle element of an associative Frobenius algebra-coalgebra is central.** No
commutativity assumption on `A` is needed. -/
theorem commute_handleElem (a : A) : Commute (handleElem R A) a :=
  (handleOp_apply_eq_handleElem_mul a).symm.trans (handleOp_apply_eq_mul_handleElem a)

/-- The handle element belongs to the center of any associative Frobenius algebra-coalgebra. -/
theorem handleElem_mem_center : handleElem R A ∈ Subsemiring.center A :=
  Subsemiring.mem_center_iff.mpr fun a => (commute_handleElem a).symm.eq

/-- Iterating the handle operator `g` times multiplies on the right by the `g`-th power of the
handle element (attaching `g` handles). -/
@[simp] theorem iterate_handleOp_apply (g : ℕ) (a : A) :
    (handleOp R A)^[g] a = a * handleElem R A ^ g := by
  induction g generalizing a with
  | zero => simp
  | succ g ih =>
    rw [Function.iterate_succ_apply, handleOp_apply_eq_mul_handleElem, ih, mul_assoc, ← pow_succ']

/-- Evaluating the `g`-th iterate of the handle operator at `1` gives `handleElem R A ^ g`. -/
theorem iterate_handleOp_one (g : ℕ) : (handleOp R A)^[g] 1 = handleElem R A ^ g := by simp

end Semiring

section CommSemiring

/-- Dual-basis expansion of the handle element: `handleElem R A = ∑ i, b i * b^* i` for every
finite `R`-basis `b` of `A`. -/
theorem handleElem_eq_sum_mul_traceDualBasis {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Coalgebra R A] [Coalgebra.IsFrobenius R A] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) :
    handleElem R A = ∑ i, b i * LinearMap.traceDualBasis Coalgebra.counit b i := by
  rw [handleElem, handleOp_apply, IsFrobenius.comul_one_eq_sum_traceDualBasis b, map_sum]; simp

/-- **Torus evaluation**: if a commutative Frobenius coalgebra `A` has a finite `R`-basis indexed
by `ι`, then `counit (handleElem R A)` equals `(Fintype.card ι : R)`. -/
theorem counit_handleElem {R A : Type*} [CommSemiring R] [CommSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [Coalgebra R A] [Coalgebra.IsFrobenius R A]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    Coalgebra.counit (R := R) (handleElem R A) = Fintype.card ι := by
  let _ : Algebra R A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  rw [handleElem_eq_sum_mul_traceDualBasis b, map_sum]
  simp [mul_comm (b _), LinearMap.traceDualBasis_mul]

end CommSemiring

end Coalgebra
