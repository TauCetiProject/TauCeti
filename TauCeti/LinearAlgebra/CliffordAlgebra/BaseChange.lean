/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Clifford involutions, the even part, and extension of scalars

This file records the structural properties of Mathlib's `CliffordAlgebra.ofBaseChangeAux`, the
canonical map from a Clifford algebra into the Clifford algebra after extension of scalars: it
commutes with the grade involution and with Clifford conjugation, and it preserves the even
subalgebra. These are the compatibilities needed to transport twisted-conjugation actions and the
Lipschitz, Pin, and Spin subgroups along scalar extensions. It also transports isomorphisms of
the coefficient algebra, such as complex conjugation of `ℂ` over `ℝ`, to the Clifford algebra after
extension of scalars.

## Main results

* `CliffordAlgebra.ofBaseChangeAux_involute` proves naturality of the grade involution.
* `CliffordAlgebra.ofBaseChangeAux_reverse` proves naturality of Clifford reversal.
* `CliffordAlgebra.ofBaseChangeAux_star` proves naturality of Clifford conjugation.
* `CliffordAlgebra.ofBaseChangeAux_mem_even` proves preservation of the even subalgebra.
* `CliffordAlgebra.ofBaseChangeAux_injective` proves injectivity for faithful flat extensions.
* `CliffordAlgebra.ofBaseChangeAux_baseChange` identifies direct and successive scalar extension.
* `CliffordAlgebra.baseChange_ringHom_ext`: a ring homomorphism out of `Cℓ(A ⊗ M)` is determined
  by its values on the scalars of `A` and on the vectors `ι (1 ⊗ₜ v)`.
* `CliffordAlgebra.baseChangeCongr` is the isomorphism `Cℓ(A ⊗ M) ≃ Cℓ(B ⊗ M)` induced by an
  isomorphism of coefficient algebras `A ≃ₐ[R] B`; `CliffordAlgebra.baseChangeCongr_unique`
  characterizes it, and it commutes with the grade involution, reversal and Clifford conjugation.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with the grade
involution. -/
@[simp]
theorem ofBaseChangeAux_involute (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (involute x) =
      involute (Q := Q.baseChange A) (ofBaseChangeAux A Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with Clifford
reversal. -/
@[simp]
theorem ofBaseChangeAux_reverse (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (reverse x) =
      reverse (Q := Q.baseChange A) (ofBaseChangeAux A Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [reverse.commutes, (ofBaseChangeAux A Q).commutes]
      rw [IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A)),
        reverse.commutes]
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with Clifford
conjugation. -/
@[simp]
theorem ofBaseChangeAux_star (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (star x) = star (ofBaseChangeAux A Q x) := by
  simp only [star_def, ofBaseChangeAux_reverse, ofBaseChangeAux_involute]

/-- The canonical map to the Clifford algebra after extension of scalars sends even elements to
even elements. -/
theorem ofBaseChangeAux_mem_even (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx : x ∈ even Q) : ofBaseChangeAux A Q x ∈ even (Q.baseChange A) := by
  -- `even` is the subalgebra wrapper around degree zero of `evenOdd`, and `even_induction` is
  -- stated for the underlying graded submodule.
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      simpa using one_le_evenOdd_zero (Q.baseChange A)
        (Submodule.mem_one.mpr ⟨algebraMap R A r,
          (IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A)) r).symm⟩)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m n x _ hx =>
      simpa only [map_mul, ofBaseChangeAux_ι, zero_add] using
        SetLike.mul_mem_graded
          (ι_mul_ι_mem_evenOdd_zero (Q.baseChange A) (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n)) hx

/-- Under the identification `Cℓ(A ⊗ M) ≃ A ⊗ Cℓ(M)` of `CliffordAlgebra.toBaseChange`, the
canonical map to the Clifford algebra after extension of scalars sends `x` to `1 ⊗ x`. -/
@[simp]
theorem toBaseChange_ofBaseChangeAux (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    toBaseChange A Q (ofBaseChangeAux A Q x) = 1 ⊗ₜ x := by
  have h : ofBaseChange A Q (1 ⊗ₜ x) = ofBaseChangeAux A Q x :=
    (Algebra.TensorProduct.lift_tmul _ _ _ 1 x).trans (by rw [map_one, one_mul])
  rw [← h, toBaseChange_ofBaseChange]

/-- The canonical map to the Clifford algebra after extension of scalars is injective when the
extension is faithful and the Clifford algebra is flat; in particular, for every extension of
fields. -/
theorem ofBaseChangeAux_injective [FaithfulSMul R A] (Q : QuadraticForm R M)
    [Module.Flat R (CliffordAlgebra Q)] :
    Function.Injective (ofBaseChangeAux A Q) := by
  intro x y hxy
  apply Algebra.TensorProduct.includeRight_injective (A := A)
    (FaithfulSMul.algebraMap_injective R A)
  simpa only [toBaseChange_ofBaseChangeAux, Algebra.TensorProduct.includeRight_apply] using
    congrArg (toBaseChange A Q) hxy

/-- The canonical Clifford scalar-extension map commutes with a quadratic isometry. -/
@[simp]
theorem _root_.QuadraticMap.Isometry.ofBaseChangeAux_map {N : Type*} [AddCommGroup N] [Module R N]
    {Q : QuadraticForm R M} {Q' : QuadraticForm R N} (f : Q →qᵢ Q')
    (z : CliffordAlgebra Q) :
    ofBaseChangeAux A Q' (CliffordAlgebra.map f z) =
      CliffordAlgebra.map (f.baseChange A) (ofBaseChangeAux A Q z) := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | mul z w hz hw => simp only [map_mul, hz, hw]

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Transporting a direct scalar extension of a Clifford element along the canonical scalar-tower
isometry agrees with extending the element successively. -/
@[simp]
theorem ofBaseChangeAux_baseChange (Q : QuadraticForm R M) (z : CliffordAlgebra Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    CliffordAlgebra.map
        (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry
        (ofBaseChangeAux B Q z) =
      ofBaseChangeAux B (Q.baseChange A) (ofBaseChangeAux A Q z) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  induction z using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | mul z w hz hw => simp only [map_mul, hz, hw]

end ScalarTower

/-! ### Coefficient isomorphisms of a scalar extension -/

section Congr

variable {B : Type*} [CommRing B] [Algebra R B]

/-- Over `A`, the base-changed Clifford algebra is generated by the scalars `algebraMap A` and the
vectors `ι (1 ⊗ₜ v)` coming from `M`: ring homomorphisms out of it are determined by these
values. -/
theorem baseChange_ringHom_ext {S : Type*} [Semiring S] (Q : QuadraticForm R M)
    {f g : CliffordAlgebra (Q.baseChange A) →+* S}
    (halg : ∀ a : A, f (algebraMap A _ a) = g (algebraMap A _ a))
    (hι : ∀ v : M, f (ι (Q.baseChange A) (1 ⊗ₜ v)) = g (ι (Q.baseChange A) (1 ⊗ₜ v))) :
    f = g := by
  ext x
  induction x using CliffordAlgebra.induction with
  | algebraMap a => exact halg a
  | ι w =>
      induction w using TensorProduct.inductionOn with
      | tmul a v =>
          have h : ι (Q.baseChange A) (a ⊗ₜ v) =
              algebraMap A _ a * ι (Q.baseChange A) (1 ⊗ₜ v) := by
            rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [h, map_mul, map_mul, halg, hι]
      | add w w' hw hw' => simp only [map_add, hw, hw']
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- An `R`-algebra isomorphism `σ : A ≃ₐ[R] B` of coefficient algebras induces an isomorphism of
the base-changed Clifford algebras, acting by `σ` on the scalars and fixing the vectors of `M`.
It is `σ ⊗ id` transported along `CliffordAlgebra.equivBaseChange`. For complex conjugation of
`ℂ` over `ℝ` this is coefficientwise conjugation of the complexified Clifford algebra. -/
def baseChangeCongr (σ : A ≃ₐ[R] B) (Q : QuadraticForm R M) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[R] CliffordAlgebra (Q.baseChange B) :=
  ((equivBaseChange A Q).restrictScalars R).trans <|
    (Algebra.TensorProduct.congr σ AlgEquiv.refl).trans
      ((equivBaseChange B Q).symm.restrictScalars R)

variable (σ : A ≃ₐ[R] B) (Q : QuadraticForm R M)

/-- On the tensor carrier `A ⊗[R] Cℓ(Q)`, `CliffordAlgebra.baseChangeCongr` is `σ ⊗ id`. -/
@[simp]
theorem toBaseChange_baseChangeCongr (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange B Q (baseChangeCongr σ Q x) =
      Algebra.TensorProduct.congr σ AlgEquiv.refl (toBaseChange A Q x) := by
  simp [baseChangeCongr]

/-- `CliffordAlgebra.baseChangeCongr` applied to an element of the tensor carrier
`A ⊗[R] Cℓ(Q)`. -/
@[simp]
theorem baseChangeCongr_ofBaseChange (x : A ⊗[R] CliffordAlgebra Q) :
    baseChangeCongr σ Q (ofBaseChange A Q x) =
      ofBaseChange B Q (Algebra.TensorProduct.congr σ AlgEquiv.refl x) := by
  simp [baseChangeCongr]

/-- `CliffordAlgebra.baseChangeCongr` acts on scalars by `σ`. -/
@[simp]
theorem baseChangeCongr_algebraMap (a : A) :
    baseChangeCongr σ Q (algebraMap A _ a) = algebraMap B _ (σ a) := by
  simp [baseChangeCongr]

/-- `CliffordAlgebra.baseChangeCongr` acts on vectors by `σ ⊗ id`. -/
@[simp]
theorem baseChangeCongr_ι (w : A ⊗[R] M) :
    baseChangeCongr σ Q (ι (Q.baseChange A) w) =
      ι (Q.baseChange B) (LinearMap.rTensor M σ.toLinearMap w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a v => simp [baseChangeCongr]
  | add w w' hw hw' => simp only [map_add, hw, hw']

theorem baseChangeCongr_ι_tmul (a : A) (v : M) :
    baseChangeCongr σ Q (ι (Q.baseChange A) (a ⊗ₜ v)) = ι (Q.baseChange B) (σ a ⊗ₜ v) := by
  simp

/-- `CliffordAlgebra.baseChangeCongr` is `σ`-semilinear for the coefficient actions. -/
@[simp]
theorem baseChangeCongr_smul (a : A) (x : CliffordAlgebra (Q.baseChange A)) :
    baseChangeCongr σ Q (a • x) = σ a • baseChangeCongr σ Q x := by
  rw [Algebra.smul_def, map_mul, baseChangeCongr_algebraMap, ← Algebra.smul_def]

/-- `CliffordAlgebra.baseChangeCongr` fixes the image of the original Clifford algebra. -/
@[simp]
theorem baseChangeCongr_ofBaseChangeAux (x : CliffordAlgebra Q) :
    baseChangeCongr σ Q (ofBaseChangeAux A Q x) = ofBaseChangeAux B Q x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, AlgEquiv.commutes]
  | ι v => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- `CliffordAlgebra.baseChangeCongr` is the unique ring homomorphism acting by `σ` on scalars and
fixing the vectors `ι (1 ⊗ₜ v)`. -/
theorem baseChangeCongr_unique (f : CliffordAlgebra (Q.baseChange A) →+*
      CliffordAlgebra (Q.baseChange B))
    (halg : ∀ a : A, f (algebraMap A _ a) = algebraMap B _ (σ a))
    (hι : ∀ v : M, f (ι (Q.baseChange A) (1 ⊗ₜ v)) = ι (Q.baseChange B) (1 ⊗ₜ v)) :
    f = (baseChangeCongr σ Q : CliffordAlgebra (Q.baseChange A) →+*
      CliffordAlgebra (Q.baseChange B)) :=
  baseChange_ringHom_ext Q (fun a ↦ by simp [halg]) (fun v ↦ by simp [hι])

/-- The identity of the coefficients induces the identity of the base-changed Clifford
algebra. -/
@[simp]
theorem baseChangeCongr_refl :
    baseChangeCongr (AlgEquiv.refl : A ≃ₐ[R] A) Q = AlgEquiv.refl :=
  AlgEquiv.ext fun x ↦
    (congr($(baseChangeCongr_unique _ Q (RingHom.id _) (fun _ ↦ rfl) (fun _ ↦ rfl)) x)).symm

/-- `CliffordAlgebra.baseChangeCongr` is compatible with composition of coefficient
isomorphisms. -/
@[simp]
theorem baseChangeCongr_trans {C : Type*} [CommRing C] [Algebra R C] (τ : B ≃ₐ[R] C) :
    (baseChangeCongr σ Q).trans (baseChangeCongr τ Q) = baseChangeCongr (σ.trans τ) Q :=
  AlgEquiv.ext fun x ↦ congr($(baseChangeCongr_unique (σ.trans τ) Q
    ((baseChangeCongr σ Q).trans (baseChangeCongr τ Q) : _ →+* _)
    (fun a ↦ by simp) (fun v ↦ by simp)) x)

/-- The inverse of `CliffordAlgebra.baseChangeCongr` is induced by the inverse coefficient
isomorphism. -/
@[simp]
theorem baseChangeCongr_symm : (baseChangeCongr σ Q).symm = baseChangeCongr σ.symm Q := by
  ext x
  apply (baseChangeCongr σ Q).injective
  simp [← AlgEquiv.trans_apply]

/-- `CliffordAlgebra.baseChangeCongr` commutes with the grade involution. -/
@[simp]
theorem baseChangeCongr_involute (x : CliffordAlgebra (Q.baseChange A)) :
    baseChangeCongr σ Q (involute x) = involute (baseChangeCongr σ Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι w => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- `CliffordAlgebra.baseChangeCongr` commutes with reversal. -/
@[simp]
theorem baseChangeCongr_reverse (x : CliffordAlgebra (Q.baseChange A)) :
    baseChangeCongr σ Q (reverse x) = reverse (baseChangeCongr σ Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι w => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]

/-- `CliffordAlgebra.baseChangeCongr` commutes with Clifford conjugation. -/
@[simp]
theorem baseChangeCongr_star (x : CliffordAlgebra (Q.baseChange A)) :
    baseChangeCongr σ Q (star x) = star (baseChangeCongr σ Q x) := by
  simp only [star_def, baseChangeCongr_reverse, baseChangeCongr_involute]

end Congr

end CliffordAlgebra
