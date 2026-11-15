/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Clifford involutions, the even part, and extension of scalars

This file records the structural properties of Mathlib's `CliffordAlgebra.ofBaseChangeAux`, the
canonical map from a Clifford algebra into the Clifford algebra after extension of scalars: it
commutes with the grade involution and with Clifford conjugation, and it preserves the even
subalgebra. These are the compatibilities needed to transport twisted-conjugation actions and the
Lipschitz, Pin, and Spin subgroups along scalar extensions. It also transports isomorphisms of
the coefficient algebra, such as complex conjugation of `ℂ` over `ℝ`, to the Clifford algebra after
extension of scalars. On the tensor carrier `A ⊗[R] Cℓ(M, Q)` of Mathlib's
`CliffordAlgebra.equivBaseChange`, it records the inverse-map forms of Mathlib's involution and
reversal laws for `CliffordAlgebra.toBaseChange`, and identifies the `ℤ/2`-grading of
`Cℓ(A ⊗ M, Q_A)` with the scalar extension of the grading of `Cℓ(M, Q)`.

Finally, for any not-necessarily-commutative `A`-algebra `B` forming a scalar tower `R → A → B`,
composing Mathlib's scalar-extension adjunction `AlgHom.liftEquiv` with
`CliffordAlgebra.toBaseChange` (the forward direction of `CliffordAlgebra.equivBaseChange`) extends
every `R`-algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[R] B` to a unique `A`-algebra
homomorphism `ρ.cliffordBaseChange A : CliffordAlgebra (Q.baseChange A) →ₐ[A] B` restricting to `ρ`
along `CliffordAlgebra.ofBaseChangeAux A Q`.

## Main definitions

* `CliffordAlgebra.baseChangeCongr`: the isomorphism `Cℓ(A ⊗ M) ≃ Cℓ(B ⊗ M)` induced by an
  isomorphism of coefficient algebras `A ≃ₐ[R] B`.
* `AlgHom.cliffordBaseChange`: the `A`-linear extension `CliffordAlgebra (Q.baseChange A) →ₐ[A] B`
  of `ρ : CliffordAlgebra Q →ₐ[R] B`.
* `AlgHom.cliffordBaseChangeEquiv`: the equivalence
  `(CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B)` inverse to
  restriction along `CliffordAlgebra.ofBaseChangeAux A Q`.

## Main results

* `CliffordAlgebra.ofBaseChangeAux_involute` proves naturality of the grade involution.
* `CliffordAlgebra.ofBaseChangeAux_reverse` proves naturality of Clifford reversal.
* `CliffordAlgebra.ofBaseChangeAux_star` proves naturality of Clifford conjugation.
* `CliffordAlgebra.ofBaseChangeAux_mem_even` proves preservation of the even subalgebra.
* `CliffordAlgebra.ofBaseChangeAux_injective` proves injectivity for faithful flat extensions.
* `CliffordAlgebra.ofBaseChangeAux_baseChange` identifies direct and successive scalar extension.
* `CliffordAlgebra.baseChange_ringHom_ext`, `CliffordAlgebra.baseChange_hom_ext_iff`: homomorphisms
  out of `Cℓ(A ⊗ M)` are determined by their values on the vectors `ι (1 ⊗ₜ v)` (together with the
  scalars of `A` for bare ring homomorphisms).
* `CliffordAlgebra.baseChangeCongr_unique` characterizes `CliffordAlgebra.baseChangeCongr`, and it
  commutes with the grade involution, reversal and Clifford conjugation.
* `CliffordAlgebra.ofBaseChange_map_involute` and `CliffordAlgebra.ofBaseChange_map_reverse`:
  under `CliffordAlgebra.ofBaseChange`, the grade involution and reversal of the right tensor
  factor become those of `Cℓ(A ⊗ M, Q_A)`.
* `CliffordAlgebra.mem_baseChange_evenOdd_zero_iff` and
  `CliffordAlgebra.mem_baseChange_evenOdd_one_iff`: on the tensor carrier, the scalar extensions
  of the even and odd parts are the `±1`-eigenspaces of the grade involution of the right factor.
* `CliffordAlgebra.toBaseChange_mem_baseChange_evenOdd_iff` and
  `CliffordAlgebra.ofBaseChange_mem_evenOdd_iff`: `CliffordAlgebra.equivBaseChange` and its
  inverse match the parity-`i` part of `Cℓ(A ⊗ M, Q_A)` with the scalar extension of the
  parity-`i` part of `Cℓ(M, Q)`.
* `AlgHom.cliffordBaseChange_ofBaseChangeAux`,
  `AlgHom.cliffordBaseChange_restrictScalars_comp_ofBaseChangeAux`: restricting
  `ρ.cliffordBaseChange A` along `ofBaseChangeAux A Q` recovers `ρ`.
* `AlgHom.cliffordBaseChange_ι_tmul`, `AlgHom.cliffordBaseChange_ι_one_tmul`: the action of
  `ρ.cliffordBaseChange A` on `ι (Q.baseChange A) (a ⊗ₜ v)` and `ι (Q.baseChange A) (1 ⊗ₜ v)`.
* `AlgHom.eq_cliffordBaseChange_iff`, `AlgHom.cliffordBaseChange_eq_lift`: uniqueness and
  `Algebra.TensorProduct.lift` factorization of `ρ.cliffordBaseChange A`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- A pure tensor generator is the scalar multiple of the corresponding generator under the
canonical Clifford scalar-extension map. -/
theorem ι_baseChange_tmul_eq_smul_ofBaseChangeAux (Q : QuadraticForm R M) (a : A) (v : M) :
    ι (Q.baseChange A) (a ⊗ₜ v) = a • ofBaseChangeAux A Q (ι Q v) := by
  rw [ofBaseChangeAux_ι, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

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
fields with `2` invertible in the base field. -/
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

/-! ### The tensor carrier: inverse-map forms and the grading -/

section TensorCarrier

variable (Q : QuadraticForm R M)

/-- The inverse-map form of Mathlib's `CliffordAlgebra.toBaseChange_involute`: on the tensor
carrier `A ⊗[R] Cℓ(M, Q)`, the grade involution acts on the right factor only. -/
theorem ofBaseChange_map_involute (x : A ⊗[R] CliffordAlgebra Q) :
    ofBaseChange A Q (TensorProduct.map LinearMap.id involute.toLinearMap x) =
      involute (ofBaseChange A Q x) := by
  conv_lhs => rw [← toBaseChange_ofBaseChange A Q x, ← toBaseChange_involute,
    ofBaseChange_toBaseChange]

/-- The inverse-map form of Mathlib's `CliffordAlgebra.toBaseChange_reverse`: on the tensor
carrier `A ⊗[R] Cℓ(M, Q)`, reversal acts on the right factor only. -/
theorem ofBaseChange_map_reverse (x : A ⊗[R] CliffordAlgebra Q) :
    ofBaseChange A Q (TensorProduct.map LinearMap.id reverse x) =
      reverse (ofBaseChange A Q x) := by
  conv_lhs => rw [← toBaseChange_ofBaseChange A Q x, ← toBaseChange_reverse,
    ofBaseChange_toBaseChange]

variable {Q}

/-- The averaging projections `z ↦ ⅟2 • (z ± involute z)` of the tensor carrier land in the scalar
extensions of the even and odd parts respectively. -/
private theorem invOf_two_smul_add_sub_map_involute_mem (z : A ⊗[R] CliffordAlgebra Q) :
    (⅟2 : R) • (z + TensorProduct.map LinearMap.id involute.toLinearMap z) ∈
        (evenOdd Q 0).baseChange A ∧
      (⅟2 : R) • (z - TensorProduct.map LinearMap.id involute.toLinearMap z) ∈
        (evenOdd Q 1).baseChange A := by
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_add,
      ← TensorProduct.tmul_sub, ← TensorProduct.tmul_smul]
    refine ⟨Submodule.tmul_mem_baseChange_of_mem a (involute_eq_self_iff.mp ?_),
      Submodule.tmul_mem_baseChange_of_mem a (involute_eq_neg_iff.mp ?_)⟩
    · simp [add_comm]
    · simp [smul_sub]
  | add z w hz hw =>
    rw [map_add, add_add_add_comm, add_sub_add_comm, smul_add, smul_add (⅟2 : R) (z - _)]
    exact ⟨add_mem hz.1 hw.1, add_mem hz.2 hw.2⟩

/-- **The even part of the tensor carrier is the fixed space of the grade involution**: an element
of `A ⊗[R] Cℓ(M, Q)` lies in the scalar extension of the even part exactly when the grade
involution of the right factor fixes it. -/
theorem mem_baseChange_evenOdd_zero_iff {y : A ⊗[R] CliffordAlgebra Q} :
    y ∈ (evenOdd Q 0).baseChange A ↔
      TensorProduct.map LinearMap.id involute.toLinearMap y = y := by
  refine ⟨?_, fun hy => ?_⟩
  · intro hy
    obtain ⟨t, rfl⟩ := Submodule.toBaseChange_surjective' A _ hy
    clear hy
    induction t using TensorProduct.inductionOn with
    | tmul a c => simp [involute_eq_of_mem_even c.2]
    | add s t hs ht => simp only [map_add, Submodule.coe_add, hs, ht]
  · simpa [hy, ← two_smul R y, smul_smul] using (invOf_two_smul_add_sub_map_involute_mem y).1

/-- **The odd part of the tensor carrier is the `-1`-eigenspace of the grade involution**: an
element of `A ⊗[R] Cℓ(M, Q)` lies in the scalar extension of the odd part exactly when the grade
involution of the right factor negates it. -/
theorem mem_baseChange_evenOdd_one_iff {y : A ⊗[R] CliffordAlgebra Q} :
    y ∈ (evenOdd Q 1).baseChange A ↔
      TensorProduct.map LinearMap.id involute.toLinearMap y = -y := by
  refine ⟨?_, fun hy => ?_⟩
  · intro hy
    obtain ⟨t, rfl⟩ := Submodule.toBaseChange_surjective' A _ hy
    clear hy
    induction t using TensorProduct.inductionOn with
    | tmul a c => simp [involute_eq_of_mem_odd c.2, TensorProduct.tmul_neg]
    | add s t hs ht => simp only [map_add, Submodule.coe_add, hs, ht, neg_add]
  · simpa [hy, ← two_smul R y, smul_smul] using (invOf_two_smul_add_sub_map_involute_mem y).2

/-- **The `ℤ/2`-grading is compatible with extension of scalars**: an element of `Cℓ(A ⊗ M, Q_A)`
is homogeneous of parity `i` exactly when its image under `CliffordAlgebra.toBaseChange` lies in
the scalar extension of the parity-`i` part of `Cℓ(M, Q)`. -/
@[simp]
theorem toBaseChange_mem_baseChange_evenOdd_iff {x : CliffordAlgebra (Q.baseChange A)}
    {i : ZMod 2} :
    toBaseChange A Q x ∈ (evenOdd Q i).baseChange A ↔ x ∈ evenOdd (Q.baseChange A) i := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  have hinj : Function.Injective (toBaseChange A Q) :=
    Function.LeftInverse.injective (ofBaseChange_toBaseChange A Q)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
  · rw [mem_baseChange_evenOdd_zero_iff, ← toBaseChange_involute, hinj.eq_iff,
      involute_eq_self_iff]
  · rw [mem_baseChange_evenOdd_one_iff, ← toBaseChange_involute, ← map_neg, hinj.eq_iff,
      involute_eq_neg_iff]

/-- **The `ℤ/2`-grading is compatible with extension of scalars**, in the direction of
`CliffordAlgebra.ofBaseChange`: it maps the scalar extension of the parity-`i` part of `Cℓ(M, Q)`
exactly onto the parity-`i` part of `Cℓ(A ⊗ M, Q_A)`. -/
@[simp]
theorem ofBaseChange_mem_evenOdd_iff {y : A ⊗[R] CliffordAlgebra Q} {i : ZMod 2} :
    ofBaseChange A Q y ∈ evenOdd (Q.baseChange A) i ↔ y ∈ (evenOdd Q i).baseChange A := by
  rw [← toBaseChange_mem_baseChange_evenOdd_iff, toBaseChange_ofBaseChange]

end TensorCarrier

/-- Two `A`-algebra homomorphisms out of `CliffordAlgebra (Q.baseChange A)` are equal if and only
if they agree on `ι (Q.baseChange A) (1 ⊗ₜ v)` for every `v : M`. -/
theorem baseChange_hom_ext_iff {B : Type*} [Semiring B] [Algebra A B] {Q : QuadraticForm R M}
    {σ₁ σ₂ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B} :
    σ₁ = σ₂ ↔ ∀ v : M, σ₁ (ι (Q.baseChange A) (1 ⊗ₜ v)) = σ₂ (ι (Q.baseChange A) (1 ⊗ₜ v)) := by
  refine ⟨fun h v ↦ congr($h _), fun h ↦ AlgHom.toRingHom_injective ?_⟩
  exact baseChange_ringHom_ext Q (fun a ↦ by simp) h

end CliffordAlgebra

/-! ### Scalar extension of Clifford algebra homomorphisms -/

namespace AlgHom

open CliffordAlgebra

variable {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
  {Q : QuadraticForm R V}

section Lift

variable (A : Type*) [CommRing A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Extend an `R`-algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[R] B` into an `A`-algebra `B`
along `CliffordAlgebra.toBaseChange A Q` to an `A`-algebra homomorphism out of
`CliffordAlgebra (Q.baseChange A)`. -/
noncomputable def cliffordBaseChange (ρ : CliffordAlgebra Q →ₐ[R] B) :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] B :=
  (ρ.liftEquiv R A (CliffordAlgebra Q) B).comp (CliffordAlgebra.toBaseChange A Q)

variable {A}

/-- Evaluating `ρ.cliffordBaseChange A` after `CliffordAlgebra.ofBaseChange A Q` recovers the
tensor-product scalar extension `AlgHom.liftEquiv`. -/
@[simp]
theorem cliffordBaseChange_ofBaseChange (ρ : CliffordAlgebra Q →ₐ[R] B)
    (x : A ⊗[R] CliffordAlgebra Q) :
    ρ.cliffordBaseChange A (ofBaseChange A Q x) = ρ.liftEquiv R A (CliffordAlgebra Q) B x := by
  simp [cliffordBaseChange]

/-- On a pure base-changed vector `a ⊗ₜ v`, `ρ.cliffordBaseChange A` acts by `a • ρ (ι Q v)`. -/
@[simp]
theorem cliffordBaseChange_ι_tmul (ρ : CliffordAlgebra Q →ₐ[R] B) (a : A) (v : V) :
    ρ.cliffordBaseChange A (ι (Q.baseChange A) (a ⊗ₜ v)) = a • ρ (ι Q v) := by
  simp [cliffordBaseChange]

/-- On an embedded vector `1 ⊗ₜ v`, `ρ.cliffordBaseChange A` agrees with `ρ` on `ι Q v`. -/
theorem cliffordBaseChange_ι_one_tmul (ρ : CliffordAlgebra Q →ₐ[R] B) (v : V) :
    ρ.cliffordBaseChange A (ι (Q.baseChange A) (1 ⊗ₜ v)) = ρ (ι Q v) := by
  rw [cliffordBaseChange_ι_tmul, one_smul]

/-- Restricting `ρ.cliffordBaseChange A` to `R` and precomposing with
`CliffordAlgebra.ofBaseChangeAux A Q` recovers `ρ`. -/
@[simp]
theorem cliffordBaseChange_restrictScalars_comp_ofBaseChangeAux (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ((ρ.cliffordBaseChange A).restrictScalars R).comp (ofBaseChangeAux A Q) = ρ := by
  apply CliffordAlgebra.hom_ext
  ext v
  simp

/-- Restricting `ρ.cliffordBaseChange A` along `CliffordAlgebra.ofBaseChangeAux A Q` recovers `ρ`
pointwise. -/
@[simp]
theorem cliffordBaseChange_ofBaseChangeAux (ρ : CliffordAlgebra Q →ₐ[R] B)
    (x : CliffordAlgebra Q) :
    ρ.cliffordBaseChange A (ofBaseChangeAux A Q x) = ρ x :=
  congr($(ρ.cliffordBaseChange_restrictScalars_comp_ofBaseChangeAux) x)

/-- An `A`-algebra homomorphism `σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B` equals
`ρ.cliffordBaseChange A` if and only if it maps every `ι (Q.baseChange A) (1 ⊗ₜ v)` to
`ρ (ι Q v)`. -/
theorem eq_cliffordBaseChange_iff (ρ : CliffordAlgebra Q →ₐ[R] B)
    {σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B} :
    σ = ρ.cliffordBaseChange A ↔ ∀ v : V, σ (ι (Q.baseChange A) (1 ⊗ₜ v)) = ρ (ι Q v) := by
  rw [CliffordAlgebra.baseChange_hom_ext_iff]
  simp

/-- `ρ.cliffordBaseChange A` is `Algebra.TensorProduct.lift` of `Algebra.ofId A B` and `ρ`,
precomposed with `CliffordAlgebra.equivBaseChange A Q`. -/
theorem cliffordBaseChange_eq_lift (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ρ.cliffordBaseChange A =
      (Algebra.TensorProduct.lift (Algebra.ofId A B) ρ
        (fun a x ↦ by rw [Algebra.ofId_apply]; exact Algebra.commutes a (ρ x))).comp
        (CliffordAlgebra.equivBaseChange A Q).toAlgHom := by
  symm
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp [equivBaseChange]

end Lift

section Equiv

/-- Scalar extension of Clifford algebra homomorphisms as an equivalence
`(CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B)`, with inverse given by
restriction along `CliffordAlgebra.ofBaseChangeAux A Q`. -/
noncomputable def cliffordBaseChangeEquiv (A : Type*) [CommRing A] [Algebra R A]
    (Q : QuadraticForm R V) (B : Type*) [Semiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] :
    (CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B) where
  toFun := cliffordBaseChange A
  invFun σ := (σ.restrictScalars R).comp (ofBaseChangeAux A Q)
  left_inv := cliffordBaseChange_restrictScalars_comp_ofBaseChangeAux
  right_inv σ := ((eq_cliffordBaseChange_iff _).2 fun v ↦ by simp).symm

variable {A : Type*} [CommRing A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Applying `AlgHom.cliffordBaseChangeEquiv` computes `AlgHom.cliffordBaseChange`. -/
@[simp]
theorem cliffordBaseChangeEquiv_apply (ρ : CliffordAlgebra Q →ₐ[R] B) :
    cliffordBaseChangeEquiv A Q B ρ = ρ.cliffordBaseChange A :=
  (rfl)

/-- The inverse of `AlgHom.cliffordBaseChangeEquiv` restricts scalars to `R` and precomposes with
`CliffordAlgebra.ofBaseChangeAux A Q`. -/
@[simp]
theorem cliffordBaseChangeEquiv_symm_apply (σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B) :
    (cliffordBaseChangeEquiv A Q B).symm σ = (σ.restrictScalars R).comp (ofBaseChangeAux A Q) :=
  (rfl)

/-- Extending the restriction `(σ.restrictScalars R).comp (ofBaseChangeAux A Q)` of an `A`-algebra
map `σ` out of `CliffordAlgebra (Q.baseChange A)` recovers `σ`. -/
@[simp]
theorem cliffordBaseChange_comp_ofBaseChangeAux (σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B) :
    ((σ.restrictScalars R).comp (ofBaseChangeAux A Q)).cliffordBaseChange A = σ :=
  (cliffordBaseChangeEquiv A Q B).right_inv σ

end Equiv

section Functoriality

variable (A : Type*) [CommRing A] [Algebra R A]
  {B C : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/-- Scalar extension of Clifford algebra homomorphisms commutes with postcomposition by an
`A`-algebra homomorphism. -/
theorem comp_cliffordBaseChange (ψ : B →ₐ[A] C) (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ψ.comp (ρ.cliffordBaseChange A) = ((ψ.restrictScalars R).comp ρ).cliffordBaseChange A := by
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp

/-- Scalar extension of Clifford algebra homomorphisms commutes with pullback along an isometry of
quadratic forms. -/
theorem cliffordBaseChange_comp_map {V' : Type*} [AddCommGroup V'] [Module R V']
    {Q' : QuadraticForm R V'} (f : Q' →qᵢ Q) (ρ : CliffordAlgebra Q →ₐ[R] B) :
    (ρ.comp (CliffordAlgebra.map f)).cliffordBaseChange A =
      (ρ.cliffordBaseChange A).comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.baseChange f A)) := by
  symm
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp

end Functoriality

end AlgHom
