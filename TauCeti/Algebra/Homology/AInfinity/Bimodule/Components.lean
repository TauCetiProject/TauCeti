/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Basic
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Suspension

/-!
# Operations of an A-infinity bimodule

The Taylor map of an `(A, B)` `A∞` bimodule restricts to suspended operations `b i j` on
`(sA)^⊗i ⊗ sM ⊗ (sB)^⊗j`. The corresponding unsuspended operations `m i j` have degree
`1 - i - j`. They are curried with the module variable first, followed by the left and right
tuples; their suspension signs use the physical input order `A, …, A, M, B, …, B`.
Thus the left input in position `k` is twisted with parameter `i + j - k`, the module input
with parameter `j`, and the right input in position `k` with parameter `j - 1 - k`.

The characteristic equations recover either family from the other on arbitrary inputs. Together
with the grading, either family determines the bimodule. In particular, the indices `(0, 0)`
record the unary operation; there are no unused arity-zero values.

The unsuspension uses Mathlib's tensor currying and `PiTensorProduct.lift`, following the Koszul
twists used in `AInfinityRightModule.unsuspend`. The nested tensor and curried presentations
preserve the separate input carriers without heterogeneous finite-index transports.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3--5.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The suspended operation with `i` left algebra inputs and `j` right algebra inputs. -/
noncomputable def b (MM : AInfinityBimodule AA BB M) (i j : ℕ) :
    (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] M :=
  MM.taylor ∘ₗ TensorProduct.map ((TensorWords.of R A i).rTensor M)
    (TensorWords.of R B j)

/-- The suspended component is the restriction of the Taylor map to the two word lengths. -/
theorem b_def (MM : AInfinityBimodule AA BB M) (i j : ℕ) :
    MM.b i j = MM.taylor ∘ₗ TensorProduct.map ((TensorWords.of R A i).rTensor M)
      (TensorWords.of R B j) :=
  (rfl)

/-- The Taylor map on words of fixed lengths is the corresponding suspended operation. -/
theorem taylor_tmul_of (MM : AInfinityBimodule AA BB M) (i j : ℕ)
    (a : TensorPower R i A) (x : M) (b : TensorPower R j B) :
    MM.taylor ((TensorWords.of R A i a ⊗ₜ x) ⊗ₜ TensorWords.of R B j b) =
      MM.b i j ((a ⊗ₜ x) ⊗ₜ b) :=
  (rfl)

/-- Suspended components raise the total suspended input degree by one. -/
theorem isHomogeneous_b_tmul_tprod (MM : AInfinityBimodule AA BB M) (i j : ℕ)
    (a : Fin i → A) (d : Fin i → ℤ)
    (ha : ∀ k, a k ∈ (AA.grading.shift 1).piece (d k))
    {x : M} {p : ℤ} (hx : x ∈ (MM.grading.shift 1).piece p)
    (b : Fin j → B) (e : Fin j → ℤ)
    (hb : ∀ k, b k ∈ (BB.grading.shift 1).piece (e k)) :
    MM.b i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) ∈
      (MM.grading.shift 1).piece ((∑ k, d k) + p + (∑ k, e k) + 1) := by
  rw [← taylor_tmul_of]
  apply MM.isHomogeneous_taylor.map_mem
  rw [barGrading_def]
  exact InternalGrading.tmul_mem_tensorProduct _ _
    (InternalGrading.tmul_mem_tensorProduct _ _
      (by simpa only [TensorWords.grading_piece] using
        TensorWords.mem_gradedPiece_of_tprod _ a d ha) hx)
    (by simpa only [TensorWords.grading_piece] using
      TensorWords.mem_gradedPiece_of_tprod _ b e hb)

/-- Equality of Taylor maps is equivalent to equality of every suspended component. -/
theorem taylor_eq_taylor_iff {MM NN : AInfinityBimodule AA BB M} :
    MM.taylor = NN.taylor ↔ ∀ i j, MM.b i j = NN.b i j := by
  refine ⟨fun h i j ↦ by rw [b_def, b_def, h], fun h ↦ ?_⟩
  apply TensorProduct.ext'
  intro u v
  suffices hv : (TensorProduct.curry MM.taylor).flip v =
      (TensorProduct.curry NN.taylor).flip v from LinearMap.congr_fun hv u
  apply TensorProduct.ext'
  intro w x
  have hw : (TensorProduct.curry ((TensorProduct.curry MM.taylor).flip v)).flip x =
      (TensorProduct.curry ((TensorProduct.curry NN.taylor).flip v)).flip x := by
    apply TensorWords.linearMap_ext
    intro i a
    have hv : TensorProduct.curry MM.taylor
        (TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) =
        TensorProduct.curry NN.taylor
          (TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) := by
      apply TensorWords.linearMap_ext
      intro j b
      simpa only [TensorProduct.curry_apply, taylor_tmul_of] using
        LinearMap.congr_fun (h i j) ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ
          PiTensorProduct.tprod R b)
    exact LinearMap.congr_fun hv v
  exact LinearMap.congr_fun hw w

/-- A bimodule is determined by its grading and suspended operations. -/
theorem ext_b {MM NN : AInfinityBimodule AA BB M} (hG : MM.grading = NN.grading)
    (hb : ∀ i j, MM.b i j = NN.b i j) : MM = NN :=
  ext hG (taylor_eq_taylor_iff.2 hb)

/-- The unsuspended bimodule operation. Evaluation is curried as `m i j x a b`, while the
suspension uses the input order of the left tuple, the module input, and the right tuple. -/
noncomputable def m (MM : AInfinityBimodule AA BB M) (i j : ℕ) :
    M →ₗ[R] MultilinearMap R (fun _ : Fin i ↦ A)
      (MultilinearMap R (fun _ : Fin j ↦ B) M) :=
  unsuspend AA.grading MM.grading BB.grading i j (MM.b i j)

/-- Unsuspension evaluates the suspended component on the input Koszul twists. -/
theorem m_apply (MM : AInfinityBimodule AA BB M) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    MM.m i j x a b = MM.b i j
      ((PiTensorProduct.tprod R (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
        ⊗ₜ MM.grading.koszulTwist j x) ⊗ₜ
          PiTensorProduct.tprod R (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k))) := by
  exact unsuspend_apply AA.grading MM.grading BB.grading i j (MM.b i j) x a b

/-- The suspended operation is recovered by the same original-grading twists. -/
theorem b_tmul_tprod (MM : AInfinityBimodule AA BB M) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    MM.b i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      MM.m i j (MM.grading.koszulTwist j x)
        (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
        (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k)) := by
  exact apply_tmul_tprod_eq_unsuspend AA.grading MM.grading BB.grading i j (MM.b i j) x a b

/-- On fixed-length pure words, the Taylor map is recovered from the unsuspended operation. -/
theorem taylor_tmul_of_tprod (MM : AInfinityBimodule AA BB M) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    MM.taylor ((TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) ⊗ₜ
      TensorWords.of R B j (PiTensorProduct.tprod R b)) =
        MM.m i j (MM.grading.koszulTwist j x)
          (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
          (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k)) := by
  rw [taylor_tmul_of, b_tmul_tprod]

/-- Unsuspended operations have degree `1 - i - j` in the original gradings. -/
theorem m_mem_piece (MM : AInfinityBimodule AA BB M) (i j : ℕ)
    {x : M} {p : ℤ} (hx : x ∈ MM.grading.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ AA.grading.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ BB.grading.piece (e k)) :
    MM.m i j x a b ∈ MM.grading.piece ((∑ k, d k) + p + (∑ k, e k) + (1 - i - j)) := by
  have h := unsuspend_mem_piece AA.grading MM.grading BB.grading
    (GN := MM.grading.shift 1) i j (F := MM.b i j) 1
    (fun hx a d ha b e hb ↦ MM.isHomogeneous_b_tmul_tprod i j a d ha hx b e hb)
    hx a d ha b e hb
  rw [unsuspend_apply, InternalGrading.shift_piece] at h
  rw [m_apply]
  convert h using 1; congr 1; ring

/-- On homogeneous inputs, suspension contributes the Koszul sign for the order `A, M, B`. -/
theorem b_tmul_tprod_of_mem (MM : AInfinityBimodule AA BB M) (i j : ℕ)
    {x : M} {p : ℤ} (hx : x ∈ MM.grading.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ AA.grading.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ BB.grading.piece (e k)) :
    MM.b i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      negOnePowCast R ((∑ k, ((i : ℤ) + j - k) * d k) + j * p +
        ∑ k, ((j : ℤ) - 1 - k) * e k) • MM.m i j x a b := by
  exact apply_tmul_tprod_of_mem AA.grading MM.grading BB.grading i j (MM.b i j)
    hx a d ha b e hb

/-- Equal unsuspended operations give equal suspended components when the gradings agree. -/
theorem b_eq_b_of_m_eq_m {MM NN : AInfinityBimodule AA BB M} (hG : MM.grading = NN.grading)
    (i j : ℕ) (hm : MM.m i j = NN.m i j) : MM.b i j = NN.b i j := by
  apply TensorProduct.ext_threefold
  intro w x v
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
      rw [b_tmul_tprod, b_tmul_tprod, hm, hG]
    | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
  | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]

/-- A bimodule is determined by its grading and unsuspended operations. -/
theorem ext_m {MM NN : AInfinityBimodule AA BB M} (hG : MM.grading = NN.grading)
    (hm : ∀ i j, MM.m i j = NN.m i j) : MM = NN :=
  ext_b hG fun i j ↦ b_eq_b_of_m_eq_m hG i j (hm i j)

/-- The unary unsuspended operation is the Taylor map on the two empty words. -/
@[simp]
theorem m_zero_zero (MM : AInfinityBimodule AA BB M) (x : M)
    (a : Fin 0 → A) (b : Fin 0 → B) :
    MM.m 0 0 x a b = MM.taylor ((1 ⊗ₜ x) ⊗ₜ 1) := by
  rw [m_apply, ← taylor_tmul_of]
  simp only [Nat.cast_zero, InternalGrading.koszulTwist_zero, LinearMap.id_apply]
  congr 2
  · congr 1
    rw [TensorWords.one_eq_of_zero]
    exact TensorWords.of_tprod_congr R A fun k ↦ k.elim0
  · rw [TensorWords.one_eq_of_zero]
    exact TensorWords.of_tprod_congr R B fun k ↦ k.elim0

end TauCeti.AInfinityBimodule
