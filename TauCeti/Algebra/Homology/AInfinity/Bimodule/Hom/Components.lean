/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Basic
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Suspension

/-!
# Components of A-infinity bimodule morphisms

A morphism of `(A, B)` bimodules has a suspended component on
`(sA)^⊗i ⊗ sM ⊗ (sB)^⊗j` of degree zero. Its unsuspended component has degree
`-i-j`. The indices count algebra inputs, so `(0, 0)` is the unary component.
We expose the components in both conventions, recover the Taylor map from them,
and prove that either family determines the morphism.

Unsuspension reuses `AInfinityBimodule.unsuspend`. Inputs are curried with the module
variable first, but the Koszul signs use the physical order `A, …, A, M, B, …, B`.
The formulas here allow bimodule morphism equations to be expressed without bar words.

## References

* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators TensorProduct

namespace TauCeti.AInfinityBimoduleHom

open AInfinityBimodule

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}

/-- The suspended component with `i` left and `j` right algebra inputs. -/
noncomputable def suspendedComponent (f : AInfinityBimoduleHom MM NN) (i j : ℕ) :
    (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B →ₗ[R] N :=
  f.taylor ∘ₗ TensorProduct.map ((TensorWords.of R A i).rTensor M)
    (TensorWords.of R B j)

/-- A suspended component restricts the Taylor map to the specified word lengths. -/
theorem suspendedComponent_def (f : AInfinityBimoduleHom MM NN) (i j : ℕ) :
    f.suspendedComponent i j = f.taylor ∘ₗ
      TensorProduct.map ((TensorWords.of R A i).rTensor M) (TensorWords.of R B j) := (rfl)

/-- Evaluation of a suspended component includes the two words into the bar bicomodule. -/
@[simp]
theorem suspendedComponent_tmul (f : AInfinityBimoduleHom MM NN) (i j : ℕ)
    (a : TensorPower R i A) (x : M) (b : TensorPower R j B) :
    f.suspendedComponent i j ((a ⊗ₜ x) ⊗ₜ b) =
      f.taylor ((TensorWords.of R A i a ⊗ₜ x) ⊗ₜ TensorWords.of R B j b) := (rfl)

/-- Each suspended component preserves the total suspended input degree. -/
theorem suspendedComponent_tmul_tprod_mem (f : AInfinityBimoduleHom MM NN) (i j : ℕ)
    (a : Fin i → A) (d : Fin i → ℤ)
    (ha : ∀ k, a k ∈ (AA.grading.shift 1).piece (d k))
    {x : M} {p : ℤ} (hx : x ∈ (MM.grading.shift 1).piece p)
    (b : Fin j → B) (e : Fin j → ℤ)
    (hb : ∀ k, b k ∈ (BB.grading.shift 1).piece (e k)) :
    f.suspendedComponent i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) ∈
      (NN.grading.shift 1).piece ((∑ k, d k) + p + (∑ k, e k)) := by
  rw [suspendedComponent_tmul]
  have hz : ((TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) ⊗ₜ
      TensorWords.of R B j (PiTensorProduct.tprod R b)) ∈
      (barGrading AA BB MM.grading).piece ((∑ k, d k) + p + (∑ k, e k)) := by
    rw [barGrading_def]
    exact InternalGrading.tmul_mem_tensorProduct _ _
      (InternalGrading.tmul_mem_tensorProduct _ _
        (by simpa only [TensorWords.grading_piece] using
          TensorWords.mem_gradedPiece_of_tprod _ a d ha) hx)
      (by simpa only [TensorWords.grading_piece] using
        TensorWords.mem_gradedPiece_of_tprod _ b e hb)
  simpa only [add_zero] using f.isHomogeneous_taylor.map_mem hz

/-- The suspended components determine a bimodule morphism. -/
@[ext]
theorem ext_suspendedComponent {f g : AInfinityBimoduleHom MM NN}
    (h : ∀ i j, f.suspendedComponent i j = g.suspendedComponent i j) : f = g := by
  apply ext
  apply TensorProduct.ext'
  intro u v
  suffices hv : (TensorProduct.curry f.taylor).flip v =
      (TensorProduct.curry g.taylor).flip v from LinearMap.congr_fun hv u
  apply TensorProduct.ext'
  intro w x
  have hw : (TensorProduct.curry ((TensorProduct.curry f.taylor).flip v)).flip x =
      (TensorProduct.curry ((TensorProduct.curry g.taylor).flip v)).flip x := by
    apply TensorWords.linearMap_ext
    intro i a
    have hv : TensorProduct.curry f.taylor
        (TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) =
        TensorProduct.curry g.taylor
          (TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) := by
      apply TensorWords.linearMap_ext
      intro j b
      simpa only [TensorProduct.curry_apply, ← suspendedComponent_tmul] using
        LinearMap.congr_fun (h i j) ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ
          PiTensorProduct.tprod R b)
    exact LinearMap.congr_fun hv v
  exact LinearMap.congr_fun hw w

/-- The unsuspended component of degree `-i-j`, curried with the module variable first. -/
noncomputable def component (f : AInfinityBimoduleHom MM NN) (i j : ℕ) :
    M →ₗ[R] MultilinearMap R (fun _ : Fin i ↦ A)
      (MultilinearMap R (fun _ : Fin j ↦ B) N) :=
  unsuspend AA.grading MM.grading BB.grading i j (f.suspendedComponent i j)

/-- An unsuspended component evaluates the suspended component on Koszul-twisted inputs. -/
theorem component_apply (f : AInfinityBimoduleHom MM NN) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    f.component i j x a b = f.suspendedComponent i j
      ((PiTensorProduct.tprod R (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
        ⊗ₜ MM.grading.koszulTwist j x) ⊗ₜ
          PiTensorProduct.tprod R (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k))) :=
  unsuspend_apply _ _ _ _ _ _ _ _ _

/-- The suspended component is recovered by applying the same involutive input twists. -/
theorem suspendedComponent_tmul_tprod (f : AInfinityBimoduleHom MM NN) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    f.suspendedComponent i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      f.component i j (MM.grading.koszulTwist j x)
        (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
        (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k)) :=
  apply_tmul_tprod_eq_unsuspend _ _ _ _ _ _ _ _ _

/-- The unsuspended components recover the Taylor map on every pair of pure words. -/
theorem taylor_tmul_of_tprod (f : AInfinityBimoduleHom MM NN) (i j : ℕ) (x : M)
    (a : Fin i → A) (b : Fin j → B) :
    f.taylor ((TensorWords.of R A i (PiTensorProduct.tprod R a) ⊗ₜ x) ⊗ₜ
      TensorWords.of R B j (PiTensorProduct.tprod R b)) =
        f.component i j (MM.grading.koszulTwist j x)
          (fun k ↦ AA.grading.koszulTwist ((i : ℤ) + j - k) (a k))
          (fun k ↦ BB.grading.koszulTwist ((j : ℤ) - 1 - k) (b k)) := by
  rw [← suspendedComponent_tmul, suspendedComponent_tmul_tprod]

/-- The unsuspended component has degree `-i-j` in the original gradings. -/
theorem component_mem_piece (f : AInfinityBimoduleHom MM NN) (i j : ℕ)
    {x : M} {p : ℤ} (hx : x ∈ MM.grading.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ AA.grading.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ BB.grading.piece (e k)) :
    f.component i j x a b ∈ NN.grading.piece ((∑ k, d k) + p + (∑ k, e k) - i - j) := by
  have h := unsuspend_mem_piece AA.grading MM.grading BB.grading
    (GN := NN.grading.shift 1) i j (F := f.suspendedComponent i j) 0
    (fun hx a d ha b e hb ↦ by
      simpa only [add_zero] using f.suspendedComponent_tmul_tprod_mem i j a d ha hx b e hb)
    hx a d ha b e hb
  rw [unsuspend_apply, InternalGrading.shift_piece] at h
  rw [component_apply]
  convert h using 1; congr 1; ring

/-- On homogeneous inputs, the suspension sign counts successors in the order `A, M, B`. -/
theorem suspendedComponent_tmul_tprod_of_mem (f : AInfinityBimoduleHom MM NN) (i j : ℕ)
    {x : M} {p : ℤ} (hx : x ∈ MM.grading.piece p)
    (a : Fin i → A) (d : Fin i → ℤ) (ha : ∀ k, a k ∈ AA.grading.piece (d k))
    (b : Fin j → B) (e : Fin j → ℤ) (hb : ∀ k, b k ∈ BB.grading.piece (e k)) :
    f.suspendedComponent i j ((PiTensorProduct.tprod R a ⊗ₜ x) ⊗ₜ PiTensorProduct.tprod R b) =
      negOnePowCast R ((∑ k, ((i : ℤ) + j - k) * d k) + j * p +
        ∑ k, ((j : ℤ) - 1 - k) * e k) • f.component i j x a b :=
  apply_tmul_tprod_of_mem _ _ _ _ _ _ hx a d ha b e hb

/-- The unsuspended components determine a bimodule morphism. -/
theorem ext_component {f g : AInfinityBimoduleHom MM NN}
    (h : ∀ i j, f.component i j = g.component i j) : f = g := by
  apply ext_suspendedComponent
  intro i j
  apply TensorProduct.ext_threefold
  intro w x v
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
      rw [suspendedComponent_tmul_tprod, suspendedComponent_tmul_tprod, h]
    | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
  | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]

/-- With no algebra inputs, unsuspension contributes no sign and both bar words are empty. -/
@[simp]
theorem component_zero_zero (f : AInfinityBimoduleHom MM NN) (x : M)
    (a : Fin 0 → A) (b : Fin 0 → B) :
    f.component 0 0 x a b = f.taylor ((1 ⊗ₜ x) ⊗ₜ 1) := by
  rw [component_apply, suspendedComponent_tmul]
  simp only [Nat.cast_zero, InternalGrading.koszulTwist_zero, LinearMap.id_apply]
  congr 2
  · congr 1
    rw [TensorWords.one_eq_of_zero]
    exact TensorWords.of_tprod_congr R A fun k ↦ k.elim0
  · rw [TensorWords.one_eq_of_zero]
    exact TensorWords.of_tprod_congr R B fun k ↦ k.elim0

/-- The identity has no suspended component with a positive number of algebra inputs. -/
@[simp]
theorem suspendedComponent_id_of_pos (MM : AInfinityBimodule AA BB M) {i j : ℕ}
    (h : 0 < i + j) : (AInfinityBimoduleHom.id MM).suspendedComponent i j = 0 := by
  apply TensorProduct.ext_threefold
  intro a x b
  simp only [suspendedComponent_tmul, taylor_id, AInfinityBimodule.taylorProj_tmul,
    LinearMap.zero_apply]
  rcases Nat.add_pos_iff_pos_or_pos.mp h with hi | hj
  · simp [TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R A hi.ne']
  · simp [TensorWords.counit_eq_counit, TensorWords.counit_of_of_ne_zero R B hj.ne']

/-- The identity has no unsuspended component with a positive number of algebra inputs. -/
@[simp]
theorem component_id_of_pos (MM : AInfinityBimodule AA BB M) {i j : ℕ} (h : 0 < i + j) :
    (AInfinityBimoduleHom.id MM).component i j = 0 := by
  ext x a b
  simp [component_apply, suspendedComponent_id_of_pos MM h]

end TauCeti.AInfinityBimoduleHom
