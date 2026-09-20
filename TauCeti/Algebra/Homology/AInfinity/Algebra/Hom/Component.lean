/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Basic

/-!
# Components of morphisms of A-infinity algebras

The bar-coalgebra definition of an `A∞` morphism stores its suspended Taylor map
`Tᶜ(sA) ⟶ sB`. This file exposes the corresponding unsuspended multilinear components
`fₙ : Aⁿ ⟶ B`. The arity-`n` component has cohomological degree `1 - n`, and its
suspension recovers the restriction of the Taylor map to words of length `n`.

The unsuspension sign is implemented by applying the Koszul twist of parameter `n - 1 - i` to
input `i`. On homogeneous inputs of degrees `d i`, this is multiplication by
`(-1) ^ MultilinearMap.suspExp n d`; applying the suspension sign a second time cancels it.
Thus consumers can calculate with ordinary multilinear maps without unfolding the bar
construction, while the stored coalgebra morphism remains the source of the composition and
component equations.

## Main definitions

* `TauCeti.AInfinityHom.component`: the unsuspended component `fₙ`.

## Main results

* `TauCeti.AInfinityHom.taylor_eq_suspend_component`: suspending `fₙ` recovers the Taylor map
  on homogeneous pure tensors.
* `TauCeti.AInfinityHom.isHomogeneous_component`: `fₙ` has degree `1 - n`.
* `TauCeti.AInfinityHom.component_one`: `f₁` is the linear part.
* `TauCeti.AInfinityHom.ext_component`: a morphism is determined by its unsuspended components.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-! ### Suspended and unsuspended arity components -/

/-- The restriction of the suspended Taylor map of an `A∞` morphism to words of length `n`.
It is zero in arity zero. -/
noncomputable def suspendedComponent (f : AInfinityHom AA BB) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ A) B :=
  if hn : 0 < n then
    PiTensorProduct.lift.symm
      (f.taylor ∘ₗ ReducedTensorWords.of R A ⟨n, hn⟩)
  else 0

/-- The suspended component in arity zero vanishes. -/
@[simp]
theorem suspendedComponent_zero (f : AInfinityHom AA BB) : f.suspendedComponent 0 = 0 := by
  rw [suspendedComponent, dite_eq_right (by omega)]

/-- Evaluation of the suspended arity component is evaluation of the Taylor map on the
corresponding pure tensor word. -/
theorem suspendedComponent_apply (f : AInfinityHom AA BB) (n : ℕ) (hn : 0 < n)
    (x : Fin n → A) :
    f.suspendedComponent n x =
      f.taylor (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x)) := by
  rw [suspendedComponent, dite_eq_left hn, PiTensorProduct.lift_symm,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]

/-- The unsuspended arity-`n` component `fₙ : Aⁿ ⟶ B` of an `A∞` morphism. It is
zero in arity zero. For positive arity, the Koszul twists undo the tensor-power suspension sign
in the Taylor map. -/
noncomputable def component (f : AInfinityHom AA BB) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ A) B :=
  (f.suspendedComponent n).compLinearMap fun i ↦
    AA.grading.koszulTwist ((n : ℤ) - 1 - i)

/-- The unsuspended component in arity zero vanishes. -/
@[simp]
theorem component_zero (f : AInfinityHom AA BB) : f.component 0 = 0 := by
  rw [component, suspendedComponent_zero, MultilinearMap.zero_compLinearMap]

/-- Evaluate an unsuspended component through the suspended Taylor map. -/
theorem component_apply (f : AInfinityHom AA BB) (n : ℕ) (hn : 0 < n)
    (x : Fin n → A) :
    f.component n x =
      f.taylor
        (ReducedTensorWords.of R A ⟨n, hn⟩
          (PiTensorProduct.tprod R fun i ↦
            AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i))) := by
  rw [component, MultilinearMap.compLinearMap_apply, suspendedComponent_apply f n hn]

/-- Suspending the unsuspended component `fₙ` recovers the Taylor map on a homogeneous pure
tensor. This is the commuting suspension square for an `A∞` morphism. -/
theorem taylor_eq_suspend_component (f : AInfinityHom AA BB) (n : ℕ) (hn : 0 < n)
    (d : ℕ → ℤ) (x : ℕ → A) (hx : ∀ i < n, x i ∈ AA.grading.piece (d i)) :
    f.taylor
        (ReducedTensorWords.of R A ⟨n, hn⟩
          (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
      MultilinearMap.evalNat (MultilinearMap.suspend d (f.component n)) x := by
  rw [AInfinity.evalNat_suspend, MultilinearMap.evalNat_def, component_apply f n hn]
  have htwist :
      (fun i : Fin n ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)) =
        fun i : Fin n ↦
          negOnePowCast R (((n : ℤ) - 1 - i) * d i) • x i := by
    funext i
    rw [AA.grading.koszulTwist_apply_of_mem (hx i i.isLt), negOnePowCast_eq_intCast]
  rw [htwist, (PiTensorProduct.tprod R).map_smul_univ, map_smul, map_smul,
    MultilinearMap.suspExp_def, negOnePowCast_sum,
    ← Fin.prod_univ_eq_prod_range (fun i ↦ negOnePowCast R _), smul_smul]
  simp only [← Finset.prod_mul_distrib, ← negOnePowCast_add, ← two_mul,
    negOnePowCast_two_mul, Finset.prod_const_one, one_smul]

/-! ### Degree and extensionality -/

/-- The suspended arity component has degree zero between the suspended gradings. -/
theorem isHomogeneous_suspendedComponent (f : AInfinityHom AA BB) (n : ℕ) :
    MultilinearMap.IsHomogeneous (f.suspendedComponent n)
      (fun _ ↦ (AA.grading.shift 1).piece) (BB.grading.shift 1).piece 0 := by
  rcases n with _ | n
  · rw [suspendedComponent_zero]
    exact MultilinearMap.isHomogeneous_zero _ _ _
  · rw [MultilinearMap.isHomogeneous_def]
    intro d x hx
    rw [suspendedComponent_apply f (n + 1) (by omega)]
    apply f.isHomogeneous_taylor.map_mem
    exact ReducedTensorWords.mem_gradedPiece_of_tprod (AA.grading.shift 1) (by omega) x d hx

/-- The unsuspended component `fₙ` has cohomological degree `1 - n`. -/
theorem isHomogeneous_component (f : AInfinityHom AA BB) (n : ℕ) :
    MultilinearMap.IsHomogeneous (f.component n)
      (fun _ ↦ AA.grading.piece) BB.grading.piece (1 - n) := by
  have hs : MultilinearMap.IsHomogeneous (f.suspendedComponent n)
      (fun _ ↦ AA.grading.piece) BB.grading.piece (1 - n) := by
    have hA : (AA.grading.shift 1).piece = Graded.shift AA.grading.piece 1 := by
      funext p
      rw [InternalGrading.shift_piece, Graded.shift_apply]
    have hB : (BB.grading.shift 1).piece = Graded.shift BB.grading.piece 1 := by
      funext p
      rw [InternalGrading.shift_piece, Graded.shift_apply]
    have h := (MultilinearMap.isHomogeneous_shift_const_iff).1
      (hA ▸ hB ▸ f.isHomogeneous_suspendedComponent n)
    simpa using h
  rw [component]
  have htwist : ∀ i : Fin n, LinearMap.IsHomogeneous
      (AA.grading.koszulTwist ((n : ℤ) - 1 - i)) AA.grading.piece AA.grading.piece 0 := by
    intro i
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    simpa only [add_zero] using
      AA.grading.koszulTwist_mem_piece ha ((n : ℤ) - 1 - i)
  simpa using hs.compLinearMap htwist

/-- The arity-one component is the linear part, regarded as a multilinear map on `Fin 1`. -/
@[simp]
theorem component_one (f : AInfinityHom AA BB) :
    f.component 1 =
      (MultilinearMap.ofSubsingleton R A B (0 : Fin 1)) f.linearPart := by
  ext x
  rw [component_apply f 1 (by omega)]
  simp only [PNat.mk_ofNat, Nat.cast_one, sub_self, Fin.val_eq_zero, CharP.cast_eq_zero,
    InternalGrading.koszulTwist_zero, LinearMap.id_coe, id_eq, Fin.isValue,
    MultilinearMap.ofSubsingleton_apply_apply, linearPart_apply]
  have hword :
      ReducedTensorWords.of R A ⟨1, Nat.one_pos⟩ (PiTensorProduct.tprod R x) =
        ReducedTensorWords.ofLetter R A (x 0) := by
    rw [ReducedTensorWords.of_tprod_eq_subword R Nat.one_pos x,
      ReducedTensorWords.subword_one R A x Nat.one_pos]
    congr 2
  exact congrArg f.taylor hword

/-- Two `A∞` morphisms are equal when all their unsuspended components agree. -/
theorem ext_component {f g : AInfinityHom AA BB}
    (h : ∀ n, f.component n = g.component n) : f = g := by
  apply AInfinityHom.ext
  apply ReducedTensorWords.linearMap_ext
  intro n z
  have hmaps : f.taylor ∘ₗ ReducedTensorWords.of R A n =
      g.taylor ∘ₗ ReducedTensorWords.of R A n := by
    apply AA.grading.piTensorProduct_ext
    intro q
    let d : ℕ → ℤ := fun i ↦ if hi : i < n.1 then (q ⟨i, hi⟩).1 else 0
    let x : ℕ → A := fun i ↦ if hi : i < n.1 then (q ⟨i, hi⟩).2 else 0
    have hx : ∀ i < n.1, x i ∈ AA.grading.piece (d i) := by
      intro i hi
      simp only [x, d, hi, dite_true]
      exact (q ⟨i, hi⟩).2.property
    have hf := f.taylor_eq_suspend_component n.1 n.2 d x hx
    have hg := g.taylor_eq_suspend_component n.1 n.2 d x hx
    rw [h n.1] at hf
    simpa only [LinearMap.comp_apply, x, Fin.isLt, dite_true] using hf.trans hg.symm
  exact LinearMap.congr_fun hmaps (PiTensorProduct.tprod R z)

end AInfinityHom

end TauCeti
