/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite tensor differentials in characteristic two

For a finite family of modules with endomorphisms `dᵢ`, the tensor differential is the sum of the
maps applying `dᵢ` in one tensor factor. If the endomorphisms square to zero and the ground ring
has characteristic two, this sum squares to zero. In characteristic two the Koszul signs are
trivial, so the differential also commutes with reindexing the factors. These are the underlying
linear maps used to tensor complexes with permutation actions.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

namespace TauCeti.PiTensorProduct

universe u v w

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι]
  {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The sum of the endomorphisms applying `d i` in the `i`-th tensor factor.
Over a ring of characteristic two this is the usual tensor differential, without Koszul signs. -/
noncomputable def differential (d : ∀ i, Module.End R (M i)) :
    Module.End R (⨂[R] i, M i) := by
  classical
  exact ∑ i, _root_.PiTensorProduct.map (Function.update (fun i ↦ LinearMap.id) i (d i))

/-- The tensor differential of zero endomorphisms is zero. -/
@[simp]
theorem differential_zero : differential (fun i ↦ (0 : Module.End R (M i))) = 0 := by
  classical
  unfold differential
  apply Finset.sum_eq_zero
  intro i _
  exact (_root_.PiTensorProduct.mapMultilinear R M M).map_update_zero _ i

/-- There is no differential on a tensor product with no factors. -/
@[simp]
theorem differential_of_isEmpty [IsEmpty ι] (d : ∀ i, Module.End R (M i)) :
    differential d = 0 := by
  classical
  simp [differential]

open Classical in
/-- On a pure tensor the differential is the sum replacing one factor by its differential. -/
@[simp]
theorem differential_tprod (d : ∀ i, Module.End R (M i)) (x : ∀ i, M i) :
    differential d (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d i (x i))) := by
  classical
  simp only [differential, LinearMap.sum_apply, _root_.PiTensorProduct.map_tprod]
  congr 1 with i
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- A tensor of maps commuting with the factor differentials commutes with the tensor
differentials. No square-zero or characteristic hypothesis is needed for this identity. -/
theorem differential_map {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (N i)] (d : ∀ i, Module.End R (M i))
    (e : ∀ i, Module.End R (N i)) (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, e i ∘ₗ f i = f i ∘ₗ d i) :
    differential e ∘ₗ _root_.PiTensorProduct.map f =
      _root_.PiTensorProduct.map f ∘ₗ differential d := by
  classical
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    _root_.PiTensorProduct.map_tprod, differential_tprod, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simpa using LinearMap.congr_fun (hf j) (x j)
  · simp [Function.update_of_ne h]

/-- On a tensor power, reindexing commutes with the tensor differential of a single module. -/
theorem differential_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    {A : Type*} [AddCommMonoid A] [Module R A] (d : Module.End R A) :
    differential (fun _ : κ ↦ d) ∘ₗ
        (_root_.PiTensorProduct.reindex R (fun _ : ι ↦ A) e).toLinearMap =
      (_root_.PiTensorProduct.reindex R (fun _ : ι ↦ A) e).toLinearMap ∘ₗ
        differential (fun _ : ι ↦ d) := by
  classical
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, _root_.PiTensorProduct.reindex_tprod, differential_tprod, map_sum]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases h : e.symm j = i
  · have hj : j = e i := by simpa using congrArg e h
    subst hj
    simp only [Function.update_self, h]
    exact congrArg (fun k ↦ d (x k)) h
  · have hj : j ≠ e i := fun hj ↦ h (by simp [hj])
    simp [Function.update_of_ne h, Function.update_of_ne hj]

/-- The finite tensor differential squares to zero in characteristic two when each factor
differential does. The mixed terms cancel in pairs. -/
theorem differential_comp_self [CharP R 2] (d : ∀ i, Module.End R (M i))
    (hd : ∀ i, d i ∘ₗ d i = 0) : differential d ∘ₗ differential d = 0 := by
  classical
  let δ (i : ι) := _root_.PiTensorProduct.map (Function.update (fun i ↦ LinearMap.id) i (d i))
  have hδ (i : ι) : δ i * δ i = 0 := by
    simp only [δ, ← _root_.PiTensorProduct.map_mul]
    have h : (fun j ↦ Function.update (fun i ↦ LinearMap.id) i (d i) j *
        Function.update (fun i ↦ LinearMap.id) i (d i) j) =
        Function.update (fun i ↦ LinearMap.id) i 0 := by
      funext j
      by_cases h : j = i
      · subst h
        simpa only [Function.update_self, Module.End.mul_eq_comp] using hd j
      · simp [Function.update_of_ne h, ← Module.End.one_eq_id]
    rw [h]
    exact (_root_.PiTensorProduct.mapMultilinear R M M).map_coord_zero i
      (Function.update_self i 0 _)
  have hc (i j : ι) : Commute (δ i) (δ j) := by
    dsimp only [Commute, SemiconjBy, δ]
    rw [← _root_.PiTensorProduct.map_mul, ← _root_.PiTensorProduct.map_mul]
    congr 1
    funext k
    by_cases hi : k = i <;> by_cases hj : k = j
    · subst hi
      subst hj
      rfl
    · simp [Function.update_of_ne hj, ← Module.End.one_eq_id]
    · simp [Function.update_of_ne hi, ← Module.End.one_eq_id]
    · simp [Function.update_of_ne hi, Function.update_of_ne hj, ← Module.End.one_eq_id]
  have htwo : (2 : Module.End R (⨂[R] i, M i)) = 0 := by
    apply LinearMap.ext
    intro z
    have h : (1 + 1 : R) • z = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
    simpa [add_smul, two_nsmul] using h
  have hs (s : Finset ι) : (∑ i ∈ s, δ i) * (∑ i ∈ s, δ i) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hcomm : Commute (δ i) (∑ j ∈ s, δ j) := Commute.sum_right s δ (δ i) fun j _ ↦ hc i j
      rw [Finset.sum_insert hi, ← pow_two, hcomm.add_sq, pow_two, hδ, pow_two, ih, htwo]
      simp
  exact hs Finset.univ

/-- The two-factor differential replaces each of `(0, 1)` in turn by `(1, 0)`.
This is a nonconstant square-zero factor differential over a ring of characteristic two. -/
example {S : Type*} [CommRing S] :
    differential (fun _ : Fin 2 ↦
      (LinearMap.inl S S S).comp (LinearMap.snd S S S))
        (_root_.PiTensorProduct.tprod S (fun _ ↦ (0, 1))) =
      _root_.PiTensorProduct.tprod S ![(1, 0), (0, 1)] +
        _root_.PiTensorProduct.tprod S ![(0, 1), (1, 0)] := by
  classical
  rw [differential_tprod, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> simp

end TauCeti.PiTensorProduct
