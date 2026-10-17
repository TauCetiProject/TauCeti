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
has characteristic two, this sum squares to zero. The unsigned differential commutes with
reindexing in every characteristic. In characteristic two the Koszul signs are trivial, so this
unsigned sum is the usual tensor differential. These are the underlying linear maps used to
tensor complexes with permutation actions.

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
  exact ∑ i, _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i (d i))

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

omit [Fintype ι] in
/-- Applying an endomorphism in one tensor coordinate replaces just that factor. -/
theorem map_update_id_tprod [DecidableEq ι] (i : ι) (f : Module.End R (M i))
    (x : ∀ i, M i) :
    _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i f)
        (_root_.PiTensorProduct.tprod R x) =
      _root_.PiTensorProduct.tprod R (Function.update x i (f (x i))) := by
  rw [_root_.PiTensorProduct.map_tprod]
  congr 1
  funext j
  simpa using Function.apply_update (fun k (g : Module.End R (M k)) ↦ g (x k))
    (fun k ↦ LinearMap.id) i f j

/-- On a pure tensor the differential is the sum replacing one factor by its differential. -/
@[simp]
theorem differential_tprod [DecidableEq ι] (d : ∀ i, Module.End R (M i))
    (x : ∀ i, M i) :
    differential d (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d i (x i))) := by
  simp only [differential, LinearMap.sum_apply, map_update_id_tprod]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun decEq ↦ @Function.update ι M decEq x i (d i (x i)))
    (Subsingleton.elim _ _)

/-- A tensor of maps commuting with the factor differentials commutes with the tensor
differentials. No square-zero or characteristic hypothesis is needed for this identity. -/
theorem differential_comp_map {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
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
  rw [Function.apply_update (fun j z ↦ f j z) x i (d i (x i)) j]
  have hfi : e i (f i (x i)) = f i (d i (x i)) := LinearMap.congr_fun (hf i) (x i)
  rw [hfi]

/-- Reindexing transports the tensor differential to the reindexed family. -/
theorem differential_comp_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (d : ∀ i, Module.End R (M i)) :
    differential (fun j ↦ d (e.symm j)) ∘ₗ
        (_root_.PiTensorProduct.reindex R M e).toLinearMap =
      (_root_.PiTensorProduct.reindex R M e).toLinearMap ∘ₗ differential d := by
  classical
  apply LinearMap.ext
  intro z
  simp only [differential, LinearMap.comp_apply, LinearMap.sum_apply, LinearEquiv.coe_coe, map_sum]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  rw [← _root_.PiTensorProduct.map_reindex]
  congr 2
  funext j
  by_cases hj : j = e i
  · subst j
    rw [Function.update_self]
    -- A variable index lets substitution transport both sides in the dependent family.
    have h (k : ι) (hk : k = i) :
        d k = Function.update (fun _ ↦ LinearMap.id) i (d i) k := by
      subst k
      simp
    exact h _ (e.symm_apply_apply i)
  · have hji : e.symm j ≠ i := fun h ↦ hj (by simpa using congrArg e h)
    simp only [Function.update_of_ne hj, Function.update_of_ne hji]

omit [Fintype ι] in
/-- Single-coordinate tensor maps multiply by composing in that coordinate. -/
@[simp]
theorem map_update_id_mul [DecidableEq ι] (i : ι) (f g : Module.End R (M i)) :
    _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i f) *
        _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i g) =
      _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i (f * g)) := by
  rw [← _root_.PiTensorProduct.map_mul]
  congr 1
  funext j
  simpa [← Module.End.one_eq_id] using
    Function.apply_update₂ (fun k (a b : Module.End R (M k)) ↦ a * b)
      (fun k ↦ LinearMap.id) (fun k ↦ LinearMap.id) i f g j

omit [Fintype ι] in
/-- Maps in distinct tensor coordinates commute. In the same coordinate they commute
whenever the factor endomorphisms do. -/
theorem map_update_id_commute [DecidableEq ι] (i j : ι)
    (f : Module.End R (M i)) (g : Module.End R (M j))
    (h : ∀ hij : i = j, Commute (hij ▸ f) g) :
    Commute (_root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i f))
      (_root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) j g)) := by
  rcases eq_or_ne i j with rfl | hij
  · simpa only [Commute, SemiconjBy, map_update_id_mul] using
      congrArg (fun a ↦ _root_.PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) i a)) (h rfl).eq
  · dsimp only [Commute, SemiconjBy]
    ext x
    simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply,
      map_update_id_tprod,
      Function.update_of_ne hij, Function.update_of_ne hij.symm]
    rw [Function.update_comm hij]

/-- The finite tensor differential squares to zero in characteristic two when each factor
differential does. The mixed terms cancel in pairs. -/
theorem differential_comp_self [CharP R 2] (d : ∀ i, Module.End R (M i))
    (hd : ∀ i, d i ∘ₗ d i = 0) : differential d ∘ₗ differential d = 0 := by
  classical
  let δ (i : ι) := _root_.PiTensorProduct.map (Function.update (fun _ ↦ LinearMap.id) i (d i))
  have hδ (i : ι) : δ i * δ i = 0 := by
    rw [map_update_id_mul, Module.End.mul_eq_comp, hd i]
    exact (_root_.PiTensorProduct.mapMultilinear R M M).map_update_zero _ i
  have hc (i j : ι) : Commute (δ i) (δ j) :=
    map_update_id_commute i j (d i) (d j)
      (fun hij ↦ by subst hij; exact Commute.refl _)
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
This uses the nonconstant square-zero factor map `(x, y) ↦ (y, 0)` over any commutative ring. -/
example {S : Type*} [CommRing S] :
    differential (fun _ : Fin 2 ↦
      (LinearMap.inl S S S).comp (LinearMap.snd S S S))
        (_root_.PiTensorProduct.tprod S (fun _ ↦ (0, 1))) =
      _root_.PiTensorProduct.tprod S ![(1, 0), (0, 1)] +
        _root_.PiTensorProduct.tprod S ![(0, 1), (1, 0)] := by
  rw [differential_tprod, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> simp

end TauCeti.PiTensorProduct
