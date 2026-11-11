/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Multilinear maps on blocks and contractions of a tuple

Two ways of building a multilinear map of a tuple `a = (a₀, …, aₙ₋₁)` of elements of `A` from
multilinear maps of shorter tuples, as in the operations and morphisms of `A∞` modules:

* `MultilinearMap.compSplit`: for `i + j = n`, a multilinear map `f` of `i` arguments with values
  in linear maps `N₁ → N₂` and a multilinear map `g` of `j` arguments with values in linear maps
  `N₂ → N₃` give `a ↦ g (aᵢ, …, aₙ₋₁) ∘ₗ f (a₀, …, aᵢ₋₁)`;
* `MultilinearMap.compContractNthMul`: for `A` an algebra, a multilinear map `f` of `n` arguments
  and a position `j < n` give the multilinear map
  `a ↦ f (a₀, …, aⱼ₋₁, aⱼ * aⱼ₊₁, aⱼ₊₂, …, aₙ)` of `n + 1` arguments.

They make the composite terms and the product terms of the `A∞` relations into multilinear maps
(see `TauCeti.UngradedAInfinityRightModule.morphismDifferential`), and the second gives the
Hochschild cofaces of cochains (see `TauCeti.hochschildCoface`).
-/

public section

open Function

namespace MultilinearMap

section Split

variable {R A N₁ N₂ N₃ : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃]
  [Module R N₃] {i j n : ℕ}

/-- Updating an entry of a tuple of length `n = i + j` updates one of its two blocks. -/
private theorem update_split {α : Type*} (h : i + j = n) (a : Fin n → α) (p : Fin n) (x : α) :
    ((fun l : Fin j => update a p x ⟨i + l, by omega⟩) =
        if hp : (p : ℕ) < i then fun l : Fin j => a ⟨i + l, by omega⟩
        else update (fun l : Fin j => a ⟨i + l, by omega⟩) ⟨p - i, by omega⟩ x) ∧
      ((fun l : Fin i => update a p x ⟨l, by omega⟩) =
        if hp : (p : ℕ) < i then update (fun l : Fin i => a ⟨l, by omega⟩) ⟨p, hp⟩ x
        else fun l : Fin i => a ⟨l, by omega⟩) := by
  constructor <;> funext l <;> split_ifs with hp <;>
    simp only [update_apply, Fin.ext_iff] <;> split_ifs <;> first | rfl | omega

/-- For `i + j = n`, the multilinear map `a ↦ g (aᵢ, …, aₙ₋₁) ∘ₗ f (a₀, …, aᵢ₋₁)`, composing the
values of `f` on the first `i` entries of `a` with those of `g` on the last `j`. -/
def compSplit (h : i + j = n) (g : MultilinearMap R (fun _ : Fin j => A) (N₂ →ₗ[R] N₃))
    (f : MultilinearMap R (fun _ : Fin i => A) (N₁ →ₗ[R] N₂)) :
    MultilinearMap R (fun _ : Fin n => A) (N₁ →ₗ[R] N₃) :=
  MultilinearMap.mk' (fun a => g (fun l => a ⟨i + l, by omega⟩) ∘ₗ f (fun l => a ⟨l, by omega⟩))
    (fun a p x y => by
      have hg := fun x => (update_split h a p x).1
      have hf := fun x => (update_split h a p x).2
      simp only [hg, hf]
      split_ifs <;> simp [LinearMap.comp_add, LinearMap.add_comp])
    (fun a p c x => by
      have hg := fun x => (update_split h a p x).1
      have hf := fun x => (update_split h a p x).2
      simp only [hg, hf]
      split_ifs <;> simp [LinearMap.comp_smul, LinearMap.smul_comp])

@[simp]
theorem compSplit_apply (h : i + j = n) (g : MultilinearMap R (fun _ : Fin j => A) (N₂ →ₗ[R] N₃))
    (f : MultilinearMap R (fun _ : Fin i => A) (N₁ →ₗ[R] N₂)) (a : Fin n → A) :
    compSplit h g f a = g (fun l => a ⟨i + l, by omega⟩) ∘ₗ f (fun l => a ⟨l, by omega⟩) :=
  (rfl)

end Split

section Contract

variable {R A N : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommMonoid N] [Module R N] {n : ℕ}

omit [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Updating an entry of a tuple updates one entry of its contraction at `j`, by an additive
function of the new value: the new value itself, or its product with a neighbouring entry. -/
private theorem contractNth_castSucc_update (j : Fin n) (a : Fin (n + 1) → A) (p : Fin (n + 1)) :
    ∃ (q : Fin n) (e : A →+ A), (e = AddMonoidHom.id A ∨ (∃ b, e = AddMonoidHom.mulLeft b) ∨
        ∃ b, e = AddMonoidHom.mulRight b) ∧ ∀ x : A,
      Fin.contractNth j.castSucc (· * ·) (update a p x) =
        update (Fin.contractNth j.castSucc (· * ·) a) q (e x) := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
  simp only [Fin.contractNth_castSucc_eq_update_removeNth_succ]
  rcases eq_or_ne p j.succ with rfl | hp
  · refine ⟨j, AddMonoidHom.mulLeft (a j.castSucc), Or.inr (Or.inl ⟨_, rfl⟩), fun x => ?_⟩
    simp [(Fin.castSucc_lt_succ (i := j)).ne]
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hp
    by_cases hq : q = j
    · subst hq
      refine ⟨q, AddMonoidHom.mulRight (a q.succ), Or.inr (Or.inr ⟨_, rfl⟩), fun x => ?_⟩
      have hc : q.castSucc = q.succ.succAbove q :=
        (Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ).symm
      rw [Fin.removeNth_update_succAbove, update_idem, update_idem, ← hc, update_self,
        update_of_ne (Fin.castSucc_lt_succ (i := q)).ne', AddMonoidHom.coe_mulRight]
    · refine ⟨q, AddMonoidHom.id A, Or.inl rfl, fun x => ?_⟩
      have h₁ : j.succ.succAbove q ≠ j.castSucc := by
        rw [Ne, ← Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ (i := j))]
        exact (Fin.succAbove_right_injective (p := j.succ)).ne hq
      have h₂ : j.succ.succAbove q ≠ j.succ := Fin.succAbove_ne _ _
      rw [Fin.removeNth_update_succAbove, update_of_ne h₁.symm, update_of_ne h₂.symm,
        AddMonoidHom.id_apply, update_comm hq]

/-- The multilinear map `a ↦ f (a₀, …, aⱼ₋₁, aⱼ * aⱼ₊₁, aⱼ₊₂, …, aₙ)` of `n + 1` arguments,
contracting the entries `j` and `j + 1` of `a` by multiplication before applying `f`. -/
def compContractNthMul (f : MultilinearMap R (fun _ : Fin n => A) N) (j : Fin n) :
    MultilinearMap R (fun _ : Fin (n + 1) => A) N :=
  MultilinearMap.mk' (fun a => f (Fin.contractNth j.castSucc (· * ·) a))
    (fun a p x y => by
      obtain ⟨q, e, -, he⟩ := contractNth_castSucc_update j a p
      simp only [he, map_add, f.map_update_add])
    (fun a p c x => by
      obtain ⟨q, e, he', he⟩ := contractNth_castSucc_update j a p
      have hc : e (c • x) = c • e x := by
        rcases he' with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · rfl
        · exact mul_smul_comm c b x
        · exact smul_mul_assoc c x b
      simp only [he, hc, f.map_update_smul])

@[simp]
theorem compContractNthMul_apply (f : MultilinearMap R (fun _ : Fin n => A) N) (j : Fin n)
    (a : Fin (n + 1) → A) :
    compContractNthMul f j a = f (Fin.contractNth j.castSucc (· * ·) a) :=
  (rfl)

end Contract

end MultilinearMap
